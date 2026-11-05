//! PaxVM M1 supervisor: a standalone native process that forks a
//! static busybox binary, attaches to it with ptrace, and traces the
//! whole guest process tree (M1 spec). It builds on the M0 design:
//!
//! - Classic PTRACE_SYSCALL double-stop model with GETREGSET /
//!   SETREGSET (NT_PRSTATUS) per tracee; no seccomp, no
//!   PTRACE_GET_SYSCALL_INFO.
//! - Path-carrying syscalls are translated onto the rootfs by
//!   rewriting the path argument to a stack scratch area, now
//!   anchored at each process's virtual cwd (vcwd).
//! - execve/execveat of busybox applets (rootfs symlinks to busybox)
//!   is rewritten to the real busybox binary in nativeLibraryDir --
//!   the rootfs lives in filesDir and cannot be exec'd directly.
//! - Unlisted syscalls pass through, logged on first occurrence
//!   (log-first principle).
//! - stdout is a line protocol for the shell: [sup] supervisor
//!   events, [sys] syscall events, [guest] forwarded guest output.
//! - Dual personality (0.2.8): the guest tree's personality is
//!   detected once from the guest binary's ELF class -- the rootfs
//!   can only ever exec that one binary, so a single personality
//!   covers the whole tree. AArch64 guests use the layout and the
//!   asm-generic numbering below; 32-bit ARM (compat) guests use
//!   the compat_pt_regs layout and the ARM EABI table (names32.rs).
//!   The stop state machine, path translation and the SIGSYS
//!   rescue are personality-agnostic; only register access,
//!   syscall numbering and a few argument layouts differ.

mod names32;

use std::collections::{HashMap, HashSet};
use std::ffi::CString;
use std::io::Write;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Mutex;

// ---- ptrace constants (raw; bionic ptrace takes c_int) ----
const PTRACE_TRACEME: i32 = 0;
const PTRACE_PEEKDATA: i32 = 2;
const PTRACE_POKEDATA: i32 = 5;
const PTRACE_SYSCALL: i32 = 24;
const PTRACE_SETOPTIONS: i32 = 0x4200;
const PTRACE_GETEVENTMSG: i32 = 0x4201;
const PTRACE_GETREGSET: i32 = 0x4204;
const PTRACE_SETREGSET: i32 = 0x4205;
const PTRACE_GETSIGINFO: i32 = 0x4207; // not exposed by libc on Android
const PTRACE_O_TRACESYSGOOD: usize = 0x1;
const PTRACE_O_TRACEFORK: usize = 0x2;
const PTRACE_O_TRACEVFORK: usize = 0x4;
const PTRACE_O_TRACECLONE: usize = 0x8;
const PTRACE_O_TRACEEXEC: usize = 0x10;
const PTRACE_O_EXITKILL: usize = 0x100000;
const PTRACE_EVENT_FORK: i32 = 1;
const PTRACE_EVENT_VFORK: i32 = 2;
const PTRACE_EVENT_CLONE: i32 = 3;
const PTRACE_EVENT_EXEC: i32 = 4;
const NT_PRSTATUS: usize = 1;
const NT_ARM_SYSTEM_CALL: usize = 0x404;

const SIGTRAP: i32 = 5;
const SIGSTOP: i32 = 19;
const SIGSYS: i32 = 31;
const SYSCALL_STOP_SIG: i32 = SIGTRAP | 0x80;
const WALL: i32 = 0x40000000; // __WALL: wait for threads too

const AT_FDCWD: i64 = -100;

const ENOSYS: i64 = 38;
const ERANGE: i64 = 34;
const EACCES: i64 = 13;
const ENOENT: i64 = 2;
const EFAULT: i64 = 14;
const ENOTDIR: i64 = 20;

// ---- syscall numbers that differ per personality ----
// AArch64 values are the asm-generic table; compat values are the
// ARM EABI table (Linux v5.4 arch/arm/tools/syscall.tbl, the same
// source names32.rs was generated from).
fn nr_getcwd(compat: bool) -> u64 {
    if compat { 183 } else { 17 }
}
fn nr_chdir(compat: bool) -> u64 {
    if compat { 12 } else { 49 }
}
fn nr_fchdir(compat: bool) -> u64 {
    if compat { 133 } else { 50 }
}
fn nr_execve(compat: bool) -> u64 {
    if compat { 11 } else { 221 }
}
fn nr_execveat(compat: bool) -> u64 {
    if compat { 387 } else { 281 }
}
fn nr_readlinkat(compat: bool) -> u64 {
    if compat { 332 } else { 78 }
}

/// Syscalls whose only path argument is (dirfd=a0, path=a1): T class.
fn is_t_dirfd_path(compat: bool, nr: u64) -> bool {
    if compat {
        // openat, mkdirat, mknodat, fchownat, futimesat, fstatat64,
        // unlinkat, readlinkat, fchmodat, faccessat, utimensat, statx
        matches!(
            nr,
            322 | 323 | 324 | 325 | 326 | 327 | 328 | 332 | 333 | 334 | 348 | 397
        )
    } else {
        matches!(
            nr,
            33 | 34 | 35 | 48 | 53 | 54 | 56 | 78 | 79 | 88 | 291 | 439
        )
    }
}

/// Syscalls with two path arguments. The *at forms carry the paths
/// at a1 and a3 with dirfds a0/a2; the compat table also has the
/// classic link/rename, whose paths sit at a0 and a1 with cwd
/// semantics (entry_translate picks the layout).
fn is_t_two_paths(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 329 | 330 | 9 | 38) // renameat, linkat, link, rename
    } else {
        matches!(nr, 37 | 38) // linkat, renameat
    }
}

/// symlinkat: a0 is the symlink *content* (not translated); the
/// linkpath is a2 with dirfd a1. The compat table's classic symlink
/// has the content at a0 and the linkpath at a1 with cwd semantics.
fn is_t_symlinkat(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 331 | 83) // symlinkat, symlink
    } else {
        nr == 36
    }
}

/// Syscalls whose path is a0 with cwd semantics (no dirfd). The
/// compat table keeps the classic forms AArch64 dropped (open,
/// creat, the stat64 family, ...), all with the path at a0.
fn is_t_path0(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(
            nr,
            5 | 8 | 10 | 14 | 15 | 30 | 33 | 39 | 40 | 85 | 92 | 99 | 193 | 195
                | 196 | 198 | 212 | 266 | 269
        )
    } else {
        matches!(nr, 43 | 45) // statfs, truncate
    }
}

/// F class answered purely from supervisor state (getcwd, fchdir).
/// chdir is also F class (the real syscall never runs) but needs
/// vcwd mutation, so it is dispatched separately in the entry path.
fn is_faked(compat: bool, nr: u64) -> bool {
    nr == nr_getcwd(compat) || nr == nr_fchdir(compat)
}

/// X class: blocked with -ENOSYS. clone/clone3 left this class in
/// M1 (children are followed via TRACEFORK/TRACECLONE), and
/// execve/execveat are routed to the exec handler instead.
fn is_blocked(compat: bool, nr: u64) -> bool {
    if compat {
        // mount, umount, ptrace, umount2, chroot, pivot_root,
        // unshare, name_to_handle_at, open_by_handle_at, setns,
        // seccomp, bpf
        matches!(
            nr,
            21 | 22 | 26 | 52 | 61 | 218 | 337 | 370 | 371 | 375 | 383 | 386
        )
    } else {
        matches!(
            nr,
            39 | 40 | 41 | 51 | 97 | 117 | 264 | 265 | 268 | 277 | 280 | 437
        )
    }
}

/// Syscall name in the tracee's personality: asm-generic names
/// for AArch64 guests, ARM EABI names (names32.rs) for compat.
fn nr_name(compat: bool, nr: u64) -> &'static str {
    if compat {
        // ARM private syscalls (0x0f0000 range) have no entry in
        // the tbl-generated table.
        match nr {
            983_041 => return "__arm_breakpoint",
            983_042 => return "__arm_cacheflush",
            983_043 => return "__arm_usr26",
            983_044 => return "__arm_usr32",
            983_045 => return "__arm_set_tls",
            983_046 => return "__arm_get_tls",
            _ => {}
        }
        names32::nr_name32(nr)
    } else {
        nr_name64(nr)
    }
}

fn nr_name64(nr: u64) -> &'static str {
    match nr {
        17 => "getcwd",
        23 => "dup",
        24 => "dup3",
        25 => "fcntl",
        29 => "ioctl",
        33 => "mknodat",
        34 => "mkdirat",
        35 => "unlinkat",
        36 => "symlinkat",
        37 => "linkat",
        38 => "renameat",
        39 => "umount2",
        40 => "mount",
        41 => "pivot_root",
        43 => "statfs",
        45 => "truncate",
        46 => "ftruncate",
        48 => "faccessat",
        49 => "chdir",
        50 => "fchdir",
        51 => "chroot",
        53 => "fchmodat",
        54 => "fchownat",
        56 => "openat",
        57 => "close",
        59 => "pipe2",
        61 => "getdents64",
        62 => "lseek",
        63 => "read",
        64 => "write",
        65 => "readv",
        66 => "writev",
        67 => "pread64",
        68 => "pwrite64",
        71 => "sendfile",
        72 => "pselect6",
        73 => "ppoll",
        76 => "splice",
        78 => "readlinkat",
        79 => "newfstatat",
        80 => "fstat",
        82 => "fsync",
        83 => "fdatasync",
        88 => "utimensat",
        93 => "exit",
        94 => "exit_group",
        95 => "waitid",
        96 => "set_tid_address",
        97 => "unshare",
        98 => "futex",
        99 => "set_robust_list",
        101 => "nanosleep",
        113 => "clock_gettime",
        114 => "clock_getres",
        115 => "clock_nanosleep",
        117 => "ptrace",
        123 => "sched_getaffinity",
        124 => "sched_yield",
        128 => "restart_syscall",
        129 => "kill",
        131 => "tgkill",
        132 => "sigaltstack",
        134 => "rt_sigaction",
        135 => "rt_sigprocmask",
        139 => "rt_sigreturn",
        143 => "setregid",
        144 => "setgid",
        145 => "setreuid",
        146 => "setuid",
        147 => "setresuid",
        148 => "getresuid",
        149 => "setresgid",
        150 => "getresgid",
        151 => "setfsuid",
        152 => "setfsgid",
        159 => "setgroups",
        160 => "uname",
        163 => "getrlimit",
        164 => "setrlimit",
        166 => "umask",
        167 => "prctl",
        168 => "getcpu",
        169 => "gettimeofday",
        172 => "getpid",
        173 => "getppid",
        174 => "getuid",
        175 => "geteuid",
        176 => "getgid",
        177 => "getegid",
        178 => "gettid",
        179 => "sysinfo",
        214 => "brk",
        215 => "munmap",
        216 => "mremap",
        220 => "clone",
        221 => "execve",
        222 => "mmap",
        226 => "mprotect",
        233 => "madvise",
        260 => "wait4",
        261 => "prlimit64",
        264 => "name_to_handle_at",
        265 => "open_by_handle_at",
        268 => "setns",
        277 => "seccomp",
        278 => "getrandom",
        280 => "bpf",
        281 => "execveat",
        291 => "statx",
        293 => "rseq",
        435 => "clone3",
        436 => "close_range",
        437 => "openat2",
        439 => "faccessat2",
        _ => "unknown",
    }
}

// ---- line output (the shell's only view of us) ----
static OUT_LOCK: Mutex<()> = Mutex::new(());

fn emit(tag: &str, msg: &str) {
    let _g = OUT_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let stdout = std::io::stdout();
    let mut h = stdout.lock();
    let _ = writeln!(h, "[{tag}] {msg}");
    let _ = h.flush();
}

macro_rules! sup {
    ($($a:tt)*) => { emit("sup", &format!($($a)*)) };
}
macro_rules! sys {
    ($($a:tt)*) => { emit("sys", &format!($($a)*)) };
}

// ---- errno / ptrace primitives ----
fn errno() -> i32 {
    // Bionic exposes the thread-local errno cell as __errno().
    unsafe { *libc::__errno() }
}

fn ptrace4(req: i32, pid: i32, addr: *mut libc::c_void, data: *mut libc::c_void) -> i64 {
    unsafe { libc::ptrace(req, pid, addr, data) as i64 }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct UserPtRegs {
    regs: [u64; 31],
    sp: u64,
    pc: u64,
    pstate: u64,
}

/// The kernel's compat_pt_regs for a 32-bit tracee on arm64:
/// r0..r15 at uregs[0..16] (sp = uregs[13], pc = uregs[15]),
/// the syscall number at uregs[7] (r7), cpsr at uregs[16],
/// orig_r0 at uregs[17].
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct CompatPtRegs {
    uregs: [u32; 18],
}

/// A tracee's register set in whichever personality it currently
/// runs. Every register touch in the supervisor goes through this
/// access surface, so the syscall machinery above and below stays
/// personality-agnostic.
#[derive(Clone, Copy)]
enum Regs {
    A64(UserPtRegs),
    A32(CompatPtRegs),
}

impl Regs {
    fn nr(&self) -> u64 {
        match self {
            Regs::A64(r) => r.regs[8],
            Regs::A32(r) => r.uregs[7] as u64,
        }
    }
    fn arg(&self, i: usize) -> u64 {
        match self {
            Regs::A64(r) => r.regs[i],
            Regs::A32(r) => r.uregs[i] as u64,
        }
    }
    fn set_arg(&mut self, i: usize, v: u64) {
        match self {
            Regs::A64(r) => r.regs[i] = v,
            Regs::A32(r) => r.uregs[i] = v as u32,
        }
    }
    fn sp(&self) -> u64 {
        match self {
            Regs::A64(r) => r.sp,
            Regs::A32(r) => r.uregs[13] as u64,
        }
    }
    fn pc(&self) -> u64 {
        match self {
            Regs::A64(r) => r.pc,
            Regs::A32(r) => r.uregs[15] as u64,
        }
    }
    /// Return value as the guest reads it: x0 sign-extended from
    /// 64 bits, r0 sign-extended from 32 (a -errno in r0 is a small
    /// u32; reading it as u64 would hide the sign).
    fn retval(&self) -> i64 {
        match self {
            Regs::A64(r) => r.regs[0] as i64,
            Regs::A32(r) => r.uregs[0] as i32 as i64,
        }
    }
    fn set_retval(&mut self, v: i64) {
        match self {
            Regs::A64(r) => r.regs[0] = v as u64,
            Regs::A32(r) => r.uregs[0] = v as u32,
        }
    }
    /// The tracee-visible syscall-number register to -1 (x8 on
    /// AArch64, r7 on compat). See skip_syscall for why this alone
    /// cancels nothing and is only kept for honesty of the dump.
    fn cancel_nr_reg(&mut self) {
        match self {
            Regs::A64(r) => r.regs[8] = u64::MAX,
            Regs::A32(r) => r.uregs[7] = u32::MAX,
        }
    }
}

/// The guest binary's personality, from its ELF header: EI_CLASS
/// 1 (ELF32) with EM_ARM means compat tracees, EI_CLASS 2 means
/// native AArch64. None when the header cannot be read or is not
/// an ARM-family ELF at all.
fn guest_is_compat(path: &str) -> Option<bool> {
    use std::io::Read;
    let mut f = std::fs::File::open(path).ok()?;
    let mut h = [0u8; 20];
    f.read_exact(&mut h).ok()?;
    if &h[0..4] != b"\x7fELF" {
        return None;
    }
    let machine = u16::from_le_bytes([h[18], h[19]]);
    match (h[4], machine) {
        (1, 40) => Some(true),   // ELF32, EM_ARM
        (2, 183) => Some(false), // ELF64, EM_AARCH64
        _ => None,
    }
}

fn get_regs(pid: i32, compat: bool) -> Option<Regs> {
    if compat {
        let mut r = CompatPtRegs::default();
        let mut iov = libc::iovec {
            iov_base: &mut r as *mut CompatPtRegs as *mut libc::c_void,
            iov_len: std::mem::size_of::<CompatPtRegs>(),
        };
        let rc = ptrace4(
            PTRACE_GETREGSET,
            pid,
            NT_PRSTATUS as *mut libc::c_void,
            &mut iov as *mut libc::iovec as *mut libc::c_void,
        );
        if rc != 0 {
            sup!("GETREGSET failed pid={pid}: errno={}", errno());
            return None;
        }
        if iov.iov_len != std::mem::size_of::<CompatPtRegs>() {
            // The kernel answered with a different regset size
            // than the personality we assumed: say so in the log
            // instead of parsing garbage (the probe's core
            // question is exactly whether this matches).
            sup!(
                "WARN: GETREGSET pid={pid}: compat layout expected {} bytes, kernel gave {}",
                std::mem::size_of::<CompatPtRegs>(),
                iov.iov_len
            );
            return None;
        }
        Some(Regs::A32(r))
    } else {
        let mut r = UserPtRegs::default();
        let mut iov = libc::iovec {
            iov_base: &mut r as *mut UserPtRegs as *mut libc::c_void,
            iov_len: std::mem::size_of::<UserPtRegs>(),
        };
        let rc = ptrace4(
            PTRACE_GETREGSET,
            pid,
            NT_PRSTATUS as *mut libc::c_void,
            &mut iov as *mut libc::iovec as *mut libc::c_void,
        );
        if rc != 0 {
            sup!("GETREGSET failed pid={pid}: errno={}", errno());
            return None;
        }
        Some(Regs::A64(r))
    }
}

fn set_regs(pid: i32, regs: &Regs) -> bool {
    let (base, len) = match regs {
        Regs::A64(r) => (
            r as *const UserPtRegs as *mut libc::c_void,
            std::mem::size_of::<UserPtRegs>(),
        ),
        Regs::A32(r) => (
            r as *const CompatPtRegs as *mut libc::c_void,
            std::mem::size_of::<CompatPtRegs>(),
        ),
    };
    let mut iov = libc::iovec {
        iov_base: base,
        iov_len: len,
    };
    ptrace4(
        PTRACE_SETREGSET,
        pid,
        NT_PRSTATUS as *mut libc::c_void,
        &mut iov as *mut libc::iovec as *mut libc::c_void,
    ) == 0
}

fn cont_syscall(pid: i32, sig: i32) {
    ptrace4(PTRACE_SYSCALL, pid, std::ptr::null_mut(), sig as usize as *mut libc::c_void);
}

/// The one option set every tracee gets (M1 spec section 1):
/// syscall stops, exec events, fork/vfork/clone following, and
/// EXITKILL so no tracee can outlive the supervisor.
fn set_trace_options(pid: i32) -> bool {
    let opts = (PTRACE_O_TRACESYSGOOD
        | PTRACE_O_TRACEEXEC
        | PTRACE_O_TRACEFORK
        | PTRACE_O_TRACEVFORK
        | PTRACE_O_TRACECLONE
        | PTRACE_O_EXITKILL) as *mut libc::c_void;
    if ptrace4(PTRACE_SETOPTIONS, pid, std::ptr::null_mut(), opts) != 0 {
        sup!(
            "PTRACE_SETOPTIONS failed pid={pid}: errno={} ({})",
            errno(),
            std::io::Error::from_raw_os_error(errno())
        );
        return false;
    }
    true
}

fn get_event_msg(pid: i32) -> Option<u64> {
    let mut msg: u64 = 0;
    let rc = ptrace4(
        PTRACE_GETEVENTMSG,
        pid,
        std::ptr::null_mut(),
        &mut msg as *mut u64 as *mut libc::c_void,
    );
    if rc == 0 {
        Some(msg)
    } else {
        None
    }
}

/// SIGSYS forensics (purely additive; never alters handling).
/// A seccomp trap fires *before* the syscall-entry stop, so the
/// culprit syscall leaves no [sys] line. The siginfo the kernel
/// attached to the signal names it: for si_code == SYS_SECCOMP (1)
/// the _sigsys union carries the trapped syscall number, the audit
/// arch and the userspace call address. siginfo_t layout:
/// si_signo@0 (i32), si_errno@4, si_code@8; the union starts at
/// @16 for a native tracee (_call_addr@16 u64, _syscall@24 i32,
/// _arch@28 u32) and at @12 for a compat tracee (_call_addr@12
/// u32, _syscall@16 i32, _arch@20 u32).
fn dump_sigsys_info(pid: i32, compat: bool) {
    let mut buf = [0u8; 128];
    let rc = ptrace4(
        PTRACE_GETSIGINFO,
        pid,
        std::ptr::null_mut(),
        buf.as_mut_ptr() as *mut libc::c_void,
    );
    if rc != 0 {
        sup!("SIGSYS detail pid={pid}: GETSIGINFO failed errno={}", errno());
    } else {
        let si_code = i32::from_ne_bytes(buf[8..12].try_into().unwrap());
        let (call_addr, sc, arch) = if compat {
            (
                u32::from_ne_bytes(buf[12..16].try_into().unwrap()) as u64,
                i32::from_ne_bytes(buf[16..20].try_into().unwrap()),
                u32::from_ne_bytes(buf[20..24].try_into().unwrap()),
            )
        } else {
            (
                u64::from_ne_bytes(buf[16..24].try_into().unwrap()),
                i32::from_ne_bytes(buf[24..28].try_into().unwrap()),
                u32::from_ne_bytes(buf[28..32].try_into().unwrap()),
            )
        };
        let name = if sc >= 0 {
            nr_name(compat, sc as u64)
        } else {
            "unknown-id"
        };
        sup!(
            "SIGSYS detail pid={pid}: si_code={si_code} syscall={sc} name={name} arch=0x{arch:x} call_addr=0x{call_addr:x}"
        );
    }
    if let Some(r) = get_regs(pid, compat) {
        sup!(
            "SIGSYS regs pid={pid}: pc=0x{:x} nr_reg=0x{:x} a0=0x{:x} a1=0x{:x} a2=0x{:x}",
            r.pc(),
            r.nr(),
            r.arg(0),
            r.arg(1),
            r.arg(2)
        );
    }
}

// ---- guest memory access (process_vm_*, PEEK/POKE fallback) ----
fn read_mem(pid: i32, addr: u64, buf: &mut [u8]) -> Result<usize, i32> {
    let mut local = libc::iovec {
        iov_base: buf.as_mut_ptr() as *mut libc::c_void,
        iov_len: buf.len(),
    };
    let mut remote = libc::iovec {
        iov_base: addr as *mut libc::c_void,
        iov_len: buf.len(),
    };
    let n = unsafe {
        libc::process_vm_readv(
            pid,
            &mut local as *mut libc::iovec,
            1,
            &mut remote as *mut libc::iovec,
            1,
            0,
        )
    };
    if n >= 0 {
        return Ok(n as usize);
    }
    // Fallback: word-at-a-time PEEKDATA.
    let mut done = 0usize;
    while done < buf.len() {
        unsafe { *libc::__errno() = 0 };
        let word = ptrace4(PTRACE_PEEKDATA, pid, (addr + done as u64) as *mut libc::c_void, std::ptr::null_mut());
        let e = errno();
        if word == -1 && e != 0 {
            return Err(e);
        }
        let bytes = word.to_ne_bytes();
        let take = (buf.len() - done).min(8);
        buf[done..done + take].copy_from_slice(&bytes[..take]);
        done += take;
    }
    Ok(done)
}

fn write_mem(pid: i32, addr: u64, data: &[u8]) -> Result<(), i32> {
    let mut local = libc::iovec {
        iov_base: data.as_ptr() as *mut libc::c_void,
        iov_len: data.len(),
    };
    let mut remote = libc::iovec {
        iov_base: addr as *mut libc::c_void,
        iov_len: data.len(),
    };
    let n = unsafe {
        libc::process_vm_writev(
            pid,
            &mut local as *mut libc::iovec,
            1,
            &mut remote as *mut libc::iovec,
            1,
            0,
        )
    };
    if n == data.len() as isize {
        return Ok(());
    }
    // Fallback: POKEDATA with read-modify-write on partial words.
    let mut done = 0usize;
    while done < data.len() {
        let cur = addr + done as u64;
        let take = (data.len() - done).min(8);
        let mut word_bytes = [0u8; 8];
        if take < 8 {
            let mut old = [0u8; 8];
            read_mem(pid, cur, &mut old)?;
            word_bytes.copy_from_slice(&old);
        }
        word_bytes[..take].copy_from_slice(&data[done..done + take]);
        let word = i64::from_ne_bytes(word_bytes);
        if ptrace4(PTRACE_POKEDATA, pid, cur as *mut libc::c_void, word as usize as *mut libc::c_void) != 0 {
            return Err(errno());
        }
        done += take;
    }
    Ok(())
}

/// Read a NUL-terminated path string out of the guest (PATH_MAX cap).
fn read_path(pid: i32, addr: u64) -> Option<String> {
    let mut all: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 512];
    loop {
        match read_mem(pid, addr + all.len() as u64, &mut chunk) {
            Ok(n) if n > 0 => {
                if let Some(pos) = chunk[..n].iter().position(|&b| b == 0) {
                    all.extend_from_slice(&chunk[..pos]);
                    break;
                }
                all.extend_from_slice(&chunk[..n]);
                if all.len() >= 4096 {
                    break;
                }
            }
            _ => return None,
        }
    }
    Some(String::from_utf8_lossy(&all).into_owned())
}

// ---- path translation (M0 spec 2.5, vcwd-anchored per M1 spec 3) ----

/// Lexically normalize a guest path into components under the guest
/// root: collapses duplicate '/', drops '.', and clamps '..' at the
/// root. No symlink resolution at this layer.
fn normalize_components(path: &str) -> Vec<&str> {
    let mut out: Vec<&str> = Vec::new();
    for c in path.split('/') {
        match c {
            "" | "." => {}
            ".." => {
                out.pop();
            }
            s => out.push(s),
        }
    }
    out
}

/// Normalize to a canonical absolute guest path ("/" for the root).
fn normalize_path_str(path: &str) -> String {
    let comps = normalize_components(path);
    if comps.is_empty() {
        "/".to_string()
    } else {
        format!("/{}", comps.join("/"))
    }
}

/// Resolve a guest path argument to its canonical absolute guest
/// form: absolute paths stand alone; relative paths anchor at the
/// process's virtual cwd.
fn guest_abs(vcwd: &str, path: &str) -> String {
    if path.starts_with('/') {
        normalize_path_str(path)
    } else {
        normalize_path_str(&format!("{vcwd}/{path}"))
    }
}

/// Decide the host path for (dirfd, path); None = do not translate.
fn translate(rootfs: &str, vcwd: &str, dirfd: i64, path: &str) -> Option<String> {
    if path.is_empty() {
        return None;
    }
    if !path.starts_with('/') && dirfd != AT_FDCWD {
        // Relative to a real fd: that fd was opened via a translated
        // path, so kernel resolution is already inside the rootfs.
        return None;
    }
    let abs = guest_abs(vcwd, path);
    if abs == "/" {
        Some(format!("{rootfs}/"))
    } else {
        Some(format!("{rootfs}{abs}"))
    }
}

fn roundup16(n: u64) -> u64 {
    (n + 15) & !15
}

/// Write `s` plus NUL into the guest's stack scratch area below `sp`
/// and return its address. `cursor` starts at sp and moves down,
/// keeping a 256-byte safety margin under the live stack.
fn scratch_write(pid: i32, cursor: &mut u64, s: &str) -> Option<u64> {
    let len = s.len() as u64 + 1;
    *cursor = cursor.saturating_sub(roundup16(len));
    let addr = *cursor;
    let mut bytes = s.as_bytes().to_vec();
    bytes.push(0);
    match write_mem(pid, addr, &bytes) {
        Ok(()) => Some(addr),
        Err(e) => {
            sup!("scratch write failed at {addr:#x}: errno={e}");
            None
        }
    }
}

// ---- SIGTERM handling: kill the guest root, then exit. Every
// tracee carries PTRACE_O_EXITKILL, so supervisor death takes the
// whole tree down with it (M0 spec section 4, extended to the tree).
static GUEST_PID: AtomicI32 = AtomicI32::new(0);

extern "C" fn on_sigterm(_sig: i32) {
    let p = GUEST_PID.load(Ordering::Relaxed);
    if p > 0 {
        unsafe { libc::kill(p, libc::SIGKILL) };
    }
    unsafe { libc::_exit(128 + 15) };
}

// ---- per-process tracing state (M1 spec section 1) ----
struct Pending {
    nr: u64,
    desc: Option<String>,
    inject: Option<i64>,
    /// True once the fabricated return value has actually been
    /// written into the tracee's regs (at the exit stop, or at a
    /// SIGSYS rescue stop). Only meaningful when inject is Some.
    applied: bool,
    /// Guest memory temporarily rewritten for the duration of
    /// one passed syscall (the unix-socket sockaddr path, see
    /// entry_unix_sockaddr): (address, original bytes), restored
    /// verbatim at the exit stop.
    mem_restore: Option<(u64, Vec<u8>)>,
}

struct ProcState {
    expect_exit: bool,
    pending: Option<Pending>,
    /// Virtual cwd in guest path space; "/" at birth, inherited
    /// across fork/vfork/clone, unchanged by exec.
    vcwd: String,
    /// True once we have set ptrace options at the initial stop.
    options_set: bool,
    /// True once the initial stop has been consumed and the process
    /// has been continued for the first time.
    started: bool,
    /// True once a syscall-entry stop has been processed. Until
    /// then no translation has used this process's vcwd, so a late
    /// fork event may still correct it from the parent.
    syscall_seen: bool,
    is_root: bool,
    /// The personality this tracee's registers and syscall numbers
    /// are read in. The root starts native (it is our own fork
    /// child, still running the supervisor image) and flips to the
    /// guest's personality at its exec event; children inherit the
    /// parent's current value at birth -- every birth in the tree
    /// happens after the launch exec, from an already-flipped
    /// parent. Execs inside the tree only ever land on the same
    /// guest binary, so the value never flips back.
    compat: bool,
}

impl ProcState {
    fn new(vcwd: &str, is_root: bool, compat: bool) -> Self {
        ProcState {
            expect_exit: false,
            pending: None,
            vcwd: vcwd.to_string(),
            options_set: false,
            started: false,
            syscall_seen: false,
            is_root,
            compat,
        }
    }
}

/// Write pt_regs.syscallno through the arm64 NT_ARM_SYSTEM_CALL
/// regset. syscallno is the field the kernel dispatches on; it is
/// NOT the tracee-visible x8 that NT_PRSTATUS exposes as regs[8].
fn set_syscallno(pid: i32, value: i32) -> bool {
    let mut v = value;
    let mut iov = libc::iovec {
        iov_base: &mut v as *mut i32 as *mut libc::c_void,
        iov_len: std::mem::size_of::<i32>(),
    };
    ptrace4(
        PTRACE_SETREGSET,
        pid,
        NT_ARM_SYSTEM_CALL as *mut libc::c_void,
        &mut iov as *mut libc::iovec as *mut libc::c_void,
    ) == 0
}

/// Cancel the syscall the guest is about to enter, and force x0 to
/// `value` at the exit stop (via pend.inject).
///
/// On arm64, cancellation works by writing pt_regs.syscallno = -1
/// through NT_ARM_SYSTEM_CALL -- never by regs[8]: in v5.4's
/// arch/arm64/kernel/ptrace.c, syscall_trace_enter reports the
/// ptrace entry stop first, then checks in_syscall(regs)
/// (syscallno != -1) before calling secure_computing, and returns
/// regs->syscallno for dispatch. So syscallno = -1 short-circuits
/// *before* the seccomp filter is ever evaluated, and the syscall
/// is never dispatched; the exit stop still arrives, so the
/// fabricated return value is injected there as before. Writing
/// regs[8] = -1 through NT_PRSTATUS changes only the tracee-visible
/// x8 register and cancels nothing (proven on device in 0.2.4: the
/// "emulated" setgid really executed -- that handset happened to
/// allow it and returned the same 0 we injected -- and the
/// following setuid really executed into the seccomp TRAP).
/// The tracee-visible number register (x8 on AArch64, r7 on
/// compat) is still set to -1 as well: harmless, and it keeps any
/// reader of x8 (including our own SIGSYS regs dump) honest.
fn skip_syscall(pid: i32, regs: &mut Regs, pend: &mut Pending, value: i64) {
    regs.cancel_nr_reg();
    if !set_syscallno(pid, -1) {
        sup!(
            "WARN: NT_ARM_SYSTEM_CALL set failed pid={pid} errno={}",
            errno()
        );
    }
    pend.inject = Some(value);
}

/// T class: rewrite each path argument into the rootfs and return a
/// log description of what was done.
fn entry_translate(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    compat: bool,
    nr: u64,
    regs: &mut Regs,
) -> String {
    // (arg index of path, arg index of its dirfd or -1 for cwd semantics)
    let pairs: Vec<(usize, i64)> = if compat && (nr == 9 || nr == 38) {
        // Classic link/rename: both paths carry cwd semantics.
        vec![(0, AT_FDCWD), (1, AT_FDCWD)]
    } else if compat && nr == 83 {
        // Classic symlink: a0 is the content, a1 the linkpath.
        vec![(1, AT_FDCWD)]
    } else if is_t_dirfd_path(compat, nr) {
        vec![(1, regs.arg(0) as i64)]
    } else if is_t_two_paths(compat, nr) {
        vec![(1, regs.arg(0) as i64), (3, regs.arg(2) as i64)]
    } else if is_t_symlinkat(compat, nr) {
        vec![(2, regs.arg(1) as i64)]
    } else {
        vec![(0, AT_FDCWD)]
    };
    let mut cursor = regs.sp().saturating_sub(256);
    let mut parts: Vec<String> = Vec::new();
    for (argi, dirfd) in pairs {
        let addr = regs.arg(argi);
        match read_path(pid, addr) {
            Some(old) => match translate(rootfs, vcwd, dirfd, &old) {
                Some(new) => {
                    let new = if is_open_family(compat, nr) {
                        device_map(rootfs, &guest_abs(vcwd, &old)).unwrap_or(new)
                    } else {
                        new
                    };
                    match scratch_write(pid, &mut cursor, &new) {
                    Some(scratch) => {
                        regs.set_arg(argi, scratch);
                        parts.push(format!("'{old}' -> '{new}'"));
                    }
                    None => parts.push(format!("'{old}' (scratch write failed, untranslated)")),
                    }
                },
                None => parts.push(format!("'{old}' (untranslated)")),
            },
            None => parts.push(format!("path@{addr:#x} (unreadable)")),
        }
    }
    let mut desc = format!("{}({}) {}", nr_name(compat, nr), nr, parts.join(", "));
    if nr == nr_readlinkat(compat) {
        // readlinkat: the result buffer gets the real (prefixed)
        // path written back; accepted per M0 spec 2.4.
        desc.push_str(" [note: readlink result may carry the rootfs prefix]");
    }
    desc
}

/// set*id family: emulated at the entry stop, always returning 0.
/// Android's app seccomp filter traps the whole family (it is not on
/// the app allowlist, and the filter's default action is TRAP), so
/// these syscalls must never actually be dispatched. Cancellation
/// at the entry stop goes through NT_ARM_SYSTEM_CALL (see
/// skip_syscall): v5.4's syscall_trace_enter checks in_syscall()
/// after the ptrace entry report and *before* secure_computing, and
/// dispatches on pt_regs.syscallno -- a field that regs[8], written
/// through NT_PRSTATUS, does not touch. (0.2.4 relied on regs[8]
/// and cancelled nothing: its setgid really ran, and its setuid
/// really ran into the TRAP.) The guest is a single-uid sandbox and busybox's startup
/// privilege-drop sequence (getuid/getgid, then setgid, then setuid,
/// dispatched per-thread by musl's synccall) only ever sets the ids
/// to their own current values, so 0 is the semantically correct
/// answer -- the same treatment proot gives the uid/gid family.
/// getresuid(148)/getresgid(150) are harmless queries and pass.
fn is_setid_emulated(compat: bool, nr: u64) -> bool {
    if compat {
        // The 16-bit and 32-bit uid forms, both: musl calls the
        // *32 variants, but the legacy numbers cost nothing to
        // cover -- the whole family is trapped by the filter.
        matches!(
            nr,
            23 | 46 | 70 | 71 | 81 | 138 | 139 | 164 | 170 | 203 | 204 | 206 | 208
                | 210 | 213 | 214 | 215 | 216
        )
    } else {
        matches!(nr, 143 | 144 | 145 | 146 | 147 | 149 | 151 | 152 | 159)
    }
}

/// F class (getcwd, fchdir): cancel the syscall and fabricate the
/// answer from the virtual cwd (M1 spec section 3).
fn entry_fake(
    pid: i32,
    vcwd: &str,
    compat: bool,
    nr: u64,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    if nr == nr_getcwd(compat) {
        let buf = regs.arg(0);
        let size = regs.arg(1);
        let need = (vcwd.len() + 1) as u64;
        let mut bytes = vcwd.as_bytes().to_vec();
        bytes.push(0);
        if size >= need && write_mem(pid, buf, &bytes).is_ok() {
            skip_syscall(pid, regs, pend, need as i64);
            format!("getcwd({nr}) FAKED -> \"{vcwd}\"")
        } else {
            skip_syscall(pid, regs, pend, -ERANGE);
            format!("getcwd({nr}) FAKED -> -ERANGE (buffer too small)")
        }
    } else {
        // fchdir: succeed without touching the vcwd. The guest
        // shell's cd uses chdir, not fchdir (M1 spec section 3).
        skip_syscall(pid, regs, pend, 0);
        format!("fchdir({nr}) FAKED -> 0 (vcwd stays {vcwd})")
    }
}

/// chdir: true proxying at the virtual level (M1 spec section 3).
/// The real syscall never runs -- the guest process's host cwd must
/// stay at "/" so relative resolution has exactly one anchor, the
/// vcwd. Returns the log description and, on success, the new vcwd.
fn entry_chdir(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    compat: bool,
    regs: &mut Regs,
    pend: &mut Pending,
) -> (String, Option<String>) {
    let cnr = nr_chdir(compat);
    let addr = regs.arg(0);
    let Some(p) = read_path(pid, addr) else {
        skip_syscall(pid, regs, pend, -ENOENT);
        return (format!("chdir({cnr}) path unreadable -> -ENOENT"), None);
    };
    let target = guest_abs(vcwd, &p);
    let host = format!("{rootfs}{target}");
    match std::fs::metadata(&host) {
        Ok(md) if md.is_dir() => {
            skip_syscall(pid, regs, pend, 0);
            (
                format!("chdir({cnr}) '{p}' vcwd {vcwd} -> {target}"),
                Some(target),
            )
        }
        Ok(_) => {
            skip_syscall(pid, regs, pend, -ENOTDIR);
            (format!("chdir({cnr}) '{p}' -> -ENOTDIR (target {target})"), None)
        }
        Err(_) => {
            skip_syscall(pid, regs, pend, -ENOENT);
            (format!("chdir({cnr}) '{p}' -> -ENOENT (target {target})"), None)
        }
    }
}

/// Open-family calls (the ones that turn a path into a live
/// object) get device-node redirections; every other path call
/// keeps plain rootfs translation.
fn is_open_family(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 5 | 8 | 322) // open, creat, openat
    } else {
        nr == 56 // openat
    }
}

/// Device nodes an Android guest expects to exist before any
/// filesystem is mounted. The guest uid cannot mknod and the
/// rootfs cannot hold real nodes, so opens of a tiny whitelist
/// are redirected: the null family and console to the host's
/// /dev/null (init points its stdio there before logging
/// exists), ashmem/zero/urandom to the real host devices (same
/// kernel, real semantics), and init's kernel-log node to a
/// capture file inside the rootfs that the shell dumps after
/// the session — that file is init's only voice in phase 1.
fn device_map(rootfs: &str, guest_abs_path: &str) -> Option<String> {
    match guest_abs_path {
        "/dev/null" | "/dev/__null__" | "/dev/console" => Some("/dev/null".to_string()),
        "/dev/ashmem" => Some("/dev/ashmem".to_string()),
        "/dev/zero" => Some("/dev/zero".to_string()),
        "/dev/urandom" | "/dev/random" => Some("/dev/urandom".to_string()),
        "/dev/__kmsg__" => Some(format!("{rootfs}/.kmsg")),
        _ => None,
    }
}

/// Compat mknod(14) for /dev/* paths: faked successful. The
/// guest uid has no CAP_MKNOD, so a passed-through mknod fails
/// EPERM — and Android 2.3's init treats that as fatal in
/// open_devnull_stdio (exit(1) before anything else runs).
/// Device nodes are virtual in this engine anyway: creation is
/// recorded nowhere, and opens of the whitelisted nodes are
/// redirected by device_map. Non-/dev paths fall through to
/// translation (and the kernel's EPERM) unchanged.
fn entry_mknod_dev(
    pid: i32,
    vcwd: &str,
    regs: &mut Regs,
    pend: &mut Pending,
) -> Option<String> {
    let p = read_path(pid, regs.arg(0))?;
    let abs = guest_abs(vcwd, &p);
    if !abs.starts_with("/dev/") {
        return None;
    }
    skip_syscall(pid, regs, pend, 0);
    Some(format!("mknod(14) '{p}' faked (virtual device node)"))
}

/// Compat chmod(15), proxied by the supervisor itself. Same
/// allowlist gap as rmdir: Android 12's bionic implements
/// chmod() as a C wrapper around fchmodat, so the standalone
/// chmod syscall has no stub, is absent from the app seccomp
/// policy, and a passed-through call is trapped — Android
/// 2.3.7's init died exactly there (import_kernel_cmdline's
/// chmod("/proc/cmdline", 0440), init.c:460; device run
/// 2026-11-06, SIGSYS at the call with the fake exit stop
/// showing the path pointer as the "return value"). The
/// supervisor performs the chmod on the translated host path;
/// same filesystem, exact errno semantics.
fn entry_chmod(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    let addr = regs.arg(0);
    let mode = regs.arg(1) as u32;
    let Some(p) = read_path(pid, addr) else {
        skip_syscall(pid, regs, pend, -EFAULT);
        return "chmod(15) path unreadable -> -EFAULT".to_string();
    };
    let target = guest_abs(vcwd, &p);
    let host = format!("{rootfs}{target}");
    use std::os::unix::fs::PermissionsExt;
    match std::fs::set_permissions(
        &host,
        std::fs::Permissions::from_mode(mode),
    ) {
        Ok(()) => {
            skip_syscall(pid, regs, pend, 0);
            format!("chmod(15) '{p}' -> '{host}' proxied mode=0{mode:o}")
        }
        Err(e) => {
            let en = e.raw_os_error().unwrap_or(libc::EIO);
            skip_syscall(pid, regs, pend, -(en as i64));
            format!("chmod(15) '{p}' -> '{host}' proxied (errno {en})")
        }
    }
}

/// Compat ftruncate(93), proxied by the supervisor itself.
/// Same allowlist family as rmdir/chmod: the guest's 2011-era
/// call has no place in the host's 2024 app policy (modern
/// bionic routes ftruncate through ftruncate64), so a passed-
/// through call is trapped — 2.3.7's init died exactly there,
/// sizing its property workspace (0.3.3 device run: ftruncate
/// passed, then SIGSYS with nr_reg=93, fd=4, len=0x8000). An fd
/// cannot be proxied by path rewriting, so the supervisor
/// resolves the guest's fd through /proc/<pid>/fd/<fd> and
/// truncates the same inode under its own fd; the guest's
/// descriptor observes the new length.
fn entry_ftruncate(pid: i32, regs: &mut Regs, pend: &mut Pending) -> String {
    let fd = regs.arg(0) as i32;
    let len = regs.arg(1) as u64;
    let link = format!("/proc/{pid}/fd/{fd}");
    let target = match std::fs::read_link(&link) {
        Ok(t) => {
            let s = t.to_string_lossy().into_owned();
            s.strip_suffix(" (deleted)").unwrap_or(&s).to_string()
        }
        Err(e) => {
            let en = e.raw_os_error().unwrap_or(libc::EBADF);
            skip_syscall(pid, regs, pend, -(en as i64));
            return format!("ftruncate(93) fd={fd} unresolvable (errno {en})");
        }
    };
    match std::fs::OpenOptions::new().write(true).open(&target) {
        Ok(f) => match f.set_len(len) {
            Ok(()) => {
                skip_syscall(pid, regs, pend, 0);
                format!("ftruncate(93) fd={fd} len={len} proxied via '{target}'")
            }
            Err(e) => {
                let en = e.raw_os_error().unwrap_or(libc::EIO);
                skip_syscall(pid, regs, pend, -(en as i64));
                format!("ftruncate(93) fd={fd} proxied (errno {en})")
            }
        },
        Err(e) => {
            let en = e.raw_os_error().unwrap_or(libc::EIO);
            skip_syscall(pid, regs, pend, -(en as i64));
            format!("ftruncate(93) fd={fd} open '{target}' failed (errno {en})")
        }
    }
}

/// Unix-socket bind/connect: virtualize the sockaddr path.
/// The path argument of bind(2)/connect(2) does not travel in a
/// register — it sits inside the sockaddr_un in guest memory,
/// where the path-translation machinery never sees it. Left
/// alone, a guest binding "/dev/socket/property_service" binds
/// the HOST's path: Gingerbread init collided with the host's
/// own live property-service socket (EADDRINUSE), the socket
/// never came up, and check_startup exit(1)'d the whole boot
/// (0.3.4 device run). The supervisor therefore rewrites the
/// path inside the guest's sockaddr to the translated host path
/// for the duration of the call and restores the original bytes
/// at the exit stop — the guest keeps seeing its own path (its
/// later chown/chmod of the socket node depend on that). The
/// path field is capped at 108 bytes; our rootfs paths fit.
/// Abstract sockets (leading NUL) and non-Unix families pass
/// untouched.
fn entry_unix_sockaddr(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    nr: u64,
    compat: bool,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    let name = nr_name(compat, nr);
    let addr_ptr = regs.arg(1);
    let addrlen = (regs.arg(2) as usize).min(512);
    if addrlen < 3 {
        return format!("{name}({nr}) pass (short sockaddr)");
    }
    let mut buf = vec![0u8; addrlen];
    let got = match read_mem(pid, addr_ptr, &mut buf) {
        Ok(n) => n,
        Err(_) => return format!("{name}({nr}) pass (sockaddr unreadable)"),
    };
    buf.truncate(got);
    if buf.len() < 3 || u16::from_ne_bytes([buf[0], buf[1]]) != libc::AF_UNIX as u16 {
        return format!("{name}({nr}) pass (non-unix sockaddr)");
    }
    if buf[2] == 0 {
        return format!("{name}({nr}) pass (abstract unix socket)");
    }
    let path_end = buf[2..]
        .iter()
        .position(|&b| b == 0)
        .map(|i| 2 + i)
        .unwrap_or(buf.len());
    let guest_path = String::from_utf8_lossy(&buf[2..path_end]).into_owned();
    let host = format!("{rootfs}{}", guest_abs(vcwd, &guest_path));
    if host.len() + 3 > 110 {
        return format!(
            "{name}({nr}) unix '{guest_path}' NOT rewritten (host path too long), passed"
        );
    }
    let mut newbuf = Vec::with_capacity(host.len() + 3);
    newbuf.extend_from_slice(&buf[0..2]);
    newbuf.extend_from_slice(host.as_bytes());
    newbuf.push(0);
    pend.mem_restore = Some((addr_ptr, buf));
    if write_mem(pid, addr_ptr, &newbuf).is_err() {
        pend.mem_restore = None;
        return format!("{name}({nr}) unix '{guest_path}' rewrite failed, passed");
    }
    regs.set_arg(2, newbuf.len() as u64);
    format!("{name}({nr}) unix '{guest_path}' -> '{host}' (sockaddr rewritten)")
}

/// Compat chown(182) / chown32(212), proxied by the supervisor
/// itself. The android12 policy inputs carry no chown stub at
/// all — SYSCALLS.TXT lists only fchown/fchownat (modern bionic
/// implements chown() as an fchownat wrapper) — so the call is
/// in the same trap family as rmdir/chmod, and it sits on a
/// proven path: create_socket chowns the socket node right
/// after bind (util.c:148), where a trap would kill init
/// mid-startup. The supervisor performs the chown on the
/// translated host path and returns its honest result
/// (chowning to uid 0 from the app's uid yields EPERM, which
/// create_socket ignores — faithful semantics, no fakery).
fn entry_chown(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    nr: u64,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    let name = if nr == 212 { "chown32" } else { "chown" };
    let addr = regs.arg(0);
    let owner = regs.arg(1) as u32;
    let group = regs.arg(2) as u32;
    let Some(p) = read_path(pid, addr) else {
        skip_syscall(pid, regs, pend, -EFAULT);
        return format!("{name}({nr}) path unreadable -> -EFAULT");
    };
    let host = format!("{rootfs}{}", guest_abs(vcwd, &p));
    let cstr = match std::ffi::CString::new(host.as_bytes()) {
        Ok(c) => c,
        Err(_) => {
            skip_syscall(pid, regs, pend, -(libc::EINVAL as i64));
            return format!("{name}({nr}) '{p}' bad path -> -EINVAL");
        }
    };
    let r = unsafe { libc::chown(cstr.as_ptr(), owner, group) };
    if r == 0 {
        skip_syscall(pid, regs, pend, 0);
        format!("{name}({nr}) '{p}' -> '{host}' proxied uid={owner} gid={group}")
    } else {
        let en = errno();
        skip_syscall(pid, regs, pend, -(en as i64));
        format!("{name}({nr}) '{p}' -> '{host}' proxied (errno {en})")
    }
}

/// Compat rmdir(40), proxied by the supervisor itself. The
/// 32-bit app seccomp allowlist does not contain rmdir at all
/// (checked against bionic android12-release policy inputs:
/// rmdir appears in neither SYSCALLS.TXT nor any
/// SECCOMP_ALLOWLIST, while unlink was explicitly added for
/// lp32), so a passed-through rmdir is trapped and its caller
/// dies of SIGSYS — 0.2.8 device runs, twice, at the same pc.
/// Cancelling at entry and performing the removal on the
/// translated host path gives the guest exact same-filesystem
/// errno semantics; the standard inject path (and its SIGSYS
/// rescue) applies as for chdir.
fn entry_rmdir(
    pid: i32,
    rootfs: &str,
    vcwd: &str,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    let addr = regs.arg(0);
    let Some(p) = read_path(pid, addr) else {
        skip_syscall(pid, regs, pend, -EFAULT);
        return "rmdir(40) path unreadable -> -EFAULT".to_string();
    };
    let target = guest_abs(vcwd, &p);
    let host = format!("{rootfs}{target}");
    match std::fs::remove_dir(&host) {
        Ok(()) => {
            skip_syscall(pid, regs, pend, 0);
            format!("rmdir(40) '{p}' -> '{host}' proxied")
        }
        Err(e) => {
            let en = e.raw_os_error().unwrap_or(libc::EIO);
            skip_syscall(pid, regs, pend, -(en as i64));
            format!("rmdir(40) '{p}' -> '{host}' proxied (errno {en})")
        }
    }
}

/// Resolve a canonical guest path through one symlink level inside
/// the rootfs. Returns (final guest path, entity exists there).
fn resolve_guest_target(rootfs: &str, abs: &str) -> (String, bool) {
    let host = format!("{rootfs}{abs}");
    match std::fs::symlink_metadata(&host) {
        Ok(md) => {
            if md.file_type().is_symlink() {
                if let Ok(target) = std::fs::read_link(&host) {
                    let t = target.to_string_lossy().into_owned();
                    let resolved = if t.starts_with('/') {
                        normalize_path_str(&t)
                    } else {
                        let parent = match abs.rfind('/') {
                            Some(0) | None => "/".to_string(),
                            Some(i) => abs[..i].to_string(),
                        };
                        normalize_path_str(&format!("{parent}/{t}"))
                    };
                    return (resolved, true);
                }
            }
            (abs.to_string(), true)
        }
        Err(_) => (abs.to_string(), false),
    }
}

/// Internal execve/execveat (M1 spec section 2b). Only the busybox
/// binary itself may truly exec, and only from its nativeLibraryDir
/// home: the rootfs lives in filesDir, where exec is forbidden.
/// argv and envp are never touched (busybox dispatches on argv[0]).
/// Returns (log description, regs were modified).
fn entry_exec(
    pid: i32,
    rootfs: &str,
    bb_native: &str,
    vcwd: &str,
    compat: bool,
    nr: u64,
    regs: &mut Regs,
    pend: &mut Pending,
) -> (String, bool) {
    let name = nr_name(compat, nr);
    let (path_arg, dirfd) = if nr == nr_execve(compat) {
        (0usize, AT_FDCWD)
    } else {
        (1usize, regs.arg(0) as i64)
    };
    let addr = regs.arg(path_arg);
    let Some(gpath) = read_path(pid, addr) else {
        return (format!("{name}({nr}) path@{addr:#x} (unreadable, passed)"), false);
    };
    let rewrite_to_bb = |regs: &mut Regs| -> bool {
        let mut cursor = regs.sp().saturating_sub(256);
        match scratch_write(pid, &mut cursor, bb_native) {
            Some(scratch) => {
                regs.set_arg(path_arg, scratch);
                true
            }
            None => false,
        }
    };
    if gpath == "/proc/self/exe" {
        // Standalone ash re-execs itself by this name to run an
        // applet; the guest really is bb_native, so point it home.
        let ok = rewrite_to_bb(regs);
        return (format!("{name}({nr}) '/proc/self/exe' -> busybox (native)"), ok);
    }
    if !gpath.starts_with('/') && dirfd != AT_FDCWD {
        // execveat relative to a real dirfd: out of M1 scope.
        skip_syscall(pid, regs, pend, -EACCES);
        return (format!("{name}({nr}) '{gpath}' BLOCKED (dirfd-relative) -> -EACCES"), true);
    }
    let abs = guest_abs(vcwd, &gpath);
    if abs == "/bin/busybox" {
        let ok = rewrite_to_bb(regs);
        return (format!("exec '{gpath}' -> busybox (native)"), ok);
    }
    let (final_abs, exists) = resolve_guest_target(rootfs, &abs);
    if exists && final_abs == "/bin/busybox" {
        let ok = rewrite_to_bb(regs);
        return (format!("exec '{gpath}' -> busybox (native)"), ok);
    }
    if exists {
        // A real rootfs file that is not busybox: filesDir cannot be
        // exec'd, and M1 opens no other door. #! scripts land here.
        let host = format!("{rootfs}{abs}");
        let mut note = "";
        if let Ok(mut f) = std::fs::File::open(&host) {
            use std::io::Read;
            let mut head = [0u8; 2];
            if f.read_exact(&mut head).is_ok() && &head == b"#!" {
                note = " [script, unsupported in M1]";
            }
        }
        skip_syscall(pid, regs, pend, -EACCES);
        return (
            format!("exec '{gpath}' BLOCKED (rootfs file, not busybox) -> -EACCES{note}"),
            true,
        );
    }
    // Does not exist in the rootfs: translate and let the kernel
    // deliver the natural verdict (usually ENOENT) -- the shell's
    // PATH search depends on trying candidates one by one.
    let host = format!("{rootfs}{abs}");
    let mut cursor = regs.sp().saturating_sub(256);
    match scratch_write(pid, &mut cursor, &host) {
        Some(scratch) => {
            regs.set_arg(path_arg, scratch);
            (format!("exec '{gpath}' -> '{host}' (pass, kernel verdict)"), true)
        }
        None => (format!("exec '{gpath}' (scratch write failed, passed)"), false),
    }
}

// ---- guest output forwarding: one pipe carries the whole tree's
// stdout/stderr (children inherit the root's fds 1/2) ----
fn spawn_guest_reader(fd: i32) -> std::thread::JoinHandle<()> {
    use std::io::Read;
    use std::os::unix::io::FromRawFd;
    std::thread::spawn(move || {
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        let mut buf = [0u8; 1024];
        let mut cur: Vec<u8> = Vec::new();
        loop {
            match f.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => {
                    for &b in &buf[..n] {
                        if b == b'\n' {
                            emit("guest", &String::from_utf8_lossy(&cur));
                            cur.clear();
                        } else {
                            cur.push(b);
                        }
                    }
                }
                Err(_) => break,
            }
        }
        if !cur.is_empty() {
            emit("guest", &String::from_utf8_lossy(&cur));
        }
    })
}

fn uts_field(field: &[libc::c_char]) -> String {
    field
        .iter()
        .take_while(|&&c| c != 0)
        .map(|&c| (c as u8) as char)
        .collect()
}

/// Kernel identity for the self-check line. SELinux denies app
/// processes read access to /proc/version on real devices, but
/// uname(2) is a plain syscall and always available.
fn kernel_release() -> String {
    let mut uts: libc::utsname = unsafe { std::mem::zeroed() };
    if unsafe { libc::uname(&mut uts) } != 0 {
        return format!("<uname failed: errno={}>", errno());
    }
    format!("{} {}", uts_field(&uts.sysname), uts_field(&uts.release))
}

fn read_context() -> String {
    match std::fs::read("/proc/self/attr/current") {
        Ok(bytes) => String::from_utf8_lossy(&bytes)
            .trim_matches(|c| c == '\0' || c == '\n' || c == ' ')
            .to_string(),
        Err(e) => format!("<unreadable: {e}>"),
    }
}

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    if argv.len() < 3 {
        sup!("usage: libsupervisor.so <rootfs_abs_path> <guest_abs_path> [-- guest_argv...]");
        std::process::exit(2);
    }
    let rootfs = argv[1].clone();
    let guest_path = argv[2].clone();
    // Optional "--bb <path>" (before "--"): the binary applet
    // execs inside the rootfs are rewritten to. Defaults to the
    // guest itself (M0-M1: the root guest IS busybox). A session
    // whose root is another binary (S3: Android init) passes the
    // busybox payload explicitly so its services can run applets.
    let bb_path = match argv.iter().position(|a| a == "--bb") {
        Some(i) if i + 1 < argv.len() && argv[i + 1] != "--" => argv[i + 1].clone(),
        _ => guest_path.clone(),
    };
    // Guest argv: everything after an optional "--", argv[0] first.
    // Defaults to the M0 single-word argv when absent.
    let guest_args: Vec<String> = match argv.iter().position(|a| a == "--") {
        Some(i) if i + 1 < argv.len() => argv[i + 1..].to_vec(),
        _ => vec!["guest".to_string()],
    };

    // Startup self-check lines: the evidence that separates
    // "device policy" from "our bug" on the first run.
    sup!("supervisor pid={}", std::process::id());
    sup!("kernel: {}", kernel_release());
    sup!("selinux: {}", read_context());
    sup!("rootfs={rootfs} guest={guest_path}");
    // The whole tree shares the guest binary's personality: the
    // rootfs can only ever exec that one binary (see entry_exec).
    let guest_compat = match guest_is_compat(&guest_path) {
        Some(c) => {
            sup!(
                "guest ELF: {} -> {} tracee mode",
                if c { "ELF32/ARM" } else { "ELF64/AArch64" },
                if c { "compat" } else { "native" }
            );
            c
        }
        None => {
            sup!("WARN: guest ELF header unreadable or not ARM-family; assuming native 64-bit");
            false
        }
    };

    unsafe {
        libc::signal(libc::SIGTERM, on_sigterm as usize as libc::sighandler_t);
    }

    let mut pipe_fds = [0i32; 2];
    if unsafe { libc::pipe2(pipe_fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        sup!("pipe2 failed: errno={}", errno());
        std::process::exit(1);
    }
    let (pipe_rd, pipe_wr) = (pipe_fds[0], pipe_fds[1]);

    // Build exec arguments before fork: after fork the child may
    // only use async-signal-safe calls.
    let guest_c = CString::new(guest_path.clone()).unwrap();
    let guest_arg_cs: Vec<CString> =
        guest_args.iter().map(|a| CString::new(a.clone()).unwrap()).collect();
    let mut child_argv: Vec<*const libc::c_char> =
        guest_arg_cs.iter().map(|c| c.as_ptr()).collect();
    child_argv.push(std::ptr::null());
    let env_path = CString::new("PATH=/bin:/usr/bin").unwrap();
    let env_home = CString::new("HOME=/").unwrap();
    let child_envp: [*const libc::c_char; 3] =
        [env_path.as_ptr(), env_home.as_ptr(), std::ptr::null()];

    let pid = unsafe { libc::fork() };
    if pid < 0 {
        sup!("fork failed: errno={}", errno());
        std::process::exit(1);
    }
    if pid == 0 {
        // ---- guest root child ----
        unsafe {
            libc::close(pipe_rd);
            if pipe_wr != 1 {
                libc::dup2(pipe_wr, 1);
            }
            if pipe_wr != 2 {
                libc::dup2(pipe_wr, 2);
            }
            if pipe_wr > 2 {
                libc::close(pipe_wr);
            }
            let devnull = libc::open(b"/dev/null\0".as_ptr() as *const libc::c_char, libc::O_RDONLY);
            if devnull >= 0 {
                if devnull != 0 {
                    libc::dup2(devnull, 0);
                    libc::close(devnull);
                }
            }
            // The real host cwd stays at "/" for the whole tree; all
            // relative resolution is virtualized through the vcwd.
            libc::chdir(b"/\0".as_ptr() as *const libc::c_char);
            ptrace4(PTRACE_TRACEME, 0, std::ptr::null_mut(), std::ptr::null_mut());
            libc::raise(libc::SIGSTOP);
            libc::execve(guest_c.as_ptr(), child_argv.as_ptr(), child_envp.as_ptr());
            libc::_exit(127);
        }
    }

    // ---- supervisor (parent) ----
    unsafe { libc::close(pipe_wr) };
    GUEST_PID.store(pid, Ordering::Relaxed);
    let reader = spawn_guest_reader(pipe_rd);
    sup!("guest pid={pid}");

    let root_pid = pid;
    let mut procs: HashMap<i32, ProcState> = HashMap::new();
    // The root starts in the native personality: until its launch
    // exec completes it is still our own fork child running the
    // supervisor image. It flips at the exec event (see below).
    procs.insert(root_pid, ProcState::new("/", true, false));
    let mut root_launched = false;
    // Keyed by (compat, nr): the root's launch execve is counted
    // under the native table, everything else under the guest's.
    let mut seen: HashSet<(bool, u64)> = HashSet::new();
    let mut counts: HashMap<(bool, u64), u64> = HashMap::new();

    // ---- main tracing loop over the whole guest tree ----
    'main_loop: loop {
        let mut status: i32 = 0;
        let r = unsafe { libc::waitpid(-1, &mut status, WALL) };
        if r < 0 {
            let e = errno();
            if e == libc::EINTR {
                continue;
            }
            if e == libc::ECHILD {
                sup!("waitpid: no tracees left");
                break;
            }
            sup!("waitpid failed: errno={e}");
            break;
        }
        let pid = r;

        if libc::WIFEXITED(status) || libc::WIFSIGNALED(status) {
            let is_root = pid == root_pid;
            if libc::WIFEXITED(status) {
                if is_root {
                    sup!("GUEST_EXITED code={}", libc::WEXITSTATUS(status));
                }
                sup!("PROC_EXITED pid={pid} code={}", libc::WEXITSTATUS(status));
            } else {
                if is_root {
                    sup!("GUEST_SIGNALED sig={}", libc::WTERMSIG(status));
                }
                sup!("PROC_SIGNALED pid={pid} sig={}", libc::WTERMSIG(status));
            }
            procs.remove(&pid);
            if is_root {
                // The session ends with the root: kill whatever is
                // left of the tree and drain the exit reports.
                let rest: Vec<i32> = procs.keys().cloned().collect();
                if !rest.is_empty() {
                    sup!("root done; killing {} remaining tracee(s)", rest.len());
                    for p in &rest {
                        unsafe { libc::kill(*p, libc::SIGKILL) };
                    }
                    loop {
                        let mut st2: i32 = 0;
                        let r2 = unsafe { libc::waitpid(-1, &mut st2, WALL) };
                        if r2 < 0 || procs.is_empty() {
                            break;
                        }
                        sup!("PROC_EXITED pid={r2} (cleanup)");
                        procs.remove(&r2);
                    }
                }
                break 'main_loop;
            }
            continue;
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        let sig = libc::WSTOPSIG(status);
        let event = status >> 16;

        // First sight of a pid (its initial stop may beat the
        // parent's fork event): register it with a root vcwd; the
        // fork event refreshes the vcwd if it arrives later.
        if !procs.contains_key(&pid) {
            sup!("new tracee pid={pid} (registered on first stop)");
            procs.insert(pid, ProcState::new("/", false, guest_compat));
        }

        // Initial stop of a fresh tracee: set the option set,
        // swallow the initial SIGSTOP, and continue it. A tracee
        // cannot produce syscall stops before TRACESYSGOOD is set.
        if !procs.get(&pid).map(|p| p.options_set).unwrap_or(false) {
            let ok = set_trace_options(pid);
            if pid == root_pid {
                sup!("ptrace options set (TRACESYSGOOD|TRACEEXEC|TRACEFORK|TRACEVFORK|TRACECLONE|EXITKILL)");
            } else {
                sup!("ptrace options set pid={pid}");
            }
            if let Some(p) = procs.get_mut(&pid) {
                p.options_set = ok;
                p.started = true;
            }
            cont_syscall(pid, if sig == SIGSTOP { 0 } else { sig });
            continue;
        }

        if sig == SYSCALL_STOP_SIG {
            let Some(proc) = procs.get_mut(&pid) else {
                cont_syscall(pid, 0);
                continue;
            };
            if !proc.expect_exit {
                // ---- syscall-entry stop ----
                proc.syscall_seen = true;
                let Some(mut regs) = get_regs(pid, proc.compat) else {
                    cont_syscall(pid, 0);
                    continue;
                };
                let nr = regs.nr();
                let mut pend = Pending {
                    nr,
                    desc: None,
                    inject: None,
                    applied: false,
                    mem_restore: None,
                };
                let mut dirty = false;
                if (nr == nr_execve(proc.compat) || nr == nr_execveat(proc.compat))
                    && pid == root_pid
                    && !root_launched
                {
                    // The guest root's own launch exec must pass;
                    // every later exec goes through the exec rules.
                    *counts.entry((proc.compat, nr)).or_insert(0) += 1;
                    if seen.insert((proc.compat, nr)) {
                        sys!(
                            "{}({}) pass (guest launch exec, allowed)",
                            nr_name(proc.compat, nr),
                            nr
                        );
                    }
                } else if nr == nr_execve(proc.compat) || nr == nr_execveat(proc.compat) {
                    let (desc, d) = entry_exec(
                        pid,
                        &rootfs,
                        &bb_path,
                        &proc.vcwd,
                        proc.compat,
                        nr,
                        &mut regs,
                        &mut pend,
                    );
                    pend.desc = Some(desc);
                    dirty = d;
                } else if nr == nr_chdir(proc.compat) {
                    let (desc, new_vcwd) = entry_chdir(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        proc.compat,
                        &mut regs,
                        &mut pend,
                    );
                    pend.desc = Some(desc);
                    dirty = true;
                    if let Some(v) = new_vcwd {
                        proc.vcwd = v;
                    }
                } else if proc.compat && nr == 14 {
                    // Compat mknod: /dev/* faked (entry_mknod_dev).
                    match entry_mknod_dev(pid, &proc.vcwd, &mut regs, &mut pend) {
                        Some(desc) => {
                            pend.desc = Some(desc);
                        }
                        None => {
                            pend.desc = Some(entry_translate(
                                pid,
                                &rootfs,
                                &proc.vcwd,
                                proc.compat,
                                nr,
                                &mut regs,
                            ));
                        }
                    }
                    dirty = true;
                } else if proc.compat && nr == 15 {
                    // Compat chmod: proxied (see entry_chmod).
                    pend.desc = Some(entry_chmod(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if proc.compat && nr == 93 {
                    // Compat ftruncate: proxied (see
                    // entry_ftruncate).
                    pend.desc = Some(entry_ftruncate(pid, &mut regs, &mut pend));
                    dirty = true;
                } else if (proc.compat && (nr == 282 || nr == 283))
                    || (!proc.compat && (nr == 200 || nr == 203))
                {
                    // bind/connect: the sockaddr path lives in
                    // guest memory; rewrite it for the call's
                    // duration (see entry_unix_sockaddr). The
                    // call itself passes through.
                    pend.desc = Some(entry_unix_sockaddr(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        nr,
                        proc.compat,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if proc.compat && (nr == 182 || nr == 212) {
                    // Compat chown/chown32: proxied (see
                    // entry_chown).
                    pend.desc = Some(entry_chown(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        nr,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if proc.compat && nr == 40 {
                    // Compat rmdir: proxied (see entry_rmdir).
                    pend.desc = Some(entry_rmdir(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if is_t_dirfd_path(proc.compat, nr)
                    || is_t_two_paths(proc.compat, nr)
                    || is_t_symlinkat(proc.compat, nr)
                    || is_t_path0(proc.compat, nr)
                {
                    pend.desc = Some(entry_translate(
                        pid,
                        &rootfs,
                        &proc.vcwd,
                        proc.compat,
                        nr,
                        &mut regs,
                    ));
                    dirty = true;
                } else if is_setid_emulated(proc.compat, nr) {
                    // Cancel before the kernel (and its seccomp
                    // filter) ever evaluates it; answer 0 at the
                    // exit stop via the standard inject path.
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(format!(
                        "{}({}) emulated (return 0)",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else if is_faked(proc.compat, nr) {
                    pend.desc = Some(entry_fake(
                        pid,
                        &proc.vcwd,
                        proc.compat,
                        nr,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if is_blocked(proc.compat, nr) {
                    skip_syscall(pid, &mut regs, &mut pend, -ENOSYS);
                    pend.desc = Some(format!(
                        "{}({}) BLOCKED -> -ENOSYS",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else {
                    // P class and unlisted: pass, log first occurrence.
                    *counts.entry((proc.compat, nr)).or_insert(0) += 1;
                    if seen.insert((proc.compat, nr)) {
                        sys!(
                            "{}({}) pass (first occurrence)",
                            nr_name(proc.compat, nr),
                            nr
                        );
                    }
                }
                if dirty {
                    set_regs(pid, &regs);
                }
                proc.pending = Some(pend);
                proc.expect_exit = true;
                cont_syscall(pid, 0);
            } else {
                // ---- syscall-exit stop ----
                if let Some(mut pend) = proc.pending.take() {
                    if let Some(mut regs) = get_regs(pid, proc.compat) {
                        let mut ret = regs.retval();
                        if let Some(v) = pend.inject {
                            regs.set_retval(v);
                            if set_regs(pid, &regs) {
                                pend.applied = true;
                            }
                            ret = v;
                        }
                        if let Some(d) = &pend.desc {
                            sys!("{d} => {ret}");
                        }
                    }
                    if let Some((addr, orig)) = &pend.mem_restore {
                        // Undo a for-the-duration rewrite (the
                        // unix sockaddr path): the guest must
                        // keep seeing its own bytes.
                        let _ = write_mem(pid, *addr, orig);
                    }
                    if pend.inject.is_some() {
                        // A faked syscall's record outlives its exit
                        // stop. On device, the SIGSYS belonging to a
                        // faked call can be delivered *after* the
                        // exit stop has already settled the fake
                        // (0.2.4 setgid, 0.2.6 getcwd), and the
                        // signal-stop handler can only recognise
                        // that SIGSYS as ours to rescue while the
                        // record is still here. The record is never
                        // consulted again otherwise: the next entry
                        // stop for this pid overwrites it.
                        proc.pending = Some(pend);
                    }
                }
                proc.expect_exit = false;
                cont_syscall(pid, 0);
            }
        } else if sig == SIGTRAP && event == PTRACE_EVENT_EXEC {
            // The exec event stop sits between the execve entry and
            // exit stops; surface the entry's description here and
            // clear it so the exit stop stays silent (M0 pairing).
            if let Some(p) = procs.get_mut(&pid) {
                if let Some(pend) = &mut p.pending {
                    if let Some(d) = pend.desc.take() {
                        sys!("{d} (exec completed)");
                    }
                }
            }
            if pid == root_pid {
                root_launched = true;
                // From here on the root runs the guest image: its
                // registers and syscall numbers switch to the
                // guest's personality.
                if let Some(p) = procs.get_mut(&pid) {
                    p.compat = guest_compat;
                }
                sup!("guest exec completed (launch)");
            } else {
                sup!("exec completed pid={pid}");
            }
            cont_syscall(pid, 0);
        } else if sig == SIGTRAP
            && (event == PTRACE_EVENT_FORK
                || event == PTRACE_EVENT_VFORK
                || event == PTRACE_EVENT_CLONE)
        {
            if let Some(child) = get_event_msg(pid) {
                let child = child as i32;
                let (parent_vcwd, parent_compat) = procs
                    .get(&pid)
                    .map(|p| (p.vcwd.clone(), p.compat))
                    .unwrap_or_else(|| ("/".to_string(), guest_compat));
                match procs.get_mut(&child) {
                    Some(cp) => {
                        // Registered early by its own initial stop.
                        // No syscall of the child has been processed
                        // yet, so no translation has consumed its
                        // vcwd and adopting the parent's current
                        // vcwd is still exact.
                        if !cp.syscall_seen {
                            cp.vcwd = parent_vcwd;
                            cp.compat = parent_compat;
                        }
                    }
                    None => {
                        procs.insert(child, ProcState::new(&parent_vcwd, false, parent_compat));
                    }
                }
                let ev_name = match event {
                    x if x == PTRACE_EVENT_FORK => "fork",
                    x if x == PTRACE_EVENT_VFORK => "vfork",
                    _ => "clone",
                };
                sup!("tracee born: parent={pid} child={child} ({ev_name})");
            }
            cont_syscall(pid, 0);
        } else if sig == SIGTRAP {
            cont_syscall(pid, 0);
        } else {
            // Signal-delivery stop. Default: reinject the signal
            // unchanged -- a trapped guest dies by this SIGSYS
            // reinjection; dump the kernel's siginfo first so the
            // log names the syscall the seccomp filter objected to.
            //
            // Exception: a SIGSYS that belongs to a syscall we
            // faked. On device (0.2.4, 0.2.6) the trap signal for a
            // faked call arrives after the fake has been applied --
            // in both observed cases after the exit stop already
            // settled it -- and kills a guest whose call we had
            // already answered. While this pid still holds the
            // fake's record, swallow the signal instead: make sure
            // the fabricated result is in place (a getcwd-style
            // buffer was already written at the entry stop; only
            // the return value can still be outstanding), drop the
            // record, and continue with no signal delivered. The
            // record is held past the exit stop for exactly this
            // (see the exit-stop path). expect_exit is deliberately
            // left alone: if this stop arrived before the fake's
            // exit stop, that exit stop still follows, and the exit
            // path already tolerates a missing record.
            let mut deliver = sig;
            if matches!(sig, 4 | 6 | 7 | 8 | 11) {
                // Fatal-signal forensics (purely additive): a
                // genuine guest crash (SIGSEGV and friends) is
                // far easier to place with its pc and fault
                // address than from the bare GUEST_SIGNALED line
                // that follows at reaping time. Motivated by
                // 2.3.7 init's SIGSEGV at its first action
                // (0.3.1 device run), which the log could only
                // bracket, not locate.
                let fcompat = procs
                    .get(&pid)
                    .map(|p| p.compat)
                    .unwrap_or(guest_compat);
                let pc = get_regs(pid, fcompat).map(|r| r.pc()).unwrap_or(0);
                let mut buf = [0u8; 128];
                let ok = ptrace4(
                    PTRACE_GETSIGINFO,
                    pid,
                    std::ptr::null_mut(),
                    buf.as_mut_ptr() as *mut libc::c_void,
                ) == 0;
                if ok {
                    let addr = if fcompat {
                        u32::from_ne_bytes(buf[12..16].try_into().unwrap()) as u64
                    } else {
                        u64::from_ne_bytes(buf[16..24].try_into().unwrap())
                    };
                    sup!(
                        "FATAL sig={sig} pid={pid} pc=0x{pc:x} fault_addr=0x{addr:x}"
                    );
                } else {
                    sup!("FATAL sig={sig} pid={pid} pc=0x{pc:x} (no siginfo)");
                }
            }
            if sig == SIGSYS {
                let sig_compat = procs
                    .get(&pid)
                    .map(|p| p.compat)
                    .unwrap_or(guest_compat);
                dump_sigsys_info(pid, sig_compat);
                if let Some(proc) = procs.get_mut(&pid) {
                    let fake = proc
                        .pending
                        .as_ref()
                        .filter(|p| p.inject.is_some())
                        .map(|p| (p.nr, p.inject.unwrap(), p.applied));
                    if let Some((fnr, value, applied)) = fake {
                        let mut pc = 0u64;
                        if let Some(mut regs) = get_regs(pid, proc.compat) {
                            pc = regs.pc();
                            if !applied {
                                regs.set_retval(value);
                                set_regs(pid, &regs);
                            }
                        }
                        sup!(
                            "SIGSYS rescued pid={pid} fake={}({fnr}) pc=0x{pc:x}",
                            nr_name(proc.compat, fnr)
                        );
                        proc.pending = None;
                        deliver = 0;
                    }
                }
            }
            cont_syscall(pid, deliver);
        }
    }

    if !counts.is_empty() {
        let mut items: Vec<((bool, u64), u64)> = counts.into_iter().collect();
        items.sort_by_key(|((_, nr), _)| *nr);
        let parts: Vec<String> = items
            .iter()
            .map(|((c, nr), n)| format!("{}({})x{}", nr_name(*c, *nr), nr, n))
            .collect();
        sys!("pass-through summary: {}", parts.join(", "));
    }
    let _ = reader.join();
    sup!("supervisor done");
}
