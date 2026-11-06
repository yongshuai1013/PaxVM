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
use std::os::unix::fs::FileExt;
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
    fn set_pc(&mut self, v: u64) {
        match self {
            Regs::A64(r) => r.pc = v,
            Regs::A32(r) => r.uregs[15] = v as u32,
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
    /// Set the tracee-visible syscall-number register (x8 on
    /// AArch64, r7 on compat) to a different number.
    fn set_nr(&mut self, v: u64) {
        match self {
            Regs::A64(r) => r.regs[8] = v,
            Regs::A32(r) => r.uregs[7] = v as u32,
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
    /// When true, `inject` is a rescue-only fallback: the exit
    /// stop must NOT apply it (the real syscall result stands);
    /// it exists solely so a SIGSYS belonging to this call can
    /// be rescued with the fabricated value. Used by the
    /// accept -> accept4 rewrite (see entry_accept).
    rescue_only: bool,
    /// getsockopt(SO_PEERCRED) in flight: (optval, optlen)
    /// guest addresses. The call passes through; at the exit
    /// stop the returned ucred is rewritten to the peer's
    /// virtual credentials (see patch_peercred).
    peercred: Option<(u64, u64)>,
    /// A binder WRITE_READ parked at its entry stop: the ioctl
    /// was cancelled and pre-answered 0, but the tracee is NOT
    /// continued until the virtual driver has data for it (see
    /// complete_parked).
    binder_parked: bool,
    /// An mmap on a binder arena fd: (arena host path, map
    /// length). At the exit stop the returned address becomes
    /// the arena base for this thread.
    mmap_binder: Option<(String, u32)>,
}

struct ProcState {
    expect_exit: bool,
    pending: Option<Pending>,
    /// Virtual cwd in guest path space; "/" at birth, inherited
    /// across fork/vfork/clone, unchanged by exec.
    vcwd: String,
    /// Virtual signal mask for the compat sigprocmask
    /// proxy (0.9.25): bookkeeping only -- delivery is not
    /// filtered by it. See entry_sigprocmask.
    sigmask: u32,
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
            sigmask: 0,
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
    binder: &mut BinderState,
) -> String {
    // /dev/binder belongs to the virtual binder driver (S5):
    // the open is rerouted to a supervisor-owned arena file.
    // (This intercept lives here, not in the dispatch chain:
    // the generic path branch matches opens first.)
    if is_open_family(compat, nr) {
        let path_arg = if (compat && nr == 322) || (!compat && nr == 56) {
            1
        } else {
            0
        };
        if let Some(p) = read_path(pid, regs.arg(path_arg)) {
            if guest_abs(vcwd, &p) == "/dev/binder" {
                return entry_open_binder(pid, rootfs, compat, nr, regs, binder);
            }
            if guest_abs(vcwd, &p) == "/dev/ashmem" {
                return entry_open_ashmem(pid, rootfs, compat, nr, regs, binder);
            }
        }
    }
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
/// The get*id family: answered from the virtual credentials.
fn is_getid(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 24 | 47 | 49 | 50 | 199 | 200 | 201 | 202)
    } else {
        matches!(nr, 174 | 175 | 176 | 177)
    }
}

/// Which half of the virtual credential pair a get*id call asks
/// for: true = uid, false = gid (real and effective ids share
/// the virtual value; the guest world has no separate saved id).
fn getid_is_uid(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 24 | 49 | 199 | 201)
    } else {
        matches!(nr, 174 | 176)
    }
}

/// Apply an emulated set*id call to the virtual credentials.
/// Only the effective-id outcome is tracked (ruid/suid slots of
/// setre*/setres* are ignored beyond their effect on the
/// effective id); setfsuid/setfsgid/setgroups carry no tracked
/// state. A -1 argument leaves its slot unchanged.
fn apply_setid(compat: bool, nr: u64, regs: &Regs, creds: &mut (u32, u32)) {
    let a0 = regs.arg(0);
    let a1 = regs.arg(1);
    let neg = |v: u64| v == u64::MAX || v == 0xFFFF_FFFF;
    let set_either = |slot: &mut u32| {
        if !neg(a1) {
            *slot = a1 as u32;
        } else if !neg(a0) {
            *slot = a0 as u32;
        }
    };
    if compat {
        match nr {
            23 | 213 => creds.0 = a0 as u32, // setuid(32)
            46 | 214 => creds.1 = a0 as u32, // setgid(32)
            70 | 203 => set_either(&mut creds.0), // setreuid(32)
            71 | 204 => set_either(&mut creds.1), // setregid(32)
            164 | 208 => {
                if !neg(a1) {
                    creds.0 = a1 as u32;
                }
            } // setresuid(32): euid slot
            170 | 210 => {
                if !neg(a1) {
                    creds.1 = a1 as u32;
                }
            } // setresgid(32): egid slot
            _ => {}
        }
    } else {
        match nr {
            143 => creds.0 = a0 as u32, // setuid
            144 => creds.1 = a0 as u32, // setgid
            145 => set_either(&mut creds.0), // setreuid
            146 => set_either(&mut creds.1), // setregid
            147 => {
                if !neg(a1) {
                    creds.0 = a1 as u32;
                }
            } // setresuid
            149 => {
                if !neg(a1) {
                    creds.1 = a1 as u32;
                }
            } // setresgid
            _ => {}
        }
    }
}

/// Rewrite a SO_PEERCRED answer in the tracee's memory to the
/// peer's virtual credentials. The kernel reports the host app
/// uid for every guest process; a guest daemon that authorizes
/// by peer creds (GB init's property service is the first) must
/// see the guest-world identity instead: the peer tracee's
/// virtual uid/gid, or 0/0 for a peer that is not a tracee but
/// runs under our own host uid (the supervisor itself, e.g.
/// future brokers). Unknown peers keep the kernel's answer.
fn patch_peercred(
    pid: i32,
    optval: u64,
    optlen: u64,
    vcreds: &HashMap<i32, (u32, u32)>,
) {
    let mut lenb = [0u8; 4];
    if read_mem(pid, optlen, &mut lenb).is_err() {
        return;
    }
    let len = u32::from_ne_bytes(lenb);
    if len < 12 {
        sup!("WARN peercred: optlen {len} < 12 pid={pid}");
        return;
    }
    let mut b = [0u8; 12];
    if read_mem(pid, optval, &mut b).is_err() {
        return;
    }
    let peer = i32::from_ne_bytes(b[0..4].try_into().unwrap());
    let ruid = u32::from_ne_bytes(b[4..8].try_into().unwrap());
    let rgid = u32::from_ne_bytes(b[8..12].try_into().unwrap());
    let (vu, vg) = match vcreds.get(&peer) {
        Some(c) => *c,
        None => {
            if ruid == unsafe { libc::getuid() } as u32 {
                (0, 0)
            } else {
                return;
            }
        }
    };
    if vu == ruid && vg == rgid {
        return;
    }
    b[4..8].copy_from_slice(&vu.to_ne_bytes());
    b[8..12].copy_from_slice(&vg.to_ne_bytes());
    if write_mem(pid, optval, &b).is_ok() {
        sup!("peercred pid={pid}: peer {peer} uid {ruid} -> {vu}, gid {rgid} -> {vg}");
    }
}

// ---- S5: the supervisor is the binder driver ----
//
// The guest's /dev/binder is a per-opener sparse file under
// {rootfs}/.binder/; its mmap is flipped PRIVATE -> SHARED so
// supervisor pwrite()s are the guest's arena contents. All
// binder ioctls on such fds are emulated here: nodes, handles
// and parcel object translation follow the real driver's
// model, and looper/reply waits park the tracee at its entry
// stop until the driver has bytes for it. Design:
// ~/workspace/vm-engine-research/s5-binder-spec.md.
const BC_TRANSACTION: u32 = 0x4028_6300;
const BC_REPLY: u32 = 0x4028_6301;
const BC_FREE_BUFFER: u32 = 0x4004_6303;
const BC_INCREFS: u32 = 0x4004_6304;
const BC_ACQUIRE: u32 = 0x4004_6305;
const BC_RELEASE: u32 = 0x4004_6306;
const BC_DECREFS: u32 = 0x4004_6307;
const BC_INCREFS_DONE: u32 = 0x4008_6308;
const BC_ACQUIRE_DONE: u32 = 0x4008_6309;
const BC_ATTEMPT_ACQUIRE: u32 = 0x4008_630a;
const BC_REGISTER_LOOPER: u32 = 0x630b;
const BC_ENTER_LOOPER: u32 = 0x630c;
const BC_EXIT_LOOPER: u32 = 0x630d;
const BC_REQUEST_DEATH_NOTIFICATION: u32 = 0x4008_630e;
const BC_CLEAR_DEATH_NOTIFICATION: u32 = 0x4008_630f;
const BC_DEAD_BINDER_DONE: u32 = 0x4004_6310;
const BR_TRANSACTION: u32 = 0x8028_7202;
const BR_REPLY: u32 = 0x8028_7203;
const BR_DEAD_REPLY: u32 = 0x7205;
const BR_TRANSACTION_COMPLETE: u32 = 0x7206;
const BR_CLEAR_DEATH_NOTIFICATION_DONE: u32 = 0x8004_7210;
const BR_FAILED_REPLY: u32 = 0x7211;
const BR_DEAD_BINDER: u32 = 0x8004_720f;
const BR_INCREFS: u32 = 0x8008_7207;
const BR_ACQUIRE: u32 = 0x8008_7208;
const BINDER_WRITE_READ: u32 = 0xC018_6201;
const BINDER_SET_IDLE_TIMEOUT: u32 = 0x4008_6203;
const BINDER_SET_MAX_THREADS: u32 = 0x4004_6205;
const BINDER_SET_IDLE_PRIORITY: u32 = 0x4004_6206;
const BINDER_SET_CONTEXT_MGR: u32 = 0x4004_6207;
const BINDER_THREAD_EXIT: u32 = 0x4004_6208;
const BINDER_VERSION: u32 = 0xC004_6209;
const OBJ_BINDER: u32 = 0x7362_2A85;
const OBJ_FD: u32 = 0x6664_2A85;
const OBJ_WEAK_BINDER: u32 = 0x7762_2A85;
const OBJ_HANDLE: u32 = 0x7368_2A85;
const OBJ_WEAK_HANDLE: u32 = 0x7768_2A85;
const TF_ONE_WAY: u32 = 0x01;
const BINDER_ARENA_CAP: u32 = 8 * 1024 * 1024;

fn u32_at(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}
fn put_u32(b: &mut [u8], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_le_bytes());
}
fn read_mem_vec(pid: i32, addr: u64, len: usize) -> Option<Vec<u8>> {
    let mut buf = vec![0u8; len];
    match read_mem(pid, addr, &mut buf) {
        Ok(n) if n == len => Some(buf),
        _ => None,
    }
}

/// If `fd` in `pid` is one of our binder arena files, return
/// its host path (the arena's identity everywhere below).
fn fd_arena(pid: i32, fd: i32) -> Option<String> {
    let target = std::fs::read_link(format!("/proc/{pid}/fd/{fd}")).ok()?;
    let s = target.to_string_lossy().into_owned();
    if s.contains("/.binder/") {
        Some(s)
    } else {
        None
    }
}

// ---- virtual framebuffer (S6) ----
// Fixed geometry, era-typical (Nexus S class): 480x800,
// 32bpp, double buffered. The guest maps {rootfs}/.fb0
// (opened via device_map) and draws; FBIOPAN_DISPLAY /
// FBIOPUT_VSCREENINFO record the visible page's yoffset
// into {rootfs}/.fb-page, which the shell polls to present
// the right page. Struct layouts are the guest era's own
// (bionic 2.3.7 linux/fb.h, verified field by field).
const FB_W: u32 = 480;
const FB_H: u32 = 800;
const FB_PAGE_BYTES: u32 = FB_W * FB_H * 4;
const FB_TOTAL_BYTES: u32 = FB_PAGE_BYTES * 2;
const FBIOGET_VSCREENINFO: u32 = 0x4600;
const FBIOPUT_VSCREENINFO: u32 = 0x4601;
const FBIOGET_FSCREENINFO: u32 = 0x4602;
const FBIOPAN_DISPLAY: u32 = 0x4606;
const FBIO_WAITFORVSYNC: u32 = 0x4004_4620;

fn fd_is_fb(pid: i32, fd: i32) -> bool {
    match std::fs::read_link(format!("/proc/{pid}/fd/{fd}")) {
        Ok(t) => t.to_string_lossy().contains("/.fb0"),
        Err(_) => false,
    }
}

fn entry_fb_ioctl(
    pid: i32,
    rootfs: &str,
    req: u32,
    regs: &mut Regs,
    pend: &mut Pending,
) -> String {
    let arg = regs.arg(2);
    match req {
        FBIOGET_VSCREENINFO => {
            let mut v = [0u32; 40];
            v[0] = FB_W;
            v[1] = FB_H;
            v[2] = FB_W;
            v[3] = FB_H * 2;
            v[6] = 32;
            v[8] = 16;
            v[9] = 8; // red: offset 16, length 8
            v[11] = 8;
            v[12] = 8; // green: offset 8, length 8
            v[14] = 0;
            v[15] = 8; // blue: offset 0, length 8
            v[17] = 24;
            v[18] = 8; // transp: offset 24, length 8
            v[22] = 127; // height mm
            v[23] = 76; // width mm
            let mut bytes = [0u8; 160];
            for (i, w) in v.iter().enumerate() {
                bytes[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
            }
            let _ = write_mem(pid, arg, &bytes);
            skip_syscall(pid, regs, pend, 0);
            format!("fb GET_VSCREENINFO -> {FB_W}x{FB_H}x32 (virtual {FB_W}x{})", FB_H * 2)
        }
        FBIOGET_FSCREENINFO => {
            let mut b = [0u8; 68];
            b[0..5].copy_from_slice(b"paxfb");
            b[20..24].copy_from_slice(&FB_TOTAL_BYTES.to_le_bytes());
            b[32..36].copy_from_slice(&2u32.to_le_bytes()); // FB_VISUAL_TRUECOLOR
            b[38..40].copy_from_slice(&1u16.to_le_bytes()); // ypanstep
            b[44..48].copy_from_slice(&(FB_W * 4).to_le_bytes()); // line_length
            let _ = write_mem(pid, arg, &b);
            skip_syscall(pid, regs, pend, 0);
            "fb GET_FSCREENINFO".to_string()
        }
        FBIOPAN_DISPLAY | FBIOPUT_VSCREENINFO => {
            let mut buf = [0u8; 160];
            let yoff = if read_mem(pid, arg, &mut buf).is_ok() {
                u32_at(&buf, 20)
            } else {
                0
            };
            let _ = std::fs::write(format!("{rootfs}/.fb-page"), format!("{yoff}"));
            skip_syscall(pid, regs, pend, 0);
            // Content fingerprint of the page about to be
            // shown: nonzero-byte counts of its first and
            // last kilobyte, so the log can tell whether
            // the composer is actually writing new pixels
            // into this framebuffer or flipping stale ones.
            let fp = (|| -> Option<String> {
                use std::os::unix::fs::FileExt;
                let f = std::fs::File::open(format!("{rootfs}/.fb0")).ok()?;
                let base = (yoff as u64) * (FB_W as u64) * 4;
                let mut head = [0u8; 1024];
                let mut tail = [0u8; 1024];
                f.read_exact_at(&mut head, base).ok()?;
                f.read_exact_at(
                    &mut tail,
                    base + (FB_W as u64) * (FB_H as u64) * 2,
                )
                .ok()?;
                let nz = |b: &[u8]| b.iter().filter(|x| **x != 0).count();
                // "tail" is really the page's middle
                // kilobyte: the fallback animation's
                // glowing wordmark sits in the vertical
                // middle band, while head and true tail
                // are black bands of the animation itself.
                Some(format!("nz={}/{}", nz(&head), nz(&tail)))
            })()
            .unwrap_or_else(|| "nz=?".to_string());
            // Alongside the framebuffer page, fingerprint
            // every virtual ashmem file the same way, so
            // the log shows whether animation pixels ever
            // land in the shared buffers at all.
            let ash = (|| -> String {
                use std::os::unix::fs::FileExt;
                let mut parts: Vec<String> = Vec::new();
                let Ok(rd) = std::fs::read_dir(format!("{rootfs}/.ashmem")) else {
                    return String::new();
                };
                let mut names: Vec<_> = rd.flatten().collect();
                names.sort_by_key(|e| e.file_name());
                for e in names.iter().take(10) {
                    let Ok(f) = std::fs::File::open(e.path()) else {
                        continue;
                    };
                    let len = f.metadata().map(|m| m.len()).unwrap_or(0);
                    if len < 2048 {
                        continue;
                    }
                    let mut h = [0u8; 1024];
                    let mut m = [0u8; 1024];
                    if f.read_exact_at(&mut h, 0).is_err()
                        || f.read_exact_at(&mut m, len / 2).is_err()
                    {
                        continue;
                    }
                    let nz = |b: &[u8]| b.iter().filter(|x| **x != 0).count();
                    parts.push(format!(
                        "{}:{}/{}",
                        e.file_name().to_string_lossy(),
                        nz(&h),
                        nz(&m)
                    ));
                }
                if parts.is_empty() {
                    String::new()
                } else {
                    format!(" ash[{}]", parts.join(","))
                }
            })();
            format!("fb PAN yoffset={yoff} (page {}) {fp}{ash}", yoff / FB_H)
        }
        _ => {
            // FBIO_WAITFORVSYNC and anything else in the
            // intercepted set: succeed silently.
            skip_syscall(pid, regs, pend, 0);
            "fb ioctl (accepted)".to_string()
        }
    }
}

struct BinderProc {
    file: std::fs::File,
    /// thread pid -> guest address of this arena's mmap
    base: HashMap<i32, u32>,
    /// thread pid -> mapped length: deliveries must stay
    /// inside what the guest actually mapped (2.3 maps
    /// 128KB), not merely inside the arena file
    maplen: HashMap<i32, u32>,
    bump: u32,
    free: Vec<(u32, u32)>,
    used: HashMap<u32, u32>,
    /// handle -> node index (handle 0 is the context manager
    /// in every process and is never stored here)
    handles: HashMap<u32, usize>,
    next_handle: u32,
    /// BR byte streams for this arena's readers, split the
    /// way the real driver splits them: work addressed to
    /// the process as a whole (inbound transactions, ref and
    /// death notices) vs work addressed to one thread
    /// (replies, and the completion/error words of a thread's
    /// own in-flight call). A single shared queue misdelivers
    /// as soon as a guest process uses two binder threads:
    /// a reply meant for thread B can be drained by thread A
    /// (bootanimation's worker starved exactly this way).
    inbound: Vec<u8>,
    queues: HashMap<i32, Vec<u8>>,
    loopers: HashSet<i32>,
}

impl BinderProc {
    fn push_to(&mut self, pid: i32, bytes: &[u8]) {
        self.queues.entry(pid).or_default().extend_from_slice(bytes);
    }
    /// Bytes this thread may read now: its own addressed
    /// queue first, then (loopers only) the inbound stream.
    fn readable_for(&self, pid: i32) -> usize {
        let own = self.queues.get(&pid).map_or(0, |q| q.len());
        if self.loopers.contains(&pid) {
            own + self.inbound.len()
        } else {
            own
        }
    }
    /// Drains up to `max` bytes for this thread; returns the
    /// bytes plus how many came from the inbound stream.
    fn drain_for(&mut self, pid: i32, max: usize) -> (Vec<u8>, usize) {
        let mut out = Vec::new();
        if let Some(q) = self.queues.get_mut(&pid) {
            let n = q.len().min(max);
            out.extend(q.drain(..n));
        }
        let mut from_inbound = 0;
        if out.len() < max && self.loopers.contains(&pid) {
            let n = self.inbound.len().min(max - out.len());
            from_inbound = n;
            out.extend(self.inbound.drain(..n));
        }
        (out, from_inbound)
    }
}

struct BinderNode {
    owner: String,
    ptr: u32,
    cookie: u32,
    /// set when the owning arena's last thread exited:
    /// outstanding handles to it dead-reply, and a fresh
    /// registration creates a new node (S5c)
    dead: bool,
}

struct ParkedIoctl {
    bwr: u32,
    read_buf: u32,
    read_size: u32,
    write_consumed: u32,
}

struct ReplyWait {
    sender_pid: i32,
    sender_arena: String,
    cookie: u32,
    target_handle: u32,
}

#[derive(Default)]
struct BinderState {
    procs: HashMap<String, BinderProc>,
    nodes: Vec<BinderNode>,
    mgr_arena: Option<String>,
    mgr_node: Option<usize>,
    parked: HashMap<i32, ParkedIoctl>,
    /// target arena -> processes waiting for a reply from it
    waiters: HashMap<String, Vec<ReplyWait>>,
    /// node index -> (watcher arena, cookie) death watches
    watchers: HashMap<usize, Vec<(String, u32)>>,
    thread_arena: HashMap<i32, String>,
    noted: HashSet<String>,
    /// (node, receiver arena) pairs already sent a
    /// BR_INCREFS(/BR_ACQUIRE) notice to the node's owner:
    /// the real driver notifies once per new reference
    /// holder, not once per parcel (S5c)
    ref_notified: HashSet<(usize, String)>,
    /// Virtual ashmem (S6b): canonical backing-file path ->
    /// region record. The host kernel's /dev/ashmem is
    /// policy-denied to app-domain processes on the Android
    /// 12 host (open returns EACCES), so the device is
    /// virtualized like binder and fb0: one plain shared
    /// file per open, ioctls answered from this table.
    ashmem: HashMap<String, AshmemRec>,
    ashmem_seq: u64,
    /// FD translation (S6 gun 4): parcels already delivered
    /// into an arena whose flat FD objects still carry the
    /// *sender's* fd numbers. A fixup names the arena-file
    /// offset of the fd word plus the sender (host pid and
    /// its fd); at wake time the receiver is made to open
    /// /proc/<sender>/fd/<n> itself (remote syscall
    /// injection, resolve_fd_fixups) and the word is patched
    /// with the receiver-side number.
    fd_pending: HashMap<String, Vec<FdFixup>>,
    fd_cache: HashMap<(String, i32, i32), i32>,
    /// Transactions addressed to handle 0 before any
    /// context manager registered (0.9.24). On real
    /// hardware this cannot happen -- servicemanager is
    /// up before any client -- and the driver has no
    /// DEAD_REPLY for the manager handle; the supervisor
    /// used to invent one, and a client that lost the
    /// boot race on it wedged for good (0.9.22 device
    /// run: gbprobe's first getService dead-replied, its
    /// retry never completed). Queued here instead and
    /// delivered when SET_CONTEXT_MGR lands; the sender
    /// parks in its read side meanwhile, exactly like a
    /// slow synchronous call.
    mgr_pending: Vec<PendingMgrTxn>,
}

/// One transaction held for the context manager (see
/// BinderState::mgr_pending). Everything the normal
/// delivery path needs, captured at the sender's entry
/// stop.
struct PendingMgrTxn {
    sender_arena: String,
    sender_pid: i32,
    target_handle: u32,
    cookie: u32,
    code: u32,
    flags: u32,
    veuid: u32,
    data: Vec<u8>,
    offs: Vec<u8>,
}

struct AshmemRec {
    size: u64,
    name: String,
    prot: u64,
}

struct FdFixup {
    file_off: u64,
    sender_pid: i32,
    sender_fd: i32,
}

impl BinderState {
    fn note(&mut self, what: &str) {
        if self.noted.insert(what.to_string()) {
            sup!("binder: {what} (first occurrence)");
        }
    }
    fn node_for_local(&mut self, owner: &str, ptr: u32, cookie: u32) -> usize {
        if let Some(i) = self.nodes.iter().position(|n| {
            !n.dead && n.owner == owner && n.ptr == ptr && n.cookie == cookie
        }) {
            return i;
        }
        self.nodes.push(BinderNode {
            owner: owner.to_string(),
            ptr,
            cookie,
            dead: false,
        });
        self.nodes.len() - 1
    }
    fn handle_for(&mut self, arena: &str, node: usize) -> u32 {
        // Never panic: the supervisor dying takes the whole
        // session with it. A missing arena degrades the object
        // to handle 0 with a note, not a crash.
        let Some(bp) = self.procs.get_mut(arena) else {
            self.note("handle_for: arena state missing; object degraded to handle 0");
            return 0;
        };
        if let Some((h, _)) = bp.handles.iter().find(|(_, n)| **n == node) {
            return *h;
        }
        let h = bp.next_handle;
        bp.next_handle += 1;
        bp.handles.insert(h, node);
        h
    }
    fn alloc(&mut self, arena: &str, size: u32) -> Option<u32> {
        let bp = self.procs.get_mut(arena)?;
        let size = (size + 7) & !7;
        for i in 0..bp.free.len() {
            let (o, s) = bp.free[i];
            if s >= size {
                bp.free.remove(i);
                if s > size {
                    bp.free.push((o + size, s - size));
                }
                bp.used.insert(o, size);
                return Some(o);
            }
        }
        let cap = bp
            .maplen
            .values()
            .copied()
            .min()
            .unwrap_or(128 * 1024)
            .min(BINDER_ARENA_CAP);
        if bp.bump + size > cap {
            return None;
        }
        let o = bp.bump;
        bp.bump += size;
        bp.used.insert(o, size);
        Some(o)
    }
}

/// Rewrite one flat_binder_object slot in a parcel being
/// transferred `to` a process: the node is presented as a
/// local object when the receiver owns it, else as a handle
/// in the receiver's table.
fn binder_write_obj(st: &mut BinderState, to: &str, node: usize, weak: bool, out: &mut [u8], off: usize) {
    let (owner, nptr, ncookie) = {
        let n = &st.nodes[node];
        (n.owner.clone(), n.ptr, n.cookie)
    };
    if owner == to {
        put_u32(out, off, if weak { OBJ_WEAK_BINDER } else { OBJ_BINDER });
        put_u32(out, off + 8, nptr);
        put_u32(out, off + 12, ncookie);
    } else {
        let h = st.handle_for(to, node);
        put_u32(out, off, if weak { OBJ_WEAK_HANDLE } else { OBJ_HANDLE });
        put_u32(out, off + 8, h);
        put_u32(out, off + 12, 0);
    }
}

/// Tell a node's owner that a new arena now holds a
/// reference to it, the way the real driver does when an
/// object crosses into another process: BR_INCREFS always,
/// BR_ACQUIRE as well for a strong object. Once per
/// (node, receiver) pair. Guests whose parse skips these
/// (stock binder.c) are unaffected; libbinder owners use
/// them for local object lifetime tracking (S5c).
fn binder_notify_ref(
    st: &mut BinderState,
    node: usize,
    to: &str,
    weak: bool,
    wakes: &mut Vec<i32>,
) {
    let (owner, nptr, ncookie, dead) = {
        let n = &st.nodes[node];
        (n.owner.clone(), n.ptr, n.cookie, n.dead)
    };
    if dead || owner == to {
        return;
    }
    if !st.ref_notified.insert((node, to.to_string())) {
        return;
    }
    if let Some(bp) = st.procs.get_mut(&owner) {
        bp.inbound.extend_from_slice(&BR_INCREFS.to_le_bytes());
        bp.inbound.extend_from_slice(&nptr.to_le_bytes());
        bp.inbound.extend_from_slice(&ncookie.to_le_bytes());
        if !weak {
            bp.inbound.extend_from_slice(&BR_ACQUIRE.to_le_bytes());
            bp.inbound.extend_from_slice(&nptr.to_le_bytes());
            bp.inbound.extend_from_slice(&ncookie.to_le_bytes());
        }
    }
    binder_maybe_wake(st, &owner, wakes);
    st.note("ref notice queued to object owner");
}

/// The driver's parcel translation: local objects become
/// nodes, handles resolve through the sender's table, and
/// everything is re-expressed in the receiver's view. FD
/// objects cannot be resolved here (the receiver-side fd
/// only exists at wake time); their locations are collected
/// into `fd_fixups` as (offset of the fd word in the output
/// data, sender's fd number) for the delivery to register.
fn binder_translate(
    st: &mut BinderState,
    from: &str,
    to: &str,
    data: &[u8],
    offs: &[u8],
    wakes: &mut Vec<i32>,
    fd_fixups: &mut Vec<(usize, i32)>,
) -> Vec<u8> {
    let mut out = data.to_vec();
    let mut i = 0;
    while i + 4 <= offs.len() {
        let off = u32_at(offs, i) as usize;
        i += 4;
        if off + 16 > out.len() {
            continue;
        }
        let ty = u32_at(&out, off);
        let ptr = u32_at(&out, off + 8);
        let cookie = u32_at(&out, off + 12);
        match ty {
            OBJ_BINDER | OBJ_WEAK_BINDER => {
                let node = st.node_for_local(from, ptr, cookie);
                binder_write_obj(st, to, node, ty == OBJ_WEAK_BINDER, &mut out, off);
                binder_notify_ref(st, node, to, ty == OBJ_WEAK_BINDER, wakes);
            }
            OBJ_HANDLE | OBJ_WEAK_HANDLE => {
                let node = if ptr == 0 {
                    st.mgr_node
                } else {
                    st.procs
                        .get(from)
                        .and_then(|p| p.handles.get(&ptr).copied())
                };
                match node {
                    Some(n) => {
                        binder_write_obj(st, to, n, ty == OBJ_WEAK_HANDLE, &mut out, off);
                        binder_notify_ref(st, n, to, ty == OBJ_WEAK_HANDLE, wakes);
                    }
                    None => st.note("parcel carried an unknown handle; left untranslated"),
                }
            }
            OBJ_FD => {
                fd_fixups.push((off + 8, ptr as i32));
            }
            _ => {
                sup!("binder: untranslated parcel object type=0x{ty:08x} ptr=0x{ptr:x} (passed through)");
            }
        }
    }
    out
}

/// Copy a translated parcel into the target arena and queue
/// the BR_TRANSACTION / BR_REPLY carrying it. On failure the
/// Err names the exact stage, so a dead delivery explains
/// itself in the log instead of hiding behind a bool.
fn binder_deliver(
    st: &mut BinderState,
    target: &str,
    br_cmd: u32,
    target_ptr: u32,
    cookie: u32,
    code: u32,
    flags: u32,
    sender_pid: i32,
    sender_euid: u32,
    data: &[u8],
    offs: &[u8],
    fd_fixups: &[(usize, i32)],
    // For BR_REPLY: the thread this reply belongs to. Its
    // bytes must land in that thread's own queue, never in
    // the shared inbound stream.
    reply_to: Option<i32>,
) -> Result<(), &'static str> {
    let total = ((data.len() as u32 + 3) & !3) + ((offs.len() as u32 + 3) & !3);
    let Some(off) = st.alloc(target, total.max(8)) else {
        return Err("alloc failed (no such arena state, or out of mapped space)");
    };
    for (rel, sfd) in fd_fixups {
        st.fd_pending
            .entry(target.to_string())
            .or_default()
            .push(FdFixup {
                file_off: off as u64 + *rel as u64,
                sender_pid,
                sender_fd: *sfd,
            });
    }
    let Some(bp) = st.procs.get_mut(target) else {
        return Err("arena state vanished after alloc");
    };
    let Some(&base) = bp.base.values().next() else {
        return Err("target arena has no recorded mmap base");
    };
    if bp.file.write_all_at(data, off as u64).is_err()
        || bp.file.write_all_at(offs, (off + ((data.len() as u32 + 3) & !3)) as u64).is_err()
    {
        return Err("arena file write failed");
    }
    let mut txn = [0u8; 40];
    put_u32(&mut txn, 0, target_ptr);
    put_u32(&mut txn, 4, cookie);
    put_u32(&mut txn, 8, code);
    put_u32(&mut txn, 12, flags);
    put_u32(&mut txn, 16, sender_pid as u32);
    put_u32(&mut txn, 20, sender_euid);
    put_u32(&mut txn, 24, data.len() as u32);
    put_u32(&mut txn, 28, offs.len() as u32);
    put_u32(&mut txn, 32, base + off);
    put_u32(&mut txn, 36, base + off + ((data.len() as u32 + 3) & !3));
    match (br_cmd, reply_to) {
        (BR_REPLY, Some(pid)) => {
            bp.push_to(pid, &br_cmd.to_le_bytes());
            bp.push_to(pid, &txn);
        }
        _ => {
            // An inbound transaction goes straight into a
            // parked looper's personal queue when one is
            // waiting; the shared inbound stream is only the
            // fallback for "nobody home". Leaving it in the
            // stream whenever possible starved once already:
            // the looper kept waking for its own replies and
            // its drain never reached the pooled transaction.
            let parked_looper = st
                .parked
                .keys()
                .find(|p| {
                    bp.loopers.contains(p)
                        && st
                            .thread_arena
                            .get(p)
                            .map(|a| a == target)
                            .unwrap_or(false)
                })
                .copied();
            match parked_looper {
                Some(p) => {
                    sup!("binder: txn for {target} landed in parked looper pid={p}'s queue");
                    bp.push_to(p, &br_cmd.to_le_bytes());
                    bp.push_to(p, &txn);
                }
                None => {
                    let parked_here: Vec<String> = st
                        .parked
                        .keys()
                        .map(|p| {
                            format!(
                                "{p}(arena={}, looper={})",
                                st.thread_arena.get(p).cloned().unwrap_or_default(),
                                bp.loopers.contains(p)
                            )
                        })
                        .collect();
                    sup!(
                        "binder: txn for {target} pooled in inbound (parked: [{}])",
                        parked_here.join(", ")
                    );
                    bp.inbound.extend_from_slice(&br_cmd.to_le_bytes());
                    bp.inbound.extend_from_slice(&txn);
                }
            }
        }
    }
    Ok(())
}

/// If the target arena has a parked reader, schedule its
/// wake (the main loop performs it after the entry stop).
fn binder_maybe_wake(st: &BinderState, arena: &str, wakes: &mut Vec<i32>) {
    let Some(bp) = st.procs.get(arena) else {
        return;
    };
    if bp.inbound.is_empty() && bp.queues.values().all(|q| q.is_empty()) {
        return;
    }
    // Wake exactly the parked threads that have bytes they
    // may read: a thread with addressed bytes, or a looper
    // while the inbound stream is non-empty. (The old code
    // woke the first parked thread it found and handed it
    // the whole shared queue, whatever the bytes were for.)
    for (pid, park) in &st.parked {
        if park.read_size == 0 || wakes.contains(pid) {
            continue;
        }
        if st.thread_arena.get(pid).map(|a| a != arena).unwrap_or(true) {
            continue;
        }
        let own = bp.queues.get(pid).map_or(0, |q| q.len());
        if own > 0 || (!bp.inbound.is_empty() && bp.loopers.contains(pid)) {
            wakes.push(*pid);
        }
    }
}

/// Process one binder WRITE_READ stream's write side.
#[allow(clippy::too_many_arguments)]
fn binder_process_stream(
    pid: i32,
    arena: &str,
    stream: &[u8],
    st: &mut BinderState,
    veuid: u32,
    wakes: &mut Vec<i32>,
    notes: &mut Vec<String>,
) {
    let mut cur = 0usize;
    while cur + 4 <= stream.len() {
        let cmd = u32_at(stream, cur);
        cur += 4;
        match cmd {
            BC_ENTER_LOOPER | BC_REGISTER_LOOPER => {
                if let Some(bp) = st.procs.get_mut(arena) {
                    bp.loopers.insert(pid);
                }
                notes.push("looper in".to_string());
            }
            BC_EXIT_LOOPER => {
                if let Some(bp) = st.procs.get_mut(arena) {
                    bp.loopers.remove(&pid);
                }
                notes.push("looper out".to_string());
            }
            BC_FREE_BUFFER => {
                if cur + 4 > stream.len() {
                    break;
                }
                let ptr = u32_at(stream, cur);
                cur += 4;
                if let Some(bp) = st.procs.get_mut(arena) {
                    if let Some(&base) = bp.base.get(&pid) {
                        let off = ptr.wrapping_sub(base);
                        if let Some(sz) = bp.used.remove(&off) {
                            bp.free.push((off, sz));
                        }
                    }
                }
            }
            BC_INCREFS | BC_ACQUIRE | BC_RELEASE | BC_DECREFS => {
                if cur + 4 > stream.len() {
                    break;
                }
                cur += 4;
                st.note("refcount BC consumed (v1 no-op)");
            }
            BC_INCREFS_DONE | BC_ACQUIRE_DONE => {
                if cur + 8 > stream.len() {
                    break;
                }
                cur += 8;
            }
            BC_ATTEMPT_ACQUIRE => {
                if cur + 8 > stream.len() {
                    break;
                }
                cur += 8;
                if let Some(bp) = st.procs.get_mut(arena) {
                    bp.push_to(pid, &BR_DEAD_REPLY.to_le_bytes());
                }
                st.note("ATTEMPT_ACQUIRE answered DEAD_REPLY (v1)");
            }
            BC_REQUEST_DEATH_NOTIFICATION => {
                if cur + 8 > stream.len() {
                    break;
                }
                let h = u32_at(stream, cur);
                let cookie = u32_at(stream, cur + 4);
                cur += 8;
                let node = if h == 0 {
                    st.mgr_node
                } else {
                    st.procs.get(arena).and_then(|p| p.handles.get(&h).copied())
                };
                if let Some(n) = node {
                    st.watchers
                        .entry(n)
                        .or_default()
                        .push((arena.to_string(), cookie));
                    notes.push("death watch registered".to_string());
                }
            }
            BC_CLEAR_DEATH_NOTIFICATION => {
                if cur + 8 > stream.len() {
                    break;
                }
                let cookie = u32_at(stream, cur + 4);
                cur += 8;
                for v in st.watchers.values_mut() {
                    v.retain(|(a, c)| !(a == arena && *c == cookie));
                }
                if let Some(bp) = st.procs.get_mut(arena) {
                    bp.push_to(pid, &BR_CLEAR_DEATH_NOTIFICATION_DONE.to_le_bytes());
                    bp.push_to(pid, &cookie.to_le_bytes());
                }
            }
            BC_DEAD_BINDER_DONE => {
                if cur + 4 > stream.len() {
                    break;
                }
                cur += 4;
            }
            BC_TRANSACTION | BC_REPLY => {
                if cur + 40 > stream.len() {
                    notes.push("short txn in write stream".to_string());
                    break;
                }
                let txn: Vec<u8> = stream[cur..cur + 40].to_vec();
                cur += 40;
                binder_handle_txn(pid, arena, cmd == BC_REPLY, &txn, st, veuid, wakes, notes);
            }
            other => {
                notes.push(format!("unknown BC {other:#010x}; stream parse stopped"));
                break;
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn binder_handle_txn(
    pid: i32,
    arena: &str,
    is_reply: bool,
    txn: &[u8],
    st: &mut BinderState,
    veuid: u32,
    wakes: &mut Vec<i32>,
    notes: &mut Vec<String>,
) {
    let target = u32_at(txn, 0);
    let cookie = u32_at(txn, 4);
    let code = u32_at(txn, 8);
    let flags = u32_at(txn, 12);
    let dsize = u32_at(txn, 24) as usize;
    let osize = u32_at(txn, 28) as usize;
    let daddr = u32_at(txn, 32);
    let oaddr = u32_at(txn, 36);
    if dsize > (1 << 20) || osize > (1 << 16) {
        notes.push("txn too large; dropped".to_string());
        return;
    }
    let Some(data) = read_mem_vec(pid, daddr as u64, dsize) else {
        notes.push("txn data unreadable; dropped".to_string());
        return;
    };
    let offs = if osize > 0 {
        read_mem_vec(pid, oaddr as u64, osize).unwrap_or_default()
    } else {
        Vec::new()
    };
    if is_reply {
        let w = st
            .waiters
            .get_mut(arena)
            .and_then(|v| if v.is_empty() { None } else { Some(v.remove(0)) });
        let Some(w) = w else {
            notes.push("BC_REPLY with no waiter; dropped".to_string());
            return;
        };
        let mut fd_fixups: Vec<(usize, i32)> = Vec::new();
        let tdata = binder_translate(st, arena, &w.sender_arena, &data, &offs, wakes, &mut fd_fixups);
        let delivered = binder_deliver(
            st,
            &w.sender_arena,
            BR_REPLY,
            w.target_handle,
            w.cookie,
            0,
            flags,
            pid,
            veuid,
            &tdata,
            &offs,
            &fd_fixups,
            Some(w.sender_pid),
        );
        if let Err(why) = delivered {
            notes.push(format!("REPLY delivery failed: {why}"));
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_FAILED_REPLY.to_le_bytes());
            }
        }
        binder_maybe_wake(st, &w.sender_arena, wakes);
        sup!(
            "binder: reply ({}B) delivered for waiter pid {}",
            tdata.len(),
            w.sender_pid
        );
        notes.push(format!("REPLY -> pid {} ({}B)", w.sender_pid, tdata.len()));
        return;
    }
    let node = if target == 0 {
        st.mgr_node
    } else {
        st.procs.get(arena).and_then(|p| p.handles.get(&target).copied())
    };
    let Some(node) = node else {
        if target == 0 {
            // No context manager yet: queue for its
            // registration instead of inventing a
            // DEAD_REPLY the real driver never sends for
            // handle 0 (see mgr_pending). The sender's
            // read side finds nothing and parks, like a
            // slow synchronous call.
            st.mgr_pending.push(PendingMgrTxn {
                sender_arena: arena.to_string(),
                sender_pid: pid,
                target_handle: target,
                cookie,
                code,
                flags,
                veuid,
                data,
                offs,
            });
            // Causal ledger (0.9.27): this line is printed
            // at entry-processing time, unlike the call's
            // desc, which can surface much later.
            sup!(
                "binder: queued mgr txn from pid={pid} code={code} (pending now {})",
                st.mgr_pending.len()
            );
            notes.push(
                "TRANSACTION to manager before it registered -> queued".to_string(),
            );
            return;
        }
        if let Some(bp) = st.procs.get_mut(arena) {
            bp.push_to(pid, &BR_DEAD_REPLY.to_le_bytes());
        }
        notes.push(format!("TRANSACTION to unknown handle {target} -> DEAD_REPLY"));
        return;
    };
    if st.nodes[node].dead {
        // The service behind this handle is gone (S5c):
        // exactly what the real driver answers here.
        if let Some(bp) = st.procs.get_mut(arena) {
            bp.push_to(pid, &BR_DEAD_REPLY.to_le_bytes());
        }
        notes.push(format!(
            "TRANSACTION to dead node (handle {target}) -> DEAD_REPLY"
        ));
        return;
    }
    let (owner, nptr, ncookie) = {
        let n = &st.nodes[node];
        (n.owner.clone(), n.ptr, n.cookie)
    };
    binder_send_txn(
        st, wakes, notes, arena, pid, target, cookie, nptr, ncookie, &owner, code, flags,
        veuid, &data, &offs,
    );
}

/// The delivery half of a transaction to a known node:
/// translate the parcel, deliver it, register the reply
/// wait and complete the sender's call. Shared by the
/// direct path and by the manager-queue flush (0.9.24).
#[allow(clippy::too_many_arguments)]
fn binder_send_txn(
    st: &mut BinderState,
    wakes: &mut Vec<i32>,
    notes: &mut Vec<String>,
    arena: &str,
    pid: i32,
    target: u32,
    cookie: u32,
    nptr: u32,
    ncookie: u32,
    owner: &str,
    code: u32,
    flags: u32,
    veuid: u32,
    data: &[u8],
    offs: &[u8],
) {
    // Telemetry: decode the interface token so the log states
    // who this transaction speaks to and whether it is one-way.
    {
        let tok = if data.len() >= 8 {
            // Parcel layout: strict-policy word, then the
            // interface token as a char count followed by
            // UTF-16 code units.
            let n = u32_at(&data, 4) as usize;
            if n <= 128 && data.len() >= 8 + (n + 1) * 2 {
                (0..n)
                    .map(|k| {
                        u16::from_le_bytes([data[8 + k * 2], data[9 + k * 2]]) as u8 as char
                    })
                    .collect::<String>()
            } else {
                String::new()
            }
        } else {
            String::new()
        };
        sup!(
            "binder: txn detail from pid={pid} code={code} flags=0x{flags:x} offs={}B token='{tok}'",
            offs.len()
        );
    }
    let mut fd_fixups: Vec<(usize, i32)> = Vec::new();
    let tdata = binder_translate(st, arena, &owner, &data, &offs, wakes, &mut fd_fixups);
    let delivered = binder_deliver(
        st, &owner, BR_TRANSACTION, nptr, ncookie, code, flags, pid, veuid, &tdata, &offs,
        &fd_fixups,
        None,
    );
    if let Err(why) = delivered {
        if let Some(bp) = st.procs.get_mut(arena) {
            bp.push_to(pid, &BR_DEAD_REPLY.to_le_bytes());
        }
        notes.push(format!("TRANSACTION target cannot receive ({why}) -> DEAD_REPLY"));
        return;
    }
    if flags & TF_ONE_WAY == 0 {
        st.waiters.entry(owner.to_string()).or_default().push(ReplyWait {
            sender_pid: pid,
            sender_arena: arena.to_string(),
            cookie,
            target_handle: target,
        });
    }
    if let Some(bp) = st.procs.get_mut(arena) {
        bp.push_to(pid, &BR_TRANSACTION_COMPLETE.to_le_bytes());
    }
    binder_maybe_wake(st, &owner, wakes);
    notes.push(format!("TRANSACTION code {code} -> node in {owner} ({}B)", tdata.len()));
}

/// Emulate one BINDER_WRITE_READ ioctl at its entry stop.
#[allow(clippy::too_many_arguments)]
fn binder_write_read(
    pid: i32,
    compat: bool,
    arena: &str,
    regs: &mut Regs,
    pend: &mut Pending,
    st: &mut BinderState,
    vcreds: &HashMap<i32, (u32, u32)>,
    wakes: &mut Vec<i32>,
) -> String {
    let bwr_addr = regs.arg(2);
    let Some(bwr) = read_mem_vec(pid, bwr_addr, 24) else {
        skip_syscall(pid, regs, pend, -14);
        return "binder WRITE_READ: bwr unreadable -> -EFAULT".to_string();
    };
    let ws = u32_at(&bwr, 0);
    let wc0 = u32_at(&bwr, 4);
    let wb = u32_at(&bwr, 8);
    let rs = u32_at(&bwr, 12);
    let rb = u32_at(&bwr, 20);
    let arena = arena.to_string();
    let veuid = vcreds.get(&pid).copied().unwrap_or((0, 0)).0;
    let mut notes: Vec<String> = Vec::new();
    if ws > wc0 && ws <= (1 << 20) {
        match read_mem_vec(pid, (wb + wc0) as u64, (ws - wc0) as usize) {
            Some(stream) => {
                binder_process_stream(pid, &arena, &stream, st, veuid, wakes, &mut notes)
            }
            None => notes.push("write stream unreadable".to_string()),
        }
    }
    let writeback = |rc: u32| {
        let mut b = [0u8; 24];
        put_u32(&mut b, 0, ws);
        put_u32(&mut b, 4, ws);
        put_u32(&mut b, 8, wb);
        put_u32(&mut b, 12, rs);
        put_u32(&mut b, 16, rc);
        put_u32(&mut b, 20, rb);
        b
    };
    let queue_len = st
        .procs
        .get(&arena)
        .map(|p| p.readable_for(pid))
        .unwrap_or(0);
    if rs > 0 && queue_len > 0 {
        let n = queue_len.min(rs as usize);
        let bytes: Vec<u8> = st
            .procs
            .get_mut(&arena)
            .map(|bp| bp.drain_for(pid, n).0)
            .unwrap_or_default();
        dump_mgr_read(st, &arena, pid, &bytes);
        let _ = write_mem(pid, rb as u64, &bytes);
        let _ = write_mem(pid, bwr_addr, &writeback(bytes.len() as u32));
        skip_syscall(pid, regs, pend, 0);
        // Deliveries to this arena may have left fd fixups
        // unresolved. They are normally settled when the
        // receiver is woken out of a park; a thread that
        // finds its reply already queued on entry never
        // parks, and would go on to read the parcel with
        // the senders' raw fds still in it (a received
        // heap's client-side mmap then fails on a foreign
        // fd). Settle them now, while this call sits in
        // the same skipped state the parked path resolves
        // from: rides consume this call's entry->exit
        // transition, so the fake result is applied to the
        // regs here and the caller drops its exit-stop
        // expectation (it keys that off pend.applied).
        if let Some(fixups) = st.fd_pending.remove(&arena) {
            if !fixups.is_empty() {
                let rides =
                    resolve_fd_fixups_core(pid, compat, st, &arena, &fixups, regs);
                if rides > 0 {
                    regs.set_retval(0);
                    if set_regs(pid, regs) {
                        pend.applied = true;
                    }
                }
            }
        }
        notes.push(format!("read filled {}B", bytes.len()));
    } else if rs > 0 {
        skip_syscall(pid, regs, pend, 0);
        st.parked.insert(
            pid,
            ParkedIoctl {
                bwr: bwr_addr as u32,
                read_buf: rb,
                read_size: rs,
                write_consumed: ws,
            },
        );
        pend.binder_parked = true;
        notes.push("parked awaiting work".to_string());
    } else {
        let _ = write_mem(pid, bwr_addr, &writeback(0));
        skip_syscall(pid, regs, pend, 0);
    }
    if notes.is_empty() {
        notes.push("no work".to_string());
    }
    format!("binder WRITE_READ pid={pid} [{}]", notes.join("; "))
}

/// Telemetry (0.9.27): when the context manager itself is
/// handed read bytes, name the command words. GB
/// servicemanager exits its loop (and the process) on
/// specific BR codes -- a stray BR_REPLY, BR_DEAD_REPLY
/// or a truncated stream would each explain the
/// manager's clean exit(0) after serving flushed work in
/// the 0.9.26 device run; this names which one it ate.
fn dump_mgr_read(st: &BinderState, arena: &str, pid: i32, bytes: &[u8]) {
    if st.mgr_arena.as_deref() != Some(arena) {
        return;
    }
    let mut cmds: Vec<String> = Vec::new();
    let mut off = 0usize;
    while off + 4 <= bytes.len() && cmds.len() < 8 {
        let c = u32_at(bytes, off);
        cmds.push(format!("{c:#010x}"));
        off += match c {
            BR_TRANSACTION | BR_REPLY => 44,
            BR_INCREFS | BR_ACQUIRE | 0x8008_7209 | 0x8008_720a => 12,
            _ => 4,
        };
    }
    sup!(
        "binder: mgr read for pid={pid}: {}B cmds=[{}]",
        bytes.len(),
        cmds.join(", ")
    );
}

/// Finish a parked binder ioctl now that its arena has bytes:
/// fill the read buffer, settle the bwr consumed fields, make
/// the exit stop report 0, and continue the tracee into it.
/// Wait (privately, targeted waitpid: no other tracee's
/// events are consumed) for the tracee's next syscall stop,
/// suppressing any signal stops on the way. Event stops
/// abort: they belong to the main loop's bookkeeping and
/// must not be silently swallowed.
fn wait_one_syscall_stop(pid: i32) -> Option<()> {
    for _ in 0..32 {
        let mut status: libc::c_int = 0;
        let r = unsafe { libc::waitpid(pid, &mut status, WALL) };
        if r <= 0 {
            return None;
        }
        if libc::WIFEXITED(status) || libc::WIFSIGNALED(status) {
            sup!("binder: fd injection lost pid={pid} (exited during injection)");
            return None;
        }
        if libc::WIFSTOPPED(status) {
            let sig = libc::WSTOPSIG(status);
            let event = (status >> 16) & 0xffff;
            if sig == (libc::SIGTRAP | 0x80) && event == 0 {
                return Some(());
            }
            if event != 0 {
                sup!("binder: fd injection hit an event stop pid={pid} event={event}; aborting");
                return None;
            }
            // Signal stop: suppress and keep waiting. (A late
            // SIGSYS belonging to the parked call is harmless
            // to suppress here; its rescue record still stands
            // and its value was already fabricated.)
            cont_syscall(pid, 0);
        }
    }
    None
}

/// Run one openat("/proc/<sender>/fd/<n>") inside a tracee
/// stopped at a syscall stop and return the new fd (or a
/// negative value). The first ride uses the stop we are
/// already sitting on; later rides rewind the PC to the svc
/// instruction and drive entry+exit privately. On return
/// `regs` holds the exit-stop registers of the injected
/// call.
fn inject_openat(
    pid: i32,
    compat: bool,
    path_addr: u64,
    entry_pc: u64,
    rewind: bool,
    regs: &mut Regs,
) -> i64 {
    if rewind {
        regs.set_pc(entry_pc);
    }
    let nr_openat: u64 = if compat { 322 } else { 56 };
    regs.set_nr(nr_openat);
    regs.set_arg(0, (-100i32) as i64 as u64); // AT_FDCWD
    regs.set_arg(1, path_addr);
    regs.set_arg(2, 2); // O_RDWR
    regs.set_arg(3, 0);
    if !set_regs(pid, regs) {
        return -1;
    }
    if !set_syscallno(pid, nr_openat as i32) {
        sup!("binder: fd injection NT_ARM_SYSTEM_CALL failed pid={pid}");
        return -1;
    }
    cont_syscall(pid, 0);
    let mut stops_needed = if rewind { 2 } else { 1 };
    loop {
        match wait_one_syscall_stop(pid) {
            Some(()) => {
                stops_needed -= 1;
                if stops_needed == 0 {
                    match get_regs(pid, compat) {
                        Some(r) => {
                            *regs = r;
                            return r.retval();
                        }
                        None => return -1,
                    }
                }
                cont_syscall(pid, 0);
            }
            None => return -1,
        }
    }
}

/// Resolve one wake's FD fixups: make the receiver open
/// each sender fd itself, patch the parcel words in its
/// arena file, then settle its parked call. The rides
/// consume the parked entry->exit transition, so the
/// recorded inject is applied here exactly as the exit-stop
/// branch would (value set, record marked applied and left
/// standing for the late-SIGSYS rescue). When every fixup
/// is a cache hit nothing is ridden and the ordinary flow
/// is left untouched.
/// Core of the fixup resolution: have the receiver open
/// each sender fd (cache first), patch the parcel words in
/// the arena file, and return how many injection rides were
/// needed. Settling the receiver's stop state differs
/// between callers (parked wake vs WRITE_READ entry), so it
/// stays with them.
fn resolve_fd_fixups_core(
    pid: i32,
    compat: bool,
    st: &mut BinderState,
    arena: &str,
    fixups: &[FdFixup],
    regs: &mut Regs,
) -> usize {
    let entry_pc = regs.pc();
    let mut cursor = regs.sp().saturating_sub(256);
    let mut rides = 0;
    for fx in fixups {
        let cache_key = (arena.to_string(), fx.sender_pid, fx.sender_fd);
        let newfd: i64 = if let Some(fd) = st.fd_cache.get(&cache_key) {
            *fd as i64
        } else {
            let path = format!("/proc/{}/fd/{}", fx.sender_pid, fx.sender_fd);
            let fd = match scratch_write(pid, &mut cursor, &path) {
                Some(addr) => inject_openat(pid, compat, addr, entry_pc, rides > 0, &mut *regs),
                None => -1,
            };
            rides += 1;
            if fd >= 0 {
                st.fd_cache.insert(cache_key, fd as i32);
            }
            fd
        };
        if let Ok(f) = std::fs::OpenOptions::new().write(true).open(arena) {
            use std::os::unix::fs::FileExt;
            let _ = f.write_all_at(&(newfd as u32).to_le_bytes(), fx.file_off);
        }
        sup!(
            "binder: fd {} of pid {} -> fd {} in pid {} (parcel fixup)",
            fx.sender_fd,
            fx.sender_pid,
            newfd,
            pid
        );
    }
    rides
}

fn resolve_fd_fixups(
    pid: i32,
    procs: &mut HashMap<i32, ProcState>,
    st: &mut BinderState,
    arena: &str,
    fixups: &[FdFixup],
) {
    let Some(proc0) = procs.get(&pid) else {
        return;
    };
    let compat = proc0.compat;
    let Some(mut regs) = get_regs(pid, compat) else {
        return;
    };
    let rides = resolve_fd_fixups_core(pid, compat, st, arena, fixups, &mut regs);
    if rides == 0 {
        return;
    }
    if let Some(proc) = procs.get_mut(&pid) {
        if let Some(pend) = proc.pending.as_mut() {
            if let Some(v) = pend.inject {
                if !pend.rescue_only {
                    regs.set_retval(v);
                    if set_regs(pid, &regs) {
                        pend.applied = true;
                    }
                    if let Some(d) = &pend.desc {
                        sys!("{d} => {v}");
                    }
                }
            }
        }
        proc.expect_exit = false;
    }
}

fn complete_parked(pid: i32, procs: &mut HashMap<i32, ProcState>, st: &mut BinderState) {
    let Some(park) = st.parked.remove(&pid) else {
        return;
    };
    let Some(arena) = st.thread_arena.get(&pid).cloned() else {
        return;
    };
    let (bytes, from_inbound) = {
        let Some(bp) = st.procs.get_mut(&arena) else {
            return;
        };
        let n = bp.readable_for(pid).min(park.read_size as usize);
        bp.drain_for(pid, n)
    };
    if !bytes.is_empty() {
        sup!(
            "binder: waking pid={pid} with {}B of queued work ({}B from inbound)",
            bytes.len(),
            from_inbound
        );
        dump_mgr_read(st, &arena, pid, &bytes);
    }
    if bytes.is_empty() {
        st.parked.insert(pid, park);
        return;
    }
    let _ = write_mem(pid, park.read_buf as u64, &bytes);
    let _ = write_mem(pid, (park.bwr + 4) as u64, &park.write_consumed.to_le_bytes());
    let _ = write_mem(pid, (park.bwr + 16) as u64, &(bytes.len() as u32).to_le_bytes());
    // The pending record must keep its inject: on this device
    // the SIGSYS belonging to a cancelled syscall is delivered
    // *after* its exit stop, and the signal-stop rescue can
    // only recognise it while the record (with inject) lives.
    // An earlier version cleared inject here "so the rescue
    // would not mistake the record" -- exactly backwards: the
    // first parked completion (0.6.5 device run) woke
    // servicemanager, which then died of its own parked
    // ioctl's late SIGSYS. Leaving inject in place gives the
    // parked call the ordinary fake lifecycle: the exit stop
    // applies the 0 and retains the record, the late SIGSYS
    // is rescued and consumes it. (No regs surgery here: the
    // exit stop applies the inject itself.)
    // FD fixups, if this delivery carried any, resolve while
    // the receiver is still parked: it opens the senders'
    // fds itself under supervisor control, and its parked
    // call is settled by the resolver (see resolve_fd_fixups).
    if let Some(fixups) = st.fd_pending.remove(&arena) {
        if !fixups.is_empty() {
            resolve_fd_fixups(pid, procs, st, &arena, &fixups);
        }
    }
    cont_syscall(pid, 0);
}

/// A tracee that held a binder arena exited (S5c). When it
/// was the arena's last thread, the arena dies with it:
/// synchronous callers still waiting for its replies get
/// BR_DEAD_REPLY, its nodes are marked dead (outstanding
/// handles to them dead-reply from now on), and every death
/// watch on those nodes fires BR_DEAD_BINDER with the exact
/// cookie the watcher registered -- stock servicemanager
/// answers it by zeroing the service's entry, so a later
/// GET returns the null form and a re-ADD revives the name.
/// Caller has already removed the pid from thread_arena.
fn binder_on_proc_exit(arena: &str, st: &mut BinderState, wakes: &mut Vec<i32>) {
    if st.thread_arena.values().any(|a| a == arena) {
        return; // sibling threads still hold this arena
    }
    // Queued manager transactions from this arena's
    // senders die with it (0.9.24).
    let before = st.mgr_pending.len();
    st.mgr_pending.retain(|q| q.sender_arena != arena);
    let purged = before - st.mgr_pending.len();
    if purged > 0 {
        sup!("binder: purged {purged} queued mgr txn(s) from dead arena {arena}");
    }
    if st.mgr_arena.as_deref() == Some(arena) {
        st.mgr_arena = None;
        if let Some(mi) = st.mgr_node.take() {
            if let Some(n) = st.nodes.get_mut(mi) {
                n.dead = true;
            }
        }
        sup!("binder: context manager arena died; manager slot cleared");
    }
    if let Some(ws) = st.waiters.remove(arena) {
        for w in ws {
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_DEAD_REPLY.to_le_bytes());
            }
            binder_maybe_wake(st, &w.sender_arena, wakes);
        }
    }
    for v in st.waiters.values_mut() {
        v.retain(|w| w.sender_arena != arena);
    }
    let mut dead_nodes: Vec<usize> = Vec::new();
    for (i, n) in st.nodes.iter_mut().enumerate() {
        if n.owner == arena && !n.dead {
            n.dead = true;
            dead_nodes.push(i);
        }
    }
    let mut notices = 0usize;
    for i in &dead_nodes {
        if let Some(list) = st.watchers.remove(i) {
            for (watcher_arena, cookie) in list {
                if let Some(bp) = st.procs.get_mut(&watcher_arena) {
                    bp.inbound.extend_from_slice(&BR_DEAD_BINDER.to_le_bytes());
                    bp.inbound.extend_from_slice(&cookie.to_le_bytes());
                    notices += 1;
                }
                binder_maybe_wake(st, &watcher_arena, wakes);
            }
        }
    }
    for v in st.watchers.values_mut() {
        v.retain(|(a, _)| a != arena);
    }
    if !dead_nodes.is_empty() {
        sup!(
            "binder: arena {arena} died; {} node(s) dead, {notices} death notice(s) queued",
            dead_nodes.len()
        );
    }
}

/// open("/dev/binder"): point the call at a fresh per-opener
/// arena file the supervisor owns, and register the arena.
fn entry_open_binder(
    pid: i32,
    rootfs: &str,
    compat: bool,
    nr: u64,
    regs: &mut Regs,
    st: &mut BinderState,
) -> String {
    let path_arg = if (compat && nr == 322) || (!compat && nr == 56) {
        1
    } else {
        0
    };
    let arena_raw = format!("{rootfs}/.binder/{pid}");
    let _ = std::fs::create_dir_all(format!("{rootfs}/.binder"));
    // The arena's identity key must be the canonical path:
    // later ioctls/mmaps find the arena through /proc/<pid>/fd
    // readlinks, which report the symlink-resolved path
    // (rootfs lives under /data/user/0, a symlink to
    // /data/data). Keying state by the unresolved string made
    // every fd-based lookup miss -- invisible while nothing
    // transacted, fatal at the first parcel translation
    // (0.6.3 device run: handle_for panicked, whole session
    // died). The guest still opens the raw path; same file.
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .open(&arena_raw);
    let arena = std::fs::canonicalize(&arena_raw)
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or(arena_raw.clone());
    match std::fs::OpenOptions::new().create(true).write(true).open(&arena) {
        Ok(f) => {
            if f.metadata().map(|m| m.len()).unwrap_or(0) < BINDER_ARENA_CAP as u64 {
                let _ = f.set_len(BINDER_ARENA_CAP as u64);
            }
            st.procs.entry(arena.clone()).or_insert_with(|| BinderProc {
                file: f,
                base: HashMap::new(),
                maplen: HashMap::new(),
                bump: 0,
                free: Vec::new(),
                used: HashMap::new(),
                handles: HashMap::new(),
                next_handle: 1,
                inbound: Vec::new(),
                queues: HashMap::new(),
                loopers: HashSet::new(),
            });
        }
        Err(e) => return format!("binder arena create failed: {e}"),
    }
    st.thread_arena.insert(pid, arena.clone());
    let mut cursor = regs.sp().saturating_sub(256);
    match scratch_write(pid, &mut cursor, &arena_raw) {
        Some(addr) => {
            regs.set_arg(path_arg, addr);
            "open '/dev/binder' -> binder arena (virtual driver)".to_string()
        }
        None => "open '/dev/binder' (scratch write failed)".to_string(),
    }
}

/// Virtual ashmem open (S6b): reroute to a fresh backing
/// file under {rootfs}/.ashmem; the record lives in the
/// state table keyed by the canonical path (fd readlinks
/// resolve symlinks -- the same lesson as binder arenas).
fn entry_open_ashmem(
    pid: i32,
    rootfs: &str,
    compat: bool,
    nr: u64,
    regs: &mut Regs,
    st: &mut BinderState,
) -> String {
    let path_arg = if (compat && nr == 322) || (!compat && nr == 56) {
        1
    } else {
        0
    };
    st.ashmem_seq += 1;
    let seq = st.ashmem_seq;
    let raw = format!("{rootfs}/.ashmem/a{pid}-{seq}");
    let _ = std::fs::create_dir_all(format!("{rootfs}/.ashmem"));
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&raw);
    // JIT code lands in some regions (pixelflinger's
    // mspace): the guest later mprotects the mapping
    // PROT_EXEC, and on a file-backed VMA the host
    // refuses that (EACCES) when the backing file
    // itself carries no execute permission -- proven
    // by the 0.9.27 device run, where the exact
    // ensureMbaseExecutable call failed -13 five lines
    // before the assembler died on its NULL base.
    // Anonymous mappings and the guest's own libraries
    // pass the same call, so give region files the
    // execute bit and re-run the experiment.
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(
            &raw,
            std::fs::Permissions::from_mode(0o700),
        );
    }
    let key = std::fs::canonicalize(&raw)
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or(raw.clone());
    st.ashmem.insert(
        key,
        AshmemRec {
            size: 0,
            name: String::new(),
            prot: 7,
        },
    );
    let mut cursor = regs.sp().saturating_sub(256);
    match scratch_write(pid, &mut cursor, &raw) {
        Some(addr) => {
            regs.set_arg(path_arg, addr);
            "open '/dev/ashmem' -> virtual ashmem region (host device is policy-denied)".to_string()
        }
        None => "open '/dev/ashmem' (scratch write failed)".to_string(),
    }
}

fn fd_ashmem(pid: i32, fd: i32) -> Option<String> {
    let target = std::fs::read_link(format!("/proc/{pid}/fd/{fd}")).ok()?;
    let s = target.to_string_lossy().into_owned();
    if s.contains("/.ashmem/") {
        Some(s)
    } else {
        None
    }
}

// Ashmem ioctls, guest-era numbering (bionic 2.3.7
// linux/ashmem.h, __ASHMEMIOC 0x77). SET_SIZE and
// SET_PROT_MASK take their value BY VALUE in arg (see
// libcutils ashmem-dev.c); PIN/UNPIN take a pointer to
// struct ashmem_pin, which we never need to read because
// the answers are constants on a file-backed region that
// is never purged.
const ASHMEM_SET_NAME: u32 = 0x4100_7701;
const ASHMEM_GET_NAME: u32 = 0x8100_7702;
const ASHMEM_SET_SIZE: u32 = 0x4004_7703;
const ASHMEM_GET_SIZE: u32 = 0x0000_7704;
const ASHMEM_SET_PROT_MASK: u32 = 0x4004_7705;
const ASHMEM_GET_PROT_MASK: u32 = 0x0000_7706;
const ASHMEM_PIN: u32 = 0x4008_7707;
const ASHMEM_UNPIN: u32 = 0x4008_7708;
const ASHMEM_GET_PIN_STATUS: u32 = 0x0000_7709;
const ASHMEM_PURGE_ALL_CACHES: u32 = 0x0000_770a;

fn entry_ashmem_ioctl(
    pid: i32,
    key: &str,
    req: u32,
    regs: &mut Regs,
    pend: &mut Pending,
    st: &mut BinderState,
) -> String {
    let arg = regs.arg(2);
    let missing = AshmemRec {
        size: 0,
        name: String::new(),
        prot: 7,
    };
    match req {
        ASHMEM_SET_NAME => {
            let mut buf = [0u8; 256];
            let _ = read_mem(pid, arg, &mut buf);
            let end = buf.iter().position(|&b| b == 0).unwrap_or(256);
            let name = String::from_utf8_lossy(&buf[..end]).into_owned();
            st.ashmem.entry(key.to_string()).or_insert(missing).name = name.clone();
            skip_syscall(pid, regs, pend, 0);
            format!("ashmem SET_NAME '{name}'")
        }
        ASHMEM_GET_NAME => {
            let rec = st.ashmem.get(key);
            let name = rec.map(|r| r.name.clone()).unwrap_or_default();
            let mut buf = [0u8; 256];
            let n = name.len().min(255);
            buf[..n].copy_from_slice(&name.as_bytes()[..n]);
            let _ = write_mem(pid, arg, &buf);
            skip_syscall(pid, regs, pend, 0);
            "ashmem GET_NAME".to_string()
        }
        ASHMEM_SET_SIZE => {
            let size = arg as u64;
            st.ashmem.entry(key.to_string()).or_insert(missing).size = size;
            if let Ok(f) = std::fs::OpenOptions::new().write(true).open(key) {
                let _ = f.set_len(size);
            }
            skip_syscall(pid, regs, pend, 0);
            format!("ashmem SET_SIZE -> {size}")
        }
        ASHMEM_GET_SIZE => {
            let size = st.ashmem.get(key).map(|r| r.size).unwrap_or(0);
            skip_syscall(pid, regs, pend, size as i64);
            format!("ashmem GET_SIZE -> {size}")
        }
        ASHMEM_SET_PROT_MASK => {
            st.ashmem.entry(key.to_string()).or_insert(missing).prot = arg as u64;
            skip_syscall(pid, regs, pend, 0);
            "ashmem SET_PROT_MASK".to_string()
        }
        ASHMEM_GET_PROT_MASK => {
            let prot = st.ashmem.get(key).map(|r| r.prot).unwrap_or(7);
            skip_syscall(pid, regs, pend, prot as i64);
            "ashmem GET_PROT_MASK".to_string()
        }
        ASHMEM_PIN => {
            skip_syscall(pid, regs, pend, 0); // ASHMEM_NOT_PURGED
            "ashmem PIN -> NOT_PURGED".to_string()
        }
        ASHMEM_UNPIN => {
            skip_syscall(pid, regs, pend, 0); // ASHMEM_IS_UNPINNED
            "ashmem UNPIN".to_string()
        }
        ASHMEM_GET_PIN_STATUS => {
            skip_syscall(pid, regs, pend, 1); // ASHMEM_IS_PINNED
            "ashmem GET_PIN_STATUS -> PINNED".to_string()
        }
        _ => {
            skip_syscall(pid, regs, pend, 0);
            "ashmem ioctl (accepted)".to_string()
        }
    }
}

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
        // /dev/ashmem is NOT mapped here anymore: the host
        // device is policy-denied to app processes, so opens
        // are intercepted earlier (entry_open_ashmem) and the
        // device is virtualized outright.
        "/dev/zero" => Some("/dev/zero".to_string()),
        "/dev/urandom" | "/dev/random" => Some("/dev/urandom".to_string()),
        "/dev/__kmsg__" => Some(format!("{rootfs}/.kmsg")),
        // The virtual framebuffer (S6): a plain shared file
        // the shell creates per session; the guest maps it
        // and draws, the shell reads pages back and shows
        // them. Its ioctls are answered by entry_fb_ioctl.
        "/dev/graphics/fb0" => Some(format!("{rootfs}/.fb0")),
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

/// Compat accept(285): absent from the host app seccomp
/// allowlist entirely -- Android 12's bionic SYSCALLS.TXT defines
/// only accept4 for arm, so GB init is killed by SIGSYS the
/// first time a property write arrives (S4b fourth shot: init
/// died at its accept on the property socket). accept4(366)
/// with flags=0 is the identical operation. Rewrite the number
/// in both the tracee-visible register and the dispatch field,
/// zero the flags argument, and arm a rescue-only fallback: if
/// this device's filter nevertheless evaluates the original
/// number and traps, the pending record lets the SIGSYS rescue
/// keep init alive with a fabricated -EAGAIN (its property
/// handler treats that as "no connection" and returns to the
/// poll loop; that client's write is lost, and both the rescue
/// line and this description say so plainly).
fn entry_accept(pid: i32, regs: &mut Regs, pend: &mut Pending) -> String {
    regs.set_nr(366);
    regs.set_arg(3, 0);
    if !set_syscallno(pid, 366) {
        sup!(
            "WARN: NT_ARM_SYSTEM_CALL set(366) failed pid={pid} errno={}",
            errno()
        );
    }
    pend.inject = Some(-(libc::EAGAIN as i64));
    pend.rescue_only = true;
    "accept(285) -> accept4(366) rewritten (rescue armed: -EAGAIN if trapped)".to_string()
}

/// Compat sigprocmask(126), proxied onto a per-process
/// virtual mask (0.9.25). The call normally passes its
/// entry stop and runs on the host -- but from some
/// libc stubs this device's seccomp filter traps it
/// with SIGSYS anyway, and with no pending record the
/// rescue cannot fire: in the 0.9.23 device run gbprobe
/// died of SIGSYS inside the dynamic linker's signal
/// masking while loading libGLESv1_CM.so, right after
/// its surface flow had completed. Cancelling at entry
/// and answering from a virtual mask takes the host out
/// of the loop. The mask is bookkeeping only: signal
/// delivery is NOT filtered by it (the tracee's real
/// host-side mask belongs to the app process and must
/// not be bent per-guest). Callers such as abort() --
/// unmask, then raise -- still get their intended
/// outcome, because the raise itself is delivered
/// through the normal fatal-signal path.
fn entry_sigprocmask(
    pid: i32,
    regs: &mut Regs,
    pend: &mut Pending,
    mask: &mut u32,
) -> String {
    let how = regs.arg(0);
    let setp = regs.arg(1);
    let oldp = regs.arg(2);
    if oldp != 0 && write_mem(pid, oldp, &mask.to_ne_bytes()).is_err() {
        skip_syscall(pid, regs, pend, -14);
        return "sigprocmask(126) oldset write failed -> -EFAULT".to_string();
    }
    if setp != 0 {
        let Some(b) = read_mem_vec(pid, setp, 4) else {
            skip_syscall(pid, regs, pend, -14);
            return "sigprocmask(126) set unreadable -> -EFAULT".to_string();
        };
        let new = u32::from_ne_bytes(b[..4].try_into().unwrap());
        match how {
            0 => *mask |= new,
            1 => *mask &= !new,
            2 => *mask = new,
            _ => {
                skip_syscall(pid, regs, pend, -22);
                return format!("sigprocmask(126) bad how={how} -> -EINVAL");
            }
        }
    }
    skip_syscall(pid, regs, pend, 0);
    format!("sigprocmask(126) proxied (virtual mask now 0x{mask:08x})")
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
/// Read the PT_INTERP string of an ELF file on the host, if it
/// has one. Used to spot dynamic guest binaries: the host kernel
/// cannot resolve their guest-absolute interpreter path, so the
/// exec is rerouted to the manual loader instead (S4).
fn elf_interp_of(host_path: &str) -> Option<String> {
    use std::io::{Read, Seek, SeekFrom};
    let mut f = std::fs::File::open(host_path).ok()?;
    let mut hdr = [0u8; 64];
    f.read_exact(&mut hdr).ok()?;
    if &hdr[0..4] != b"\x7fELF" {
        return None;
    }
    let is32 = hdr[4] == 1;
    let (phoff, phentsize, phnum): (u64, u64, u64) = if is32 {
        (
            u32::from_le_bytes(hdr[28..32].try_into().ok()?) as u64,
            u16::from_le_bytes(hdr[42..44].try_into().ok()?) as u64,
            u16::from_le_bytes(hdr[44..46].try_into().ok()?) as u64,
        )
    } else {
        (
            u64::from_le_bytes(hdr[32..40].try_into().ok()?),
            u16::from_le_bytes(hdr[54..56].try_into().ok()?) as u64,
            u16::from_le_bytes(hdr[56..58].try_into().ok()?) as u64,
        )
    };
    if phnum == 0 || phnum > 128 || phentsize == 0 {
        return None;
    }
    for i in 0..phnum {
        let mut ph = [0u8; 56];
        f.seek(SeekFrom::Start(phoff + i * phentsize)).ok()?;
        let take = (phentsize as usize).min(56);
        f.read_exact(&mut ph[..take]).ok()?;
        let p_type = u32::from_le_bytes(ph[0..4].try_into().ok()?);
        if p_type != 3 {
            continue; // PT_INTERP
        }
        let (off, size): (u64, u64) = if is32 {
            (
                u32::from_le_bytes(ph[4..8].try_into().ok()?) as u64,
                u32::from_le_bytes(ph[16..20].try_into().ok()?) as u64,
            )
        } else {
            (
                u64::from_le_bytes(ph[8..16].try_into().ok()?),
                u64::from_le_bytes(ph[32..40].try_into().ok()?),
            )
        };
        if size == 0 || size > 512 {
            return None;
        }
        let mut buf = vec![0u8; size as usize];
        f.seek(SeekFrom::Start(off)).ok()?;
        f.read_exact(&mut buf).ok()?;
        if buf.last() == Some(&0) {
            buf.pop();
        }
        return Some(String::from_utf8_lossy(&buf).into_owned());
    }
    None
}

/// Reroute an execve/execveat to the manual ELF loader: the
/// filename becomes the loader (a host path in nativeLibraryDir),
/// and a fresh argv is built in stack scratch space:
/// [target guest path, orig argv[0], orig argv[1], ..., NULL].
/// The loader's own argv[0] slot carries the target; the program
/// argv follows. envp is untouched. Returns false when the guest
/// argv is unreadable or too large for the scratch budget.
fn rewrite_exec_to_loader(
    pid: i32,
    compat: bool,
    path_arg: usize,
    loader_path: &str,
    target_guest: &str,
    regs: &mut Regs,
) -> bool {
    let argv_ptr = regs.arg(path_arg + 1);
    let ptr_size: u64 = if compat { 4 } else { 8 };
    // Read the guest argv pointer array and strings.
    let mut args: Vec<String> = Vec::new();
    let mut total: usize = target_guest.len() + 1;
    if argv_ptr != 0 {
        for i in 0..64u64 {
            let mut raw = [0u8; 8];
            if read_mem(pid, argv_ptr + i * ptr_size, &mut raw[..ptr_size as usize]).is_err() {
                return false;
            }
            let p = if compat {
                u32::from_le_bytes(raw[..4].try_into().unwrap()) as u64
            } else {
                u64::from_le_bytes(raw)
            };
            if p == 0 {
                break;
            }
            match read_path(pid, p) {
                Some(s) => {
                    total += s.len() + 1;
                    args.push(s);
                }
                None => return false,
            }
        }
    }
    if total > 3000 {
        return false;
    }
    // Scratch layout below sp: strings first (target, args,
    // loader), then the pointer array.
    let mut cursor = regs.sp().saturating_sub(4096);
    let Some(target_addr) = scratch_write(pid, &mut cursor, target_guest) else {
        return false;
    };
    let mut arg_addrs: Vec<u64> = Vec::new();
    for a in &args {
        match scratch_write(pid, &mut cursor, a) {
            Some(x) => arg_addrs.push(x),
            None => return false,
        }
    }
    let Some(loader_addr) = scratch_write(pid, &mut cursor, loader_path) else {
        return false;
    };
    let n_words = (arg_addrs.len() + 2) as u64; // target + args + NULL
    cursor = cursor.saturating_sub(n_words * ptr_size) & !(ptr_size - 1);
    let array_addr = cursor;
    let mut words: Vec<u8> = Vec::new();
    let mut push_word = |v: u64, words: &mut Vec<u8>| {
        if compat {
            words.extend_from_slice(&(v as u32).to_le_bytes());
        } else {
            words.extend_from_slice(&v.to_le_bytes());
        }
    };
    push_word(target_addr, &mut words);
    for a in &arg_addrs {
        push_word(*a, &mut words);
    }
    push_word(0, &mut words);
    if write_mem(pid, array_addr, &words).is_err() {
        return false;
    }
    regs.set_arg(path_arg, loader_addr);
    regs.set_arg(path_arg + 1, array_addr);
    true
}

fn entry_exec(
    pid: i32,
    rootfs: &str,
    bb_native: &str,
    loader_path: &str,
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
        let host = format!("{rootfs}{final_abs}");
        // Dynamic ELF (S4): the host kernel cannot resolve the
        // guest-absolute PT_INTERP, so hand the exec to the manual
        // loader, which maps the target and its linker itself.
        if !loader_path.is_empty() {
            if let Some(interp) = elf_interp_of(&host) {
                if rewrite_exec_to_loader(pid, compat, path_arg, loader_path, &abs, regs) {
                    return (
                        format!("exec '{gpath}' -> gbloader (dynamic, interp {interp})"),
                        true,
                    );
                }
                skip_syscall(pid, regs, pend, -EACCES);
                return (
                    format!("exec '{gpath}' BLOCKED (dynamic, loader argv rewrite failed) -> -EACCES"),
                    true,
                );
            }
        }
        // A real rootfs file that is not busybox: filesDir cannot be
        // exec'd, and M1 opens no other door. #! scripts land here.
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
    // Optional "--loader <path>" (before "--"): the manual ELF
    // loader that dynamic guest binaries are rerouted to (S4).
    // Empty when the session has no loader payload.
    let loader_path = match argv.iter().position(|a| a == "--loader") {
        Some(i) if i + 1 < argv.len() && argv[i + 1] != "--" => argv[i + 1].clone(),
        _ => String::new(),
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
    // Virtual credentials per tracee (guest-world uid/gid). The
    // whole guest tree really runs under the host app uid; this
    // map is the guest's belief: the root starts as 0/0,
    // children inherit, the emulated set*id family updates it,
    // the get*id family reports it, and SO_PEERCRED answers are
    // rewritten from it (see patch_peercred). Kept outside
    // ProcState so the exit-stop handler can consult a peer's
    // creds while another ProcState is borrowed.
    let mut vcreds: HashMap<i32, (u32, u32)> = HashMap::new();
    vcreds.insert(root_pid, (0, 0));
    // The virtual binder driver (S5): all state lives here,
    // keyed by arena host path; wakes collects parked tracees
    // to complete after each entry stop.
    let mut binder = BinderState::default();
    let mut wakes: Vec<i32> = Vec::new();
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
            vcreds.remove(&pid);
            if let Some(a) = binder.thread_arena.remove(&pid) {
                if let Some(bp) = binder.procs.get_mut(&a) {
                    bp.loopers.remove(&pid);
                }
                // S5c: if that was the arena's last thread,
                // run the driver's death processing; it may
                // wake parked tracees (death notices, dead
                // replies), completed like any other wake.
                let mut dwakes: Vec<i32> = Vec::new();
                binder_on_proc_exit(&a, &mut binder, &mut dwakes);
                for wpid in dwakes {
                    if wpid != pid {
                        complete_parked(wpid, &mut procs, &mut binder);
                    }
                }
            }
            binder.parked.remove(&pid);
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
            vcreds.entry(pid).or_insert((0, 0));
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
                    rescue_only: false,
                    peercred: None,
                    binder_parked: false,
                    mmap_binder: None,
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
                        &loader_path,
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
                                &mut binder,
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
                } else if proc.compat && nr == 285 {
                    // Compat accept: rewritten to accept4 (see
                    // entry_accept).
                    pend.desc = Some(entry_accept(pid, &mut regs, &mut pend));
                    dirty = true;
                } else if proc.compat && nr == 126 {
                    // Compat sigprocmask: proxied onto a
                    // virtual mask (see entry_sigprocmask).
                    pend.desc = Some(entry_sigprocmask(
                        pid,
                        &mut regs,
                        &mut pend,
                        &mut proc.sigmask,
                    ));
                    dirty = true;
                } else if proc.compat && nr == 125 && (regs.arg(2) & 0x4) != 0 {
                    // Telemetry only (0.9.26): an mprotect
                    // that adds PROT_EXEC passes through
                    // untouched, but the desc makes the exit
                    // stop print the host's verdict.
                    // Pixelflinger's Assembly frees its code
                    // buffer and NULLs the base when this
                    // call fails (ensureMbaseExecutable),
                    // and the assembler then emits into
                    // address 0 -- the SurfaceFlinger
                    // +0xec0a crash signature (mPC=0,
                    // prologue word in hand).
                    pend.desc = Some(format!(
                        "mprotect EXEC addr=0x{:x} len={} prot={:#x}",
                        regs.arg(0),
                        regs.arg(1),
                        regs.arg(2)
                    ));
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
                        &mut binder,
                    ));
                    dirty = true;
                } else if is_getid(proc.compat, nr) {
                    // Answered from the virtual credentials:
                    // inside the guest world this process has the
                    // identity its set*id history says it has.
                    let creds = vcreds.get(&pid).copied().unwrap_or((0, 0));
                    let v = if getid_is_uid(proc.compat, nr) {
                        creds.0
                    } else {
                        creds.1
                    };
                    skip_syscall(pid, &mut regs, &mut pend, v as i64);
                    pend.desc = Some(format!(
                        "{}({}) FAKED -> {v} (virtual creds)",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else if is_setid_emulated(proc.compat, nr) {
                    // Cancel before the kernel (and its seccomp
                    // filter) ever evaluates it; answer 0 at the
                    // exit stop via the standard inject path. The
                    // call also updates the virtual credentials.
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    let creds = vcreds.entry(pid).or_insert((0, 0));
                    apply_setid(proc.compat, nr, &regs, creds);
                    let (vu, vg) = *creds;
                    pend.desc = Some(format!(
                        "{}({}) emulated (return 0); virtual creds now uid={vu} gid={vg}",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else if ((proc.compat && nr == 192) || (!proc.compat && nr == 222))
                    && fd_arena(pid, regs.arg(4) as i32).is_some()
                {
                    // mmap on a binder arena: flip PRIVATE to
                    // SHARED so driver writes are visible.
                    let arena = fd_arena(pid, regs.arg(4) as i32).unwrap();
                    let flags = regs.arg(3);
                    regs.set_arg(3, (flags & !2) | 1);
                    binder.thread_arena.insert(pid, arena.clone());
                    pend.mmap_binder = Some((arena, regs.arg(1) as u32));
                    pend.desc = Some(format!(
                        "mmap({nr}) pid={pid} binder arena (PRIVATE -> SHARED for driver writes)"
                    ));
                    dirty = true;
                } else if ((proc.compat && nr == 192) || (!proc.compat && nr == 222))
                    && regs.arg(2) & 4 != 0
                {
                    // Telemetry only: any executable mapping.
                    // A JIT code buffer must be mapped
                    // PROT_EXEC; if the host policy denies
                    // that on our file-backed ashmem, the
                    // exit stop shows the failure here.
                    let fdname = fd_ashmem(pid, regs.arg(4) as i32)
                        .or_else(|| fd_arena(pid, regs.arg(4) as i32))
                        .unwrap_or_else(|| {
                            format!("fd {}", regs.arg(4) as i32)
                        });
                    pend.desc = Some(format!(
                        "mmap({nr}) pid={pid} EXEC prot={} len={} on {} (passed through)",
                        regs.arg(2),
                        regs.arg(1),
                        fdname.rsplit('/').next().unwrap_or("").to_string()
                    ));
                } else if ((proc.compat && nr == 192) || (!proc.compat && nr == 222))
                    && fd_ashmem(pid, regs.arg(4) as i32).is_some()
                {
                    // Telemetry only: the call still passes
                    // through untouched; the exit stop notes
                    // that a virtual ashmem file was mapped.
                    let key = fd_ashmem(pid, regs.arg(4) as i32).unwrap();
                    let name = key.rsplit('/').next().unwrap_or("").to_string();
                    pend.desc = Some(format!(
                        "mmap({nr}) pid={pid} virtual ashmem {name} len={} prot={} flags=0x{:x} (passed through)",
                        regs.arg(1),
                        regs.arg(2),
                        regs.arg(3)
                    ));
                } else if ((proc.compat && nr == 54) || (!proc.compat && nr == 29))
                    && matches!(
                        regs.arg(1) as u32,
                        ASHMEM_SET_NAME
                            | ASHMEM_GET_NAME
                            | ASHMEM_SET_SIZE
                            | ASHMEM_GET_SIZE
                            | ASHMEM_SET_PROT_MASK
                            | ASHMEM_GET_PROT_MASK
                            | ASHMEM_PIN
                            | ASHMEM_UNPIN
                            | ASHMEM_GET_PIN_STATUS
                            | ASHMEM_PURGE_ALL_CACHES
                    )
                    && fd_ashmem(pid, regs.arg(0) as i32).is_some()
                {
                    // Virtual ashmem ioctls (S6b).
                    let key = fd_ashmem(pid, regs.arg(0) as i32).unwrap();
                    pend.desc = Some(entry_ashmem_ioctl(
                        pid,
                        &key,
                        regs.arg(1) as u32,
                        &mut regs,
                        &mut pend,
                        &mut binder,
                    ));
                    dirty = true;
                } else if ((proc.compat && nr == 54) || (!proc.compat && nr == 29))
                    && matches!(
                        regs.arg(1) as u32,
                        FBIOGET_VSCREENINFO
                            | FBIOPUT_VSCREENINFO
                            | FBIOGET_FSCREENINFO
                            | FBIOPAN_DISPLAY
                            | FBIO_WAITFORVSYNC
                    )
                    && fd_is_fb(pid, regs.arg(0) as i32)
                {
                    // Virtual framebuffer ioctls (S6): the
                    // geometry answers and the pan bookkeeping
                    // live in entry_fb_ioctl.
                    pend.desc = Some(entry_fb_ioctl(
                        pid,
                        &rootfs,
                        regs.arg(1) as u32,
                        &mut regs,
                        &mut pend,
                    ));
                    dirty = true;
                } else if ((proc.compat && nr == 54) || (!proc.compat && nr == 29))
                    && matches!(
                        regs.arg(1) as u32,
                        BINDER_WRITE_READ
                            | BINDER_SET_IDLE_TIMEOUT
                            | BINDER_SET_MAX_THREADS
                            | BINDER_SET_IDLE_PRIORITY
                            | BINDER_SET_CONTEXT_MGR
                            | BINDER_THREAD_EXIT
                            | BINDER_VERSION
                    )
                    && fd_arena(pid, regs.arg(0) as i32).is_some()
                {
                    let arena = fd_arena(pid, regs.arg(0) as i32).unwrap();
                    binder.thread_arena.insert(pid, arena.clone());
                    match regs.arg(1) as u32 {
                        BINDER_VERSION => {
                            let _ = write_mem(pid, regs.arg(2), &7u32.to_le_bytes());
                            skip_syscall(pid, &mut regs, &mut pend, 0);
                            pend.desc = Some("binder VERSION -> 7".to_string());
                        }
                        BINDER_SET_CONTEXT_MGR => {
                            let ok = match &binder.mgr_arena {
                                None => {
                                    binder.mgr_arena = Some(arena.clone());
                                    let n = binder.node_for_local(&arena, 0, 0);
                                    binder.mgr_node = Some(n);
                                    true
                                }
                                Some(a) => *a == arena,
                            };
                            if ok && !binder.mgr_pending.is_empty() {
                                // Deliver everything clients
                                // addressed to the manager
                                // before it existed (0.9.24);
                                // their senders are parked in
                                // their read sides and complete
                                // through the normal wake path.
                                let node = binder.mgr_node.unwrap();
                                let (nptr, ncookie) = {
                                    let nd = &binder.nodes[node];
                                    (nd.ptr, nd.cookie)
                                };
                                let queued: Vec<PendingMgrTxn> =
                                    std::mem::take(&mut binder.mgr_pending);
                                let total = queued.len();
                                let mut delivered = 0;
                                for q in queued {
                                    sup!(
                                        "binder: flushing queued mgr txn from pid={} code={}",
                                        q.sender_pid, q.code
                                    );
                                    if !binder.procs.contains_key(&q.sender_arena) {
                                        sup!(
                                            "binder: queued mgr txn from pid={} dropped (sender arena gone)",
                                            q.sender_pid
                                        );
                                        continue;
                                    }
                                    let mut qnotes: Vec<String> = Vec::new();
                                    binder_send_txn(
                                        &mut binder,
                                        &mut wakes,
                                        &mut qnotes,
                                        &q.sender_arena,
                                        q.sender_pid,
                                        q.target_handle,
                                        q.cookie,
                                        nptr,
                                        ncookie,
                                        &arena,
                                        q.code,
                                        q.flags,
                                        q.veuid,
                                        &q.data,
                                        &q.offs,
                                    );
                                    delivered += 1;
                                }
                                sup!(
                                    "binder: SET_CONTEXT_MGR flushed {delivered}/{total} queued manager transaction(s)"
                                );
                            }
                            skip_syscall(pid, &mut regs, &mut pend, if ok { 0 } else { -1 });
                            pend.desc = Some(format!(
                                "binder SET_CONTEXT_MGR -> {}",
                                if ok {
                                    "ok (this process is the context manager)"
                                } else {
                                    "denied (a manager already exists)"
                                }
                            ));
                        }
                        BINDER_THREAD_EXIT => {
                            if let Some(bp) = binder.procs.get_mut(&arena) {
                                bp.loopers.remove(&pid);
                            }
                            binder.parked.remove(&pid);
                            skip_syscall(pid, &mut regs, &mut pend, 0);
                            pend.desc = Some("binder THREAD_EXIT".to_string());
                        }
                        BINDER_WRITE_READ => {
                            pend.desc = Some(binder_write_read(
                                pid,
                                proc.compat,
                                &arena,
                                &mut regs,
                                &mut pend,
                                &mut binder,
                                &vcreds,
                                &mut wakes,
                            ));
                        }
                        req => {
                            skip_syscall(pid, &mut regs, &mut pend, 0);
                            pend.desc = Some(format!("binder ioctl {req:#010x} (no-op)"));
                        }
                    }
                    dirty = true;
                } else if ((proc.compat && nr == 295) || (!proc.compat && nr == 209))
                    && regs.arg(1) == 1
                    && regs.arg(2) == 17
                {
                    // getsockopt(SOL_SOCKET, SO_PEERCRED): the
                    // call passes through untouched; at the exit
                    // stop the returned ucred is rewritten to
                    // the peer's virtual credentials.
                    pend.peercred = Some((regs.arg(3), regs.arg(4)));
                    pend.desc = Some(format!(
                        "getsockopt({nr}) SO_PEERCRED (virtual creds patch armed)"
                    ));
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
                let parked = pend.binder_parked;
                if dirty {
                    set_regs(pid, &regs);
                }
                // A WRITE_READ whose entry handling rode fd
                // fixup injections has already consumed its
                // entry->exit transition and applied its fake
                // result (pend.applied): the next stop is a
                // fresh entry stop, not this call's exit.
                let transition_consumed = pend.applied;
                proc.pending = Some(pend);
                proc.expect_exit = !transition_consumed;
                if !parked {
                    cont_syscall(pid, 0);
                }
                // Complete parked binder ioctls this stop's
                // work woke (other tracees only; our own read
                // side was settled inline or parked above).
                for wpid in std::mem::take(&mut wakes) {
                    if wpid != pid {
                        complete_parked(wpid, &mut procs, &mut binder);
                    }
                }
            } else {
                // ---- syscall-exit stop ----
                if let Some(mut pend) = proc.pending.take() {
                    if let Some(mut regs) = get_regs(pid, proc.compat) {
                        let mut ret = regs.retval();
                        if let Some(v) = pend.inject {
                            if !pend.rescue_only {
                                regs.set_retval(v);
                                if set_regs(pid, &regs) {
                                    pend.applied = true;
                                }
                                ret = v;
                            }
                        }
                        if let Some(d) = &pend.desc {
                            sys!("{d} => {ret}");
                        }
                        if proc.compat && pend.nr == 125 && ret < 0 {
                            // Telemetry (0.9.26): any failing
                            // compat mprotect, exec or not --
                            // the mspace growth path also
                            // mprotects, and its failure
                            // NULLs allocations the same way.
                            sup!("mprotect FAILED pid={pid} ret={ret}");
                        }
                        if let Some((optval, optlen)) = pend.peercred {
                            if ret == 0 {
                                patch_peercred(pid, optval, optlen, &vcreds);
                            }
                        }
                        if let Some((arena, maplen)) = &pend.mmap_binder {
                            // mmap success is a u32 test, not
                            // `ret > 0`: guest bases sit above
                            // 0x80000000, whose sign-extended
                            // i64 form is negative -- with the
                            // signed test no base was ever
                            // recorded and every delivery failed
                            // (0.6.4 device run).
                            let r32 = ret as u32;
                            if r32 != 0 && r32 < 0xFFFFF001 {
                                if let Some(bp) = binder.procs.get_mut(arena) {
                                    bp.base.insert(pid, r32);
                                    bp.maplen.insert(pid, *maplen);
                                }
                            }
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
                let parent_creds = vcreds.get(&pid).copied().unwrap_or((0, 0));
                vcreds.insert(child, parent_creds);
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
                let fregs = get_regs(pid, fcompat);
                let pc = fregs.as_ref().map(|r| r.pc()).unwrap_or(0);
                let regdump = fregs
                    .as_ref()
                    .map(|r| {
                        format!(
                            " r0=0x{:x} r1=0x{:x} r2=0x{:x} r3=0x{:x} sp=0x{:x}",
                            r.arg(0),
                            r.arg(1),
                            r.arg(2),
                            r.arg(3),
                            r.sp()
                        )
                    })
                    .unwrap_or_default();
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
                        "FATAL sig={sig} pid={pid} pc=0x{pc:x} fault_addr=0x{addr:x}{regdump}"
                    );
                } else {
                    sup!("FATAL sig={sig} pid={pid} pc=0x{pc:x} (no siginfo){regdump}");
                }
                // Memory around the crash (0.9.24): on this
                // device GETSIGINFO fails, so the fault
                // address is usually unknown. The bytes at
                // pc name the faulting instruction; the
                // bytes at the data registers show what the
                // code was about to touch (e.g. the
                // pixelflinger JIT's emission pointer).
                if sig == 11 {
                    if let Some(r) = &fregs {
                        let hexat = |addr: u64, n: usize| -> String {
                            match read_mem_vec(pid, addr, n) {
                                Some(b) => b
                                    .iter()
                                    .map(|x| format!("{x:02x}"))
                                    .collect::<Vec<_>>()
                                    .concat(),
                                None => "??".to_string(),
                            }
                        };
                        let mut line = format!(
                            "FATAL mem pid={pid} pc@0x{:x}: {}",
                            pc & !1,
                            hexat(pc & !1, 16)
                        );
                        for (nm, v) in
                            [("r2", r.arg(2)), ("r3", r.arg(3)), ("sp", r.sp())]
                        {
                            if v > 0x10000 {
                                line += &format!(
                                    " {nm}@0x{v:x}: {}",
                                    hexat(v, 16)
                                );
                            }
                        }
                        sup!("{line}");
                    }
                }
                // Name the guest library the crash pc lives
                // in, from the dying thread's memory map, so
                // a bare address becomes a library and an
                // offset in the next reading.
                if sig == 11 || sig == 6 {
                    if let Ok(maps) = std::fs::read_to_string(format!("/proc/{pid}/maps")) {
                        for line in maps.lines() {
                            let mut it = line.split_whitespace();
                            let Some(range) = it.next() else { continue };
                            let Some((lo, hi)) = range.split_once('-') else {
                                continue;
                            };
                            let lo = u64::from_str_radix(lo, 16).unwrap_or(0);
                            let hi = u64::from_str_radix(hi, 16).unwrap_or(0);
                            if pc >= lo && pc < hi {
                                let name = line.rsplit('/').next().unwrap_or("?");
                                sup!(
                                    "FATAL map: pc in {} (+0x{:x})",
                                    name.trim(),
                                    pc - lo
                                );
                                break;
                            }
                        }
                    }
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
