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

use std::collections::{HashMap, HashSet, VecDeque};
use std::ffi::CString;
use std::io::{Read, Write};
use std::os::unix::fs::FileExt;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};
use std::sync::Mutex;

// ---- ptrace constants (raw; bionic ptrace takes c_int) ----
const PTRACE_TRACEME: i32 = 0;
const PTRACE_PEEKDATA: i32 = 2;
const PTRACE_POKEDATA: i32 = 5;
const PTRACE_ATTACH: i32 = 16;
const PTRACE_DETACH: i32 = 17;
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
// Batched since S7's field runs: a zygote preload makes
// the guest issue ~70k logged calls in a few minutes,
// and a flush per line put a pipe write on the
// supervisor's critical path for every one of them --
// the phone's interface stuttered for exactly that
// stretch (user-reported twice). [sys] lines now
// accumulate and flush at 16 KB or 100 ms, whichever
// comes first; [sup] lines (state changes, verdicts)
// still flush immediately, so nothing a human is
// waiting on is ever delayed and no content is lost.
struct OutState {
    buf: String,
    last: std::time::Instant,
}
static OUT: Mutex<Option<OutState>> = Mutex::new(None);

/// S2 log attribution: which tracer process emitted the
/// line (0 = W0, the main supervisor; 1.. = workers). Set
/// once per process before its first emit.
static WID: AtomicU32 = AtomicU32::new(0);

/// Direct mirror logs. The shell's session log dies
/// with the app -- twice in the 0.9.59/0.9.60 field
/// runs the crashed session's record was trapped
/// behind the reopened app's rotation stub and could
/// not be downloaded. Each tracer therefore mirrors
/// its own emitted lines to
/// supervisor-direct-w<wid>.log (W0 rotates the
/// previous session's mirrors to *-prev.log first).
/// 0.9.61: the directory was the vm directory (the
/// rootfs parent). 0.9.78: the shell passes
/// --logdir <path> pointing at this launch's
/// directory in the app's external files dir
/// (Android/data/...), a real path these native
/// processes can write and the user can read without
/// the app -- the Download folder proper is
/// MediaStore-only and unreachable from here -- so
/// the mirrors are written live, next to the session
/// log's directory name, as the session runs. Without
/// --logdir the vm directory is used as before.
static DIRECT_DIR: std::sync::OnceLock<String> = std::sync::OnceLock::new();

/// The --logdir override, scanned from argv on every
/// call: the coordinator and the shard workers are
/// forked from W0 and inherit its argv, so no extra
/// plumbing is needed to carry it to them.
fn logdir_override() -> Option<String> {
    let argv: Vec<String> = std::env::args().collect();
    match argv.iter().position(|a| a == "--logdir") {
        Some(i) if i + 1 < argv.len() && argv[i + 1] != "--" => {
            Some(argv[i + 1].clone())
        }
        _ => None,
    }
}

fn set_direct_log_dir(rootfs: &str, rotate: bool) {
    let dir = match logdir_override() {
        Some(d) => d,
        None => match rootfs.rfind('/') {
            Some(i) if i > 0 => rootfs[..i].to_string(),
            _ => return,
        },
    };
    if rotate {
        for w in 0..=6u32 {
            let cur = format!("{dir}/supervisor-direct-w{w}.log");
            let prev = format!("{dir}/supervisor-direct-w{w}-prev.log");
            if std::path::Path::new(&cur).exists() {
                let _ = std::fs::remove_file(&prev);
                let _ = std::fs::rename(&cur, &prev);
            }
        }
    }
    let _ = DIRECT_DIR.set(dir);
}

/// 0.9.141 (s9-141-desk S6): per-process count of
/// lines handed to emit(); the servicer-face age
/// field is the distance, in this worker's own
/// emitted lines, between a tracee's last processed
/// stop and the snapshot instant. Counted here so
/// every emitter (sup!/sys!/direct writers) shares
/// one sequence.
static EMIT_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn emit_seq_now() -> u64 {
    EMIT_SEQ.load(Ordering::Relaxed)
}

fn emit(tag: &str, msg: &str) {
    EMIT_SEQ.fetch_add(1, Ordering::Relaxed);
    let mut g = OUT.lock().unwrap_or_else(|p| p.into_inner());
    let st = g.get_or_insert_with(|| OutState {
        buf: String::new(),
        last: std::time::Instant::now(),
    });
    st.buf.push_str("[W");
    st.buf.push_str(&WID.load(Ordering::Relaxed).to_string());
    st.buf.push(' ');
    st.buf.push_str(tag);
    st.buf.push_str("] ");
    st.buf.push_str(msg);
    st.buf.push('\n');
    if tag != "sys"
        || st.buf.len() >= 16384
        || st.last.elapsed() >= std::time::Duration::from_millis(100)
    {
        let stdout = std::io::stdout();
        let mut h = stdout.lock();
        let _ = h.write_all(st.buf.as_bytes());
        let _ = h.flush();
        if let Some(dir) = DIRECT_DIR.get() {
            let path = format!(
                "{dir}/supervisor-direct-w{}.log",
                WID.load(Ordering::Relaxed)
            );
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
            {
                let _ = f.write_all(st.buf.as_bytes());
            }
        }
        st.buf.clear();
        st.last = std::time::Instant::now();
    }
}

macro_rules! sup {
    ($($a:tt)*) => { emit("sup", &format!($($a)*)) };
}
macro_rules! sys {
    ($($a:tt)*) => { emit("sys", &format!($($a)*)) };
}

/// Decision-side log: lines the binder family produces
/// while deciding belong to the coordinator's reply, not
/// to the log stream, so they are captured (cap_log) and
/// replayed by the tracer at the original emit point.
macro_rules! bsup {
    ($($a:tt)*) => { cap_log("sup", &format!($($a)*)) };
}

/// Freeze forensics (0.9.81): leave W0's pid where
/// the shell can find it -- supervisor.pid in the vm
/// directory. The vm directory is the rootfs's
/// parent, deliberately NOT the --logdir override
/// directory: that one belongs to this launch's log
/// mirrors, while the pid file is a property of the
/// vm slot itself. The shell's stack-dump menu entry
/// reads the pid and sends SIGUSR2 (see on_sigusr2).
/// Written once at startup; the pid is W0's own, so
/// no plumbing carries it anywhere. A failed write
/// costs the menu entry, not the run.
fn write_supervisor_pid(rootfs: &str) {
    let dir = match rootfs.rfind('/') {
        Some(i) if i > 0 => &rootfs[..i],
        _ => {
            sup!("supervisor.pid: rootfs {rootfs} has no parent; dump menu unavailable");
            return;
        }
    };
    let path = format!("{dir}/supervisor.pid");
    match std::fs::write(&path, format!("{}", std::process::id())) {
        Ok(()) => sup!("supervisor pid recorded at {path}"),
        Err(e) => {
            sup!("supervisor.pid write failed ({path}): {e}; dump menu unavailable")
        }
    }
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

// ---- Freeze forensics (0.9.81): the shell's guest
// stack-dump request. The shell cannot speak the
// coordinator protocol, so it signals W0 with
// SIGUSR2 (W0's pid is left in the vm directory's
// supervisor.pid for it to find). The handler's whole
// job is setting this flag -- async-signal-safe: no
// allocation, no locking, no I/O. W0's event loop
// notices it at its coordinator-service point
// (next_stop) and relays the request over the
// coordinator socket like any other oneway. The
// handler is installed with no SA_RESTART for the
// same reason as the SIGCHLD self-pipe's handler
// below: the loop sleeps in poll, and during a guest
// freeze nothing else may arrive to wake it -- the
// signal itself has to interrupt the poll, and the
// loop treats the resulting EINTR as a free pass.
static DUMP_REQ: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

extern "C" fn on_sigusr2(_sig: i32) {
    DUMP_REQ.store(true, Ordering::Relaxed);
}

/// Install the SIGUSR2 handler. Called from main on
/// W0's parent path only, after the coordinator, the
/// workers and the guest root have all been forked:
/// none of them inherits the handler, and the flag is
/// only ever checked in W0's loop besides.
fn install_dump_signal() {
    unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = on_sigusr2 as *const () as usize;
        sa.sa_flags = 0;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(libc::SIGUSR2, &sa, std::ptr::null_mut());
    }
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
    /// A compat mprotect in flight: (addr, prot). The exit
    /// stop names the target VMA when the host refuses the
    /// call (0.9.31 telemetry).
    mprot: Option<(u64, u64)>,
    /// 0.9.140 (s9-140-desk-ignition M1): a futex of the
    /// WAIT family (WAIT / WAIT_BITSET) seen at this
    /// call's entry stop: (uaddr, op, val) exactly as the
    /// guest passed them, op masked to the command bits.
    /// The record lives in this call's Pending, which is
    /// exactly the span the thread sits inside the wait,
    /// so at wedge-snapshot time it names the wait the
    /// thread is frozen in; the next entry stop's fresh
    /// Pending replaces it, as with every field here.
    last_futex: Option<(u32, u32, u32)>,
    /// 0.9.140 (M1): the same for the WAKE family
    /// (WAKE / WAKE_BITSET): (uaddr, nr_wake). See
    /// last_futex.
    last_wake: Option<(u32, u32)>,
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
    /// 0.9.102 forensics: this thread's most recent binder
    /// read fill (guest read_buf addr, fill length), recorded
    /// on both fill paths. At a FATAL the buffer is dumped
    /// from the stopped tracee (FATAL minbuf) so the exact
    /// bytes the guest was consuming can be compared against
    /// the batches the supervisor assembled.
    last_binder_read: Option<(u32, u32)>,
    /// 0.9.108: consecutive pre-entry SIGSYS swallows for
    /// this tracee (reset when an entry stop assigns a
    /// fresh pending record). A cap keeps a pathological
    /// trap from livelocking: past it the signal is
    /// delivered as before.
    sigsys_preentry: u32,
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
    /// S2: the tracer-side parent (the pid whose fork event
    /// announced this tracee; 0 when unknown or adopted).
    /// W0 uses it to recognise direct children of the guest
    /// root for shard handoff.
    parent: i32,
    /// S2: guest-absolute image path decided by the most
    /// recent entry_exec (None when the path could not be
    /// decided); consumed by the handoff decision at that
    /// exec's exit stop.
    exec_path: Option<String>,
    /// S2: the most recent exec was blocked (an injected
    /// result was armed at its entry stop), so the tracee
    /// never really changed image; no handoff for it.
    exec_blocked: bool,
    /// S2: the handoff decision for this tracee (as a
    /// direct child of the guest root) has been made.
    shard_decided: bool,
    /// S2 fix (0.9.60): an exec entry has armed the
    /// handoff decision for the exit stop that settles
    /// THIS exec. The 0.9.59 decision ran at the first
    /// syscall-exit stop of a child's life -- init's
    /// service children do fd setup and credential
    /// syscalls before their execve, so the latch
    /// (shard_decided) burned with exec_path still None
    /// and no service ever handed off.
    exec_armed: bool,
    /// 0.9.141 (s9-141-desk P3): tracer-side assembly
    /// window profile for this thread (see WinProfile).
    /// Telemetry only.
    win: WinProfile,
    /// 0.9.141 (s9-141-desk S6): this worker's emit
    /// sequence at the last stop processed for this
    /// tracee; the servicer-face age field reads it.
    last_stop_seq: u64,
}

/// 0.9.141 (s9-141-desk P3): per-thread counters over
/// the assembly window that ends at the thread's next
/// forwarded BC_REPLY: syscall stops seen, futex WAIT
/// entries, allocator syscalls (brk/mmap/munmap),
/// binder parks, forwarded streams carrying at least
/// one BC_TRANSACTION, and the deepest serving-stack
/// level the supervisor itself drove this thread to
/// in the window (fills delivered to it, less the
/// replies it forwarded out). Maintained tracer-side;
/// a snapshot rides each write_read request and the
/// coordinator prints it on the reply-pop descriptor
/// line. Telemetry only -- nothing reads it back.
#[derive(Default, Clone, Copy)]
struct WinProfile {
    stops: u32,
    futex: u32,
    alloc: u32,
    parks: u32,
    sends: u32,
    depth: i32,
    maxdepth: u32,
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
            parent: 0,
            exec_path: None,
            exec_blocked: false,
            shard_decided: false,
            exec_armed: false,
            last_binder_read: None,
            sigsys_preentry: 0,
            win: WinProfile::default(),
            last_stop_seq: 0,
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

/// The read mirror of set_syscallno -- pt_regs.syscallno
/// as the kernel currently holds it for this stopped
/// tracee. Pure read; the 0.9.139 ride-entry guardrail
/// compares it against the number a rewind ride
/// injected. (It was the 0.9.138 ride photograph's
/// second source before that telemetry retired in
/// 0.9.140, the fd line having closed in .139.)
fn get_syscallno(pid: i32) -> Option<i32> {
    let mut v: i32 = -2;
    let mut iov = libc::iovec {
        iov_base: &mut v as *mut i32 as *mut libc::c_void,
        iov_len: std::mem::size_of::<i32>(),
    };
    if ptrace4(
        PTRACE_GETREGSET,
        pid,
        NT_ARM_SYSTEM_CALL as *mut libc::c_void,
        &mut iov as *mut libc::iovec as *mut libc::c_void,
    ) == 0
    {
        Some(v)
    } else {
        None
    }
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
    coord: &mut CoordClient,
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
                return entry_open_binder(pid, rootfs, compat, nr, regs, coord);
            }
            if guest_abs(vcwd, &p) == "/dev/ashmem" {
                return entry_open_ashmem(pid, rootfs, compat, nr, regs, coord);
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
                    let new = if is_open_family(compat, nr) || is_device_probe(compat, nr) {
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
    let mut desc = format!(
        "{}({}) pid={} {}",
        nr_name(compat, nr),
        nr,
        pid,
        parts.join(", ")
    );
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
    coord: &mut CoordClient,
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
            if ruid != unsafe { libc::getuid() } as u32 {
                // The peer is not a guest tracee at all
                // (a host-side socket): the kernel's answer
                // stands, exactly as before.
                return;
            }
            // S2: the peer may be traced by another
            // worker; the coordinator holds the global
            // credential book. A miss there keeps the old
            // default: the peer speaks for the supervisor
            // itself, (0, 0).
            coord.vcred_query(peer).unwrap_or((0, 0))
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
const BR_DECREFS: u32 = 0x8008_7209;
const BR_RELEASE: u32 = 0x8008_720a;
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

/// Plain bitwise CRC32 (0.9.99 parcel fingerprints; the
/// inputs are a few hundred bytes at a time, so the naive
/// loop is fast enough and needs no table).
fn crc32(bytes: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            crc = if crc & 1 != 0 {
                (crc >> 1) ^ 0xEDB8_8320
            } else {
                crc >> 1
            };
        }
    }
    !crc
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
            // Every 40th pan, also dump the composed page's
            // coarse shape: 20 row bands, each a decile digit
            // of nonzero density, then the busiest band's 8
            // column deciles. Two 1KB windows could not tell
            // a displaced/scaled/ghost composition from an
            // absent one (gun 5, 0.9.34 field run: page
            // windows read ~0/105 while the client's own
            // buffer held the full logo) -- the shape can.
            static PAN_COUNT: std::sync::atomic::AtomicU32 =
                std::sync::atomic::AtomicU32::new(0);
            let shape = if PAN_COUNT
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                % 40
                == 0
            {
                (|| -> Option<String> {
                    use std::os::unix::fs::FileExt;
                    let f = std::fs::File::open(format!("{rootfs}/.fb0")).ok()?;
                    let base = (yoff as u64) * (FB_W as u64) * 4;
                    let mut page = vec![0u8; (FB_W * FB_H * 4) as usize];
                    f.read_exact_at(&mut page, base).ok()?;
                    let band_bytes = page.len() / 20;
                    let mut rows = String::new();
                    let mut best = (0usize, 0usize);
                    for b in 0..20 {
                        let s = &page[b * band_bytes..(b + 1) * band_bytes];
                        let n = s.iter().filter(|x| **x != 0).count();
                        if n > best.1 {
                            best = (b, n);
                        }
                        rows.push(char::from_digit(
                            ((n * 10) / band_bytes).min(9) as u32,
                            10,
                        )?);
                    }
                    let s = &page[best.0 * band_bytes..(best.0 + 1) * band_bytes];
                    let col_bytes = band_bytes / 8;
                    let mut cols = String::new();
                    for c in 0..8 {
                        let cs = &s[c * col_bytes..(c + 1) * col_bytes];
                        let n = cs.iter().filter(|x| **x != 0).count();
                        cols.push(char::from_digit(
                            ((n * 10) / col_bytes).min(9) as u32,
                            10,
                        )?);
                    }
                    // Exact census: nonzero pixel count and
                    // bounding box. Deciles floor out sparse
                    // content (a 64x64 square and thin text
                    // strokes both read 0), so the 0.9.35 run
                    // could not separate 'dim text composed
                    // correctly' from 'content lost'. A bbox
                    // can: the boot wordmark's box is centered
                    // and wide; a displaced or ghosted image
                    // lands somewhere else entirely.
                    let w = FB_W as usize;
                    let (mut px, mut x0, mut y0, mut x1, mut y1) =
                        (0usize, w, FB_H as usize, 0usize, 0usize);
                    for (i, p) in page.chunks_exact(4).enumerate() {
                        if p.iter().any(|b| *b != 0) {
                            px += 1;
                            let (x, y) = (i % w, i / w);
                            x0 = x0.min(x);
                            x1 = x1.max(x);
                            y0 = y0.min(y);
                            y1 = y1.max(y);
                        }
                    }
                    // Shared-stack dump, take 2: the 0.9.40
                    // signature scan found bootanimation's
                    // stack at heap+8 with a perfect
                    // swap-rect dirty, but gbprobe's heap
                    // only validated at +96 with permanently
                    // empty slots -- either its real stack
                    // (at the same +8 as every SharedClient)
                    // failed the plausibility gate, or the
                    // +96 hit is a lookalike inside it. No
                    // more gating: interpret offset +8 of
                    // every mid-size heap as surfaces[0]
                    // verbatim and print the raw fields.
                    // (GB SharedBufferStack.h layout; the
                    // client heaps are exactly 32768 bytes,
                    // both clients provably map the files
                    // SF allocated -- 0.9.40 mmap lines.)
                    let stacks = (|| -> String {
                        use std::os::unix::fs::FileExt;
                        let mut out = String::new();
                        let Ok(rd) =
                            std::fs::read_dir(format!("{rootfs}/.ashmem"))
                        else {
                            return out;
                        };
                        let mut names: Vec<_> = rd.flatten().collect();
                        names.sort_by_key(|e| e.file_name());
                        let mut found = 0;
                        for e in names.iter() {
                            if found >= 4 {
                                break;
                            }
                            let Ok(f) = std::fs::File::open(e.path())
                            else {
                                continue;
                            };
                            let len =
                                f.metadata().map(|m| m.len()).unwrap_or(0);
                            if !(8192..=70000).contains(&len) {
                                continue;
                            }
                            let mut data = vec![0u8; 1200];
                            if f.read_exact_at(&mut data, 0).is_err() {
                                continue;
                            }
                            let i32at = |o: usize| -> i32 {
                                i32::from_le_bytes(
                                    data[o..o + 4].try_into().unwrap(),
                                )
                            };
                            let u32at = |o: usize| -> u32 {
                                u32::from_le_bytes(
                                    data[o..o + 4].try_into().unwrap(),
                                )
                            };
                            let u16at = |o: usize| -> u16 {
                                u16::from_le_bytes(
                                    data[o..o + 2].try_into().unwrap(),
                                )
                            };
                            let off = 8usize;
                            let mut slots = String::new();
                            for b in 0..3usize {
                                let bo = off + 72 + b * 64;
                                let cnt = u32at(bo);
                                if cnt == 0 {
                                    slots.push_str(" []");
                                } else if cnt <= 5 {
                                    slots.push_str(&format!(
                                        " [{}:{},{},{},{}]",
                                        cnt,
                                        u16at(bo + 4),
                                        u16at(bo + 6),
                                        u16at(bo + 8),
                                        u16at(bo + 10)
                                    ));
                                } else {
                                    slots.push_str(&format!(" [!{cnt}]"));
                                }
                            }
                            out.push_str(&format!(
                                " stk8[{} id={} tok={} h={} a={} q={} st={}{}]",
                                e.file_name().to_string_lossy(),
                                i32at(off + 40),
                                i32at(off + 44),
                                i32at(off),
                                i32at(off + 4),
                                i32at(off + 8),
                                i32at(off + 16),
                                slots
                            ));
                            found += 1;
                        }
                        out
                    })();
                    // Brightness census for the page: the
                    // nonzero count cannot tell a bright
                    // white wordmark from values like
                    // 0x00010802 that read as black to the
                    // eye (the 0.9.38/39 previews looked
                    // black while the census counted 3.6k
                    // 'lit' pixels).
                    let bright = {
                        let mut n = 0usize;
                        let mut mx = 0u8;
                        let mut a0 = 0usize;
                        for p in page.chunks_exact(4) {
                            let m = p.iter().copied().max().unwrap_or(0);
                            if m >= 0x80 {
                                n += 1;
                            }
                            mx = mx.max(m);
                            // Lit RGB with a zero alpha byte:
                            // the exact signature that made
                            // the shell preview render black
                            // (0.9.46 forces opacity there).
                            if p[3] == 0
                                && (p[0] >= 0x80
                                    || p[1] >= 0x80
                                    || p[2] >= 0x80)
                            {
                                a0 += 1;
                            }
                        }
                        format!(" bright={n} maxv={mx} a0={a0}")
                    };
                    Some(format!(
                        " shape={rows}|{cols} px={px} bb={x0},{y0}-{x1},{y1}{bright}{stacks}"
                    ))
                })()
                .unwrap_or_default()
            } else {
                String::new()
            };
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
            format!(
                "fb PAN yoffset={yoff} (page {}) by pid={pid} {fp}{shape}{ash}",
                yoff / FB_H
            )
        }
        _ => {
            // FBIO_WAITFORVSYNC and anything else in the
            // intercepted set: succeed silently.
            skip_syscall(pid, regs, pend, 0);
            "fb ioctl (accepted)".to_string()
        }
    }
}

/// What binder_deliver wrote into an arena buffer, kept
/// until the buffer is freed (0.9.99): a CRC32 of the file
/// image (data, zero padding, offsets) with fd-fixup words
/// zeroed -- fixups legitimately rewrite those words
/// before the guest reads the parcel.
struct ParcelPrint {
    crc: u32,
    total: u32,
    mask: Vec<u32>,
    head: Vec<u32>,
    /// Death-inventory telemetry (0.9.118, ported from
    /// 0.9.116): who sent this parcel and what it carried,
    /// captured at delivery so an arena that dies holding
    /// unread/unfreed parcels can name them. Read only by
    /// the death inventory dump in binder_on_proc_exit;
    /// delivery logic never consults these fields.
    from_pid: i32,
    code: u32,
    target_ptr: u32,
    txn_cookie: u32,
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
    /// Delivery fingerprints of live parcels (0.9.99):
    /// arena offset -> what binder_deliver wrote there.
    /// Re-verified when the batch handing the parcel to
    /// its reader is assembled (dump_mgr_read): a parcel
    /// rewritten in flight -- a stray fd fixup, a double
    /// allocation, a wild write -- shows up here as a
    /// fingerprint mismatch instead of surfacing in the
    /// guest as a crash on a pointer no stream carried.
    parcels: HashMap<u32, ParcelPrint>,
    /// BC_FREE_BUFFER outcome counters (0.9.99), reported
    /// when the arena dies: hit = recycled, nobase = the
    /// freeing thread had no registered base (the free was
    /// dropped), stale = offset was not in the used table.
    free_hit: u32,
    free_nobase: u32,
    free_stale: u32,
    /// BC_FREE_BUFFER delivery-record outcome counters
    /// (0.9.118, ported from 0.9.117), reported when the
    /// arena dies alongside the 0.9.99 set: free_parcel_hit
    /// = the free removed a live ParcelPrint (the delivery
    /// record), free_miss = the freeing thread had no
    /// registered base and the free was dropped -- the
    /// nobase path, counted under this name so a tenure
    /// whose frees silently miss can be told apart from
    /// one whose frees land; each miss is also logged as
    /// it happens.
    free_parcel_hit: u32,
    free_miss: u32,
    /// BC_FREE_BUFFER rescue hits (0.9.119): the freeing
    /// thread's own base missed (or it had none), but the
    /// pointer resolved against another registered base of
    /// the same arena and the free landed. Reported at
    /// arena death alongside the other free counters.
    free_rescued: u32,
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
    /// Copies up to `max` bytes of this thread's readable
    /// stream (own queue first, then the inbound stream
    /// for loopers) without draining -- the same order
    /// drain_for serves.
    fn peek_for(&self, pid: i32, max: usize) -> Vec<u8> {
        let mut out = Vec::new();
        if let Some(q) = self.queues.get(&pid) {
            let n = q.len().min(max);
            out.extend_from_slice(&q[..n]);
        }
        if out.len() < max && self.loopers.contains(&pid) {
            let n = self.inbound.len().min(max - out.len());
            out.extend_from_slice(&self.inbound[..n]);
        }
        out
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
    /// Transaction code of the call being waited on
    /// (0.9.125): part of the identity a serving thread
    /// claims this wait by when the fill hands it the
    /// transaction parcel (binder_claim_fills).
    code: u32,
}

/// One frame of a serving thread's transaction stack
/// (0.9.125). Reply = a claimed two-way wait this thread
/// owes an answer; Other = a transaction that owes none
/// (one-way, or a two-way parcel whose wait record could
/// not be claimed -- the miss is logged at fill time and
/// the orphan wait stays in the shared queue). The
/// Reply frame's second field is the claim sequence
/// number (0.9.128, BinderState::claim_seq): stamped at
/// claim time so the claim / reply-pop / big-reply
/// dumps can be joined on it. Telemetry only -- it is
/// written here and printed by those dumps, never read
/// by any pairing or delivery decision.
enum ServingFrame {
    Reply(ReplyWait, u64),
    Other,
}

/// One read fill's worth of frames on a serving stack
/// (0.9.130): every frame binder_claim_fills pushed for
/// a single fill, in claim (stream) order. See
/// ServingStack for why fills are kept apart.
struct ServingGroup {
    /// Fill sequence number (BinderState::fill_seq):
    /// one number per fill that claimed at least one
    /// frame, printed by the claim / reply-pop dumps so
    /// a delivered reply can be joined to its fill
    /// batch. Telemetry only.
    fill_id: u64,
    frames: Vec<ServingFrame>,
}

/// A serving thread's transaction stack (0.9.125): the
/// supervisor-side mirror of the kernel's per-thread
/// transaction stack. A two-way wait lives in the shared
/// per-arena queue only until a read fill hands the
/// transaction parcel to a serving thread; the claim
/// (binder_claim_fills) moves it here, and the thread's
/// later BC_REPLY answers a claimed wait -- never a
/// stranger picked off the shared queue.
///
/// Pairing discipline (0.9.130): groups are answered
/// newest-first (a fill that arrives while an older
/// call is still open is a deeper serving level --
/// the old stack order across fills), but frames
/// WITHIN one group are answered in claim order
/// (FIFO). A guest thread that read several
/// transactions in one fill serves them in buffer
/// order and sends its BC_REPLYs in that same order;
/// the 0.9.125 flat stack popped a batch LIFO and
/// swapped the batch's replies (s9-130-provider-data
/// line one: pinyin's getContentProvider was answered
/// with phone's PackageInfo, read as a ProviderInfo --
/// NPE, crash report, ignition).
struct ServingStack {
    /// Arena the serving thread belongs to.
    arena: String,
    groups: Vec<ServingGroup>,
}

impl ServingStack {
    /// Total frames across all groups (the depth the
    /// claim / reply-pop dumps print).
    fn depth(&self) -> usize {
        self.groups.iter().map(|g| g.frames.len()).sum()
    }
}

/// One large transaction parcel kept in an arena's
/// ignition evidence ring (0.9.131): the translated
/// bytes exactly as delivered, capped at 8KB (a longer
/// parcel is truncated in storage and the dump says
/// so), with the identity the big-txn dump line
/// carries -- (sender, code, slot) joins a stored
/// parcel to that line, which is the delivery's place
/// in the session log (the supervisor numbers no log
/// lines of its own).
struct BigTxnRec {
    code: u32,
    sender_pid: i32,
    full_size: usize,
    slot: u32,
    bytes: Vec<u8>,
}

/// Per-arena ignition evidence (0.9.131, telemetry
/// only): the last two large transactions delivered
/// into the arena and the last 24 short event tags
/// naming what the binder driver did to or for this
/// arena's process (deliveries, shield3/4 intercepts,
/// claims, pops, FAILED/DEAD_REPLY answers). Written
/// by the evidence_* helpers at the delivery /
/// intercept / claim / pop sites, read only by
/// binder_ignition_dump, and cleared when the arena
/// dies (binder_on_proc_exit). An arena is one guest
/// process in this driver, so the ring is the
/// process's evidence; the dump trigger names a pid
/// and resolves its arena through thread_arena.
/// Worst case per arena: 2 x 8KB of parcel bytes plus
/// 24 short strings -- about 19KB.
#[derive(Default)]
struct PidEvidence {
    big: VecDeque<BigTxnRec>,
    tags: VecDeque<String>,
}

/// One parcel a serving thread was handed in a read
/// fill (0.9.135, telemetry only): the guest VA and
/// size of the transaction parcel exactly as the
/// fill's BR_TRANSACTION descriptor named them, the
/// claim sequence the frame took (None for one-way
/// parcels and claim misses) and the fill it arrived
/// in. Written by binder_claim_fills beside the claim
/// push, read only by the reply-source collision
/// check in binder_handle_txn; never consulted by
/// any pairing, delivery or judgement decision.
struct ClaimParcelRec {
    seq: Option<u64>,
    fill_id: u64,
    va: u32,
    size: usize,
    code: u32,
    sender_pid: i32,
}

/// One large transaction or reply a thread itself
/// sent (0.9.135, telemetry only): the guest buffer
/// it was copied from, its size, code and the first
/// 64 bytes as copied. Written by binder_handle_txn
/// for every transaction of 256B or more (the house
/// big-parcel floor), replies included; read only by
/// the reply-source collision check; never consulted
/// by any decision.
struct SendSrcRec {
    daddr: u32,
    dsize: usize,
    code: u32,
    is_reply: bool,
    head: Vec<u8>,
}

/// Per-thread ring caps for the 0.9.135 collision
/// records (see ClaimParcelRec / SendSrcRec): a
/// serving thread's nested depth is single digits,
/// so a handful of entries covers every buffer the
/// aliasing hypothesis can name; the caps keep the
/// rings at a few KB per thread worst case.
const CLAIM_PARCEL_CAP: usize = 16;
const SEND_SRC_CAP: usize = 8;

/// 0.9.135: file one fill parcel in a reader's
/// collision ring (see ClaimParcelRec). Pure
/// bookkeeping; prints nothing.
fn record_claim_parcel(st: &mut BinderState, pid: i32, rec: ClaimParcelRec) {
    let ring = st.claim_parcels.entry(pid).or_default();
    ring.push_back(rec);
    while ring.len() > CLAIM_PARCEL_CAP {
        ring.pop_front();
    }
}

/// 0.9.135: file one of a thread's own sends in its
/// collision ring (see SendSrcRec). Pure bookkeeping;
/// prints nothing.
fn record_send_src(st: &mut BinderState, pid: i32, rec: SendSrcRec) {
    let ring = st.send_src.entry(pid).or_default();
    ring.push_back(rec);
    while ring.len() > SEND_SRC_CAP {
        ring.pop_front();
    }
}

/// 0.9.135 telemetry helper: byte verdict for two
/// guest ranges that overlap -- "match" when every
/// stored-head byte that falls inside the compared
/// range agrees with the copy in hand, "differ" on
/// the first disagreement, "na" when the stored head
/// does not reach the overlap.
fn overlap_verdict(head: &[u8], head_addr: u32, addr: u32, data: &[u8]) -> &'static str {
    let h_lo = head_addr as u64;
    let h_hi = h_lo + head.len() as u64;
    let d_lo = addr as u64;
    let d_hi = d_lo + data.len() as u64;
    let lo = h_lo.max(d_lo);
    let hi = h_hi.min(d_hi);
    if lo >= hi {
        return "na";
    }
    let hs = (lo - h_lo) as usize;
    let ds = (lo - d_lo) as usize;
    let n = (hi - lo) as usize;
    if head[hs..hs + n] == data[ds..ds + n] {
        "match"
    } else {
        "differ"
    }
}

/// 0.9.135 telemetry helper: byte verdict of a copy
/// against stored parcel bytes at a data offset --
/// "match" / "differ" over the comparable span, or
/// "na" when the offset starts past the stored bytes.
fn span_verdict(stored: &[u8], off: usize, data: &[u8]) -> &'static str {
    if off >= stored.len() {
        return "na";
    }
    let n = (stored.len() - off).min(data.len());
    if stored[off..off + n] == data[..n] {
        "match"
    } else {
        "differ"
    }
}

/// One supervisor delivery write into a guest arena,
/// kept for the 0.9.132 write-overlap audit (telemetry
/// only): the guest virtual-address interval and total
/// length of the parcel image binder_deliver laid
/// down, plus its first 64 bytes exactly as written.
/// The audit (write_audit_check) compares a poisoned
/// reply's source range against these records to
/// separate "the guest assembled garbage from its own
/// memory" from "an earlier supervisor delivery write
/// landed on the very bytes later read back as poison"
/// (s9-132-spec section 2.3). Records are written at
/// the delivery site and read only by the audit; they
/// feed no decision.
/// 0.9.133 coordinate fix (s9-132-verify Q3): the
/// record used to keep the arena-FILE offset, but a
/// poisoned reply's source is a heap Parcel buffer in
/// the replier's own address space -- the two domains
/// never intersect by construction, so every check
/// died at the base conversion (verdict=no-base 8/8)
/// without comparing a single byte. The record now
/// keeps the guest VA interval the delivery actually
/// landed at (the target's registered mmap base plus
/// the file offset, exactly the address the delivered
/// BR_TRANSACTION/BR_REPLY names), and the check
/// compares VA against VA.
struct WriteAuditRec {
    arena: String,
    va: u64,
    len: u32,
    head: Vec<u8>,
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
    /// 0.9.125: per-serving-thread transaction stacks
    /// (see ServingStack): where a reply wait lives once
    /// the parcel has been handed to a serving thread,
    /// and where a BC_REPLY finds the wait it answers.
    serving: HashMap<i32, ServingStack>,
    /// node index -> (watcher arena, cookie) death watches
    watchers: HashMap<usize, Vec<(String, u32)>>,
    thread_arena: HashMap<i32, String>,
    noted: HashSet<String>,
    /// (node, receiver arena) pairs already sent a
    /// BR_INCREFS(/BR_ACQUIRE) notice to the node's owner:
    /// the real driver notifies once per new reference
    /// holder, not once per parcel (S5c). The value is
    /// the weak flag of the crossing that actually sent
    /// the notice, kept so the death settlement in
    /// binder_on_proc_exit can mirror the pair exactly
    /// (BR_DECREFS always, BR_RELEASE only where an
    /// ACQUIRE went out); the dedup key is the pair
    /// alone, exactly as before (0.9.118).
    ref_notified: HashMap<(usize, String), bool>,
    /// Count of reference notices actually queued to an
    /// owner (0.9.100's suppression experiment counted the
    /// suppressed calls here; 0.9.101 restored the notices
    /// and counts the queued ones). Reported at arena
    /// death alongside the free counters.
    notify_queued: u64,
    /// 0.9.103: cumulative shield drops (see
    /// shield_ref_pairs). Reported at arena death.
    shield_drops: u64,
    /// 0.9.120: cumulative shield-cookie suspects
    /// reported by the workers' shield_live_pairs
    /// probe (delivered REF pairs whose referent's
    /// strong count already read zero, or whose
    /// memory was unreadable). Global like
    /// shield_drops; reported at arena death
    /// alongside the free counters.
    shield_cookie_suspects: u64,
    /// 0.9.125: cumulative BC_REPLYs dropped because the
    /// replier's serving stack held no claimed wait for
    /// them (identity-bound pairing: an unmatched reply
    /// is dropped, never paired with a stranger from the
    /// shared queue). Global like shield_drops; reported
    /// at arena death alongside the free counters.
    reply_unmatched: u64,
    /// 0.9.129: cumulative replies dropped by shield4 --
    /// a first word in guest-pointer territory where a
    /// reply's exception header belongs (the replier's
    /// own memory at (daddr, dsize) already held a
    /// native memory slice when the supervisor copied
    /// it; s9-128-substitution (c)). The waiter is
    /// answered FAILED_REPLY instead, mirroring
    /// shield3. Global like shield_drops; reported at
    /// arena death alongside the free counters.
    shield4_drops: u64,
    /// 0.9.132: shield4 drops bucketed by the rejected
    /// first word's shape (cookie domain / libc domain /
    /// stack domain / fragment-other), so the next
    /// field run's intercept account can be reconciled
    /// shape by shape. Counters only; reported on the
    /// arena-death free-counters line beside
    /// shield4_drops.
    shield4_cookie: u64,
    shield4_libc: u64,
    shield4_stack: u64,
    shield4_other: u64,
    /// 0.9.132: the write-overlap audit's table of the
    /// supervisor's own delivery writes (see
    /// WriteAuditRec). Global FIFO, capped at
    /// WRITE_AUDIT_CAP records; an arena's records are
    /// dropped when the arena dies (binder_on_proc_exit),
    /// beside its evidence ring. Telemetry only.
    write_audit: VecDeque<WriteAuditRec>,
    /// 0.9.133: judgement-point second-read counters
    /// (telemetry only). The pre-0.9.133 re-read hook
    /// covered only replies of 256B+, so the 8B poison
    /// family was never re-read at all and its read-
    /// window race question stayed open (s9-132-verify
    /// Q3); the hook at the shield4 judgement point now
    /// re-reads the first min(size, 64B) of every judged
    /// reply and counts the comparisons here, printing
    /// a line only when one differs. The second read is
    /// never consulted by the judgement or the delivery.
    /// Global like shield4_drops; reported on the
    /// arena-death free-counters line.
    second_reads: u64,
    second_read_differs: u64,
    /// 0.9.134: fd fixup resolution account (see
    /// resolve_fd_fixups_core): failures routed to the
    /// delivery-failure path instead of being written
    /// into the parcel as -1 / a foreign number, low-
    /// slot results dupped up out of the stdio range,
    /// and write-back verifications passed. The work is
    /// tracer-side; the counts arrive by MSG_ONEWAY_FD_
    /// FAIL / MSG_ONEWAY_FD_STATS. Global like
    /// shield4_drops; reported on the arena-death
    /// free-counters line.
    fd_fixup_failed: u64,
    fd_fixup_dupped: u64,
    fd_fixup_verified: u64,
    /// 0.9.137: settle-point retries of the injected
    /// open and the fixups they saved (see
    /// resolve_fd_fixups_core). Same account and
    /// arrival path as the three counters above.
    fd_fixup_retried: u64,
    fd_fixup_retry_saved: u64,
    /// 0.9.140: cumulative code-2 transactions whose
    /// interface token the trigger-A heuristic could
    /// not extract at all (see binder_send_txn) --
    /// the trigger's blind-spot account. Global like
    /// shield_drops; reported at arena death beside
    /// the free counters.
    crash_token_miss: u64,
    /// 0.9.141 (s9-141-desk P1): global issuance
    /// double-read account (see MSG_ONEWAY_ISSUANCE_
    /// STATS): snapshots of BC_REPLY buffers taken at
    /// the ioctl entry stop, and how many of them read
    /// back different at the exit-side re-read -- a
    /// nonzero differs count is a new poison sub-form
    /// (the buffer changed inside the ioctl window).
    /// Reported at arena death beside the free
    /// counters. Telemetry only.
    issuance_reads: u64,
    issuance_differs: u64,
    /// 0.9.141 (s9-141-desk P2): poisoned-reply first
    /// words classified against the reply's own data
    /// address (see poison_word0_class): [self-8,
    /// self, self-page, heap-other, libc, stack,
    /// other]. Global like shield4_drops; reported
    /// at arena death on its own settlement line.
    poison_word0: [u64; 7],
    /// 0.9.141 (s9-141-desk P3): the assembly-window
    /// profile attached to the write_read request
    /// currently being served (stops, futex, alloc,
    /// parks, sends, maxdepth); printed on the
    /// reply-pop descriptor line. Set by the server
    /// arm around binder_write_read, which is never
    /// re-entered. Telemetry only.
    cur_win: Option<(u32, u32, u32, u32, u32, u32)>,
    /// 0.9.135: per-thread rings for the reply-source
    /// collision check (see ClaimParcelRec /
    /// SendSrcRec) and its counters. Telemetry only,
    /// like the evidence rings: a thread's rings die
    /// with it in binder_thread_exit, and the counters
    /// are global like shield4_drops, reported on the
    /// arena-death free-counters line.
    claim_parcels: HashMap<i32, VecDeque<ClaimParcelRec>>,
    send_src: HashMap<i32, VecDeque<SendSrcRec>>,
    reply_collide_checks: u64,
    reply_collide_hits: u64,
    /// 0.9.135: the write-stream batch skeleton of the
    /// binder_process_stream call currently running
    /// (command names and total lengths in stream
    /// order) and the ordinal of the BC_REPLY inside
    /// it that is being handled; read by the reply-pop
    /// descriptor dump in binder_handle_txn.
    /// process_stream is never re-entered, so plain
    /// fields are safe; both sit empty/zero outside a
    /// stream walk. Telemetry only.
    cur_batch_skel: String,
    cur_batch_reply_ord: usize,
    /// 0.9.128: global claim sequence counter. Every
    /// successful claim in binder_claim_fills takes the
    /// next number and stamps it on the ServingFrame it
    /// pushes; the claim, reply-pop and big-reply dumps
    /// print it so one delivered reply traces back to
    /// the exact claim that sourced its frame
    /// (s9-127-big-reply Q5: separating fill-claim
    /// aliasing, wrong-frame pops and replier-side
    /// buffer aliasing). Written here and on frames,
    /// printed by dumps, never read by any decision.
    claim_seq: u64,
    /// 0.9.130: global fill sequence counter. Each
    /// binder_claim_fills call that pushes at least one
    /// frame takes the next number as its ServingGroup's
    /// fill_id; the claim and reply-pop dumps print it
    /// so a batch's claims can be told apart from a
    /// nested fill's. Telemetry only, like claim_seq.
    fill_seq: u64,
    /// 0.9.131: per-arena ignition evidence rings (see
    /// PidEvidence). Telemetry only -- written by the
    /// evidence_* record helpers, read only by
    /// binder_ignition_dump, never consulted by any
    /// pairing, delivery, shield or settlement
    /// decision.
    evidence: HashMap<String, PidEvidence>,
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
    /// 0.9.134: guest VA of the owning parcel's data in
    /// the receiver (base + allocation offset, recorded
    /// by binder_deliver). The resolution site finds the
    /// BR command carrying this parcel in the batch it
    /// is settling by matching this VA against the
    /// commands' data pointers -- no base arithmetic
    /// tracer-side, and the match survives the ref-pair
    /// filters, which only ever drop INCREFS/ACQUIRE
    /// commands. Used when a resolution failure converts
    /// the delivery to FAILED_REPLY (see
    /// fd_convert_in_stream); never consulted on the
    /// success path.
    data_va: u32,
}

impl BinderState {
    fn note(&mut self, what: &str) {
        if self.noted.insert(what.to_string()) {
            bsup!("binder: {what} (first occurrence)");
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
        let id = self.nodes.len() - 1;
        bsup!(
            "binder: node#{} registered owner={} ptr=0x{:x} cookie=0x{:x}",
            id, owner, ptr, cookie
        );
        id
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

// ---- coordinator IPC (multi-process split, spec S1b) ----
//
// BinderState lives in a child process running this same
// binary's coordinator mode (coordinator_main). The
// tracer keeps no binder state: driver decisions are
// requested over a socketpair and return as data -- a
// desc string, the decision's log lines (captured with
// bsup!, replayed by the tracer at the point the call
// used to make them), and the S1a action list. The wire
// format is hand-rolled: u32 little-endian frame length,
// one kind byte, then little-endian scalars and
// length-prefixed byte/UTF-8 strings in field order.
//
// The one flow that runs backwards is guest memory: a
// decision mid-flight can need parcel bytes only the
// tracer can read (it holds the ptrace stops), so the
// coordinator issues MSG_REV_READ sub-requests on the
// same socket while a request is in flight, and the
// tracer's rpc loop services them before reading the
// reply. One request at a time, strictly ordered: the
// split cannot reorder anything the inline code ordered.

/// The fd_cache key: (arena path, sender pid, sender fd).
type CacheKey = (String, i32, i32);

const MSG_REQ_WRITE_READ: u8 = 1;
const MSG_REQ_COMPLETE_PARKED: u8 = 2;
const MSG_REQ_THREAD_EXIT: u8 = 3;
const MSG_REQ_SET_CONTEXT_MGR: u8 = 4;
const MSG_REQ_OPEN_BINDER: u8 = 5;
const MSG_REQ_OPEN_ASHMEM: u8 = 6;
const MSG_REQ_ASHMEM_GET: u8 = 7;
const MSG_ONEWAY_PARK: u8 = 16;
const MSG_ONEWAY_FD_CACHE_PUT: u8 = 17;
const MSG_ONEWAY_PARK_REMOVE: u8 = 18;
const MSG_ONEWAY_THREAD_ARENA: u8 = 19;
const MSG_ONEWAY_ARENA_REGISTER: u8 = 20;
const MSG_ONEWAY_THREAD_EXIT_IOCTL: u8 = 21;
const MSG_ONEWAY_ASHMEM_SET_NAME: u8 = 22;
const MSG_ONEWAY_ASHMEM_SET_SIZE: u8 = 23;
const MSG_ONEWAY_ASHMEM_SET_PROT: u8 = 24;
// S2 (sharding): routing, credential book and handoff.
const MSG_REQ_VCRED: u8 = 8;
// 0.9.131: the tracer asks the coordinator to print
// one pid's ignition evidence ring (trigger B: a
// FATAL whose pc lands in the dvmAbort range) and
// replays the captured lines beside the FATAL line.
// A request (not a oneway) on purpose: oneway-path
// cap_log lines never reach the log (the next
// request's cap_clear discards them -- the
// shield-cookie suspect line is the field proof),
// while a reply carries its logs in order.
const MSG_REQ_IGNITION_DUMP: u8 = 9;
// 0.9.140: the tracer asks the coordinator for the
// wedge chain dump of one system_server arena (see
// binder_wedge_chain): serving stacks, outstanding
// waits, park kinds and the provisional verdict. A
// request/reply for the same reason as 9 -- the dump
// rides the snapshot instant and the oneway log
// channel provably loses lines there.
const MSG_REQ_WEDGE_CHAIN: u8 = 10;
const MSG_ONEWAY_HANDOFF: u8 = 25;
const MSG_ONEWAY_REGISTER_PID: u8 = 26;
const MSG_ONEWAY_UNREGISTER_PID: u8 = 27;
const MSG_ONEWAY_WAKE_ROUTE: u8 = 28;
const MSG_ONEWAY_VCRED_PUBLISH: u8 = 29;
const MSG_ONEWAY_ADOPT_ACK: u8 = 30;
const MSG_HELLO: u8 = 31;
// Freeze forensics (0.9.81): W0 relays the shell's
// SIGUSR2 stack-dump request; the coordinator
// broadcasts it to the workers as a push.
const MSG_ONEWAY_DUMP_REQ: u8 = 32;
// 0.9.120: a worker's shield_live_pairs probe found a
// delivered REF pair whose referent's strong count is
// already zero (or unreadable); the coordinator
// resolves the pair's node, counts it and logs it.
// Telemetry only -- the pair is delivered regardless.
const MSG_ONEWAY_SHIELD_COOKIE_SUSPECT: u8 = 33;
// 0.9.134: a fixup resolution failed tracer-side; the
// coordinator counts it and, per the disposition the
// tracer reports, either does nothing (converted in
// the tracer's own batch), fails the dropped
// transaction's waiting sender, or converts the
// delivery in its own queues. See fd_fail_convert_*.
const MSG_ONEWAY_FD_FAIL: u8 = 34;
// 0.9.134: per-resolution fixup statistics deltas
// (low-slot dups performed, verifications passed),
// counted coordinator-side for the arena-death
// free-counters line.
const MSG_ONEWAY_FD_STATS: u8 = 35;
// 0.9.141 (s9-141-desk P1): per-worker deltas of the
// reply-issuance double read (snapshots taken at the
// ioctl entry stop, buffers found differing at the
// exit-side re-read), counted coordinator-side for
// the arena-death settlement lines.
const MSG_ONEWAY_ISSUANCE_STATS: u8 = 36;
const MSG_PUSH_WAKE: u8 = 40;
const MSG_PUSH_ADOPT: u8 = 41;
const MSG_PUSH_ADOPT_ACK: u8 = 42;
const MSG_PUSH_DUMP_STACKS: u8 = 43;
// 0.9.141 (s9-141-desk S6): after a wedge chain dump
// that found a frozen claimed wait, the coordinator
// broadcasts the servicer pids so the worker owning
// each prints its tracer-side face line.
const MSG_PUSH_SERVICER_FACE: u8 = 44;
const MSG_RESP_VCRED: u8 = 108;
const MSG_RESP_IGNITION_DUMP: u8 = 109;
const MSG_RESP_WEDGE_CHAIN: u8 = 110;
const MSG_RESP_ACTIONS: u8 = 101;
const MSG_RESP_COMPLETE: u8 = 102;
const MSG_RESP_THREAD_EXIT: u8 = 103;
const MSG_RESP_CTX_MGR: u8 = 104;
const MSG_RESP_OPEN_BINDER: u8 = 105;
const MSG_RESP_OPEN_ASHMEM: u8 = 106;
const MSG_RESP_ASHMEM_GET: u8 = 107;
const MSG_REV_READ: u8 = 120;
const MSG_REV_READ_RESP: u8 = 121;

/// Decision-side log capture. In coordinator mode the
/// binder family must not emit: its lines belong in the
/// reply, in order, for the tracer to replay. cap_log is
/// only ever called on the coordinator side of the split
/// (via bsup!); in the tracer the buffer stays empty.
static CAP_LOG: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());

fn cap_log(tag: &str, msg: &str) {
    if let Ok(mut g) = CAP_LOG.lock() {
        g.push((tag.to_string(), msg.to_string()));
    }
}

fn cap_clear() {
    if let Ok(mut g) = CAP_LOG.lock() {
        g.clear();
    }
}

fn cap_take() -> Vec<(String, String)> {
    match CAP_LOG.lock() {
        Ok(mut g) => std::mem::take(&mut *g),
        Err(_) => Vec::new(),
    }
}

/// Replay the decision log lines a coordinator reply
/// carried, at the point the inline code emitted them.
fn replay_logs(logs: Vec<(String, String)>) {
    for (tag, msg) in &logs {
        emit(tag, msg);
    }
}

/// One ashmem region's record, as the tracer consumes it
/// (the coordinator's own copy stays an AshmemRec).
struct AshmemInfo {
    size: u64,
    name: String,
    prot: u64,
}

fn default_ashmem_rec() -> AshmemRec {
    AshmemRec { size: 0, name: String::new(), prot: 7 }
}

struct Enc(Vec<u8>);

impl Enc {
    fn new() -> Self {
        Enc(Vec::new())
    }
    fn u8(&mut self, v: u8) {
        self.0.push(v);
    }
    fn bool(&mut self, v: bool) {
        self.u8(if v { 1 } else { 0 });
    }
    fn u32(&mut self, v: u32) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn i32(&mut self, v: i32) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn i64(&mut self, v: i64) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn usize(&mut self, v: usize) {
        self.u64(v as u64);
    }
    fn bytes(&mut self, b: &[u8]) {
        self.u32(b.len() as u32);
        self.0.extend_from_slice(b);
    }
    fn opt_bytes(&mut self, b: Option<&[u8]>) {
        self.bool(b.is_some());
        if let Some(b) = b {
            self.bytes(b);
        }
    }
    fn string(&mut self, s: &str) {
        self.bytes(s.as_bytes());
    }
    fn park(&mut self, p: &ParkedIoctl) {
        self.u32(p.bwr);
        self.u32(p.read_buf);
        self.u32(p.read_size);
        self.u32(p.write_consumed);
    }
    fn fixup(&mut self, f: &FdFixup) {
        self.u64(f.file_off);
        self.i32(f.sender_pid);
        self.i32(f.sender_fd);
        self.u32(f.data_va);
    }
    fn fixups(&mut self, fs: &[FdFixup]) {
        self.u32(fs.len() as u32);
        for f in fs {
            self.fixup(f);
        }
    }
    fn cache(&mut self, es: &[(CacheKey, i32)]) {
        self.u32(es.len() as u32);
        for ((arena, spid, sfd), fd) in es {
            self.string(arena);
            self.i32(*spid);
            self.i32(*sfd);
            self.i32(*fd);
        }
    }
    fn logs(&mut self, ls: &[(String, String)]) {
        self.u32(ls.len() as u32);
        for (t, m) in ls {
            self.string(t);
            self.string(m);
        }
    }
    fn actions(&mut self, acts: &[BAction]) {
        self.u32(acts.len() as u32);
        for a in acts {
            match a {
                BAction::WriteMem { addr, bytes } => {
                    self.u8(0);
                    self.u64(*addr);
                    self.bytes(bytes);
                }
                BAction::SkipSyscall(v) => {
                    self.u8(1);
                    self.i64(*v);
                }
                BAction::Park { pid, park } => {
                    self.u8(2);
                    self.i32(*pid);
                    self.park(park);
                }
                BAction::MarkBinderParked => self.u8(3),
                BAction::Wake(pid) => {
                    self.u8(4);
                    self.i32(*pid);
                }
                BAction::ResolveFdFixupsInline { arena, fixups, cache } => {
                    self.u8(5);
                    self.string(arena);
                    self.fixups(fixups);
                    self.cache(cache);
                }
            }
        }
    }
}

struct Dec<'a> {
    b: &'a [u8],
    off: usize,
}

impl<'a> Dec<'a> {
    fn new(b: &'a [u8]) -> Self {
        Dec { b, off: 0 }
    }
    // Defensive reads: a short buffer yields zeroes
    // past its end instead of panicking. The protocol
    // is internal and same-version on both ends; a
    // desync is caught at the rpc kind check.
    fn take(&mut self, n: usize) -> &'a [u8] {
        let avail = self.b.len().saturating_sub(self.off);
        let n = n.min(avail);
        let s = &self.b[self.off..self.off + n];
        self.off += n;
        s
    }
    fn raw(&mut self, n: usize) -> [u8; 8] {
        let mut out = [0u8; 8];
        let s = self.take(n);
        out[..s.len()].copy_from_slice(s);
        out
    }
    fn u8(&mut self) -> u8 {
        self.take(1).first().copied().unwrap_or(0)
    }
    fn bool(&mut self) -> bool {
        self.u8() != 0
    }
    fn u32(&mut self) -> u32 {
        let r = self.raw(4);
        u32::from_le_bytes([r[0], r[1], r[2], r[3]])
    }
    fn i32(&mut self) -> i32 {
        self.u32() as i32
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.raw(8))
    }
    fn i64(&mut self) -> i64 {
        self.u64() as i64
    }
    fn usize(&mut self) -> usize {
        self.u64() as usize
    }
    fn bytes(&mut self) -> Vec<u8> {
        let n = self.u32() as usize;
        self.take(n).to_vec()
    }
    fn opt_bytes(&mut self) -> Option<Vec<u8>> {
        if self.bool() {
            Some(self.bytes())
        } else {
            None
        }
    }
    fn string(&mut self) -> String {
        String::from_utf8_lossy(&self.bytes()).into_owned()
    }
    fn park(&mut self) -> ParkedIoctl {
        ParkedIoctl {
            bwr: self.u32(),
            read_buf: self.u32(),
            read_size: self.u32(),
            write_consumed: self.u32(),
        }
    }
    fn fixup(&mut self) -> FdFixup {
        FdFixup {
            file_off: self.u64(),
            sender_pid: self.i32(),
            sender_fd: self.i32(),
            data_va: self.u32(),
        }
    }
    fn fixups(&mut self) -> Vec<FdFixup> {
        let n = self.u32();
        (0..n).map(|_| self.fixup()).collect()
    }
    fn cache(&mut self) -> Vec<(CacheKey, i32)> {
        let n = self.u32();
        (0..n)
            .map(|_| {
                let arena = self.string();
                let spid = self.i32();
                let sfd = self.i32();
                let fd = self.i32();
                ((arena, spid, sfd), fd)
            })
            .collect()
    }
    fn logs(&mut self) -> Vec<(String, String)> {
        let n = self.u32();
        (0..n).map(|_| (self.string(), self.string())).collect()
    }
    fn actions(&mut self) -> Vec<BAction> {
        let n = self.u32();
        let mut out = Vec::new();
        for _ in 0..n {
            match self.u8() {
                0 => {
                    let addr = self.u64();
                    let bytes = self.bytes();
                    out.push(BAction::WriteMem { addr, bytes });
                }
                1 => out.push(BAction::SkipSyscall(self.i64())),
                2 => {
                    let pid = self.i32();
                    let park = self.park();
                    out.push(BAction::Park { pid, park });
                }
                3 => out.push(BAction::MarkBinderParked),
                4 => out.push(BAction::Wake(self.i32())),
                _ => {
                    let arena = self.string();
                    let fixups = self.fixups();
                    let cache = self.cache();
                    out.push(BAction::ResolveFdFixupsInline { arena, fixups, cache });
                }
            }
        }
        out
    }
}

fn write_msg(s: &mut UnixStream, kind: u8, payload: &[u8]) -> bool {
    let len = (payload.len() + 1) as u32;
    let mut hdr = [0u8; 5];
    hdr[..4].copy_from_slice(&len.to_le_bytes());
    hdr[4] = kind;
    s.write_all(&hdr).is_ok() && s.write_all(payload).is_ok()
}

/// What a parked completion needs when it goes ahead:
/// the coordinator-side half of the parked-completion
/// dance (the old complete_parked's state work). The
/// tracer performs the memory writes, the fd fixups
/// and the continue itself.
enum ParkedOutcome {
    Nothing,
    Complete {
        park: ParkedIoctl,
        bytes: Vec<u8>,
        fixups: Option<(String, Vec<FdFixup>, Vec<(CacheKey, i32)>)>,
    },
}

/// Cache entries a fixup resolution learned: present
/// in the resolution's map afterwards, but absent from
/// the seed it started with or carrying a different
/// value than the seed's (0.9.134: a seeded entry whose
/// fd sat in the stdio slots is dupped upward in
/// place). Those are exactly the inserts the inline
/// resolver used to make in the driver's fd_cache,
/// owed back to the coordinator before any later
/// decision reads the cache again.
fn learned_entries(
    map: &std::collections::HashMap<CacheKey, i32>,
    seed: &std::collections::HashMap<CacheKey, i32>,
) -> Vec<(CacheKey, i32)> {
    map.iter()
        .filter(|(k, v)| seed.get(*k) != Some(*v))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}

/// A frame the coordinator pushes to a tracer outside
/// any request/response pair (S2): a wake for a parked
/// pid this tracer owns, an adopted tracee to attach,
/// the verdict on a handoff this tracer offered, or a
/// stack-dump request for whichever tracer holds a
/// system_server candidate.
// S2 also moves guest pid -> worker routing and the
// global credential book into the coordinator; the
// pushes are how its decisions reach other tracers.
enum Push {
    Wake(i32),
    Adopt {
        pid: i32,
        vcwd: String,
        compat: bool,
        sigmask: u32,
        creds: (u32, u32),
        // True when the handoff came from the
        // root-service rule (a guest-root child in
        // W0's shard map): the adoptee becomes the
        // worker's shard root. Kin re-shards carry
        // false.
        root: bool,
    },
    AdoptAck {
        pid: i32,
        ok: bool,
    },
    /// Freeze forensics (0.9.81): broadcast to every
    /// worker; only the one holding a system_server
    /// candidate acts (SIGQUIT, see tracer_loop's
    /// candidate bookkeeping), the rest drop it.
    DumpStacks,
    /// 0.9.141 (s9-141-desk S6): broadcast after a
    /// wedge chain dump; the worker owning one of
    /// `pids` prints that servicer's tracer-side face
    /// line (arena names the system_server arena the
    /// dump was taken for).
    ServicerFace {
        arena: String,
        pids: Vec<i32>,
    },
}

/// The tracer's end of the coordinator channel. Every
/// failure here is fatal on purpose: the spec's ruling
/// is a dead coordinator fails the whole run, exactly
/// like the old supervisor dying did, so the run stops
/// loudly instead of driving guests with no driver.
/// Since S2 the channel is a connection to a listening
/// socket shared with the other workers, so incoming
/// frames are demultiplexed: replies complete the rpc
/// that asked for them, reverse reads are serviced in
/// place, and pushes queue in `inbox` for the tracer's
/// event loop. The stream stays blocking; `pump` only
/// reads after poll says data is waiting, so a read
/// never waits for more than what has already arrived.
struct CoordClient {
    s: UnixStream,
    inbuf: Vec<u8>,
    queue: std::collections::VecDeque<(u8, Vec<u8>)>,
    inbox: std::collections::VecDeque<Push>,
    eof: bool,
}

impl CoordClient {
    fn send(&mut self, kind: u8, payload: &[u8]) {
        if !write_msg(&mut self.s, kind, payload) {
            sup!("coordinator write failed; supervisor exiting");
            std::process::exit(1);
        }
    }

    /// Connect to the coordinator's listening socket
    /// (retrying briefly: the listener is created by a
    /// freshly forked child and may not be bound yet)
    /// and introduce this tracer with a HELLO frame.
    fn connect(path: &str, wid: u8, shard: &str) -> CoordClient {
        let mut last_err = String::new();
        for _ in 0..200 {
            match UnixStream::connect(path) {
                Ok(s) => {
                    let mut c = CoordClient {
                        s,
                        inbuf: Vec::new(),
                        queue: std::collections::VecDeque::new(),
                        inbox: std::collections::VecDeque::new(),
                        eof: false,
                    };
                    let mut e = Enc::new();
                    e.u8(wid);
                    e.string(shard);
                    c.send(MSG_HELLO, &e.0);
                    return c;
                }
                Err(e) => {
                    last_err = e.to_string();
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
            }
        }
        sup!("coordinator connect failed ({path}): {last_err}; supervisor exiting");
        std::process::exit(1);
    }

    fn poll_fd(&self) -> i32 {
        use std::os::unix::io::AsRawFd;
        self.s.as_raw_fd()
    }

    /// Read whatever the coordinator has sent (poll has
    /// said it is there) and demultiplex the frames:
    /// pushes go to the inbox; anything else queues for
    /// rpc. Returns false on EOF / hard error.
    fn fill(&mut self) -> bool {
        if self.eof {
            return false;
        }
        let mut buf = [0u8; 65536];
        match self.s.read(&mut buf) {
            Ok(0) => {
                self.eof = true;
                false
            }
            Ok(n) => {
                self.inbuf.extend_from_slice(&buf[..n]);
                true
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => true,
            Err(_) => {
                self.eof = true;
                false
            }
        }
    }

    /// Move every complete frame out of the input
    /// buffer: pushes are decoded into the inbox, the
    /// rest queue in arrival order for rpc.
    fn extract(&mut self) {
        loop {
            if self.inbuf.len() < 4 {
                return;
            }
            let len = u32::from_le_bytes(self.inbuf[..4].try_into().unwrap()) as usize;
            if len == 0 || len > (64 << 20) {
                self.eof = true;
                return;
            }
            if self.inbuf.len() < 4 + len {
                return;
            }
            let frame: Vec<u8> = self.inbuf.drain(..4 + len).collect();
            let kind = frame[4];
            let payload = frame[5..].to_vec();
            match kind {
                MSG_PUSH_WAKE => {
                    let mut d = Dec::new(&payload);
                    self.inbox.push_back(Push::Wake(d.i32()));
                }
                MSG_PUSH_ADOPT => {
                    let mut d = Dec::new(&payload);
                    let pid = d.i32();
                    let vcwd = d.string();
                    let compat = d.bool();
                    let sigmask = d.u32();
                    let uid = d.u32();
                    let gid = d.u32();
                    let root = d.bool();
                    self.inbox.push_back(Push::Adopt {
                        pid,
                        vcwd,
                        compat,
                        sigmask,
                        creds: (uid, gid),
                        root,
                    });
                }
                MSG_PUSH_ADOPT_ACK => {
                    let mut d = Dec::new(&payload);
                    let pid = d.i32();
                    let ok = d.bool();
                    self.inbox.push_back(Push::AdoptAck { pid, ok });
                }
                MSG_PUSH_DUMP_STACKS => {
                    self.inbox.push_back(Push::DumpStacks);
                }
                MSG_PUSH_SERVICER_FACE => {
                    let mut d = Dec::new(&payload);
                    let arena = d.string();
                    let n = d.u32();
                    let mut pids = Vec::new();
                    for _ in 0..n {
                        pids.push(d.i32());
                    }
                    self.inbox.push_back(Push::ServicerFace { arena, pids });
                }
                _ => self.queue.push_back((kind, payload)),
            }
        }
    }

    /// Non-blocking harvest for the event loop: read
    /// only when poll says the socket is readable.
    fn pump(&mut self) {
        let mut pfd = libc::pollfd {
            fd: self.poll_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        let n = unsafe { libc::poll(&mut pfd, 1, 0) };
        if n > 0 && pfd.revents != 0 {
            self.fill();
            self.extract();
        }
    }

    /// Block until at least one more frame is queued
    /// (used by rpc). EOF here is the fatal ruling.
    fn fill_blocking(&mut self) {
        loop {
            if !self.queue.is_empty() || self.eof {
                return;
            }
            let mut pfd = libc::pollfd {
                fd: self.poll_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            let n = unsafe { libc::poll(&mut pfd, 1, -1) };
            if n < 0 && errno() == libc::EINTR {
                continue;
            }
            if n > 0 && pfd.revents != 0 {
                if !self.fill() {
                    return;
                }
                self.extract();
            }
        }
    }

    /// Fetch and remove the ack for one handoff, if the
    /// coordinator has pushed it (handoff handshake).
    fn take_adopt_ack(&mut self, pid: i32) -> Option<bool> {
        let pos = self.inbox.iter().position(|p| matches!(p, Push::AdoptAck { pid: q, .. } if *q == pid))?;
        match self.inbox.remove(pos) {
            Some(Push::AdoptAck { ok, .. }) => Some(ok),
            _ => None,
        }
    }

    /// Send one request and read its reply, servicing
    /// reverse guest-memory reads on the way: while the
    /// reply is outstanding the coordinator may ask for
    /// parcel bytes (MSG_REV_READ), which only the
    /// tracer can fetch, and the request resumes once
    /// the read is answered. Pushes arriving mid-rpc go
    /// to the inbox, never to this reply.
    fn rpc(&mut self, kind: u8, payload: &[u8], expect: u8) -> Vec<u8> {
        self.send(kind, payload);
        loop {
            if let Some((k, p)) = self.queue.pop_front() {
                if k == MSG_REV_READ {
                    let mut d = Dec::new(&p);
                    let (rpid, addr, len) = (d.i32(), d.u64(), d.usize());
                    let data = read_mem_vec(rpid, addr, len);
                    let mut e = Enc::new();
                    e.opt_bytes(data.as_deref());
                    self.send(MSG_REV_READ_RESP, &e.0);
                    continue;
                }
                if k == expect {
                    return p;
                }
                sup!("coordinator protocol desync (kind {k}, expected {expect}); supervisor exiting");
                std::process::exit(1);
            }
            self.fill_blocking();
            if self.queue.is_empty() {
                sup!("coordinator connection lost; supervisor exiting");
                std::process::exit(1);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn write_read(
        &mut self,
        pid: i32,
        compat: bool,
        veuid: u32,
        arena: &str,
        bwr_addr: u64,
        bwr: Option<Vec<u8>>,
        stream: Option<Vec<u8>>,
        win: (u32, u32, u32, u32, u32, u32),
    ) -> (String, Vec<(String, String)>, Vec<BAction>) {
        let mut e = Enc::new();
        e.i32(pid);
        e.bool(compat);
        e.u32(veuid);
        e.string(arena);
        e.u64(bwr_addr);
        e.opt_bytes(bwr.as_deref());
        e.opt_bytes(stream.as_deref());
        // 0.9.141 (P3): the sender thread's assembly-
        // window profile snapshot rides after the
        // stream (both ends are this same build).
        e.u32(win.0);
        e.u32(win.1);
        e.u32(win.2);
        e.u32(win.3);
        e.u32(win.4);
        e.u32(win.5);
        let p = self.rpc(MSG_REQ_WRITE_READ, &e.0, MSG_RESP_ACTIONS);
        let mut d = Dec::new(&p);
        (d.string(), d.logs(), d.actions())
    }

    fn complete_parked(&mut self, pid: i32) -> (Vec<(String, String)>, ParkedOutcome) {
        let mut e = Enc::new();
        e.i32(pid);
        let p = self.rpc(MSG_REQ_COMPLETE_PARKED, &e.0, MSG_RESP_COMPLETE);
        let mut d = Dec::new(&p);
        let logs = d.logs();
        let outcome = if d.u8() == 1 {
            let park = d.park();
            let bytes = d.bytes();
            let fixups = if d.bool() {
                let arena = d.string();
                let fx = d.fixups();
                let cache = d.cache();
                Some((arena, fx, cache))
            } else {
                None
            };
            ParkedOutcome::Complete { park, bytes, fixups }
        } else {
            ParkedOutcome::Nothing
        };
        (logs, outcome)
    }

    /// Proc-exit binder cleanup. None means the thread
    /// had no arena registered (the old code's early
    /// return); Some carries the captured logs and the
    /// parked threads the exit wants woken, in order.
    fn thread_exit(&mut self, pid: i32) -> Option<(Vec<(String, String)>, Vec<i32>)> {
        let mut e = Enc::new();
        e.i32(pid);
        let p = self.rpc(MSG_REQ_THREAD_EXIT, &e.0, MSG_RESP_THREAD_EXIT);
        let mut d = Dec::new(&p);
        if !d.bool() {
            return None;
        }
        let logs = d.logs();
        let n = d.u32();
        let dwakes = (0..n).map(|_| d.i32()).collect();
        Some((logs, dwakes))
    }

    /// 0.9.131 ignition forensics, trigger B plumbing:
    /// ask the coordinator to print one pid's ignition
    /// evidence ring (the coordinator owns the binder
    /// state) and hand the captured lines back for
    /// in-order replay beside the FATAL line, exactly
    /// like thread_exit. Whether the pc qualifies is
    /// the caller's judgement (see the FATAL site).
    fn ignition_dump(&mut self, pid: i32, trigger: &str) -> Vec<(String, String)> {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(trigger);
        let p = self.rpc(MSG_REQ_IGNITION_DUMP, &e.0, MSG_RESP_IGNITION_DUMP);
        let mut d = Dec::new(&p);
        d.logs()
    }

    /// 0.9.140 wedge forensics (M3 plumbing): ask the
    /// coordinator for one system_server tenure's
    /// chain dump (the coordinator owns the binder
    /// state) and hand the captured lines back for
    /// in-order replay beside the wedge snapshot,
    /// exactly like ignition_dump. The solo futex
    /// waiter the snapshot named (0 when none) rides
    /// along for the verdict; the reply carries the
    /// holder the verdict named, for the traces
    /// harvest (M5). Guest-memory reads the
    /// coordinator needs on the way (frozen ioctl
    /// write streams) ride the rpc's reverse channel,
    /// as with every other decision.
    fn wedge_chain(
        &mut self,
        leader: i32,
        solo: i32,
    ) -> (Vec<(String, String)>, i32, Vec<(String, i32)>) {
        let mut e = Enc::new();
        e.i32(leader);
        e.i32(solo);
        let p = self.rpc(MSG_REQ_WEDGE_CHAIN, &e.0, MSG_RESP_WEDGE_CHAIN);
        let mut d = Dec::new(&p);
        let logs = d.logs();
        let holder = d.i32();
        // 0.9.141 (S6): the servicers the chain named,
        // for the coordinator's face broadcast record;
        // the requesting worker itself does not consume
        // them (the broadcast reaches it like everyone).
        let n = d.u32();
        let mut servicers = Vec::new();
        for _ in 0..n {
            let a = d.string();
            let p = d.i32();
            servicers.push((a, p));
        }
        (logs, holder, servicers)
    }

    fn set_context_mgr(
        &mut self,
        pid: i32,
        arena: &str,
    ) -> (bool, Vec<(String, String)>, Vec<BAction>, usize, usize) {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(arena);
        let p = self.rpc(MSG_REQ_SET_CONTEXT_MGR, &e.0, MSG_RESP_CTX_MGR);
        let mut d = Dec::new(&p);
        let ok = d.bool();
        let logs = d.logs();
        let acts = d.actions();
        let delivered = d.usize();
        let total = d.usize();
        (ok, logs, acts, delivered, total)
    }

    fn open_binder(&mut self, pid: i32, rootfs: &str) -> Result<(String, String), String> {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(rootfs);
        let p = self.rpc(MSG_REQ_OPEN_BINDER, &e.0, MSG_RESP_OPEN_BINDER);
        let mut d = Dec::new(&p);
        if d.bool() {
            let arena = d.string();
            let raw = d.string();
            Ok((arena, raw))
        } else {
            Err(d.string())
        }
    }

    fn open_ashmem(&mut self, pid: i32, rootfs: &str) -> String {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(rootfs);
        let p = self.rpc(MSG_REQ_OPEN_ASHMEM, &e.0, MSG_RESP_OPEN_ASHMEM);
        Dec::new(&p).string()
    }

    fn ashmem_get(&mut self, key: &str) -> Option<AshmemInfo> {
        let mut e = Enc::new();
        e.string(key);
        let p = self.rpc(MSG_REQ_ASHMEM_GET, &e.0, MSG_RESP_ASHMEM_GET);
        let mut d = Dec::new(&p);
        if !d.bool() {
            return None;
        }
        Some(AshmemInfo { size: d.u64(), name: d.string(), prot: d.u64() })
    }

    fn oneway_park(&mut self, pid: i32, park: &ParkedIoctl) {
        let mut e = Enc::new();
        e.i32(pid);
        e.park(park);
        self.send(MSG_ONEWAY_PARK, &e.0);
    }

    fn oneway_fd_cache_put(&mut self, entries: &[(CacheKey, i32)]) {
        if entries.is_empty() {
            return;
        }
        let mut e = Enc::new();
        e.cache(entries);
        self.send(MSG_ONEWAY_FD_CACHE_PUT, &e.0);
    }

    /// 0.9.134: report one failed fixup group to the
    /// coordinator (counting, plus whatever finishing
    /// the disposition names -- see fd_fail_convert_
    /// local and the MSG_ONEWAY_FD_FAIL handler).
    #[allow(clippy::too_many_arguments)]
    fn oneway_fd_fail(
        &mut self,
        arena: &str,
        data_va: u32,
        sender_pid: i32,
        sender_fd: i32,
        nfail: u32,
        disp: u8,
        fail_pid: i32,
        code: u32,
        why: &str,
    ) {
        let mut e = Enc::new();
        e.string(arena);
        e.u32(data_va);
        e.i32(sender_pid);
        e.i32(sender_fd);
        e.u32(nfail);
        e.u8(disp);
        e.i32(fail_pid);
        e.u32(code);
        e.string(why);
        self.send(MSG_ONEWAY_FD_FAIL, &e.0);
    }

    /// 0.9.134: per-resolution fixup statistics deltas
    /// (low-slot dups performed, write-back
    /// verifications passed). 0.9.137 appends the
    /// injected-open retry deltas (retries performed,
    /// fixups saved by one).
    fn oneway_fd_stats(&mut self, dupped: u32, verified: u32, retried: u32, retry_saved: u32) {
        let mut e = Enc::new();
        e.u32(dupped);
        e.u32(verified);
        e.u32(retried);
        e.u32(retry_saved);
        self.send(MSG_ONEWAY_FD_STATS, &e.0);
    }

    /// 0.9.141 (s9-141-desk P1): issuance double-read
    /// deltas from this worker (snapshots taken,
    /// buffers found differing at the re-read).
    fn oneway_issuance_stats(&mut self, reads: u32, differs: u32) {
        let mut e = Enc::new();
        e.u32(reads);
        e.u32(differs);
        self.send(MSG_ONEWAY_ISSUANCE_STATS, &e.0);
    }

    fn oneway_park_remove(&mut self, pid: i32) {
        let mut e = Enc::new();
        e.i32(pid);
        self.send(MSG_ONEWAY_PARK_REMOVE, &e.0);
    }

    fn oneway_thread_arena(&mut self, pid: i32, arena: &str) {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(arena);
        self.send(MSG_ONEWAY_THREAD_ARENA, &e.0);
    }

    fn oneway_arena_register(&mut self, pid: i32, arena: &str, base: u32, maplen: u32) {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(arena);
        e.u32(base);
        e.u32(maplen);
        self.send(MSG_ONEWAY_ARENA_REGISTER, &e.0);
    }

    fn oneway_thread_exit_ioctl(&mut self, pid: i32, arena: &str) {
        let mut e = Enc::new();
        e.i32(pid);
        e.string(arena);
        self.send(MSG_ONEWAY_THREAD_EXIT_IOCTL, &e.0);
    }

    fn oneway_ashmem_set_name(&mut self, key: &str, name: &str) {
        let mut e = Enc::new();
        e.string(key);
        e.string(name);
        self.send(MSG_ONEWAY_ASHMEM_SET_NAME, &e.0);
    }

    fn oneway_ashmem_set_size(&mut self, key: &str, size: u64) {
        let mut e = Enc::new();
        e.string(key);
        e.u64(size);
        self.send(MSG_ONEWAY_ASHMEM_SET_SIZE, &e.0);
    }

    fn oneway_ashmem_set_prot(&mut self, key: &str, prot: u64) {
        let mut e = Enc::new();
        e.string(key);
        e.u64(prot);
        self.send(MSG_ONEWAY_ASHMEM_SET_PROT, &e.0);
    }

    /// 0.9.120 telemetry: shield_live_pairs delivered
    /// a REF pair whose referent already looks dead
    /// (see the probe there). The worker cannot name
    /// the pair's node or keep the global count --
    /// both live in the coordinator's BinderState --
    /// so the sighting is reported, not logged here.
    fn oneway_shield_cookie_suspect(&mut self, pid: i32, ptr: u32, cookie: u32, why: &str) {
        let mut e = Enc::new();
        e.i32(pid);
        e.u32(ptr);
        e.u32(cookie);
        e.string(why);
        self.send(MSG_ONEWAY_SHIELD_COOKIE_SUSPECT, &e.0);
    }

    /// S2 routing: this tracer now owns `pid`, with
    /// these virtual credentials (seeds the coordinator's
    /// global credential book too).
    fn register_pid(&mut self, pid: i32, creds: (u32, u32)) {
        let mut e = Enc::new();
        e.i32(pid);
        e.u32(creds.0);
        e.u32(creds.1);
        self.send(MSG_ONEWAY_REGISTER_PID, &e.0);
    }

    /// S2 routing: `pid` is gone (or being taken back);
    /// the coordinator drops our route for it.
    fn unregister_pid(&mut self, pid: i32) {
        let mut e = Enc::new();
        e.i32(pid);
        self.send(MSG_ONEWAY_UNREGISTER_PID, &e.0);
    }

    /// S2 credential book: a faked setid changed this
    /// pid's virtual credentials; publish them.
    fn vcred_publish(&mut self, pid: i32, creds: (u32, u32)) {
        let mut e = Enc::new();
        e.i32(pid);
        e.u32(creds.0);
        e.u32(creds.1);
        self.send(MSG_ONEWAY_VCRED_PUBLISH, &e.0);
    }

    /// S2 credential book: ask the coordinator for a
    /// pid's virtual credentials (SO_PEERCRED rewrite
    /// for a peer another worker traces).
    fn vcred_query(&mut self, pid: i32) -> Option<(u32, u32)> {
        let mut e = Enc::new();
        e.i32(pid);
        let p = self.rpc(MSG_REQ_VCRED, &e.0, MSG_RESP_VCRED);
        let mut d = Dec::new(&p);
        if d.bool() {
            Some((d.u32(), d.u32()))
        } else {
            None
        }
    }

    /// S2 routing: a decision wants this parked pid
    /// woken, but another worker owns it; the
    /// coordinator pushes the wake to its owner.
    fn wake_route(&mut self, pid: i32) {
        let mut e = Enc::new();
        e.i32(pid);
        self.send(MSG_ONEWAY_WAKE_ROUTE, &e.0);
    }

    /// Freeze forensics (0.9.81): W0 relays the
    /// shell's stack-dump request (it arrived as
    /// SIGUSR2; the handler only set a flag, and W0's
    /// event loop calls this at its next coordinator
    /// service point). The coordinator broadcasts it
    /// to the workers as MSG_PUSH_DUMP_STACKS. No
    /// payload: the request carries nothing but
    /// itself.
    fn dump_req(&mut self) {
        self.send(MSG_ONEWAY_DUMP_REQ, &[]);
    }

    /// S2 handoff offer: the offering tracer has
    /// detached `pid` (stopped) and asks the coordinator
    /// to route it to worker `twid`, carrying the state
    /// the new tracer needs to rebuild its ProcState.
    /// `root` marks a root-service handoff: the adoptee
    /// becomes the target worker's shard root.
    fn handoff_notice(
        &mut self,
        pid: i32,
        twid: u8,
        vcwd: &str,
        compat: bool,
        sigmask: u32,
        creds: (u32, u32),
        root: bool,
    ) {
        let mut e = Enc::new();
        e.i32(pid);
        e.u8(twid);
        e.string(vcwd);
        e.bool(compat);
        e.u32(sigmask);
        e.u32(creds.0);
        e.u32(creds.1);
        e.bool(root);
        self.send(MSG_ONEWAY_HANDOFF, &e.0);
    }

    /// S2 handoff verdict: this worker did (or did not)
    /// attach the handed-off pid.
    fn adopt_ack(&mut self, pid: i32, ok: bool) {
        let mut e = Enc::new();
        e.i32(pid);
        e.bool(ok);
        self.send(MSG_ONEWAY_ADOPT_ACK, &e.0);
    }
}

/// Fork the coordinator: this same binary, running
/// coordinator_main, which listens on a unix socket
/// under the rootfs so every tracer (W0 and the S2
/// workers) can connect. The child's stdout is
/// redirected to /dev/null before anything else -- its
/// inherited stdout is the shell's log pipe, and
/// nothing but protocol frames may ever leave it. Its
/// stderr stays inherited, so a panic in the
/// coordinator shows up in the shell's stderr like any
/// supervisor crash did.
fn spawn_coordinator(sock_path: &str) {
    let cpid = unsafe { libc::fork() };
    if cpid < 0 {
        sup!("coordinator fork failed: errno={}", errno());
        std::process::exit(1);
    }
    if cpid == 0 {
        unsafe {
            let dn = libc::open(
                b"/dev/null\0".as_ptr() as *const libc::c_char,
                libc::O_WRONLY,
            );
            if dn >= 0 {
                if dn != 1 {
                    libc::dup2(dn, 1);
                }
                if dn > 2 {
                    libc::close(dn);
                }
            }
        }
        coordinator_main(sock_path);
    }
}


/// The proc-exit binder cleanup sequence, coordinator
/// side (S1b): drop the thread's arena registration
/// and its looper membership, then run the driver's
/// death processing and report who it wants woken --
/// the exact order the main loop used to run them in.
fn binder_thread_exit(pid: i32, st: &mut BinderState) -> Option<Vec<i32>> {
    let a = st.thread_arena.remove(&pid)?;
    if let Some(bp) = st.procs.get_mut(&a) {
        bp.loopers.remove(&pid);
    }
    let mut dwakes: Vec<i32> = Vec::new();
    // 0.9.125: transactions this thread had claimed die
    // with it -- a claimed wait lives only on its stack
    // and no other thread can answer for a parcel only
    // it consumed. Fail their callers with DEAD_REPLY
    // now (unclaimed waits get the same treatment at
    // arena death in binder_on_proc_exit; running this
    // first, for every exiting thread including the
    // arena's last, keeps each wait's failure single).
    // 0.9.135: the thread's collision-check rings die
    // with it, like its serving stack below -- a
    // recycled pid must never collide against a dead
    // thread's parcels.
    st.claim_parcels.remove(&pid);
    st.send_src.remove(&pid);
    if let Some(stack) = st.serving.remove(&pid) {
        // 0.9.130: groups oldest-first, frames in claim
        // order -- the flat stack's iteration order, so
        // every claimed wait is still failed exactly
        // once, in the order it was claimed.
        for fr in stack.groups.into_iter().flat_map(|g| g.frames) {
            if let ServingFrame::Reply(w, _) = fr {
                if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                    bp.push_to(w.sender_pid, &BR_DEAD_REPLY.to_le_bytes());
                }
                // 0.9.131: the DEAD_REPLY is an event in
                // the waiter's evidence ring.
                evidence_tag(
                    st,
                    &w.sender_arena,
                    format!("dead-reply code={} thread={pid}", w.code),
                );
                binder_maybe_wake_pids(st, &w.sender_arena, &mut dwakes);
            }
        }
    }
    binder_on_proc_exit(&a, st, &mut dwakes);
    Some(dwakes)
}

/// SET_CONTEXT_MGR state work, coordinator side (S1b):
/// the whole registration-and-flush sequence the ioctl
/// dispatch used to run inline. Returns (registered,
/// flush actions, delivered, total). The flush actions
/// only ever wake threads, so the tracer executes them
/// at the same stop before skipping the syscall, and
/// prints the flushed line itself afterwards.
fn binder_set_context_mgr(
    arena: &str,
    st: &mut BinderState,
) -> (bool, Vec<BAction>, usize, usize) {
    if let Some(m) = &st.mgr_arena {
        if m != arena {
            return (false, Vec::new(), 0, 0);
        }
    } else {
        st.mgr_arena = Some(arena.to_string());
    }
    let node = st.node_for_local(arena, 0, 0);
    st.mgr_node = Some(node);
    let (nptr, ncookie) = {
        let n = &st.nodes[node];
        (n.ptr, n.cookie)
    };
    let pending = std::mem::take(&mut st.mgr_pending);
    let total = pending.len();
    let mut delivered = 0usize;
    let mut acts: Vec<BAction> = Vec::new();
    for q in &pending {
        bsup!(
            "binder: flushing queued mgr txn from pid={} code={}",
            q.sender_pid,
            q.code
        );
        if !st.procs.contains_key(&q.sender_arena) {
            bsup!(
                "binder: queued mgr txn from pid={} dropped (sender arena gone)",
                q.sender_pid
            );
            continue;
        }
        // The per-transaction notes were collected by
        // the old inline flush and never used; they are
        // dropped here too, exactly as unread as before.
        let mut qnotes: Vec<String> = Vec::new();
        binder_send_txn(
            st,
            &mut acts,
            &mut qnotes,
            &q.sender_arena,
            q.sender_pid,
            q.target_handle,
            q.cookie,
            nptr,
            ncookie,
            arena,
            q.code,
            q.flags,
            q.veuid,
            &q.data,
            &q.offs,
        );
        delivered += 1;
    }
    (true, acts, delivered, total)
}

/// The state half of opening /dev/binder, coordinator
/// side (S1b): create the arena file under the guest
/// rootfs, register the proc, and report both paths --
/// the canonical arena key and the raw path the guest
/// opens. The filesystem work is the same operations
/// in the same order the tracer used to do inline;
/// only the process doing them changed.
fn binder_open_arena(
    pid: i32,
    rootfs: &str,
    st: &mut BinderState,
) -> Result<(String, String), String> {
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
    match std::fs::OpenOptions::new().create(true).read(true).write(true).open(&arena) {
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
                parcels: HashMap::new(),
                free_hit: 0,
                free_nobase: 0,
                free_stale: 0,
                free_parcel_hit: 0,
                free_miss: 0,
                free_rescued: 0,
                handles: HashMap::new(),
                next_handle: 1,
                inbound: Vec::new(),
                queues: HashMap::new(),
                loopers: HashSet::new(),
            });
        }
        Err(e) => return Err(e.to_string()),
    }
    st.thread_arena.insert(pid, arena.clone());
    Ok((arena, arena_raw))
}

/// The state half of opening /dev/ashmem, coordinator
/// side (S1b): create the region backing file (mode
/// 0700 -- the exec permission is load-bearing, see the
/// execute-map ruling in supervisor history), register
/// the record, and report the raw path the tracer
/// rewrites the guest's open to.
fn ashmem_open_region(pid: i32, rootfs: &str, st: &mut BinderState) -> String {
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
    raw
}

/// The state half of completing a parked WRITE_READ,
/// coordinator side (S1b): the exact sequence the old
/// complete_parked ran against the state before it
/// touched the guest -- remove the park, resolve the
/// thread's arena and queue, drain the pending reply
/// bytes, and take any fd fixups owed to this arena.
/// A drained-empty queue puts the park back (Nothing),
/// as before. What the tracer still owes is returned:
/// the reply bytes to write into the guest, and the
/// fixups with the cache entries they will consult.
/// The parcel data VAs a BR byte stream carries: the
/// data pointer of every BR_TRANSACTION / BR_REPLY
/// record in it, walked with the same advance rules
/// fd_locate_cmd uses.
fn stream_data_vas(bytes: &[u8]) -> Vec<u32> {
    let mut vas = Vec::new();
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(bytes, off);
        let len = br_one_len(cmd);
        if off + len > bytes.len() {
            break;
        }
        if (cmd == BR_TRANSACTION || cmd == BR_REPLY) && len == 44 {
            vas.push(u32_at(bytes, off + 36));
        }
        off += len;
    }
    vas
}

/// 0.9.136: take the pending fd fixups that belong to
/// one guest-bound batch -- the ones whose parcel data
/// VA the batch's byte stream names -- and leave the
/// rest queued for their own deliveries.
///
/// Both settle points (binder_complete_decision for a
/// parked wake, binder_write_read for an inline fill)
/// used to drain the arena's WHOLE fd_pending list into
/// whichever completion or fill came first. A fixup
/// settled by a sibling thread's batch was resolved in
/// the sibling's context, and on failure its conversion
/// searched the sibling's stream, missed, and fell to
/// the coordinator's queue search -- which misses in
/// turn when the owning delivery's bytes have already
/// been drained by their own completion and are in
/// flight to their worker: fd-fixup-fail-late, the one
/// outcome where a guest can consume a parcel whose fd
/// words were never settled. Selecting per delivery
/// closes that by construction: a fixup is only ever
/// settled by the decision handing its own delivery to
/// the guest, in that guest's worker, before the batch
/// is written or the tracee continued. (The .135
/// field's three "late convert" cases were re-audited
/// against this: all three took the parked path, where
/// complete_parked already resolves and converts
/// before write_mem and cont_syscall; the guest-side
/// line interleaved between the fail and convert lines
/// is the resolver wrapper's own parked-desc print at
/// rides>0, not a guest read. The hole closed here is
/// the cross-decision one above, which the field has
/// not fired yet.)
fn take_fixups_for(
    st: &mut BinderState,
    arena: &str,
    vas: &[u32],
) -> Option<(String, Vec<FdFixup>, Vec<(CacheKey, i32)>)> {
    let pending = st.fd_pending.get_mut(arena)?;
    if pending.is_empty() {
        return None;
    }
    let mut taken: Vec<FdFixup> = Vec::new();
    let mut left: Vec<FdFixup> = Vec::new();
    for f in pending.drain(..) {
        if vas.contains(&f.data_va) {
            taken.push(f);
        } else {
            left.push(f);
        }
    }
    *pending = left;
    if taken.is_empty() {
        return None;
    }
    // The resolver runs tracer-side but the cache lives
    // here: attach the entries these fixups will
    // consult; what it learns comes back before any
    // later decision reads the cache again.
    let cache: Vec<(CacheKey, i32)> = taken
        .iter()
        .filter_map(|f| {
            let key: CacheKey = (arena.to_string(), f.sender_pid, f.sender_fd);
            st.fd_cache.get(&key).map(|fd| (key, *fd))
        })
        .collect();
    Some((arena.to_string(), taken, cache))
}

fn binder_complete_decision(pid: i32, st: &mut BinderState) -> ParkedOutcome {
    let Some(park) = st.parked.remove(&pid) else {
        return ParkedOutcome::Nothing;
    };
    let Some(arena) = st.thread_arena.get(&pid).cloned() else {
        return ParkedOutcome::Nothing;
    };
    let (bytes, from_inbound) = {
        let Some(bp) = st.procs.get_mut(&arena) else {
            return ParkedOutcome::Nothing;
        };
        // Command-boundary cut, same rule as the inline
        // fill (br_prefix_len): a parked reader woken
        // with a split command is the same poison.
        let peek = bp.peek_for(pid, park.read_size as usize);
        let n = br_prefix_len(&peek, park.read_size as usize);
        bp.drain_for(pid, n)
    };
    let bytes = shield_ref_pairs(st, &arena, pid, bytes);
    binder_claim_fills(st, &arena, pid, &bytes);
    if !bytes.is_empty() {
        bsup!(
            "binder: waking pid={pid} with {}B of queued work ({}B from inbound)",
            bytes.len(),
            from_inbound
        );
        dump_mgr_read(st, &arena, pid, &bytes);
        // Drain-verify: re-read every object-carrying parcel
        // this batch points at from the arena file, under
        // each registered base, and dump its slots as the
        // guest is about to see them.
        {
            let mut vi = 0usize;
            while vi + 4 <= bytes.len() {
                let cmd = u32_at(&bytes, vi);
                let adv = match cmd {
                    BR_TRANSACTION | BR_REPLY => 44,
                    BR_INCREFS | BR_ACQUIRE | 0x8008_7209 | 0x8008_720a => 12,
                    BR_DEAD_BINDER | BR_CLEAR_DEATH_NOTIFICATION_DONE | 0x8000_7200 => 8,
                    _ => 4,
                };
                if (cmd == BR_TRANSACTION || cmd == BR_REPLY) && vi + 44 <= bytes.len() {
                    let dsize = u32_at(&bytes, vi + 28) as usize;
                    let osize = u32_at(&bytes, vi + 32) as usize;
                    let daddr = u32_at(&bytes, vi + 36);
                    let oaddr = u32_at(&bytes, vi + 40);
                    if osize > 0 && dsize <= (1 << 20) && osize <= (1 << 16) {
                        if let Some(bp) = st.procs.get(&arena) {
                            for (bpid, base) in &bp.base {
                                let (Some(doff), Some(ooff)) = (
                                    daddr.checked_sub(*base),
                                    oaddr.checked_sub(*base),
                                ) else {
                                    continue;
                                };
                                let mut dbuf = vec![0u8; dsize];
                                let mut obuf = vec![0u8; osize];
                                if bp.file.read_exact_at(&mut dbuf, doff as u64).is_ok()
                                    && bp.file.read_exact_at(&mut obuf, ooff as u64).is_ok()
                                {
                                    bsup!(
                                        "binder: drain-verify pid={pid} base_pid={bpid} slots{}",
                                        slot_dump(&dbuf, &obuf)
                                    );
                                    break;
                                }
                            }
                        }
                    }
                }
                vi += adv;
            }
        }
    }
    if bytes.is_empty() {
        st.parked.insert(pid, park);
        return ParkedOutcome::Nothing;
    }
    // 0.9.136: only the fixups whose deliveries this
    // completion's own bytes carry (see take_fixups_for);
    // the rest stay queued for their own completions.
    let fixups = take_fixups_for(st, &arena, &stream_data_vas(&bytes));
    ParkedOutcome::Complete { park, bytes, fixups }
}

/// The coordinator: own BinderState and answer the
/// tracer's requests until the channel closes. EOF --
/// the tracer died or the socket broke -- ends the
/// process silently: a driver with no tracer has no
/// guests left to serve. Replies are best-effort
/// writes for the same reason; if the tracer is gone
/// the next read ends the loop anyway.
/// Move every complete frame out of a connection's
/// input buffer into its frame queue; a malformed
/// length marks the connection dead.
fn extract_frames(
    inbuf: &mut Vec<u8>,
    queue: &mut std::collections::VecDeque<(u8, Vec<u8>)>,
    dead: &mut bool,
) {
    loop {
        if inbuf.len() < 4 {
            return;
        }
        let len = u32::from_le_bytes(inbuf[..4].try_into().unwrap()) as usize;
        if len == 0 || len > (64 << 20) {
            *dead = true;
            return;
        }
        if inbuf.len() < 4 + len {
            return;
        }
        let frame: Vec<u8> = inbuf.drain(..4 + len).collect();
        let kind = frame[4];
        let payload = frame[5..].to_vec();
        queue.push_back((kind, payload));
    }
}

/// One accepted tracer connection on the
/// coordinator's listening socket.
struct CConn {
    s: UnixStream,
    inbuf: Vec<u8>,
    queue: std::collections::VecDeque<(u8, Vec<u8>)>,
    wid: Option<u8>,
    dead: bool,
}

/// The coordinator process (S2): BinderState plus the
/// pid -> worker route table and the global virtual
/// credential book, served to every tracer over one
/// listening socket. Frames are handled strictly one
/// at a time across all connections, and a decision
/// that needs reverse reads waits only on its own
/// connection -- the atomicity the single-tracer S1b
/// channel had; other connections' frames simply
/// queue while a decision runs. W0's connection
/// closing is the death-chain trigger: the
/// coordinator exits, every worker's connection
/// EOFs, and the workers exit in turn.
struct CoordServer {
    conns: Vec<CConn>,
    st: BinderState,
    routes: HashMap<i32, usize>,
    vcreds_g: HashMap<i32, (u32, u32)>,
    w0: Option<usize>,
    /// Handoffs in flight: guest pid -> the connection
    /// that offered it, so the adopt verdict returns to
    /// the offering tracer (W0 for root-service
    /// handoffs, a worker for kin re-shards).
    handoff_from: HashMap<i32, usize>,
}

impl CoordServer {
    fn conn_by_wid(&self, wid: u8) -> Option<usize> {
        self.conns.iter().position(|c| !c.dead && c.wid == Some(wid))
    }

    /// Read once from a connection poll has flagged;
    /// a clean EOF or a hard error marks it dead.
    fn fill(&mut self, ci: usize) {
        use std::io::Read;
        let mut buf = [0u8; 65536];
        let c = &mut self.conns[ci];
        match c.s.read(&mut buf) {
            Ok(0) => c.dead = true,
            Ok(n) => c.inbuf.extend_from_slice(&buf[..n]),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
            Err(_) => c.dead = true,
        }
    }

    fn extract(&mut self, ci: usize) {
        let c = &mut self.conns[ci];
        extract_frames(&mut c.inbuf, &mut c.queue, &mut c.dead);
    }

    fn send_to(&mut self, ci: usize, kind: u8, payload: &[u8]) {
        if ci >= self.conns.len() || self.conns[ci].dead {
            return;
        }
        let c = &mut self.conns[ci];
        if !write_msg(&mut c.s, kind, payload) {
            c.dead = true;
        }
    }

    /// Deliver a wake for `pid` to the worker that
    /// owns it. No route means the pid died in the
    /// meantime; the wake is dropped, which is
    /// strictly safer than the old single-tracer world
    /// completing a parked entry for a recycled pid.
    fn push_wake(&mut self, pid: i32) {
        if let Some(&ci) = self.routes.get(&pid) {
            let mut e = Enc::new();
            e.i32(pid);
            self.send_to(ci, MSG_PUSH_WAKE, &e.0);
        }
    }

    /// The adopt verdict goes back to the tracer that
    /// offered the handoff.
    fn push_adopt_ack(&mut self, ci: usize, pid: i32, ok: bool) {
        let mut e = Enc::new();
        e.i32(pid);
        e.bool(ok);
        self.send_to(ci, MSG_PUSH_ADOPT_ACK, &e.0);
    }

    /// Freeze forensics (0.9.81): broadcast the
    /// shell's stack-dump request to every worker.
    /// Exactly one of them can hold a system_server
    /// candidate; the rest drop the push. W0 is
    /// skipped: it traces the guest root's shard and
    /// never adopts a root, so it can never hold a
    /// candidate.
    fn push_dump_stacks(&mut self) {
        for ci in 0..self.conns.len() {
            if self.conns[ci].wid.map_or(false, |w| w != 0) {
                self.send_to(ci, MSG_PUSH_DUMP_STACKS, &[]);
            }
        }
    }

    /// 0.9.141 (s9-141-desk S6): broadcast the wedge
    /// chain's servicer list to every worker (W0
    /// included: a failed shard fork can leave a
    /// service on W0, and the push is a no-op for any
    /// worker that does not own a named pid).
    fn push_servicer_face(&mut self, ss_arena: &str, servicers: &[(String, i32)]) {
        let mut e = Enc::new();
        e.string(ss_arena);
        e.u32(servicers.len() as u32);
        for (_, p) in servicers {
            e.i32(*p);
        }
        for ci in 0..self.conns.len() {
            if self.conns[ci].wid.is_some() {
                self.send_to(ci, MSG_PUSH_SERVICER_FACE, &e.0);
            }
        }
    }

    /// A connection died: drop its routes (its
    /// tracees are being EXITKILLed with it). W0's
    /// death ends the run: exit, and every worker
    /// sees EOF on its own connection.
    fn conn_died(&mut self, ci: usize) {
        self.routes.retain(|_, &mut owner| owner != ci);
        self.handoff_from.retain(|_, &mut from| from != ci);
        if self.w0 == Some(ci) {
            std::process::exit(0);
        }
    }

    /// Handle one frame from connection `ci`. The
    /// S1b arms are unchanged in shape: decode, run
    /// the binder/ashmem state work, reply on the
    /// same connection. New in S2: HELLO, the routing
    /// and credential-book oneways, the vcred query,
    /// and the handoff.
    fn handle(&mut self, ci: usize, kind: u8, payload: &[u8]) {
        let mut d = Dec::new(payload);
        match kind {
            MSG_HELLO => {
                let wid = d.u8();
                let _shard = d.string();
                if ci < self.conns.len() {
                    self.conns[ci].wid = Some(wid);
                }
                if wid == 0 {
                    self.w0 = Some(ci);
                }
            }
            MSG_REQ_WRITE_READ => {
                let pid = d.i32();
                let _compat = d.bool();
                let veuid = d.u32();
                let arena = d.string();
                let bwr_addr = d.u64();
                let bwr = d.opt_bytes();
                let stream = d.opt_bytes();
                // 0.9.141 (P3): the sender thread's
                // assembly-window profile snapshot,
                // appended after the stream.
                let win = (d.u32(), d.u32(), d.u32(), d.u32(), d.u32(), d.u32());
                cap_clear();
                let mut actions: Vec<BAction> = Vec::new();
                let desc = {
                    // Disjoint field borrows: the state
                    // goes to the decision, the one
                    // connection serves its reverse reads.
                    let st = &mut self.st;
                    let conn = &mut self.conns[ci];
                    use std::os::unix::io::AsRawFd;
                    let cfd = conn.s.as_raw_fd();
                    let mut rd = |rpid: i32, addr: u64, len: usize| -> Option<Vec<u8>> {
                        let mut re = Enc::new();
                        re.i32(rpid);
                        re.u64(addr);
                        re.usize(len);
                        if !write_msg(&mut conn.s, MSG_REV_READ, &re.0) {
                            return None;
                        }
                        loop {
                            if let Some((k, p)) = conn.queue.pop_front() {
                                if k == MSG_REV_READ_RESP {
                                    return Dec::new(&p).opt_bytes();
                                }
                                return None;
                            }
                            if conn.dead {
                                return None;
                            }
                            let mut pfd = libc::pollfd {
                                fd: cfd,
                                events: libc::POLLIN,
                                revents: 0,
                            };
                            let n = unsafe { libc::poll(&mut pfd, 1, -1) };
                            if n < 0 {
                                if errno() == libc::EINTR {
                                    continue;
                                }
                                return None;
                            }
                            if n == 0 || pfd.revents == 0 {
                                continue;
                            }
                            use std::io::Read;
                            let mut buf = [0u8; 65536];
                            match conn.s.read(&mut buf) {
                                Ok(0) => {
                                    conn.dead = true;
                                    return None;
                                }
                                Ok(m) => {
                                    conn.inbuf.extend_from_slice(&buf[..m]);
                                    extract_frames(
                                        &mut conn.inbuf,
                                        &mut conn.queue,
                                        &mut conn.dead,
                                    );
                                }
                                Err(e)
                                    if e.kind() == std::io::ErrorKind::WouldBlock => {}
                                Err(_) => {
                                    conn.dead = true;
                                    return None;
                                }
                            }
                        }
                    };
                    st.cur_win = Some(win);
                    let desc = binder_write_read(
                        pid,
                        &arena,
                        bwr_addr,
                        bwr,
                        stream,
                        st,
                        veuid,
                        &mut rd,
                        &mut actions,
                    );
                    st.cur_win = None;
                    desc
                };
                let mut e = Enc::new();
                e.string(&desc);
                e.logs(&cap_take());
                e.actions(&actions);
                self.send_to(ci, MSG_RESP_ACTIONS, &e.0);
            }
            MSG_REQ_COMPLETE_PARKED => {
                let pid = d.i32();
                cap_clear();
                let outcome = binder_complete_decision(pid, &mut self.st);
                let mut e = Enc::new();
                e.logs(&cap_take());
                match &outcome {
                    ParkedOutcome::Nothing => e.u8(0),
                    ParkedOutcome::Complete { park, bytes, fixups } => {
                        e.u8(1);
                        e.park(park);
                        e.bytes(bytes);
                        match fixups {
                            None => e.bool(false),
                            Some((arena, fx, cache)) => {
                                e.bool(true);
                                e.string(arena);
                                e.fixups(fx);
                                e.cache(cache);
                            }
                        }
                    }
                }
                self.send_to(ci, MSG_RESP_COMPLETE, &e.0);
            }
            MSG_REQ_THREAD_EXIT => {
                let pid = d.i32();
                cap_clear();
                match binder_thread_exit(pid, &mut self.st) {
                    Some(dwakes) => {
                        let mut e = Enc::new();
                        e.bool(true);
                        e.logs(&cap_take());
                        e.u32(dwakes.len() as u32);
                        for w in dwakes {
                            e.i32(w);
                        }
                        self.send_to(ci, MSG_RESP_THREAD_EXIT, &e.0);
                    }
                    None => {
                        let mut e = Enc::new();
                        e.bool(false);
                        self.send_to(ci, MSG_RESP_THREAD_EXIT, &e.0);
                    }
                }
            }
            MSG_REQ_SET_CONTEXT_MGR => {
                let _pid = d.i32();
                let arena = d.string();
                cap_clear();
                let (ok, acts, delivered, total) =
                    binder_set_context_mgr(&arena, &mut self.st);
                let mut e = Enc::new();
                e.bool(ok);
                e.logs(&cap_take());
                e.actions(&acts);
                e.usize(delivered);
                e.usize(total);
                self.send_to(ci, MSG_RESP_CTX_MGR, &e.0);
            }
            MSG_REQ_OPEN_BINDER => {
                let pid = d.i32();
                let rootfs = d.string();
                let mut e = Enc::new();
                match binder_open_arena(pid, &rootfs, &mut self.st) {
                    Ok((arena, raw)) => {
                        e.bool(true);
                        e.string(&arena);
                        e.string(&raw);
                    }
                    Err(err) => {
                        e.bool(false);
                        e.string(&err);
                    }
                }
                self.send_to(ci, MSG_RESP_OPEN_BINDER, &e.0);
            }
            MSG_REQ_OPEN_ASHMEM => {
                let pid = d.i32();
                let rootfs = d.string();
                let raw = ashmem_open_region(pid, &rootfs, &mut self.st);
                let mut e = Enc::new();
                e.string(&raw);
                self.send_to(ci, MSG_RESP_OPEN_ASHMEM, &e.0);
            }
            MSG_REQ_ASHMEM_GET => {
                let key = d.string();
                let mut e = Enc::new();
                match self.st.ashmem.get(&key) {
                    Some(r) => {
                        e.bool(true);
                        e.u64(r.size);
                        e.string(&r.name);
                        e.u64(r.prot);
                    }
                    None => e.bool(false),
                }
                self.send_to(ci, MSG_RESP_ASHMEM_GET, &e.0);
            }
            MSG_REQ_VCRED => {
                let pid = d.i32();
                let mut e = Enc::new();
                match self.vcreds_g.get(&pid) {
                    Some(&(u, g)) => {
                        e.bool(true);
                        e.u32(u);
                        e.u32(g);
                    }
                    None => e.bool(false),
                }
                self.send_to(ci, MSG_RESP_VCRED, &e.0);
            }
            MSG_REQ_IGNITION_DUMP => {
                let pid = d.i32();
                let trigger = d.string();
                cap_clear();
                binder_ignition_dump(&self.st, pid, &trigger);
                let mut e = Enc::new();
                e.logs(&cap_take());
                self.send_to(ci, MSG_RESP_IGNITION_DUMP, &e.0);
            }
            MSG_REQ_WEDGE_CHAIN => {
                let leader = d.i32();
                let solo = d.i32();
                cap_clear();
                // Disjoint field borrows, as in the
                // WRITE_READ arm: the state goes to the
                // dump, the one connection serves its
                // reverse reads (the frozen write
                // streams of the arena's parked threads).
                let holder = {
                    let st = &mut self.st;
                    let conn = &mut self.conns[ci];
                    use std::os::unix::io::AsRawFd;
                    let cfd = conn.s.as_raw_fd();
                    let mut rd = |rpid: i32, addr: u64, len: usize| -> Option<Vec<u8>> {
                        let mut re = Enc::new();
                        re.i32(rpid);
                        re.u64(addr);
                        re.usize(len);
                        if !write_msg(&mut conn.s, MSG_REV_READ, &re.0) {
                            return None;
                        }
                        loop {
                            if let Some((k, p)) = conn.queue.pop_front() {
                                if k == MSG_REV_READ_RESP {
                                    return Dec::new(&p).opt_bytes();
                                }
                                return None;
                            }
                            if conn.dead {
                                return None;
                            }
                            let mut pfd = libc::pollfd {
                                fd: cfd,
                                events: libc::POLLIN,
                                revents: 0,
                            };
                            let n = unsafe { libc::poll(&mut pfd, 1, -1) };
                            if n < 0 {
                                if errno() == libc::EINTR {
                                    continue;
                                }
                                return None;
                            }
                            if n == 0 || pfd.revents == 0 {
                                continue;
                            }
                            use std::io::Read;
                            let mut buf = [0u8; 65536];
                            match conn.s.read(&mut buf) {
                                Ok(0) => {
                                    conn.dead = true;
                                    return None;
                                }
                                Ok(m) => {
                                    conn.inbuf.extend_from_slice(&buf[..m]);
                                    extract_frames(
                                        &mut conn.inbuf,
                                        &mut conn.queue,
                                        &mut conn.dead,
                                    );
                                }
                                Err(e)
                                    if e.kind() == std::io::ErrorKind::WouldBlock => {}
                                Err(_) => {
                                    conn.dead = true;
                                    return None;
                                }
                            }
                        }
                    };
                    binder_wedge_chain(st, leader, solo, &mut rd)
                };
                let (holder, servicers) = holder;
                let mut e = Enc::new();
                e.logs(&cap_take());
                e.i32(holder);
                e.u32(servicers.len() as u32);
                for (sa, sp) in &servicers {
                    e.string(sa);
                    e.i32(*sp);
                }
                self.send_to(ci, MSG_RESP_WEDGE_CHAIN, &e.0);
                // 0.9.141 (S6): the servicer faces ride
                // a broadcast so each servicer's owner
                // prints its tracer-side line; sent
                // after the reply so the chain dump's
                // own lines stay ahead in the log.
                if !servicers.is_empty() {
                    let ss_arena = self
                        .st
                        .thread_arena
                        .get(&leader)
                        .cloned()
                        .unwrap_or_default();
                    self.push_servicer_face(&ss_arena, &servicers);
                }
            }
            MSG_ONEWAY_PARK => {
                let pid = d.i32();
                let park = d.park();
                self.st.parked.insert(pid, park);
                // A delivery that finds nobody parked
                // pools its bytes in the arena's inbound
                // stream (binder_deliver), and the matching
                // wake is only computed at delivery time --
                // so a looper that parks AFTER the pool
                // sleeps beside pending work forever. The
                // 0.9.81 field froze exactly here:
                // servicemanager re-parked a breath after
                // system_server's addService pooled, and
                // nothing ever woke it. Registration is the
                // last word before sleeping, so re-check
                // the wake candidates for the parker's arena
                // here, the way a real driver's ioctl
                // re-checks its wait queue under the lock
                // before blocking.
                if let Some(arena) = self.st.thread_arena.get(&pid).cloned() {
                    for cand in binder_wake_candidates(&self.st, &arena) {
                        bsup!(
                            "binder: park of pid={pid} found pending work in {arena}; pushing wake for pid={cand}"
                        );
                        self.push_wake(cand);
                    }
                }
            }
            MSG_ONEWAY_FD_CACHE_PUT => {
                for (k, fd) in d.cache() {
                    // 0.9.134: a negative value is an
                    // eviction (a cached fd that failed
                    // verification tracer-side), not an
                    // entry.
                    if fd < 0 {
                        self.st.fd_cache.remove(&k);
                    } else {
                        self.st.fd_cache.insert(k, fd);
                    }
                }
            }
            MSG_ONEWAY_FD_STATS => {
                let dupped = d.u32();
                let verified = d.u32();
                let retried = d.u32();
                let retry_saved = d.u32();
                self.st.fd_fixup_dupped += dupped as u64;
                self.st.fd_fixup_verified += verified as u64;
                self.st.fd_fixup_retried += retried as u64;
                self.st.fd_fixup_retry_saved += retry_saved as u64;
            }
            MSG_ONEWAY_ISSUANCE_STATS => {
                let reads = d.u32();
                let differs = d.u32();
                self.st.issuance_reads += reads as u64;
                self.st.issuance_differs += differs as u64;
            }
            MSG_ONEWAY_FD_FAIL => {
                let arena = d.string();
                let data_va = d.u32();
                let fd_sender_pid = d.i32();
                let fd_sender_fd = d.i32();
                let nfail = d.u32();
                let disp = d.u8();
                let fail_pid = d.i32();
                let code = d.u32();
                let why = d.string();
                self.st.fd_fixup_failed += nfail as u64;
                // Disposition 0 (converted in the
                // tracer's batch) is counted above and
                // logged tracer-side; nothing is owed
                // here.
                let mut wake = 0;
                if disp == FD_DISP_FAIL_SENDER {
                    // The tracer dropped a transaction
                    // from its batch; fail its waiting
                    // sender from here, with the same
                    // push_to + wake the delivery-failure
                    // branch in binder_handle_txn uses.
                    if fail_pid > 0 {
                        if let Some(sarena) = self.st.thread_arena.get(&fail_pid).cloned() {
                            if let Some(bp) = self.st.procs.get_mut(&sarena) {
                                bp.push_to(fail_pid, &BR_FAILED_REPLY.to_le_bytes());
                            }
                            evidence_tag(
                                &mut self.st,
                                &sarena,
                                format!("failed-reply fd-fail code={code}"),
                            );
                            wake = fail_pid;
                        }
                    }
                    bsup!(
                        "binder: fd-fixup-convert txn sender failed pid={fail_pid} code={code} arena={arena} data_va=0x{data_va:x} fixups={nfail} why={why}"
                    );
                } else if disp == FD_DISP_QUEUED {
                    // The fixups were settled by a
                    // sibling thread's batch, so the
                    // owning delivery never passed through
                    // the reporting tracer's hands: search
                    // this arena's queues for it.
                    let mut outcome = FdConvert::NotFound;
                    if let Some(bp) = self.st.procs.get_mut(&arena) {
                        for q in bp.queues.values_mut() {
                            let c = fd_convert_in_stream(q, data_va);
                            if !matches!(c, FdConvert::NotFound) {
                                outcome = c;
                                break;
                            }
                        }
                        if matches!(outcome, FdConvert::NotFound) {
                            let c = fd_convert_in_stream(&mut bp.inbound, data_va);
                            if !matches!(c, FdConvert::NotFound) {
                                outcome = c;
                            }
                        }
                    }
                    match outcome {
                        FdConvert::Reply => {
                            bsup!(
                                "binder: fd-fixup-convert queued arena={arena} data_va=0x{data_va:x} cmd=BR_REPLY -> FAILED_REPLY fixups={nfail} why={why}"
                            );
                        }
                        FdConvert::Txn {
                            fail_pid: fp,
                            code: c2,
                        } => {
                            if fp > 0 {
                                if let Some(sarena) = self.st.thread_arena.get(&fp).cloned() {
                                    if let Some(bp) = self.st.procs.get_mut(&sarena) {
                                        bp.push_to(fp, &BR_FAILED_REPLY.to_le_bytes());
                                    }
                                    evidence_tag(
                                        &mut self.st,
                                        &sarena,
                                        format!("failed-reply fd-fail code={c2}"),
                                    );
                                    wake = fp;
                                }
                            }
                            bsup!(
                                "binder: fd-fixup-convert queued arena={arena} data_va=0x{data_va:x} cmd=BR_TRANSACTION code={c2} -> dropped; failing sender pid={fp} fixups={nfail} why={why}"
                            );
                        }
                        FdConvert::NotFound => {
                            bsup!(
                                "binder: fd-fixup-fail-late arena={arena} data_va=0x{data_va:x} sender_pid={fd_sender_pid} sender_fd={fd_sender_fd} fixups={nfail} why={why} (owning command in no queue; delivery already consumed, parcel word left unwritten)"
                            );
                        }
                    }
                }
                if wake > 0 {
                    self.push_wake(wake);
                }
            }
            MSG_ONEWAY_PARK_REMOVE => {
                let pid = d.i32();
                self.st.parked.remove(&pid);
            }
            MSG_ONEWAY_THREAD_ARENA => {
                let pid = d.i32();
                let arena = d.string();
                self.st.thread_arena.insert(pid, arena);
            }
            MSG_ONEWAY_ARENA_REGISTER => {
                let pid = d.i32();
                let arena = d.string();
                let base = d.u32();
                let maplen = d.u32();
                if let Some(bp) = self.st.procs.get_mut(&arena) {
                    bp.base.insert(pid, base);
                    bp.maplen.insert(pid, maplen);
                }
            }
            MSG_ONEWAY_THREAD_EXIT_IOCTL => {
                let pid = d.i32();
                let arena = d.string();
                if let Some(bp) = self.st.procs.get_mut(&arena) {
                    bp.loopers.remove(&pid);
                }
                self.st.parked.remove(&pid);
            }
            MSG_ONEWAY_ASHMEM_SET_NAME => {
                let key = d.string();
                let name = d.string();
                self.st
                    .ashmem
                    .entry(key)
                    .or_insert_with(default_ashmem_rec)
                    .name = name;
            }
            MSG_ONEWAY_ASHMEM_SET_SIZE => {
                let key = d.string();
                let size = d.u64();
                self.st
                    .ashmem
                    .entry(key.clone())
                    .or_insert_with(default_ashmem_rec)
                    .size = size;
                if let Ok(f) = std::fs::OpenOptions::new().write(true).open(&key) {
                    let _ = f.set_len(size);
                }
            }
            MSG_ONEWAY_ASHMEM_SET_PROT => {
                let key = d.string();
                let prot = d.u64();
                self.st.ashmem.entry(key).or_insert_with(default_ashmem_rec).prot = prot;
            }
            MSG_ONEWAY_REGISTER_PID => {
                let pid = d.i32();
                let creds = (d.u32(), d.u32());
                self.routes.insert(pid, ci);
                self.vcreds_g.insert(pid, creds);
            }
            MSG_ONEWAY_UNREGISTER_PID => {
                let pid = d.i32();
                // Only the current owner may drop the
                // route: a stale unregister (W0 taking a
                // pid back after a failed handoff) must
                // not clobber the new owner's entry --
                // but W0's take-back unregister comes
                // AFTER the worker's own failure
                // unregister cleared it, so accept both
                // "owned by sender" and "no route".
                match self.routes.get(&pid) {
                    Some(&owner) if owner == ci => {
                        self.routes.remove(&pid);
                        self.vcreds_g.remove(&pid);
                    }
                    None => {
                        self.vcreds_g.remove(&pid);
                    }
                    _ => {}
                }
            }
            MSG_ONEWAY_VCRED_PUBLISH => {
                let pid = d.i32();
                let creds = (d.u32(), d.u32());
                self.vcreds_g.insert(pid, creds);
            }
            MSG_ONEWAY_WAKE_ROUTE => {
                let pid = d.i32();
                self.push_wake(pid);
            }
            MSG_ONEWAY_DUMP_REQ => {
                self.push_dump_stacks();
            }
            MSG_ONEWAY_SHIELD_COOKIE_SUSPECT => {
                let pid = d.i32();
                let ptr = d.u32();
                let cookie = d.u32();
                let why = d.string();
                self.st.shield_cookie_suspects += 1;
                // REF pairs in a read batch name nodes
                // the reader's own arena owns (notices
                // are only ever queued to the owner), so
                // (owner, ptr, cookie) resolves the node
                // exactly the way node_for_local keyed
                // it; prefer the live record if a dead
                // one happens to share the tuple.
                let node = self.st.thread_arena.get(&pid).and_then(|owner| {
                    let st = &self.st;
                    st.nodes
                        .iter()
                        .position(|n| {
                            !n.dead && n.owner == *owner && n.ptr == ptr && n.cookie == cookie
                        })
                        .or_else(|| {
                            st.nodes.iter().position(|n| {
                                n.owner == *owner && n.ptr == ptr && n.cookie == cookie
                            })
                        })
                });
                let node = node.map(|i| i.to_string()).unwrap_or_else(|| "-".to_string());
                bsup!(
                    "binder: shield-cookie suspect node={} ptr=0x{:x} cookie=0x{:x} why={}",
                    node, ptr, cookie, why
                );
            }
            MSG_ONEWAY_HANDOFF => {
                let pid = d.i32();
                let twid = d.u8();
                let vcwd = d.string();
                let compat = d.bool();
                let sigmask = d.u32();
                let creds = (d.u32(), d.u32());
                let root = d.bool();
                // The verdict must find its way back to
                // the offering tracer, whoever that is.
                self.handoff_from.insert(pid, ci);
                match self.conn_by_wid(twid) {
                    Some(tci) => {
                        self.routes.insert(pid, tci);
                        self.vcreds_g.insert(pid, creds);
                        let mut e = Enc::new();
                        e.i32(pid);
                        e.string(&vcwd);
                        e.bool(compat);
                        e.u32(sigmask);
                        e.u32(creds.0);
                        e.u32(creds.1);
                        e.bool(root);
                        self.send_to(tci, MSG_PUSH_ADOPT, &e.0);
                    }
                    None => {
                        // No such worker (its fork
                        // failed): tell the offering
                        // tracer at once so it takes the
                        // tracee back instead of waiting
                        // out the ack timeout.
                        self.handoff_from.remove(&pid);
                        self.push_adopt_ack(ci, pid, false);
                    }
                }
            }
            MSG_ONEWAY_ADOPT_ACK => {
                let pid = d.i32();
                let ok = d.bool();
                // Normally the recorded offering tracer;
                // W0 is the fallback for an ack whose
                // offer was never recorded.
                let dest = self.handoff_from.remove(&pid).or(self.w0);
                if let Some(ci) = dest {
                    self.push_adopt_ack(ci, pid, ok);
                }
            }
            _ => {}
        }
    }
}

/// The coordinator process body: bind the listening
/// socket (a stale file from a previous run is
/// unlinked first), accept tracer connections, and
/// serve frames one at a time until W0 goes away.
fn coordinator_main(sock_path: &str) -> ! {
    use std::os::unix::io::AsRawFd;
    let _ = std::fs::remove_file(sock_path);
    let listener = match std::os::unix::net::UnixListener::bind(sock_path) {
        Ok(l) => l,
        Err(_) => std::process::exit(1),
    };
    let _ = listener.set_nonblocking(true);
    let lfd = listener.as_raw_fd();
    let mut srv = CoordServer {
        conns: Vec::new(),
        st: BinderState::default(),
        routes: HashMap::new(),
        vcreds_g: HashMap::new(),
        w0: None,
        handoff_from: HashMap::new(),
    };
    loop {
        let mut pfds: Vec<libc::pollfd> = Vec::with_capacity(srv.conns.len() + 1);
        pfds.push(libc::pollfd {
            fd: lfd,
            events: libc::POLLIN,
            revents: 0,
        });
        let mut idx: Vec<usize> = Vec::new();
        for (i, c) in srv.conns.iter().enumerate() {
            if !c.dead {
                idx.push(i);
                pfds.push(libc::pollfd {
                    fd: c.s.as_raw_fd(),
                    events: libc::POLLIN,
                    revents: 0,
                });
            }
        }
        let n = unsafe { libc::poll(pfds.as_mut_ptr(), pfds.len() as libc::nfds_t, -1) };
        if n > 0 {
            if pfds[0].revents & libc::POLLIN != 0 {
                if let Ok((s, _)) = listener.accept() {
                    srv.conns.push(CConn {
                        s,
                        inbuf: Vec::new(),
                        queue: std::collections::VecDeque::new(),
                        wid: None,
                        dead: false,
                    });
                }
            }
            for (j, &ci) in idx.iter().enumerate() {
                let rev = pfds[j + 1].revents;
                if rev != 0 {
                    if rev & libc::POLLIN != 0 {
                        srv.fill(ci);
                        srv.extract(ci);
                    } else {
                        srv.conns[ci].dead = true;
                    }
                    if srv.conns[ci].dead {
                        srv.conn_died(ci);
                    }
                }
            }
        }
        // Drain every queued frame, one at a time;
        // handling a request never interleaves with
        // another frame, so decisions stay atomic.
        let mut progress = true;
        while progress {
            progress = false;
            for ci in 0..srv.conns.len() {
                if srv.conns[ci].dead {
                    continue;
                }
                if let Some((k, p)) = srv.conns[ci].queue.pop_front() {
                    progress = true;
                    srv.handle(ci, k, &p);
                }
            }
        }
    }
}


/// One tracer-side effect the binder driver decided on
/// (multi-process split, spec stage S1a). The binder
/// family used to perform these inline while it decided;
/// it now only returns them, and the entry-stop caller
/// executes them in order (exec_binder_actions). This is
/// the seam the coordinator IPC later sits on: decisions
/// travel as data, execution stays with whoever holds
/// the tracee's ptrace stop. Contents and order are
/// exactly the old inline effects, so behaviour is
/// unchanged.
enum BAction {
    /// write_mem(pid, addr, bytes); result ignored,
    /// as it was at every old inline site.
    WriteMem { addr: u64, bytes: Vec<u8> },
    /// skip_syscall(pid, regs, pend, value).
    SkipSyscall(i64),
    /// st.parked.insert(pid, park): this call parks.
    Park { pid: i32, park: ParkedIoctl },
    /// pend.binder_parked = true (the caller keys its
    /// no-continue decision off the flag, as before).
    MarkBinderParked,
    /// A parked pid has work waiting. The caller appends
    /// it to its wakes list -- deduplicated there, where
    /// binder_maybe_wake used to deduplicate against the
    /// same vec -- and completes it after the entry stop,
    /// exactly as before.
    Wake(i32),
    /// Settle one arena's fd fixups inline, riding the
    /// current call's entry stop (resolve_fd_fixups_core);
    /// when rides were needed, the fake result is applied
    /// to the regs and pend.applied is set -- the old
    /// inline tail of binder_write_read, verbatim. Since
    /// S1b the resolver's fd cache lives with the
    /// coordinator: `cache` carries the entries these
    /// fixups consult, and entries the resolution learns
    /// are sent back before anything else can read them.
    ResolveFdFixupsInline {
        arena: String,
        fixups: Vec<FdFixup>,
        cache: Vec<(CacheKey, i32)>,
    },
}

/// Execute, in order, the effects a binder decision
/// returned. Runs at the entry stop that made the
/// decision, with that stop's regs/pend in hand -- the
/// same place and order the family used to act in.
fn exec_binder_actions(
    pid: i32,
    compat: bool,
    regs: &mut Regs,
    pend: &mut Pending,
    coord: &mut CoordClient,
    actions: Vec<BAction>,
    wakes: &mut Vec<i32>,
) -> Option<(u32, u32)> {
    // Pre-filter any batch WriteMem through
    // shield_live_pairs BEFORE the actions run, fixing
    // the paired writeback struct (24B, batch length at
    // +16) to the filtered length -- a stale read_consumed
    // would make the guest read past the batch into old
    // buffer content. The identified fill is also the
    // thread's last_binder_read for FATAL minbuf.
    let mut actions = actions;
    let mut fill: Option<(u32, u32)> = None;
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..actions.len() {
        let ilen = match &actions[i] {
            BAction::WriteMem { bytes, .. } if ref_batch_qualifies(bytes) => {
                bytes.len()
            }
            _ => continue,
        };
        for j in 0..actions.len() {
            if i == j {
                continue;
            }
            if let BAction::WriteMem { bytes, .. } = &actions[j] {
                if bytes.len() == 24
                    && u32::from_le_bytes(bytes[16..20].try_into().unwrap())
                        as usize
                        == ilen
                {
                    pairs.push((i, j));
                }
            }
        }
    }
    for &(i, j) in &pairs {
        let (baddr, newlen) = match &mut actions[i] {
            BAction::WriteMem { addr, bytes } => {
                let filtered = shield_live_pairs(pid, std::mem::take(bytes), coord);
                *bytes = filtered;
                (*addr, bytes.len() as u32)
            }
            _ => continue,
        };
        fill = Some((baddr as u32, newlen));
        if let BAction::WriteMem { bytes, .. } = &mut actions[j] {
            bytes[16..20].copy_from_slice(&newlen.to_le_bytes());
        }
    }
    // 0.9.134: the identified fill's action indices,
    // remembered so a ResolveFdFixupsInline later in the
    // list can convert a failed fixup's delivery inside
    // the batch it rode in on (see that arm).
    let batch_idx = pairs.first().map(|&(i, _)| i);
    let wb_idx = pairs.first().map(|&(_, j)| j);
    let mut batch_snap: Option<(u64, Vec<u8>)> = None;
    let mut wb_addr: Option<u64> = None;
    for (ai, a) in actions.into_iter().enumerate() {
        match a {
            BAction::WriteMem { addr, bytes } => {
                if Some(ai) == batch_idx {
                    batch_snap = Some((addr, bytes.clone()));
                }
                if Some(ai) == wb_idx {
                    wb_addr = Some(addr);
                }
                let _ = write_mem(pid, addr, &bytes);
            }
            BAction::SkipSyscall(v) => skip_syscall(pid, regs, pend, v),
            BAction::Park { pid: p, park } => {
                // The parked record lives with the
                // coordinator now; the channel is ordered
                // and this process is single-threaded, so
                // the insert lands before any later request
                // can observe its absence -- the same
                // ordering the inline insert had.
                coord.oneway_park(p, &park);
            }
            BAction::MarkBinderParked => pend.binder_parked = true,
            BAction::Wake(w) => {
                if !wakes.contains(&w) {
                    wakes.push(w);
                }
            }
            BAction::ResolveFdFixupsInline { arena, fixups, cache } => {
                let seed: HashMap<CacheKey, i32> = cache.iter().cloned().collect();
                let mut cmap: HashMap<CacheKey, i32> = cache.into_iter().collect();
                // 0.9.141 (S3.3): the inline path holds
                // no process table to read a sender
                // face from; the field renders remote.
                let res = resolve_fd_fixups_core(
                    pid,
                    compat,
                    &mut cmap,
                    &arena,
                    &fixups,
                    regs,
                    &|_| "-/remote".to_string(),
                );
                // Learned entries ride back as inserts;
                // evictions (0.9.134) as -1 removals.
                let mut put = learned_entries(&cmap, &seed);
                for k in &res.evictions {
                    put.push((k.clone(), -1));
                }
                coord.oneway_fd_cache_put(&put);
                if res.dupped > 0 || res.verified > 0 || res.retried > 0 || res.retry_saved > 0 {
                    coord.oneway_fd_stats(res.dupped, res.verified, res.retried, res.retry_saved);
                }
                if !res.failed.is_empty() {
                    // 0.9.134 (fix (a)): convert the
                    // failed deliveries inside the batch
                    // this decision just wrote into the
                    // guest. The guest has not run yet --
                    // the whole action list executes at
                    // its entry stop -- so repair the
                    // read buffer and the writeback's
                    // read_consumed in place, and the
                    // guest consumes the converted stream,
                    // never the failed parcels. With no
                    // identified batch the conversion
                    // finds nothing locally and every
                    // failure is handed to the
                    // coordinator's queue search.
                    let mut snap: Vec<u8> = batch_snap
                        .as_ref()
                        .map(|(_, b)| b.clone())
                        .unwrap_or_default();
                    if fd_fail_convert_local(coord, &arena, pid, &mut snap, &res.failed) {
                        if let (Some((baddr, _)), Some(wb)) = (&batch_snap, &wb_addr) {
                            let _ = write_mem(pid, *baddr, &snap);
                            let _ = write_mem(
                                pid,
                                wb + 16,
                                &(snap.len() as u32).to_le_bytes(),
                            );
                            fill = Some((*baddr as u32, snap.len() as u32));
                        }
                    }
                }
                if res.rides > 0 {
                    regs.set_retval(0);
                    if set_regs(pid, regs) {
                        pend.applied = true;
                    }
                }
                // 0.9.136: the settle-before-wake audit
                // mark, inline path: resolution and any
                // failure conversion (with its in-place
                // read-buffer repair above) are complete
                // inside this entry stop's action list,
                // before the handler continues the tracee.
                sup!(
                    "binder: fd-fixup-settled recv_pid={pid} path=inline fixups={} failed={}",
                    fixups.len(),
                    res.failed.len()
                );
            }
        }
    }
    fill
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
        bsup!(
            "binder: obj BINDER node#{} -> owner arena {} ptr=0x{:x} cookie=0x{:x} weak={}",
            node, to, nptr, ncookie, weak
        );
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
    actions: &mut Vec<BAction>,
) {
    let (owner, nptr, ncookie, dead) = {
        let n = &st.nodes[node];
        (n.owner.clone(), n.ptr, n.cookie, n.dead)
    };
    if dead || owner == to {
        return;
    }
    let notified_key = (node, to.to_string());
    if st.ref_notified.contains_key(&notified_key) {
        return;
    }
    st.ref_notified.insert(notified_key, weak);
    st.notify_queued += 1;
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
    binder_maybe_wake(st, &owner, actions);
    st.note("ref notice queued to object owner");
}

/// Compact dump of a parcel's object slots for telemetry:
/// one "off: type +8 +12" triple per offsets entry.
fn slot_dump(data: &[u8], offs: &[u8]) -> String {
    let mut s = String::new();
    let mut i = 0;
    while i + 4 <= offs.len() {
        let off = u32_at(offs, i) as usize;
        i += 4;
        if off + 16 > data.len() {
            s.push_str(&format!(" @{off}:OOB"));
            continue;
        }
        s.push_str(&format!(
            " @{}: t=0x{:08x} b=0x{:x} k=0x{:x}",
            off,
            u32_at(data, off),
            u32_at(data, off + 8),
            u32_at(data, off + 12)
        ));
    }
    s
}

/// First `n` bytes of `b` as lowercase hex (all of `b`
/// when shorter); 0.9.124 reply-pair dump helper.
fn hex_head(b: &[u8], n: usize) -> String {
    let mut s = String::with_capacity(b.len().min(n) * 2);
    for byte in b.iter().take(n) {
        s.push_str(&format!("{byte:02x}"));
    }
    s
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
    actions: &mut Vec<BAction>,
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
                binder_notify_ref(st, node, to, ty == OBJ_WEAK_BINDER, actions);
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
                        binder_notify_ref(st, n, to, ty == OBJ_WEAK_HANDLE, actions);
                    }
                    None => bsup!(
                        "binder: unknown handle 0x{ptr:x} in parcel {from} -> {to}; left untranslated"
                    ),
                }
            }
            OBJ_FD => {
                fd_fixups.push((off + 8, ptr as i32));
            }
            _ => {
                bsup!("binder: untranslated parcel object type=0x{ty:08x} ptr=0x{ptr:x} (passed through)");
            }
        }
    }
    out
}

/// 0.9.133 fd-object telemetry (log only; see
/// s9-132-verify Q4 item 1): photograph every FD-type
/// flat object a translation just carried, on both
/// the transaction and the reply path. The field's
/// biggest ignition family is now systemui dying in
/// InputQueue.registerInputChannel after WMS replies,
/// and an input channel crosses as exactly one of
/// these objects; until now the log named FD fixups
/// only at wake-time resolution, never at the parcel
/// that carried them. For each fixup this prints the
/// recipient (arena, and the waiter/sender pid where
/// the site knows it), the call code, the object's
/// offset in the parcel, the fd word before
/// translation (the sender's guest fd -- translation
/// leaves the word untouched; the receiver-side
/// patch happens later, in resolve_fd_fixups, whose
/// own log line names the resulting fd) and after,
/// read back from the translated bytes, plus the
/// host-side standing of the sender's fd at this
/// moment: the /proc/<sender>/fd/<n> link target
/// (socket / pipe / file / ashmem path), or the errno
/// when the link cannot be read -- the supervisor
/// cannot fcntl another process's descriptor, and
/// the proc link is the read-only equivalent check.
/// FD objects are rare in this traffic (a few dozen
/// per run), so every one prints. Nothing here feeds
/// translation, the fixup list or delivery.
fn fd_obj_dump(
    site: &str,
    from_pid: i32,
    to_arena: &str,
    to_pid: Option<i32>,
    code: u32,
    out: &[u8],
    fixups: &[(usize, i32)],
) {
    for &(rel, gfd) in fixups {
        let obj_off = rel.saturating_sub(8);
        let post = if rel + 4 <= out.len() {
            u32_at(out, rel)
        } else {
            gfd as u32
        };
        let host = match std::fs::read_link(format!("/proc/{from_pid}/fd/{gfd}")) {
            Ok(t) => format!("ok target={}", t.display()),
            Err(e) => match e.raw_os_error() {
                Some(c) => format!("invalid errno={c}"),
                None => format!("invalid kind={:?}", e.kind()),
            },
        };
        let to_pid_s = to_pid
            .map(|p| p.to_string())
            .unwrap_or_else(|| "-".to_string());
        bsup!(
            "binder: fd-obj dump site={site} from_pid={from_pid} to={to_arena} to_pid={to_pid_s} code={code} off={obj_off} guest_fd={gfd} word_pre={gfd} word_post={post} host={host}"
        );
    }
}

/// Copy a translated parcel into the target arena and queue
/// the BR_TRANSACTION / BR_REPLY carrying it. On failure the
/// Err names the exact stage, so a dead delivery explains
/// itself in the log instead of hiding behind a bool. On
/// success the Ok carries the arena allocation offset the
/// parcel landed at -- the slot identity the 0.9.127
/// big-reply / big-txn delivery dumps print; callers that
/// do not log it simply ignore the value, as they ignored
/// the unit Ok before.
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
) -> Result<u32, &'static str> {
    let total = ((data.len() as u32 + 3) & !3) + ((offs.len() as u32 + 3) & !3);
    let Some(off) = st.alloc(target, total.max(8)) else {
        return Err("alloc failed (no such arena state, or out of mapped space)");
    };
    // 0.9.134: the base is read before the fixups are
    // queued so each fixup can carry the parcel's guest
    // VA (data_va, see FdFixup). Same value the delivery
    // below names in its transaction words; the error
    // behaviour is unchanged (the lookup simply moved
    // ahead of the fixup queueing, which no failure path
    // could observe: a missing arena state or base fails
    // the delivery either way, before any byte is
    // queued).
    let base = {
        let Some(bp) = st.procs.get(target) else {
            return Err("arena state vanished after alloc");
        };
        let Some(&base) = bp.base.values().next() else {
            return Err("target arena has no recorded mmap base");
        };
        base
    };
    for (rel, sfd) in fd_fixups {
        st.fd_pending
            .entry(target.to_string())
            .or_default()
            .push(FdFixup {
                file_off: off as u64 + *rel as u64,
                sender_pid,
                sender_fd: *sfd,
                data_va: base + off,
            });
    }
    let Some(bp) = st.procs.get_mut(target) else {
        return Err("arena state vanished after alloc");
    };
    if bp.file.write_all_at(data, off as u64).is_err()
        || bp.file.write_all_at(offs, (off + ((data.len() as u32 + 3) & !3)) as u64).is_err()
    {
        return Err("arena file write failed");
    }
    let wa_rec: Option<WriteAuditRec>;
    {
        // 0.9.99: fingerprint the parcel image exactly as
        // it now lies in the arena file, so dump_mgr_read
        // can call out any in-flight rewrite when the
        // batch carrying this parcel is handed over.
        let mut img = vec![0u8; total as usize];
        img[..data.len()].copy_from_slice(data);
        let offs_at = ((data.len() as u32 + 3) & !3) as usize;
        img[offs_at..offs_at + offs.len()].copy_from_slice(offs);
        let mut mask: Vec<u32> = fd_fixups.iter().map(|(rel, _)| (*rel / 4) as u32).collect();
        mask.sort_unstable();
        mask.dedup();
        for &w in &mask {
            let at = (w as usize) * 4;
            if at + 4 <= img.len() {
                img[at..at + 4].copy_from_slice(&[0, 0, 0, 0]);
            }
        }
        let head: Vec<u32> = (0..8)
            .filter(|&i| (i + 1) * 4 <= img.len())
            .map(|i| u32_at(&img, i * 4))
            .collect();
        let crc = crc32(&img);
        bp.parcels.insert(
            off,
            ParcelPrint {
                crc,
                total,
                mask,
                head,
                from_pid: sender_pid,
                code,
                target_ptr,
                txn_cookie: cookie,
            },
        );
        // 0.9.132: keep this delivery write in the
        // write-overlap audit's table (record only; the
        // write above is untouched). The record is
        // pushed after the borrow of bp ends, just
        // before the return below.
        wa_rec = Some(WriteAuditRec {
            arena: target.to_string(),
            // 0.9.133: guest VA interval, not the file
            // offset -- base here is the very base the
            // delivery's txn words name (base + off is
            // where the parcel lives in the receiver).
            va: base as u64 + off as u64,
            len: total,
            head: img[..img.len().min(64)].to_vec(),
        });
    }
    if !offs.is_empty() {
        let bases: Vec<String> = bp
            .base
            .iter()
            .map(|(p, b)| format!("{p}=0x{b:x}"))
            .collect();
        bsup!(
            "binder: deliver to={target} br={br_cmd} code={code} from_pid={sender_pid} base=0x{base:x} bases=[{}] slots{}",
            bases.join(","),
            slot_dump(data, offs)
        );
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
            // Kernel ordering: the reference notices for
            // objects carried in the request (BR_INCREFS /
            // BR_ACQUIRE) were queued when the peer received
            // it, before the peer produced this reply, and
            // the real driver returns them in the same read,
            // ahead of the BR_REPLY. Our two-queue split let
            // the reply overtake them: the caller completed
            // its transaction, dropped the last strong ref
            // of a temporary service object and freed it,
            // and the pending BR_ACQUIRE then incStrong'd
            // recycled heap (mediaserver's addService
            // temporaries died exactly this way: mRefs read
            // back as a small integer). Drain the shared
            // stream into the waiting thread's queue first.
            if !bp.inbound.is_empty() {
                let pending = std::mem::take(&mut bp.inbound);
                bp.push_to(pid, &pending);
                bsup!("binder: flushed pending inbound ahead of reply to pid={pid}");
            }
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
                    bsup!("binder: txn for {target} landed in parked looper pid={p}'s queue");
                    // Same ordering rule as the reply path:
                    // whatever the shared stream already
                    // holds for this arena was queued before
                    // this transaction and must be read first.
                    if !bp.inbound.is_empty() {
                        let pending = std::mem::take(&mut bp.inbound);
                        bp.push_to(p, &pending);
                    }
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
                    bsup!(
                        "binder: txn for {target} pooled in inbound (parked: [{}])",
                        parked_here.join(", ")
                    );
                    bp.inbound.extend_from_slice(&br_cmd.to_le_bytes());
                    bp.inbound.extend_from_slice(&txn);
                }
            }
        }
    }
    // 0.9.132: file this delivery in the write-overlap
    // audit table (see WriteAuditRec). Global FIFO with
    // a hard cap; the oldest records fall off first.
    if let Some(rec) = wa_rec {
        st.write_audit.push_back(rec);
        while st.write_audit.len() > WRITE_AUDIT_CAP {
            st.write_audit.pop_front();
        }
    }
    Ok(off)
}

/// Which parked threads of `arena` have work they may
/// read. Pure decision, shared by the action-returning
/// family (binder_maybe_wake) and by binder_on_proc_exit
/// (binder_maybe_wake_pids), whose caller still collects
/// plain pids and completes them on the spot.
fn binder_wake_candidates(st: &BinderState, arena: &str) -> Vec<i32> {
    let Some(bp) = st.procs.get(arena) else {
        return Vec::new();
    };
    if bp.inbound.is_empty() && bp.queues.values().all(|q| q.is_empty()) {
        return Vec::new();
    }
    // Wake exactly the parked threads that have bytes they
    // may read: a thread with addressed bytes, or a looper
    // while the inbound stream is non-empty. (The old code
    // woke the first parked thread it found and handed it
    // the whole shared queue, whatever the bytes were for.)
    let mut out = Vec::new();
    for (pid, park) in &st.parked {
        if park.read_size == 0 {
            continue;
        }
        if st.thread_arena.get(pid).map(|a| a != arena).unwrap_or(true) {
            continue;
        }
        let own = bp.queues.get(pid).map_or(0, |q| q.len());
        if own > 0 || (!bp.inbound.is_empty() && bp.loopers.contains(pid)) {
            out.push(*pid);
        }
    }
    out
}

/// If the target arena has parked readers with work,
/// queue their wakes as actions (the caller executes
/// them after the entry stop, as it always did; the
/// executor deduplicates against the wakes vec, where
/// the old inline version deduplicated too).
fn binder_maybe_wake(st: &BinderState, arena: &str, actions: &mut Vec<BAction>) {
    for pid in binder_wake_candidates(st, arena) {
        actions.push(BAction::Wake(pid));
    }
}

/// binder_maybe_wake for binder_on_proc_exit: same
/// candidates, same dedup against the caller's vec
/// the old shared implementation applied.
fn binder_maybe_wake_pids(st: &BinderState, arena: &str, wakes: &mut Vec<i32>) {
    for pid in binder_wake_candidates(st, arena) {
        if !wakes.contains(&pid) {
            wakes.push(pid);
        }
    }
}

/// Process one binder WRITE_READ stream's write side.
/// `rd` is the decision's guest-memory reader: inline
/// it was read_mem_vec; since S1b it is the reverse
/// read channel to the tracer (see binder_write_read).
#[allow(clippy::too_many_arguments)]
/// 0.9.135 telemetry: the command skeleton of one
/// guest write stream -- each BC command's short name
/// and total length in stream order, e.g.
/// "REPLY(44) FREE_BUFFER(8)". Walks with exactly the
/// advance rules binder_process_stream uses and stops
/// where it would stop: an unknown command ends the
/// skeleton (its length is unknowable) and a
/// truncated tail is marked. Names and lengths only;
/// reads nothing out of the guest, decides nothing.
fn batch_skeleton(stream: &[u8]) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut cur = 0usize;
    while cur + 4 <= stream.len() {
        let cmd = u32_at(stream, cur);
        let (name, adv): (&str, usize) = match cmd {
            BC_ENTER_LOOPER => ("ENTER_LOOPER", 4),
            BC_REGISTER_LOOPER => ("REGISTER_LOOPER", 4),
            BC_EXIT_LOOPER => ("EXIT_LOOPER", 4),
            BC_FREE_BUFFER => ("FREE_BUFFER", 8),
            BC_INCREFS => ("INCREFS", 8),
            BC_ACQUIRE => ("ACQUIRE", 8),
            BC_RELEASE => ("RELEASE", 8),
            BC_DECREFS => ("DECREFS", 8),
            BC_INCREFS_DONE => ("INCREFS_DONE", 12),
            BC_ACQUIRE_DONE => ("ACQUIRE_DONE", 12),
            BC_ATTEMPT_ACQUIRE => ("ATTEMPT_ACQUIRE", 12),
            BC_REQUEST_DEATH_NOTIFICATION => ("REQ_DEATH", 12),
            BC_CLEAR_DEATH_NOTIFICATION => ("CLEAR_DEATH", 12),
            BC_DEAD_BINDER_DONE => ("DEAD_BINDER_DONE", 8),
            BC_TRANSACTION => ("TRANSACTION", 44),
            BC_REPLY => ("REPLY", 44),
            other => {
                parts.push(format!("UNKNOWN(0x{other:08x})"));
                return parts.join(" ");
            }
        };
        if cur + adv > stream.len() {
            parts.push(format!("{name}(trunc)"));
            return parts.join(" ");
        }
        parts.push(format!("{name}({adv})"));
        cur += adv;
    }
    parts.join(" ")
}

fn binder_process_stream<R: FnMut(i32, u64, usize) -> Option<Vec<u8>>>(
    pid: i32,
    arena: &str,
    stream: &[u8],
    st: &mut BinderState,
    veuid: u32,
    rd: &mut R,
    actions: &mut Vec<BAction>,
    notes: &mut Vec<String>,
) {
    // 0.9.135 telemetry: photograph this write batch's
    // command skeleton for the reply-pop descriptor
    // dump (see BinderState::cur_batch_skel). The walk
    // below is untouched; the skeleton is cleared on
    // the way out so no later path can quote a stale
    // batch.
    st.cur_batch_skel = batch_skeleton(stream);
    st.cur_batch_reply_ord = 0;
    let mut reply_ord = 0usize;
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
                    // Path 1 (unchanged): the freeing thread's
                    // own registered base.
                    let mut freed = false;
                    if let Some(&base) = bp.base.get(&pid) {
                        let off = ptr.wrapping_sub(base);
                        if let Some(sz) = bp.used.remove(&off) {
                            bp.free.push((off, sz));
                            if bp.parcels.remove(&off).is_some() {
                                bp.free_parcel_hit += 1;
                            }
                            bp.free_hit += 1;
                            freed = true;
                        }
                    }
                    if !freed {
                        // Rescue (0.9.119): a buffer can be
                        // freed by a thread whose own base was
                        // never registered, or whose offset
                        // misses under its own base; before
                        // this, such a free was dropped whole
                        // and the parcel leaked for the life
                        // of the arena. Try every distinct
                        // registered base of this arena: the
                        // buffer lives at exactly one offset
                        // in the used table.
                        let mut bases: Vec<u32> =
                            bp.base.values().copied().collect();
                        bases.sort_unstable();
                        bases.dedup();
                        for base in bases {
                            let Some(off) = ptr.checked_sub(base) else {
                                continue;
                            };
                            if let Some(sz) = bp.used.remove(&off) {
                                bp.free.push((off, sz));
                                if bp.parcels.remove(&off).is_some() {
                                    bp.free_parcel_hit += 1;
                                }
                                bp.free_hit += 1;
                                bp.free_rescued += 1;
                                freed = true;
                                break;
                            }
                        }
                    }
                    if !freed {
                        if bp.base.contains_key(&pid) {
                            bp.free_stale += 1;
                        } else {
                            bp.free_nobase += 1;
                            bp.free_miss += 1;
                            bsup!(
                                "binder: free-buffer miss arena={arena} pid={pid} ptr=0x{ptr:x}"
                            );
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
                // 0.9.135 telemetry: name this reply's
                // ordinal inside its batch for the
                // descriptor dump (see batch_skeleton).
                if cmd == BC_REPLY {
                    st.cur_batch_reply_ord = reply_ord;
                    reply_ord += 1;
                }
                binder_handle_txn(pid, arena, cmd == BC_REPLY, &txn, st, veuid, rd, actions, notes);
            }
            other => {
                notes.push(format!("unknown BC {other:#010x}; stream parse stopped"));
                break;
            }
        }
    }
    // 0.9.135: the batch photograph is spent with the
    // walk (see the note at the top of this function).
    st.cur_batch_skel.clear();
    st.cur_batch_reply_ord = 0;
}

#[allow(clippy::too_many_arguments)]
/// 0.9.127 telemetry helper: the (ptr, cookie) of the
/// node a reply wait's claim key names -- the wait's
/// recorded target handle resolved in the sender's own
/// handle table, exactly as binder_claim_fills resolves
/// it (handle 0 names the context manager node, which
/// lives outside every handle table). Falls back to the
/// wait's raw (target_handle, cookie) words when the
/// handle no longer resolves. Read-only; log use only.
fn claim_key_node(st: &BinderState, w: &ReplyWait) -> (u32, u32) {
    let idx = if w.target_handle == 0 {
        st.mgr_node
    } else {
        st.procs
            .get(&w.sender_arena)
            .and_then(|bp| bp.handles.get(&w.target_handle).copied())
    };
    match idx.and_then(|i| st.nodes.get(i)) {
        Some(n) => (n.ptr, n.cookie),
        None => (w.target_handle, w.cookie),
    }
}

/// 0.9.131: record one short event tag in an arena's
/// ignition evidence ring (see PidEvidence). Pure
/// bookkeeping for the ignition dump; nothing reads
/// the ring back into any decision.
fn evidence_tag(st: &mut BinderState, arena: &str, tag: String) {
    let e = st.evidence.entry(arena.to_string()).or_default();
    if e.tags.len() >= 24 {
        e.tags.pop_front();
    }
    e.tags.push_back(tag);
}

/// 0.9.131: keep a large delivered transaction's
/// parcel in the receiving arena's evidence ring
/// (bytes capped at 8KB; see BigTxnRec).
fn evidence_big_txn(
    st: &mut BinderState,
    arena: &str,
    code: u32,
    sender_pid: i32,
    slot: u32,
    tdata: &[u8],
) {
    let e = st.evidence.entry(arena.to_string()).or_default();
    let keep = tdata.len().min(8192);
    e.big.push_back(BigTxnRec {
        code,
        sender_pid,
        full_size: tdata.len(),
        slot,
        bytes: tdata[..keep].to_vec(),
    });
    while e.big.len() > 2 {
        e.big.pop_front();
    }
}

/// The dvmAbort pc range for the ignition dump's
/// trigger B (checked tracer-side at the FATAL site).
/// The 0.9.130 line-three forensics pinned the field
/// signature (0.9.126 through 0.9.130) to pc
/// 0x8004612c, inside libdvm's dvmAbort body (VA
/// 0x46105, 68 bytes: Dalvik's internal-check failure
/// path, which deliberately jumps at the 0xdeadd00d
/// poison address); the range below is that page with
/// margin. A constant, not a lookup: the guest libdvm
/// is one fixed build in this rootfs.
const DVMABORT_PC_LO: u64 = 0x8004_6000;
const DVMABORT_PC_HI: u64 = 0x8004_7000;

/// 0.9.131 ignition dump: print one guest process's
/// evidence ring (see PidEvidence) -- the last two
/// large transactions delivered to it, in full, and
/// its last 24 event tags. Fired from two triggers:
/// (A) in binder_send_txn, when the pid sends its
/// crash report (code 2 on the IActivityManager
/// interface -- the parcel's own token is the AMS
/// identity; binder nodes carry no name registry in
/// this driver), and (B) over MSG_REQ_IGNITION_DUMP,
/// when the tracer sees a FATAL in the dvmAbort pc
/// range above. The guest's logcat near-window is
/// deliberately NOT part of the group: the guest's
/// /dev/log/* are path-translated files under the
/// rootfs that the supervisor never parses or
/// streams, and no channel it owns carries logcat
/// text (the [guest] channel is the guest console) --
/// the end line below is the offline anchor the
/// forensics align the packaged log-*.txt files
/// against. Volume: a stored parcel prints at most
/// 3072 of its bytes (96 hex lines), so one trigger
/// stays under ~230 lines. Log only throughout.
fn binder_ignition_dump(st: &BinderState, pid: i32, trigger: &str) {
    let arena = st.thread_arena.get(&pid).cloned();
    let ev = arena.as_ref().and_then(|a| st.evidence.get(a));
    bsup!(
        "binder: ignition dump pid={pid} trigger={trigger} arena={} evidence={}",
        arena.as_deref().unwrap_or("-"),
        if ev.is_some() { "yes" } else { "none" }
    );
    if let Some(ev) = ev {
        for (n, rec) in ev.big.iter().enumerate() {
            bsup!(
                "binder: ignition bigtxn pid={pid} n={n} code={} from={} size={} slot={} stored={} truncated={}",
                rec.code,
                rec.sender_pid,
                rec.full_size,
                rec.slot,
                rec.bytes.len(),
                rec.full_size > rec.bytes.len()
            );
            let show = rec.bytes.len().min(3072);
            for (i, chunk) in rec.bytes[..show].chunks(32).enumerate() {
                bsup!(
                    "binder: ignition hex pid={pid} n={n} off={} {}",
                    i * 32,
                    hex_head(chunk, 32)
                );
            }
            if show < rec.bytes.len() {
                bsup!(
                    "binder: ignition hex pid={pid} n={n} print-truncated stored={} shown={show}",
                    rec.bytes.len()
                );
            }
        }
        for (i, t) in ev.tags.iter().enumerate() {
            bsup!("binder: ignition tag pid={pid} i={i} {t}");
        }
    }
    bsup!("binder: ignition dump end pid={pid}");
}

/// 0.9.140 (M2): the first outstanding wait one
/// thread owns as sender, wherever it currently
/// lives -- the shared per-target queues, or claimed
/// on a serving thread's stack. Returns (target
/// arena, code). This is the ground truth a parked
/// thread's park kind is judged from: a parked
/// thread with a wait outstanding is waiting for
/// that wait's reply, not for work.
fn find_wait_for_sender(st: &BinderState, pid: i32) -> Option<(String, u32)> {
    for (t_arena, q) in &st.waiters {
        for w in q {
            if w.sender_pid == pid {
                return Some((t_arena.clone(), w.code));
            }
        }
    }
    for stack in st.serving.values() {
        for g in &stack.groups {
            for fr in &g.frames {
                if let ServingFrame::Reply(w, _) = fr {
                    if w.sender_pid == pid {
                        return Some((stack.arena.clone(), w.code));
                    }
                }
            }
        }
    }
    None
}

/// 0.9.141 (s9-141-desk S4): one decoded command of
/// a parked thread's frozen write stream. `consumed`
/// is the offset test against the frozen
/// write_consumed: everything below it the
/// supervisor already consumed at the entry stop,
/// everything at or above it the guest presented
/// but nothing has acted on.
struct FrozenCmd {
    name: String,
    consumed: bool,
    trunc: bool,
    /// TRANSACTION/REPLY payload as read off the
    /// stream: (target, code, flags, data_size).
    txn: Option<(u32, u32, u32, u32)>,
}

/// The full decode of one frozen write stream
/// (0.9.141 S4): the whole presented stream, up to
/// 64KB and 64 commands, with no write_consumed==0
/// early-out -- a parked thread whose stream the
/// coordinator consumed in full can still be
/// carrying the transaction it froze inside. This
/// replaces the 0.9.140 two-command frozen_write_
/// desc. Decode advances exactly as batch_
/// skeleton's walk does; an unknown command ends
/// the decode. Telemetry only: the synthesis below
/// prints lines and feeds no decision.
struct FrozenStream {
    cmds: Vec<FrozenCmd>,
    stream_trunc: bool,
    cmds_trunc: bool,
    unreadable: bool,
}

fn decode_frozen_stream<R: FnMut(i32, u64, usize) -> Option<Vec<u8>>>(
    rd: &mut R,
    pid: i32,
    park: &ParkedIoctl,
) -> FrozenStream {
    let mut out = FrozenStream {
        cmds: Vec::new(),
        stream_trunc: false,
        cmds_trunc: false,
        unreadable: false,
    };
    let Some(bwr) = rd(pid, park.bwr as u64, 24) else {
        out.unreadable = true;
        return out;
    };
    let ws = u32_at(&bwr, 0) as usize;
    let wb = u32_at(&bwr, 8);
    if ws == 0 {
        return out;
    }
    out.stream_trunc = ws > 65536;
    let want = ws.min(65536);
    let Some(stream) = rd(pid, wb as u64, want) else {
        out.unreadable = true;
        return out;
    };
    let rd32 = |off: usize| -> u32 {
        if off + 4 <= stream.len() {
            u32_at(&stream, off)
        } else {
            0
        }
    };
    let mut cur = 0usize;
    loop {
        if cur + 4 > stream.len() {
            break;
        }
        if out.cmds.len() >= 64 {
            out.cmds_trunc = true;
            break;
        }
        let cmd = u32_at(&stream, cur);
        let (name, adv): (&str, usize) = match cmd {
            BC_ENTER_LOOPER => ("ENTER_LOOPER", 4),
            BC_REGISTER_LOOPER => ("REGISTER_LOOPER", 4),
            BC_EXIT_LOOPER => ("EXIT_LOOPER", 4),
            BC_FREE_BUFFER => ("FREE_BUFFER", 8),
            BC_INCREFS => ("INCREFS", 8),
            BC_ACQUIRE => ("ACQUIRE", 8),
            BC_RELEASE => ("RELEASE", 8),
            BC_DECREFS => ("DECREFS", 8),
            BC_INCREFS_DONE => ("INCREFS_DONE", 12),
            BC_ACQUIRE_DONE => ("ACQUIRE_DONE", 12),
            BC_ATTEMPT_ACQUIRE => ("ATTEMPT_ACQUIRE", 12),
            BC_REQUEST_DEATH_NOTIFICATION => ("REQ_DEATH", 12),
            BC_CLEAR_DEATH_NOTIFICATION => ("CLEAR_DEATH", 12),
            BC_DEAD_BINDER_DONE => ("DEAD_BINDER_DONE", 8),
            BC_TRANSACTION => ("TRANSACTION", 44),
            BC_REPLY => ("REPLY", 44),
            other => {
                out.cmds.push(FrozenCmd {
                    name: format!("UNKNOWN(0x{other:08x})"),
                    consumed: cur < park.write_consumed as usize,
                    trunc: false,
                    txn: None,
                });
                break;
            }
        };
        let trunc = cur + adv > stream.len();
        let txn = if cmd == BC_TRANSACTION || cmd == BC_REPLY {
            Some((
                rd32(cur + 4),
                rd32(cur + 12),
                rd32(cur + 16),
                rd32(cur + 28),
            ))
        } else {
            None
        };
        out.cmds.push(FrozenCmd {
            name: name.to_string(),
            consumed: cur < park.write_consumed as usize,
            trunc,
            txn,
        });
        if trunc {
            break;
        }
        cur += adv;
    }
    out
}

/// Render a decoded stream as the frozen_write
/// skeleton: command names in order, transactions
/// and replies with their code/target/flags/
/// data_size, every command carrying its consumed
/// flag. Past ten commands the line folds to the
/// first eight and last two with the total named.
fn frozen_skeleton(fs: &FrozenStream) -> String {
    if fs.unreadable {
        return "unreadable".to_string();
    }
    let render = |c: &FrozenCmd| -> String {
        let nm = if c.trunc {
            format!("{}(trunc)", c.name)
        } else {
            c.name.clone()
        };
        match &c.txn {
            Some((t, code, flags, ds)) => format!(
                "{nm} code={code} target={t} flags=0x{flags:x} data_size={ds} consumed={}",
                c.consumed as u8
            ),
            None => format!("{nm} consumed={}", c.consumed as u8),
        }
    };
    let n = fs.cmds.len();
    let mut s = if n > 10 {
        let mut parts: Vec<String> = fs.cmds[..8].iter().map(&render).collect();
        parts.push("…".to_string());
        parts.extend(fs.cmds[n - 2..].iter().map(&render));
        format!("{} (total {n} cmds)", parts.join(" "))
    } else {
        fs.cmds
            .iter()
            .map(&render)
            .collect::<Vec<_>>()
            .join(" ")
    };
    if fs.stream_trunc {
        s.push_str(" stream_trunc=1");
    }
    if fs.cmds_trunc {
        s.push_str(" cmds_trunc=1");
    }
    s
}

/// Resolve a decoded transaction's target handle
/// to its owner arena the way the claim path does:
/// handle 0 through the context-manager node, any
/// other handle through the sender arena's own
/// handle table into the node registry.
fn frozen_target_owner(st: &BinderState, sender_arena: &str, target: u32) -> Option<String> {
    let idx = if target == 0 {
        st.mgr_node
    } else {
        st.procs
            .get(sender_arena)
            .and_then(|bp| bp.handles.get(&target).copied())
    };
    idx.and_then(|i| st.nodes.get(i)).map(|n| n.owner.clone())
}

/// Whether the wait tables -- the same tables
/// find_wait_for_sender scans -- hold a wait from
/// `pid` with this code toward `owner` (any target
/// when the decoded handle did not resolve).
fn frozen_wait_exists(st: &BinderState, pid: i32, code: u32, owner: Option<&str>) -> bool {
    for (t_arena, q) in &st.waiters {
        if owner.is_some() && Some(t_arena.as_str()) != owner {
            continue;
        }
        if q.iter().any(|w| w.sender_pid == pid && w.code == code) {
            return true;
        }
    }
    for stack in st.serving.values() {
        if owner.is_some() && Some(stack.arena.as_str()) != owner {
            continue;
        }
        for g in &stack.groups {
            for fr in &g.frames {
                if let ServingFrame::Reply(w, _) = fr {
                    if w.sender_pid == pid && w.code == code {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// One synthesized outstanding wait (0.9.141 S4):
/// a BC_TRANSACTION decoded out of a parked
/// thread's own stream that no registered wait
/// corresponds to.
struct InferredWait {
    target_arena: Option<String>,
    target: u32,
    code: u32,
    flags: u32,
    data_size: u32,
    consumed: bool,
}

fn frozen_inferred(
    st: &BinderState,
    sender_arena: &str,
    pid: i32,
    fs: &FrozenStream,
) -> Vec<InferredWait> {
    let mut out = Vec::new();
    for c in &fs.cmds {
        if c.name != "TRANSACTION" || c.trunc {
            continue;
        }
        let Some((target, code, flags, ds)) = c.txn else {
            continue;
        };
        let owner = frozen_target_owner(st, sender_arena, target);
        if !frozen_wait_exists(st, pid, code, owner.as_deref()) {
            out.push(InferredWait {
                target_arena: owner,
                target,
                code,
                flags,
                data_size: ds,
                consumed: c.consumed,
            });
        }
    }
    out
}

fn print_inferred(arena: &str, pid: i32, inf: &[InferredWait]) {
    for w in inf {
        match &w.target_arena {
            Some(t) => bsup!(
                "binder: wedge-pending-inferred arena={arena} pid={pid} target_arena={t} code={} flags=0x{:x} data_size={} consumed={} src=stream-decode",
                w.code,
                w.flags,
                w.data_size,
                w.consumed as u8
            ),
            None => bsup!(
                "binder: wedge-pending-inferred arena={arena} pid={pid} target_arena=unresolved target=0x{:x} code={} flags=0x{:x} data_size={} consumed={} src=stream-decode",
                w.target,
                w.code,
                w.flags,
                w.data_size,
                w.consumed as u8
            ),
        }
    }
}

/// 0.9.140 (s9-140-desk-ignition M2/M3/M6): the
/// wedge chain dump for one system_server arena,
/// assembled coordinator-side at the tracer's
/// request (see MSG_REQ_WEDGE_CHAIN) in the wedge
/// snapshot's instant, and carried back over the
/// reply for in-order replay. Everything printed is
/// a read of existing BinderState tables -- serving
/// stacks, the waiters queues, the parked table --
/// plus, per parked thread of the arena, the frozen
/// write decode above. Nothing here feeds any
/// pairing, delivery, shield or settlement decision.
/// Returns the holder the provisional verdict (M6)
/// named, 0 when it named none; the tracer keeps it
/// for the traces harvest (M5). 0.9.141 (S4/S6)
/// adds the full stream decode with synthesized
/// pending lines and the servicer view; the
/// verdict's inputs are exactly the 0.9.140 set,
/// and the servicers the dump found ride the reply
/// back for the face broadcast.
fn binder_wedge_chain<R: FnMut(i32, u64, usize) -> Option<Vec<u8>>>(
    st: &BinderState,
    leader: i32,
    solo: i32,
    rd: &mut R,
) -> (i32, Vec<(String, i32)>) {
    let Some(arena) = st.thread_arena.get(&leader).cloned() else {
        bsup!(
            "binder: wedge-chain leader={leader} arena=- (leader holds no binder arena)"
        );
        bsup!(
            "binder: wedge-verdict arena=- class=unknown holder=- basis=none (provisional)"
        );
        return (0, Vec::new());
    };
    // (a) Serving stacks of this arena: every frame
    // the arena's threads are serving, in stack
    // order. A code-2 frame sitting unreplied on a
    // stack names the crash report's holder.
    let mut stack_pids: Vec<i32> = st
        .serving
        .iter()
        .filter(|(_, s)| s.arena == arena)
        .map(|(p, _)| *p)
        .collect();
    stack_pids.sort_unstable();
    let mut crash_frame_holder: Option<i32> = None;
    for tpid in &stack_pids {
        let stack = &st.serving[tpid];
        let mut parts: Vec<String> = Vec::new();
        for g in &stack.groups {
            for fr in &g.frames {
                match fr {
                    ServingFrame::Reply(w, _) => {
                        parts.push(format!("({},{})", w.sender_pid, w.code));
                        if w.code == 2 {
                            crash_frame_holder = Some(*tpid);
                        }
                    }
                    ServingFrame::Other => parts.push("(-,oneway)".to_string()),
                }
            }
        }
        bsup!(
            "binder: wedge-serving arena={arena} pid={tpid} depth={} stack=[{}]",
            stack.depth(),
            parts.join(",")
        );
    }
    // (b) Outstanding waits, both directions. A wait
    // lives in exactly one of two places: the shared
    // queue of its target arena (delivered, not yet
    // claimed by a serving thread) or, once claimed,
    // as a Reply frame on the serving thread's stack.
    // Out-waits are this arena's threads as senders;
    // in-waits are the waits addressed to this arena
    // (who is queued behind the wedge). For an
    // unclaimed out-wait the peer cell is read off
    // the target arena's parcel table: the parcel is
    // either there (received, unclaimed) or not
    // (never landed).
    let mut out_waits: Vec<(i32, String, u32, String, String)> = Vec::new();
    let mut in_waits: Vec<(i32, String, u32, String)> = Vec::new();
    for (t_arena, q) in &st.waiters {
        for w in q {
            if w.sender_arena == arena {
                let peer = match st.procs.get(t_arena) {
                    Some(bp) if bp
                        .parcels
                        .values()
                        .any(|pp| pp.from_pid == w.sender_pid && pp.code == w.code) =>
                    {
                        "received-unclaimed"
                    }
                    _ => "not-received",
                };
                out_waits.push((
                    w.sender_pid,
                    t_arena.clone(),
                    w.code,
                    "queued".to_string(),
                    peer.to_string(),
                ));
            }
            if *t_arena == arena {
                in_waits.push((
                    w.sender_pid,
                    w.sender_arena.clone(),
                    w.code,
                    "queued".to_string(),
                ));
            }
        }
    }
    // 0.9.141 (S6): the servicers behind this
    // arena's frozen claimed out-waits, collected
    // alongside the waits scan below.
    let mut servicer_hits: Vec<(String, i32)> = Vec::new();
    for (tpid, stack) in &st.serving {
        for g in &stack.groups {
            for fr in &g.frames {
                let ServingFrame::Reply(w, seq) = fr else {
                    continue;
                };
                if w.sender_arena == arena {
                    out_waits.push((
                        w.sender_pid,
                        stack.arena.clone(),
                        w.code,
                        format!("claimed serving_pid={tpid} claim_seq={seq}"),
                        "serving".to_string(),
                    ));
                    servicer_hits.push((stack.arena.clone(), *tpid));
                }
                if stack.arena == arena {
                    in_waits.push((
                        w.sender_pid,
                        w.sender_arena.clone(),
                        w.code,
                        format!("claimed serving_pid={tpid} claim_seq={seq}"),
                    ));
                }
            }
        }
    }
    out_waits.sort();
    in_waits.sort();
    for (from, t_arena, code, state, peer) in &out_waits {
        bsup!(
            "binder: wedge-waits arena={arena} dir=out from={from} target_arena={t_arena} code={code} state={state} peer={peer}"
        );
    }
    for (from, s_arena, code, state) in &in_waits {
        bsup!(
            "binder: wedge-waits arena={arena} dir=in from={from} sender_arena={s_arena} code={code} state={state}"
        );
    }
    // (M2) Park kinds for this arena's parked
    // threads: idle awaiting-work versus frozen
    // mid-call, judged from the wait tables above,
    // with the frozen call named from its own write
    // stream.
    let mut park_pids: Vec<i32> = st
        .parked
        .keys()
        .copied()
        .filter(|p| st.thread_arena.get(p) == Some(&arena))
        .collect();
    park_pids.sort_unstable();
    for ppid in &park_pids {
        let park = &st.parked[ppid];
        // 0.9.141 (S4): the full stream decode, and
        // the waits it implies that the tables do
        // not hold. The synthesized lines are pure
        // telemetry; the park kind is the only
        // judgement they touch, and it judges from
        // the same stream the lines were read off.
        let fs = decode_frozen_stream(rd, *ppid, park);
        let inferred = frozen_inferred(st, &arena, *ppid, &fs);
        let (kind, t_arena_s, code_s) = match find_wait_for_sender(st, *ppid) {
            Some((t, c)) => ("wait-reply", t, c.to_string()),
            None => match inferred.first() {
                Some(f) => (
                    "wait-reply-inferred",
                    f.target_arena
                        .clone()
                        .unwrap_or_else(|| "unresolved".to_string()),
                    f.code.to_string(),
                ),
                None => ("idle", "-".to_string(), "-".to_string()),
            },
        };
        let frozen = frozen_skeleton(&fs);
        bsup!(
            "binder: wedge-park arena={arena} pid={ppid} park_kind={kind} target_arena={t_arena_s} code={code_s} frozen_write=[{frozen}]"
        );
        print_inferred(&arena, *ppid, &inferred);
    }
    // (S6) The servicer view (0.9.141): for each
    // distinct servicer behind a frozen claimed
    // out-wait (at most two), recompute the waits
    // picture inside the servicer's own arena --
    // its outstanding sends, the waits it has
    // claimed, its serving stack -- and, when the
    // servicer itself sits parked, its own full
    // stream decode. Same tables, same line
    // formats; nothing here feeds the verdict
    // below, whose inputs stay the 0.9.140 set.
    servicer_hits.sort();
    servicer_hits.dedup();
    servicer_hits.truncate(2);
    for (s_arena, x) in &servicer_hits {
        let x = *x;
        bsup!(
            "binder: wedge-servicer-waits arena={arena} servicer_arena={s_arena} pid={x}"
        );
        for (t_arena, q) in &st.waiters {
            for w in q {
                if w.sender_pid == x {
                    let peer = match st.procs.get(t_arena) {
                        Some(bp) if bp
                            .parcels
                            .values()
                            .any(|pp| pp.from_pid == w.sender_pid && pp.code == w.code) =>
                        {
                            "received-unclaimed"
                        }
                        _ => "not-received",
                    };
                    bsup!(
                        "binder: wedge-waits arena={s_arena} dir=out from={x} target_arena={t_arena} code={} state=queued peer={peer}",
                        w.code
                    );
                }
            }
        }
        for (tpid2, stack) in &st.serving {
            if stack.arena != *s_arena {
                continue;
            }
            for g in &stack.groups {
                for fr in &g.frames {
                    if let ServingFrame::Reply(w, seq) = fr {
                        if w.sender_pid == x {
                            bsup!(
                                "binder: wedge-waits arena={s_arena} dir=out from={x} target_arena={s_arena} code={} state=claimed serving_pid={tpid2} claim_seq={seq} peer=serving",
                                w.code
                            );
                        }
                    }
                }
            }
        }
        if let Some(stack) = st.serving.get(&x) {
            for g in &stack.groups {
                for fr in &g.frames {
                    if let ServingFrame::Reply(w, seq) = fr {
                        bsup!(
                            "binder: wedge-waits arena={s_arena} dir=in from={} sender_arena={} code={} state=claimed serving_pid={x} claim_seq={seq}",
                            w.sender_pid, w.sender_arena, w.code
                        );
                    }
                }
            }
        }
        let (depth, frames) = match st.serving.get(&x) {
            Some(stack) => {
                let mut parts: Vec<String> = Vec::new();
                for g in &stack.groups {
                    for fr in &g.frames {
                        match fr {
                            ServingFrame::Reply(w, _) => {
                                parts.push(format!("({},{})", w.sender_pid, w.code))
                            }
                            ServingFrame::Other => {
                                parts.push("(-,oneway)".to_string())
                            }
                        }
                    }
                }
                (stack.depth(), parts.join(","))
            }
            None => (0, String::new()),
        };
        bsup!(
            "binder: wedge-servicer-serving arena={arena} servicer_arena={s_arena} pid={x} depth={depth} frames=[{frames}]"
        );
        if let Some(park) = st.parked.get(&x) {
            let fs = decode_frozen_stream(rd, x, park);
            let inferred = frozen_inferred(st, s_arena, x, &fs);
            let (kind, t_s, c_s) = match find_wait_for_sender(st, x) {
                Some((t, c)) => ("wait-reply", t, c.to_string()),
                None => match inferred.first() {
                    Some(f) => (
                        "wait-reply-inferred",
                        f.target_arena
                            .clone()
                            .unwrap_or_else(|| "unresolved".to_string()),
                        f.code.to_string(),
                    ),
                    None => ("idle", "-".to_string(), "-".to_string()),
                },
            };
            let skel = frozen_skeleton(&fs);
            bsup!(
                "binder: wedge-servicer-park arena={arena} servicer_arena={s_arena} pid={x} park_kind={kind} target_arena={t_s} code={c_s} frozen_full=[{skel}]"
            );
            print_inferred(s_arena, x, &inferred);
        }
    }
    // (M6) The provisional verdict. Field forensics
    // re-judge every tenure against the decision
    // rules in s9-140-desk-ignition section 5.1;
    // this line is a grep entry point, not a ruling.
    // The B family splits by the waiting thread (the
    // leader itself, or a binder thread) -- B versus
    // B' (a wait on an app arena) is read off the
    // target_arena the waits lines above print, not
    // guessed here.
    let (class, holder, basis): (&str, i32, &str) =
        if let Some(h) = crash_frame_holder {
            (if h == leader { "A1" } else { "A2" }, h, "report+stack")
        } else if in_waits.iter().any(|w| w.2 == 2) {
            // A crash report delivered but never
            // claimed: the report exists (the waits
            // lines prove it) but no stack frame names
            // its holder; the solo futex waiter is the
            // only holder candidate in evidence.
            if solo > 0 {
                (
                    if solo == leader { "A1" } else { "A2" },
                    solo,
                    "futex-solo",
                )
            } else {
                ("unknown", 0, "none")
            }
        } else if let Some(w) =
            out_waits.iter().find(|w| w.0 == leader).or(out_waits.first())
        {
            (if w.0 == leader { "B" } else { "B2" }, w.0, "wait-target")
        } else if solo > 0 {
            ("C", solo, "futex-solo")
        } else {
            ("unknown", 0, "none")
        };
    bsup!(
        "binder: wedge-verdict arena={arena} class={class} holder={} basis={basis} (provisional)",
        if holder > 0 {
            holder.to_string()
        } else {
            "-".to_string()
        }
    );
    (holder, servicer_hits)
}

/// Cap on the write-overlap audit table (0.9.132):
/// the most recent delivery writes kept, across all
/// arenas. Each record costs at most 64 bytes of head
/// plus the arena name, so the table stays under
/// roughly 40KB however long the run.
const WRITE_AUDIT_CAP: usize = 384;

/// 0.9.132 shield4 judgement: a reply's first word is
/// legal only if it matches one of the five shapes an
/// honest reply header can take. The two-range
/// blacklist this replaces (guest heap-pointer domain,
/// libc domain) provably leaked: the .130/.131 census
/// of 3,317 reply pops found four poisoned first words
/// already delivered outside both ranges -- three
/// stack-domain words and one string fragment
/// ("/dat") -- each followed immediately by the
/// waiter's crash report. Poison is "arbitrary
/// replier memory", so no enumeration of bad domains
/// can close it; enumerate the good shapes instead
/// (s9-132-spec section 1.3). Retrospective check of
/// this exact predicate against both field censuses:
/// flagged 17 (the 13 the old shields caught plus the
/// 4 leaks), honest replies misjudged 0 of 3,300.
fn shield4_legal_first(w: u32) -> bool {
    w == 0 // no-exception header / zero return value
        || w >= 0xFFFF_FF00 // -256..=-1: exception codes, negative errno
        || w <= 0x0000_FFFF // small positive counts / lengths / status
        // flat_binder_object type words, the full
        // BINDER_TYPE_* family from the binder protocol
        // constants: BINDER / WEAK_BINDER / HANDLE /
        // WEAK_HANDLE / FD. The census observed BINDER,
        // HANDLE and FD; the two weak constants were
        // never observed and are admitted as same-family.
        || matches!(
            w,
            0x7362_2A85 | 0x7762_2A85 | 0x7368_2A85 | 0x7768_2A85 | 0x6664_2A85
        )
        || w == 0x504F_4E47 // 'PONG', the paxsvc PING reply magic
}

/// Which bucket a shield4-rejected first word counts
/// into (settlement telemetry, s9-132-spec 1.4). The
/// boundaries are descriptive, not judgemental: the
/// first two are the old blacklist's domains, the
/// third is the stack range the .130/.131 leaks fell
/// in, and everything else is fragment/other.
fn shield4_bucket(w: u32) -> &'static str {
    if (0x4000_0000..0x5000_0000).contains(&w) {
        "cookie"
    } else if (0xafd0_0000..0xb100_0000).contains(&w) {
        "libc"
    } else if (0xe800_0000..0xf400_0000).contains(&w) {
        "stack"
    } else {
        "other"
    }
}

/// 0.9.141 (s9-141-desk P2): classify a poisoned
/// reply's first word against the reply's own data
/// address (the D2 test): a word pointing at the
/// buffer itself, or eight bytes before it (the
/// chunk header a stale head would carry), convicts
/// the fat family's self-referential shape; a word
/// inside the same page is the near form; anything
/// else falls to the shield4 domain buckets under
/// their class names. Returns the class name and
/// its index in BinderState::poison_word0.
fn poison_word0_class(w: u32, daddr: u32) -> (&'static str, usize) {
    let delta = w as i64 - daddr as i64;
    if delta == -8 {
        ("self-8", 0)
    } else if delta == 0 {
        ("self", 1)
    } else if delta.abs() < 4096 {
        ("self-page", 2)
    } else {
        match shield4_bucket(w) {
            "cookie" => ("heap-other", 3),
            "libc" => ("libc", 4),
            "stack" => ("stack", 5),
            _ => ("other", 6),
        }
    }
}

/// 0.9.132 write-overlap audit (telemetry only; see
/// WriteAuditRec). Fires at a shield intercept on the
/// reply path, where the poison parcel's source --
/// the replier's arena, its guest address daddr and
/// the copied bytes -- is in hand; compared against
/// every delivery write the supervisor itself made
/// into that arena: an overlap whose recorded head
/// bytes match the poison bytes over the comparable
/// span means one of our own delivery writes landed
/// on the range later read back as poison (case (b)
/// in s9-132-spec 2.3); zero overlap means the range
/// was never ours (case (a)). Prints exactly one line
/// and feeds nothing.
/// 0.9.133 coordinate fix (s9-132-verify Q3): the
/// comparison now runs in guest VA space end to end --
/// records carry VA intervals (see WriteAuditRec) and
/// the poison source [daddr, daddr+len) is already a
/// guest VA, so no base conversion stands between the
/// two. The old file-offset form converted the source
/// through the replier thread's registered binder
/// mmap base; heap Parcel buffers sit gigabases below
/// that window, the subtraction underflowed on every
/// field intercept (8/8), and the audit compared
/// nothing. What remains of the base here is
/// diagnostic: the line prints the arena's full
/// registered base set (all threads of one process
/// share one mmap, so the set should hold one value;
/// the replier thread's own key is named separately),
/// and src_rel names where the source sits against
/// the lowest registered base -- below-base is the
/// old underflow case, now compared instead of
/// refused, and for heap-sourced poison the expected
/// outcome is no-overlap. verdict=no-base survives
/// only where there is nothing to compare against:
/// branch=no-proc (the arena's proc state is gone)
/// or branch=no-key (no thread ever registered a
/// base for this arena).
fn write_audit_check(
    st: &BinderState,
    arena: &str,
    replier: i32,
    daddr: u32,
    data: &[u8],
    trigger: &str,
    claim_seq: u64,
) {
    let Some(bp) = st.procs.get(arena) else {
        bsup!(
            "binder: write-audit trigger={trigger} claim_seq={claim_seq} replier={replier} arena={arena} daddr=0x{daddr:x} size={} verdict=no-base branch=no-proc base=none",
            data.len()
        );
        return;
    };
    let mut bases: Vec<u32> = bp.base.values().copied().collect();
    bases.sort_unstable();
    bases.dedup();
    if bases.is_empty() {
        bsup!(
            "binder: write-audit trigger={trigger} claim_seq={claim_seq} replier={replier} arena={arena} daddr=0x{daddr:x} size={} verdict=no-base branch=no-key base=none",
            data.len()
        );
        return;
    }
    let bases_str = bases
        .iter()
        .map(|b| format!("0x{b:x}"))
        .collect::<Vec<_>>()
        .join(",");
    let key_base = bp
        .base
        .get(&replier)
        .map(|b| format!("0x{b:x}"))
        .unwrap_or_else(|| "none".to_string());
    let src_rel = if (daddr as u64) < bases[0] as u64 {
        "below-base"
    } else {
        "at-or-above-base"
    };
    let src_start = daddr as u64;
    let src_end = src_start.saturating_add(data.len() as u64);
    let mut records = 0usize;
    let mut overlaps = 0usize;
    let mut compared = 0usize;
    let mut mismatch = 0usize;
    for rec in &st.write_audit {
        if rec.arena != arena {
            continue;
        }
        records += 1;
        let rec_end = rec.va.saturating_add(rec.len as u64);
        let o_start = src_start.max(rec.va);
        let o_end = src_end.min(rec_end);
        if o_start >= o_end {
            continue;
        }
        overlaps += 1;
        // Bytes are comparable only where the record's
        // kept head (the write's first 64 bytes)
        // reaches into the overlap.
        let head_reach = (rec.va + rec.head.len() as u64).min(o_end);
        if o_start >= head_reach {
            continue;
        }
        let n = (head_reach - o_start) as usize;
        let d_at = (o_start - src_start) as usize;
        let r_at = (o_start - rec.va) as usize;
        for k in 0..n {
            compared += 1;
            if data[d_at + k] != rec.head[r_at + k] {
                mismatch += 1;
            }
        }
    }
    let verdict = if overlaps == 0 {
        "no-overlap"
    } else if compared == 0 {
        "overlap-uncovered"
    } else if mismatch == 0 {
        "overlap-bytes-match"
    } else {
        "overlap-bytes-differ"
    };
    bsup!(
        "binder: write-audit trigger={trigger} claim_seq={claim_seq} replier={replier} arena={arena} daddr=0x{daddr:x} size={} src_va=0x{src_start:x} bases=[{bases_str}] key_base={key_base} src_rel={src_rel} records={records} overlaps={overlaps} compared={compared} mismatch={mismatch} verdict={verdict}",
        data.len()
    );
}

/// 0.9.135 reply-source collision check (telemetry
/// only; see s9-135-desk Q2): at a claimed reply pop,
/// collide the replier descriptor's source range
/// [daddr, daddr+size) against every parcel record
/// this supervisor keeps for the replier's own
/// address space:
///
/// (A) the parcels fills handed THIS thread
///     (ClaimParcelRec ring) -- a hit names the claim
///     the buffer belongs to: rel=self (the very call
///     being answered), rel=newer (a parcel claimed
///     after it -- the nested call's next parcel,
///     the aliasing hypothesis' exact prediction),
///     rel=older (a stale buffer recycled), or an
///     unclaimed one-way parcel;
/// (B) the parcels THIS thread itself sent earlier
///     (SendSrcRec ring), with a byte verdict against
///     the head as copied then: match means the
///     buffer still holds that send's bytes verbatim;
/// (C) the supervisor's own delivery writes into the
///     replier's arena (the write-audit table), with
///     a head verdict in the audit's own style;
/// (D) the replier arena's ignition evidence big
///     parcels (0.9.131), their window interval
///     derived from the arena slot under the replier
///     thread's registered base, BR_TRANSACTION +
///     descriptor (44B) ahead of the stored data.
///
/// Every hit prints one line; a miss prints nothing
/// and only moves the settlement counters
/// (reply_collide_checks / reply_collide_hits on the
/// arena-death free-counters line). The check reads
/// records and the copied bytes; it feeds no
/// judgement, pairing or delivery decision.
fn reply_source_collide(
    st: &mut BinderState,
    arena: &str,
    pid: i32,
    claim_seq: u64,
    daddr: u32,
    data: &[u8],
) {
    st.reply_collide_checks += 1;
    let lo = daddr as u64;
    let hi = lo + data.len() as u64;
    let mut lines: Vec<String> = Vec::new();
    // (A) parcels this thread was handed in fills.
    if let Some(ring) = st.claim_parcels.get(&pid) {
        for rec in ring.iter() {
            let rlo = rec.va as u64;
            let rhi = rlo + rec.size as u64;
            if lo < rhi && rlo < hi {
                let rel = match rec.seq {
                    Some(s) if s == claim_seq => "self",
                    Some(s) if s > claim_seq => "newer",
                    Some(_) => "older",
                    None => "unclaimed",
                };
                let seq_s = match rec.seq {
                    Some(s) => s.to_string(),
                    None => "-".to_string(),
                };
                lines.push(format!(
                    "claim-parcel seq={seq_s} fill={} va=0x{:x} size={} code={} sender={} rel={rel}",
                    rec.fill_id, rec.va, rec.size, rec.code, rec.sender_pid
                ));
            }
        }
    }
    // (B) this thread's own earlier sends.
    if let Some(ring) = st.send_src.get(&pid) {
        for rec in ring.iter() {
            let rlo = rec.daddr as u64;
            let rhi = rlo + rec.dsize as u64;
            if lo < rhi && rlo < hi {
                let verdict = overlap_verdict(&rec.head, rec.daddr, daddr, data);
                lines.push(format!(
                    "own-send daddr=0x{:x} size={} code={} reply={} bytes={verdict}",
                    rec.daddr, rec.dsize, rec.code, rec.is_reply
                ));
            }
        }
    }
    // (C) supervisor delivery writes into this arena.
    for rec in st.write_audit.iter().filter(|r| r.arena == arena) {
        let rlo = rec.va;
        let rhi = rlo + rec.len as u64;
        if lo < rhi && rlo < hi {
            let verdict = overlap_verdict(&rec.head, rec.va as u32, daddr, data);
            lines.push(format!(
                "delivery-write va=0x{:x} len={} head={verdict}",
                rec.va, rec.len
            ));
        }
    }
    // (D) the arena's ignition evidence big parcels.
    let base = st
        .procs
        .get(arena)
        .and_then(|bp| bp.base.get(&pid))
        .copied();
    if let (Some(base), Some(ev)) = (base, st.evidence.get(arena)) {
        for rec in ev.big.iter() {
            let img_lo = base as u64 + rec.slot as u64;
            let img_hi = img_lo + 44 + rec.full_size as u64;
            if lo < img_hi && img_lo < hi {
                let verdict = if lo >= img_lo + 44 {
                    span_verdict(&rec.bytes, (lo - (img_lo + 44)) as usize, data)
                } else {
                    "na"
                };
                lines.push(format!(
                    "evidence-big sender={} code={} size={} slot={} bytes={verdict}",
                    rec.sender_pid, rec.code, rec.full_size, rec.slot
                ));
            }
        }
    }
    if !lines.is_empty() {
        st.reply_collide_hits += 1;
        for m in lines {
            bsup!(
                "binder: reply source collide seq={claim_seq} replier={pid} daddr=0x{daddr:x} size={} matches={m}",
                data.len()
            );
        }
    }
}

fn binder_handle_txn<R: FnMut(i32, u64, usize) -> Option<Vec<u8>>>(
    pid: i32,
    arena: &str,
    is_reply: bool,
    txn: &[u8],
    st: &mut BinderState,
    veuid: u32,
    rd: &mut R,
    actions: &mut Vec<BAction>,
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
    let Some(data) = rd(pid, daddr as u64, dsize) else {
        notes.push("txn data unreadable; dropped".to_string());
        return;
    };
    let offs = if osize > 0 {
        rd(pid, oaddr as u64, osize).unwrap_or_default()
    } else {
        Vec::new()
    };
    // 0.9.135 telemetry: file a large outgoing
    // transaction in the sender's collision ring (see
    // SendSrcRec) -- the buffer it was copied from is
    // one of the addresses a later reply descriptor of
    // the same thread can alias. Replies file
    // themselves at their pop instead, so a pop never
    // collides with its own record. Bookkeeping only.
    if !is_reply && dsize >= 256 {
        record_send_src(
            st,
            pid,
            SendSrcRec {
                daddr,
                dsize,
                code,
                is_reply: false,
                head: data[..data.len().min(64)].to_vec(),
            },
        );
    }
    if !offs.is_empty() {
        bsup!(
            "binder: raw txn pid={pid} arena={arena} reply={is_reply} code={code} slots{}",
            slot_dump(&data, &offs)
        );
        // 0.9.109 forensics: an out-of-bounds object offset
        // in the sender's array is a landmine for the
        // receiver (Parcel::scanForFds dereferences
        // mData + offset unchecked; the 0.9.108 field's
        // tenure-killing libbinder deaths trace to raw
        // OOB slots on scheduleLaunchActivity, three with
        // the identical word 0xae20e2b8 across tenures).
        // Capture the addressing facts while the sender
        // is still stopped: where the offsets pointer
        // aimed relative to the data, whether a re-read
        // agrees, and what sits just past the data (where
        // a contiguous offsets array would live).
        for i in 0..(offs.len() / 4) {
            let o = u32_at(&offs, i * 4);
            if (o as usize) + 16 > data.len() {
                let head: Vec<String> = (0..8)
                    .filter(|&k| (k + 1) * 4 <= data.len())
                    .map(|k| format!("{:08x}", u32_at(&data, k * 4)))
                    .collect();
                let reread = rd(pid, oaddr as u64, osize)
                    .map(|v| {
                        (0..(v.len() / 4))
                            .map(|k| format!("{:08x}", u32_at(&v, k * 4)))
                            .collect::<Vec<_>>()
                            .join(" ")
                    })
                    .unwrap_or_else(|| "<unreadable>".to_string());
                let past = rd(pid, (daddr as u64) + (dsize as u64), 4)
                    .map(|v| format!("0x{:08x}", u32_at(&v, 0)))
                    .unwrap_or_else(|| "<unreadable>".to_string());
                bsup!(
                    "binder: OOB slot forensics pid={pid} reply={is_reply} code={code} daddr=0x{daddr:x} oaddr=0x{oaddr:x} dsize={dsize} osize={osize} bad_off=0x{o:x} data_head=[{}] offs_reread=[{reread}] past_data_word={past}",
                    head.join(" ")
                );
                break;
            }
        }
    }
    // 0.9.110 shield, third layer: never deliver a parcel
    // whose object offsets are out of bounds. Field
    // evidence (0.9.108/0.9.109): the sender's offsets
    // array itself arrives poisoned (a pointer-valued
    // word -- 0xae20e2b8, identical across tenures -- in
    // place of the offset, on scheduleLaunchActivity),
    // reads are not torn (a re-read agrees), and the
    // receiver dies unchecked in Parcel::scanForFds.
    // The real driver validates offsets during its copy
    // and fails such a transaction; the faithful mirror
    // is to fail it too: drop a request outright (the
    // poisoned ones are one-way; the sender has moved
    // on) and answer a poisoned reply with FAILED_REPLY
    // so its waiter unwinds instead of hanging.
    let oob = (0..(offs.len() / 4)).any(|i| {
        let o = u32_at(&offs, i * 4) as usize;
        o + 16 > data.len()
    });
    if oob && !is_reply {
        bsup!(
            "binder: shield3 dropped OOB txn pid={pid} code={code} dsize={} osize={}",
            data.len(),
            offs.len()
        );
        notes.push("TRANSACTION with OOB object offset -> dropped (shield3)".to_string());
        return;
    }
    if is_reply {
        // 0.9.125: pairing is by transaction identity, not
        // by queue position. The wait this reply answers
        // was claimed onto the replier thread's own serving
        // stack when a read fill handed it the transaction
        // parcel (binder_claim_fills). 0.9.130: the pop
        // walks groups newest-first but consumes each
        // group from the front (see ServingStack) -- one
        // fill's transactions are served and answered in
        // buffer order, so a batch's first reply answers
        // its earliest claimed wait, not its latest.
        // The shared queue's FIFO pop is gone: under
        // concurrency it handed waiters other callers'
        // parcels (0.9.124's reply-pair dump photographed
        // 632-792B transaction parcels delivered as
        // replies; the receivers died on the garbage first
        // word -- s9-app-crash).
        // 0.9.124's dump below keeps the pairing line's
        // outstanding definition: the shared queue's
        // length before this pairing (unclaimed waits
        // only, now that claimed ones live on stacks).
        let n_outstanding = st.waiters.get(arena).map_or(0, |v| v.len());
        let mut claimed: Option<(ReplyWait, u64)> = None;
        // 0.9.128 telemetry: frames this pop consumed to
        // reach its Reply frame and the stack depth it
        // left behind, for the reply-pop dump below.
        // 0.9.130 adds the answered frame's fill_id.
        let mut pop_count = 0usize;
        let mut pop_depth = 0usize;
        let mut claimed_fill = 0u64;
        if let Some(stack) = st.serving.get_mut(&pid) {
            // 0.9.130 pairing: newest group first (a fill
            // claimed while an older call is still open is
            // a deeper serving level -- the old stack
            // order across fills), within the group from
            // the FRONT: the guest serves one fill's
            // transactions in buffer order and replies in
            // that order, so the batch's first reply
            // answers its earliest claimed wait. Other
            // frames ahead of it in the group are one-way
            // work already finished by the time the thread
            // replies; consume them on the way, as the
            // flat stack consumed the frames above its
            // Reply. A group drained without a Reply is
            // dropped and the search falls to the next
            // group down; groups left empty are removed,
            // so a group on the stack always holds frames.
            while claimed.is_none() {
                let gi = match stack.groups.len() {
                    0 => break,
                    n => n - 1,
                };
                let gfill = stack.groups[gi].fill_id;
                while !stack.groups[gi].frames.is_empty() {
                    let fr = stack.groups[gi].frames.remove(0);
                    pop_count += 1;
                    if let ServingFrame::Reply(w, seq) = fr {
                        claimed = Some((w, seq));
                        claimed_fill = gfill;
                        break;
                    }
                }
                if stack.groups[gi].frames.is_empty() {
                    stack.groups.remove(gi);
                }
            }
            pop_depth = stack.depth();
        }
        let Some((w, claim_seq)) = claimed else {
            // No claimed wait: this reply answers nothing
            // this thread was ever handed. Drop it and
            // count it -- pairing it with a stranger from
            // the shared queue is exactly the defect being
            // removed. The pre-0.9.125 "no waiter" early
            // return lands here too (a reply whose
            // transaction was never claimed can have no
            // legitimate recipient).
            st.reply_unmatched += 1;
            bsup!(
                "binder: reply-pair unmatched sender={pid} size={} dropped",
                data.len()
            );
            // 0.9.131: the orphan reply belongs in the
            // replier's own evidence ring (there is no
            // waiter's ring to charge it to).
            evidence_tag(st, arena, format!("unmatched size={}", data.len()));
            notes.push(
                "BC_REPLY with no claimed waiter; dropped (reply-pair unmatched)"
                    .to_string(),
            );
            return;
        };
        // 0.9.128 telemetry: photograph the pop itself --
        // the claim sequence of the frame this BC_REPLY
        // is answering (its source claim, stamped in
        // binder_claim_fills), how many frames the pop
        // consumed to reach it, the stack depth left
        // behind, and the reply parcel's first word and
        // size as the replier wrote them. Joined with the
        // claim dump and the big-reply dump's claim_seq,
        // one delivered reply traces claim -> pop ->
        // delivery, which is what separates a wrong-frame
        // pop from the other two substitution candidates
        // (s9-127-big-reply Q5). Log only.
        let first_word = if data.len() >= 4 { u32_at(&data, 0) } else { 0 };
        {
            let first = first_word;
            bsup!(
                "binder: reply-pop dump replier={pid} claim_seq={claim_seq} fill_id={claimed_fill} popped={pop_count} depth={pop_depth} first=0x{first:x} size={}",
                data.len()
            );
        }
        // 0.9.131: the pop is an event in the replier's
        // own evidence ring.
        evidence_tag(
            st,
            arena,
            format!("pop seq={claim_seq} size={} first=0x{first_word:x}", data.len()),
        );
        // 0.9.135 telemetry: the pop's full descriptor
        // photograph -- the replier's own transaction
        // descriptor exactly as read at the BC_REPLY
        // stop (source and offsets ranges, plus the
        // descriptor's own target/code/cookie words),
        // beside the claimed wait's identity and the
        // write batch this reply arrived in (skeleton
        // and this reply's ordinal inside it). The
        // .133/.134 add-reply family (s9-135-desk Q2)
        // claims clean and delivers a foreign parcel;
        // separating replier-side buffer aliasing from
        // the remaining candidates starts with naming
        // the buffer the descriptor actually pointed
        // at and the batch it rode in on. Log only.
        // 0.9.141 (P3): the replier's assembly-window
        // profile rides the descriptor line's tail.
        let win = st.cur_win.unwrap_or((0, 0, 0, 0, 0, 0));
        bsup!(
            "binder: reply-pop desc claim_seq={claim_seq} fill_id={claimed_fill} replier={pid} arena={arena} waiter={} waiter_arena={} handle={} code={} txn_target={target} txn_code={code} txn_cookie=0x{cookie:x} flags=0x{flags:x} daddr=0x{daddr:x} dsize={dsize} oaddr=0x{oaddr:x} osize={osize} batch_reply={} batch=[{}] win=[stops={} futex={} alloc={} parks={} sends={} maxdepth={}]",
            w.sender_pid,
            w.sender_arena,
            w.target_handle,
            w.code,
            st.cur_batch_reply_ord,
            st.cur_batch_skel,
            win.0,
            win.1,
            win.2,
            win.3,
            win.4,
            win.5
        );
        // 0.9.135 telemetry: for the slots the foreign
        // family haunts (handle 10, the add codes
        // 1/3/8), widen the head photograph from the
        // house 32B to the first 128B, hex with a
        // printable column: the family's 49-char
        // String16 sits past the old window, and the
        // parcel's true owner is named by its
        // interface token and head fields. Fires on
        // the raw copy, before any shield judgement,
        // for every claimed pop in the subset. Log
        // only.
        if w.target_handle == 10 && matches!(w.code, 1 | 3 | 8) {
            let show = data.len().min(128);
            bsup!(
                "binder: reply-head128 claim_seq={claim_seq} replier={pid} waiter={} handle={} code={} size={} shown={show}",
                w.sender_pid, w.target_handle, w.code, data.len()
            );
            for (ci, chunk) in data[..show].chunks(32).enumerate() {
                let hexs: Vec<String> =
                    chunk.iter().map(|b| format!("{b:02x}")).collect();
                let asc: String = chunk
                    .iter()
                    .map(|&b| {
                        if (0x20..0x7f).contains(&b) {
                            b as char
                        } else {
                            '.'
                        }
                    })
                    .collect();
                bsup!(
                    "binder: reply-head128 +{:3} {} |{}|",
                    ci * 32,
                    hexs.join(" "),
                    asc
                );
            }
        }
        // 0.9.135 telemetry: collide the descriptor's
        // source range against this thread's own
        // parcel records (see reply_source_collide) --
        // then file this reply itself as one of the
        // thread's send sources, in that order, so a
        // pop never collides with its own record.
        if data.len() >= 4 {
            reply_source_collide(st, arena, pid, claim_seq, daddr, &data);
        }
        if dsize >= 256 {
            record_send_src(
                st,
                pid,
                SendSrcRec {
                    daddr,
                    dsize,
                    code,
                    is_reply: true,
                    head: data[..data.len().min(64)].to_vec(),
                },
            );
        }
        // 0.9.129 c1/c2 separation, first half (telemetry
        // only): for large replies, name the guest
        // address the data was copied from. The re-read
        // half sits just before the shield4 judgement
        // below (delivery-adjacent); this line is what
        // covers replies that never reach it (shield3's
        // OOB return above all). Log only.
        if data.len() >= 256 {
            bsup!(
                "binder: reply-pop daddr claim_seq={claim_seq} replier={pid} daddr=0x{daddr:x} size={}",
                data.len()
            );
        }
        // The 0.9.100 concurrency line, kept truthful:
        // it now fires when this reply pairs while other
        // waits for the same arena are still outstanding
        // (shared queue plus Reply frames claimed on
        // other threads' stacks), and names the waiter
        // actually claimed -- concurrency is context now,
        // not the pairing mechanism.
        {
            let mut others = n_outstanding;
            for (tpid, stack) in st.serving.iter() {
                if stack.arena == arena && *tpid != pid {
                    others += stack
                        .groups
                        .iter()
                        .flat_map(|g| g.frames.iter())
                        .filter(|fr| matches!(fr, ServingFrame::Reply(..)))
                        .count();
                }
            }
            if others > 0 {
                bsup!(
                    "binder: reply pairing under concurrency: arena={arena} replier pid={pid} outstanding={} claimed waiter pid={}",
                    others + 1,
                    w.sender_pid
                );
            }
        }
        if oob {
            bsup!(
                "binder: shield3 dropped OOB reply pid={pid} dsize={} osize={}",
                data.len(),
                offs.len()
            );
            // 0.9.132: an intercept is the write-overlap
            // audit's trigger (telemetry only).
            write_audit_check(st, arena, pid, daddr, &data, "shield3", claim_seq);
            // 0.9.131: the intercept is an event in the
            // waiter's evidence ring (s9-130-swap-verify
            // Q4's open question (ii): what follows a
            // shield intercept in the same app).
            evidence_tag(
                st,
                &w.sender_arena,
                format!("shield3 size={} seq={claim_seq}", data.len()),
            );
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_FAILED_REPLY.to_le_bytes());
            }
            binder_maybe_wake(st, &w.sender_arena, actions);
            notes.push("REPLY with OOB object offset -> FAILED_REPLY (shield3)".to_string());
            return;
        }
        // 0.9.129 c1/c2 separation, second half (telemetry
        // only): for large replies, re-read the first word
        // at the copied-from address, delivery-adjacent.
        // A re-read that differs from the copy means the
        // replier's buffer moved under the supervisor's
        // segmented handling; agreement means whatever
        // the copy holds sat static in the replier's
        // memory (s9-128-substitution Q5). Read only: the
        // shield4 judgement below and the delivery after
        // it both use the copied bytes, never this value.
        if data.len() >= 256 {
            if let Some(v) = rd(pid, daddr as u64, 4) {
                let reread = u32_at(&v, 0);
                if reread != first_word {
                    bsup!(
                        "binder: reply reread differs seq={claim_seq} first=0x{first_word:x} reread=0x{reread:x}"
                    );
                }
            }
        }
        // 0.9.133 (telemetry only): the second read
        // above never covered small replies -- its
        // 256B floor left the 8B poison family (five of
        // the .132 run's eight intercepts) entirely
        // un-re-read, so for small poison the "garbage
        // sat static before our first read" verdict had
        // no evidence either way (s9-132-verify Q3).
        // At this same judgement-adjacent point, now
        // re-read the first min(size, 64B) of EVERY
        // judged reply and compare the whole span
        // against the copy: agreement extends the
        // pre-existing-corruption evidence to the small
        // family; a difference would put the read
        // window itself back under suspicion. A
        // differing span prints one line; agreement
        // only moves the settlement counters. Read
        // only -- the judgement below and the delivery
        // after it use the copied bytes, never this.
        if data.len() >= 4 {
            st.second_reads += 1;
            let span = data.len().min(64);
            if let Some(v) = rd(pid, daddr as u64, span) {
                let m = v.len().min(span);
                if m > 0 && v[..m] != data[..m] {
                    st.second_read_differs += 1;
                    let second = if v.len() >= 4 { u32_at(&v, 0) } else { 0 };
                    bsup!(
                        "binder: reply second-read differs seq={claim_seq} size={} first=0x{first_word:x} second=0x{second:x} span={span}",
                        data.len()
                    );
                }
            }
        }
        // 0.9.129 shield, fourth layer: a reply whose
        // first word is not a reply header at all is not
        // a reply. The 0.9.128 field run's three poisoned
        // replies (claim_seq 1040/1434/1618) were copied
        // verbatim from the replier's own memory at its
        // (daddr, dsize): the size was the honest size of
        // the call's real reply, the bytes were a native
        // memory slice (paired heap pointers, zeroes, a
        // libc address 0xafd4658c that cannot appear in
        // any wire parcel), while every honest reply in
        // the census began 0x0, 0xffffffff, a type
        // constant or a small integer -- never a pointer.
        // A waiter reading such a parcel takes the
        // pointer for an exception code and dies
        // (0.9.126's systemui). The faithful mirror of
        // the driver failing a bad copy: answer
        // FAILED_REPLY instead, exactly like shield3
        // above, and let the waiter unwind cleanly.
        // Judged on the copied bytes; a reply shorter
        // than 4B carries no first word and is never
        // judged.
        // 0.9.132: the judgement itself is now the
        // whitelist of shield4_legal_first (the two-range
        // blacklist it replaces leaked stack-domain and
        // string-fragment poison in .130/.131; see the
        // helper's comment). Judgement point, FAILED_REPLY
        // disposal and counting are otherwise unchanged.
        let poisoned = data.len() >= 4 && !shield4_legal_first(first_word);
        if poisoned {
            st.shield4_drops += 1;
            let bucket = shield4_bucket(first_word);
            match bucket {
                "cookie" => st.shield4_cookie += 1,
                "libc" => st.shield4_libc += 1,
                "stack" => st.shield4_stack += 1,
                _ => st.shield4_other += 1,
            }
            bsup!(
                "binder: shield4 poisoned reply dropped claim_seq={claim_seq} replier={pid} waiter={} size={} first=0x{first_word:x} bucket={bucket} -> FAILED_REPLY",
                w.sender_pid,
                data.len()
            );
            // 0.9.141 (P2): every poisoned pop -- not
            // just the handle-10 subset -- gets its
            // full head (first 128B of the copy in
            // hand, reply-head128 format), the 16
            // bytes in front of the buffer, and the
            // first word's class against the buffer's
            // own address (see poison_word0_class).
            // Judgement, disposal and the bucket
            // account above are untouched.
            let (w0class, w0idx) = poison_word0_class(first_word, daddr);
            st.poison_word0[w0idx] += 1;
            let show = data.len().min(128);
            bsup!(
                "binder: poison-head128 claim_seq={claim_seq} replier={pid} waiter={} handle={} code={} daddr=0x{daddr:x} size={} shown={show} word0_rel={w0class}",
                w.sender_pid, w.target_handle, w.code, data.len()
            );
            for (ci2, chunk) in data[..show].chunks(32).enumerate() {
                let hexs: Vec<String> =
                    chunk.iter().map(|b| format!("{b:02x}")).collect();
                let asc: String = chunk
                    .iter()
                    .map(|&b| {
                        if (0x20..0x7f).contains(&b) {
                            b as char
                        } else {
                            '.'
                        }
                    })
                    .collect();
                bsup!(
                    "binder: poison-head128 +{:3} {} |{}|",
                    ci2 * 32,
                    hexs.join(" "),
                    asc
                );
            }
            if daddr >= 16 {
                match rd(pid, (daddr - 16) as u64, 16) {
                    Some(pre) if pre.len() == 16 => bsup!(
                        "binder: poison-pre claim_seq={claim_seq} daddr=0x{daddr:x} pre=[0x{:08x} 0x{:08x} 0x{:08x} 0x{:08x}]",
                        u32_at(&pre, 0),
                        u32_at(&pre, 4),
                        u32_at(&pre, 8),
                        u32_at(&pre, 12)
                    ),
                    _ => bsup!(
                        "binder: poison-pre claim_seq={claim_seq} daddr=0x{daddr:x} pre=unreadable"
                    ),
                }
            } else {
                bsup!(
                    "binder: poison-pre claim_seq={claim_seq} daddr=0x{daddr:x} pre=unreadable"
                );
            }
            // 0.9.132: same write-overlap audit trigger
            // as shield3 (telemetry only).
            write_audit_check(st, arena, pid, daddr, &data, "shield4", claim_seq);
            // 0.9.131: same evidence-ring tag as shield3.
            evidence_tag(
                st,
                &w.sender_arena,
                format!(
                    "shield4 size={} first=0x{first_word:x} seq={claim_seq}",
                    data.len()
                ),
            );
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_FAILED_REPLY.to_le_bytes());
            }
            binder_maybe_wake(st, &w.sender_arena, actions);
            notes.push("POISONED REPLY -> FAILED_REPLY (shield4)".to_string());
            return;
        }
        let mut fd_fixups: Vec<(usize, i32)> = Vec::new();
        let tdata = binder_translate(st, arena, &w.sender_arena, &data, &offs, actions, &mut fd_fixups);
        // 0.9.133: photograph any FD objects this reply
        // carries before delivery (telemetry only; see
        // fd_obj_dump). The WMS -> systemui relayout
        // replies this exists for travel this path.
        if !fd_fixups.is_empty() {
            fd_obj_dump("reply", pid, &w.sender_arena, Some(w.sender_pid), w.code, &tdata, &fd_fixups);
        }
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
        let delivered_off = delivered.as_ref().ok().copied();
        let delivered_ok = delivered.is_ok();
        if let Err(why) = delivered {
            notes.push(format!("REPLY delivery failed: {why}"));
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_FAILED_REPLY.to_le_bytes());
            }
            // 0.9.131: the FAILED_REPLY answer is an
            // event in the waiter's evidence ring.
            evidence_tag(
                st,
                &w.sender_arena,
                format!("failed-reply size={} seq={claim_seq}", tdata.len()),
            );
        }
        binder_maybe_wake(st, &w.sender_arena, actions);
        bsup!(
            "binder: reply ({}B) delivered for waiter pid {}",
            tdata.len(),
            w.sender_pid
        );
        // 0.9.131: a successful delivery is an event in
        // the waiter's evidence ring (gated on
        // delivered_ok -- the line above prints either
        // way, the ring should not).
        if delivered_ok {
            evidence_tag(
                st,
                &w.sender_arena,
                format!("reply size={} seq={claim_seq} from={pid}", tdata.len()),
            );
        }
        // 0.9.124 telemetry: photograph any parcel this
        // pairing path actually sent out as a reply whose
        // size falls outside the honest reply set {4, 8,
        // 16} (s9-app-crash: FIFO pairing under
        // concurrency hands a waiter some other caller's
        // parcel and the receiver dies on the garbage
        // first word; the donor parcel's head bytes are
        // its fingerprint). Pairing, delivery and every
        // result stay byte-identical -- log only.
        if delivered_ok && !matches!(tdata.len(), 4 | 8 | 16) {
            bsup!(
                "binder: reply-pair dump waiter={} size={} head={} outstanding={}",
                w.sender_pid,
                tdata.len(),
                hex_head(&tdata, 32),
                n_outstanding
            );
        }
        // 0.9.127 telemetry: photograph every large
        // parcel actually delivered at reply position,
        // with the claim key of the wait it answered
        // (sender / node / code, the identity the serving
        // thread claimed it by) and the slot it landed in
        // (the allocation offset in the waiter's arena --
        // the key of that arena's used/parcels tables; the
        // allocator keeps no generation counter). The
        // 0.9.126 field run's one app-thread kill was a
        // 672B parcel delivered at reply position whose
        // first word was a cookie value (0x41dd91b0),
        // claimed cleanly, no miss / unmatched / dump --
        // its origin (arena slot recycling residue vs a
        // genuine transaction whose claim key collided)
        // could not be read back from that package. The
        // big-txn dump in binder_send_txn is the same
        // photograph on the transaction side, so the two
        // can be joined on (key_sender, key_node,
        // key_code, slot, head). Log only, after the
        // delivery above; nothing here feeds back.
        // 0.9.128: the line also carries the popped
        // frame's claim_seq, joining it to that claim's
        // claim dump and this delivery's reply-pop dump.
        if delivered_ok && tdata.len() >= 256 {
            let (kptr, kcookie) = claim_key_node(st, &w);
            bsup!(
                "binder: big-reply dump waiter={} size={} key_sender={} key_node=0x{kptr:x}/0x{kcookie:x} key_code={} claim_seq={claim_seq} slot={} head={}",
                w.sender_pid,
                tdata.len(),
                w.sender_pid,
                w.code,
                delivered_off.unwrap_or(0),
                hex_head(&tdata, 32)
            );
        }
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
            bsup!(
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
        st, actions, notes, arena, pid, target, cookie, nptr, ncookie, &owner, code, flags,
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
    actions: &mut Vec<BAction>,
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
        bsup!(
            "binder: txn detail from pid={pid} code={code} flags=0x{flags:x} offs={}B token='{tok}'",
            offs.len()
        );
        // 0.9.131 ignition forensics, trigger A: a
        // code-2 transaction on the IActivityManager
        // interface is a dying app's crash report (the
        // field census behind s9-130-swap-verify Q2:
        // every tenure's ignition anchors on one).
        // Print the sender's evidence ring BEFORE this
        // transaction is translated or delivered, so
        // the group shows the bind-family parcels and
        // intercepts that preceded the crash, not the
        // report itself. The parcel's own interface
        // token is the AMS identity here: binder nodes
        // carry no name registry in this driver, and
        // the token is what the caller itself declared.
        if code == 2 && tok == "android.app.IActivityManager" {
            // 0.9.140 (M4): the token is demoted to an
            // annotation on the trigger -- it is the
            // caller's own declaration, quoted, not the
            // identity the dump stands on.
            binder_ignition_dump(st, pid, &format!("crash-report token={tok}"));
        } else if code == 2 && tok.is_empty() {
            // 0.9.140 (M4): a code-2 transaction whose
            // interface token the heuristic above could
            // not extract at all. If this parcel is a
            // crash report whose shape defeated the
            // parse, trigger A missed it, and "no dump"
            // stops being proof of "no report" -- the
            // A' blind spot (s9-140-desk-ignition
            // section 3). Every such transaction is
            // named and counted into the arena-death
            // settlement, so a field run can convict or
            // clear the blind spot from the count. The
            // trigger widening the spec pairs with this
            // (code==2 addressed to a system_server
            // arena firing regardless of token) needs
            // an SS-arena identity the coordinator does
            // not hold -- no registry of it exists in
            // BinderState, and the tracer's candidate
            // knowledge never crosses -- so it is NOT
            // implemented in this build; see the 0.9.140
            // delivery notes.
            st.crash_token_miss += 1;
            bsup!(
                "binder: crash-report-token-miss from pid={pid} code=2 target_arena={owner} (token unparseable; trigger A blind spot)"
            );
        }
    }
    let mut fd_fixups: Vec<(usize, i32)> = Vec::new();
    let tdata = binder_translate(st, arena, &owner, &data, &offs, actions, &mut fd_fixups);
    // 0.9.133: same FD-object photograph on the
    // transaction path (telemetry only; see
    // fd_obj_dump). The receiving thread is chosen
    // inside delivery, so the recipient here is the
    // owner arena alone.
    if !fd_fixups.is_empty() {
        fd_obj_dump("txn", pid, &owner, None, code, &tdata, &fd_fixups);
    }
    let delivered = binder_deliver(
        st, &owner, BR_TRANSACTION, nptr, ncookie, code, flags, pid, veuid, &tdata, &offs,
        &fd_fixups,
        None,
    );
    let delivered_off = delivered.as_ref().ok().copied();
    if let Err(why) = delivered {
        if let Some(bp) = st.procs.get_mut(arena) {
            bp.push_to(pid, &BR_DEAD_REPLY.to_le_bytes());
        }
        // 0.9.131: the refusal is part of the sender's
        // ignition evidence (see PidEvidence).
        evidence_tag(
            st,
            arena,
            format!("dead-reply code={code} size={}", data.len()),
        );
        notes.push(format!("TRANSACTION target cannot receive ({why}) -> DEAD_REPLY"));
        return;
    }
    // 0.9.127 telemetry: the transaction-side mirror of
    // the big-reply dump in binder_handle_txn -- same
    // field set, so a large transaction parcel and a
    // large parcel delivered at reply position can be
    // joined on (key_sender, key_node, key_code, slot,
    // head). waiter= names the sending pid (the caller a
    // two-way call leaves waiting; the receiving thread
    // is only chosen inside delivery), slot= is the
    // allocation offset in the receiving (owner) arena.
    // Log only, after the delivery above.
    if tdata.len() >= 256 {
        bsup!(
            "binder: big-txn dump waiter={pid} size={} key_sender={pid} key_node=0x{nptr:x}/0x{ncookie:x} key_code={code} slot={} head={}",
            tdata.len(),
            delivered_off.unwrap_or(0),
            hex_head(&tdata, 32)
        );
        // 0.9.131: keep the parcel itself in the
        // receiving arena's ignition evidence ring --
        // the bind-family parcels this photographs are
        // exactly what an ignition dump needs verbatim
        // (s9-130-swap-verify Q4). Storage only; the
        // delivery above is already complete.
        evidence_big_txn(st, owner, code, pid, delivered_off.unwrap_or(0), &tdata);
    }
    // 0.9.131: every successful delivery leaves a
    // short tag in the receiving arena's evidence ring.
    evidence_tag(
        st,
        owner,
        format!("txn code={code} size={} from={pid}", tdata.len()),
    );
    if flags & TF_ONE_WAY == 0 {
        st.waiters.entry(owner.to_string()).or_default().push(ReplyWait {
            sender_pid: pid,
            sender_arena: arena.to_string(),
            cookie,
            target_handle: target,
            code,
        });
    }
    if let Some(bp) = st.procs.get_mut(arena) {
        // Kernel ordering: 81e7dc2 flushed the shared
        // inbound stream ahead of BR_REPLY (and ahead of
        // direct looper delivery), but the completion
        // word took the same two-queue shortcut it fixed
        // elsewhere: binder_translate queued this
        // transaction's reference notices into this
        // arena's inbound stream, yet the reads fill from
        // the sender's personal queue first, so a
        // one-way sender read BR_TRANSACTION_COMPLETE,
        // returned from transact and dropped the last
        // strong ref of the very object it had just sent
        // before reaching the pending BR_ACQUIRE, which
        // then incStrong'd a dead cookie (S-B). Drain
        // the stream into the sender's queue first, so
        // it reads [..., notices, TRANSACTION_COMPLETE].
        if !bp.inbound.is_empty() {
            let pending = std::mem::take(&mut bp.inbound);
            bp.push_to(pid, &pending);
            bsup!("binder: flushed pending inbound ahead of transaction-complete to pid={pid}");
        }
        bp.push_to(pid, &BR_TRANSACTION_COMPLETE.to_le_bytes());
    }
    binder_maybe_wake(st, &owner, actions);
    notes.push(format!("TRANSACTION code {code} -> node in {owner} ({}B)", tdata.len()));
}

/// Emulate one BINDER_WRITE_READ ioctl at its entry
/// stop: the decision half (S1a, coordinator-resident
/// since S1b). The caller pre-reads the ioctl's inputs
/// from the tracee -- the 24-byte bwr struct at
/// `bwr_addr`, and the write stream when the struct
/// says one follows (same condition the old inline
/// read used) -- sends them with the caller's virtual
/// euid (vcreds stays tracer-side this stage), and
/// executes the actions this returns at the stop, in
/// order. Everything the old body did to the tracee
/// (memory writes, the skip, the park, the inline
/// fd-fixup settle) is in the action list at the same
/// position it used to happen. Parcel payload reads
/// stay inside binder_handle_txn, behind the `rd`
/// reader: they gate the drop branches mid-decision,
/// so the coordinator asks the tracer for exactly
/// those bytes, when it reaches them, over the
/// protocol's reverse read channel.
#[allow(clippy::too_many_arguments)]
fn binder_write_read<R: FnMut(i32, u64, usize) -> Option<Vec<u8>>>(
    pid: i32,
    arena: &str,
    bwr_addr: u64,
    bwr: Option<Vec<u8>>,
    stream: Option<Vec<u8>>,
    st: &mut BinderState,
    veuid: u32,
    rd: &mut R,
    actions: &mut Vec<BAction>,
) -> String {
    let Some(bwr) = bwr else {
        actions.push(BAction::SkipSyscall(-14));
        return "binder WRITE_READ: bwr unreadable -> -EFAULT".to_string();
    };
    let ws = u32_at(&bwr, 0);
    let wc0 = u32_at(&bwr, 4);
    let wb = u32_at(&bwr, 8);
    let rs = u32_at(&bwr, 12);
    let rb = u32_at(&bwr, 20);
    let arena = arena.to_string();
    let mut notes: Vec<String> = Vec::new();
    if ws > wc0 && ws <= (1 << 20) {
        match stream {
            Some(stream) => {
                binder_process_stream(pid, &arena, &stream, st, veuid, rd, actions, &mut notes)
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
    // Never split a BR command across reads (see
    // br_prefix_len): fill only up to a command
    // boundary inside the reader's buffer; the rest
    // stays queued for its next read.
    let fill_n = if rs > 0 && queue_len > 0 {
        let peek = st
            .procs
            .get(&arena)
            .map(|p| p.peek_for(pid, rs as usize))
            .unwrap_or_default();
        br_prefix_len(&peek, rs as usize)
    } else {
        0
    };
    if fill_n > 0 {
        let bytes: Vec<u8> = st
            .procs
            .get_mut(&arena)
            .map(|bp| bp.drain_for(pid, fill_n).0)
            .unwrap_or_default();
        let bytes = shield_ref_pairs(st, &arena, pid, bytes);
        binder_claim_fills(st, &arena, pid, &bytes);
        dump_mgr_read(st, &arena, pid, &bytes);
        // 0.9.136: this fill's delivery VAs, taken before
        // the bytes move into the action list; the fd
        // fixup selection below keys off them.
        let fill_vas = stream_data_vas(&bytes);
        let filled = bytes.len();
        actions.push(BAction::WriteMem {
            addr: rb as u64,
            bytes,
        });
        actions.push(BAction::WriteMem {
            addr: bwr_addr,
            bytes: writeback(filled as u32).to_vec(),
        });
        actions.push(BAction::SkipSyscall(0));
        // Deliveries in this fill may have left fd
        // fixups unresolved. They are normally settled
        // when the receiver is woken out of a park; a
        // thread that finds its reply already queued on
        // entry never parks, and would go on to read the
        // parcel with the senders' raw fds still in it
        // (a received heap's client-side mmap then fails
        // on a foreign fd). Settle them now, while this
        // call sits in the same skipped state the parked
        // path resolves from: rides consume this call's
        // entry->exit transition, so the fake result is
        // applied to the regs by the executor and the
        // caller drops its exit-stop expectation (it keys
        // that off pend.applied). 0.9.136: only the
        // fixups whose deliveries THIS fill carries are
        // settled here (see take_fixups_for); a fixup for
        // a still-queued delivery stays pending for that
        // delivery's own fill or wake.
        if let Some((_, fixups, cache)) = take_fixups_for(st, &arena, &fill_vas) {
            actions.push(BAction::ResolveFdFixupsInline {
                arena: arena.clone(),
                fixups,
                cache,
            });
        }
        notes.push(format!("read filled {}B", filled));
    } else if rs > 0 {
        actions.push(BAction::SkipSyscall(0));
        actions.push(BAction::Park {
            pid,
            park: ParkedIoctl {
                bwr: bwr_addr as u32,
                read_buf: rb,
                read_size: rs,
                write_consumed: ws,
            },
        });
        actions.push(BAction::MarkBinderParked);
        notes.push("parked awaiting work".to_string());
    } else {
        actions.push(BAction::WriteMem {
            addr: bwr_addr,
            bytes: writeback(0).to_vec(),
        });
        actions.push(BAction::SkipSyscall(0));
    }
    if notes.is_empty() {
        notes.push("no work".to_string());
    }
    format!("binder WRITE_READ pid={pid} [{}]", notes.join("; "))
}

/// Length of the longest prefix of a BR command stream
/// that ends on a command boundary and fits in `cap`.
/// A real binder driver never splits a command across
/// reads; our byte-granular drains did, and GB
/// servicemanager's 128-byte read buffer made the flaw
/// fatal: three flushed transactions (132B) arrived in
/// one read, the third was cut 4 bytes short, and its
/// binder_parse returned "txn too small" -- the
/// manager's clean exit(0) after serving flushed work
/// (0.9.26/0.9.29 device runs). Deliveries must be
/// cut only between commands.
fn br_one_len(cmd: u32) -> usize {
    match cmd {
        BR_TRANSACTION | BR_REPLY => 44,
        BR_INCREFS | BR_ACQUIRE | 0x8008_7209 | 0x8008_720a => 12,
        BR_DEAD_BINDER | BR_CLEAR_DEATH_NOTIFICATION_DONE | 0x8000_7200 => 8,
        _ => 4,
    }
}

fn br_prefix_len(bytes: &[u8], cap: usize) -> usize {
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(bytes, off);
        let len = br_one_len(cmd);
        if off + len > cap || off + len > bytes.len() {
            break;
        }
        off += len;
    }
    off
}

/// 0.9.141 (P3): count the BR_TRANSACTION commands
/// in a delivered fill (the serving-depth input to
/// the window profile). Walks with br_one_len; an
/// unknown command ends the count, as elsewhere.
fn count_br_transactions(bytes: &[u8]) -> u32 {
    // The fills counted here are batches the
    // supervisor itself assembled, so every command
    // in them is one br_one_len knows.
    let mut n = 0u32;
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(bytes, off);
        if cmd == BR_TRANSACTION {
            n += 1;
        }
        off += br_one_len(cmd);
    }
    n
}

/// 0.9.125: claim the transactions in a read fill for
/// the thread consuming them. Every BR_TRANSACTION the
/// supervisor hands a thread moves that transaction's
/// reply wait out of the shared per-arena queue and onto
/// the thread's own serving stack, keyed by the
/// identity the parcel itself carries: (sender pid,
/// target node, code) against the wait recorded at send
/// time -- so the thread's later BC_REPLY is paired
/// with the transaction it actually executed, the
/// kernel's per-thread transaction-stack routing.
/// Frames are pushed in stream order, grouped per
/// fill (0.9.130, see ServingStack); one-way
/// transactions and unclaimable parcels push Other so
/// the stack's depth keeps matching what the thread
/// executed. A claim miss leaves the wait in the shared
/// queue (it can still be claimed by a later parcel of
/// the same identity, or failed at arena death) and is
/// logged -- it means the send-side wait record and
/// the fill-side parcel disagreed, which should not
/// happen and must not pass silently.
fn binder_claim_fills(st: &mut BinderState, arena: &str, pid: i32, bytes: &[u8]) {
    // 0.9.130: this call IS one fill (both call sites
    // hand over exactly one command-boundary-cut fill),
    // so the group id is a per-call lazy allocation:
    // taken at the fill's first transaction -- every
    // transaction pushes exactly one frame below, so an
    // allocated id always names a real group, and a
    // fill carrying no transaction burns no id.
    let mut fill_id: Option<u64> = None;
    let mut i = 0usize;
    while i + 4 <= bytes.len() {
        let cmd = u32_at(bytes, i);
        let adv = br_one_len(cmd);
        if adv < 4 || i + adv > bytes.len() {
            break;
        }
        if cmd == BR_TRANSACTION {
            let fid = match fill_id {
                Some(f) => f,
                None => {
                    st.fill_seq += 1;
                    fill_id = Some(st.fill_seq);
                    st.fill_seq
                }
            };
            let tptr = u32_at(bytes, i + 4);
            let tcookie = u32_at(bytes, i + 8);
            let code = u32_at(bytes, i + 12);
            let flags = u32_at(bytes, i + 16);
            let sender_pid = u32_at(bytes, i + 20) as i32;
            // 0.9.135 telemetry: where the fill's own
            // descriptor says this parcel sits in the
            // reader's address space, and how large --
            // kept for the collision ring record below.
            let pva = u32_at(bytes, i + 36);
            let psz = u32_at(bytes, i + 28) as usize;
            let mut frame = ServingFrame::Other;
            // 0.9.128 telemetry: the claimed wait's key
            // scalars and its frame's claim sequence
            // number, copied out before the wait moves
            // into the frame (claim dump after the push).
            let mut claimed_key: Option<(u64, i32, String, u32, u32, u32, u32)> = None;
            if flags & TF_ONE_WAY == 0 {
                let sender_arena = st.thread_arena.get(&sender_pid).cloned();
                let node_idx = st.nodes.iter().position(|n| {
                    n.owner == arena && n.ptr == tptr && n.cookie == tcookie
                });
                let qpos = match (sender_arena, node_idx) {
                    (Some(sa), Some(ni)) => st.waiters.get(arena).and_then(|q| {
                        q.iter().position(|w| {
                            if w.sender_pid != sender_pid
                                || w.sender_arena != sa
                                || w.code != code
                            {
                                return false;
                            }
                            if st
                                .procs
                                .get(&w.sender_arena)
                                .and_then(|bp| bp.handles.get(&w.target_handle))
                                .copied()
                                == Some(ni)
                            {
                                return true;
                            }
                            // Context-manager lane (0.9.126):
                            // a transaction addressed to
                            // handle 0 is routed send-side
                            // through mgr_node and its wait
                            // recorded with target_handle 0,
                            // but handle 0 is never stored in
                            // any handles map (it is the
                            // manager in every process), so
                            // the resolution above can never
                            // name the manager node and
                            // 0.9.125 missed every
                            // ServiceManager self-transaction
                            // (6/6 on device; the callers
                            // froze inside transact). Bind
                            // this lane on the transaction's
                            // own identity only: the parcel
                            // target is the manager node
                            // itself (0/0), the resolved node
                            // IS the registered manager node,
                            // the reader arena IS the
                            // manager's, and the wait was
                            // recorded against handle 0.
                            // General node targets gain
                            // nothing from this lane.
                            w.target_handle == 0
                                && tptr == 0
                                && tcookie == 0
                                && st.mgr_node == Some(ni)
                                && st.mgr_arena.as_deref() == Some(arena)
                        })
                    }),
                    _ => None,
                };
                match qpos {
                    Some(j) => {
                        let w = st.waiters.get_mut(arena).unwrap().remove(j);
                        // 0.9.128: stamp the frame with
                        // the next claim sequence number
                        // and keep the wait's key for the
                        // claim dump (node resolved by the
                        // same helper the big-reply dump
                        // uses, so the two lines join).
                        st.claim_seq += 1;
                        let (kptr, kcookie) = claim_key_node(st, &w);
                        claimed_key = Some((
                            st.claim_seq,
                            w.sender_pid,
                            // 0.9.131: the waiter's arena,
                            // carried for the evidence-ring
                            // tags at the claim dump below
                            // (telemetry only, like the
                            // rest of this tuple).
                            w.sender_arena.clone(),
                            kptr,
                            kcookie,
                            w.code,
                            w.target_handle,
                        ));
                        frame = ServingFrame::Reply(w, st.claim_seq);
                    }
                    None => {
                        bsup!(
                            "binder: reply-claim miss: reader pid={pid} arena={arena} sender pid={sender_pid} code={code} target=0x{tptr:x}/0x{tcookie:x} (wait stays queued)"
                        );
                    }
                }
            }
            let stack = st.serving.entry(pid).or_insert_with(|| ServingStack {
                arena: arena.to_string(),
                groups: Vec::new(),
            });
            // 0.9.130: this fill's frames form the top
            // group, in claim order. Open the group at
            // the fill's first frame; later frames of
            // the same fill (same fid on top) append.
            if stack.groups.last().map_or(true, |g| g.fill_id != fid) {
                stack.groups.push(ServingGroup {
                    fill_id: fid,
                    frames: Vec::new(),
                });
            }
            stack.groups.last_mut().unwrap().frames.push(frame);
            // 0.9.128 telemetry: photograph the claim
            // event itself -- the fill entry's own read
            // identity (sender / target / code exactly as
            // read out of the BR_TRANSACTION) beside the
            // key of the wait it claimed, the serving
            // thread and its stack depth after the push.
            // The 0.9.127 dumps record only the claimed
            // wait's key and the delivered parcel's head,
            // never the fill entry that triggered the
            // claim, so fill-claim aliasing, a wrong-frame
            // pop and replier-side buffer aliasing could
            // not be separated (s9-127-big-reply Q5).
            // Log only; the push above is the last state
            // change in this iteration either way.
            // 0.9.135: the claim sequence this parcel
            // took, copied before the dump below moves
            // the key (for the collision ring record).
            let claimed_seq = claimed_key.as_ref().map(|k| k.0);
            if let Some((seq, wsender, wsarena, kptr, kcookie, wcode, whandle)) = claimed_key {
                bsup!(
                    "binder: claim dump claim_seq={seq} fill_id={fid} reader={pid} arena={arena} fill_sender={sender_pid} fill_target=0x{tptr:x}/0x{tcookie:x} fill_code={code} wait_sender={wsender} wait_node=0x{kptr:x}/0x{kcookie:x} wait_code={wcode} wait_handle={whandle} depth={}",
                    stack.depth()
                );
                // 0.9.131: the claim is an event in both
                // parties' evidence rings -- the waiter's
                // (its call is now being served) and the
                // reader's (it took the call on).
                evidence_tag(
                    st,
                    &wsarena,
                    format!("claim code={wcode} seq={seq} by={pid}"),
                );
                evidence_tag(
                    st,
                    arena,
                    format!("serve code={wcode} seq={seq} for={wsender}"),
                );
            }
            // 0.9.135 telemetry: file the parcel in the
            // reader's collision ring (see
            // ClaimParcelRec) -- every transaction the
            // fill carried, claimed or not, under the
            // claim identity it took. Prints nothing;
            // the reply-source collision check reads
            // the ring back at this thread's reply pops.
            record_claim_parcel(
                st,
                pid,
                ClaimParcelRec {
                    seq: claimed_seq,
                    fill_id: fid,
                    va: pva,
                    size: psz,
                    code,
                    sender_pid,
                },
            );
        }
        i += adv;
    }
}

/// 0.9.103 shield (user's call: intercept the bad
/// reference before the receiver can consume it).
/// Validate every BR_INCREFS / BR_ACQUIRE pair in an
/// assembled batch against the node registry: a pair is
/// deliverable only if it names a LIVE node owned by the
/// batch's own arena -- exactly the (ptr, obj) words
/// binder_notify_ref queued it from. Anything else
/// (unknown pair, or a dead node's pair: delivering it
/// makes the guest incStrong freed memory, the crash
/// shape itself) is cut out of the batch whole -- 12B
/// command units, so the stream stays aligned -- and
/// logged. The walk uses the same length table as
/// br_prefix_len; a truncated tail is delivered as-is.
fn shield_ref_pairs(
    st: &mut BinderState,
    arena: &str,
    pid: i32,
    bytes: Vec<u8>,
) -> Vec<u8> {
    if bytes.len() < 12 {
        return bytes;
    }
    let mut live: std::collections::HashSet<(u32, u32)> =
        std::collections::HashSet::new();
    let mut known: std::collections::HashSet<(u32, u32)> =
        std::collections::HashSet::new();
    for n in &st.nodes {
        if n.owner == arena {
            known.insert((n.ptr, n.cookie));
            if !n.dead {
                live.insert((n.ptr, n.cookie));
            }
        }
    }
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(&bytes, off);
        let len = br_one_len(cmd);
        if off + len > bytes.len() {
            break;
        }
        if cmd == BR_INCREFS || cmd == BR_ACQUIRE {
            let a = u32_at(&bytes, off + 4);
            let b = u32_at(&bytes, off + 8);
            if !live.contains(&(a, b)) {
                let why = if known.contains(&(a, b)) {
                    "dead node"
                } else {
                    "no such node"
                };
                st.shield_drops += 1;
                bsup!(
                    "binder: shield dropped ref pair for pid={pid}: op=0x{cmd:x} a=0x{a:x} b=0x{b:x} ({why})"
                );
                off += len;
                continue;
            }
        }
        out.extend_from_slice(&bytes[off..off + len]);
        off += len;
    }
    if off < bytes.len() {
        out.extend_from_slice(&bytes[off..]);
    }
    out
}

/// Strict batch shape check for shield_live_pairs: the
/// buffer walks end-to-end on known BR opcodes only and
/// contains at least one REF pair.
fn ref_batch_qualifies(bytes: &[u8]) -> bool {
    if bytes.len() < 12 {
        return false;
    }
    let mut off = 0usize;
    let mut has_ref = false;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(bytes, off);
        match cmd {
            BR_TRANSACTION
            | BR_REPLY
            | BR_INCREFS
            | BR_ACQUIRE
            | 0x8008_7209
            | 0x8008_720a
            | BR_DEAD_BINDER
            | BR_CLEAR_DEATH_NOTIFICATION_DONE
            | 0x8000_7200
            | BR_DEAD_REPLY
            | BR_TRANSACTION_COMPLETE => {}
            _ => return false,
        }
        if cmd == BR_INCREFS || cmd == BR_ACQUIRE {
            has_ref = true;
        }
        let len = br_one_len(cmd);
        if off + len > bytes.len() {
            return false;
        }
        off += len;
    }
    off == bytes.len() && has_ref
}

/// 0.9.107 shield, second layer (worker side, at the two
/// fill applications): validate each REF pair's referent
/// by the bidirectional RefBase link, the only form of
/// the invariant that holds for every object layout:
/// word at refs+8 (weakref_impl::mBase) names the
/// RefBase subobject, and the word at mBase+4 (the
/// subobject's mRefs, per getWeakRefs = ldr [r0, #4])
/// must point back at refs. 0.9.106 compared mBase to
/// the pair's obj word directly, which is only valid
/// when the RefBase subobject sits at offset 0 of the
/// outer object -- BnInterface-style multiple
/// inheritance (SurfaceFlinger's own service object:
/// mBase = obj + 0x2dc) failed en masse (120 false
/// drops). Layout offsets are from the donor GB
/// libutils.so: mStrong +0, mWeak +4, mBase +8 in
/// weakref_impl (0.9.104 read +12 = mFlags and killed
/// everything; that attempt was removed in 0.9.105).
/// A pair whose link does not close, or whose memory
/// is unmapped, is cut whole and logged.
/// 0.9.120 adds a passive probe beside the check:
/// each pair that passes also has the word at refs+0
/// (weakref_impl::mStrong, same donor layout) read
/// and classified, and a pair whose referent's
/// strong count is already zero -- or whose memory
/// cannot be read -- is reported to the coordinator
/// as a shield-cookie suspect. The probe never
/// drops: it exists to count how often a pair the
/// link check waves through names an object the
/// guest side has already destroyed.
fn shield_live_pairs(pid: i32, bytes: Vec<u8>, coord: &mut CoordClient) -> Vec<u8> {
    if !ref_batch_qualifies(&bytes) {
        return bytes;
    }
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    // 0.9.120: per-batch verdict cache for the
    // mStrong probe below, keyed by (ptr, cookie):
    // the INCREFS and the ACQUIRE of one pair name
    // the same referent, so a suspect pair is
    // reported once per batch, not twice.
    let mut probe_cache: HashMap<(u32, u32), Option<&'static str>> = HashMap::new();
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(&bytes, off);
        let len = br_one_len(cmd);
        if cmd == BR_INCREFS || cmd == BR_ACQUIRE {
            let a = u32_at(&bytes, off + 4);
            let b = u32_at(&bytes, off + 8);
            let mbase = read_mem_vec(pid, (a as u64) + 8, 4)
                .map(|v| u32::from_le_bytes(v[0..4].try_into().unwrap()));
            let backref = mbase.and_then(|m| {
                read_mem_vec(pid, (m as u64) + 4, 4)
                    .map(|v| u32::from_le_bytes(v[0..4].try_into().unwrap()))
            });
            if backref != Some(a) {
                sup!(
                    "binder: shield2 dropped stale ref pair pid={pid}: op=0x{cmd:x} a=0x{a:x} b=0x{b:x} mbase={} backref={}",
                    mbase
                        .map(|m| format!("0x{m:x}"))
                        .unwrap_or_else(|| "<unmapped>".to_string()),
                    backref
                        .map(|m| format!("0x{m:x}"))
                        .unwrap_or_else(|| "<unmapped>".to_string())
                );
                off += len;
                continue;
            }
            // 0.9.120 probe (telemetry only -- the
            // pair is delivered either way): the link
            // check above validates the weakref half
            // of the referent, which by design
            // outlives the object; read the word it
            // is blind to, weakref_impl::mStrong at
            // ptr+0 (donor libutils layout, see the
            // function comment). Zero means the
            // object's own strong count is already
            // gone -- the referent is a husk the
            // guest is about to dereference through
            // the cookie. An unreadable word is
            // reported the same way. Every other
            // value (1.. or INITIAL_STRONG_VALUE) is
            // unremarkable and stays silent.
            if !probe_cache.contains_key(&(a, b)) {
                let verdict = match read_mem_vec(pid, a as u64, 4) {
                    Some(v) => {
                        let mstrong = u32::from_le_bytes(v[0..4].try_into().unwrap());
                        if mstrong == 0 {
                            Some("strong-zero")
                        } else {
                            None
                        }
                    }
                    None => Some("unreadable"),
                };
                probe_cache.insert((a, b), verdict);
                if let Some(why) = verdict {
                    coord.oneway_shield_cookie_suspect(pid, a, b, why);
                }
            }
        }
        out.extend_from_slice(&bytes[off..off + len]);
        off += len;
    }
    out
}

/// One-shot latch for the success-side VMA sample.
static MPROT_OK_SAMPLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Name the VMA containing `addr` in tracee `pid`:
/// its perms and backing path from /proc/<pid>/maps.
/// Telemetry for the mprotect refusals (0.9.31): the
/// host keeps denying PROT_EXEC on the pixelflinger
/// mspace VMA even when the mapping is born RWX, while
/// other file VMAs in the same process take the same
/// call -- this names what the denied VMA actually is.
fn vma_desc(pid: i32, addr: u64) -> String {
    let Ok(maps) = std::fs::read_to_string(format!("/proc/{pid}/maps")) else {
        return "<maps unreadable>".to_string();
    };
    for line in maps.lines() {
        let mut it = line.split_whitespace();
        let Some(range) = it.next() else { continue };
        let Some((lo, hi)) = range.split_once('-') else { continue };
        let lo = u64::from_str_radix(lo, 16).unwrap_or(0);
        let hi = u64::from_str_radix(hi, 16).unwrap_or(0);
        if addr >= lo && addr < hi {
            let perms = it.next().unwrap_or("????");
            let path = it.nth(3).unwrap_or("");
            return format!("{perms} {}", if path.is_empty() { "[anon]" } else { path });
        }
    }
    "<no vma>".to_string()
}

/// The VMA containing `addr` in tracee `pid` as
/// (lo, hi, perms, path); None when unmapped.
fn vma_range(pid: i32, addr: u64) -> Option<(u64, u64, String, String)> {
    let maps = std::fs::read_to_string(format!("/proc/{pid}/maps")).ok()?;
    for line in maps.lines() {
        let mut it = line.split_whitespace();
        let range = it.next()?;
        let (lo, hi) = range.split_once('-')?;
        let lo = u64::from_str_radix(lo, 16).ok()?;
        let hi = u64::from_str_radix(hi, 16).ok()?;
        if addr >= lo && addr < hi {
            let perms = it.next()?.to_string();
            let path = it.nth(3).unwrap_or("").to_string();
            return Some((lo, hi, perms, path));
        }
    }
    None
}

/// Ride an anonymous MAP_FIXED mmap over [addr,
/// addr+len) in the stopped tracee, in the style of
/// inject_openat: overwrite the current syscall's
/// registers, run it to its exit stop, report the
/// result. Consumes the caller's entry->exit
/// transition exactly like a fixup ride.
fn inject_mmap(
    pid: i32,
    compat: bool,
    addr: u64,
    len: u64,
    prot: u64,
    regs: &mut Regs,
) -> i64 {
    let nr_mmap: u64 = if compat { 192 } else { 222 };
    regs.set_nr(nr_mmap);
    regs.set_arg(0, addr);
    regs.set_arg(1, len);
    regs.set_arg(2, prot);
    regs.set_arg(3, 0x32); // MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS
    regs.set_arg(4, (-1i32) as i64 as u64);
    regs.set_arg(5, 0);
    if !set_regs(pid, regs) {
        return -1;
    }
    if !set_syscallno(pid, nr_mmap as i32) {
        return -1;
    }
    cont_syscall(pid, 0);
    match wait_one_syscall_stop(pid) {
        Some(()) => match get_regs(pid, compat) {
            Some(r) => {
                *regs = r;
                r.retval()
            }
            None => -1,
        },
        None => -1,
    }
}

/// The SELinux context of a process (self when
/// pid <= 0), for the same telemetry: if the denied
/// files' creator runs in another domain, it shows.
fn selinux_ctx(pid: i32) -> String {
    let p = if pid <= 0 {
        "/proc/self/attr/current".to_string()
    } else {
        format!("/proc/{pid}/attr/current")
    };
    std::fs::read_to_string(p)
        .map(|s| s.trim_end_matches(['\0', '\n']).to_string())
        .unwrap_or_else(|_| "<ctx unreadable>".to_string())
}

/// Telemetry (0.9.27): when the context manager itself is
/// handed read bytes, name the command words. GB
/// servicemanager exits its loop (and the process) on
/// specific BR codes -- a stray BR_REPLY, BR_DEAD_REPLY
/// or a truncated stream would each explain the
/// manager's clean exit(0) after serving flushed work in
/// the 0.9.26 device run; this names which one it ate.
fn dump_mgr_read(st: &BinderState, arena: &str, pid: i32, bytes: &[u8]) {
    let mut cmds: Vec<String> = Vec::new();
    let mut off = 0usize;
    while off + 4 <= bytes.len() && cmds.len() < 10 {
        let c = u32_at(bytes, off);
        match c {
            BR_TRANSACTION | BR_REPLY => {
                if off + 44 <= bytes.len() {
                    cmds.push(format!(
                        "TXN code={} ds={} os={}",
                        u32_at(bytes, off + 12),
                        u32_at(bytes, off + 28),
                        u32_at(bytes, off + 32)
                    ));
                } else {
                    cmds.push("TXN?".into());
                }
                off += 44;
            }
            BR_INCREFS | BR_ACQUIRE | 0x8008_7209 | 0x8008_720a => {
                if off + 12 <= bytes.len() {
                    cmds.push(format!(
                        "REF {c:#x} a=0x{:x} b=0x{:x}",
                        u32_at(bytes, off + 4),
                        u32_at(bytes, off + 8)
                    ));
                } else {
                    cmds.push("REF?".into());
                }
                off += 12;
            }
            BR_DEAD_BINDER | BR_CLEAR_DEATH_NOTIFICATION_DONE | 0x8000_7200 => {
                cmds.push(format!("{c:#010x}"));
                off += 8;
            }
            _ => {
                cmds.push(format!("{c:#010x}"));
                off += 4;
            }
        }
    }
    bsup!(
        "binder: read for pid={pid}: {}B cmds=[{}]",
        bytes.len(),
        cmds.join(", ")
    );
    let nw = bytes.len() / 4;
    let show = nw.min(128);
    let mut words: Vec<String> = Vec::with_capacity(show);
    for i in 0..show {
        words.push(format!("{:08x}", u32_at(bytes, i * 4)));
    }
    bsup!(
        "binder: hex for pid={pid}: w=[{}]{}",
        words.join(" "),
        if nw > show { " .." } else { "" }
    );
    // 0.9.99 parcel fingerprint verification: for every
    // transaction this batch hands to the reader, re-read
    // the parcel from the arena file and compare it with
    // the fingerprint taken at delivery. A mismatch means
    // the parcel changed in flight -- the class of fault
    // that surfaces in the guest as a crash on a pointer
    // no byte stream ever carried.
    let Some(bp) = st.procs.get(arena) else { return };
    let Some(base) = bp
        .base
        .get(&pid)
        .copied()
        .or_else(|| bp.base.values().next().copied())
    else {
        return;
    };
    let mut voff = 0usize;
    while voff + 4 <= bytes.len() {
        let c = u32_at(bytes, voff);
        let step = match c {
            BR_TRANSACTION | BR_REPLY => 44,
            BR_INCREFS | BR_ACQUIRE | 0x8008_7209 | 0x8008_720a => 12,
            BR_DEAD_BINDER | BR_CLEAR_DEATH_NOTIFICATION_DONE | 0x8000_7200 => 8,
            _ => 4,
        };
        if (c == BR_TRANSACTION || c == BR_REPLY) && voff + 44 <= bytes.len() {
            let aoff = u32_at(bytes, voff + 36).wrapping_sub(base);
            if let Some(pp) = bp.parcels.get(&aoff) {
                use std::os::unix::fs::FileExt;
                let mut img = vec![0u8; pp.total as usize];
                if bp.file.read_exact_at(&mut img, aoff as u64).is_ok() {
                    for &w in &pp.mask {
                        let at = (w as usize) * 4;
                        if at + 4 <= img.len() {
                            img[at..at + 4].copy_from_slice(&[0, 0, 0, 0]);
                        }
                    }
                    if crc32(&img) != pp.crc {
                        let now_head: Vec<String> = (0..8)
                            .filter(|&i| (i + 1) * 4 <= img.len())
                            .map(|i| format!("{:08x}", u32_at(&img, i * 4)))
                            .collect();
                        let old_head: Vec<String> =
                            pp.head.iter().map(|w| format!("{w:08x}")).collect();
                        bsup!(
                            "binder: CLOBBER pid={pid} arena={arena} off={aoff} stored_head=[{}] now_head=[{}]",
                            old_head.join(" "),
                            now_head.join(" ")
                        );
                    }
                }
            }
        }
        voff += step;
    }
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

/// 0.9.139 (s9-138-verify Q2/Q5): is the 4-byte word at
/// `addr` in the tracee an svc instruction? The rewind
/// landing is only released once this proves the tracee
/// will re-execute an svc there. A32 form: bits 27..24
/// are 1111 (the SWI/SVC encoding space, any cond/imm).
/// A64 form: SVC is 1101 0100 000 imm16 00001.
fn svc_anchor_ok(pid: i32, compat: bool, addr: u64) -> bool {
    let mut b = [0u8; 4];
    if read_mem(pid, addr, &mut b) != Ok(4) {
        return false;
    }
    let w = u32::from_le_bytes(b);
    if compat {
        w & 0x0F00_0000 == 0x0F00_0000
    } else {
        w & 0xFFE0_001F == 0xD400_0001
    }
}

/// Run one syscall inside a tracee stopped at a syscall
/// stop and return its result (or a negative value). The
/// first ride uses the stop we are already sitting on;
/// later rides rewind the PC to the svc instruction and
/// drive entry+exit privately. On return `regs` holds
/// the exit-stop registers of the injected call.
#[allow(clippy::too_many_arguments)]
fn inject_syscall(
    pid: i32,
    compat: bool,
    nr: u64,
    args: [u64; 4],
    entry_pc: u64,
    rewind: bool,
    regs: &mut Regs,
    raw_r0: &mut Option<i64>,
) -> i64 {
    if rewind {
        // 0.9.139 (s9-138-verify Q2/Q5): entry_pc comes
        // from the parked syscall-entry stop, whose pc
        // has already advanced PAST the svc (svc+4 -- the
        // exception link register semantics on both
        // personalities). Rewinding to entry_pc itself
        // therefore never re-executed the svc: the tracee
        // ran its stub epilogue on the injected args, then
        // its own clock_gettime/writev, and the ride's
        // two-stop budget harvested those (13/13 in the
        // .138 photographs). Land on the svc itself
        // (entry_pc - 4) and prove the landing before
        // releasing: if the word there is not an svc
        // encoding, fail this obtain honestly instead of
        // releasing the tracee into the wrong instruction.
        let landing = entry_pc.saturating_sub(4);
        if !svc_anchor_ok(pid, compat, landing) {
            sup!(
                "binder: fd injection rewind-anchor-bad pid={pid} nr={nr} entry_pc=0x{entry_pc:x} landing=0x{landing:x}; obtain aborted"
            );
            return -1;
        }
        regs.set_pc(landing);
    }
    regs.set_nr(nr);
    for (i, a) in args.iter().enumerate() {
        regs.set_arg(i, *a);
    }
    if !set_regs(pid, regs) {
        return -1;
    }
    if !set_syscallno(pid, nr as i32) {
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
                            // 0.9.141 (S3.3): the one
                            // place a return value is
                            // the guest's own r0 --
                            // every other return path
                            // of this function is a
                            // synthetic -1, and the fd
                            // telemetry's errno field
                            // must never wear a
                            // synthetic value as the
                            // kernel's.
                            *raw_r0 = Some(r.retval());
                            return r.retval();
                        }
                        None => return -1,
                    }
                }
                // A rewind ride's intermediate entry
                // stop: the kernel has loaded the
                // dispatch number by now, and the
                // guardrail below reads it before
                // continuing past the stop.
                let entry_sysno = get_syscallno(pid);
                // 0.9.139 guardrail (s9-138-verify Q5):
                // if the number loaded at this entry stop
                // provably is not the one this ride
                // injected, the stops ahead belong to a
                // guest syscall, not to our call -- fail
                // the obtain here rather than harvesting
                // its exit as our candidate. (An unreadable
                // syscallno proves nothing and keeps the
                // pre-.139 path.)
                if let Some(n) = entry_sysno {
                    if n != nr as i32 {
                        sup!(
                            "binder: fd injection ride-entry-mismatch pid={pid} nr={nr} entry_sysno={n}; obtain aborted"
                        );
                        return -1;
                    }
                }
                cont_syscall(pid, 0);
            }
            None => return -1,
        }
    }
}

/// 0.9.139 (s9-137-desk / s9-138-verify Q5): the access
/// mode to open the sender's fd with, read host-side
/// from the sender's fdinfo flags (the low two bits are
/// O_ACCMODE). A real binder driver's delivered fd
/// shares the sender's struct file, so its direction is
/// the sender's: the read end of a pipe is read-only,
/// the write end write-only. Opening everything O_RDWR
/// (the pre-.139 shape) silently downgrades the
/// channel-teardown detection (EOF/POLLHUP/EPIPE) that
/// keys off the delivered end's direction. Falls back
/// to O_RDWR when the mode cannot be read or is O_RDWR
/// itself.
fn sender_fd_open_flags(sender_pid: i32, sender_fd: i32) -> u64 {
    const O_RDWR: u64 = 2;
    let Ok(info) = std::fs::read_to_string(format!("/proc/{sender_pid}/fdinfo/{sender_fd}"))
    else {
        return O_RDWR;
    };
    for line in info.lines() {
        if let Some(v) = line.strip_prefix("flags:") {
            if let Ok(flags) = u64::from_str_radix(v.trim(), 8) {
                return match flags & 0o3 {
                    0 => 0, // O_RDONLY
                    1 => 1, // O_WRONLY
                    _ => O_RDWR,
                };
            }
        }
    }
    O_RDWR
}

/// inject_syscall specialised to the fixup resolver's
/// founding call: openat an already-scratch-written
/// "/proc/<sender>/fd/<n>" path in the receiver.
fn inject_openat(
    pid: i32,
    compat: bool,
    path_addr: u64,
    entry_pc: u64,
    rewind: bool,
    regs: &mut Regs,
    sender_pid: i32,
    sender_fd: i32,
) -> (i64, Option<i64>) {
    let nr_openat: u64 = if compat { 322 } else { 56 };
    let flags = sender_fd_open_flags(sender_pid, sender_fd);
    let mut raw = None;
    let r = inject_syscall(
        pid,
        compat,
        nr_openat,
        [(-100i32) as i64 as u64, path_addr, flags, 0], // AT_FDCWD, path, flags, mode
        entry_pc,
        rewind,
        regs,
        &mut raw,
    );
    // 0.9.141 (S3.3): the raw guest r0 rides beside
    // the collapsed return, so the resolver's errno
    // rendering can tell a kernel errno from the
    // ride's own synthetic -1.
    (r, raw)
}

/// 0.9.134: fcntl(fd, F_DUPFD, min) inside the receiver:
/// the lowest free descriptor at or above `min`, naming
/// the same open file as `fd`. Retires a resolved fd
/// out of the stdio slots (see resolve_fd_fixups_core,
/// fix (c)).
fn inject_dupfd_min(
    pid: i32,
    compat: bool,
    fd: i32,
    min: i32,
    entry_pc: u64,
    rewind: bool,
    regs: &mut Regs,
) -> i64 {
    let nr_fcntl: u64 = if compat { 55 } else { 25 };
    inject_syscall(
        pid,
        compat,
        nr_fcntl,
        [fd as u64, 0, min as u64, 0], // F_DUPFD = 0
        entry_pc,
        rewind,
        regs,
        &mut None,
    )
}

/// 0.9.134: close(fd) inside the receiver -- retiring
/// the sub-3 original after a low-slot dup.
fn inject_close(
    pid: i32,
    compat: bool,
    fd: i32,
    entry_pc: u64,
    rewind: bool,
    regs: &mut Regs,
) -> i64 {
    let nr_close: u64 = if compat { 6 } else { 57 };
    inject_syscall(
        pid,
        compat,
        nr_close,
        [fd as u64, 0, 0, 0],
        entry_pc,
        rewind,
        regs,
        &mut None,
    )
}

/// 0.9.134 (s9-133-verify Q2, fix (b)): before a resolved
/// fd is written into the parcel, prove from the host
/// side that the number names, in the receiver, the same
/// open file the sender's number names in the sender --
/// the mirror image of the sender-side check fd_obj_dump
/// photographs. It catches the resolver producing a
/// number that was never opened (the .133 run's
/// pid-value word) and cache entries the guest has since
/// closed or whose slot has been recycled onto another
/// file. A sender that has already exited cannot be
/// compared; existence in the receiver is the whole
/// check then (a fresh open of a dead sender's fd fails
/// on its own, so the un-comparable case is the cache
/// hit, whose fd was opened legitimately while the
/// sender lived).
fn fd_verify(recv_pid: i32, sender_pid: i32, sender_fd: i32, fd: i32) -> Result<(), &'static str> {
    let rt = std::fs::read_link(format!("/proc/{recv_pid}/fd/{fd}"))
        .map_err(|_| "verify-recv-missing")?;
    if let Ok(st) = std::fs::read_link(format!("/proc/{sender_pid}/fd/{sender_fd}")) {
        if st != rt {
            return Err("verify-target-mismatch");
        }
    }
    Ok(())
}

/// A BR_TRANSACTION / BR_REPLY command located in a
/// byte stream by the guest VA of its parcel data.
struct FdCmdLoc {
    off: usize,
    cmd: u32,
    code: u32,
    flags: u32,
    sender_pid: i32,
}

/// Walk a BR command stream for the transaction/reply
/// whose data pointer equals `data_va`. The last match
/// wins: if an arena slot was recycled inside one
/// stream, the live delivery is the later command, and
/// it is the one the pending fixup belongs to.
fn fd_locate_cmd(bytes: &[u8], data_va: u32) -> Option<FdCmdLoc> {
    let mut found = None;
    let mut off = 0usize;
    while off + 4 <= bytes.len() {
        let cmd = u32_at(bytes, off);
        let len = br_one_len(cmd);
        if off + len > bytes.len() {
            break;
        }
        if (cmd == BR_TRANSACTION || cmd == BR_REPLY) && len == 44 {
            if u32_at(bytes, off + 36) == data_va {
                found = Some(FdCmdLoc {
                    off,
                    cmd,
                    code: u32_at(bytes, off + 12),
                    flags: u32_at(bytes, off + 16),
                    sender_pid: u32_at(bytes, off + 20) as i32,
                });
            }
        }
        off += len;
    }
    found
}

/// What converting one failed delivery did to a stream.
enum FdConvert {
    /// BR_REPLY replaced in place by BR_FAILED_REPLY:
    /// the receiver is the waiter and has its answer.
    Reply,
    /// BR_TRANSACTION removed; its synchronous sender
    /// (fail_pid; 0 when the call was one-way) still
    /// has to be failed by whoever owns the queues.
    Txn { fail_pid: i32, code: u32 },
    NotFound,
}

/// 0.9.134 (s9-133-verify Q2, fix (a)): convert the
/// delivery whose parcel data lives at `data_va` inside
/// `bytes` to the delivery-failure path, in place --
/// the same BR_FAILED_REPLY answer the shield drops and
/// the binder_deliver error branch give a waiter,
/// applied to a delivery that only fails at
/// fd-resolution time. The stream stays command-aligned
/// throughout: a reply shrinks to the 4-byte
/// BR_FAILED_REPLY, a transaction is cut out whole. Used
/// on the tracer's own batch (both fill paths) and on
/// the coordinator's queues.
fn fd_convert_in_stream(bytes: &mut Vec<u8>, data_va: u32) -> FdConvert {
    let Some(loc) = fd_locate_cmd(bytes, data_va) else {
        return FdConvert::NotFound;
    };
    if loc.cmd == BR_REPLY {
        bytes[loc.off..loc.off + 4].copy_from_slice(&BR_FAILED_REPLY.to_le_bytes());
        bytes.drain(loc.off + 4..loc.off + 44);
        FdConvert::Reply
    } else {
        let fail_pid = if loc.flags & TF_ONE_WAY == 0 {
            loc.sender_pid
        } else {
            0
        };
        bytes.drain(loc.off..loc.off + 44);
        FdConvert::Txn {
            fail_pid,
            code: loc.code,
        }
    }
}

/// One fixup whose resolution failed (0.9.134, fix (a)).
/// Its parcel word is left unwritten -- never -1, never
/// a foreign number -- and the owning delivery is
/// converted by fd_fail_convert_local (tracer batch) or
/// by the coordinator (queued deliveries).
struct FdFail {
    sender_pid: i32,
    sender_fd: i32,
    data_va: u32,
    file_off: u64,
    why: String,
}

/// The outcome of one resolve_fd_fixups_core pass:
/// rides taken (the callers' stop bookkeeping keys off
/// it exactly as it keyed off the old return value),
/// the failures to convert, the cache keys to evict
/// (cached fds that failed verification), and the
/// statistics the coordinator counts.
#[derive(Default)]
struct FdResolution {
    rides: usize,
    failed: Vec<FdFail>,
    evictions: Vec<CacheKey>,
    dupped: u32,
    verified: u32,
    /// 0.9.137: injected-open retries performed at
    /// this settle point, and the fixups a retry
    /// carried all the way to a successful write-back
    /// (without it they would have been converted to
    /// the delivery-failure path).
    retried: u32,
    retry_saved: u32,
}

/// Dispositions reported to the coordinator with each
/// failed fixup group (MSG_ONEWAY_FD_FAIL, see
/// fd_fail_convert_local).
const FD_DISP_LOCAL: u8 = 0; // converted in the tracer's batch; counted only
const FD_DISP_FAIL_SENDER: u8 = 1; // txn dropped from the batch; coordinator fails its sender
const FD_DISP_QUEUED: u8 = 2; // not in the batch; coordinator searches its queues

/// 0.9.134 (fix (a)): route one resolution's failures to
/// the delivery-failure path. `bytes` is the batch the
/// tracer is about to hand the receiver (either fill
/// path); each failed parcel's owning command is
/// converted in it via fd_convert_in_stream, and every
/// failure group is reported to the coordinator, which
/// counts it and finishes whatever the batch could not
/// (failing a dropped transaction's waiting sender, or
/// finding the delivery in its queues when a sibling
/// thread of the arena settled the fixups first).
/// Returns true when the batch changed.
fn fd_fail_convert_local(
    coord: &mut CoordClient,
    arena: &str,
    recv_pid: i32,
    bytes: &mut Vec<u8>,
    failed: &[FdFail],
) -> bool {
    // Group by parcel: several failed fixups can ride
    // one delivery (the .133 three-object groups), and
    // a delivery converts once.
    let mut groups: Vec<(u32, Vec<&FdFail>)> = Vec::new();
    for f in failed {
        if let Some(g) = groups.iter_mut().find(|(va, _)| *va == f.data_va) {
            g.1.push(f);
        } else {
            groups.push((f.data_va, vec![f]));
        }
    }
    let mut changed = false;
    for (va, group) in groups {
        let first = group[0];
        let nfail = group.len() as u32;
        match fd_convert_in_stream(bytes, va) {
            FdConvert::Reply => {
                changed = true;
                sup!(
                    "binder: fd-fixup-convert recv_pid={recv_pid} data_va=0x{va:x} file_off=0x{:x} cmd=BR_REPLY -> FAILED_REPLY fixups={nfail} why={}",
                    first.file_off,
                    first.why
                );
                coord.oneway_fd_fail(
                    arena, va, first.sender_pid, first.sender_fd, nfail, FD_DISP_LOCAL, 0, 0,
                    &first.why,
                );
            }
            FdConvert::Txn { fail_pid, code } => {
                changed = true;
                if fail_pid > 0 {
                    sup!(
                        "binder: fd-fixup-convert recv_pid={recv_pid} data_va=0x{va:x} file_off=0x{:x} cmd=BR_TRANSACTION code={code} -> dropped; failing sender pid={fail_pid} fixups={nfail} why={}",
                        first.file_off,
                        first.why
                    );
                    coord.oneway_fd_fail(
                        arena,
                        va,
                        first.sender_pid,
                        first.sender_fd,
                        nfail,
                        FD_DISP_FAIL_SENDER,
                        fail_pid,
                        code,
                        &first.why,
                    );
                } else {
                    sup!(
                        "binder: fd-fixup-convert recv_pid={recv_pid} data_va=0x{va:x} file_off=0x{:x} cmd=BR_TRANSACTION code={code} -> dropped (one-way) fixups={nfail} why={}",
                        first.file_off,
                        first.why
                    );
                    coord.oneway_fd_fail(
                        arena, va, first.sender_pid, first.sender_fd, nfail, FD_DISP_LOCAL, 0,
                        code, &first.why,
                    );
                }
            }
            FdConvert::NotFound => {
                sup!(
                    "binder: fd-fixup-convert recv_pid={recv_pid} data_va=0x{va:x} file_off=0x{:x} not in batch; asking coordinator to search its queues fixups={nfail} why={}",
                    first.file_off,
                    first.why
                );
                coord.oneway_fd_fail(
                    arena, va, first.sender_pid, first.sender_fd, nfail, FD_DISP_QUEUED, 0, 0,
                    &first.why,
                );
            }
        }
    }
    changed
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
/// each sender fd (cache first), verify the result,
/// keep it out of the stdio slots, and only then patch
/// the parcel word in the arena file. Settling the
/// receiver's stop state differs between callers
/// (parked wake vs WRITE_READ entry), so it stays with
/// them; what comes back is the FdResolution.
///
/// 0.9.134 rewrites the failure semantics wholesale
/// (s9-133-verify Q2: of 53 resolutions, 8 were
/// defective and two of them killed their receiver at
/// the same pc in libsurfaceflinger_client -- one of
/// them a system_server tenure -- because the old code
/// wrote whatever the resolver produced into the
/// parcel, including -1 for a failed open and, once, a
/// value equal to the receiver's own pid):
/// (a) a failed resolution writes NOTHING into the
/// parcel. The failure is returned to the caller,
/// which converts the whole delivery to the
/// delivery-failure path (fd_fail_convert_local) --
/// the honest error the shield drops give a waiter,
/// instead of a fabricated fd it then dereferences.
/// (b) before any write-back, the candidate fd is
/// verified host-side (fd_verify): in the receiver it
/// must name the same open file the sender's fd names.
/// A cached entry that fails is evicted, here and with
/// the coordinator.
/// (c) a result below 3 is dupped up to the first free
/// slot at or above 3 and the original closed: the
/// resolver's open lands on the lowest free descriptor,
/// which in a freshly forked guest whose stdio is not
/// redirected yet is slot 0 -- the .133 three-object
/// groups resolved their middle pipe to 0 in five of
/// five tenures, and the guest's later stdio redirect
/// silently overwrote the slot.
///
/// 0.9.137 adds one behaviour inside the obtain step:
/// the injected open itself is retried, in place at
/// the same settle point, up to three attempts in
/// total. Its failure is the one transient class on
/// record -- both HEAP_ID cases (.134/.135) failed
/// exactly once here with open_ret=-1 on an ashmem fd
/// that resolved fine for other receivers afterwards,
/// and GB's assertReallyMapped swallows the honest
/// FAILED_REPLY this failure would produce and poisons
/// its cached control block anyway
/// (s9-136-desk-failedreply), so on that path the only
/// lever is not failing. Verify verdicts are NOT
/// retried: they are structural (a pipe endpoint the
/// /proc-open injection cannot materialise), not
/// transient, and go to the failure path at once.
/// 0.9.141 (s9-141-desk S3.3): render the errno an
/// injected open failed with, from the ride's raw
/// final r0. Only a value in [-4095, -1] is a
/// kernel errno; anything else -- including the
/// ride's own synthetic -1 on its failure paths,
/// which never sets the raw slot -- renders na,
/// never a fabricated 1.
fn errno_of_raw(raw: Option<i64>) -> String {
    match raw {
        Some(r) if (-4095..=-1).contains(&r) => format!("{}", -r),
        _ => "na".to_string(),
    }
}

/// 0.9.141 (S3.3): what the sender's fd names on
/// the host right now, read from /proc at the
/// failure (or success) point.
fn sender_link(sender_pid: i32, sender_fd: i32) -> String {
    match std::fs::read_link(format!("/proc/{sender_pid}/fd/{sender_fd}")) {
        Ok(p) => p.to_string_lossy().into_owned(),
        Err(e) => format!("err{}", e.raw_os_error().unwrap_or(0)),
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_fd_fixups_core(
    pid: i32,
    compat: bool,
    cache: &mut HashMap<CacheKey, i32>,
    arena: &str,
    fixups: &[FdFixup],
    regs: &mut Regs,
    sender_face: &dyn Fn(i32) -> String,
) -> FdResolution {
    let entry_pc = regs.pc();
    let mut cursor = regs.sp().saturating_sub(256);
    let mut res = FdResolution::default();
    for fx in fixups.iter() {
        let cache_key = (arena.to_string(), fx.sender_pid, fx.sender_fd);
        let from_cache = cache.contains_key(&cache_key);
        // Obtain a candidate: the cache's number, or a
        // fresh open of the sender's fd ridden in the
        // receiver.
        let mut candidate: Option<i32> = None;
        let mut why: Option<String> = None;
        // 0.9.137: set when this fixup's open consumed
        // at least one retry; a fixup that then reaches
        // its write-back counts as saved by the retry.
        let mut open_retried = false;
        // 0.9.141 (S3.3): the errno the failing open
        // itself produced, when the failure is the
        // open's; later failure stages (verify, dup)
        // have no kernel errno of their own and keep
        // na.
        let mut why_errno = "na".to_string();
        if let Some(fd) = cache.get(&cache_key) {
            candidate = Some(*fd);
        } else {
            let path = format!("/proc/{}/fd/{}", fx.sender_pid, fx.sender_fd);
            // 0.9.137: retry the injected open in place,
            // up to three attempts in total (see the
            // header comment). Only this step retries:
            // its failure means the sender's fd was never
            // even opened -- the transient class. Each
            // retry rides exactly like the first attempt
            // and is counted and logged as it launches,
            // so the fd-fixup-retry lines and the
            // fd_fixup_retried counter reconcile 1:1.
            let mut attempt = 0u32;
            loop {
                attempt += 1;
                // 0.9.140: the 0.9.138 ride photograph
                // (fd-ride-photo) retires here -- the fd
                // line closed in .139 on its evidence
                // (rewind rides landing on the svc, trio
                // members writing back, failed=0), and
                // the settlement counters, the settled
                // lines and the two guardrail lines
                // (rewind-anchor-bad, ride-entry-mismatch)
                // stay on watch. The rides themselves are
                // byte-for-byte the .139 ones.
                let rw = res.rides > 0;
                let (r, raw_r0) = match scratch_write(pid, &mut cursor, &path) {
                    Some(addr) => inject_openat(
                        pid,
                        compat,
                        addr,
                        entry_pc,
                        rw,
                        &mut *regs,
                        fx.sender_pid,
                        fx.sender_fd,
                    ),
                    None => (-1, None),
                };
                res.rides += 1;
                if r >= 0 {
                    candidate = Some(r as i32);
                    break;
                }
                let w = format!("open_ret={r}");
                // 0.9.141 (S3.3): the failed attempt's
                // own errno / sender link / sender
                // face, appended to the retry line
                // (and kept for the fail line when
                // this failure is the final one).
                let errno_s = errno_of_raw(raw_r0);
                if attempt >= 3 {
                    why_errno = errno_s;
                    why = Some(w);
                    break;
                }
                open_retried = true;
                res.retried += 1;
                sup!(
                    "binder: fd-fixup-retry sender_pid={} sender_fd={} recv_pid={pid} attempt={} why={w} errno={errno_s} host_fd={} path_link={} sender_state={}",
                    fx.sender_pid,
                    fx.sender_fd,
                    attempt + 1,
                    fx.sender_fd,
                    sender_link(fx.sender_pid, fx.sender_fd),
                    sender_face(fx.sender_pid)
                );
            }
        }
        if let Some(fd0) = candidate {
            match fd_verify(pid, fx.sender_pid, fx.sender_fd, fd0) {
                Ok(()) => {
                    res.verified += 1;
                    let mut fd = fd0;
                    // Fix (c): the stdio slot ban.
                    if fd < 3 {
                        let d = inject_dupfd_min(
                            pid,
                            compat,
                            fd,
                            3,
                            entry_pc,
                            res.rides > 0,
                            &mut *regs,
                        );
                        res.rides += 1;
                        if d >= 3 {
                            // The dup names the same
                            // file by construction; the
                            // original is retired so the
                            // guest's stdio redirect finds
                            // the slot free, as it would
                            // have been had the fd never
                            // landed there.
                            let _ = inject_close(pid, compat, fd, entry_pc, true, &mut *regs);
                            res.rides += 1;
                            sup!(
                                "binder: fd-fixup dup sender_pid={} sender_fd={} fd {} -> {} in pid {} (low slot)",
                                fx.sender_pid,
                                fx.sender_fd,
                                fd,
                                d,
                                pid
                            );
                            res.dupped += 1;
                            fd = d as i32;
                            if std::fs::read_link(format!("/proc/{pid}/fd/{fd}")).is_err() {
                                why = Some("dup-verify-missing".to_string());
                            }
                        } else {
                            why = Some(format!("dup_ret={d}"));
                        }
                    }
                    if why.is_none() {
                        // 0.9.137: the fixup completed;
                        // had its open not been retried it
                        // would have been converted to the
                        // delivery-failure path instead.
                        if open_retried {
                            res.retry_saved += 1;
                        }
                        cache.insert(cache_key, fd);
                        if let Ok(f) = std::fs::OpenOptions::new().write(true).open(arena) {
                            use std::os::unix::fs::FileExt;
                            let _ = f.write_all_at(&(fd as u32).to_le_bytes(), fx.file_off);
                        }
                        sup!(
                            "binder: fd {} of pid {} -> fd {} in pid {} (parcel fixup) path_link={}",
                            fx.sender_fd,
                            fx.sender_pid,
                            fd,
                            pid,
                            sender_link(fx.sender_pid, fx.sender_fd)
                        );
                    }
                }
                Err(w) => {
                    why = Some(w.to_string());
                    if from_cache {
                        // The cached number no longer
                        // names the sender's file in
                        // this process (closed since, or
                        // the slot recycled): evict it
                        // here and with the coordinator,
                        // so the next delivery re-opens
                        // instead of re-trusting it.
                        cache.remove(&cache_key);
                        res.evictions.push(cache_key);
                    }
                }
            }
        }
        if let Some(w) = why {
            sup!(
                "binder: fd-fixup-fail sender_pid={} sender_fd={} recv_pid={pid} data_va=0x{:x} file_off=0x{:x} why={w} errno={why_errno} host_fd={} path_link={} sender_state={}",
                fx.sender_pid,
                fx.sender_fd,
                fx.data_va,
                fx.file_off,
                fx.sender_fd,
                sender_link(fx.sender_pid, fx.sender_fd),
                sender_face(fx.sender_pid)
            );
            res.failed.push(FdFail {
                sender_pid: fx.sender_pid,
                sender_fd: fx.sender_fd,
                data_va: fx.data_va,
                file_off: fx.file_off,
                why: w,
            });
        }
    }
    res
}

fn resolve_fd_fixups(
    pid: i32,
    procs: &mut HashMap<i32, ProcState>,
    coord: &mut CoordClient,
    arena: &str,
    fixups: &[FdFixup],
    cache_seed: Vec<(CacheKey, i32)>,
) -> FdResolution {
    let Some(proc0) = procs.get(&pid) else {
        return FdResolution::default();
    };
    let compat = proc0.compat;
    let Some(mut regs) = get_regs(pid, compat) else {
        return FdResolution::default();
    };
    let seed: HashMap<CacheKey, i32> = cache_seed.iter().cloned().collect();
    let mut cache: HashMap<CacheKey, i32> = cache_seed.into_iter().collect();
    // 0.9.141 (S3.3): the sender face for the fixup
    // telemetry, from this worker's own account: a
    // co-located sender renders its in-flight call
    // and park state; a sender owned by another
    // worker renders remote (its face comes from
    // the S6 servicer channel, not from here).
    let sender_face = |spid: i32| -> String {
        match procs.get(&spid) {
            Some(p) => match &p.pending {
                Some(pd) if pd.binder_parked => {
                    format!("{}({})/ioctl-park", nr_name(p.compat, pd.nr), pd.nr)
                }
                Some(pd) => {
                    let park = if (p.compat && pd.nr == 240) || (!p.compat && pd.nr == 98) {
                        "futex"
                    } else {
                        "syscall"
                    };
                    format!("{}({})/{}", nr_name(p.compat, pd.nr), pd.nr, park)
                }
                None => "-/running".to_string(),
            },
            None => "-/remote".to_string(),
        }
    };
    let res = resolve_fd_fixups_core(
        pid,
        compat,
        &mut cache,
        arena,
        fixups,
        &mut regs,
        &sender_face,
    );
    // Learned entries ride back as inserts; evictions
    // (0.9.134) ride back as -1 values, which the
    // coordinator's cache-put handler reads as removals.
    let mut put = learned_entries(&cache, &seed);
    for k in &res.evictions {
        put.push((k.clone(), -1));
    }
    coord.oneway_fd_cache_put(&put);
    if res.dupped > 0 || res.verified > 0 || res.retried > 0 || res.retry_saved > 0 {
        coord.oneway_fd_stats(res.dupped, res.verified, res.retried, res.retry_saved);
    }
    if res.rides == 0 {
        return res;
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
    res
}

/// Finish a parked binder ioctl now that its arena has
/// bytes. Since S1b the state half of the dance runs in
/// the coordinator (binder_complete_decision): it hands
/// back the park record, the reply bytes and any fd
/// fixups, and this side performs the guest effects --
/// the memory writes, the fixups, the continue -- in
/// the order the combined function used to.
fn complete_parked(pid: i32, procs: &mut HashMap<i32, ProcState>, coord: &mut CoordClient) {
    let (logs, outcome) = coord.complete_parked(pid);
    replay_logs(logs);
    let ParkedOutcome::Complete { park, bytes, fixups } = outcome else {
        return;
    };
    let mut bytes = shield_live_pairs(pid, bytes, coord);
    // 0.9.134: FD fixups resolve BEFORE the batch is
    // written into the guest. They used to resolve after
    // the writes; the parcel words they patch live in the
    // arena file either way, but a resolution failure now
    // has to convert its delivery inside this byte stream
    // (a BR_REPLY becomes BR_FAILED_REPLY, see
    // fd_fail_convert_local), and that is only possible
    // while the stream is still ours. The rides still
    // ride the parked call's entry->exit transition and
    // resolve_fd_fixups still applies its recorded inject
    // exactly as before; on the success path nothing the
    // guest can observe changes.
    if let Some((arena, fx, cache)) = fixups {
        let res = resolve_fd_fixups(pid, procs, coord, &arena, &fx, cache);
        if !res.failed.is_empty() {
            fd_fail_convert_local(coord, &arena, pid, &mut bytes, &res.failed);
        }
        // 0.9.136: the settle-before-wake audit mark.
        // Printed at the exact point the invariant
        // becomes true: every fixup of the deliveries in
        // this batch is resolved (parcel words patched)
        // or converted (stream rewritten) and the batch
        // has neither been written to the guest nor the
        // tracee continued. An offline audit can assert
        // every fd-fixup-fail group is covered by one of
        // these lines for its recv_pid before that pid's
        // next guest-visible line.
        sup!(
            "binder: fd-fixup-settled recv_pid={pid} path=parked fixups={} failed={}",
            fx.len(),
            res.failed.len()
        );
    }
    if let Some(p) = procs.get_mut(&pid) {
        p.last_binder_read = Some((park.read_buf, bytes.len() as u32));
        // 0.9.141 (P3): the parked-path fill deepens
        // this thread's serving window too.
        let n = count_br_transactions(&bytes);
        if n > 0 {
            p.win.depth += n as i32;
            let d = p.win.depth.max(0) as u32;
            if d > p.win.maxdepth {
                p.win.maxdepth = d;
            }
        }
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
    // 0.9.131: the arena is really gone (the guard
    // above held while sibling threads remained); its
    // ignition evidence ring dies with it.
    st.evidence.remove(arena);
    // 0.9.132: its write-overlap audit records die with
    // it too, so a later arena can never be audited
    // against a dead one's writes.
    st.write_audit.retain(|r| r.arena != arena);
    // 0.9.136: pending fd fixups belong to this arena's
    // deliveries; with per-delivery selection an
    // unsettled one can only name a delivery nobody
    // consumed, and it must not survive into a later
    // tenure of the same arena path (its data_va could
    // coincide with a fresh parcel's).
    st.fd_pending.remove(arena);
    if let Some(bp) = st.procs.get(arena) {
        bsup!(
            "binder: arena {arena} free counters: hit={} nobase={} stale={} parcels_left={} notify_queued={} shield_drops={} free_hit={} free_miss={} free_rescued={} shield_cookie_suspects={} reply_unmatched={} shield4_drops={} shield4_buckets: cookie={} libc={} stack={} other={} second_reads={} second_read_differs={} fd_fixup_failed={} fd_fixup_dupped={} fd_fixup_verified={} fd_fixup_retried={} fd_fixup_retry_saved={} reply_collide_checks={} reply_collide_hits={}",
            bp.free_hit,
            bp.free_nobase,
            bp.free_stale,
            bp.parcels.len(),
            st.notify_queued,
            st.shield_drops,
            bp.free_parcel_hit,
            bp.free_miss,
            bp.free_rescued,
            st.shield_cookie_suspects,
            st.reply_unmatched,
            st.shield4_drops,
            st.shield4_cookie,
            st.shield4_libc,
            st.shield4_stack,
            st.shield4_other,
            st.second_reads,
            st.second_read_differs,
            st.fd_fixup_failed,
            st.fd_fixup_dupped,
            st.fd_fixup_verified,
            st.fd_fixup_retried,
            st.fd_fixup_retry_saved,
            st.reply_collide_checks,
            st.reply_collide_hits
        );
    }
    // 0.9.140: the trigger-A blind-spot account (see
    // BinderState::crash_token_miss), reported at the
    // same settlement on its own line -- the
    // free-counters format above is byte-stable field
    // tooling and does not grow new fields.
    bsup!(
        "binder: arena {arena} crash-report account: token_miss={}",
        st.crash_token_miss
    );
    // 0.9.141 (P1/P2): the issuance double-read and
    // poison word0 accounts, at the same settlement
    // on their own lines, like the account above.
    bsup!(
        "binder: arena {arena} issuance account: reads={} differs={}",
        st.issuance_reads, st.issuance_differs
    );
    bsup!(
        "binder: arena {arena} poison account: word0_rel self-8={} self={} self-page={} heap-other={} libc={} stack={} other={}",
        st.poison_word0[0],
        st.poison_word0[1],
        st.poison_word0[2],
        st.poison_word0[3],
        st.poison_word0[4],
        st.poison_word0[5],
        st.poison_word0[6]
    );
    // 0.9.118 death inventory (telemetry only: reads
    // state, changes nothing; ported from 0.9.116). When
    // an arena dies holding a backlog of unfreed parcels,
    // name what they were and who sent them, which death
    // notices this death is about to fire, and how the
    // global ref-notice ledger stands -- a tenure-killing
    // backlog should identify itself, not just its size.
    if let Some(bp) = st.procs.get(arena) {
        if bp.parcels.len() >= 10 {
            let total = bp.parcels.len();
            let mut offs: Vec<u32> = bp.parcels.keys().copied().collect();
            offs.sort_unstable();
            for (i, &off) in offs.iter().take(200).enumerate() {
                let pp = &bp.parcels[&off];
                bsup!(
                    "binder: arena {arena} death-inventory parcel {}/{}: off=0x{:x} size={} from_pid={} code={} target_ptr=0x{:x} cookie=0x{:x}",
                    i + 1,
                    total,
                    off,
                    pp.total,
                    pp.from_pid,
                    pp.code,
                    pp.target_ptr,
                    pp.txn_cookie
                );
            }
            if total > 200 {
                bsup!(
                    "binder: arena {arena} death-inventory parcels truncated: showing 200 of {total}"
                );
            }
        }
    }
    {
        // Death notices this death is about to fire: the
        // watches registered on this arena's nodes (the
        // firing loop further down consumes exactly this
        // set). Recipient pids are the watcher arena's
        // registered thread pids at this instant.
        let mut dn: Vec<(usize, &String, u32)> = Vec::new();
        for (i, n) in st.nodes.iter().enumerate() {
            if n.owner == arena && !n.dead {
                if let Some(list) = st.watchers.get(&i) {
                    for (w, c) in list {
                        dn.push((i, w, *c));
                    }
                }
            }
        }
        let dn_total = dn.len();
        for (i, (node, w, c)) in dn.iter().take(200).enumerate() {
            let mut pids: Vec<i32> = st
                .procs
                .get(w.as_str())
                .map(|bp| bp.base.keys().copied().collect())
                .unwrap_or_default();
            pids.sort_unstable();
            let pids: Vec<String> = pids.iter().map(|p| p.to_string()).collect();
            bsup!(
                "binder: arena {arena} death-inventory death-notice {}/{}: to_arena={} to_pids=[{}] node={} cookie=0x{:x}",
                i + 1,
                dn_total,
                w,
                pids.join(" "),
                node,
                c
            );
        }
        if dn_total > 200 {
            bsup!(
                "binder: arena {arena} death-inventory death-notices truncated: showing 200 of {dn_total}"
            );
        }
    }
    {
        // Global ref-notice ledger by owner arena. The
        // 0.9.116 original tallied per-node queued flags
        // from the 0.9.113 state machine; this tree has no
        // such flags -- a notice is pushed straight into
        // the owner's inbound stream at crossing time, and
        // ref_notified is the ledger of (node, holder)
        // pairs it went out for. Tally the outstanding
        // pairs per owner arena in one read-only pass.
        let mut by_owner: HashMap<String, u32> = HashMap::new();
        for ((node, _holder), _weak) in &st.ref_notified {
            if let Some(n) = st.nodes.get(*node) {
                *by_owner.entry(n.owner.clone()).or_default() += 1;
            }
        }
        if by_owner.is_empty() {
            bsup!("binder: arena {arena} death-inventory pending-ref-notices global: none");
        } else {
            let mut owners: Vec<&String> = by_owner.keys().collect();
            owners.sort();
            let parts: Vec<String> = owners
                .iter()
                .map(|o| format!("{o} notified={}", by_owner[*o]))
                .collect();
            bsup!(
                "binder: arena {arena} death-inventory pending-ref-notices global: {}",
                parts.join("; ")
            );
        }
    }
    // C2 death settlement (0.9.118, ported from 0.9.117
    // to this tree's reference model): references this
    // arena held on other arenas' nodes were announced
    // to their owners with BR_INCREFS(/BR_ACQUIRE) when
    // the objects crossed (binder_notify_ref) and are
    // ledgered in ref_notified. The holder is gone now;
    // settle every pair the way the real driver does --
    // queue BR_DECREFS (plus BR_RELEASE where the hold
    // was strong) to the node's owner and forget the
    // pair -- instead of leaking one count per tenure on
    // every long-lived owner's books. Only this arena's
    // holds are touched: no node is destroyed, no other
    // arena's parcels move, notify_queued is untouched,
    // and the death-notice firing further down runs
    // exactly as before. Parcels left in the dead arena
    // are counted as settled: in this tree they carry no
    // per-parcel ref records, and the buffer table dies
    // with the arena record.
    {
        let parcels_left = st.procs.get(arena).map_or(0, |bp| bp.parcels.len());
        let held: Vec<(usize, bool)> = st
            .ref_notified
            .iter()
            .filter(|(k, _)| k.1 == arena)
            .map(|(k, w)| (k.0, *w))
            .collect();
        let mut nodes_touched: HashSet<usize> = HashSet::new();
        let mut settle_owners: HashSet<String> = HashSet::new();
        let mut refs_returned = 0usize;
        for (node, weak) in held {
            st.ref_notified.remove(&(node, arena.to_string()));
            nodes_touched.insert(node);
            let Some(n) = st.nodes.get(node) else {
                continue;
            };
            let (owner, nptr, ncookie) = (n.owner.clone(), n.ptr, n.cookie);
            if let Some(bp) = st.procs.get_mut(&owner) {
                bp.inbound.extend_from_slice(&BR_DECREFS.to_le_bytes());
                bp.inbound.extend_from_slice(&nptr.to_le_bytes());
                bp.inbound.extend_from_slice(&ncookie.to_le_bytes());
                if !weak {
                    bp.inbound.extend_from_slice(&BR_RELEASE.to_le_bytes());
                    bp.inbound.extend_from_slice(&nptr.to_le_bytes());
                    bp.inbound.extend_from_slice(&ncookie.to_le_bytes());
                }
                refs_returned += 1;
                settle_owners.insert(owner);
            }
        }
        for owner in settle_owners {
            binder_maybe_wake_pids(st, &owner, wakes);
        }
        bsup!(
            "binder: arena {arena} death-settle parcels={parcels_left} refs_returned={refs_returned} nodes_touched={}",
            nodes_touched.len()
        );
    }
    // Queued manager transactions from this arena's
    // senders die with it (0.9.24).
    let before = st.mgr_pending.len();
    st.mgr_pending.retain(|q| q.sender_arena != arena);
    let purged = before - st.mgr_pending.len();
    if purged > 0 {
        bsup!("binder: purged {purged} queued mgr txn(s) from dead arena {arena}");
    }
    if st.mgr_arena.as_deref() == Some(arena) {
        st.mgr_arena = None;
        if let Some(mi) = st.mgr_node.take() {
            if let Some(n) = st.nodes.get_mut(mi) {
                n.dead = true;
            }
        }
        bsup!("binder: context manager arena died; manager slot cleared");
    }
    if let Some(ws) = st.waiters.remove(arena) {
        for w in ws {
            if let Some(bp) = st.procs.get_mut(&w.sender_arena) {
                bp.push_to(w.sender_pid, &BR_DEAD_REPLY.to_le_bytes());
            }
            binder_maybe_wake_pids(st, &w.sender_arena, wakes);
        }
    }
    for v in st.waiters.values_mut() {
        v.retain(|w| w.sender_arena != arena);
    }
    // 0.9.125: claimed waits sent BY the dead arena are
    // scrubbed from the surviving serving stacks too
    // (mirror of the queue retain above -- their callers
    // are gone, so the claims can never be answered).
    // Stacks belonging to the dead arena's own threads
    // need no handling here: binder_thread_exit drained
    // them, failing their callers, before this ran.
    for stack in st.serving.values_mut() {
        // 0.9.130: the same retain, per group; groups
        // the scrub empties are removed (a group on the
        // stack always holds frames).
        for group in stack.groups.iter_mut() {
            group.frames.retain(|fr| match fr {
                ServingFrame::Reply(w, _) => w.sender_arena != arena,
                ServingFrame::Other => true,
            });
        }
        stack.groups.retain(|g| !g.frames.is_empty());
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
                binder_maybe_wake_pids(st, &watcher_arena, wakes);
            }
        }
    }
    for v in st.watchers.values_mut() {
        v.retain(|(a, _)| a != arena);
    }
    if !dead_nodes.is_empty() {
        bsup!(
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
    coord: &mut CoordClient,
) -> String {
    let path_arg = if (compat && nr == 322) || (!compat && nr == 56) {
        1
    } else {
        0
    };
    // The arena file, its canonical identity key and the
    // proc registration live with the coordinator since
    // S1b (binder_open_arena, the old body verbatim);
    // this side only rewrites the guest's path argument,
    // to the raw path as before.
    let arena_raw = match coord.open_binder(pid, rootfs) {
        Ok((_arena, raw)) => raw,
        Err(e) => return format!("binder arena create failed: {e}"),
    };
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
    coord: &mut CoordClient,
) -> String {
    let path_arg = if (compat && nr == 322) || (!compat && nr == 56) {
        1
    } else {
        0
    };
    // The region file and its record live with the
    // coordinator since S1b (ashmem_open_region, the old
    // body verbatim); this side only rewrites the
    // guest's path argument, to the raw path as before.
    let raw = coord.open_ashmem(pid, rootfs);
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
    coord: &mut CoordClient,
) -> String {
    let arg = regs.arg(2);
    // The records live with the coordinator since S1b:
    // reads are one request each, writes are one-way
    // updates (the entry-or-default semantics run on
    // that side, against default_ashmem_rec).
    match req {
        ASHMEM_SET_NAME => {
            let mut buf = [0u8; 256];
            let _ = read_mem(pid, arg, &mut buf);
            let end = buf.iter().position(|&b| b == 0).unwrap_or(256);
            let name = String::from_utf8_lossy(&buf[..end]).into_owned();
            coord.oneway_ashmem_set_name(key, &name);
            skip_syscall(pid, regs, pend, 0);
            format!("ashmem SET_NAME '{name}'")
        }
        ASHMEM_GET_NAME => {
            let rec = coord.ashmem_get(key);
            let name = rec.map(|r| r.name).unwrap_or_default();
            let mut buf = [0u8; 256];
            let n = name.len().min(255);
            buf[..n].copy_from_slice(&name.as_bytes()[..n]);
            let _ = write_mem(pid, arg, &buf);
            skip_syscall(pid, regs, pend, 0);
            "ashmem GET_NAME".to_string()
        }
        ASHMEM_SET_SIZE => {
            let size = arg as u64;
            // 0.9.60 ordering fix: the file length is
            // the guest-visible effect of SET_SIZE, and
            // the guest may mmap and touch the region
            // the moment this ioctl returns. Since S1b
            // the length lived behind a one-way message
            // to the coordinator, which applies it
            // whenever it gets there -- a guest that won
            // the race touched pages past EOF and took
            // SIGBUS (SF, 0.9.59 field run). Apply the
            // length here, synchronously, before the
            // guest resumes -- the pre-S1b order; the
            // coordinator's record follows on the
            // one-way and its duplicate set_len is
            // idempotent.
            if let Ok(f) = std::fs::OpenOptions::new().write(true).open(key) {
                let _ = f.set_len(size);
            }
            coord.oneway_ashmem_set_size(key, size);
            skip_syscall(pid, regs, pend, 0);
            format!("ashmem SET_SIZE -> {size}")
        }
        ASHMEM_GET_SIZE => {
            let size = coord.ashmem_get(key).map(|r| r.size).unwrap_or(0);
            skip_syscall(pid, regs, pend, size as i64);
            format!("ashmem GET_SIZE -> {size}")
        }
        ASHMEM_SET_PROT_MASK => {
            coord.oneway_ashmem_set_prot(key, arg as u64);
            skip_syscall(pid, regs, pend, 0);
            "ashmem SET_PROT_MASK".to_string()
        }
        ASHMEM_GET_PROT_MASK => {
            let prot = coord.ashmem_get(key).map(|r| r.prot).unwrap_or(7);
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

/// capset (compat 185, native 90): answered from the
/// virtual world, like the set*id family above. The
/// host process is an Android app and holds no real
/// capabilities, so a passed-through capset asking for
/// any permitted bit fails EPERM on the host kernel --
/// and GB's forkAndSpecialize treats exactly that as
/// fatal: "cannot set capabilities" -> dvmAbort ->
/// the deliberate *(char*)0xDEADD00D store (S8 gun 1
/// field: system_server died at libdvm+0x4612c on all
/// 13 zygote tenures, right after the emulated
/// setuid). Capability sets are bookkeeping of the
/// guest's virtual credential state, so the call is
/// answered success here without reaching the kernel.
/// capget is deliberately left passed through for
/// now: nothing in the specialization path reads the
/// sets back, and a future consumer that does will
/// name itself the same way this one did.
fn is_capset(compat: bool, nr: u64) -> bool {
    if compat {
        nr == 185
    } else {
        nr == 90
    }
}

/// ioprio_set / ioprio_get (compat 314/315, native
/// 30/31): answered success here, like capset above.
/// GB's init applies a service's `ioprio` line in the
/// forked child before exec; the host app seccomp
/// filter traps the call with SIGSYS and, unrescued,
/// the signal kills the child before it ever reaches
/// execve (0.9.83 field: vold, the only service with
/// an ioprio line, died all 63 tenures at exactly
/// this call -- SIGSYS regs nr=0x13a, a2=0x4002 =
/// IOPRIO_CLASS_BE/2, matching the rc line). I/O
/// priority is advisory bookkeeping the guest gains
/// nothing real from; faking success lets the child
/// proceed to exec. ioprio_get faked to 0 reports
/// the default priority, which is what an untouched
/// process holds anyway.
fn is_ioprio(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 314 | 315)
    } else {
        matches!(nr, 30 | 31)
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

/// Path probes (compat access/stat64/lstat64) get the
/// device_map redirection too, not just opens. A probe
/// translated plainly into the rootfs hits a nonexistent
/// node and reports the device ABSENT even though opens
/// of it are redirected and would succeed -- and library
/// code that probes once and caches the verdict poisons
/// itself for the process's whole life: Harmony's
/// RandomBitsSupplier probes /dev/urandom with access(2)
/// during class init; in the 0.9.83 field the zygote's
/// probe came back -ENOENT, the class marked itself
/// unavailable ("no random devices"), and the forked
/// system_server inherited the verdict, killing
/// SettingsProvider at installSystemProviders time.
fn is_device_probe(compat: bool, nr: u64) -> bool {
    if compat {
        matches!(nr, 33 | 195 | 196) // access, stat64, lstat64
    } else {
        false
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
        // The guest's log devices (S7 gun 3): GB has no
        // logd; every LOGE lands in /dev/log/*. Without a
        // target, the runtime's own account of its
        // failures (Dalvik aborts, uncaught exceptions)
        // vanishes -- app_process died silently 13 times
        // in 0.9.48's field run. Map the four channels to
        // plain files; the shell folds a printable-strings
        // extraction into the session log on save.
        "/dev/log/main" => Some(format!("{rootfs}/.logs/log-main")),
        "/dev/log/radio" => Some(format!("{rootfs}/.logs/log-radio")),
        "/dev/log/events" => Some(format!("{rootfs}/.logs/log-events")),
        "/dev/log/system" => Some(format!("{rootfs}/.logs/log-system")),
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
/// The address family at the head of a guest sockaddr,
/// or None when the head bytes are unreadable.
fn sockaddr_family(pid: i32, addr_ptr: u64) -> Option<u16> {
    let mut buf = [0u8; 2];
    match read_mem(pid, addr_ptr, &mut buf) {
        Ok(2) => Some(u16::from_ne_bytes(buf)),
        _ => None,
    }
}

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
) -> (String, bool, Option<String>) {
    // The third return value is the decided guest-absolute
    // image path (S2 handoff key), None when no path could
    // be decided (unreadable, /proc/self/exe).
    let name = nr_name(compat, nr);
    let (path_arg, dirfd) = if nr == nr_execve(compat) {
        (0usize, AT_FDCWD)
    } else {
        (1usize, regs.arg(0) as i64)
    };
    let addr = regs.arg(path_arg);
    let Some(gpath) = read_path(pid, addr) else {
        return (format!("{name}({nr}) path@{addr:#x} (unreadable, passed)"), false, None);
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
        return (format!("{name}({nr}) '/proc/self/exe' -> busybox (native)"), ok, None);
    }
    if !gpath.starts_with('/') && dirfd != AT_FDCWD {
        // execveat relative to a real dirfd: out of M1 scope.
        skip_syscall(pid, regs, pend, -EACCES);
        return (format!("{name}({nr}) '{gpath}' BLOCKED (dirfd-relative) -> -EACCES"), true, None);
    }
    let abs = guest_abs(vcwd, &gpath);
    if abs == "/bin/busybox" {
        let ok = rewrite_to_bb(regs);
        return (format!("exec '{gpath}' -> busybox (native)"), ok, Some("/bin/busybox".to_string()));
    }
    let (final_abs, exists) = resolve_guest_target(rootfs, &abs);
    if exists && final_abs == "/bin/busybox" {
        let ok = rewrite_to_bb(regs);
        return (format!("exec '{gpath}' -> busybox (native)"), ok, Some(abs));
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
                        Some(abs),
                    );
                }
                skip_syscall(pid, regs, pend, -EACCES);
                return (
                    format!("exec '{gpath}' BLOCKED (dynamic, loader argv rewrite failed) -> -EACCES"),
                    true,
                    Some(abs),
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
            Some(abs),
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
            (format!("exec '{gpath}' -> '{host}' (pass, kernel verdict)"), true, Some(abs))
        }
        None => (format!("exec '{gpath}' (scratch write failed, passed)"), false, None),
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

// ---- S2: sharded tracing (multiworker spec) ----
//
// The one tracing loop (tracer_loop) runs in several
// processes: W0 (the main supervisor, wid 0) owns the
// guest root and every tracee no shard claims, and one
// worker per shard owns the tracees W0 hands it. All
// cross-tracee state lives in the coordinator (binder
// state since S1b; pid routing and the global virtual
// credential book since S2), so a tracer only ever
// touches its own procs/vcreds tables.

/// Everything one tracer process needs: its own
/// process table, its own credential slice, its own
/// coordinator connection, and the session constants.
/// Moved into tracer_loop by value so the loop body's
/// local names (and their &mut shapes) are exactly
/// what the single-process code had.
struct TracerCtx {
    wid: u8,
    rootfs: String,
    bb_path: String,
    loader_path: String,
    guest_compat: bool,
    /// The guest root's pid on W0; 0 in workers (they
    /// own no root: the exit branch's root handling is
    /// W0-only and can never trigger there, since none
    /// of their pids equals 0).
    root_pid: i32,
    coord: CoordClient,
    procs: HashMap<i32, ProcState>,
    vcreds: HashMap<i32, (u32, u32)>,
    wakes: Vec<i32>,
    root_launched: bool,
    seen: HashSet<(bool, u64)>,
    counts: HashMap<(bool, u64), u64>,
    /// Handoff table (W0 only): guest image path ->
    /// worker id. Empty in workers.
    shard_map: HashMap<String, u8>,
    /// Kin re-shard target (workers only): a direct
    /// child of this worker's shard root that exec's a
    /// new image is handed to this worker instead.
    /// Only W2 (sf) sets it, to W6; None on W0 and on
    /// every other worker.
    kin_target: Option<u8>,
    /// The pid this worker adopted as its shard root
    /// (a root=true adoption). A later root adoption
    /// (a restarted service) replaces it. 0 until the
    /// first one; unused on W0, whose root is the
    /// guest root itself.
    shard_root: i32,
    /// Freeze forensics (0.9.81): this worker's
    /// system_server candidate -- the earliest living
    /// fork/vfork child of the shard root that has
    /// never exec'd. system_server is zygote's first
    /// fork child and the only child of any root that
    /// never execs: app children exec at once (and are
    /// handed off), threads arrive as CLONE births and
    /// never enter the running. Maintained at the
    /// birth/exec/exit sites in tracer_loop; consumed
    /// by the Push::DumpStacks arm in next_stop. None
    /// until a candidate is born, and on W0 forever
    /// (it never adopts a root).
    dump_candidate: Option<i32>,
}

/// The shard table: which worker takes which guest
/// service binary when it is born as a direct child of
/// the guest root. Paths are guest-absolute image
/// paths as decided by entry_exec. W6 (kin) owns no
/// image of its own: it receives the kin re-shards --
/// children of another worker's shard root -- so its
/// path list is empty.
const SHARDS: [(u8, &str, &[&str]); 6] = [
    (1, "mgr", &["/system/bin/servicemanager"]),
    (2, "sf", &["/system/bin/surfaceflinger"]),
    (3, "zygote", &["/system/bin/app_process"]),
    (4, "leaf", &["/system/bin/gbprobe"]),
    (5, "anim", &["/system/bin/bootanimation"]),
    (6, "kin", &[]),
];

/// Fork the shard workers. Each child closes
/// W0's coordinator connection first (its EOF is the
/// death-chain trigger and must mean W0 itself went
/// away) and runs worker_main. A shard whose fork
/// fails is simply absent from the returned map, and
/// its would-be handoffs stay on W0.
fn spawn_workers(
    coord_sock: &str,
    rootfs: &str,
    bb_path: &str,
    loader_path: &str,
    guest_compat: bool,
    w0_coord_fd: i32,
) -> HashMap<String, u8> {
    let mut map: HashMap<String, u8> = HashMap::new();
    for (wid, name, paths) in SHARDS {
        let cpid = unsafe { libc::fork() };
        if cpid < 0 {
            sup!(
                "worker W{wid} ({name}) fork failed: errno={}; shard stays on W0",
                errno()
            );
            continue;
        }
        if cpid == 0 {
            unsafe { libc::close(w0_coord_fd) };
            worker_main(
                wid, name, rootfs, coord_sock, bb_path, loader_path, guest_compat,
            );
        }
        for p in paths {
            map.insert(p.to_string(), wid);
        }
        sup!("worker W{wid} spawned for shard {name}");
    }
    map
}

/// A worker process: a full tracer for one shard. It
/// starts with no tracees at all; the coordinator
/// pushes adoptions as W0 hands tracees off. It ends
/// when the coordinator connection EOFs (the death
/// chain: the shell stops W0, W0's connection closes,
/// the coordinator exits, this connection EOFs) or
/// when nothing is left to trace.
fn worker_main(
    wid: u8,
    shard: &str,
    rootfs: &str,
    coord_sock: &str,
    bb_path: &str,
    loader_path: &str,
    guest_compat: bool,
) -> ! {
    WID.store(wid as u32, Ordering::Relaxed);
    let coord = CoordClient::connect(coord_sock, wid, shard);
    sup!("worker W{wid} online: shard {shard}");
    let ctx = TracerCtx {
        wid,
        rootfs: rootfs.to_string(),
        bb_path: bb_path.to_string(),
        loader_path: loader_path.to_string(),
        guest_compat,
        root_pid: 0,
        coord,
        procs: HashMap::new(),
        vcreds: HashMap::new(),
        wakes: Vec::new(),
        root_launched: false,
        seen: HashSet::new(),
        counts: HashMap::new(),
        shard_map: HashMap::new(),
        // Only the sf worker re-shards its root's
        // children, to the kin worker.
        kin_target: if wid == 2 { Some(6) } else { None },
        shard_root: 0,
        dump_candidate: None,
    };
    tracer_loop(ctx);
    sup!("worker W{wid} done");
    std::process::exit(0);
}

// SIGCHLD self-pipe: the tracer's event loop sleeps in
// poll on (coordinator socket, self-pipe); the handler
// only writes a byte, so a tracee stop wakes the poll
// without the handler touching any tracer state. No
// SA_RESTART: nothing in the loop blocks in a call
// that must resume, and an occasional EINTR is free.
static SIGCHLD_WR: AtomicI32 = AtomicI32::new(-1);

extern "C" fn on_sigchld(_sig: i32) {
    let fd = SIGCHLD_WR.load(Ordering::Relaxed);
    if fd >= 0 {
        let b = [1u8; 1];
        unsafe { libc::write(fd, b.as_ptr() as *const libc::c_void, 1) };
    }
}

fn install_sigchld_pipe() -> i32 {
    let mut fds = [0i32; 2];
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC | libc::O_NONBLOCK) } != 0 {
        return -1;
    }
    SIGCHLD_WR.store(fds[1], Ordering::Relaxed);
    unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = on_sigchld as *const () as usize;
        sa.sa_flags = 0;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(libc::SIGCHLD, &sa, std::ptr::null_mut());
    }
    fds[0]
}

enum NextStop {
    Stop(i32, i32),
    End,
}

/// The head of the tracing loop, and the whole S2
/// event machinery: drain pending stops without
/// blocking, then coordinator pushes (adoptions and
/// cross-shard wakes), and only then sleep in poll
/// until a tracee stops or the coordinator speaks.
/// Pushes are only acted on at stop boundaries, the
/// same places the old blocking loop could act, so
/// decision ordering is unchanged.
fn next_stop(
    wid: u8,
    coord: &mut CoordClient,
    procs: &mut HashMap<i32, ProcState>,
    vcreds: &mut HashMap<i32, (u32, u32)>,
    shard_root: &mut i32,
    dump_candidate: &mut Option<i32>,
    selfpipe_rd: i32,
) -> NextStop {
    loop {
        // 1) Drain every pending ptrace stop.
        let mut status: i32 = 0;
        let r = unsafe { libc::waitpid(-1, &mut status, WALL | libc::WNOHANG) };
        if r > 0 {
            return NextStop::Stop(r, status);
        }
        if r < 0 && errno() == libc::ECHILD {
            if wid == 0 {
                sup!("waitpid: no tracees left");
                return NextStop::End;
            }
            // A worker holding no tracees (yet, or any
            // more) is idle, not done: adoptions arrive
            // over the coordinator socket, and only the
            // coordinator going away ends a worker
            // (step 3 below). The 0.9.61 field run lost
            // all four workers to this line within
            // milliseconds of their starting -- ECHILD
            // is a newborn worker's normal state -- so
            // every handoff was refused and W0 took
            // each service back.
        }
        // 2) Coordinator pushes: an adoption rebuilds a
        // tracee here; a wake completes a parked ioctl;
        // a dump request SIGQUITs the system_server
        // candidate.
        coord.pump();
        // Freeze forensics relay (W0 only, 0.9.81):
        // the shell's dump request arrived as SIGUSR2,
        // whose handler only set DUMP_REQ. Forward it
        // to the coordinator here, at the loop's
        // coordinator-service point; the coordinator
        // broadcasts it to the workers. The handler is
        // installed after every fork, so no other
        // tracer process can see the signal, and the
        // flag is only ever checked on this line.
        if wid == 0 && DUMP_REQ.swap(false, Ordering::Relaxed) {
            coord.dump_req();
        }
        let mut acted = false;
        while let Some(push) = coord.inbox.pop_front() {
            acted = true;
            match push {
                Push::Wake(wpid) => {
                    if procs.contains_key(&wpid) {
                        complete_parked(wpid, procs, coord);
                    }
                }
                Push::Adopt {
                    pid,
                    vcwd,
                    compat,
                    sigmask,
                    creds,
                    root,
                } => {
                    let prev_root = *shard_root;
                    adopt_tracee(
                        pid, &vcwd, compat, sigmask, creds, root, procs, vcreds, coord,
                        shard_root,
                    );
                    // A replaced shard root orphans the
                    // old root's dump candidate: it was
                    // the old zygote's child, and the new
                    // root's own system_server earns the
                    // slot when it is born (the old one's
                    // exit clears it too, but a restarted
                    // service must not leave a stale pid
                    // armed in the meantime).
                    if root && *shard_root != prev_root {
                        *dump_candidate = None;
                    }
                }
                Push::AdoptAck { .. } => {
                    // Acks are consumed by do_handoff's
                    // wait; one reaching the loop head is
                    // stale (its handoff already timed out
                    // and was taken back). Drop it.
                }
                Push::DumpStacks => {
                    // Freeze forensics (0.9.81): SIGQUIT
                    // this worker's system_server
                    // candidate, if it holds one (the
                    // broadcast reaches every worker;
                    // only one can). GB Dalvik's signal
                    // catcher answers SIGQUIT with a full
                    // Java stack dump and keeps running --
                    // that non-lethality is the whole
                    // point -- and the signal reaches the
                    // guest by the ordinary reinjection at
                    // its delivery stop.
                    if let Some(cpid) = *dump_candidate {
                        if procs.contains_key(&cpid) {
                            if unsafe { libc::kill(cpid, libc::SIGQUIT) } == 0 {
                                sup!(
                                    "dumpstacks: SIGQUIT -> system_server pid={cpid}"
                                );
                            } else {
                                sup!(
                                    "dumpstacks: SIGQUIT -> system_server pid={cpid} failed errno={}",
                                    errno()
                                );
                            }
                        }
                    }
                }
                Push::ServicerFace { arena, pids } => {
                    // 0.9.141 (S6): the wedge chain in
                    // the coordinator named servicers;
                    // whichever worker owns one prints
                    // its face from its own tables.
                    for x in &pids {
                        if procs.contains_key(x) {
                            print_servicer_face(&arena, *x, procs);
                        }
                    }
                }
            }
        }
        if acted {
            continue;
        }
        // 3) The coordinator going away ends a worker
        // (the death chain); for W0 it is the fatal
        // ruling every rpc already enforces.
        if coord.eof {
            if wid == 0 {
                sup!("coordinator connection lost; supervisor exiting");
                std::process::exit(1);
            }
            return NextStop::End;
        }
        // 4) Sleep until a tracee stops (SIGCHLD
        // self-pipe) or the coordinator speaks.
        let mut pfds = [
            libc::pollfd {
                fd: coord.poll_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: selfpipe_rd,
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        let n = unsafe { libc::poll(pfds.as_mut_ptr(), 2, -1) };
        if n > 0 {
            if pfds[1].revents & libc::POLLIN != 0 {
                let mut buf = [0u8; 128];
                loop {
                    let got = unsafe {
                        libc::read(
                            selfpipe_rd,
                            buf.as_mut_ptr() as *mut libc::c_void,
                            buf.len(),
                        )
                    };
                    if got <= 0 {
                        break;
                    }
                }
            }
            if pfds[0].revents != 0 {
                coord.pump();
            }
        }
    }
}

/// Worker side of a handoff: attach a tracee the
/// offering tracer detached (it is stopped, with no
/// tracer), set the full option set back, rebuild its
/// ProcState from the state the handoff carried, and
/// continue it. Its signal mask and vcwd travelled
/// with the handoff; binder registrations
/// (thread_arena and friends) are re-filed by its own
/// later ioctls and mmaps through the existing
/// coordinator oneways. The exec record (pend) was
/// settled by the offering tracer at the exec exit
/// stop before the detach, so there is nothing to
/// carry. A root adoption makes the pid this worker's
/// shard root (replacing any previous one); a kin
/// adoption leaves the root unchanged.
fn adopt_tracee(
    pid: i32,
    vcwd: &str,
    compat: bool,
    sigmask: u32,
    creds: (u32, u32),
    root: bool,
    procs: &mut HashMap<i32, ProcState>,
    vcreds: &mut HashMap<i32, (u32, u32)>,
    coord: &mut CoordClient,
    shard_root: &mut i32,
) {
    if ptrace4(PTRACE_ATTACH, pid, std::ptr::null_mut(), std::ptr::null_mut()) != 0 {
        sup!("adopt: PTRACE_ATTACH pid={pid} failed errno={}", errno());
        coord.adopt_ack(pid, false);
        coord.unregister_pid(pid);
        return;
    }
    let mut status: i32 = 0;
    let r = unsafe { libc::waitpid(pid, &mut status, WALL) };
    if r != pid || !libc::WIFSTOPPED(status) {
        sup!("adopt: pid={pid} vanished at its attach stop (r={r} status={status:#x})");
        coord.adopt_ack(pid, false);
        coord.unregister_pid(pid);
        return;
    }
    let mut ps = ProcState::new(vcwd, false, compat);
    ps.sigmask = sigmask;
    ps.options_set = set_trace_options(pid);
    ps.started = true;
    procs.insert(pid, ps);
    vcreds.insert(pid, creds);
    coord.adopt_ack(pid, true);
    if root {
        *shard_root = pid;
    }
    sup!("adopted pid={pid} vcwd={vcwd} compat={compat}");
    // The attach stop was the SIGSTOP W0's detach
    // delivered; swallow it and run.
    cont_syscall(pid, 0);
}

/// Offering side of a handoff: detach a freshly
/// exec'd tracee with SIGSTOP so it stays stopped
/// with no tracer (it cannot run userland in
/// between), offer it to the target worker through
/// the coordinator, and wait briefly for the adopt
/// verdict. On any failure the offering tracer takes
/// the tracee back itself -- attach it, rebuild the
/// same ProcState, continue it -- so a failed handoff
/// degrades to the offering tracer keeping that pid
/// instead of losing it. W0 offers root-service
/// handoffs (root=true); a worker offering a kin
/// re-shard passes root=false.
fn do_handoff(
    pid: i32,
    twid: u8,
    root: bool,
    from: u8,
    procs: &mut HashMap<i32, ProcState>,
    vcreds: &mut HashMap<i32, (u32, u32)>,
    coord: &mut CoordClient,
) {
    let Some(ps) = procs.remove(&pid) else {
        return;
    };
    let creds = vcreds.remove(&pid).unwrap_or((0, 0));
    let path = ps.exec_path.clone().unwrap_or_default();
    if ptrace4(
        PTRACE_DETACH,
        pid,
        std::ptr::null_mut(),
        libc::SIGSTOP as *mut libc::c_void,
    ) != 0
    {
        sup!(
            "handoff: pid={pid} PTRACE_DETACH failed errno={}; keeping it on W{from}",
            errno()
        );
        procs.insert(pid, ps);
        vcreds.insert(pid, creds);
        cont_syscall(pid, 0);
        return;
    }
    sup!("handoff: pid={pid} W{from} -> W{twid} (exec {path})");
    coord.handoff_notice(pid, twid, &ps.vcwd, ps.compat, ps.sigmask, creds, root);
    let deadline =
        std::time::Instant::now() + std::time::Duration::from_millis(2000);
    let mut acked: Option<bool> = None;
    while acked.is_none() {
        if let Some(ok) = coord.take_adopt_ack(pid) {
            acked = Some(ok);
            break;
        }
        if coord.eof || std::time::Instant::now() >= deadline {
            break;
        }
        coord.pump();
        if coord.inbox.is_empty() && !coord.eof {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }
    if acked == Some(true) {
        return;
    }
    sup!("handoff: pid={pid} not adopted (ack={acked:?}); W{from} takes it back");
    coord.unregister_pid(pid);
    if ptrace4(PTRACE_ATTACH, pid, std::ptr::null_mut(), std::ptr::null_mut()) == 0 {
        let mut status: i32 = 0;
        let r = unsafe { libc::waitpid(pid, &mut status, WALL) };
        if r == pid && libc::WIFSTOPPED(status) {
            let mut ps = ps;
            ps.options_set = set_trace_options(pid);
            ps.started = true;
            procs.insert(pid, ps);
            vcreds.insert(pid, creds);
            coord.register_pid(pid, creds);
            cont_syscall(pid, 0);
            return;
        }
    }
    sup!(
        "handoff: pid={pid} take-back FAILED errno={}; tracee left stopped",
        errno()
    );
}

/// 0.9.141 (s9-141-desk S6): one servicer's
/// tracer-side face, printed by the worker that
/// owns it when the coordinator's wedge chain
/// names it. Every field is read off this worker's
/// own account for the thread: its in-flight call
/// (the Pending captured at its entry stop), the
/// futex face that call carries, its process
/// family's futex group on the same uaddr, and an
/// age in this worker's own emitted lines since
/// the thread's last processed stop. Nothing is
/// inferred across workers.
fn print_servicer_face(ss_arena: &str, x: i32, procs: &HashMap<i32, ProcState>) {
    let Some(proc) = procs.get(&x) else {
        return;
    };
    // This thread's process root inside this
    // worker: walk the parent chain to its top.
    let leader_of = |mut p: i32| -> i32 {
        for _ in 0..512 {
            match procs.get(&p) {
                Some(pr) if pr.parent != 0 && pr.parent != p && procs.contains_key(&pr.parent) => {
                    p = pr.parent;
                }
                _ => break,
            }
        }
        p
    };
    let leader = leader_of(x);
    let (last_syscall, state, futex_uaddr, futex_grp, last_op) = match &proc.pending {
        Some(pd) => {
            let ls = format!("{}({})", nr_name(proc.compat, pd.nr), pd.nr);
            let state = if pd.binder_parked {
                "parked-binder"
            } else if (proc.compat && pd.nr == 240) || (!proc.compat && pd.nr == 98) {
                "futex"
            } else {
                "parked-other"
            };
            let (ua, grp, op) = match pd.last_futex {
                Some((u, o, _)) => {
                    let n = procs
                        .iter()
                        .filter(|(p, pr)| {
                            **p != x
                                && leader_of(**p) == leader
                                && pr.pending
                                    .as_ref()
                                    .is_some_and(|q| q.last_futex.is_some_and(|(u2, _, _)| u2 == u))
                        })
                        .count()
                        + 1;
                    (
                        format!("0x{u:x}"),
                        if n == 1 {
                            "solo".to_string()
                        } else {
                            n.to_string()
                        },
                        if o == 9 { "WAIT_BITSET" } else { "WAIT" },
                    )
                }
                None => (
                    "-".to_string(),
                    "-".to_string(),
                    if pd.last_wake.is_some() { "WAKE" } else { "-" },
                ),
            };
            (ls, state, ua, grp, op)
        }
        None => (
            "-".to_string(),
            "running",
            "-".to_string(),
            "-".to_string(),
            "-",
        ),
    };
    let age = emit_seq_now().saturating_sub(proc.last_stop_seq);
    sup!(
        "binder: wedge-servicer-face arena={ss_arena} pid={x} last_syscall={last_syscall} state={state} futex_uaddr={futex_uaddr} futex_grp={futex_grp} last_op={last_op} age={age}"
    );
}

/// The tracing loop, shared verbatim by W0 and every
/// worker: it differs only in the TracerCtx it is fed
/// (root/shard map on W0, neither in workers).
/// Wedge forensics (0.9.122, telemetry only): when a
/// guest-sent SIGQUIT reaches a thread of the current
/// system_server candidate's family, print a one-shot
/// snapshot of every family thread's supervised state.
/// The S9 residual forensics found every surviving
/// system_server tenure now dies the same way: the
/// whole arena falls silent around span line ~10k and
/// the guest's own Watchdog executes it with
/// sig3 x2 -> sig9; the first sig3 is the last moment
/// the arena's state is still news. The snapshot
/// discriminates the two candidate worlds at that
/// instant: every thread idle-parked on the binder
/// driver (nobody is sending -- a sender / dependency
/// problem) versus threads stopped inside synchronous
/// calls awaiting replies (a peer problem). Purely
/// additive: callers (0.9.123: the kill-syscall hook
/// in the entry stop, primarily; the signal-delivery
/// stop as backstop) invoke this with the SIGQUIT's
/// target and leave signal handling exactly as
/// before. Returns true when the snapshot was
/// printed (the caller spends the one-shot).
fn wedge_snapshot(
    trig: i32,
    procs: &HashMap<i32, ProcState>,
    leader: i32,
    solo_out: &mut Option<i32>,
) -> bool {
    // Family membership: the tracer-side parent chain
    // (ProcState.parent, recorded at each birth event)
    // walks from any family thread up to the leader;
    // the leader's own parent is the shard root
    // (zygote), outside the family.
    let in_family = |mut cur: i32| -> bool {
        for _ in 0..256 {
            if cur == leader {
                return true;
            }
            match procs.get(&cur) {
                Some(p) if p.parent > 0 && p.parent != cur => {
                    cur = p.parent
                }
                _ => return false,
            }
        }
        false
    };
    if !in_family(trig) {
        return false;
    }
    // The snapshot is for the guest Watchdog's SIGQUIT.
    // A host-sent one must not spend the one-shot: the
    // DumpStacks path kill()s the candidate from this
    // very supervisor, and a manual dump an hour before
    // the wedge would leave nothing for the wedge. When
    // GETSIGINFO names a sender that is not one of our
    // tracees, stay silent. On the device GETSIGINFO
    // usually fails; an unreadable siginfo falls
    // through and the snapshot fires, as an unattended
    // run has no host dumps to confuse it with.
    {
        let compat = procs.get(&trig).map(|p| p.compat).unwrap_or(false);
        let mut buf = [0u8; 128];
        if ptrace4(
            PTRACE_GETSIGINFO,
            trig,
            std::ptr::null_mut(),
            buf.as_mut_ptr() as *mut libc::c_void,
        ) == 0
        {
            let sender = if compat {
                u32::from_ne_bytes(buf[12..16].try_into().unwrap()) as i32
            } else {
                u32::from_ne_bytes(buf[16..20].try_into().unwrap()) as i32
            };
            if sender > 0 && !procs.contains_key(&sender) {
                return false;
            }
        }
    }
    let mut family: Vec<i32> =
        procs.keys().copied().filter(|p| in_family(*p)).collect();
    family.sort_unstable();
    sup!(
        "binder: wedge-snapshot arena={leader} threads={}",
        family.len()
    );
    // 0.9.140 (M1): futex waiter groups by address,
    // accumulated inside the per-thread loop below
    // (the loop consumes the family vector).
    let mut futex_groups: Vec<(u32, Vec<i32>)> = Vec::new();
    for pid in family {
        let p = &procs[&pid];
        // State vocabulary, all from the thread's
        // existing Pending record:
        //   binder_parked -- held at a binder
        //     WRITE_READ entry stop, waiting for the
        //     virtual driver to grow data (park=binder).
        //   expect_exit with a pending record -- inside
        //     that syscall now, in-kernel or held
        //     (park=syscall; last_syscall names it).
        //   anything else -- no call in flight from the
        //     supervisor's seat (a fake's record retained
        //     past its exit stop does not count);
        //     park=running, last_syscall=-.
        // last_read_lines_ago has no honest source: the
        // worker keeps no event / log-line sequence, so
        // the field prints - rather than a fabricated
        // age.
        let (last_syscall, park) = match &p.pending {
            Some(pend) if pend.binder_parked => (
                format!("{}({})", nr_name(p.compat, pend.nr), pend.nr),
                "binder",
            ),
            Some(pend) if p.expect_exit => (
                format!("{}({})", nr_name(p.compat, pend.nr), pend.nr),
                "syscall",
            ),
            _ => ("-".to_string(), "running"),
        };
        // 0.9.140 (M1): the thread's futex face, from
        // the entry capture in its in-flight Pending
        // (see Pending::last_futex). Threads not inside
        // a futex keep the pre-.140 line byte for byte.
        // A thread inside a WAIT-family futex is also
        // counted into the snapshot's address groups
        // below.
        let mut futex_face = String::new();
        if let Some(pend) = &p.pending {
            if let Some((u, op, v)) = pend.last_futex {
                futex_face.push_str(&format!(
                    " futex_uaddr=0x{u:x} op={} val={v}",
                    match op {
                        0 => "WAIT".to_string(),
                        9 => "WAIT_BITSET".to_string(),
                        n => n.to_string(),
                    }
                ));
                match futex_groups.iter_mut().find(|(a, _)| *a == u) {
                    Some((_, ws)) => ws.push(pid),
                    None => futex_groups.push((u, vec![pid])),
                }
            }
            if let Some((u, v)) = pend.last_wake {
                futex_face
                    .push_str(&format!(" last_wake_uaddr=0x{u:x} last_wake_val={v}"));
            }
        }
        sup!(
            "binder: wedge-thread pid={pid} last_syscall={last_syscall} park={park} last_read_lines_ago=-{futex_face}"
        );
    }
    // 0.9.140 (M1): group the family's in-flight futex
    // waiters by the address they wait on. A group with
    // several waiters is the AMS monitor's futex word
    // (the queue); a solo group's waiter waits on an
    // object of its own -- in the wedge taxonomy it is
    // the monitor holder, and naming it here is what
    // lets the chain dump (M3) and the traces harvest
    // (M5) point at the same thread. The holder is
    // only named when exactly one solo group exists:
    // two private waits would leave it ambiguous.
    {
        futex_groups.sort_unstable();
        let mut solo_groups = 0usize;
        let mut solo_pid = 0i32;
        for (u, ws) in &futex_groups {
            sup!(
                "binder: wedge-futex arena={leader} uaddr=0x{u:x} waiters=[{}]{}",
                ws.iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                if ws.len() == 1 { " solo" } else { "" }
            );
            if ws.len() == 1 {
                solo_groups += 1;
                solo_pid = ws[0];
            }
        }
        if solo_groups == 1 {
            *solo_out = Some(solo_pid);
        }
    }
    true
}

/// 0.9.140 (s9-140-desk-ignition M3): the chain dump
/// rides the wedge snapshot's one-shot. The snapshot
/// itself is tracer-side state, but the serving
/// stacks, the outstanding waits and the park kinds
/// live in the coordinator's BinderState, so they are
/// requested over the request/reply channel (the
/// oneway log channel provably loses lines under
/// cap_clear at exactly this pressure) and replayed
/// here, in order, straight after the snapshot lines.
/// The holder the coordinator's provisional verdict
/// names is kept for the traces harvest (M5).
fn fire_wedge_chain(
    coord: &mut CoordClient,
    leader: i32,
    solo: Option<i32>,
    wedge_leader: &mut Option<i32>,
    wedge_holder: &mut Option<i32>,
) {
    let (logs, holder, _servicers) = coord.wedge_chain(leader, solo.unwrap_or(0));
    replay_logs(logs);
    *wedge_leader = Some(leader);
    *wedge_holder = if holder > 0 { Some(holder) } else { None };
}

/// 0.9.140 (s9-140-desk-ignition M5): per-tenure
/// traces preservation. The guest's /data/anr/
/// traces.txt only ever holds the LAST tenure's
/// Watchdog dumps -- the next tenure's first dump
/// overwrites it -- so a wedged tenure's Java stacks
/// have to be lifted out of the file between its
/// death and its successor's birth; that is what
/// made per-tenure classification a lottery in every
/// field before this one. Runs tracer-side at the
/// dead leader's reap: a direct host read of the
/// rootfs file (no guest cooperation, no binder
/// channel), printed on the session log's own
/// immediate-write channel. Only the dead leader's
/// own (last) section is read; from it, the main
/// thread's block, the chain dump's named holder's
/// block, and any block whose text names a wedge
/// keyword are kept, capped at roughly 200 printed
/// lines. A file that no longer holds this leader's
/// section is a miss, printed as one, never papered
/// over.
/// 0.9.141 (s9-141-desk S5): the holder match is
/// fixed -- block headers carry Dalvik tids (small
/// integers) while the holder is a host pid, so the
/// identity arm never fired in .140; the holder is
/// now matched against the sysTid= each block body
/// states, in the same number space. The main block
/// is recognised by tid==1 or its name. Kept-block
/// lines name the block by tid= (with systid= when
/// the body states one). When the selection still
/// keeps nothing, the whole section is excerpted
/// instead: main first, then the monitor-graph
/// blocks, then file order, 30 lines per block,
/// 400 lines in total.
fn wedge_traces_harvest(rootfs: &str, leader: i32, holder: i32) {
    let path = format!("{rootfs}/data/anr/traces.txt");
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            sup!("binder: wedge-traces-miss arena={leader} why=unreadable ({e})");
            return;
        }
    };
    // Sections begin "----- pid <pid> at ... -----";
    // collect their start offsets, then take the LAST
    // section naming this leader.
    let mut starts: Vec<usize> = Vec::new();
    let mut from = 0usize;
    while let Some(i) = text[from..].find("----- pid ") {
        starts.push(from + i);
        from += i + 10;
    }
    starts.push(text.len());
    let mut section: Option<&str> = None;
    for w in starts.windows(2) {
        let seg = &text[w[0]..w[1]];
        let num: String = seg[10..]
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        if num.parse::<i32>() == Ok(leader) {
            section = Some(seg);
        }
    }
    let Some(section) = section else {
        sup!(
            "binder: wedge-traces-miss arena={leader} why=no-section (file holds a later tenure, or the dump never landed)"
        );
        return;
    };
    // Thread blocks begin at lines starting with '"'
    // and run to the next block; a block's header
    // carries its guest tid as tid=<n>. The section's
    // preamble (header, Cmd line) belongs to no block
    // and is skipped. 0.9.141: each block also yields
    // the host-space sysTid= its body lines state
    // (the "  | sysTid=<n> ..." group line), the
    // number space holder pids live in.
    let mut blocks: Vec<(i32, String, Vec<&str>, Option<i32>)> = Vec::new();
    for ln in section.lines() {
        if ln.starts_with('"') {
            let name = ln[1..].split('"').next().unwrap_or("").to_string();
            let tid = ln
                .split("tid=")
                .nth(1)
                .map(|s| {
                    s.chars()
                        .take_while(|c| c.is_ascii_digit())
                        .collect::<String>()
                })
                .and_then(|s| s.parse::<i32>().ok())
                .unwrap_or(0);
            blocks.push((tid, name, Vec::new(), None));
        }
        if let Some(b) = blocks.last_mut() {
            b.2.push(ln);
            if b.3.is_none() {
                if let Some(rest) = ln.split("sysTid=").nth(1) {
                    let num: String =
                        rest.chars().take_while(|c| c.is_ascii_digit()).collect();
                    b.3 = num.parse::<i32>().ok();
                }
            }
        }
    }
    let is_main = |tid: i32, name: &str| tid == 1 || name == "main";
    let mut printed = 0usize;
    let mut kept = 0usize;
    for (tid, name, blines, systid) in &blocks {
        let body = blines.join("\n");
        let keep = is_main(*tid, name)
            || (holder > 0 && *systid == Some(holder))
            || body.contains("AppErrorResult")
            || body.contains("Surface")
            || body.contains("createSurfaceLocked");
        if !keep {
            continue;
        }
        kept += 1;
        match systid {
            Some(s) => sup!(
                "binder: wedge-traces arena={leader} tid={tid} systid={s} name={name} lines={}",
                blines.len()
            ),
            None => sup!(
                "binder: wedge-traces arena={leader} tid={tid} name={name} lines={}",
                blines.len()
            ),
        }
        for ln in blines {
            if printed >= 200 {
                break;
            }
            sup!("binder: wedge-traces arena={leader} tid={tid} | {ln}");
            printed += 1;
        }
        if printed >= 200 {
            sup!("binder: wedge-traces arena={leader} truncated at 200 lines");
            break;
        }
    }
    if kept == 0 {
        if blocks.is_empty() {
            sup!(
                "binder: wedge-traces arena={leader} (section found; no main, holder or keyword block in it)"
            );
        } else {
            // 0.9.141 (S5): selection found nothing --
            // excerpt the whole section instead of
            // reporting an empty harvest: main blocks
            // first, then the blocks carrying the
            // monitor graph, then the rest in file
            // order; 30 lines per block, 400 total.
            sup!(
                "binder: wedge-traces arena={leader} fallback=whole-section blocks={}",
                blocks.len()
            );
            let mut order: Vec<usize> = Vec::new();
            for (i, (tid, name, _, _)) in blocks.iter().enumerate() {
                if is_main(*tid, name) {
                    order.push(i);
                }
            }
            for (i, (_, _, blines, _)) in blocks.iter().enumerate() {
                if order.contains(&i) {
                    continue;
                }
                let body = blines.join("\n");
                if body.contains("waiting to lock") || body.contains("held by") {
                    order.push(i);
                }
            }
            for i in 0..blocks.len() {
                if !order.contains(&i) {
                    order.push(i);
                }
            }
            let mut total = 0usize;
            'fb: for i in order {
                let (tid, name, blines, systid) = &blocks[i];
                match systid {
                    Some(s) => sup!(
                        "binder: wedge-traces arena={leader} tid={tid} systid={s} name={name} lines={}",
                        blines.len()
                    ),
                    None => sup!(
                        "binder: wedge-traces arena={leader} tid={tid} name={name} lines={}",
                        blines.len()
                    ),
                }
                for ln in blines.iter().take(30) {
                    if total >= 400 {
                        sup!(
                            "binder: wedge-traces arena={leader} fallback truncated at 400 lines"
                        );
                        break 'fb;
                    }
                    sup!("binder: wedge-traces arena={leader} tid={tid} | {ln}");
                    total += 1;
                }
            }
        }
    }
}

fn tracer_loop(ctx: TracerCtx) {
    let TracerCtx {
        wid,
        rootfs,
        bb_path,
        loader_path,
        guest_compat,
        root_pid,
        mut coord,
        mut procs,
        mut vcreds,
        mut wakes,
        mut root_launched,
        mut seen,
        mut counts,
        shard_map,
        kin_target,
        mut shard_root,
        mut dump_candidate,
    } = ctx;
    let selfpipe_rd = install_sigchld_pipe();
    if selfpipe_rd < 0 {
        sup!("WARN: SIGCHLD self-pipe failed; stop wakeups ride coordinator traffic only");
    }

    // Wedge forensics (0.9.122): one snapshot per
    // system_server tenure, spent by the first
    // guest-sent SIGQUIT to reach a family thread (see
    // wedge_snapshot); reset whenever the candidate
    // slot changes hands.
    let mut wedge_snapped = false;
    // 0.9.140 (M5): the tenure the wedge snapshot last
    // fired for, and the holder its chain dump (M3)
    // named; consumed by the traces harvest when that
    // tenure's leader dies (see wedge_traces_harvest).
    let mut wedge_leader: Option<i32> = None;
    let mut wedge_holder: Option<i32> = None;

    // ---- main tracing loop over the whole guest tree ----
    // (S2: one loop body for every tracer process. The
    // head asks next_stop for the next ptrace stop;
    // next_stop also drains coordinator pushes and is
    // where a worker learns the run is over.)
    'main_loop: loop {
        let (pid, status) = match next_stop(
            wid,
            &mut coord,
            &mut procs,
            &mut vcreds,
            &mut shard_root,
            &mut dump_candidate,
            selfpipe_rd,
        ) {
            NextStop::Stop(p, s) => (p, s),
            NextStop::End => break 'main_loop,
        };

        if libc::WIFEXITED(status) || libc::WIFSIGNALED(status) {
            if pid != root_pid && !procs.contains_key(&pid) {
                // Not a tracee of ours: a process child of
                // this tracer (a worker, the coordinator)
                // reaped by the shared waitpid. Only W0 can
                // see these; no guest state belongs to it.
                sup!("non-tracee child exited pid={pid} status={status:#x}");
                continue;
            }
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
            // Freeze forensics (0.9.81): a dead dump
            // candidate gives up its slot; a later
            // zygote tenure's system_server re-earns it
            // at its own birth.
            if dump_candidate == Some(pid) {
                // 0.9.140 (M5): lift this tenure's Java
                // stacks out of traces.txt before the
                // slot changes hands -- the file is only
                // overwritten by the NEXT tenure's first
                // ANR dump, so the dead leader's reap is
                // inside the preservation window by
                // construction.
                if wedge_snapped && wedge_leader == Some(pid) {
                    wedge_traces_harvest(
                        &rootfs,
                        pid,
                        wedge_holder.unwrap_or(0),
                    );
                }
                wedge_leader = None;
                wedge_holder = None;
                dump_candidate = None;
                wedge_snapped = false;
            }
            // S5c: if that was the arena's last thread,
            // run the driver's death processing; it may
            // wake parked tracees (death notices, dead
            // replies), completed like any other wake. The
            // sequence runs in the coordinator
            // (binder_thread_exit); no arena registered
            // for this thread means None, as the old early
            // return did.
            if let Some((logs, dwakes)) = coord.thread_exit(pid) {
                replay_logs(logs);
                for wpid in dwakes {
                    if wpid != pid {
                        if procs.contains_key(&wpid) {
                            complete_parked(wpid, &mut procs, &mut coord);
                        } else {
                            // Another worker's parked
                            // tracee: route the wake
                            // through the coordinator.
                            coord.wake_route(wpid);
                        }
                    }
                }
            }
            coord.unregister_pid(pid);
            coord.oneway_park_remove(pid);
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

        let mut pending_handoff: Option<(i32, u8, bool)> = None;
        // Wedge forensics (0.9.123): a kill-family entry
        // stop that aims SIGQUIT at a pid records the
        // target here; the snapshot fires after the
        // stop's handlers release their &mut borrow of
        // procs (mirrors pending_handoff).
        let mut wedge_kill_target: Option<i32> = None;
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
                    mprot: None,
                    last_futex: None,
                    last_wake: None,
                };
                if proc.compat && nr == 125 {
                    pend.mprot = Some((regs.arg(0), regs.arg(2)));
                }
                // 0.9.140 (M1): futex entry capture, at
                // the same seat the peercred / killfam
                // argument captures read -- the entry
                // stop's registers, pure reads, nothing
                // rewritten (futex passes through this
                // engine untouched). The WAIT family
                // keeps (uaddr, op, val), the WAKE family
                // (uaddr, nr_wake), the op masked with
                // the futex command mask (0x7f): the
                // private / clock bits ride above it and
                // are not part of the command the wedge
                // snapshot names.
                if (proc.compat && nr == 240) || (!proc.compat && nr == 98) {
                    let op = regs.arg(1) as u32 & 0x7f;
                    match op {
                        0 | 9 => {
                            pend.last_futex = Some((
                                regs.arg(0) as u32,
                                op,
                                regs.arg(2) as u32,
                            ));
                        }
                        1 | 10 => {
                            pend.last_wake =
                                Some((regs.arg(0) as u32, regs.arg(2) as u32));
                        }
                        _ => {}
                    }
                }
                // 0.9.141 (P3): assembly-window
                // counters for this thread (see
                // WinProfile): entry stops, futex
                // WAIT entries and the allocator
                // family. Pure bookkeeping on values
                // already in hand.
                proc.win.stops += 1;
                proc.last_stop_seq = emit_seq_now();
                if pend.last_futex.is_some() {
                    proc.win.futex += 1;
                }
                if (proc.compat && matches!(nr, 45 | 91 | 192))
                    || (!proc.compat && matches!(nr, 214 | 215 | 222))
                {
                    proc.win.alloc += 1;
                }
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
                    let (desc, d, xpath) = entry_exec(
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
                    // The handoff decision at this exec's
                    // exit stop keys off these two, armed
                    // for that one stop only (0.9.60).
                    proc.exec_path = xpath;
                    proc.exec_blocked = pend.inject.is_some();
                    proc.exec_armed = true;
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
                                &mut coord,
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
                } else if proc.compat && nr == 282 && sockaddr_family(pid, regs.arg(1)) == Some(libc::AF_NETLINK as u16) {
                    // bind with a netlink sockaddr: the
                    // uevent socket substituted below is a
                    // unix socket in truth, and the host
                    // kernel would refuse a netlink address
                    // on it (EAFNOSUPPORT) -- on real
                    // hardware this bind is what enrolls the
                    // socket for kernel uevents, which this
                    // engine never delivers anyway. Answer
                    // success without the kernel. (A guest
                    // binding a REAL netlink socket would
                    // also land here; no GB component binds
                    // one explicitly -- route sockets are
                    // kernel-bound implicitly on first send.)
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(
                        "bind(282) netlink sockaddr FAKED -> 0 (virtual uevent socket)"
                            .to_string(),
                    );
                    dirty = true;
                } else if proc.compat && nr == 281
                    && regs.arg(0) == libc::AF_NETLINK as u64
                    && regs.arg(2) == 15
                {
                    // socket(AF_NETLINK, _, NETLINK_KOBJECT_
                    // UEVENT): the host SELinux policy denies
                    // netlink uevent sockets to app processes
                    // outright (0.9.83 field: netd exited 63
                    // tenures in a row on "Unable to create
                    // uevent socket: Permission denied", and
                    // NetworkManagementService's create()
                    // latch never released). Substitute a
                    // plain unix datagram socket: real fd,
                    // blocks in select/recv forever, never
                    // readable -- semantically a uevent
                    // socket on hardware that never changes.
                    // netd's real work runs on the separate
                    // init-provided command socket, which is
                    // untouched. arg0 family -> AF_UNIX,
                    // arg2 protocol -> 0; type (arg1) kept.
                    regs.set_arg(0, libc::AF_UNIX as u64);
                    regs.set_arg(2, 0);
                    pend.desc = Some(
                        "socket(281) netlink uevent -> unix dgram (virtual uevent socket)"
                            .to_string(),
                    );
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
                    // An mprotect that adds PROT_EXEC.
                    // On a virtual-ashmem VMA the host
                    // refuses it outright (-13), no matter
                    // the mapping's current perms -- the
                    // 0.9.31 maps evidence shows the denied
                    // VMA rw-p over our region file while a
                    // libc VMA in the same process sits
                    // rwxp and passes. The mspace is
                    // MAP_PRIVATE, so its pages are
                    // process-local: satisfy the call by
                    // remapping the range anonymous with
                    // its contents preserved (0.9.32).
                    // Anonymous exec transitions ride on
                    // the app domain's execmem grant, the
                    // same reason ART's JIT works.
                    let addr = regs.arg(0);
                    let len = regs.arg(1);
                    let prot = regs.arg(2);
                    let page_start = addr & !0xfff;
                    let page_end = (addr + len + 0xfff) & !0xfff;
                    let mut handled = false;
                    if page_end > page_start
                        && page_end - page_start <= (8 << 20)
                    {
                        if let Some((vlo, vhi, _p, path)) =
                            vma_range(pid, addr)
                        {
                            if path.contains("/.ashmem/")
                                && page_start >= vlo
                                && page_end <= vhi
                            {
                                if let Some(contents) = read_mem_vec(
                                    pid,
                                    page_start,
                                    (page_end - page_start) as usize,
                                ) {
                                    skip_syscall(pid, &mut regs, &mut pend, 0);
                                    let r = inject_mmap(
                                        pid,
                                        proc.compat,
                                        page_start,
                                        page_end - page_start,
                                        prot,
                                        &mut regs,
                                    );
                                    // The ride's result is a
                                    // 32-bit address in a
                                    // 64-bit register read as
                                    // signed: compare in u32,
                                    // or every success looks
                                    // like a huge negative
                                    // (0.9.32's bug -- the mmap
                                    // landed and the contents
                                    // restore was skipped).
                                    if (r as u32) == (page_start as u32)
                                        && write_mem(pid, page_start, &contents)
                                            .is_ok()
                                    {
                                        regs.set_retval(0);
                                        if set_regs(pid, &regs) {
                                            pend.applied = true;
                                        }
                                        sup!(
                                            "mprotect: ashmem range {page_start:#x}..{page_end:#x} of pid={pid} converted to anonymous ({} bytes preserved)",
                                            contents.len()
                                        );
                                    } else {
                                        pend.inject = Some(-13);
                                        regs.set_retval(-13);
                                        if set_regs(pid, &regs) {
                                            pend.applied = true;
                                        }
                                        sup!(
                                            "mprotect: anonymous conversion FAILED for pid={pid} at {page_start:#x} (ride={r}); guest gets -13 as before"
                                        );
                                    }
                                    handled = true;
                                }
                            }
                        }
                    }
                    pend.desc = Some(format!(
                        "mprotect EXEC addr=0x{addr:x} len={len} prot={prot:#x}{}",
                        if handled { " (ashmem conversion attempted)" } else { "" }
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
                        &mut coord,
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
                    coord.vcred_publish(pid, (vu, vg));
                    pend.desc = Some(format!(
                        "{}({}) emulated (return 0); virtual creds now uid={vu} gid={vg}",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else if is_capset(proc.compat, nr) {
                    // Virtual capabilities (see is_capset):
                    // the guest's capability sets belong to
                    // its emulated credential state. Passed
                    // through, the host kernel refuses any
                    // nonzero request -- the app holds no
                    // real caps -- and GB's specialization
                    // aborts the child over it (S8 gun 1).
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(format!(
                        "{}({}) FAKED -> 0 (virtual caps)",
                        nr_name(proc.compat, nr),
                        nr
                    ));
                    dirty = true;
                } else if proc.compat && nr == 294
                    && regs.arg(1) == libc::SOL_SOCKET as u64
                    && matches!(regs.arg(2), 32 | 33)
                {
                    // setsockopt(SOL_SOCKET, SO_SNDBUF-
                    // FORCE / SO_RCVBUFFORCE): the FORCE
                    // variants exist for root daemons --
                    // they bypass the net buffer sysctls
                    // and demand CAP_NET_ADMIN, which the
                    // host app does not hold (0.9.84 field:
                    // netd and vold both died every tenure
                    // on "Unable to set uevent socket
                    // SO_RCVBUFFORCE option: Operation not
                    // permitted" right after the uevent
                    // socket substitution let them start).
                    // The forced size is advisory -- the
                    // receive buffer governs uevent burst
                    // absorption, and the virtual uevent
                    // socket never delivers at all. Answer
                    // success without the kernel.
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(
                        "setsockopt(294) BUFFORCE FAKED -> 0 (virtual caps)"
                            .to_string(),
                    );
                    dirty = true;
                } else if is_ioprio(proc.compat, nr) {
                    // I/O priority (see is_ioprio): the
                    // host seccomp filter traps this call
                    // with SIGSYS; unrescued it killed
                    // every vold service child in init's
                    // pre-exec setup (0.9.83 field).
                    // Answer success without the kernel.
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(format!(
                        "{}({}) FAKED -> 0 (virtual ioprio)",
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
                    coord.oneway_thread_arena(pid, &arena);
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
                    let key = fd_ashmem(pid, regs.arg(4) as i32).unwrap();
                    let name = key.rsplit('/').next().unwrap_or("").to_string();
                    // Born-exec for PRIVATE region mappings
                    // (0.9.29): the host denies adding
                    // PROT_EXEC to an already-live file VMA
                    // (the mprotect comes back -13 and
                    // pixelflinger's assembler dies on the
                    // NULLed base), while mappings BORN with
                    // exec -- every guest library -- take the
                    // same mprotect without complaint. A
                    // private region's contents never leave
                    // this process (the mspace JIT cache is
                    // the case that matters), so let the
                    // mapping be born RWX and the later
                    // mprotect becomes a no-transition. SHARED
                    // regions (surface heaps) keep the
                    // guest's prot exactly.
                    let upgraded = regs.arg(3) & 1 == 0 && regs.arg(2) & 4 == 0;
                    if upgraded {
                        regs.set_arg(2, regs.arg(2) | 4);
                        dirty = true;
                    }
                    pend.desc = Some(format!(
                        "mmap({nr}) pid={pid} virtual ashmem {name} len={} prot={} flags=0x{:x} (passed through{})",
                        regs.arg(1),
                        regs.arg(2),
                        regs.arg(3),
                        if upgraded { "; prot upgraded +EXEC" } else { "" }
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
                        &mut coord,
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
                    coord.oneway_thread_arena(pid, &arena);
                    match regs.arg(1) as u32 {
                        BINDER_VERSION => {
                            let _ = write_mem(pid, regs.arg(2), &7u32.to_le_bytes());
                            skip_syscall(pid, &mut regs, &mut pend, 0);
                            pend.desc = Some("binder VERSION -> 7".to_string());
                        }
                        BINDER_SET_CONTEXT_MGR => {
                            // Registration and the pending
                            // flush run in the coordinator
                            // (binder_set_context_mgr): it
                            // delivers everything clients
                            // addressed to the manager before
                            // it existed (0.9.24); their
                            // senders are parked in their
                            // read sides and complete through
                            // the normal wake path. The flush
                            // effects (wakes only, by
                            // construction) execute at this
                            // stop, as the old inline
                            // version's did.
                            let (ok, logs, flush_actions, delivered, total) =
                                coord.set_context_mgr(pid, &arena);
                            replay_logs(logs);
                            if ok && total > 0 {
                                let _ = exec_binder_actions(
                                    pid,
                                    proc.compat,
                                    &mut regs,
                                    &mut pend,
                                    &mut coord,
                                    flush_actions,
                                    &mut wakes,
                                );
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
                            coord.oneway_thread_exit_ioctl(pid, &arena);
                            skip_syscall(pid, &mut regs, &mut pend, 0);
                            pend.desc = Some("binder THREAD_EXIT".to_string());
                        }
                        BINDER_WRITE_READ => {
                            // S1b split: pre-read the
                            // ioctl's inputs (the 24-byte
                            // bwr struct, then the write
                            // stream under the same
                            // condition the decision used
                            // inline), let the coordinator
                            // decide, then execute its
                            // actions at this stop. The
                            // sender's virtual euid travels
                            // with the request (vcreds stays
                            // on this side); parcel bytes
                            // the decision still needs are
                            // read back through the reverse
                            // channel inside the rpc.
                            let bwr_addr = regs.arg(2);
                            let bwr = read_mem_vec(pid, bwr_addr, 24);
                            let stream = match &bwr {
                                Some(b) => {
                                    let ws = u32_at(b, 0);
                                    let wc0 = u32_at(b, 4);
                                    let wb = u32_at(b, 8);
                                    if ws > wc0 && ws <= (1 << 20) {
                                        read_mem_vec(
                                            pid,
                                            (wb + wc0) as u64,
                                            (ws - wc0) as usize,
                                        )
                                    } else {
                                        None
                                    }
                                }
                                None => None,
                            };
                            // 0.9.141 (P1/P3): one walk
                            // over the presented stream
                            // before the rpc: count its
                            // transactions and replies
                            // for the window profile, and
                            // snapshot up to four BC_
                            // REPLY buffers (data VA,
                            // declared size, first
                            // min(size,128) bytes) as
                            // the guest presented them.
                            // The coordinator's copy of
                            // a reply happens inside the
                            // rpc; the re-read after the
                            // actions have executed
                            // brackets that instant --
                            // the issuance window made
                            // observable in this split.
                            let mut win_ntxn = 0u32;
                            let mut win_nreply = 0u32;
                            let mut iss_snaps: Vec<(u32, u32, Vec<u8>)> = Vec::new();
                            if let Some(s) = stream.as_deref() {
                                let mut cur = 0usize;
                                while cur + 4 <= s.len() {
                                    let cmd = u32_at(s, cur);
                                    let adv = match cmd {
                                        BC_ENTER_LOOPER
                                        | BC_REGISTER_LOOPER
                                        | BC_EXIT_LOOPER => 4,
                                        BC_FREE_BUFFER
                                        | BC_INCREFS
                                        | BC_ACQUIRE
                                        | BC_RELEASE
                                        | BC_DECREFS
                                        | BC_DEAD_BINDER_DONE => 8,
                                        BC_INCREFS_DONE
                                        | BC_ACQUIRE_DONE
                                        | BC_ATTEMPT_ACQUIRE
                                        | BC_REQUEST_DEATH_NOTIFICATION
                                        | BC_CLEAR_DEATH_NOTIFICATION => 12,
                                        BC_TRANSACTION | BC_REPLY => 44,
                                        _ => break,
                                    };
                                    if cur + adv > s.len() {
                                        break;
                                    }
                                    if cmd == BC_TRANSACTION {
                                        win_ntxn += 1;
                                    }
                                    if cmd == BC_REPLY {
                                        win_nreply += 1;
                                        if iss_snaps.len() < 4 {
                                            let dsize = u32_at(s, cur + 28);
                                            let daddr = u32_at(s, cur + 36);
                                            let want =
                                                (dsize as usize).min(128);
                                            if want > 0 {
                                                if let Some(bytes) =
                                                    read_mem_vec(
                                                        pid, daddr as u64, want,
                                                    )
                                                {
                                                    iss_snaps.push((
                                                        daddr, dsize, bytes,
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                    cur += adv;
                                }
                            }
                            let win_snap = (
                                proc.win.stops,
                                proc.win.futex,
                                proc.win.alloc,
                                proc.win.parks,
                                proc.win.sends,
                                proc.win.maxdepth,
                            );
                            if win_ntxn > 0 {
                                proc.win.sends += 1;
                            }
                            if win_nreply > 0 {
                                proc.win.depth =
                                    (proc.win.depth - win_nreply as i32).max(0);
                            }
                            let veuid = vcreds.get(&pid).copied().unwrap_or((0, 0)).0;
                            let (desc, logs, actions) = coord.write_read(
                                pid,
                                proc.compat,
                                veuid,
                                &arena,
                                bwr_addr,
                                bwr,
                                stream,
                                win_snap,
                            );
                            replay_logs(logs);
                            if let Some(f) = exec_binder_actions(
                                pid,
                                proc.compat,
                                &mut regs,
                                &mut pend,
                                &mut coord,
                                actions,
                                &mut wakes,
                            ) {
                                proc.last_binder_read = Some(f);
                                // 0.9.141 (P3): the fill
                                // just delivered deepens
                                // this thread's serving
                                // window by its trans-
                                // action count.
                                if let Some(fb) =
                                    read_mem_vec(pid, f.0 as u64, f.1 as usize)
                                {
                                    let n = count_br_transactions(&fb);
                                    if n > 0 {
                                        proc.win.depth += n as i32;
                                        let d = proc.win.depth.max(0) as u32;
                                        if d > proc.win.maxdepth {
                                            proc.win.maxdepth = d;
                                        }
                                    }
                                }
                            }
                            // 0.9.141 (P1): re-read the
                            // snapshotted reply buffers
                            // now the decision (and its
                            // copy) has completed, the
                            // guest still stopped at
                            // this entry stop. A buffer
                            // that reads back different
                            // changed inside the window
                            // -- the issuance-time sub-
                            // form of the poison family.
                            if !iss_snaps.is_empty() {
                                let mut differs = 0u32;
                                for (daddr, dsize, entry) in &iss_snaps {
                                    let Some(now) = read_mem_vec(
                                        pid,
                                        *daddr as u64,
                                        entry.len(),
                                    ) else {
                                        continue;
                                    };
                                    if now != *entry {
                                        differs += 1;
                                        let ef = if entry.len() >= 4 {
                                            u32_at(entry, 0)
                                        } else {
                                            0
                                        };
                                        let xf = if now.len() >= 4 {
                                            u32_at(&now, 0)
                                        } else {
                                            0
                                        };
                                        sup!(
                                            "binder: reply issuance differs pid={pid} daddr=0x{daddr:x} size={dsize} entry_first=0x{ef:08x} exit_first=0x{xf:08x} entry_head={} exit_head={}",
                                            hex_head(entry, 32),
                                            hex_head(&now, 32)
                                        );
                                    }
                                }
                                coord.oneway_issuance_stats(
                                    iss_snaps.len() as u32,
                                    differs,
                                );
                            }
                            if win_nreply > 0 {
                                // 0.9.141 (P3): the
                                // window closes at this
                                // thread's forwarded
                                // reply; the counters
                                // restart, the depth
                                // carries over.
                                proc.win.stops = 0;
                                proc.win.futex = 0;
                                proc.win.alloc = 0;
                                proc.win.parks = 0;
                                proc.win.sends = 0;
                                proc.win.maxdepth =
                                    proc.win.depth.max(0) as u32;
                            }
                            if pend.binder_parked {
                                proc.win.parks += 1;
                            }
                            pend.desc = Some(desc);
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
                    // 0.9.63 telemetry: kill-family calls
                    // always log their arguments -- a
                    // pass-through kill is otherwise
                    // invisible, and 0.9.62's field run
                    // lost every SurfaceFlinger on W2 to
                    // an unexplained realtime signal (35).
                    let killfam = if proc.compat {
                        matches!(nr, 37 | 238 | 270)
                    } else {
                        matches!(nr, 129 | 130 | 131)
                    };
                    if killfam {
                        let (target, signum) =
                            if nr == 270 || nr == 131 {
                                (regs.arg(1), regs.arg(2))
                            } else {
                                (regs.arg(0), regs.arg(1))
                            };
                        sys!(
                            "{}({}) killfam pid={pid} target={target} sig={signum} (pass)",
                            nr_name(proc.compat, nr),
                            nr
                        );
                        // Wedge forensics (0.9.123): a
                        // SIGQUIT aimed at a named pid is
                        // a snapshot candidate; family
                        // membership is judged when the
                        // target is consumed below.
                        if signum == 3 {
                            wedge_kill_target = Some(target as i32);
                        }
                    }
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
                proc.sigsys_preentry = 0;
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
                        if procs.contains_key(&wpid) {
                            complete_parked(wpid, &mut procs, &mut coord);
                        } else {
                            coord.wake_route(wpid);
                        }
                    }
                }
            } else {
                // ---- syscall-exit stop ----
                // 0.9.141 (P3/S6): the exit half of the
                // window stop count, and the tracee's
                // last-activity mark for the face age.
                proc.win.stops += 1;
                proc.last_stop_seq = emit_seq_now();
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
                            // 0.9.31: name the denied VMA and
                            // the caller's context.
                            let (addr, prot) = pend.mprot.unwrap_or((0, 0));
                            sup!(
                                "mprotect FAILED pid={pid} ret={ret} addr={addr:#x} prot={prot:#x} vma=[{}] ctx=[{}]",
                                vma_desc(pid, addr),
                                selinux_ctx(pid)
                            );
                        }
                        if proc.compat
                            && pend.nr == 125
                            && ret == 0
                            && pend.mprot.is_some_and(|(_, p)| p & 7 == 7)
                            && !MPROT_OK_SAMPLED.swap(
                                true,
                                std::sync::atomic::Ordering::Relaxed,
                            )
                        {
                            // Success-side sample (0.9.31):
                            // the first RWX mprotect the host
                            // ACCEPTS, with its VMA named --
                            // the contrast case for the
                            // denials above.
                            let (addr, _) = pend.mprot.unwrap();
                            sup!(
                                "mprotect RWX ok sample pid={pid} addr={addr:#x} vma=[{}] ctx=[{}]",
                                vma_desc(pid, addr),
                                selinux_ctx(pid)
                            );
                        }
                        if let Some((optval, optlen)) = pend.peercred {
                            if ret == 0 {
                                patch_peercred(pid, optval, optlen, &vcreds, &mut coord);
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
                                coord.oneway_arena_register(pid, arena, r32, *maplen);
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
                        proc.sigsys_preentry = 0;
                proc.pending = Some(pend);
                    }
                }
                proc.expect_exit = false;
                // Handoff decisions, at the exit stop of
                // the exec that armed them. Root-service
                // rule (W0 only): a direct child of the
                // guest root whose decided image belongs
                // to a worker shard changes tracer here.
                // Kin rule (a worker with a kin target):
                // a direct child of this worker's shard
                // root, exec'ing any image other than the
                // root's own, moves to the kin worker.
                // The exec's pend is settled above exactly
                // as if it continued with us; the transfer
                // itself runs after this branch, once the
                // procs borrow is over. A blocked exec
                // never changed image, so it never hands
                // off.
                let mut ho: Option<(u8, bool)> = None;
                if proc.exec_armed && (wid == 0 || kin_target.is_some()) {
                    // 0.9.60: decide only at the exit stop
                    // of the exec that armed this, and say
                    // the outcome out loud (the 0.9.59
                    // latch burned silently at a child's
                    // first pre-exec syscall exit).
                    proc.exec_armed = false;
                    if pid != root_pid && !proc.shard_decided {
                        proc.shard_decided = true;
                        if wid == 0 {
                            if proc.parent != root_pid {
                                sup!(
                                    "handoff check pid={pid}: parent {} is not the guest root; stays on W0",
                                    proc.parent
                                );
                            } else if proc.exec_blocked {
                                sup!("handoff check pid={pid}: exec blocked; stays on W0");
                            } else if let Some(path) = &proc.exec_path {
                                match shard_map.get(path.as_str()).copied() {
                                    Some(twid) => {
                                        sup!("handoff check pid={pid}: {path} -> W{twid}");
                                        ho = Some((twid, true));
                                    }
                                    None => {
                                        sup!("handoff check pid={pid}: {path} has no shard; stays on W0");
                                    }
                                }
                            } else {
                                sup!("handoff check pid={pid}: no decided image path; stays on W0");
                            }
                        } else if proc.exec_blocked {
                            sup!("handoff check pid={pid}: exec blocked; stays on W{wid}");
                        } else if proc.parent != shard_root {
                            sup!(
                                "handoff check pid={pid}: parent {} is not the shard root; stays on W{wid}",
                                proc.parent
                            );
                        } else if let Some(path) = &proc.exec_path {
                            // The root's own image is the
                            // first (only) path of this
                            // worker's shard entry: a root
                            // child exec'ing that same
                            // image stays; any other image
                            // is kin and moves.
                            let root_image = SHARDS
                                .iter()
                                .find(|(w, _, _)| *w == wid)
                                .and_then(|(_, _, paths)| paths.first().copied());
                            if Some(path.as_str()) == root_image {
                                sup!("handoff check pid={pid}: {path} is the shard root's own image; stays on W{wid}");
                            } else if let Some(twid) = kin_target {
                                sup!("handoff check pid={pid}: {path} -> W{twid}");
                                ho = Some((twid, false));
                            }
                        } else {
                            sup!("handoff check pid={pid}: no decided image path; stays on W{wid}");
                        }
                    }
                }
                match ho {
                    Some((twid, root)) => {
                        pending_handoff = Some((pid, twid, root))
                    }
                    None => cont_syscall(pid, 0),
                }
            }
            if let Some((hpid, twid, root)) = pending_handoff.take() {
                do_handoff(hpid, twid, root, wid, &mut procs, &mut vcreds, &mut coord);
            }
            // Wedge forensics (0.9.123): the kill-syscall
            // hook is the snapshot's primary trigger.
            // 0.9.122 hooked the signal-delivery stop, and
            // its field run fired zero times: a wedged
            // family thread sits in a ptrace stop the
            // supervisor never restarts, so the queued
            // SIGQUIT raises no delivery stop before the
            // watchdog's SIGKILL terminates the stopped
            // tracee and discards it. Firing here -- at
            // the sender's entry stop, the first moment
            // the SIGQUIT exists -- reaches the wedge by
            // construction. The one-shot flag and
            // wedge_snapshot itself are 0.9.122's,
            // unchanged; the delivery-stop hook below
            // stays as a backstop under the same flag for
            // any SIGQUIT that does get delivered (a
            // running, unparked family thread).
            if let Some(tp) = wedge_kill_target.take() {
                if !wedge_snapped {
                    if let Some(leader) = dump_candidate {
                        let mut solo: Option<i32> = None;
                        if wedge_snapshot(tp, &procs, leader, &mut solo) {
                            wedge_snapped = true;
                            fire_wedge_chain(
                                &mut coord,
                                leader,
                                solo,
                                &mut wedge_leader,
                                &mut wedge_holder,
                            );
                        }
                    }
                }
            }
        } else if sig == SIGTRAP && event == PTRACE_EVENT_EXEC {
            // The exec event stop sits between the execve entry and
            // exit stops; surface the entry's description here and
            // clear it so the exit stop stays silent (M0 pairing).
            // Freeze forensics (0.9.81): whatever execs
            // is not system_server -- it never execs --
            // so a candidate reaching its exec gives up
            // the slot. This is what keeps zygote's app
            // children (fork, then exec at once) out of
            // the slot the fork site provisionally
            // filled.
            if dump_candidate == Some(pid) {
                dump_candidate = None;
            }
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
                        cp.parent = pid;
                        if !cp.syscall_seen {
                            cp.vcwd = parent_vcwd;
                            cp.compat = parent_compat;
                        }
                    }
                    None => {
                        let mut nps = ProcState::new(&parent_vcwd, false, parent_compat);
                        nps.parent = pid;
                        procs.insert(child, nps);
                    }
                }
                let parent_creds = vcreds.get(&pid).copied().unwrap_or((0, 0));
                vcreds.insert(child, parent_creds);
                // Route + credential bookkeeping for the
                // child lives with the coordinator from
                // birth (S2), whoever traces it.
                coord.register_pid(child, parent_creds);
                let ev_name = match event {
                    x if x == PTRACE_EVENT_FORK => "fork",
                    x if x == PTRACE_EVENT_VFORK => "vfork",
                    _ => "clone",
                };
                sup!("tracee born: parent={pid} child={child} ({ev_name})");
                // Freeze forensics (0.9.81): a fork or
                // vfork child of this worker's shard root
                // becomes the system_server candidate if
                // the slot is free; the earliest living
                // one keeps it. Only FORK/VFORK births
                // count: threads arrive as CLONE events
                // (zygote spawns its own threads long
                // before it forks system_server, and a
                // thread's tid is not a dump target), and
                // app children surrender the slot again at
                // their exec. On W0 shard_root stays 0 and
                // no guest parent ever equals it, so the
                // slot never fills there.
                if (event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK)
                    && pid == shard_root
                    && dump_candidate.is_none()
                {
                    dump_candidate = Some(child);
                    // A new tenure earns a fresh wedge
                    // snapshot (0.9.122).
                    wedge_snapped = false;
                    // 0.9.140 (M5): and no chain-dump
                    // bookkeeping from any earlier one.
                    wedge_leader = None;
                    wedge_holder = None;
                }
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
            // Wedge forensics (0.9.122, telemetry only;
            // backstop since 0.9.123): the primary trigger
            // is the kill-syscall hook in the entry stop
            // above -- a wedged (parked) family thread
            // never reaches this delivery stop. If a
            // SIGQUIT (3) does get delivered to a family
            // thread, it spends the same shared one-shot
            // here. Pure logging on the side: `deliver`
            // and everything below proceed exactly as
            // before.
            if sig == 3 && !wedge_snapped {
                if let Some(leader) = dump_candidate {
                    let mut solo: Option<i32> = None;
                    if wedge_snapshot(pid, &procs, leader, &mut solo) {
                        wedge_snapped = true;
                        fire_wedge_chain(
                            &mut coord,
                            leader,
                            solo,
                            &mut wedge_leader,
                            &mut wedge_holder,
                        );
                    }
                }
            }
            if sig >= 32 {
                // 0.9.63 telemetry: realtime-range
                // signals are rare in the guests and
                // are never part of the funnel's own
                // machinery. 0.9.62's field run lost
                // every SurfaceFlinger incarnation on
                // W2 to sig=35 with no sender visible;
                // record every arrival in that range
                // and the reinjection decision.
                sup!("signal stop pid={pid} sig={sig} (realtime range) -> reinject");
            }
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
                // 0.9.131 ignition forensics, trigger B:
                // a SIGSEGV whose pc lands in the
                // dvmAbort range (see DVMABORT_PC_LO/HI
                // at binder_ignition_dump: Dalvik's
                // internal-check suicide, not a wild
                // pointer) gets the dying pid's binder
                // evidence ring printed beside this
                // FATAL line -- the deliveries, shield
                // intercepts and claims that preceded
                // the abort, readable directly instead
                // of reconstructed from the whole log.
                if sig == 11 && (DVMABORT_PC_LO..DVMABORT_PC_HI).contains(&pc) {
                    let logs = coord.ignition_dump(pid, "dvmabort");
                    replay_logs(logs);
                }
                // 0.9.133 ignition forensics, trigger C:
                // a SIGILL death gets the same evidence
                // ring treatment. The .132 run's T8 was
                // a new species: an SS thread mprotect'd
                // an image-data page EXEC and jumped
                // into it, and the fatal signal killed
                // system_server outright in ~9.8K lines
                // -- the fastest tenure death on record,
                // with no wedge and no crash report to
                // anchor on, and its cause (Dalvik JIT
                // cache incompatibility vs a (c)-family
                // corrupted function pointer) undecidable
                // from what was captured. n=1: capture
                // first, fix later (s9-132-verify Q4).
                // This site only ever runs for guest
                // tracees, so sig == 4 here is a guest
                // process's SIGILL by construction.
                if sig == 4 {
                    let logs = coord.ignition_dump(pid, "sigill");
                    replay_logs(logs);
                }
                // 0.9.102: dump the tracee's binder input
                // buffer (its most recent read fill) verbatim.
                // Compared offline against the batches the
                // supervisor assembled for this pid, this is
                // the ground truth of what the guest was
                // consuming when it died -- the splice /
                // stale-buffer check the stream-side telemetry
                // could never settle.
                if let Some((rb, flen)) =
                    procs.get(&pid).and_then(|p| p.last_binder_read)
                {
                    let n = ((flen as usize) + 128).min(512);
                    if let Some(mem) = read_mem_vec(pid, rb as u64, n) {
                        let words: Vec<String> = mem
                            .chunks_exact(4)
                            .take(64)
                            .map(|c| {
                                format!(
                                    "0x{:08x}",
                                    u32::from_le_bytes(c.try_into().unwrap())
                                )
                            })
                            .collect();
                        sup!(
                            "FATAL minbuf pid={pid} rb=0x{rb:x} filled={flen} w=[{}]",
                            words.join(", ")
                        );
                    }
                }
                // Memory around the crash (0.9.24): on this
                // device GETSIGINFO fails, so the fault
                // address is usually unknown. The bytes at
                // pc name the faulting instruction; the
                // bytes at the data registers show what the
                // code was about to touch (e.g. the
                // pixelflinger JIT's emission pointer).
                // 0.9.134: the dump extends to SIGILL --
                // at a SIGILL the pc bytes are the whole
                // question (garbage jumped to, vs code the
                // JIT emitted), and the register windows
                // come free.
                if sig == 11 || sig == 4 {
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
                        // Follow the first stack words one
                        // level: a heap object's first word
                        // is its vtable, and the vtable's
                        // home library names the class. This
                        // turns "some RefBase with a bad
                        // mRefs" into a named object.
                        if let Some(swords) =
                            read_mem_vec(pid, r.sp(), 8)
                        {
                            for i in 0..2 {
                                let w = u32::from_le_bytes(
                                    swords[i * 4..i * 4 + 4]
                                        .try_into()
                                        .unwrap(),
                                ) as u64;
                                if w <= 0x10000 {
                                    continue;
                                }
                                if let Some(vb) =
                                    read_mem_vec(pid, w, 4)
                                {
                                    let v = u32::from_le_bytes(
                                        vb.try_into().unwrap(),
                                    ) as u64;
                                    sup!(
                                        "FATAL ptr stk[{i}]=0x{w:x} -> 0x{v:x}"
                                    );
                                }
                            }
                        }
                    }
                }
                // 0.9.134: SIGILL page forensics
                // (s9-133-verify Q5). Two SIGILL deaths so
                // far, both system_server threads in
                // app-start traffic, both killing the
                // tenure outright -- and both undecidable
                // between (a) a Dalvik JIT compatibility
                // gap (the thread legitimately executed
                // into its own compiled-code page, whose
                // encoding the supervisor's CPU model
                // mishandles) and (b) a (c)-family
                // corrupted pointer (the thread was thrown
                // into a data page). The deciding evidence
                // is the page itself: compiled code reads
                // as code with a literal pool, image/data
                // bytes read as data. Dump the whole pc
                // page (256B reads, stopping at the first
                // unreadable chunk) plus the raw maps entry
                // for it -- permissions and backing name
                // included -- so the next occurrence is
                // decidable from the log alone. Print only;
                // nothing here feeds any decision.
                if sig == 4 {
                    let page = pc & !0xfffu64;
                    let mut mapline = "none".to_string();
                    if let Ok(maps) =
                        std::fs::read_to_string(format!("/proc/{pid}/maps"))
                    {
                        for line in maps.lines() {
                            let mut it = line.split_whitespace();
                            let Some(range) = it.next() else { continue };
                            let Some((lo, hi)) = range.split_once('-') else {
                                continue;
                            };
                            let lo = u64::from_str_radix(lo, 16).unwrap_or(0);
                            let hi = u64::from_str_radix(hi, 16).unwrap_or(0);
                            if pc >= lo && pc < hi {
                                mapline = line.trim().to_string();
                                break;
                            }
                        }
                    }
                    sup!(
                        "FATAL sigill-page pid={pid} pc=0x{pc:x} page=0x{page:x} map=[{mapline}]"
                    );
                    let mut off = 0usize;
                    while off < 4096 {
                        match read_mem_vec(pid, page + off as u64, 256) {
                            Some(b) => {
                                for (i, chunk) in b.chunks(32).enumerate() {
                                    let hex: String = chunk
                                        .iter()
                                        .map(|x| format!("{x:02x}"))
                                        .collect::<Vec<_>>()
                                        .concat();
                                    sup!(
                                        "FATAL sigill-page pid={pid} +0x{:03x}: {}",
                                        off + i * 32,
                                        hex
                                    );
                                }
                            }
                            None => {
                                sup!(
                                    "FATAL sigill-page pid={pid} +0x{off:03x}: <unreadable; page dump truncated>"
                                );
                                break;
                            }
                        }
                        off += 256;
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
                        // Resolve the first stack words the
                        // same way: a crash inside a shared
                        // helper (an atomic, a lock) is only
                        // attributable with its caller, and
                        // the caller sits on the stack. Words
                        // landing in a pathname mapping print
                        // as "FATAL stk[i] in lib (+off)".
                        if let Some(r) = &fregs {
                            let sp = r.sp();
                            if let Some(words) =
                                read_mem_vec(pid, sp, 32)
                            {
                                let mut ranges: Vec<(
                                    u64,
                                    u64,
                                    String,
                                )> = Vec::new();
                                for line in maps.lines() {
                                    if !line.contains('/') {
                                        continue;
                                    }
                                    let mut it =
                                        line.split_whitespace();
                                    let Some(range) = it.next()
                                    else {
                                        continue;
                                    };
                                    let Some((lo, hi)) =
                                        range.split_once('-')
                                    else {
                                        continue;
                                    };
                                    let lo = u64::from_str_radix(
                                        lo, 16,
                                    )
                                    .unwrap_or(0);
                                    let hi = u64::from_str_radix(
                                        hi, 16,
                                    )
                                    .unwrap_or(0);
                                    let name = line
                                        .rsplit('/')
                                        .next()
                                        .unwrap_or("?")
                                        .trim()
                                        .to_string();
                                    ranges.push((lo, hi, name));
                                }
                                // Also name the raw map line
                                // for each stack word, pathname
                                // or not: which mapping a wild
                                // pointer lives in (arena file,
                                // ashmem substitute, anonymous)
                                // is often the whole diagnosis.
                                let mut seen_lines: std::collections::HashSet<String> =
                                    std::collections::HashSet::new();
                                for i in 0..8 {
                                    let w = u32::from_le_bytes(
                                        words[i * 4..i * 4 + 4]
                                            .try_into()
                                            .unwrap(),
                                    ) as u64;
                                    if w < 0x10000 {
                                        continue;
                                    }
                                    for line in maps.lines() {
                                        let mut it =
                                            line.split_whitespace();
                                        let Some(range) = it.next()
                                        else {
                                            continue;
                                        };
                                        let Some((lo, hi)) =
                                            range.split_once('-')
                                        else {
                                            continue;
                                        };
                                        let lo = u64::from_str_radix(
                                            lo, 16,
                                        )
                                        .unwrap_or(0);
                                        let hi = u64::from_str_radix(
                                            hi, 16,
                                        )
                                        .unwrap_or(0);
                                        if w >= lo && w < hi {
                                            if seen_lines
                                                .insert(line.to_string())
                                            {
                                                sup!(
                                                    "FATAL mapline 0x{w:x}: {line}"
                                                );
                                            }
                                            break;
                                        }
                                    }
                                }
                                for i in 0..8 {
                                    let w = u32::from_le_bytes(
                                        words[i * 4..i * 4 + 4]
                                            .try_into()
                                            .unwrap(),
                                    ) as u64;
                                    if w < 0x10000 {
                                        continue;
                                    }
                                    for (lo, hi, name) in &ranges {
                                        if w >= *lo && w < *hi
                                            && !name.is_empty()
                                            && *name != "?"
                                        {
                                            sup!(
                                                "FATAL stk[{i}] 0x{w:x} in {name} (+0x{:x})",
                                                w - lo
                                            );
                                            break;
                                        }
                                    }
                                }
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
                if deliver != 0 {
                    // 0.9.108: the seccomp trap stop raced
                    // ahead of the syscall-entry stop. The
                    // entry stop normally runs first and
                    // arms the pending record (the "late
                    // SIGSYS" rescue above); occasionally
                    // the trap is reported first, when no
                    // record exists yet -- and delivering
                    // the signal then kills the whole guest
                    // process (the 0.9.107 long field: 81
                    // system_server tenures in 11 minutes,
                    // dying process-wide by SIGSYS; the
                    // proven culprit stop had nr_reg intact
                    // at 0x10d = utimes). A fresh trap is
                    // recognisable exactly: the syscall
                    // number register still holds a real
                    // number (a late trap reads -1 after
                    // cancellation). Swallow the signal and
                    // continue: the pending entry stop for
                    // the same call lands next and handles
                    // it through the normal path.
                    if let Some(proc) = procs.get_mut(&pid) {
                        let nr = get_regs(pid, proc.compat).map(|r| r.nr());
                        if let Some(nr) = nr {
                            if nr >= 0 && nr < 0x10_0000 && proc.sigsys_preentry < 8 {
                                proc.sigsys_preentry += 1;
                                sup!(
                                    "SIGSYS pre-entry pid={pid}: syscall={nr} name={} swallowed (#{}) awaiting entry stop",
                                    nr_name(proc.compat, nr as u64),
                                    proc.sigsys_preentry
                                );
                                deliver = 0;
                            }
                        }
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
}

fn main() {
    // Coordinator / worker modes (multi-process split,
    // spec S1b + S2): this same binary also runs the
    // binder-driver coordinator (`--coordinator-sock
    // <path>`) and the shard tracers (`--worker ...`).
    // spawn_coordinator / spawn_workers reach the same
    // entries by fork; the argv forms keep both modes
    // runnable by hand. These branches run before any
    // logging: the coordinator's stdout belongs to the
    // protocol and is silenced by its spawner besides.
    {
        let argv: Vec<String> = std::env::args().collect();
        if argv.len() >= 3 && argv[1] == "--coordinator-sock" {
            coordinator_main(&argv[2]);
        }
        if argv.len() >= 9 && argv[1] == "--worker" {
            // --worker <wid> <shard> <rootfs> <coord_sock>
            //   <bb_path> <loader_path> <compat 0|1>
            set_direct_log_dir(&argv[4], false);
            let wid: u8 = argv[2].parse().unwrap_or(0);
            worker_main(
                wid,
                &argv[3],
                &argv[4],
                &argv[5],
                &argv[6],
                &argv[7],
                argv[8] == "1",
            );
        }
    }
    sup!("supervisor ctx: [{}]", selinux_ctx(0));
    // Yield the phone to its own interface: the funnel
    // makes the supervisor burn a full core for the
    // whole guest-boot stretch, and 0.9.54's field run
    // showed the host UI (even our own stop button)
    // starving despite batched logging. Nice ourselves
    // to background priority; every guest inherits it
    // across fork/exec, so the whole guest complex
    // schedules behind the phone's foreground work.
    // Boot takes a little longer; the phone stays
    // usable while it happens.
    let nrc = unsafe { libc::setpriority(libc::PRIO_PROCESS, 0, 10) };
    sup!("supervisor niced to +10 (rc={nrc}); guest tree inherits");
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

    // The binder driver lives in a coordinator child
    // from here on (multi-process split, spec S1b): all
    // BinderState is on its side of the socket, and this
    // process only asks it for decisions. Spawned before
    // the first tracee exists, so the child inherits no
    // stops, no reader thread and no guest fds. Since
    // S2 the coordinator listens on a unix socket under
    // the rootfs and the shard workers connect to it
    // too; they are forked here, before the guest pipe
    // and the guest root exist, for the same inheritance
    // reasons.
    set_direct_log_dir(&rootfs, true);
    write_supervisor_pid(&rootfs);
    let coord_sock = format!("{rootfs}/.coord.sock");
    spawn_coordinator(&coord_sock);
    let mut coord = CoordClient::connect(&coord_sock, 0, "w0");
    let shard_map = spawn_workers(
        &coord_sock,
        &rootfs,
        &bb_path,
        &loader_path,
        guest_compat,
        coord.poll_fd(),
    );

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
    // creds while another ProcState is borrowed. Since S2 each
    // tracer keeps only its own shard's slice of the book; the
    // coordinator holds the global copy for cross-shard peers.
    let mut vcreds: HashMap<i32, (u32, u32)> = HashMap::new();
    vcreds.insert(root_pid, (0, 0));
    // The root has no fork event to register it; file
    // its coordinator route now so cross-shard wakes
    // and credential queries can reach it too.
    coord.register_pid(root_pid, (0, 0));
    // The virtual binder driver (S5) lives in the
    // coordinator (see spawn_coordinator above); wakes
    // collects parked tracees to complete after each
    // entry stop.
    let ctx = TracerCtx {
        wid: 0,
        rootfs,
        bb_path,
        loader_path,
        guest_compat,
        root_pid,
        coord,
        procs,
        vcreds,
        wakes: Vec::new(),
        root_launched: false,
        seen: HashSet::new(),
        counts: HashMap::new(),
        shard_map,
        kin_target: None,
        shard_root: 0,
        dump_candidate: None,
    };
    // Freeze forensics (0.9.81): take the shell's
    // SIGUSR2 stack-dump requests from here on. Every
    // fork this process will ever make (coordinator,
    // workers, the guest root) has already happened,
    // so none of them inherits the handler; the guest
    // tree in particular must never see our request
    // line as its own disposition.
    install_dump_signal();
    tracer_loop(ctx);

    let _ = reader.join();
    sup!("supervisor done");
}
