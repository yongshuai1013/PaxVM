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
const ENOTDIR: i64 = 20;

// ---- aarch64 syscall numbers (asm-generic table) ----
const NR_GETCWD: u64 = 17;
const NR_CHDIR: u64 = 49;
const NR_FCHDIR: u64 = 50;
const NR_EXECVE: u64 = 221;
const NR_EXECVEAT: u64 = 281;

/// Syscalls whose only path argument is (dirfd=a0, path=a1): T class.
fn is_t_dirfd_path(nr: u64) -> bool {
    matches!(
        nr,
        33 | 34 | 35 | 48 | 53 | 54 | 56 | 78 | 79 | 88 | 291 | 439
    )
}

/// Syscalls with two path arguments (paths a1 and a3, dirfds a0/a2).
fn is_t_two_paths(nr: u64) -> bool {
    matches!(nr, 37 | 38) // linkat, renameat
}

/// symlinkat: a0 is the symlink *content* (not translated); the
/// linkpath is a2 with dirfd a1.
fn is_t_symlinkat(nr: u64) -> bool {
    nr == 36
}

/// Syscalls whose path is a0 with cwd semantics (no dirfd).
fn is_t_path0(nr: u64) -> bool {
    matches!(nr, 43 | 45) // statfs, truncate
}

/// F class answered purely from supervisor state (getcwd, fchdir).
/// chdir is also F class (the real syscall never runs) but needs
/// vcwd mutation, so it is dispatched separately in the entry path.
fn is_faked(nr: u64) -> bool {
    matches!(nr, NR_GETCWD | NR_FCHDIR)
}

/// X class: blocked with -ENOSYS. clone/clone3 left this class in
/// M1 (children are followed via TRACEFORK/TRACECLONE), and
/// execve/execveat are routed to the exec handler instead.
fn is_blocked(nr: u64) -> bool {
    matches!(
        nr,
        39 | 40 | 41 | 51 | 97 | 117 | 264 | 265 | 268 | 277 | 280 | 437
    )
}

fn nr_name(nr: u64) -> &'static str {
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

fn get_regs(pid: i32) -> Option<UserPtRegs> {
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
    Some(r)
}

fn set_regs(pid: i32, r: &UserPtRegs) -> bool {
    let mut iov = libc::iovec {
        iov_base: r as *const UserPtRegs as *mut libc::c_void,
        iov_len: std::mem::size_of::<UserPtRegs>(),
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
/// arch and the userspace call address. aarch64 siginfo_t layout:
/// si_signo@0 (i32), si_errno@4, si_code@8, union@16 —
/// _call_addr@16 (u64), _syscall@24 (i32), _arch@28 (u32).
fn dump_sigsys_info(pid: i32) {
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
        let call_addr = u64::from_ne_bytes(buf[16..24].try_into().unwrap());
        let sc = i32::from_ne_bytes(buf[24..28].try_into().unwrap());
        let arch = u32::from_ne_bytes(buf[28..32].try_into().unwrap());
        let name = if sc >= 0 { nr_name(sc as u64) } else { "unknown-id" };
        sup!(
            "SIGSYS detail pid={pid}: si_code={si_code} syscall={sc} name={name} arch=0x{arch:x} call_addr=0x{call_addr:x}"
        );
    }
    if let Some(r) = get_regs(pid) {
        sup!(
            "SIGSYS regs pid={pid}: pc=0x{:x} x8=0x{:x} x0=0x{:x} x1=0x{:x} x2=0x{:x}",
            r.pc, r.regs[8], r.regs[0], r.regs[1], r.regs[2]
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
}

impl ProcState {
    fn new(vcwd: &str, is_root: bool) -> Self {
        ProcState {
            expect_exit: false,
            pending: None,
            vcwd: vcwd.to_string(),
            options_set: false,
            started: false,
            syscall_seen: false,
            is_root,
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
/// regs[8] is still set to -1 as well: harmless, and it keeps any
/// reader of x8 (including our own SIGSYS regs dump) honest.
fn skip_syscall(pid: i32, regs: &mut UserPtRegs, pend: &mut Pending, value: i64) {
    regs.regs[8] = u64::MAX;
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
fn entry_translate(pid: i32, rootfs: &str, vcwd: &str, nr: u64, regs: &mut UserPtRegs) -> String {
    // (arg index of path, arg index of its dirfd or -1 for cwd semantics)
    let pairs: Vec<(usize, i64)> = if is_t_dirfd_path(nr) {
        vec![(1, regs.regs[0] as i64)]
    } else if is_t_two_paths(nr) {
        vec![(1, regs.regs[0] as i64), (3, regs.regs[2] as i64)]
    } else if is_t_symlinkat(nr) {
        vec![(2, regs.regs[1] as i64)]
    } else {
        vec![(0, AT_FDCWD)]
    };
    let mut cursor = regs.sp.saturating_sub(256);
    let mut parts: Vec<String> = Vec::new();
    for (argi, dirfd) in pairs {
        let addr = regs.regs[argi];
        match read_path(pid, addr) {
            Some(old) => match translate(rootfs, vcwd, dirfd, &old) {
                Some(new) => match scratch_write(pid, &mut cursor, &new) {
                    Some(scratch) => {
                        regs.regs[argi] = scratch;
                        parts.push(format!("'{old}' -> '{new}'"));
                    }
                    None => parts.push(format!("'{old}' (scratch write failed, untranslated)")),
                },
                None => parts.push(format!("'{old}' (untranslated)")),
            },
            None => parts.push(format!("path@{addr:#x} (unreadable)")),
        }
    }
    let mut desc = format!("{}({}) {}", nr_name(nr), nr, parts.join(", "));
    if nr == 78 {
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
fn is_setid_emulated(nr: u64) -> bool {
    matches!(nr, 143 | 144 | 145 | 146 | 147 | 149 | 151 | 152 | 159)
}

/// F class (getcwd, fchdir): cancel the syscall and fabricate the
/// answer from the virtual cwd (M1 spec section 3).
fn entry_fake(pid: i32, vcwd: &str, nr: u64, regs: &mut UserPtRegs, pend: &mut Pending) -> String {
    match nr {
        NR_GETCWD => {
            let buf = regs.regs[0];
            let size = regs.regs[1];
            let need = (vcwd.len() + 1) as u64;
            let mut bytes = vcwd.as_bytes().to_vec();
            bytes.push(0);
            if size >= need && write_mem(pid, buf, &bytes).is_ok() {
                skip_syscall(pid, regs, pend, need as i64);
                format!("getcwd(17) FAKED -> \"{vcwd}\"")
            } else {
                skip_syscall(pid, regs, pend, -ERANGE);
                "getcwd(17) FAKED -> -ERANGE (buffer too small)".to_string()
            }
        }
        _ => {
            // fchdir: succeed without touching the vcwd. The guest
            // shell's cd uses chdir, not fchdir (M1 spec section 3).
            skip_syscall(pid, regs, pend, 0);
            format!("fchdir(50) FAKED -> 0 (vcwd stays {vcwd})")
        }
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
    regs: &mut UserPtRegs,
    pend: &mut Pending,
) -> (String, Option<String>) {
    let addr = regs.regs[0];
    let Some(p) = read_path(pid, addr) else {
        skip_syscall(pid, regs, pend, -ENOENT);
        return ("chdir(49) path unreadable -> -ENOENT".to_string(), None);
    };
    let target = guest_abs(vcwd, &p);
    let host = format!("{rootfs}{target}");
    match std::fs::metadata(&host) {
        Ok(md) if md.is_dir() => {
            skip_syscall(pid, regs, pend, 0);
            (
                format!("chdir(49) '{p}' vcwd {vcwd} -> {target}"),
                Some(target),
            )
        }
        Ok(_) => {
            skip_syscall(pid, regs, pend, -ENOTDIR);
            (format!("chdir(49) '{p}' -> -ENOTDIR (target {target})"), None)
        }
        Err(_) => {
            skip_syscall(pid, regs, pend, -ENOENT);
            (format!("chdir(49) '{p}' -> -ENOENT (target {target})"), None)
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
    nr: u64,
    regs: &mut UserPtRegs,
    pend: &mut Pending,
) -> (String, bool) {
    let name = nr_name(nr);
    let (path_arg, dirfd) = if nr == NR_EXECVE {
        (0usize, AT_FDCWD)
    } else {
        (1usize, regs.regs[0] as i64)
    };
    let addr = regs.regs[path_arg];
    let Some(gpath) = read_path(pid, addr) else {
        return (format!("{name}({nr}) path@{addr:#x} (unreadable, passed)"), false);
    };
    let rewrite_to_bb = |regs: &mut UserPtRegs| -> bool {
        let mut cursor = regs.sp.saturating_sub(256);
        match scratch_write(pid, &mut cursor, bb_native) {
            Some(scratch) => {
                regs.regs[path_arg] = scratch;
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
    let mut cursor = regs.sp.saturating_sub(256);
    match scratch_write(pid, &mut cursor, &host) {
        Some(scratch) => {
            regs.regs[path_arg] = scratch;
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
    procs.insert(root_pid, ProcState::new("/", true));
    let mut root_launched = false;
    let mut seen: HashSet<u64> = HashSet::new();
    let mut counts: HashMap<u64, u64> = HashMap::new();

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
            procs.insert(pid, ProcState::new("/", false));
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
                let Some(mut regs) = get_regs(pid) else {
                    cont_syscall(pid, 0);
                    continue;
                };
                let nr = regs.regs[8];
                let mut pend = Pending { nr, desc: None, inject: None };
                let mut dirty = false;
                if (nr == NR_EXECVE || nr == NR_EXECVEAT) && pid == root_pid && !root_launched {
                    // The guest root's own launch exec must pass;
                    // every later exec goes through the exec rules.
                    *counts.entry(nr).or_insert(0) += 1;
                    if seen.insert(nr) {
                        sys!("{}({}) pass (guest launch exec, allowed)", nr_name(nr), nr);
                    }
                } else if nr == NR_EXECVE || nr == NR_EXECVEAT {
                    let (desc, d) = entry_exec(
                        pid,
                        &rootfs,
                        &guest_path,
                        &proc.vcwd,
                        nr,
                        &mut regs,
                        &mut pend,
                    );
                    pend.desc = Some(desc);
                    dirty = d;
                } else if nr == NR_CHDIR {
                    let (desc, new_vcwd) =
                        entry_chdir(pid, &rootfs, &proc.vcwd, &mut regs, &mut pend);
                    pend.desc = Some(desc);
                    dirty = true;
                    if let Some(v) = new_vcwd {
                        proc.vcwd = v;
                    }
                } else if is_t_dirfd_path(nr)
                    || is_t_two_paths(nr)
                    || is_t_symlinkat(nr)
                    || is_t_path0(nr)
                {
                    pend.desc = Some(entry_translate(pid, &rootfs, &proc.vcwd, nr, &mut regs));
                    dirty = true;
                } else if is_setid_emulated(nr) {
                    // Cancel before the kernel (and its seccomp
                    // filter) ever evaluates it; answer 0 at the
                    // exit stop via the standard inject path.
                    skip_syscall(pid, &mut regs, &mut pend, 0);
                    pend.desc = Some(format!("{}({}) emulated (return 0)", nr_name(nr), nr));
                    dirty = true;
                } else if is_faked(nr) {
                    pend.desc = Some(entry_fake(pid, &proc.vcwd, nr, &mut regs, &mut pend));
                    dirty = true;
                } else if is_blocked(nr) {
                    skip_syscall(pid, &mut regs, &mut pend, -ENOSYS);
                    pend.desc = Some(format!("{}({}) BLOCKED -> -ENOSYS", nr_name(nr), nr));
                    dirty = true;
                } else {
                    // P class and unlisted: pass, log first occurrence.
                    *counts.entry(nr).or_insert(0) += 1;
                    if seen.insert(nr) {
                        sys!("{}({}) pass (first occurrence)", nr_name(nr), nr);
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
                if let Some(pend) = proc.pending.take() {
                    if let Some(mut regs) = get_regs(pid) {
                        let mut ret = regs.regs[0] as i64;
                        if let Some(v) = pend.inject {
                            regs.regs[0] = v as u64;
                            set_regs(pid, &regs);
                            ret = v;
                        }
                        if let Some(d) = &pend.desc {
                            sys!("{d} => {ret}");
                        }
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
                let parent_vcwd = procs
                    .get(&pid)
                    .map(|p| p.vcwd.clone())
                    .unwrap_or_else(|| "/".to_string());
                match procs.get_mut(&child) {
                    Some(cp) => {
                        // Registered early by its own initial stop.
                        // No syscall of the child has been processed
                        // yet, so no translation has consumed its
                        // vcwd and adopting the parent's current
                        // vcwd is still exact.
                        if !cp.syscall_seen {
                            cp.vcwd = parent_vcwd;
                        }
                    }
                    None => {
                        procs.insert(child, ProcState::new(&parent_vcwd, false));
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
            // Signal-delivery stop: reinject the signal unchanged.
            // A trapped guest dies by this SIGSYS reinjection; dump
            // the kernel's siginfo first so the log names the syscall
            // the seccomp filter objected to.
            if sig == SIGSYS {
                dump_sigsys_info(pid);
            }
            cont_syscall(pid, sig);
        }
    }

    if !counts.is_empty() {
        let mut items: Vec<(u64, u64)> = counts.into_iter().collect();
        items.sort_by_key(|(nr, _)| *nr);
        let parts: Vec<String> = items
            .iter()
            .map(|(nr, n)| format!("{}({})x{}", nr_name(*nr), nr, n))
            .collect();
        sys!("pass-through summary: {}", parts.join(", "));
    }
    let _ = reader.join();
    sup!("supervisor done");
}
