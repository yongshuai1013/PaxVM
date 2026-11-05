//! PaxVM M0 supervisor: a standalone native process that forks a
//! static guest binary, attaches to it with ptrace, and proxies a
//! minimal syscall set so the guest's file accesses land inside the
//! app sandbox rootfs (M0 spec, sections 2.1-2.7).
//!
//! Design points fixed by the spec:
//! - ptrace is used raw through libc, only in the classic
//!   PTRACE_SYSCALL double-stop model with GETREGSET/SETREGSET
//!   (NT_PRSTATUS). No seccomp, no PTRACE_GET_SYSCALL_INFO.
//! - Path-carrying syscalls are translated onto the rootfs by
//!   rewriting the path argument to a stack scratch area.
//! - Unlisted syscalls are passed through and logged on first
//!   occurrence (log-first principle, spec 2.6).
//! - stdout is a line protocol for the shell: [sup] supervisor
//!   events, [sys] syscall events, [guest] forwarded guest output.

use std::collections::{HashMap, HashSet};
use std::ffi::CString;
use std::io::Write;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Mutex;

// ---- ptrace constants (raw, per spec 2.1; bionic ptrace takes c_int) ----
const PTRACE_TRACEME: i32 = 0;
const PTRACE_PEEKDATA: i32 = 2;
const PTRACE_POKEDATA: i32 = 5;
const PTRACE_SYSCALL: i32 = 24;
const PTRACE_SETOPTIONS: i32 = 0x4200;
const PTRACE_GETREGSET: i32 = 0x4204;
const PTRACE_SETREGSET: i32 = 0x4205;
const PTRACE_O_TRACESYSGOOD: usize = 0x1;
const PTRACE_O_TRACEEXEC: usize = 0x10;
const PTRACE_O_EXITKILL: usize = 0x100000;
const PTRACE_EVENT_EXEC: i32 = 4;
const NT_PRSTATUS: usize = 1;

const SIGTRAP: i32 = 5;
const SYSCALL_STOP_SIG: i32 = SIGTRAP | 0x80;

const AT_FDCWD: i64 = -100;

const ENOSYS: i64 = 38;
const ERANGE: i64 = 34;

// ---- aarch64 syscall numbers (asm-generic table, spec 2.5/2.6) ----
const NR_GETCWD: u64 = 17;
const NR_CHDIR: u64 = 49;
const NR_FCHDIR: u64 = 50;

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

/// F class: answered by the supervisor itself.
fn is_faked(nr: u64) -> bool {
    matches!(nr, NR_GETCWD | NR_CHDIR | NR_FCHDIR)
}

/// X class: blocked with -ENOSYS (spec 2.6). execve/execveat are
/// handled specially in the entry path: the guest's own launch exec
/// must pass, later ones are blocked.
fn is_blocked(nr: u64) -> bool {
    matches!(
        nr,
        39 | 40 | 41 | 51 | 97 | 117 | 220 | 264 | 265 | 268 | 277 | 280 | 281 | 435 | 437
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
        78 => "readlinkat",
        79 => "newfstatat",
        80 => "fstat",
        82 => "fsync",
        83 => "fdatasync",
        88 => "utimensat",
        93 => "exit",
        94 => "exit_group",
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

// ---- line output (the shell's only view of us; spec 2.7) ----
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
        sup!("GETREGSET failed: errno={} ({})", errno(), std::io::Error::from_raw_os_error(errno()));
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

// ---- guest memory access (process_vm_*, PEEK/POKE fallback; spec 2.4) ----
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

// ---- path translation (spec 2.5) ----

/// Lexically normalize a guest path into components under the guest
/// root: collapses duplicate '/', drops '.', and clamps '..' at the
/// root. No symlink resolution (the M0 rootfs contains none).
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

/// Decide the host path for (dirfd, path); None = do not translate.
fn translate(rootfs: &str, dirfd: i64, path: &str) -> Option<String> {
    if path.is_empty() {
        return None;
    }
    if !path.starts_with('/') && dirfd != AT_FDCWD {
        // Relative to a real fd: that fd was opened via a translated
        // path, so kernel resolution is already inside the rootfs.
        return None;
    }
    let comps = normalize_components(path);
    if comps.is_empty() {
        Some(format!("{rootfs}/"))
    } else {
        Some(format!("{rootfs}/{}", comps.join("/")))
    }
}

fn roundup16(n: u64) -> u64 {
    (n + 15) & !15
}

/// Write `s` plus NUL into the guest's stack scratch area below `sp`
/// (spec 2.4) and return its address. `cursor` starts at sp and moves
/// down, keeping a 256-byte safety margin under the live stack.
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

// ---- SIGTERM handling: kill the guest, then exit (spec 4) ----
static GUEST_PID: AtomicI32 = AtomicI32::new(0);

extern "C" fn on_sigterm(_sig: i32) {
    let p = GUEST_PID.load(Ordering::Relaxed);
    if p > 0 {
        unsafe { libc::kill(p, libc::SIGKILL) };
    }
    unsafe { libc::_exit(128 + 15) };
}

// ---- syscall-stop entry handling ----
struct Pending {
    nr: u64,
    desc: Option<String>,
    inject: Option<i64>,
}

/// Cancel the syscall the guest is about to enter: with x8 = -1 the
/// kernel skips execution, and we force x0 at the exit stop.
fn skip_syscall(regs: &mut UserPtRegs, pend: &mut Pending, value: i64) {
    regs.regs[8] = u64::MAX;
    pend.inject = Some(value);
}

/// T class: rewrite each path argument into the rootfs (spec 2.4/2.5)
/// and return a log description of what was done.
fn entry_translate(pid: i32, rootfs: &str, nr: u64, regs: &mut UserPtRegs) -> String {
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
            Some(old) => match translate(rootfs, dirfd, &old) {
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
        // path written back; accepted for M0 per spec 2.4.
        desc.push_str(" [note: readlink result may carry the rootfs prefix]");
    }
    desc
}

/// F class: cancel the syscall and fabricate the answer (spec 2.6).
fn entry_fake(pid: i32, nr: u64, regs: &mut UserPtRegs, pend: &mut Pending) -> String {
    match nr {
        NR_GETCWD => {
            let buf = regs.regs[0];
            let size = regs.regs[1];
            if size >= 2 && write_mem(pid, buf, b"/\0").is_ok() {
                skip_syscall(regs, pend, 2);
                "getcwd(17) FAKED -> \"/\"".to_string()
            } else {
                skip_syscall(regs, pend, -ERANGE);
                "getcwd(17) FAKED -> -ERANGE (buffer too small)".to_string()
            }
        }
        NR_CHDIR => {
            // Logical cwd never moves; relative opens anchor at "/".
            skip_syscall(regs, pend, 0);
            "chdir(49) FAKED -> 0 (logical cwd stays /)".to_string()
        }
        _ => {
            skip_syscall(regs, pend, 0);
            "fchdir(50) FAKED -> 0 (logical cwd stays /)".to_string()
        }
    }
}

// ---- guest output forwarding (spec 2.7) ----
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

fn read_first_line(path: &str) -> String {
    match std::fs::read(path) {
        Ok(bytes) => {
            let s = String::from_utf8_lossy(&bytes);
            s.lines().next().unwrap_or("").trim().to_string()
        }
        Err(e) => format!("<unreadable: {e}>"),
    }
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
        sup!("usage: libsupervisor.so <rootfs_abs_path> <guest_abs_path>");
        std::process::exit(2);
    }
    let rootfs = argv[1].clone();
    let guest_path = argv[2].clone();

    // Startup self-check lines (spec 2.2 step 2): the evidence that
    // separates "device policy" from "our bug" on the first run.
    sup!("supervisor pid={}", std::process::id());
    sup!("kernel: {}", read_first_line("/proc/version"));
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

    // Build exec arguments before fork: after fork the child may only
    // use async-signal-safe calls (spec 2.2 step 4).
    let guest_c = CString::new(guest_path.clone()).unwrap();
    let argv0_c = CString::new("guest").unwrap();
    let env_path = CString::new("PATH=/usr/bin:/bin").unwrap();
    let child_argv: [*const libc::c_char; 2] = [argv0_c.as_ptr(), std::ptr::null()];
    let child_envp: [*const libc::c_char; 2] = [env_path.as_ptr(), std::ptr::null()];

    let pid = unsafe { libc::fork() };
    if pid < 0 {
        sup!("fork failed: errno={}", errno());
        std::process::exit(1);
    }
    if pid == 0 {
        // ---- guest child ----
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

    let mut status: i32 = 0;
    let r = unsafe { libc::waitpid(pid, &mut status, 0) };
    if r != pid || !libc::WIFSTOPPED(status) {
        sup!("initial waitpid unexpected: r={r} status={status:#x}");
        std::process::exit(1);
    }
    let opts = (PTRACE_O_TRACESYSGOOD | PTRACE_O_TRACEEXEC | PTRACE_O_EXITKILL) as *mut libc::c_void;
    if ptrace4(PTRACE_SETOPTIONS, pid, std::ptr::null_mut(), opts) != 0 {
        sup!(
            "PTRACE_SETOPTIONS failed: errno={} ({})",
            errno(),
            std::io::Error::from_raw_os_error(errno())
        );
        std::process::exit(1);
    }
    sup!("ptrace options set (TRACESYSGOOD|TRACEEXEC|EXITKILL)");
    cont_syscall(pid, 0);

    // ---- main tracing loop (spec 2.2) ----
    let mut expect_exit = false;
    let mut pending: Option<Pending> = None;
    let mut launched = false;
    let mut seen: HashSet<u64> = HashSet::new();
    let mut counts: HashMap<u64, u64> = HashMap::new();

    loop {
        let mut status: i32 = 0;
        let r = unsafe { libc::waitpid(pid, &mut status, 0) };
        if r < 0 {
            let e = errno();
            if e == libc::EINTR {
                continue;
            }
            sup!("waitpid failed: errno={e}");
            break;
        }
        if libc::WIFEXITED(status) {
            sup!("GUEST_EXITED code={}", libc::WEXITSTATUS(status));
            break;
        }
        if libc::WIFSIGNALED(status) {
            sup!("GUEST_SIGNALED sig={}", libc::WTERMSIG(status));
            break;
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        let sig = libc::WSTOPSIG(status);
        let event = status >> 16;

        if sig == SYSCALL_STOP_SIG {
            if !expect_exit {
                // ---- syscall-entry stop ----
                let Some(mut regs) = get_regs(pid) else {
                    cont_syscall(pid, 0);
                    continue;
                };
                let nr = regs.regs[8];
                let mut pend = Pending { nr, desc: None, inject: None };
                let mut dirty = false;
                if (nr == 221 || nr == 281) && !launched {
                    // The guest's own launch exec (after TRACEME) must
                    // pass; only later execs are X class.
                    *counts.entry(nr).or_insert(0) += 1;
                    if seen.insert(nr) {
                        sys!("{}({}) pass (guest launch exec, allowed)", nr_name(nr), nr);
                    }
                } else if is_t_dirfd_path(nr)
                    || is_t_two_paths(nr)
                    || is_t_symlinkat(nr)
                    || is_t_path0(nr)
                {
                    pend.desc = Some(entry_translate(pid, &rootfs, nr, &mut regs));
                    dirty = true;
                } else if is_faked(nr) {
                    pend.desc = Some(entry_fake(pid, nr, &mut regs, &mut pend));
                    dirty = true;
                } else if is_blocked(nr) || nr == 221 || nr == 281 {
                    skip_syscall(&mut regs, &mut pend, -ENOSYS);
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
                pending = Some(pend);
            } else {
                // ---- syscall-exit stop ----
                if let Some(pend) = pending.take() {
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
            }
            expect_exit = !expect_exit;
            cont_syscall(pid, 0);
        } else if sig == SIGTRAP && event == PTRACE_EVENT_EXEC {
            launched = true;
            sup!("guest exec completed (launch)");
            cont_syscall(pid, 0);
        } else if sig == SIGTRAP {
            cont_syscall(pid, 0);
        } else {
            // Signal-delivery stop: reinject the signal unchanged
            // (M0 swallows none, spec 2.2).
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
