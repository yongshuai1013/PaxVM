//! PaxVM M0 guest: the smallest possible tracee.
//!
//! A fully static aarch64 musl binary (packaged as libguest.so). It is
//! launched under the supervisor's ptrace and performs the four
//! verifiable actions fixed by the M0 spec (section 3), printing one
//! marker line per action so the shell log can be checked line by line.
//! It deliberately stays single-threaded, uses only absolute paths,
//! and reads neither argv nor the environment, to keep the syscall
//! surface minimal and observable.

use std::fs;
use std::io::Write;

fn main() {
    let stdout = std::io::stdout();
    let mut out = stdout.lock();

    let _ = writeln!(out, "GUEST_START");
    let _ = out.flush();

    let _ = writeln!(out, "PID={}", std::process::id());
    let _ = out.flush();

    // Written under the guest's view of "/" -- the supervisor rewrites
    // the path into the app sandbox rootfs before the kernel sees it.
    fs::write("/tmp/out.txt", "hello-from-guest\n").expect("write /tmp/out.txt");
    let back = fs::read_to_string("/tmp/out.txt").expect("read /tmp/out.txt");
    let _ = writeln!(out, "READBACK={}", back.trim_end());
    let _ = out.flush();

    // Seeded by the shell before launch (spec section 4).
    let seed = fs::read_to_string("/seed.txt").expect("read /seed.txt");
    let _ = writeln!(out, "SEED={}", seed.trim_end());
    let _ = out.flush();

    let _ = writeln!(out, "GUEST_DONE");
    let _ = out.flush();
}
