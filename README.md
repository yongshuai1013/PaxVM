# PaxVM

Self-developed Android VM engine — a userspace-kernel route in the
spirit of the titan engine (VPhoneOS) and twoyi, but written from
scratch: no fork, no PRoot code, only published designs as reference.

## M0 (this milestone)

The smallest end-to-end proof of the engine's heart — *ptrace
supervision + syscall proxying + native execution* — on an unrooted
moto g51 (Snapdragon 480, Android 12):

- **Shell app** (Kotlin, Holo dark): one screen with start/stop
  buttons and a log view. Zero JNI — it launches the supervisor with
  `ProcessBuilder` and renders its stdout line protocol.
- **Supervisor** (Rust, aarch64 Android PIE, shipped as
  `libsupervisor.so`): forks the guest, attaches with ptrace
  (classic `PTRACE_SYSCALL` double-stop + `GETREGSET`), rewrites
  path-carrying syscalls into an app-sandbox rootfs, fabricates a
  small set (getcwd/chdir), blocks escapes with `-ENOSYS`, and
  passes everything else through while logging first occurrences.
- **Guest** (Rust, fully static aarch64 musl, shipped as
  `libguest.so`): prints markers, writes `/tmp/out.txt`, reads it
  back, and reads a shell-seeded `/seed.txt`.

Acceptance: on the device, the log shows the guest's output and the
read-back content, with the openat translation pair proving the file
landed in `files/vm0/rootfs/` rather than the host `/tmp`.

Design source of truth: the M0 spec (kept outside this repo) fixes
the syscall T/F/P/X classification, the stack-scratch path rewrite,
and the packaging rule (`useLegacyPackaging = true`, exec from
`nativeLibraryDir`).

## Build

GitHub Actions (`build` workflow): builds both Rust payloads (the
guest with an INTERP assertion), copies them into `jniLibs`, and
assembles a debug APK uploaded as the `paxvm-apk` artifact.
