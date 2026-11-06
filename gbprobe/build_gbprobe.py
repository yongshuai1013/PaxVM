#!/usr/bin/env python3
"""Build gbprobe, the guest graphics probe.

lld cannot link the 2011 guest .so files directly (their
symbol tables predate its checks), so -- exactly like the
paxsvc libc stub, generalized -- this script:

  1. compiles gbprobe.cpp + entry.c against the era
     headers vendored in gbprobe/include,
  2. reads the objects' undefined symbols,
  3. finds each symbol's home library among the REAL guest
     libraries (llvm-readelf reads them fine),
  4. generates one assembly stub .so per library carrying
     exactly those names (functions as bx lr, objects as
     zero-filled storage of the recorded size), with the
     right SONAME,
  5. links the probe against the stubs only. The guest
     linker binds the real libraries at run time.

Usage: build_gbprobe.py <clang-dir> <guest-lib-dir> <out>
Objects and stubs land in a temp dir under /tmp.
"""
import os
import subprocess
import sys
import tempfile

LIBS = [
    "libc.so",
    "libstdc++.so",
    "libm.so",
    "libdl.so",
    "libcutils.so",
    "liblog.so",
    "libutils.so",
    "libbinder.so",
    "libsurfaceflinger_client.so",
    "libui.so",
    "libEGL.so",
    "libGLESv1_CM.so",
    "libhardware.so",
    "libpixelflinger.so",
]

HERE = os.path.dirname(os.path.abspath(__file__))


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.stderr.write("FAILED: %s\n%s\n%s\n" % (" ".join(cmd), r.stdout, r.stderr))
        sys.exit(1)
    return r.stdout


def _sym_rows(readelf, path, dyn):
    """Yield (name, type, size, bind, ndx) per symbol row.

    llvm-readelf rows are whitespace-separated:
    Num: Value Size Type Bind Vis Ndx Name[@ver]
    """
    out = run([readelf, "--dyn-syms" if dyn else "-s", "-W", path])
    for line in out.splitlines():
        t = line.split()
        if len(t) < 8 or not t[0].endswith(":") or not t[0][:-1].strip().isdigit():
            continue
        name = t[7].split("@")[0]
        yield name, t[3], int(t[2]), t[4], t[6]


def dynsyms(readelf, path):
    """name -> (type, size) for defined dynamic symbols."""
    syms = {}
    for name, typ, size, bind, ndx in _sym_rows(readelf, path, True):
        if (
            name
            and ndx != "UND"
            and typ in ("FUNC", "OBJECT", "NOTYPE", "TLS")
            and bind in ("GLOBAL", "WEAK")
        ):
            syms.setdefault(name, (typ, size))
    return syms


def undef_syms(readelf, path):
    return [
        name
        for name, _t, _s, _b, ndx in _sym_rows(readelf, path, False)
        if ndx == "UND" and name
    ]


def main():
    tc, libdir, outpath = sys.argv[1], sys.argv[2], sys.argv[3]
    clang = os.path.join(tc, "clang")
    clangxx = os.path.join(tc, "clang++")
    readelf = os.path.join(tc, "llvm-readelf")
    target = "armv7a-linux-androideabi"
    tmp = tempfile.mkdtemp(prefix="gbprobe-")

    common = [
        "--target=" + target,
        "-marm",
        "-O2",
        "-fno-stack-protector",
        "-fno-builtin",
        "-nostdlib",
    ]
    obj_cpp = os.path.join(tmp, "gbprobe.o")
    run(
        [clangxx]
        + common
        + [
            "-std=gnu++98",
            "-DHAVE_SYS_UIO_H",
            "-fno-exceptions",
            "-fno-rtti",
            "-nostdinc++",
            "-I",
            os.path.join(HERE, "include"),
            "-c",
            os.path.join(HERE, "gbprobe.cpp"),
            "-o",
            obj_cpp,
        ]
    )
    obj_c = os.path.join(tmp, "entry.o")
    run([clang] + common + ["-c", os.path.join(HERE, "entry.c"), "-o", obj_c])

    homes = {}
    for lib in LIBS:
        homes[lib] = dynsyms(readelf, os.path.join(libdir, lib))

    defined = set()
    for obj in (obj_cpp, obj_c):
        for name, _t, _s, _b, ndx in _sym_rows(readelf, obj, False):
            if ndx != "UND" and name:
                defined.add(name)
    need = {}
    missing = []
    for name in set(undef_syms(readelf, obj_cpp) + undef_syms(readelf, obj_c)) - defined:
        for lib in LIBS:
            if name in homes[lib]:
                need.setdefault(lib, {})[name] = homes[lib][name]
                break
        else:
            missing.append(name)
    if missing:
        sys.stderr.write("symbols in no guest library: %s\n" % ", ".join(sorted(missing)))
        sys.exit(1)

    stub_paths = []
    for lib, syms in sorted(need.items()):
        src = os.path.join(tmp, lib + ".s")
        with open(src, "w") as f:
            for name, (typ, size) in sorted(syms.items()):
                f.write(".globl %s\n" % name)
                if typ == "FUNC":
                    f.write(".type %s, %%function\n%s:\n    bx lr\n" % (name, name))
                else:
                    f.write(
                        ".type %s, %%object\n.section .bss\n%s:\n    .zero %d\n"
                        % (name, name, max(size, 4))
                    )
        so = os.path.join(tmp, lib)
        run(
            [clang, "--target=" + target, "-nostdlib", "-shared",
             "-Wl,-soname," + lib, "-o", so, src]
        )
        stub_paths.append(so)

    run(
        [clangxx]
        + common
        + [
            "-no-pie",
            "-Wl,-e,_start",
            "-Wl,--no-undefined",
            "-Wl,--as-needed",
            "-Wl,-dynamic-linker,/system/bin/linker",
            "-o",
            outpath,
            obj_cpp,
            obj_c,
        ]
        + stub_paths
    )
    print("gbprobe built:", outpath)


if __name__ == "__main__":
    main()
