#!/usr/bin/env python3
"""The policy of part (B) of `Confined` (lean/FV7z/Statement/Policy.lean, `allowT`), checked on real runs.

Builds a small corpus with 7zzs itself (as tools/systrace.sh does), runs `7zzs l` and `7zzs t` on each archive under
the single-thread flags of PLAN.md §6.2 (7z: -mmt1 -mmtf=off, the rest: -mmt1) with `strace -X raw -e raw=all`, and
checks that every system call after the launch's `execve` is one `allowT` accepts, with its arguments. A refusal means
the Lean policy is too strict for a real run (the theorem could not hold), or that 7zzs does something the policy
should refuse. Not evidence for a theorem: a test of the statement before proofs rely on it.

Keep `allow` the same as `allowT` (same numbers, same argument tests).
Usage: tools/policy.py BINARY [WORKDIR]
"""
import lzma
import os
import re
import subprocess
import sys
import tempfile

# x86-64 numbers of the calls 7zzs makes (arch/x86/entry/syscalls/syscall_64.tbl), and of some it must not
NR = {
    "read": 0, "write": 1, "close": 3, "stat": 4, "fstat": 5, "lseek": 8, "mmap": 9, "mprotect": 10,
    "munmap": 11, "brk": 12, "rt_sigaction": 13, "rt_sigprocmask": 14, "ioctl": 16, "pread64": 17,
    "madvise": 28, "clone": 56, "fork": 57, "vfork": 58, "execve": 59, "uname": 63, "getcwd": 79, "mkdir": 83,
    "readlink": 89, "umask": 95, "sysinfo": 99, "arch_prctl": 158, "futex": 202, "getdents64": 217,
    "set_tid_address": 218, "exit_group": 231, "openat": 257, "newfstatat": 262, "set_robust_list": 273,
    "prlimit64": 302, "getrandom": 318, "rseq": 334, "lstat": 6, "utimensat": 280, "socket": 41,
}

ANY = {0, 3, 4, 5, 8, 11, 12, 13, 14, 28, 63, 79, 89, 95, 99, 158, 202, 217, 218, 231, 273}


def allow(nr, a):
    """`allowT` of Policy.lean."""
    a = a + [0] * (6 - len(a))
    if nr in ANY:
        return True
    if nr == 1:
        return a[0] in (1, 2)
    if nr in (9, 10):
        return a[2] & 4 == 0
    if nr == 16:
        return a[1] in (0x5401, 0x5413, 0x802C542A)
    if nr == 257:
        return a[2] & 0x243 == 0
    if nr == 302:
        return a[2] == 0
    return False


LINE = re.compile(r"^(?:\d+ +)?([a-z_0-9]+)\((.*)\) += ")


def calls(path):
    """The calls of a `strace -X raw -e raw=all` log: (name, args)."""
    for ln in open(path):
        m = LINE.match(ln)
        if not m:
            continue
        args = [int(x, 16) if x.startswith("0x") else int(x) for x in m.group(2).split(", ") if x]
        yield m.group(1), args


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__.strip().splitlines()[-1])
    binp = os.path.realpath(sys.argv[1])
    work = sys.argv[2] if len(sys.argv) > 2 else tempfile.mkdtemp(prefix="policy.")
    os.makedirs(work, exist_ok=True)
    run = lambda *c: subprocess.run(c, cwd=work, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    src = os.path.join(work, "src")
    os.makedirs(os.path.join(src, "sub"), exist_ok=True)
    with open(os.path.join(src, "rand.bin"), "wb") as f:
        f.write(os.urandom(300000))
    with open(os.path.join(src, "seq.txt"), "w") as f:
        f.write("".join(f"{i}\n" for i in range(1, 200001)))
    fmts = ["7z", "zip", "tar", "xz", "gzip", "bzip2", "wim", "lzma"]
    for f in fmts[:-1]:
        what = "src/seq.txt" if f in ("xz", "gzip", "bzip2") else "src"
        run(binp, "a", f"-t{f}", f"c.{f}", what, "-bso0", "-bsp0")
    # 7zzs does not write .lzma (E_NOTIMPL): the "alone" format, from Python (M1's format, PLAN.md §M)
    with open(os.path.join(src, "seq.txt"), "rb") as i, open(os.path.join(work, "c.lzma"), "wb") as o:
        o.write(lzma.compress(i.read(), format=lzma.FORMAT_ALONE))
    bad = 0
    for f in fmts:
        flags = ["-t7z", "-mmt1", "-mmtf=off"] if f == "7z" else ["-mmt1"]
        if f == "lzma":
            flags = ["-tlzma:s0", "-mmt1"]
        for cmd in ("l", "t"):
            log = os.path.join(work, f"{cmd}.{f}.strace")
            run("strace", "-f", "-qq", "-X", "raw", "-e", "raw=all", "-o", log, binp, cmd, f"c.{f}", *flags)
            seen = list(calls(log))
            if not seen or seen[0][0] != "execve":
                print(f"{cmd} {f}: no execve first in {log}")
                bad += 1
                continue
            if not any(n == "read" and a and a[0] >= 3 for n, a in seen):
                print(f"{cmd} {f}: never read the archive ({log})")
                bad += 1
            refused = [(n, a) for n, a in seen[1:] if not allow(NR.get(n, -1), a)]
            print(f"{cmd} {f}: {len(seen) - 1} calls, {len(refused)} refused")
            for n, a in refused[:5]:
                print(f"  refused: {n}({', '.join(hex(x) for x in a)})")
            bad += bool(refused)
    print("ok: the policy accepts every run" if not bad else f"FAIL: {bad} runs refused")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
