#!/usr/bin/env python3
"""Differential test of the G1 system calls (PLAN.md §7 G1): the model (`lake exe systest`, lean/Tools/SysTest.lean)
against the kernel this runs on.

Each case makes one system call natively (`syscall(2)` through ctypes) with its pointers into a read-write page
followed by an inaccessible one (PROT_NONE; unmapped in the model, which the kernel treats alike: EFAULT), the page
filled with the pattern `(7 * i + 3) % 256` and the case's bytes. The environment's answers the model asks for (the
names, the file system, the terminal) are taken from the same call made natively with a buffer the kernel can
write (the reference run, before and after the test run; a case whose reference answers differ is run again). Then
the model runs the call on the same page and answers, and the result (`rax`), the page after the call and the mask
(`umask`) must be the same; a path the model asks the environment about must be the case's path.

Usage: tools/systest/run.py [-v]. Exit status 0 when every case agrees.
"""
import ctypes
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN = os.path.join(ROOT, "lean")
EXE = os.path.join(LEAN, ".lake", "build", "bin", "systest")

libc = ctypes.CDLL(None, use_errno=True)
libc.syscall.restype = ctypes.c_long
libc.syscall.argtypes = [ctypes.c_long] * 5
libc.mmap.restype = ctypes.c_void_p
libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long]
libc.mprotect.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]

NR = {"madvise": 28, "stat": 4, "ioctl": 16, "uname": 63, "getcwd": 79, "readlink": 89, "umask": 95, "sysinfo": 99,
      "getdents64": 217}
TCGETS, TCGETS2 = 0x5401, 0x802C542A
M64 = (1 << 64) - 1

PAGE = libc.mmap(None, 8192, 3, 0x22, -1, 0)  # PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS
assert PAGE not in (None, ctypes.c_void_p(-1).value)
assert libc.mprotect(PAGE + 4096, 4096, 0) == 0
THP = os.path.isdir("/sys/kernel/mm/transparent_hugepage")  # CONFIG_TRANSPARENT_HUGEPAGE
PATTERN = bytes((7 * i + 3) % 256 for i in range(4096))


def sc(nr, *args):
    a = list(args) + [0] * (4 - len(args))
    r = libc.syscall(nr, *a)
    return (-ctypes.get_errno() if r == -1 else r) & M64


def reg(t):
    return PAGE + int(t[2:], 16) if t.startswith("b+") else int(t, 16)


def native_args(args):
    return [ctypes.c_long(reg(t) - (1 << 64) if reg(t) >= 1 << 63 else reg(t)).value for t in args]


def errtok(r):
    return "!%d" % ((-r) & M64) if r >= 1 << 63 else None


# The reference runs: what the kernel answers with a buffer it can write.
def ref_uname():
    b = ctypes.create_string_buffer(390)
    sc(NR["uname"], ctypes.addressof(b))
    return b.raw.hex()


def ref_sysinfo():
    b = ctypes.create_string_buffer(112)
    sc(NR["sysinfo"], ctypes.addressof(b))
    return b.raw.hex()


def ref_cwd():
    b = ctypes.create_string_buffer(8192)
    r = sc(NR["getcwd"], ctypes.addressof(b), 8192)
    return errtok(r) or b.raw[:r].hex()


def ref_stat(path):
    p = ctypes.create_string_buffer(path)
    b = ctypes.create_string_buffer(144)
    r = sc(NR["stat"], ctypes.addressof(p), ctypes.addressof(b))
    return errtok(r) or b.raw.hex()


def ref_link(path):
    p = ctypes.create_string_buffer(path)
    b = ctypes.create_string_buffer(8192)
    r = sc(NR["readlink"], ctypes.addressof(p), ctypes.addressof(b), 8192)
    return errtok(r) or b.raw[:r].hex()


def ref_dirents(fd, count):
    b = ctypes.create_string_buffer(1 << 16)
    r = sc(NR["getdents64"], fd, ctypes.addressof(b), count % (1 << 32))
    return errtok(r) or b.raw[:r].hex()


def ref_ioctl(fd, cmd, n):
    b = ctypes.create_string_buffer(64)
    r = sc(NR["ioctl"], fd, cmd, ctypes.addressof(b))
    return errtok(r) or b.raw[:n].hex()


class Case:
    """One call: `args` (hex, or `b+OFF` into the page), the bytes to put in the page first (`writes`), the mask
    before (`umask0`), a descriptor (`fd`: a function that opens it and returns `(fd, kind)`, called afresh for the
    reference and the test run), the answers (`answers(fd)`: KEY -> VALUE), the path the model must ask about, and
    whether the model may stop with `nm` (a case it does not model), or must ask the environment nothing (`noreq`)."""

    def __init__(self, name, call, args, writes=(), umask0=0o022, fd=None, answers=None, path=None, nm_ok=False,
                 pre=None, noreq=False):
        self.name, self.call, self.args, self.writes = name, call, args, list(writes)
        self.umask0, self.fd, self.answers, self.path, self.nm_ok, self.pre = umask0, fd, answers, path, nm_ok, pre
        self.noreq = noreq

    def open(self):
        if self.fd is None:
            return None, "-"
        fd, kind = self.fd()
        if self.pre:
            self.pre(fd)
        return fd, kind

    def ref(self):
        fd, _ = self.open()
        a = self.answers(fd) if self.answers else {}
        if fd is not None and fd >= 0:
            os.close(fd)
        return a

    def native(self):
        fd, kind = self.open()
        page = bytearray(PATTERN)
        for o, bs in self.writes:
            page[o:o + len(bs)] = bs
        ctypes.memmove(PAGE, bytes(page), 4096)
        os.umask(self.umask0)
        args = [a.replace("FD", "%08x" % fd) if fd is not None else a for a in self.args]
        r = sc(NR[self.call], *native_args(args))
        um = os.umask(0o022)
        out = ctypes.string_at(PAGE, 4096)
        if fd is not None and fd >= 0:
            os.close(fd)
        fdtok = "-" if fd is None or kind == "closed" else "%d:%s" % (fd, kind)
        return args, fdtok, r, um, out

    def run(self):
        for _ in range(20):
            a0 = self.ref()
            args, fdtok, r, um, out = self.native()
            if self.ref() == a0:
                break
        else:
            raise SystemExit("%s: the reference answers change between runs" % self.name)
        regs = (["%x" % NR[self.call]] + args + ["0"] * 4)[:5]
        toks = regs + ["%x" % self.umask0, fdtok] + ["%s=%s" % kv for kv in a0.items()]
        toks += ["w=%x:%s" % (o, bs.hex()) for o, bs in self.writes]
        return " ".join(toks), (r, um, out)


def cases(tmp):
    cs = []
    good = lambda: {"uname": ref_uname()}  # noqa: E731
    for name, a in [("ok", "b+0"), ("end", "b+e7a"), ("straddle", "b+f00"), ("straddle1", "b+e7b"),
                    ("unmapped", "b+1000"), ("null", "0"), ("noncanon", "800000000000"),
                    ("kernel", "ffffffffff600000"), ("last-page", "7ffffffff000")]:
        cs.append(Case("uname/" + name, "uname", [a], answers=lambda fd: good()))
    for name, a in [("ok", "b+0"), ("straddle", "b+fc0"), ("unmapped", "b+2000"), ("null", "0")]:
        cs.append(Case("sysinfo/" + name, "sysinfo", [a], answers=lambda fd: {"sysinfo": ref_sysinfo()}))
    for u0, a in [(0o022, "0"), (0o777, "1ff"), (0o123, "ffffffffffff0abc"), (0, "fffffe00"), (0o644, "777")]:
        cs.append(Case("umask/%o:%s" % (u0, a), "umask", [a], umask0=u0))

    cwd = os.getcwd().encode()
    n = len(cwd) + 1
    cw = lambda fd: {"cwd": ref_cwd()}  # noqa: E731
    for name, a, size in [("ok", "b+0", "%x" % n), ("exact-end", "b+%x" % (4096 - n), "%x" % n),
                          ("short", "b+0", "%x" % (n - 1)), ("zero", "b+0", "0"), ("huge", "b+0", "ffffffffffffffff"),
                          ("size-hi", "b+0", "100000000"), ("straddle", "b+%x" % (4096 - n + 3), "1000"),
                          ("unmapped", "b+1000", "1000"), ("null", "0", "1000"), ("noncanon", "800000000000", "1000")]:
        cs.append(Case("getcwd/" + name, "getcwd", [a, size], answers=cw))

    # stat: a file, a directory, a link (followed), a dangling link, a missing name.
    f = os.path.join(tmp, "file").encode()
    d = os.path.join(tmp, "dir").encode()
    ln = os.path.join(tmp, "link").encode()
    dang = os.path.join(tmp, "dangling").encode()
    st = lambda p: (lambda fd: {"stat": ref_stat(p)})  # noqa: E731
    for name, p in [("file", f), ("dir", d), ("link", ln), ("dangling", dang), ("missing", f + b"x"),
                    ("dev", b"/dev/null"), ("proc", b"/proc/self/exe"), ("notdir", f + b"/x")]:
        cs.append(Case("stat/" + name, "stat", ["b+100", "b+800"], writes=[(0x100, p + b"\0")], answers=st(p),
                       path=p))
    cs.append(Case("stat/empty", "stat", ["b+100", "b+800"], writes=[(0x100, b"\0")], noreq=True))
    cs.append(Case("stat/buf-straddle", "stat", ["b+100", "b+f80"], writes=[(0x100, f + b"\0")], answers=st(f),
                   path=f))
    cs.append(Case("stat/buf-unmapped", "stat", ["b+100", "b+1000"], writes=[(0x100, f + b"\0")], answers=st(f),
                   path=f))
    cs.append(Case("stat/path-null", "stat", ["0", "b+800"], noreq=True))
    cs.append(Case("stat/path-straddle", "stat", ["b+ff0", "b+0"], writes=[(0xff0, b"a" * 16)], noreq=True))
    cs.append(Case("stat/path-4096", "stat", ["b+0", "b+0"], writes=[(0, b"a" * 4096)], noreq=True))
    p4095 = b"/" * 4095  # with its NUL the whole page: the longest name `PATH_MAX` admits
    cs.append(Case("stat/path-4095", "stat", ["b+0", "b+0"], writes=[(0, p4095 + b"\0")], answers=st(p4095),
                   path=p4095))

    # readlink
    rl = lambda p: (lambda fd: {"link": ref_link(p)})  # noqa: E731
    target = os.readlink(ln)
    tl = len(target)
    for name, buf, size in [("ok", "b+800", "1000"), ("exact", "b+800", "%x" % tl), ("trunc", "b+800", "%x" % (tl - 3)),
                            ("one", "b+800", "1"), ("hi-bits", "b+800", "100000005"),
                            ("straddle", "b+%x" % (4096 - tl + 2), "1000"), ("unmapped", "b+1000", "1000"),
                            ("null", "0", "1000")]:
        cs.append(Case("readlink/" + name, "readlink", ["b+100", buf, size], writes=[(0x100, ln + b"\0")],
                       answers=rl(ln), path=ln))
    # `bufsiz <= 0` (an `int`) is EINVAL before the name is looked up.
    for name, size in [("zero", "0"), ("neg", "ffffffff"), ("neg64", "ffffffff80000000")]:
        cs.append(Case("readlink/" + name, "readlink", ["b+100", "b+800", size], writes=[(0x100, ln + b"\0")],
                       noreq=True))
    for name, p in [("notlink", f), ("missing", f + b"x"), ("exe", b"/proc/self/exe"), ("dangling", dang)]:
        cs.append(Case("readlink/" + name, "readlink", ["b+100", "b+800", "1000"], writes=[(0x100, p + b"\0")],
                       answers=rl(p), path=p))
    cs.append(Case("readlink/empty", "readlink", ["b+100", "b+800", "1000"], writes=[(0x100, b"\0")],
                   answers=rl(b"")))

    # getdents64
    def opener(path, flags, kind):
        return lambda: (os.open(path, flags), kind)

    dirfd = opener(tmp, os.O_RDONLY | os.O_DIRECTORY, "none")
    cpu = opener("/sys/devices/system/cpu", os.O_RDONLY | os.O_DIRECTORY, "none")
    de = lambda count: (lambda fd: {"dirents": ref_dirents(fd, count)})  # noqa: E731

    def drain(fd):
        b = ctypes.create_string_buffer(1 << 16)
        while sc(NR["getdents64"], fd, ctypes.addressof(b), 1 << 16) not in range(0, 1):
            pass

    for name, fdf, count in [("tmp", dirfd, 0x1000), ("cpu", cpu, 0x1000), ("small", dirfd, 0x30),
                             ("first-only", dirfd, 0x18), ("tiny", dirfd, 0x17), ("zero", dirfd, 0),
                             ("count-hi", dirfd, (1 << 32) | 0x1000), ("count-big", dirfd, 0xFFFFFFFF)]:
        cs.append(Case("getdents64/" + name, "getdents64", ["FD", "b+0", "%x" % count], fd=fdf, answers=de(count)))
    cs.append(Case("getdents64/fd-hi", "getdents64", ["1FD", "b+0", "1000"], fd=dirfd, answers=de(0x1000)))
    cs.append(Case("getdents64/drained", "getdents64", ["FD", "b+0", "1000"], fd=dirfd, answers=de(0x1000),
                   pre=drain))
    cs.append(Case("getdents64/regular", "getdents64", ["FD", "b+0", "1000"],
                   fd=opener(f, os.O_RDONLY, "pages"), noreq=True))
    cs.append(Case("getdents64/opath", "getdents64", ["FD", "b+0", "1000"],
                   fd=opener(tmp, os.O_PATH | os.O_DIRECTORY, "path"), noreq=True))
    cs.append(Case("getdents64/closed", "getdents64", ["3e7", "b+0", "1000"], noreq=True))
    cs.append(Case("getdents64/straddle", "getdents64", ["FD", "b+fd0", "1000"], fd=dirfd, answers=de(0x1000),
                   nm_ok=True))
    cs.append(Case("getdents64/unmapped", "getdents64", ["FD", "b+1000", "1000"], fd=dirfd, answers=de(0x1000),
                   nm_ok=True))

    # ioctl(TCGETS), ioctl(TCGETS2): a terminal, a regular file.
    masters = []

    def pty():  # the slave side; its master stays open (a hung-up terminal answers EIO)
        m, s = os.openpty()
        masters.append(m)
        return s, "other"

    io = lambda cmd, n: (lambda fd: {"ioctl": ref_ioctl(fd, cmd, n)})  # noqa: E731
    for name, cmd, n in [("tcgets", TCGETS, 36), ("tcgets2", TCGETS2, 44)]:
        cs.append(Case("ioctl/%s-pty" % name, "ioctl", ["FD", "%x" % cmd, "b+0"], fd=pty, answers=io(cmd, n)))
        cs.append(Case("ioctl/%s-straddle" % name, "ioctl", ["FD", "%x" % cmd, "b+ff0"], fd=pty, answers=io(cmd, n)))
        cs.append(Case("ioctl/%s-file" % name, "ioctl", ["FD", "%x" % cmd, "b+0"],
                       fd=opener(f, os.O_RDONLY, "pages"), answers=io(cmd, n)))
    cs.append(Case("ioctl/tcgets-cmd-hi", "ioctl", ["FD", "100005401", "b+0"], fd=pty, answers=io(TCGETS, 36)))
    cs.append(Case("ioctl/closed", "ioctl", ["3e7", "5401", "b+0"], noreq=True))

    # madvise(MADV_HUGEPAGE = 14, MADV_NOHUGEPAGE = 15), which `t` of a bzip2 archive gives a large buffer; the page
    # after the test page is PROT_NONE natively but unmapped in the model (ENOMEM), so the ranges stay in the page.
    for name, a, n, adv in [("huge", "b+0", "1000", "e"), ("nohuge", "b+0", "1000", "f"), ("short", "b+0", "1", "e"),
                            ("empty", "b+0", "0", "e"), ("misaligned", "b+1", "1000", "e"),
                            ("advice-hi", "b+0", "1000", "10000000e"), ("wrap", "b+0", "fffffffffffff001", "e")]:
        cs.append(Case("madvise/" + name, "madvise", [a, n, adv]))
    return cs


def deep_cases(tmp):
    """getcwd in a directory whose path, with its NUL, is 4095, 4096 and 4097 bytes long (`PATH_MAX`)."""
    out = []
    for total in (4095, 4096, 4097):
        base = os.path.join(tmp, "deep%d" % total)
        os.mkdir(base)
        here = os.getcwd()
        os.chdir(base)
        path = base.encode()
        while len(path) + 1 + 201 < total:
            os.mkdir("d" * 200)
            os.chdir("d" * 200)
            path += b"/" + b"d" * 200
        last = b"e" * (total - 1 - len(path) - 1)
        os.mkdir(last)
        os.chdir(last)
        path += b"/" + last
        assert len(path) + 1 == total
        c = Case("getcwd/deep-%d" % total, "getcwd", ["b+0", "1000"], answers=lambda fd, p=path: {"cwd": p.hex()})
        out.append(c.run() + (c,))
        os.chdir(here)
    return out


def main():
    verbose = "-v" in sys.argv
    subprocess.run(["lake", "build", "systest"], cwd=LEAN, check=True, stdout=subprocess.DEVNULL)
    with tempfile.TemporaryDirectory(prefix="fv7z-systest-") as tmp:
        open(os.path.join(tmp, "file"), "wb").write(b"contents\n")
        os.mkdir(os.path.join(tmp, "dir"))
        for i in range(12):
            open(os.path.join(tmp, "dir", "entry-%02d-%s" % (i, "x" * i)), "wb").close()
        os.symlink(os.path.join(tmp, "file"), os.path.join(tmp, "link"))
        os.symlink(os.path.join(tmp, "nowhere"), os.path.join(tmp, "dangling"))
        cs = cases(tmp)
        runs = [c.run() + (c,) for c in cs] + deep_cases(tmp)
    lines = "".join(l + "\n" for l, _, _ in runs)
    res = subprocess.run([EXE] + (["thp"] if THP else []), input=lines, capture_output=True, text=True, check=True).stdout.splitlines()
    assert len(res) == len(runs), (len(res), len(runs))
    bad = 0
    for (line, (r, um, out), c), m in zip(runs, res):
        t = m.split(" ")
        why = None
        if t[0] == "nm":
            if not c.nm_ok:
                why = "model stops: " + m
        elif t[0] != "ok":
            why = "model: " + m
        else:
            mr, mu, reqs, mpage = int(t[1], 16), int(t[2], 16), t[3], bytes.fromhex(t[4])
            if mr != r:
                why = "rax native %x model %x" % (r, mr)
            elif c.call == "umask" and mu != um:
                why = "umask native %o model %o" % (um, mu)
            elif mpage != out:
                diff = [i for i in range(4096) if mpage[i] != out[i]]
                why = "page differs at %d bytes from %#x (native %s model %s)" % (
                    len(diff), diff[0], out[diff[0]:diff[0] + 16].hex(), mpage[diff[0]:diff[0] + 16].hex())
            elif c.noreq and reqs != "-":
                why = "model asked the environment: " + reqs
            elif c.path is not None and r != (-14 & M64) and (":%s:" % c.path.hex()) not in reqs + ":" and \
                    (":%s" % c.path.hex()) not in reqs:
                why = "model asked about another path: " + reqs
        status = "ok" if why is None else "DIFF"
        if why or verbose:
            print("%-28s %s native rax=%x %s" % (c.name, status, r, why or (t[3][:100] if t[0] == "ok" else t[0])))
        bad += why is not None
    print("%d cases, %d mismatches (kernel %s, thp %s)" % (len(runs), bad, os.uname().release, THP))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
