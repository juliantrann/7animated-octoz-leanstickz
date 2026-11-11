#!/usr/bin/env python3
"""Port what the project pins to one release of 7zzs to the next release (PLAN.md §11).

A new release moves every function and every datum of the statically linked, non-PIE 7zzs, so everything the Lean
sources and the tools say about the old file by address is rewritten: addresses, the bytes pinned at an address, and
the displacements in decoding facts. What the rewriting produces is checked afterwards by what checked the original:
the `_pin` theorems (the kernel's evaluation of the ELF reader on the new file), the `Dec` facts (`rfl` on the new
bytes) and the proofs themselves. This tool is not trusted, and neither is its address map: a wrong address in a
*statement* (`FV7z/Spec`, `Challenges`) is what review and the measurements of tools/dispatch.py guard against.

The address map (old virtual address -> new), from tools/reldiff.py's outputs:
  code   inside a function that is the same after relocation: the paired function, same offset; a changed function:
         its entry only; between two functions that moved by the same amount: that amount
  data   an address the paired functions name: what they name in its place; any other address: the offset of its
         two nearest named neighbours in its section, if they agree
An address without an image under these rules is left as it is and reported (exit status 1).

What is rewritten in each FILE:
  1. hexadecimal literals of six digits inside the old image (`0x615ab0`), and identifiers `r<address>` (`r638e80`)
  2. `def NAME : List Byte := [...]` for each NAME its file pins by `Exe.bytesAt ...zzs.blob 0xADDR N = some NAME :=`: the N bytes of the new file at the new address (the old list must be the old file's bytes)
  3. in `Dec feat NAME K (FV7z.mk ... LEN)`, for an instruction whose bytes differ between the two files: the
     numbers that are the value of a 32-bit field that changed (`mrip D`, `.rel R`, an `.imm` that is an address)
  4. with --version OLD NEW (e.g. 26.05 26.06): `V2605`, `26.05`, `7z2605`

Usage: port.py [--write] [--version OLD NEW] RELDIFF.tsv DATAMAP.tsv OLD_BIN NEW_BIN FILE...
       (without --write: only the report, on stdout). The FILEs must be as they were for the old release: a second
       run on its own output stops at the byte lists.

The steps of a port, from a tree whose checks pass for OLD (done for 26.05 -> 26.06, PLAN.md §11):
  1. the new tarball into release/NEW (digest from the release page), pins/release-NEW.sha256
  2. objdump.tsv and funcs.tsv of both 7zzs (the first lines of tools/g0.sh), then tools/reldiff.py
  3. this tool with --write --version OLD NEW on lean/**/*.lean and the tools with addresses (prepare_gen.py,
     dispatch.py, codemap.py); `git mv` of lean/Challenges/V<OLD>; the SHA-256 in lean/FV7z/Image.lean; the
     version, tarball name and upstream commit in tools/*.sh, .github/workflows, checks/*/comparator.json
  4. tools/setup.sh, tools/ci.sh: what the port got wrong fails there (pins, proofs, g0, dispatch)
"""
import bisect, re, subprocess, sys

M64 = 1 << 64


def sections(path):
    out = subprocess.run(["readelf", "-S", "-W", path], capture_output=True, text=True, check=True).stdout
    secs = []
    for l in out.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+\S+\s+(\S*)", l)
        if m and int(m.group(2), 16):
            secs.append((m.group(1), int(m.group(2), 16), int(m.group(4), 16), "X" in m.group(5)))
    return secs


class Amap:
    def __init__(self, reldiff, datamap, obin, nbin):
        self.fn = []
        for l in open(reldiff):
            c = l.rstrip("\n").split("\t")
            if c[0] and c[1]:
                self.fn.append((int(c[0], 16), int(c[2]), int(c[1], 16), c[4]))
            elif c[0]:
                self.fn.append((int(c[0], 16), int(c[2]), None, c[4]))
        self.fn.sort()
        self.starts = [f[0] for f in self.fn]
        self.dm = {}
        for l in open(datamap):
            x, y, agree, uses = l.split("\t")
            if agree == uses.strip():
                self.dm[int(x, 16)] = int(y, 16)
        self.known = sorted(self.dm)
        self.osec, self.nsec = sections(obin), {n: (a, z) for n, a, z, _ in sections(nbin)}
        self.lo = min(a for _, a, _, _ in self.osec)
        self.hi = max(a + z for _, a, z, _ in self.osec)

    def sec(self, a):
        for n, s, z, x in self.osec:
            if s <= a < s + z:
                return n, s, z, x
        for n, s, z, x in self.osec:                 # an end address
            if a == s + z:
                return n, s, z, x
        return None

    def __call__(self, a):
        """(new address or None, how)"""
        if a == 0x400000:
            return a, "image base"
        s = self.sec(a)
        if s is None:
            return None, "in no section"
        n, s0, z, x = s
        if x and a < s0 + z or (x and a not in self.dm):
            return self.code(a)
        if a in self.dm:
            return self.dm[a], "data, named by code"
        if n in self.nsec and self.nsec[n] == (s0, z) and a < 0x401000:
            return a, f"{n}, not moved"
        i = bisect.bisect_left(self.known, a)
        lo = self.known[i - 1] if i > 0 else None
        hi = self.known[i] if i < len(self.known) else None
        ok = lambda k: k is not None and s0 <= k <= s0 + z
        if ok(lo) and ok(hi) and self.dm[lo] - lo == self.dm[hi] - hi:
            return a + self.dm[lo] - lo, f"data in {n}, between {lo:x} and {hi:x}"
        return None, f"data in {n}, neighbours disagree or are missing"

    def code(self, a):
        i = bisect.bisect_right(self.starts, a) - 1
        if i < 0:
            return None, "before the first function"
        o, z, n, v = self.fn[i]
        paired = n is not None and v in ("same", "moved")
        if a < o + z:
            if paired:
                return n + a - o, "code" if a == o else f"code, {o:x}+{a - o}"
            if v == "changed" and a == o:
                return n, "code, entry of a changed function"
            return None, f"code inside a {v} function ({o:x})"
        if paired and a == o + z:
            return n + z, f"code, end of {o:x}"
        if paired and i + 1 < len(self.fn):
            o2, _, n2, v2 = self.fn[i + 1]
            if n2 is not None and v2 in ("same", "moved") and n2 - o2 == n - o:
                return a + n - o, f"padding after {o:x}"
        return None, f"padding after {o:x}, neighbours moved differently"


def image(path):
    data = open(path, "rb").read()
    out = subprocess.run(["readelf", "-l", "-W", path], capture_output=True, text=True, check=True).stdout
    segs = [(int(m[1], 16), int(m[0], 16), int(m[2], 16)) for m in
            re.findall(r"LOAD\s+0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+0x[0-9a-f]+\s+0x([0-9a-f]+)", out)]

    def at(a, n):
        for va, off, fz in segs:
            if va <= a and a + n <= va + fz:
                return data[off + a - va: off + a - va + n]
        raise Exception(f"{a:x}+{n}: not in the file")
    return at


def main():
    args = sys.argv[1:]
    write = "--write" in args
    if write:
        args.remove("--write")
    ver = None
    if "--version" in args:
        i = args.index("--version")
        ver = (args[i + 1], args[i + 2])
        del args[i:i + 3]
    reldiff, datamap, obin, nbin, files = args[0], args[1], args[2], args[3], args[4:]
    amap = Amap(reldiff, datamap, obin, nbin)
    oat, nat = image(obin), image(nbin)
    texts = {f: open(f).read() for f in files}
    seen, bad = {}, []

    def mp(a, where):
        n, how = amap(a)
        seen.setdefault(a, (n, how, set()))[2].add(where)
        if n is None:
            bad.append(f"{where}: {a:#x}: {how}")
        return n

    # the pinned byte lists: a name is its file's, else the one file's that pins it
    local, glob = {f: {} for f in files}, {}
    for f, t in texts.items():
        for m in re.finditer(r"Exe\.bytesAt (?:\w+\.)*zzs\.blob 0x([0-9a-f]+) (\d+) = some (\w+) :=", t):
            local[f][m[3]] = (int(m[1], 16), int(m[2]))
            glob.setdefault(m[3], set()).add((int(m[1], 16), int(m[2])))

    def pin(f, nm):
        if nm in local[f]:
            return local[f][nm]
        if re.search(r"[({]\s*(\w+\s+)*" + nm + r"(\s+\w+)*\s*:\s*List Byte", texts[f]):
            return None                              # the file's own variable of that name
        return next(iter(glob[nm])) if len(glob.get(nm, ())) == 1 else None
    out = {}
    for f, t in texts.items():
        # 2. the byte lists (before the addresses in the surrounding text change)
        def lst(m):
            nm = m[1]
            if nm not in local[f]:
                return m[0]
            a, n = local[f][nm]
            old = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-f]{2})\b", m[2]))
            if old != oat(a, n):
                bad.append(f"{f}: {nm}: the list is not the old file's {n} bytes at {a:#x}")
                return m[0]
            na = mp(a, f)
            if na is None:
                return m[0]
            b = nat(na, n)
            if "\n" not in m[2]:                     # a list written on one line stays on one line
                return f"def {nm} : List Byte := [" + ", ".join(f"0x{x:02x}" for x in b) + "]"
            rows = ["  " + ", ".join(f"0x{x:02x}" for x in b[i:i + 16]) for i in range(0, n, 16)]
            return f"def {nm} : List Byte := [\n" + ",\n".join(rows) + "]"
        t = re.sub(r"def (\w+) : List Byte := \[([^\]]*)\]", lst, t)
        for nm in local[f]:
            if not re.search(r"def " + nm + r" : List Byte := \[", t):
                bad.append(f"{f}: {nm}: pinned here, but its list is not found")

        # 3. relocated fields in decoding facts: where the instruction's bytes differ between the two files, a
        #    32-bit field (the last four bytes, or the four before an immediate) changed; a number of the fact
        #    that is the old field's value (zero- or sign-extended to 64 bits) becomes the new field's
        def dec(m):
            nm, k, body, ln = m[1], int(m[2]), m[3], int(m[4])
            if pin(f, nm) is None:
                return m[0]
            a = pin(f, nm)[0]
            na = mp(a, f)
            if na is None:
                return m[0]
            ob, nb = oat(a + k, ln), nat(na + k, ln)
            if ob == nb:
                return m[0]
            diff = [i for i in range(ln) if ob[i] != nb[i]]
            spans = [s0 for s0 in (ln - 4, ln - 5, ln - 8) if s0 >= 0]
            flds = [s0 for s0 in spans if any(s0 <= i < s0 + 4 for i in diff)]
            if not all(any(s0 <= i < s0 + 4 for s0 in flds) for i in diff):
                bad.append(f"{f}: {nm}+{k}: the bytes differ outside a 32-bit field")
                return m[0]
            sub, used = {}, set()
            for s0 in flds:
                for sx in (False, True):
                    o_ = int.from_bytes(ob[s0:s0 + 4], "little", signed=sx) % M64
                    n_ = int.from_bytes(nb[s0:s0 + 4], "little", signed=sx) % M64
                    if sub.setdefault(str(o_), str(n_)) != str(n_):
                        bad.append(f"{f}: {nm}+{k}: two fields with the value {o_}")

            def num(d):
                if d[0] in sub:
                    used.add(d[0])
                    return sub[d[0]]
                return d[0]
            body2 = re.sub(r"(?<![\w.])\d{2,}(?![\w.])", num, body)
            if not used:
                bad.append(f"{f}: {nm}+{k}: the bytes differ, but no number of the fact is a changed field's value")
            return f"Dec feat {nm} {k} ({body2} {ln})"
        t = re.sub(r"Dec feat (\w+) (\d+) \((FV7z\.mk .*?\]) (\d+)\)", dec, t)

        # 1. addresses
        def hexlit(m):
            a = int(m[1], 16)
            if not amap.lo <= a <= amap.hi and a != 0x400000:
                return m[0]
            n = mp(a, f)
            return m[0] if n is None else f"0x{n:x}"
        t = re.sub(r"(?<![\w.])0x([0-9a-fA-F]{6})(?![0-9a-fA-F_])", hexlit, t)

        def ident(m):
            n = mp(int(m[1], 16), f)
            return m[0] if n is None else f"r{n:x}"
        t = re.sub(r"\br([4-7][0-9a-f]{5})(?=_|\b)", ident, t)

        # 4. the release's name
        if ver:
            o, n = ver
            t = t.replace(o, n).replace(o.replace(".", ""), n.replace(".", ""))
        out[f] = t

    for a in sorted(seen):
        n, how, where = seen[a]
        print(f"{a:x}\t{'' if n is None else format(n, 'x')}\t{how}\t{len(where)} file(s)")
    changed = [f for f in files if out[f] != texts[f]]
    print(f"# {len(seen)} addresses, {sum(len(v) for v in local.values())} pinned lists, {len(changed)} of {len(files)} files change")
    for b in bad:
        print("UNMAPPED " + b)
    if write:
        for f in changed:
            open(f, "w").write(out[f])
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
