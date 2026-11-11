#!/usr/bin/env python3
"""Function inventory of a stripped static ELF: one line per function, from its .eh_frame FDEs, plus the code no FDE
describes.

Output (TSV): start_hex  size  kind  section
  kind = fde      a function described by an FDE (compiler output: C, C++, glibc, libstdc++)
         asmsec   a whole section of hand-written assembly without CFI (7-Zip's `.text$...` sections)
         nofde    a run of instructions outside every FDE and `.text$...` section, ended by alignment padding
                  (needs INSNS.TSV): 7-Zip's other assembly modules (`Asm/x86/*.asm`, assembled without CFI),
                  crtbegin, `.init`, `.plt`, `.fini`, glibc stubs without CFI. A run may hold several functions
                  that follow each other without padding, or a function and its unpadded neighbour.
Usage: ehframe_funcs.py BINARY [INSNS.TSV] > funcs.tsv   (needs binutils' readelf; INSNS.TSV is objdump's
       instructions as `address length mnemonic text`, made by tools/g0.sh)
"""
import bisect, re, subprocess, sys

def is_pad(m):
    """Alignment padding: any NOP form (`nop`, `nopw`, `data16 cs nopw`, `xchg %ax,%ax`), `int3`."""
    w = m.split()
    return not w or w[0] in ("int3", "(bad)") or any(x.startswith("nop") for x in w) or m == "xchg %ax,%ax"

def main(path, insns_path=None):
    secs = []
    for l in subprocess.run(["readelf", "-S", "-W", path], capture_output=True, text=True, check=True).stdout.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)\s+\S+\s+(\S*X\S*)", l)
        if m:
            secs.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16)))
    fdes = []
    out = subprocess.run(["readelf", "--debug-dump=frames", path], capture_output=True, text=True, check=True).stdout
    for m in re.finditer(r"FDE cie=[0-9a-f]+ pc=([0-9a-f]+)\.\.([0-9a-f]+)", out):
        a, b = int(m.group(1), 16), int(m.group(2), 16)
        if b > a:
            fdes.append((a, b - a))
    fdes = sorted(set(fdes))
    def sec_of(a):
        for n, s, z in secs:
            if s <= a < s + z:
                return n
        return "?"
    rows = [(a, n, "fde", sec_of(a)) for a, n in fdes]
    for n, s, z in secs:
        if n.startswith(".text$") and not any(s <= a < s + z for a, _ in fdes):
            rows.append((s, z, "asmsec", n))
    if insns_path:
        covered = sorted((a, a + n) for a, n, _, _ in rows)
        starts = [a for a, _ in covered]
        def inside(a):
            i = bisect.bisect_right(starts, a) - 1
            return i >= 0 and a < covered[i][1]
        run = None
        for l in open(insns_path):
            a, n, _, m = l.rstrip("\n").split("\t")[:4]
            a, n = int(a, 16), int(n)
            if inside(a) or is_pad(m) or (run and sec_of(a) != run[2]):
                if run:
                    rows.append((run[0], run[1] - run[0], "nofde", run[2]))
                    run = None
                if inside(a) or is_pad(m):
                    continue
            if run:
                run[1] = a + n
            else:
                run = [a, a + n, sec_of(a)]
        if run:
            rows.append((run[0], run[1] - run[0], "nofde", run[2]))
    for a, n, k, s in sorted(rows):
        print(f"{a:x}\t{n}\t{k}\t{s}")

if __name__ == "__main__":
    main(*sys.argv[1:3])
