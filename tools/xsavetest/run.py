#!/usr/bin/env python3
"""Differential test of the model's XSAVE, XSAVEC and XRSTOR against this processor (PLAN.md §6.4, G1).

Generates cases (lean/Tools/XsaveTest.lean documents the format): instruction masks drawn from the components XCR0
enables (sometimes with bits outside it, outside the components the model handles, or in the ignored upper halves of
RAX and RDX), areas aligned and misaligned, inside the page and running into the unmapped page after it, register
state random or in its initial configuration (so that XINUSE is clear), and for XRSTOR areas with standard and
compacted headers, valid and not (header bits outside XCR0, reserved header bytes, MXCSR bits the processor lacks).
Runs them through the model (`lake exe xsavetest`) and natively (build/xsavetest-native, from native.c), and
compares: the page, the defined fields of the FXSAVE64 image of the state after (not its reserved bytes), ZMM0-ZMM31
and k0-k7. A model case `undef` (choices the model leaves open) gives the result of each pattern of its choices
(lean/Tools/XsaveTest.lean): the processor's must be one of them, or agree with two patterns P ⊆ Q on the bits they
agree on. For XSAVE and XSAVEC the model is given the processor's XINUSE as the XSTATE_BV it wrote. `nm` is counted.

Usage: run.py [-n CASES_PER_OP] [-s SEED] [--dump FILE]      (exit status 1 on any mismatch; FILE: each mismatch's
case, the model's line and the processor's, in full, with the processor's `native info`)
"""
import argparse, os, random, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OPS = ["xsave", "xsave64", "xsavec", "xsavec64", "xrstor", "xrstor64"]
HELD = 0xE7   # xInsnHeld

# the defined bytes of an FXSAVE64 image: FCW FSW FTW, FOP FIP FDP, MXCSR MXCSR_MASK, ST0-ST7 (10 of 16), XMM0-XMM15
LEG_DEF = bytearray(512)
for lo, hi in [(0, 5), (6, 32)] + [(32 + 16 * i, 42 + 16 * i) for i in range(8)] + [(160, 416)]:
    for o in range(lo, hi): LEG_DEF[o] = 0xFF

def rb(r, n, p_zero=0.0):
    return bytes(n) if r.random() < p_zero else bytes(r.getrandbits(8) for _ in range(n))

def subset(r, m):
    return sum(1 << i for i in range(64) if m >> i & 1 and r.random() < 0.6)

def legacy(r, mask, x87init, sseinit):
    b = bytearray(512)
    if not x87init:
        fcw = r.choice([0x37F, 0x27F, r.getrandbits(16)])
        b[0:2] = fcw.to_bytes(2, "little"); b[2:4] = r.choice([0, r.getrandbits(16)]).to_bytes(2, "little")
        b[4] = r.choice([0, 0xFF, r.getrandbits(8)])
        b[6:8] = (r.getrandbits(11)).to_bytes(2, "little"); b[8:24] = rb(r, 16, 0.3)
        # FIP and FDP as canonical 48-bit addresses: an Intel processor keeps bits 47-0 of a loaded FIP, an AMD
        # processor of a loaded FDP, sign-extended (as measured: Core i7-14650HX, EPYC 7763; the model loads all 64,
        # which an image FXSAVE or XSAVE stored never shows)
        for o in (8, 16):
            p = int.from_bytes(b[o:o + 8], "little") & (1 << 48) - 1
            b[o:o + 8] = (p | (0xFFFF << 48 if p >> 47 else 0)).to_bytes(8, "little")
        for i in range(8): b[32 + 16 * i:42 + 16 * i] = rb(r, 10, 0.2)
    else:
        b[0:2] = (0x37F).to_bytes(2, "little")
    mx = 0x1F80 if r.random() < 0.4 else r.getrandbits(16) & mask
    b[24:28] = mx.to_bytes(4, "little")
    if not sseinit:
        for j in range(16): b[160 + 16 * j:176 + 16 * j] = rb(r, 16, 0.2)
    return bytes(b)

def area(r, info, op, off, page):
    """For XRSTOR: write a header (standard or compacted) and a legacy region into the page at `off`."""
    xcr0 = info["xcr0"]
    if off % 64 or off + 576 > 4096: return
    leg = bytearray(legacy(r, info["mxcsrmask"], r.random() < 0.2, r.random() < 0.2))
    if r.random() < 0.05: leg[24:28] = (r.getrandbits(32) | 1 << 31).to_bytes(4, "little")   # an unsupported MXCSR bit
    hdr = bytearray(64)
    if r.random() < 0.5:   # compacted
        fmt = subset(r, xcr0 & HELD) | (r.choice([0, 1 << 1]) if r.random() < 0.1 else 0)
        bv = subset(r, fmt)
        if r.random() < 0.05: bv |= 1 << r.choice([0, 1, 2, 5])
        if r.random() < 0.05: fmt |= 1 << r.choice([3, 4, 8, 9, 17])
        hdr[8:16] = (fmt | 1 << 63).to_bytes(8, "little")
    else:
        bv = subset(r, xcr0 & HELD)
        if r.random() < 0.05: bv |= 1 << r.choice([3, 4, 8, 9, 17])
        if r.random() < 0.05: hdr[8 + r.randrange(16)] = r.randrange(1, 256)
    hdr[0:8] = bv.to_bytes(8, "little")
    if r.random() < 0.05: hdr[16 + r.randrange(48)] = r.randrange(1, 256)
    page[off:off + 512] = leg; page[off + 512:off + 576] = hdr

def case(r, op, info):
    xcr0 = info["xcr0"]
    m = r.choice([subset(r, xcr0 & HELD), xcr0 & HELD, 0xEE, 0xFFFFFFFFFFFFFFFF, 0, subset(r, xcr0)])
    if r.random() < 0.1: m |= 1 << r.choice([3, 4, 8, 9, 17, 18, 40, 63])
    rax = (r.getrandbits(32) << 32 if r.random() < 0.3 else 0) | (m & 0xFFFFFFFF)
    rdx = (r.getrandbits(32) << 32 if r.random() < 0.3 else 0) | (m >> 32)
    k = r.random()
    off = (64 * r.randrange(0, 24) if k < 0.6 else 64 * r.randrange(24, 64) if k < 0.9
           else 64 * r.randrange(0, 60) + r.randrange(1, 64))
    wide = info["wide"]
    x87init, sseinit = r.random() < 0.25, r.random() < 0.25
    leg = legacy(r, info["mxcsrmask"], x87init, sseinit)
    ymmh = rb(r, 256, 0.3)
    zmmh = rb(r, 512, 0.3) if wide else bytes(512)
    zhi = rb(r, 1024, 0.3) if wide else bytes(1024)
    kk = rb(r, 64, 0.3) if wide else bytes(64)
    page = bytearray(rb(r, 4096))
    if op.startswith("xrstor"): area(r, info, op, off, page)
    return " ".join([op, f"{rax:x}", f"{rdx:x}", f"{off:x}", leg.hex(), ymmh.hex(), zmmh.hex(), zhi.hex(), kk.hex(),
                     page.hex()])

def masked(fields):
    """The integers compared of an `ok` line: the page, the FXSAVE64 image's defined bytes, the vector registers."""
    page, leg, z, k = fields
    lg = bytes(a & b for a, b in zip(bytes.fromhex(leg), LEG_DEF))
    return [int(page, 16), int(lg.hex(), 16), int(z, 16), int(k, 16)]

def same(m, n):
    fm, fn = m.split(), n.split()
    if fm[0] != "ok" or fn[0] != "ok": return m == n
    return masked(fm[1:]) == masked(fn[1:])

def agrees(m, n):
    if not m.startswith("undef "): return same(m, n)
    rs = m[len("undef "):].split(" | ")
    if any(same(r, n) for r in rs): return True
    fn = n.split()
    if fn[0] != "ok": return False
    vn = masked(fn[1:])
    for p, a in enumerate(rs):
        for q, b in enumerate(rs):
            if p == q or q & p != p or not a.startswith("ok") or not b.startswith("ok"): continue
            va, vb = masked(a.split()[1:]), masked(b.split()[1:])
            if all((x ^ z) & ~(x ^ y) == 0 for x, y, z in zip(va, vb, vn)): return True
    return False

def hint(c, n):
    """The XINUSE the processor's XSAVE or XSAVEC of case c showed in its result n: the XSTATE_BV it wrote."""
    f, fn = c.split(), n.split()
    if not f[0].startswith(("xsave", "xsavec")) or fn[0] != "ok": return c
    off = int(f[3], 16)
    return c + " " + bytes.fromhex(fn[1])[off + 512:off + 520][::-1].hex()

def run(cmd, cases, cwd=None):
    p = subprocess.run(cmd, input="\n".join(cases) + "\n", capture_output=True, text=True, cwd=cwd, check=True)
    out = p.stdout.splitlines()
    assert len(out) == len(cases), (cmd, len(out), len(cases), p.stderr[-2000:])
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=150)
    ap.add_argument("-s", type=int, default=1)
    ap.add_argument("--dump")
    a = ap.parse_args()
    exe, src = os.path.join(ROOT, "build", "xsavetest-native"), os.path.join(ROOT, "tools", "xsavetest", "native.c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        os.makedirs(os.path.dirname(exe), exist_ok=True)
        subprocess.run(["gcc", "-O1", "-Wall", "-o", exe, src], check=True)
    words = subprocess.run([exe, "info"], capture_output=True, text=True, check=True).stdout.split()
    print("host:", " ".join(w for w in words if not w.startswith("d") or w.split("=")[1] != "0,0,0"))
    kv = dict(w.split("=", 1) for w in words)
    info = {"xcr0": int(kv["xcr0"], 16), "mxcsrmask": int(kv["mxcsrmask"], 16), "wide": kv["wide"] == "1"}
    r = random.Random(a.s)
    cases = [(op, case(r, op, info)) for op in OPS for _ in range(a.n)]
    native = run([exe], [c for _, c in cases])
    model = run(["lake", "exe", "xsavetest", *words], [hint(c, n) for (_, c), n in zip(cases, native)],
                cwd=os.path.join(ROOT, "lean"))
    stats, bad = {}, 0
    dump = open(a.dump, "w") if a.dump else None
    if dump: print("info " + " ".join(words), file=dump)
    for (op, c), m, n in zip(cases, model, native):
        s = stats.setdefault(op, {"ok": 0, "exc": 0, "undef": 0, "nm": 0, "diff": 0})
        if m.startswith("nm"):
            s["nm"] += 1
            if s["nm"] == 1: print(f"NM {op}: {m}")
            continue
        if agrees(m, n):
            s["undef" if m.startswith("undef") else "exc" if m.startswith("exc") else "ok"] += 1
        else:
            s["diff"] += 1; bad += 1
            if dump: print(f"case {c}\nmodel {m}\nnative {n}", file=dump)
            if s["diff"] <= 2:
                f = c.split()
                print(f"DIFF {op} rax={f[1]} rdx={f[2]} off={f[3]}\n  model  {m[:300]}\n  native {n[:300]}")
    print(f"{'op':<10} {'ok':>5} {'exc':>5} {'undef':>5} {'nm':>5} {'diff':>5}")
    for op in OPS:
        s = stats[op]; print(f"{op:<10} {s['ok']:>5} {s['exc']:>5} {s['undef']:>5} {s['nm']:>5} {s['diff']:>5}")
    print(f"{len(cases)} cases, {bad} mismatches")
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
