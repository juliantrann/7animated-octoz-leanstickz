#!/usr/bin/env python3
"""Differential test of the model's instruction semantics against this processor (PLAN.md §6.4, G1).

Generates cases for each instruction form below (register and memory operands; aligned, misaligned and past-the-end
memory offsets; random and edge values; for VEX forms both vector lengths, and encodings the manuals make #UD), runs
them through the model (`lake exe difftest`, lean/Tools/DiffTest.lean) and natively (build/difftest-native,
tools/difftest/native.c), and compares. A case the model calls `undef` (a value the manuals leave undefined) is compared
on the bits its two runs (every undefined value all zeros, all ones) agree on; `nm` (not modelled) is counted, not
compared.

Usage: run.py [-n CASES_PER_FORM] [-s SEED] [FORM...]      (exit status 1 on any mismatch)
"""
import argparse, os, random, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def L(*a): return ("leg", list(a))
def V(mm, op, l, w=0, pp=1): return ("vex", mm, op, l, w, pp)

# name -> (encoding, options). Legacy: prefix and opcode bytes. VEX: map (1 0F, 2 0F38, 3 0F3A), opcode, L, W, pp
# (1: 66). Options: nds (VEX.vvvv is the first source), ext (ModRM.reg is an opcode extension and VEX.vvvv the
# destination), imm (an 8-bit immediate; a list: the values to draw from, else edge and random values), mem ("any",
# "only", "never"), gpr (ModRM.reg and a register r/m are general registers: rcx or rdx, which the harness sets and compares; rax
# holds the buffer's address, which differs between the two sides), bare (no
# ModRM), rcx (the
# values to draw RCX from; None: random).
FORMS = {
    # G1 batch 1
    "ptest":        (L(0x66, 0x0F, 0x38, 0x17), {}),
    "pmaxud":       (L(0x66, 0x0F, 0x38, 0x3F), {}),
    "lddqu":        (L(0xF2, 0x0F, 0xF0), {"mem": "only"}),
    "lddqu.reg":    (L(0xF2, 0x0F, 0xF0), {"mem": "never"}),
    # G1 batch 2: AES-NI, SHA-1
    "aesenc":       (L(0x66, 0x0F, 0x38, 0xDC), {}),
    "aesenclast":   (L(0x66, 0x0F, 0x38, 0xDD), {}),
    "aesdec":       (L(0x66, 0x0F, 0x38, 0xDE), {}),
    "aesdeclast":   (L(0x66, 0x0F, 0x38, 0xDF), {}),
    "sha1rnds4":    (L(0x0F, 0x3A, 0xCC), {"imm": [0, 1, 2, 3, 4, 0xFF]}),
    "sha1nexte":    (L(0x0F, 0x38, 0xC8), {}),
    "sha1msg1":     (L(0x0F, 0x38, 0xC9), {}),
    "sha1msg2":     (L(0x0F, 0x38, 0xCA), {}),
    # G1 batch 2: VEX
    "vaesenc.128":  (V(2, 0xDC, 0), {"nds": True}),
    "vaesenc.256":  (V(2, 0xDC, 1), {"nds": True}),
    "vaesenclast.256": (V(2, 0xDD, 1), {"nds": True}),
    "vaesdec.256":  (V(2, 0xDE, 1), {"nds": True}),
    "vaesdeclast.256": (V(2, 0xDF, 1), {"nds": True}),
    "vaesdeclast.128": (V(2, 0xDF, 0), {"nds": True}),
    "vpunpckldq.128": (V(1, 0x62, 0), {"nds": True}),
    "vpunpckldq.256": (V(1, 0x62, 1), {"nds": True}),
    "vpunpckhdq.256": (V(1, 0x6A, 1), {"nds": True}),
    "vpshufd.128":  (V(1, 0x70, 0), {"imm": None}),
    "vpshufd.256":  (V(1, 0x70, 1), {"imm": None}),
    "vpsrldq.256":  (V(1, 0x73, 1), {"ext": 3, "imm": [0, 1, 4, 8, 15, 16, 17, 0xFF], "mem": "never"}),
    "vpslldq.128":  (V(1, 0x73, 0), {"ext": 7, "imm": [0, 1, 4, 8, 15, 16, 17, 0xFF], "mem": "never"}),
    "vpslldq.256":  (V(1, 0x73, 1), {"ext": 7, "imm": [0, 1, 4, 8, 15, 16, 17, 0xFF], "mem": "never"}),
    "vpalignr.128": (V(3, 0x0F, 0), {"nds": True, "imm": [0, 1, 4, 8, 15, 16, 17, 31, 32, 0xFF]}),
    "vpalignr.256": (V(3, 0x0F, 1), {"nds": True, "imm": [0, 1, 4, 8, 15, 16, 17, 31, 32, 0xFF]}),
    "vperm2i128":   (V(3, 0x46, 1), {"nds": True, "imm": None}),
    "vperm2i128.L0": (V(3, 0x46, 0), {"nds": True, "imm": None}),
    "vperm2i128.W1": (V(3, 0x46, 1, 1), {"nds": True, "imm": None}),
    "vbroadcasti128": (V(2, 0x5A, 1), {"mem": "only"}),
    "vbroadcasti128.reg": (V(2, 0x5A, 1), {"mem": "never"}),
    "vbroadcasti128.L0": (V(2, 0x5A, 0), {"mem": "only"}),
    "vptest.128":   (V(2, 0x17, 0), {}),
    "vptest.256":   (V(2, 0x17, 1), {}),
    "vpcmpistri":   (V(3, 0x63, 0), {"imm": None}),
    "vpcmpistri.L1": (V(3, 0x63, 1), {"imm": None}),
    # G1 batch 2: shifts of memory by CL, by 0 (`zeroCountMem`) and by other counts
    "shr.m32.cl":   (L(0xD3), {"ext": 5, "mem": "only", "rcx": [0, 32, 64, 1, 7, 31, None]}),
    "shl.m32.cl":   (L(0xD3), {"ext": 4, "mem": "only", "rcx": [0, 32, 64, 1, 7, 31, None]}),
    "ror.m64.cl":   (L(0x48, 0xD3), {"ext": 1, "mem": "only", "rcx": [0, 64, 1, 63, None]}),
    "shrd.m32.cl":  (L(0x0F, 0xAD), {"mem": "only", "gpr": True, "rcx": [0, 32, 1, 31, None]}),
    # G1 batch 2: POPCNT, PAUSE
    "popcnt.32":    (L(0xF3, 0x0F, 0xB8), {"gpr": True}),
    "popcnt.64":    (L(0xF3, 0x48, 0x0F, 0xB8), {"gpr": True}),
    "popcnt.16":    (L(0x66, 0xF3, 0x0F, 0xB8), {"gpr": True}),
    "pause":        (L(0xF3, 0x90), {"bare": True}),
    # G1 batch 3: RTM outside a transaction (#UD without RTM), INCSSPQ without a shadow stack
    "xabort":       (L(0xC6, 0xF8), {"bare": True, "imm": None}),
    "xabort.lock":  (L(0xF0, 0xC6, 0xF8), {"bare": True, "imm": None}),
    "xend":         (L(0x0F, 0x01, 0xD5), {"bare": True}),
    "xend.lock":    (L(0xF0, 0x0F, 0x01, 0xD5), {"bare": True}),
    "xbegin":       (L(0xC7, 0xF8, 0, 0, 0, 0), {"bare": True}),
    "xbegin.lock":  (L(0xF0, 0xC7, 0xF8, 0, 0, 0, 0), {"bare": True}),
    "incsspq":      (L(0xF3, 0x48, 0x0F, 0xAE), {"ext": 5, "mem": "never", "gpr": True}),
    "incsspd":      (L(0xF3, 0x0F, 0xAE), {"ext": 5, "mem": "never", "gpr": True}),
    # G1 batch 3: 0F 1A/1B on a processor without MPX (glibc's `_dl_runtime_profile_*` has BNDMOV, 66 0F 1A/1B)
    "bndmov.1a":    (L(0x66, 0x0F, 0x1A), {}),
    "bndmov.1b":    (L(0x66, 0x0F, 0x1B), {}),
    "bndmov.1b.rex": (L(0x66, 0x4D, 0x0F, 0x1B), {}),
    "bndmov.67":    (L(0x67, 0x66, 0x0F, 0x1A), {}),
    "bndmov.lock":  (L(0xF0, 0x66, 0x0F, 0x1B), {"mem": "only"}),
    "bndldx":       (L(0x0F, 0x1A), {}),
    "bndstx":       (L(0x0F, 0x1B), {}),
    "bndcl":        (L(0xF3, 0x0F, 0x1A), {}),
    "bndmk":        (L(0xF3, 0x0F, 0x1B), {}),
    "bndcu":        (L(0xF2, 0x0F, 0x1A), {}),
    "bndcn":        (L(0xF2, 0x48, 0x0F, 0x1B), {}),
    # controls: already in the model
    "pminud":       (L(0x66, 0x0F, 0x38, 0x3B), {}),
    "pshufb":       (L(0x66, 0x0F, 0x38, 0x00), {}),
    "pcmpistri":    (L(0x66, 0x0F, 0x3A, 0x63), {"imm": None}),
    "movdqa":       (L(0x66, 0x0F, 0x6F), {}),
    "sha256msg1":   (L(0x0F, 0x38, 0xCC), {}),
    "vpunpcklqdq.256": (V(1, 0x6C, 1), {"nds": True}),
    "vpshufb.256":  (V(2, 0x00, 1), {"nds": True}),
}

EDGE32 = [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE]
IMMS = [0x00, 0x01, 0x08, 0x0C, 0x18, 0x1A, 0x40, 0x48, 0x38, 0x80, 0x88, 0x20, 0x31, 0x13, 0x02]

def vec128(r):
    k = r.randrange(6)
    if k == 0: return 0
    if k == 1: return (1 << 128) - 1
    if k == 2: return sum(r.choice(EDGE32) << (32 * i) for i in range(4))
    if k == 3:   # bytes with zeros and repeats (string instructions, compares)
        return sum(r.choice([0, 0x41, 0x42, 0x61, 0xFF, r.randrange(256)]) << (8 * i) for i in range(16))
    return r.getrandbits(128)

def vec(r): return vec128(r) << 128 | vec128(r)

def encode(enc, reg, rm_byte_tail, vvvv):
    if enc[0] == "leg":
        return enc[1] + rm_byte_tail(reg)
    _, mm, op, l, w, pp = enc
    return [0xC4, 0xE0 | mm, w << 7 | (~vvvv & 0xF) << 3 | l << 2 | pp, op] + rm_byte_tail(reg)

def case(r, form):
    enc, o = FORMS[form]
    mem_mode = o.get("mem", "any")
    xs = [vec(r) for _ in range(8)]
    m = bytearray(r.getrandbits(8) for _ in range(64))
    if r.random() < 0.15:   # related operands: equal, complementary, zero (PTEST's ZF/CF)
        a, b = r.randrange(8), r.randrange(8)
        xs[b] = r.choice([xs[a], ~xs[a] & ((1 << 256) - 1), 0])
    reg = o["ext"] if "ext" in o else r.choice([1, 2]) if o.get("gpr") else r.randrange(8)
    vvvv = r.randrange(8) if (o.get("nds") or "ext" in o) else 0
    off = 0
    use_mem = mem_mode == "only" or (mem_mode == "any" and r.random() < 0.5)
    if use_mem:
        off = r.choice([0, 0, 16, 32, r.randrange(1, 16), r.randrange(17, 48), r.randrange(33, 64)])
        disp = r.choice([0, 0, 0, 8, 16])
        if r.random() < 0.15 and off + disp + 32 <= 64:   # the memory operand related to a register
            m[off + disp:off + disp + 32] = xs[r.randrange(8)].to_bytes(32, "little")
        tail = lambda g: [0x40 | g << 3, disp]   # [rax + disp8]
    else:
        rm = r.choice([1, 2]) if o.get("gpr") else r.randrange(8)
        tail = lambda g: [0xC0 | g << 3 | rm]
    b = encode(enc, reg, (lambda g: []) if o.get("bare") else tail, vvvv)
    if "imm" in o:
        b += [r.choice(o["imm"]) if o["imm"] else r.choice(IMMS + [r.randrange(256)])]
    fl = r.choice([0, 0x8D5, r.getrandbits(12) & 0x8D5])
    rcx, rdx = r.getrandbits(64), r.choice([r.getrandbits(64), r.randrange(17), 16])
    if "rcx" in o:
        rcx = r.choice(o["rcx"])
        if rcx is None: rcx = r.getrandbits(64)
    return (bytes(b).hex() + f" {off:x} {rcx:x} {rdx:x} {fl:x} " + " ".join(f"{x:064x}" for x in xs)
            + " " + bytes(m).hex())

def agrees(m, n):
    """Whether native line `n` matches model line `undef OK0 | OK1` on every bit OK0 and OK1 agree on."""
    a, b = m[len("undef "):].split(" | ")
    fa, fb, fn = a.split(), b.split(), n.split()
    if fb[0] != "ok" or fn[0] != "ok" or len(fa) != len(fn) or len(fb) != len(fn):
        return False
    return all((int(x, 16) ^ int(z, 16)) & ~(int(x, 16) ^ int(y, 16)) == 0 for x, y, z in zip(fa[1:], fb[1:], fn[1:]))

def run(cmd, cases, cwd=None):
    p = subprocess.run(cmd, input="\n".join(cases) + "\n", capture_output=True, text=True, cwd=cwd, check=True)
    out = p.stdout.splitlines()
    assert len(out) == len(cases), (cmd, len(out), len(cases), p.stderr[-2000:])
    return out

# Features' fields (lean/Tools/DiffTest.lean, featOf) and the /proc/cpuinfo flag of each (Linux shows a flag only
# when the kernel enables it: avx needs OSXSAVE, pku OSPKE)
CPU_FLAGS = {"ssse3": "ssse3", "sse41": "sse4_1", "sha": "sha_ni", "bmi1": "bmi1", "lzcnt": "abm", "avx": "avx",
             "avx512f": "avx512f", "apx": "apx_f", "pku": "ospke", "nx": "nx", "la57": "la57", "sse42": "sse4_2",
             "bmi2": "bmi2", "avx2": "avx2", "avx512bw": "avx512bw", "avx512dq": "avx512dq", "avx512vl": "avx512vl",
             "movbe": "movbe", "rdtscp": "rdtscp", "sse3": "pni", "fma": "fma", "cetSs": "user_shstk", "rtm": "rtm",
             "hle": "hle", "aes": "aes", "vaes": "vaes", "popcnt": "popcnt", "mpx": "mpx"}

def host_features():
    """The arguments of `lake exe difftest`: `amd` on an AMD processor, then the Features fields it has."""
    flags, vendor = set(), ""
    with open("/proc/cpuinfo") as f:
        for l in f:
            if l.startswith("vendor_id") and not vendor:
                vendor = l.split(":", 1)[1].strip()
            if l.startswith("flags"):
                flags = set(l.split(":", 1)[1].split()); break
    if vendor not in ("GenuineIntel", "AuthenticAMD"): sys.exit(f"vendor {vendor!r}: the model knows Intel and AMD")
    return (["amd"] if vendor == "AuthenticAMD" else []) + sorted(k for k, v in CPU_FLAGS.items() if v in flags)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=400)
    ap.add_argument("-s", type=int, default=1)
    ap.add_argument("forms", nargs="*")
    a = ap.parse_args()
    forms = a.forms or list(FORMS)
    r = random.Random(a.s)
    cases = [(f, case(r, f)) for f in forms for _ in range(a.n)]
    feats = host_features()
    if "avx" not in feats: sys.exit("the native side loads and stores YMM registers: needs AVX")
    exe, src = os.path.join(ROOT, "build", "difftest-native"), os.path.join(ROOT, "tools", "difftest", "native.c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):   # (re)build the native side
        os.makedirs(os.path.dirname(exe), exist_ok=True)
        subprocess.run(["gcc", "-O1", "-Wall", "-o", exe, src], check=True)
    # `Features.rtm` is "the processor implements RTM", which CPUID may not report (`IA32_TSX_CTRL.TSX_CPUID_CLEAR`,
    # a hypervisor's mask; Spec/Profile.lean): XABORT outside a transaction is a no-op with RTM and #UD without, so
    # the processor is asked, not /proc/cpuinfo
    if "rtm" not in feats and run([exe], [case(random.Random(0), "xabort")])[0].startswith("ok"):
        feats = sorted(feats + ["rtm"], key=lambda k: (k != "amd", k))
        print("rtm: not in /proc/cpuinfo, XABORT runs: the processor implements it")
    print("host features:", " ".join(feats))
    model = run(["lake", "exe", "difftest", *feats], [c for _, c in cases], cwd=os.path.join(ROOT, "lean"))
    native = run([exe], [c for _, c in cases])
    stats, bad = {}, 0
    for (f, c), m, n in zip(cases, model, native):
        s = stats.setdefault(f, {"ok": 0, "exc": 0, "undef": 0, "nm": 0, "diff": 0})
        if m.startswith("nm"):
            s["nm"] += 1
            if s["nm"] == 1: print(f"NM {f}: {m}")
            continue
        same = agrees(m, n) if m.startswith("undef") else m == n
        if same:
            s["undef" if m.startswith("undef") else "exc" if m.startswith("exc") else "ok"] += 1
        else:
            s["diff"] += 1; bad += 1
            if s["diff"] <= 3:
                print(f"DIFF {f}\n  case   {c}\n  model  {m}\n  native {n}")
    print(f"{'form':<20} {'ok':>5} {'exc':>5} {'undef':>5} {'nm':>5} {'diff':>5}")
    for f in forms:
        s = stats[f]; print(f"{f:<20} {s['ok']:>5} {s['exc']:>5} {s['undef']:>5} {s['nm']:>5} {s['diff']:>5}")
    print(f"{len(cases)} cases, {bad} mismatches")
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
