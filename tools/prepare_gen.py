#!/usr/bin/env python3
"""Generate lean/FV7z/Prepare/Code.lean and Decode.lean (PLAN.md G2, 7-Zip).

For each function in FNS: its bytes in 7zzs 26.06 (`def`, pinned to the file by `decide +kernel`) and, at each
instruction's offset, what Zellic's decoder makes of them (`Dec`, by `rfl`), from the decoder's own output
(`lake exe decshow`).

Usage (from lean/):  python3 -I ../tools/prepare_gen.py DECDIR FV7z/Prepare [Prepare|CpuFeat]
The group (default `Prepare`) picks the functions and the namespace (`FV7z.<group>`). DECDIR holds `<name>.txt` from `lake exe decshow ../release/26.06/7zzs <hex addr> <len>`; missing ones are made.
"""
import os, re, subprocess, sys

FNS = [("cpuid", "z7_x86_cpuid", 0x424290, 24), ("maxf", "z7_x86_cpuid_GetMaxFunc", 0x4242b0, 56),
       ("sse41", "CPU_IsSupported_SSE41", 0x424390, 73), ("avx", "CPU_IsSupported_AVX", 0x424440, 101),
       ("avx2", "CPU_IsSupported_AVX2", 0x4244b0, 104), ("lz", "LzFindPrepare", 0x427de0, 77),
       ("ssse3", "CPU_IsSupported_SSSE3", 0x424340, 73), ("aes", "CPU_IsSupported_AES", 0x4242f0, 73),
       ("swap", "z7_SwapBytesPrepare", 0x43d3d0, 67),
       ("sha", "CPU_IsSupported_SHA", 0x4243e0, 89), ("sha1p", "Sha1Prepare", 0x43a740, 69),
       ("sha256p", "Sha256Prepare", 0x43b3e0, 69), ("b2s", "z7_Black2sp_Prepare", 0x422a20, 161),
       ("vaes", "CPU_IsSupported_VAES_AVX2", 0x4245a0, 113), ("aesg", "AesGenTables", 0x41e540, 617)]

# glibc 2.31's `get_common_indices`, with `update_usable` inlined (`sysdeps/x86/cpu-features.c`), in `7zzs`.
CPUFEAT = [("gci", "get_common_indices", 0x612cc0, 896),
           ("icf", "init_cpu_features", 0x613113, 0x165),
           ("icfk", "init_cpu_features", 0x613592, 0xac),
           ("tgv", "__tunable_get_val", 0x66f3a0, 0x6d),
           ("icfa", "init_cpu_features", 0x6132ad, 0xef),
           ("icfh", "init_cpu_features", 0x613803, 0x54),
           ("icfi", "init_cpu_features", 0x613676, 0x176),
           # `apply_irel` (`csu/libc-start.c`, `ARCH_SETUP_IREL`), inlined in `__libc_start_main`
           ("irl", "apply_irel", 0x613278, 53)]


def op(o):
    o = re.sub(r'\s+', ' ', o.strip())
    m = re.fullmatch(r'reg \{ w(\d+), n(\d+), ?\}', o)
    if m: return f"gr {m[1]} {m[2]}"
    m = re.fullmatch(r'reg \{ w8, n(\d+), high8 := true \}', o)
    if m: return f"gh {m[1]}"
    m = re.fullmatch(r'imm (\d+) (\d+)', o)
    if m: return f".imm {m[1]} {m[2]}"
    m = re.fullmatch(r'rel (\d+)', o)
    if m: return f".rel {m[1]}"
    m = re.fullmatch(r'mem \{ seg := none, base := some (\d+), index := none, scale := 1, disp := (\d+), '
                     r'ripRel := false, addr32 := false, w(\d+) \}', o)
    if m: return f".mem (mbd {m[1]} {m[2]} {m[3]})"
    m = re.fullmatch(r'mem \{ seg := none, base := some (\d+), index := some (\d+), scale := 1, disp := (\d+), '
                     r'ripRel := false, addr32 := false, w(\d+) \}', o)
    if m: return f".mem (mbi {m[1]} {m[2]} {m[3]} {m[4]})"
    m = re.fullmatch(r'mem \{ seg := some \(Seg.fs\), base := none, index := none, scale := 1, disp := (\d+), '
                     r'ripRel := false, addr32 := false, w(\d+) \}', o)
    if m: return f".mem (mfs {m[1]} {m[2]})"
    m = re.fullmatch(r'mem \{ seg := none, base := none, index := none, scale := 1, disp := (\d+), '
                     r'ripRel := true, addr32 := false, w(\d+) \}', o)
    if m: return f".mem (mrip {m[1]} {m[2]})"
    m = re.fullmatch(r'mem \{ seg := none, base := (none|some \d+), index := (none|some \d+), scale := (\d+), '
                     r'disp := (\d+), ripRel := false, addr32 := false, w(\d+) \}', o)
    if m: return (f".mem {{ seg := none, base := {m[1]}, index := {m[2]}, scale := {m[3]}, disp := {m[4]}, "
                  f"ripRel := false, addr32 := false, width := {m[5]} }}")
    raise Exception(o)


def main():
    S, out = sys.argv[1], sys.argv[2]
    grp = sys.argv[3] if len(sys.argv) > 3 else "Prepare"
    fns = {"Prepare": FNS, "CpuFeat": CPUFEAT}[grp]
    os.makedirs(S, exist_ok=True)
    code, dec = [], []
    for nm, cn, a, n in fns:
        p = f"{S}/{nm}.txt"
        if not os.path.exists(p):
            r = subprocess.run(["lake", "exe", "decshow", "../release/26.06/7zzs", f"{a:x}", str(n)],
                               capture_output=True, text=True, check=True)
            open(p, "w").write(r.stdout)
        t = open(p).read()
        bs = re.search(r'bytes \w+ \d+: \[([^\]]*)\]', t)[1].split(', ')[:n]
        assert len(bs) == n
        rows = ["  " + ", ".join(bs[i:i + 16]) for i in range(0, n, 16)]
        code.append(f"/-- `{cn}`, `{a:#x}` to `{a+n-1:#x}` of `7zzs`. -/\ndef {nm} : List Byte := [\n"
                    + ",\n".join(rows) + "]\n\n"
                    f"theorem {nm}_pin : Exe.bytesAt V2606.zzs.blob {a:#x} {n} = some {nm} := by decide +kernel\n"
                    f"theorem {nm}_length : {nm}.length = {n} := rfl\n")
        for b in re.split(r'\n(?=\d+ \()', t)[1:]:
            b = re.sub(r'ZellicX86\.Decode\.(Opd\.|Mn\.)?', '', b); b = re.sub(r'\s+', ' ', b)
            b = re.sub(r'rep := none, lock := false, mask := none, zero := false, fop := 0 ', '', b)
            b = b.replace('high8 := false', '').replace('width := ', 'w').replace('num := ', 'n')
            m = re.match(r'(\d+) \(\w+\): \{ mn := ([^,]+), opsz := (\d+), ops := \[(.*)\], len := (\d+), \}', b)
            if not m: raise Exception(b)
            off, mn, sz, ops, ln = m.groups()
            if int(off) >= n or mn == 'nop': continue
            mn = mn.strip()
            mnl = f"(.{mn})" if ' ' in mn else f".{mn}"
            ol = [op(x) for x in re.split(r',\s*(?=(?:reg|imm|rel|mem) )', ops)] if ops.strip() else []
            dec.append(f"theorem {nm}_{off} : ∀ feat, Dec feat {nm} {off} "
                       f"(FV7z.mk {mnl} {sz} [{', '.join(ol)}] {ln}) := by dec_rfl")
        dec.append("")
    code_doc = CODE_DOC if grp == "Prepare" else CF_CODE_DOC
    dec_doc = DEC_DOC if grp == "Prepare" else CF_DEC_DOC
    open(out + "/Code.lean", "w").write("""import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Lemmas.InsFn
/-!""" + code_doc + """-/
namespace FV7z.""" + grp + """
set_option maxRecDepth 20000
open ZellicX86

""" + "\n".join(code) + "\nend FV7z." + grp + "\n")
    open(out + "/Decode.lean", "w").write("""import FV7z.""" + grp + """.Code
import FV7z.Lemmas.Leaf
/-!""" + dec_doc + """-/
namespace FV7z.""" + grp + """
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

""" + "\n".join(dec) + "\nend FV7z." + grp + "\n")


CODE_DOC = """
# The code of 7-Zip's CPU feature tests and `*Prepare` functions in `7zzs` (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

The bytes of `C/CpuArch.c`'s `z7_x86_cpuid`, `z7_x86_cpuid_GetMaxFunc`, `CPU_IsSupported_SSE41`, `CPU_IsSupported_AVX`,
`CPU_IsSupported_AVX2`, `CPU_IsSupported_SSSE3`, `CPU_IsSupported_AES`, `CPU_IsSupported_SHA`,
`CPU_IsSupported_VAES_AVX2`, `C/Aes.c`'s `AesGenTables`, `C/LzFind.c`'s
`LzFindPrepare`, `C/SwapBytes.c`'s `z7_SwapBytesPrepare`, `C/Sha1.c`'s `Sha1Prepare`, `C/Sha256.c`'s
`Sha256Prepare` and `C/Blake2s.c`'s `z7_Black2sp_Prepare` (`objdump -d`), as lists, and the fact that they are the
file's (`*_pin`, by the kernel's evaluation of Zellic's ELF reader). Generated by `tools/prepare_gen.py`.
"""

DEC_DOC = """
# What the instructions of 7-Zip's CPU feature tests and `*Prepare` functions decode to (PLAN.md G2, 7-Zip)

At each instruction's offset, on every processor, the instruction Zellic's decoder makes of the bytes, whatever bytes
follow the code (`Leaf.Dec`), by evaluation. Generated from the decoder's own output (`decshow`) by
`tools/prepare_gen.py`; the padding after each function's last instruction is never run.
"""

CF_CODE_DOC = """
# The code of glibc 2.31's `init_cpu_features` in `7zzs` (PLAN.md G2, "Dispatch theo CPUID", glibc)

The bytes of `sysdeps/x86/cpu-features.c`'s `get_common_indices`, with `update_usable` inlined, two pieces of
`init_cpu_features` (`0x613113` to `0x613277`, the part every vendor runs, and `0x613592` to `0x61363d`, the part for
Intel's kind) and `elf/dl-tunables.c`'s `__tunable_get_val` (`objdump -d`), as lists, and the fact that they are the
file's (`*_pin`, by the kernel's evaluation of Zellic's ELF reader). Generated by `tools/prepare_gen.py`.
"""

CF_DEC_DOC = """
# What the instructions of glibc 2.31's `init_cpu_features` in `7zzs` decode to (PLAN.md G2, glibc)

At each instruction's offset, on every processor, the instruction Zellic's decoder makes of the bytes, whatever bytes
follow the code (`Leaf.Dec`), by evaluation. Generated from the decoder's own output (`decshow`) by
`tools/prepare_gen.py`.
"""


main()
