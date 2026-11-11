#!/usr/bin/env python3
"""CODEMAP.md of a release binary (G0, PLAN.md §8): its regions, its functions by origin, and the model's coverage.

Inputs are the G0 artefacts of tools/g0.sh and tools/libmatch.py; the regions and the assembly modules are read off
them (see ANCHORS) and are rechecked here against the inputs, so a new release that moves them fails loudly.
Usage: codemap.py NAME > CODEMAP.md        e.g. codemap.py 7zzs (reads build/7zzs.*)
"""
import collections, os, subprocess, sys

# 7zzs 26.06. `main` and `__libc_start_main` are the arguments of `_start` (the ELF entry); the end of 7-Zip's
# objects is the first function libmatch names after them (libpthread's `free_stacks`, 0x5f8ff0). The assembly
# modules are 7-Zip's Asm/x86/*.asm (USE_ASM=1 in CPP/7zip/7zip_gcc.mak), assembled without CFI, so `nofde` runs;
# each is recognised by its instructions (AES-NI, SHA-NI, the CRC table loops, the cmov heap sort of Sort.asm).
ANCHORS = {
    "7zzs": dict(
        entry=0x41d350, main=0x41cd90, libc_start_main=0x613040, seven_end=0x5f8ff0,
        asm={  # start of the module's first run, its end, module
            (0x41d670, 0x41d852): "Asm/x86/7zCrcOpt.asm",
            (0x41e990, 0x41f2e3): "Asm/x86/AesOpt.asm",
            (0x43a790, 0x43a9e3): "Asm/x86/Sha1Opt.asm",
            (0x43b430, 0x43b75a): "Asm/x86/Sha256Opt.asm",
            (0x43cda0, 0x43d0da): "Asm/x86/Sort.asm",
            (0x443f00, 0x444034): "Asm/x86/XzCrc64Opt.asm",
            (0x6d4040, 0x6d52af): "Asm/x86/LzmaDecOpt.asm (.text$LZMADECOPT)",
            (0x6d52c0, 0x6d5665): "Asm/x86/LzFindOpt.asm (.text$LZFINDOPT)",
        },
        guess={},  # 7-Zip C functions named by what they do, until the rebuild names them: none left
        crt={(0x41d350, 0x41d475): "crt1.o, crti.o, crtbeginT.o (_start, deregister_tm_clones, frame_dummy)"},
    )
}

def rows(path, skip_header=False):
    with open(path) as f:
        for i, l in enumerate(f):
            if (skip_header and i == 0) or l.startswith("#"):
                continue
            yield l.rstrip("\n").split("\t")

def main(name):
    A = ANCHORS[name]
    b = f"build/{name}"
    fns = [(int(r[0], 16), int(r[1]), r[2], r[3]) for r in rows(f"{b}.funcs.tsv")]
    names = {int(r[0], 16): (r[2], r[3], r[4]) for r in rows(f"{b}.names.lib.tsv")}
    # 7-Zip's own functions, named from the GCC 9.4 rebuild (tools/rebuild_focal.sh), if it was made
    names7 = {}
    if os.path.exists(f"{b}.names.7zip.tsv"):
        r7 = list(rows(f"{b}.names.7zip.tsv"))
        syms = [r[4].split(",")[0] for r in r7]
        dem = subprocess.run(["c++filt"], input="\n".join(syms), capture_output=True, text=True, check=True).stdout.split("\n")
        for r, d, raw in zip(r7, dem, (r[4] for r in r7)):
            more = raw.count(",")
            names7[int(r[0], 16)] = (r[3].split(";")[0], d + (f" (+{more} cùng byte)" if more else ""))
    cov = {s: {int(r[0], 16): (int(r[4]), int(r[5]), r[6] if len(r) > 6 else "") for r in rows(f"{b}.insncov.{s}", True)}
           for s in ("full", "min")}
    insns = sum(1 for _ in open(f"{b}.objdump.tsv"))
    assert A["seven_end"] in names and names[A["seven_end"]][0] == "libpthread.a", "the 7-Zip/runtime boundary moved"

    def asm_of(a):
        for (s, e), m in A["asm"].items():
            if s <= a < e:
                return m
    def origin(a, kind, sec):
        if a in names7 and a < A["seven_end"] and not (a in names and names[a][0] != "libstdc++.a"):
            return "7-Zip C/C++"
        if a in names:
            return names[a][0]
        if asm_of(a):
            return "7-Zip asm"
        for (s, e), m in A["crt"].items():
            if s <= a < e:
                return "crt"
        if sec in (".init", ".plt", ".fini"):
            return "crt"
        if a < A["seven_end"]:
            return "7-Zip C/C++"
        return "runtime, unnamed"
    def label(a):
        o = origin(a, "", "")
        if o == "7-Zip C/C++" and a in names7:
            return f"{names7[a][0]}: {names7[a][1]}"
        if a in names:
            return f"{names[a][1].split(';')[0]}: {names[a][2]}"
        return asm_of(a) or A["guess"].get(a, "")
    for (s, e), m in A["asm"].items():
        assert any(a == s for a, _, _, _ in fns), f"no function at the start of {m}"

    by = collections.defaultdict(lambda: [0, 0, 0, 0])   # origin -> functions, bytes, instructions, issues (full)
    for a, n, k, sec in fns:
        o = origin(a, k, sec)
        c = cov["full"].get(a, (0, 0, ""))
        by[o][0] += 1; by[o][1] += n; by[o][2] += c[0]; by[o][3] += c[1]

    # call graph from objdump's text: direct `call`/`jmp` to another function's start (a `jmp` there is a tail call),
    # and the indirect calls and jumps of each function (each a CFI obligation, PLAN.md P5)
    import bisect, re
    fstarts = [a for a, _, _, _ in fns]
    fend = {a: a + n for a, n, _, _ in fns}
    def fn_of(x):
        i = bisect.bisect_right(fstarts, x) - 1
        return fstarts[i] if i >= 0 and x < fend[fstarts[i]] else None
    edges, indirect = collections.Counter(), collections.Counter()
    for r in rows(f"{b}.objdump.tsv"):
        m = r[2].split(" ")[-1]
        if m not in ("call", "callq", "jmp", "jmpq"):
            continue
        a = int(r[0], 16); f = fn_of(a)
        if f is None:
            continue
        t = re.match(r"(?:notrack |bnd |addr32 )*(?:call|jmp)q? 0x([0-9a-f]+)", r[3])
        if t:
            g = int(t.group(1), 16)
            if g in fend and g != f:
                edges[(f, g, "call" if m.startswith("call") else "tail")] += 1
        elif "*" in r[3]:
            indirect[f] += 1
    callers, callees = collections.defaultdict(set), collections.defaultdict(set)
    with open(f"{b}.callgraph.tsv", "w") as t:
        t.write("caller\tcallee\tkind\tsites\n")
        for (f, g, k), c in sorted(edges.items()):
            t.write(f"{f:x}\t{g:x}\t{k}\t{c}\n"); callers[g].add(f); callees[f].add(g)
    with open(f"{b}.codemap.tsv", "w") as t:
        t.write("start\tsize\tkind\torigin\tname\tinsns\tissues_full\tissues_min\tcallers\tcallees\tindirect\tstatus\n")
        for a, n, k, sec in fns:
            cf, cm = cov["full"].get(a, (0, 0, "")), cov["min"].get(a, (0, 0, ""))
            t.write(f"{a:x}\t{n}\t{k}\t{origin(a, k, sec)}\t{label(a)}\t{cf[0]}\t{cf[1]}\t{cm[1]}\t"
                    f"{len(callers[a])}\t{len(callees[a])}\t{indirect[a]}\ttodo\n")
    p = print
    p(f"# CODEMAP — `{name}` 26.06 (G0)\n")
    p("Sinh tự động bởi `tools/codemap.py` từ `build/` (`tools/g0.sh`, `tools/libmatch.py`); đừng sửa tay.")
    p("Đây là bản đồ đo đạc, không phải bằng chứng: tên hàm runtime là khớp byte (đã che relocation) với `.a` của")
    p("Ubuntu 20.04, tên module asm là nhận dạng theo lệnh, còn ranh giới hàm là FDE của `.eh_frame` và các đoạn")
    p("code không có FDE.\n")
    p("## 1. Bố cục\n")
    p("| Vùng | Địa chỉ | Nguồn gốc |\n|---|---|---|")
    p(f"| `.init`, `.plt` (IRELATIVE) | 0x401000–0x401118 | crt, glibc IFUNC |")
    p(f"| `.text.unlikely`/`.text.startup` của GCC | 0x401120–0x{A['entry']:x} | phần cold của mọi object, `main` = 0x{A['main']:x} |")
    p(f"| object 7-Zip (C, C++, asm) | 0x{A['entry']:x}–0x{A['seven_end']:x} | link theo thứ tự `7zip_gcc.mak` |")
    p(f"| libpthread, libstdc++, libc, libgcc(_eh), libm | 0x{A['seven_end']:x}–0x6d4040 | glibc 2.31-0ubuntu9.18, gcc-9 9.4.0-1ubuntu1~20.04.2 |")
    p(f"| `.text$LZMADECOPT`, `.text$LZFINDOPT` | 0x6d4040–0x6d5665 | asm 7-Zip |")
    p(f"| `.fini` | 0x6d7670 | crt |\n")
    n7 = [a for a, _, k, sec in fns if origin(a, k, sec) == "7-Zip C/C++"]
    p(f"Tổng: {insns} lệnh (objdump), {len(fns)} hàm. Hàm C/C++ của 7-Zip có tên từ bản build lại GCC 9.4: "
      f"{sum(1 for a in n7 if a in names7)}/{len(n7)}. Bảng đầy đủ từng hàm (địa chỉ, nguồn gốc, tên, độ phủ, trạng "
      f"thái `todo`/`contract`/`proved`/`bug`/`assumed`): `build/{name}.codemap.tsv`.\n")
    p("## 2. Hàm theo nguồn gốc (feature set `full`)\n")
    p("| Nguồn gốc | Hàm | Byte | Lệnh | Lệnh model chưa hỗ trợ |\n|---|---:|---:|---:|---:|")
    for o, (f_, n, i, x) in sorted(by.items(), key=lambda kv: -kv[1][1]):
        p(f"| {o} | {f_} | {n} | {i} | {x} |")
    p(f"\nĐồ thị gọi (`build/{name}.callgraph.tsv`): {len(edges)} cạnh trực tiếp; {sum(indirect.values())} lệnh "
      f"`call`/`jmp` gián tiếp trong {len(indirect)} hàm (gọi qua con trỏ, vtable và bảng nhảy của `switch`; mỗi lệnh là một nghĩa vụ CFI, P5). Theo nguồn gốc:\n")
    p("| Nguồn gốc | Lệnh gián tiếp |\n|---|---:|")
    ind_by = collections.Counter()
    for a, _, k, sec in fns:
        ind_by[origin(a, k, sec)] += indirect[a]
    for o, c in ind_by.most_common():
        if c:
            p(f"| {o} | {c} |")
    p("\n## 3. Module assembly của 7-Zip (không có CFI)\n")
    p("| Module | Hàm (đoạn) | Lệnh | Chưa hỗ trợ (`full`) | Chưa hỗ trợ (`min`) |\n|---|---|---:|---:|---:|")
    for (s, e), m in sorted(A["asm"].items()):
        parts = [a for a, _, _, _ in fns if s <= a < e]
        i = sum(cov["full"].get(a, (0, 0, ""))[0] for a in parts)
        x = sum(cov["full"].get(a, (0, 0, ""))[1] for a in parts)
        y = sum(cov["min"].get(a, (0, 0, ""))[1] for a in parts)
        p(f"| {m} | {', '.join(f'0x{a:x}' for a in parts)} | {i} | {x} | {y} |")
    for s in ("full", "min"):
        p(f"\n## {4 if s == 'full' else 5}. Hàm có lệnh model chưa hỗ trợ — feature set `{s}`\n")
        p("| Hàm | Byte | Nguồn gốc | Tên | Lệnh | Vấn đề | Ví dụ |\n|---|---:|---|---|---:|---:|---|")
        for a, n, k, sec in fns:
            c = cov[s].get(a)
            if not c or c[1] == 0:
                continue
            nm = label(a)
            ex = c[2].split(" | ")[0].replace("|", "\\|")
            p(f"| 0x{a:x} | {n} | {origin(a, k, sec)} | {nm[:60]} | {c[0]} | {c[1]} | `{ex[:90]}` |")

    p("\n## 6. Việc cho G1: lệnh model chưa hỗ trợ, theo nguồn gốc (`full`)\n")
    p("Lệnh có `[on the 0 path only]` có thể chỉ là hệ quả của đường đo (số lần dịch bằng 0), cần xem lại khi chứng minh.\n")
    p("| Nguồn gốc | Lệnh (objdump) | Số lệnh | Vấn đề |\n|---|---|---:|---|")
    starts = sorted(a for a, _, _, _ in fns)
    import bisect
    agg = collections.Counter()
    for r in rows(f"{b}.insncov.full.insns", True):
        a = int(r[0], 16)
        i = bisect.bisect_right(starts, a) - 1
        f = next(x for x in fns if x[0] == starts[i]) if i >= 0 else None
        o = origin(f[0], f[2], f[3]) if f and a < f[0] + f[1] else "?"
        agg[(o, r[2].split(" ")[0], r[4])] += 1
    for (o, m, why), c in sorted(agg.items(), key=lambda kv: (kv[0][0], -kv[1])):
        p(f"| {o} | `{m}` | {c} | {why} |")

if __name__ == "__main__":
    main(*sys.argv[1:2])
