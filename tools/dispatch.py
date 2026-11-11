#!/usr/bin/env python3
"""Dispatch by CPUID in 7zzs: which variant each glibc IFUNC resolver picks, and whether the processor features
that choice guarantees cover what the variant needs (PLAN.md G2, "Dispatch theo CPUID"). A measurement, not a proof:
the Lean proofs of the resolvers state the same table.

  dispatch.py targets BINARY FUNCS.TSV OUT          the functions (start, size) holding a candidate of a resolver
  dispatch.py check BINARY FUNCS.TSV NEEDS.TSV MININSNS OUT
                                                    the table; exit 1 if a candidate may need a feature its choice
                                                    does not guarantee, or a function with an instruction the
                                                    feature set `min` lacks is no candidate and not explained

Each resolver (the targets of the R_X86_64_IRELATIVE relocations, `readelf -r`) is executed by a small interpreter
of the instructions objdump prints for it, on every assignment of the bits of glibc 2.31's `struct cpu_features`
(`sysdeps/x86/cpu-features.h`, at 0x7a4ae0 in 7zzs) it tests; it stops at an instruction or a load it does not
know. What a set bit guarantees about the processor (`implied`) follows the model's `Profile.Consistent` and what
`init_cpu_features` (`sysdeps/x86/cpu-features.c`, without GLIBC_TUNABLES) sets each `*_Usable` and
`AVX_Fast_Unaligned_Load` bit for.
"""
import re, subprocess, sys, itertools

CPU = 0x7a4ae0                      # &_dl_x86_cpu_features: cpuid[6] (16 bytes each), then feature[2]
WORDS = {                           # address -> (name, what a set bit i guarantees)
    CPU + 0x08: 'cpuid1.ecx', CPU + 0x0c: 'cpuid1.edx', CPU + 0x14: 'cpuid7.ebx', CPU + 0x18: 'cpuid7.ecx',
    CPU + 0x60: 'feature0', CPU + 0x64: 'feature1'}
# Profile.Consistent: a CPUID bit some CPU reports, saved by get_common_indices (Profile.Reported), means the
# feature (those that need XCR0 state as well are guaranteed only through the *_Usable bits below)
CPUID_FEAT = {('cpuid1.ecx', 0): 'sse3', ('cpuid1.ecx', 9): 'ssse3', ('cpuid1.ecx', 19): 'sse41',
              ('cpuid1.ecx', 20): 'sse42', ('cpuid1.ecx', 22): 'movbe', ('cpuid1.ecx', 23): 'popcnt',
              ('cpuid1.ecx', 25): 'aes', ('cpuid7.ebx', 3): 'bmi1', ('cpuid7.ebx', 8): 'bmi2',
              ('cpuid7.ebx', 29): 'sha', ('cpuid7.ebx', 4): 'hle', ('cpuid7.ebx', 11): 'rtm'}
# init_cpu_features: feature0 = the *_Usable bits, each set only with the CPUID bit and XCR0's state for it
USABLE = {0: ('AVX_Usable', {'avx'}), 1: ('AVX2_Usable', {'avx', 'avx2'}), 2: ('AVX512F_Usable', {'avx512f'}),
          6: ('AVX512VL_Usable', {'avx512f', 'avx512vl'}), 7: ('AVX512DQ_Usable', {'avx512f', 'avx512dq'}),
          8: ('AVX512BW_Usable', {'avx512f', 'avx512bw'}), 17: ('FMA_Usable', {'avx', 'fma'}),
          19: ('VAES_Usable', {'avx', 'vaes'})}
# AVX_Fast_Unaligned_Load (feature1 bit 8) is set only together with AVX2_Usable (cpu-features.c, line 131)
PREF_IMPLIES = {8: 1}
# Not from CPUID: the order in which the extensions came, on every Intel and AMD processor (H-CPU-chain, PLAN.md §5.3):
# glibc 2.31 picks a variant by one flag while its code uses an older extension too (`palignr` in the SSE4.2
# variants, `lddqu` in the SSSE3 ones, VEX `vpbroadcastb` and `vzeroupper` in the AVX-512 ones). Profile.Consistent
# ties each flag to its own feature only: a hypervisor may clear a flag of what the processor still executes.
HYP = {'avx512f': {'avx2', 'avx'}, 'avx2': {'avx'}, 'sse42': {'ssse3'}, 'ssse3': {'sse3'}}

# The functions with an instruction the feature set `min` lacks that no resolver picks: the other dispatch points
# (PLAN.md G1, H-CPU-min), each still to be proved (G2 "Dispatch theo CPUID").
def _o(group, *starts): return {a: group for a in starts}
OTHER = {
    **_o('7-Zip AesGenTables (Aes.c: CPU_IsSupported_AES, _VAES_AVX2) -> AesOpt.asm',
         0x41e9c0, 0x41ebc0, 0x41ec20, 0x41ee90, 0x41f0b0, 0x41f130),
    **_o('7-Zip z7_Black2sp_Prepare (Blake2s.c: AVX2, SSE41, SSSE3)', 0x4208e0, 0x420a80, 0x420dc0, 0x421700, 0x421820),
    **_o('7-Zip LzFindPrepare (LzFind.c: SSE41, AVX2)', 0x425150, 0x4251b0),
    **_o('7-Zip Sha1Prepare, Sha256Prepare (CPU_IsSupported_SHA, SSSE3) -> Sha1Opt.asm, Sha256Opt.asm', 0x43a7c0, 0x43b470),
    **_o('7-Zip z7_SwapBytesPrepare (SwapBytes.c: SSSE3, AVX2)', 0x43d0e0, 0x43d140),
    **_o('glibc lock elision (RTM, and the tunable glibc.elision.enable)', 0x5ffd40, 0x5ffe00, 0x5ffe30),
    **_o('glibc __longjmp: incsspq (SHSTK in feature_1, the thread has no shadow stack)', 0x6223f0),
    **_o('glibc __memset_avx2_erms, __memset_avx512_erms: no reference in code or data', 0x65c800, 0x65c990),
    **_o('glibc _dl_runtime_profile_avx512, _avx: lazy binding with LD_AUDIT (elf_machine_runtime_setup)',
         0x6b16e0, 0x6b1b60),
}

def implied(vals):
    f, hyp = set(), set()
    for (w, i), feat in CPUID_FEAT.items():
        if vals[w] >> i & 1: f.add(feat)
    f0 = vals['feature0']
    for b, a in PREF_IMPLIES.items():
        if vals['feature1'] >> b & 1: f0 |= 1 << a
    for b, (_, fs) in USABLE.items():
        if f0 >> b & 1: f |= fs
    g = set(f)
    while True:                                   # the closure of f under HYP
        more = set().union(*(HYP[k] for k in g if k in HYP)) - g
        if not more: break
        g |= more
    return f, g - f

def objdump(binp, a, n=0x100):
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', f'--start-address={a:#x}',
                          f'--stop-address={a + n:#x}', binp], capture_output=True, text=True, check=True).stdout
    ins = {}
    order = []
    for ln in out.splitlines():
        m = re.match(r'\s*([0-9a-f]+):\t(\S+)\s*(.*)$', ln)
        if not m: continue
        addr = int(m.group(1), 16); mn = m.group(2); rest = m.group(3)
        com = None
        if '#' in rest:
            rest, c = rest.split('#', 1); cm = re.search(r'0x([0-9a-f]+)', c); com = int(cm.group(1), 16) if cm else None
        ins[addr] = (mn, [o.strip() for o in re.split(r',(?![^(]*\))', rest.strip()) if o.strip()], com)
        order.append(addr)
    nxt = {a: b for a, b in zip(order, order[1:])}
    return ins, nxt

R64 = ['rax', 'rcx', 'rdx', 'rbx', 'rsi', 'rdi']
SUB = {}  # register name -> (base, shift, width)
for r in R64:
    b = r[1:]
    SUB['%' + r] = (r, 0, 64); SUB['%e' + b] = (r, 0, 32)
for i in range(8, 16):
    R64.append(f'r{i}'); SUB[f'%r{i}'] = (f'r{i}', 0, 64); SUB[f'%r{i}d'] = (f'r{i}', 0, 32); SUB[f'%r{i}b'] = (f'r{i}', 0, 8)
for r in ['ax', 'cx', 'dx', 'bx']:
    SUB['%' + r[0] + 'l'] = ('r' + r, 0, 8); SUB['%' + r[0] + 'h'] = ('r' + r, 8, 8)

class Stop(Exception): pass

# A value: (v, t), the integer and, for each tainted bit position, the input bits (word, bit) it may depend on.
def run(ins, nxt, entry, mem, src):
    """Execute from `entry` to `ret`; returns (rax, the input bits some branch or cmov decided on)."""
    reg = {r: (0, {}) for r in R64}; zf = None; zt = set(); dec = set(); pc = entry
    def load(a, w):
        v = 0; t = {}
        for k in range(w // 8):
            if a + k not in mem: raise Stop(f'load of {a + k:#x}')
            v |= mem[a + k] << (8 * k)
            for j in range(8):
                if (a + k, j) in src: t[8 * k + j] = frozenset([src[(a + k, j)]])
        return v, t
    def get(o, w, com):
        if o.startswith('$'): return int(o[1:], 0) & ((1 << w) - 1), {}
        if o in SUB:
            b, s, ww = SUB[o]; v, t = reg[b]
            return v >> s & ((1 << ww) - 1), {i - s: x for i, x in t.items() if s <= i < s + ww}
        if '(%rip)' in o: return load(com, w)
        raise Stop(f'operand {o}')
    def width(o): return SUB[o][2] if o in SUB else None
    def put(o, val):
        b, s, w = SUB[o]; m = (1 << w) - 1; v, t = val; ov, ot = reg[b]
        if w == 32: reg[b] = (v & m, {i: x for i, x in t.items() if i < 32})
        else:
            nt = {i: x for i, x in ot.items() if not s <= i < s + w}
            nt.update({i + s: x for i, x in t.items() if i < w})
            reg[b] = (ov & ~(m << s) | (v & m) << s, nt)
    for _ in range(200):
        if pc not in ins: raise Stop(f'pc {pc:#x}')
        mn, ops, com = ins[pc]; n = nxt.get(pc)
        if mn in ('endbr64', 'nopl', 'nopw') or (mn == 'xchg' and ops == ['%ax', '%ax']) or mn == 'cs': pc = n; continue
        if mn == 'ret': return reg['rax'][0], dec
        if mn in ('movabs', 'mov'):
            w = width(ops[1]); put(ops[1], get(ops[0], w, com)); pc = n; continue
        if mn == 'lea' and '(%rip)' in ops[0]: put(ops[1], (com, {})); pc = n; continue
        if mn in ('and', 'test', 'testb', 'cmp'):
            w = 8 if mn == 'testb' else width(ops[1])
            (x, xt), (y, yt) = get(ops[0], w, com), get(ops[1], w, com)
            if mn == 'cmp':
                r = (y - x) & ((1 << w) - 1); rt = {}
                for i in range(w): rt[i] = xt.get(i, frozenset()) | yt.get(i, frozenset())
                deps = set().union(*xt.values(), *yt.values()) if (xt or yt) else set()
            else:
                r = x & y; rt = {}
                for i in range(w):
                    d = set()
                    if i in xt and (y >> i & 1 or i in yt): d |= xt[i]
                    if i in yt and (x >> i & 1 or i in xt): d |= yt[i]
                    if d: rt[i] = frozenset(d)
                deps = set().union(*rt.values()) if rt else set()
            zf = r == 0; zt = deps
            if mn == 'and': put(ops[1], (r, rt))
            pc = n; continue
        if mn in ('je', 'jne', 'jmp'):
            t = int(ops[0], 16)
            if mn != 'jmp': dec |= zt
            pc = t if mn == 'jmp' or (zf if mn == 'je' else not zf) else n; continue
        if mn in ('cmove', 'cmovne'):
            dec |= zt
            if zf == (mn == 'cmove'): put(ops[1], get(ops[0], 64, com))
            pc = n; continue
        raise Stop(f'{pc:#x}: {mn} {ops}')
    raise Stop('too long')

def mem_of(vals):
    m = {}                  # only the words of WORDS: a load of another byte stops the run
    for a, w in WORDS.items():
        for k in range(4): m[a + k] = vals[w] >> (8 * k) & 0xff
    return m

SRC = {(a + k, j): (w, 8 * k + j) for a, w in WORDS.items() for k in range(4) for j in range(8)}

def resolvers(binp):
    out = subprocess.run(['readelf', '-rW', binp], capture_output=True, text=True, check=True).stdout
    return [(int(l.split()[0], 16), int(l.split()[3], 16)) for l in out.splitlines() if 'IRELATIV' in l]

def table(binp):
    res = []
    for got, r in resolvers(binp):
        ins, nxt = objdump(binp, r)
        cand = set()
        while True:              # the bits the choices depend on: until no run decides on another
            cl = sorted(cand); more = set(); picks = {}
            for asg in itertools.product((0, 1), repeat=len(cl)):
                vals = {w: 0 for w in WORDS.values()}
                for (w, b), x in zip(cl, asg):
                    if x: vals[w] |= 1 << b
                t, dec = run(ins, nxt, r, mem_of(vals), SRC)
                more |= dec - cand
                f, hyp = implied(vals)
                p = picks.setdefault(t, [None, set(), 0])
                p[0] = f if p[0] is None else p[0] & f
                p[1] |= hyp; p[2] += 1
            if not more: break
            cand |= more
            if len(cand) > 20: raise SystemExit(f'resolver {r:#x}: {len(cand)} bits')
        res.append((got, r, cl, picks))
    return res

def load_funcs(path):
    fs = []
    for l in open(path):
        f = l.split('\t')
        try: fs.append((int(f[0], 16), int(f[1])))
        except ValueError: pass
    fs.sort(); return fs

def containing(fs, a):
    for s, n in fs:
        if s <= a < s + n: return (s, n)
    return None

def main():
    mode = sys.argv[1]
    if mode == 'targets':
        binp, funcs, out = sys.argv[2:5]
        fs = load_funcs(funcs); tgt = set()
        for _, _, _, picks in table(binp):
            for t in picks:
                c = containing(fs, t)
                if c is None: raise SystemExit(f'candidate {t:#x} in no function')
                tgt.add(c)
        with open(out, 'w') as o:
            for s, n in sorted(tgt): o.write(f'{s:x}\t{n}\n')
        print(f'dispatch: {len(tgt)} functions hold a candidate'); return 0
    binp, funcs, needsf, mininsns, out = sys.argv[2:7]
    fs = load_funcs(funcs)
    needs = {}
    for l in open(needsf):
        f = l.rstrip('\n').split('\t')
        if f[0] == 'start': continue
        needs[int(f[0], 16)] = set(x for x in f[3].split(',') if x)
    rc = 0; lines = []; covered = set(); nres = ncand = 0
    for got, r, cl, picks in table(binp):
        nres += 1
        lines.append(f'resolver {r:x} (GOT {got:x}), tests ' + ' '.join(f'{w}.{b}' for w, b in cl))
        for t, (f, hyp, _) in sorted(picks.items()):
            ncand += 1
            c = containing(fs, t); nd = needs.get(c[0], {'?'})
            covered.add(c[0])
            miss = nd - f - hyp
            st = 'ok' if not miss else 'FAIL'
            if miss: rc = 1
            h = f' (with H-CPU: {",".join(sorted(hyp & nd))})' if hyp & nd else ''
            lines.append(f'  {t:x}\tin {c[0]:x}\tneeds {",".join(sorted(nd)) or "-"}\tguaranteed '
                         f'{",".join(sorted(f)) or "-"}\t{st}{h}' + (f'\tmissing {",".join(sorted(miss))}' if miss else ''))
    # every function with an instruction `min` lacks: a candidate, or listed in the other dispatch points
    bad = {}
    for l in open(mininsns):
        f = l.split('\t')
        if f[0] == 'addr': continue
        if f[3] != '-': bad.setdefault(int(f[3], 16), 0); bad[int(f[3], 16)] += 1
    other = [s for s in bad if s not in covered]
    lines.append(f'functions with an instruction min lacks: {len(bad)}; candidates of a resolver: '
                 f'{len(bad) - len(other)}; others: {len(other)}')
    for s in sorted(other):
        g = OTHER.get(s)
        if g is None: rc = 1
        lines.append(f'  other {s:x}\t{bad[s]} instructions\tneeds {",".join(sorted(needs.get(s, {"?"})))}\t'
                     + (g if g else 'FAIL: no dispatch point known'))
    open(out, 'w').write('\n'.join(lines) + '\n')
    nh = sum(1 for l in lines if 'H-CPU' in l)
    print('\n'.join(l for l in lines if 'FAIL' in l or l.startswith('functions')))
    print(f'candidates that rely on H-CPU-chain: {nh}')
    print(f'dispatch: {nres} resolvers, {ncand} candidates, ' + ('ok' if rc == 0 else 'FAIL'))
    return rc

if __name__ == '__main__':
    sys.exit(main())
