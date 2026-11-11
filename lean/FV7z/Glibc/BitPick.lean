import FV7z.Glibc.Cpu
/-!
# The IFUNC resolvers of `7zzs` that pick a variant by one bit of `_dl_x86_cpu_features` (PLAN.md G2, "Dispatch theo
CPUID")

Five resolvers of `7zzs` (`__sched_cpucount`, `strspn`, `strcspn`, `strpbrk`, `strstr`, …) are the same 30 bytes but for
the byte and bit they test, their `rip`-relative displacements and their `cmov`'s condition:

```
 0  endbr64
 4  test byte [cpu + a], 2^i
11  lea rdx, vd
18  lea rax, va
25  cmovcc rax, rdx          (cmovne: vd if the bit is set; cmove: vd if it is clear)
29  ret
```

`Shape code e a i cc vd va`: `code`, at `e`, is such a resolver. `holds`: with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it (`CpuOk`), it returns `vClr`, or `vSet` with bit `i` of byte `a` set: so, given what that
bit says (`hfs`), `vSet` only on a processor with the features `fs`.
-/
namespace FV7z.Glibc.BitPick
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e : Addr) (a i : Nat) (cc : Cond) (vd va : Addr) : Prop where
  len : code.length = 30
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∃ d imm, (∀ feat, Dec feat code 4 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 imm] 7)) ∧
    e.add (4 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add a ∧ imm = 2 ^ i
  hi : i < 8
  hn : a + 1 ≤ cpuRgn.len
  d11 : ∃ d, (∀ feat, Dec feat code 11 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip d 0)] 7)) ∧
    e.add (11 + 7) + BitVec.ofNat 64 d = vd
  d18 : ∃ d, (∀ feat, Dec feat code 18 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip d 0)] 7)) ∧
    e.add (18 + 7) + BitVec.ofNat 64 d = va
  d25 : ∀ feat, Dec feat code 25 (FV7z.mk (.cmovcc cc) 64 [gr 64 0, gr 64 2] 4)
  d29 : ∀ feat, Dec feat code 29 (FV7z.mk .ret 64 [] 1)

abbrev RR : State → List Rgn := fun _ => [cpuRgn]
abbrev PP (prof : Profile) : State → Prop := fun s => CpuOk prof s.proc.mm.mem
abbrev QQ (prof : Profile) (vs : Variants) : State → BitVec 64 → Prop := fun _ r => Returns prof vs r

theorem hr0 {s : State} : cpuRgn ∈ RR s := List.mem_singleton_self _

variable {prof : Profile} {code : List Byte} {e vd va vSet vClr : Addr} {a i : Nat} {cc : Cond}
  {fs : List (Features → Bool)} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e a i cc vd va)
    (hp : (cc = 5 ∧ vd = vSet ∧ va = vClr) ∨ (cc = 4 ∧ va = vSet ∧ vd = vClr))
    (hfs : bit s₀.proc.mm.mem a i = true → ∀ f ∈ fs, f prof.feat = true)
    (c : Call prof RR (PP prof) (QQ prof [(vClr, []), (vSet, fs)]) code e L s₀ ra o) {t : Nat} :
    Go prof RR (PP prof) (QQ prof [(vClr, []), (vSet, fs)]) L s₀ ra o s₀ t := by
  have hk : ∀ k, k < 30 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨dt, imm, hdt, hat, himm⟩ := sh.d4
  obtain ⟨d1, hd1, ha1⟩ := sh.d11
  obtain ⟨d2, hd2, ha2⟩ := sh.d18
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_test_m8i_rip hK1 (hk 4 (by decide)) hr1 (hdt _) hr0 hat sh.hn fun Y2 _ hK2 hr2 ⟨g2, z2⟩ => ?_
  refine c.s_lea_rip hK2 (hk 11 (by decide)) hr2 (hd1 _) ha1 fun Y3 _ hK3 hr3 ⟨g3, z3⟩ => ?_
  refine c.s_lea_rip hK3 (hk 18 (by decide)) hr3 (hd2 _) ha2 fun Y4 _ hK4 hr4 ⟨g4, z4⟩ => ?_
  refine c.s_cmov hK4 (hk 25 (by decide)) hr4 (sh.d25 _) fun Y5 _ hK5 hr5 g5 => ?_
  have hset : Y4.cpu.rflags.zf = false → bit s₀.proc.mm.mem a i = true := by
    intro h
    rw [z4, z3, z2, himm] at h
    have hb := getLsbD_of_and_pow (i := i) _ h
    rwa [getLsbD_word _ (by have := sh.hi; omega) sh.hi] at hb
  have hax : Y5.cpu.gpr.rax = if Y4.cpu.rflags.cond cc then vd else va := by
    rw [g5]
    split <;> simp [g4, g3]
  refine c.ret hK5 (calleeOf ?_) (hk 29 (by decide)) hr5 (sh.d29 _) ?_
  · rw [g5]
    split <;> simp [g4, g3, g2, g1]
  · show Returns prof [(vClr, []), (vSet, fs)] Y5.cpu.gpr.rax
    rw [hax]
    rcases hp with ⟨rfl, h2, h3⟩ | ⟨rfl, h2, h3⟩
    · rw [← h2, ← h3, cond5]
      cases hz : Y4.cpu.rflags.zf
      · exact ⟨(vd, fs), by simp, by simp, hfs (hset hz)⟩
      · exact ⟨(va, []), by simp, by simp, by simp⟩
    · rw [← h2, ← h3, cond4]
      cases hz : Y4.cpu.rflags.zf
      · exact ⟨(va, fs), by simp, by simp, hfs (hset hz)⟩
      · exact ⟨(vd, []), by simp, by simp, by simp⟩

/-- Such a resolver, run at `e`: on a consistent profile (with H-CPU-chain), with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns `vClr`, or `vSet` on a processor with the features `fs`, given that a set
bit `i` of byte `a` says the processor has them (`hfs`). -/
theorem holds (sh : Shape code e a i cc vd va)
    (hp : (cc = 5 ∧ vd = vSet ∧ va = vClr) ∨ (cc = 4 ∧ va = vSet ∧ vd = vClr))
    (hfs : ∀ (prof : Profile) m, prof.Consistent → Chain prof → CpuOk prof m → bit m a i = true →
      ∀ f ∈ fs, f prof.feat = true)
    (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L e code) : ImplementsCall prof e L (resolverK prof [(vClr, []), (vSet, fs)]) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    run sh hp (hfs prof _ hc hch hcall.pre) ⟨hcall, hin, ho⟩

end FV7z.Glibc.BitPick
