import FV7z.Lemmas.Sse2
/-!
# Steps of `__strlen_sse2` that keep the vector registers (PLAN.md M, the PLT contracts)

`Seg.s_jcc` and `Seg.s_jmp` say only where the run goes and that the registers stay; `strlen`'s loop needs its zeroed
`xmm1`–`xmm3` to stay across its jumps too. `bsf` of a register not 0, at 64 and at 32 bits, as a step of a segment.
-/
namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `jcc` to the `tgt`-th byte of the same segment, the vector registers kept. -/
theorem s_jccV (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {rel len tgt : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true → ContG prof F Wl L s₀ o gev gP gE V fun Y =>
      Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec)
    (fall : X.cpu.rflags.cond cc = false → ContG prof F Wl L s₀ o gev gP gE V fun Y =>
      Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf
      (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) (fall hcc)
  · refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) (taken hcc)
    have hca := ((c.codeAt hK' hin) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
      rw [withMem_cpu, hrip]; exact addr_rel htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hin hrip hd) hcc (by rw [ha]; exact hca),
      hK'.upd rfl rfl rfl, hA', ha, rfl, rfl⟩

/-- `jmp` to the `tgt`-th byte of the same segment, the vector registers kept. -/
theorem s_jmpV (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {rel len tgt : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.rel rel] len))
    (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y =>
      Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t := by
  refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) k'
  have hca := ((c.codeAt hK' hin) tgt ht).1
  have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
    rw [withMem_cpu, hrip]; exact addr_rel htgt
  exact ⟨_, _, jmp_rel (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl, rfl⟩

/-- `bsf r64, q` of `q` not 0. -/
theorem s_bsf64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.bit .bsf) 64 [gr 64 r, gr 64 q] len)) (hx : rv X 64 q ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (BitVec.ofNat 64 (lowestSetBit (rv X 64 q)))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := bsf64_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd) hx
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

/-- `bsf r32, q` of `q`'s low half not 0. -/
theorem s_bsf32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.bit .bsf) 32 [gr 32 r, gr 32 q] len)) (hx : rv X 32 q ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((BitVec.ofNat 32 (lowestSetBit (rv X 32 q))).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := tzcnt_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (Or.inr (c.dec hK' hin hrip hd)) hx
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
