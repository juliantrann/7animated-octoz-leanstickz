import FV7z.Lemmas.BlkOps
/-!
# Code with branches, by its cut points (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

`Sp prof code e' j W`: from the `j`-th byte of `code`, registers `g`, flags `f` and the footprint's bytes `V`, the run
goes on to an exit `j'` with `Q j'` of what it leaves there, if `W F Wl Q g f V`: the accesses' side conditions and
`Q` at the exits, a set of conditions on registers, flags and bytes alone. A stretch of straight-line code
(`Sp.blk`), a jump (`Sp.jmp`), a conditional jump with its two exits (`Sp.jcc`), one piece after another
(`Sp.comp`).

`Seg.cfg`: with an `Sp` at each cut point and an invariant `Inv ℓ n` there, `n` a measure that every way from a cut
point to the next decreases, the run from a cut point reaches `Fin`. What is left to prove of a function is then,
at each cut point, `W` from the invariant: no machine state in it.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- What holds at exit `j'`, of the registers, the flags and the footprint's bytes. -/
abbrev Post := Nat → Gprs → Rflags → (Addr → Byte) → Prop

/-- What a piece of code needs for `Q` at its exits. -/
abbrev Wpt := Footprint → List Rgn → Post → Gprs → Rflags → (Addr → Byte) → Prop

/-- The run from the `j`-th byte of `code`, which lies at `e'`, goes on from an exit with `Q`, if `W … Q` holds. -/
structure Sp (prof : Profile) (code : List Byte) (e' : Addr) (j : Nat) (W : Wpt) : Prop where
  run : ∀ {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop},
    Seg prof F Wl L s₀ o → CodeIn L e' code →
    ∀ {X : State} {t : Nat} {V : Addr → Byte} (Q : Post), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → W F Wl Q X.cpu.gpr X.cpu.rflags V →
      (∀ j' g fl V', Q j' g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') →
      GoG prof L o gev gP gE X t

variable {prof : Profile} {code : List Byte} {e' : Addr}

/-- No code: the exit is where the run is. -/
theorem Sp.skip (j : Nat) : Sp prof code e' j fun _ _ Q => Q j :=
  ⟨fun _ _ _ _ _ _ hK hA hrip h k => k _ _ _ _ h _ _ hK hA hrip rfl rfl⟩

/-- Nothing to prove from a state that does not arise. -/
theorem Sp.never (j : Nat) : Sp prof code e' j fun _ _ _ _ _ _ => False :=
  ⟨fun _ _ _ _ _ _ _ _ _ h _ => h.elim⟩

/-- A stronger condition. -/
theorem Sp.mono {j : Nat} {W W' : Wpt} (h : Sp prof code e' j W)
    (hw : ∀ F Wl Q g f V, W' F Wl Q g f V → W F Wl Q g f V) : Sp prof code e' j W' :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => h.run c hin Q hK hA hrip (hw _ _ _ _ _ _ hW) k⟩

/-- A stretch of straight-line code. -/
theorem Sp.blk {j j' : Nat} {ops : List Op} (hb : Blk prof code j j' ops) :
    Sp prof code e' j fun F Wl Q => wp F Wl ops (Q j') :=
  ⟨fun c hin _ _ _ _ hK hA hrip hW k => c.s_blk hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq Y t' hKY hAY hrY hg hf => k _ _ _ _ hq Y t' hKY hAY hrY hg hf) hW)⟩

/-- A stretch of straight-line code, at the code's place. -/
theorem Sp.blkA {j j' : Nat} {ops : List Op} (hb : BlkA prof code e' j j' ops) :
    Sp prof code e' j fun F Wl Q => wp F Wl ops (Q j') :=
  ⟨fun c hin _ _ _ _ hK hA hrip hW k => c.s_blkA hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq Y t' hKY hAY hrY hg hf => k _ _ _ _ hq Y t' hKY hAY hrY hg hf) hW)⟩

/-- A stretch of straight-line code at the code's place, then a piece from its end. -/
theorem Sp.blkA_then {j j' : Nat} {ops : List Op} {W : Wpt} (hb : BlkA prof code e' j j' ops)
    (h : Sp prof code e' j' W) : Sp prof code e' j fun F Wl Q => wp F Wl ops (W F Wl Q) :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => c.s_blkA hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq _ _ hKY hAY hrY hg hf => h.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k) hW)⟩

/-- A stretch of straight-line code, then a piece from its end. -/
theorem Sp.blk_then {j j' : Nat} {ops : List Op} {W : Wpt} (hb : Blk prof code j j' ops) (h : Sp prof code e' j' W) :
    Sp prof code e' j fun F Wl Q => wp F Wl ops (W F Wl Q) :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => c.s_blk hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq _ _ hKY hAY hrY hg hf => h.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k) hW)⟩

/-- One piece, then from each of its exits another. -/
theorem Sp.comp {j : Nat} {W : Wpt} {W' : Nat → Wpt} (h : Sp prof code e' j W) (h' : ∀ j', Sp prof code e' j' (W' j')) :
    Sp prof code e' j fun F Wl Q => W F Wl fun j' => W' j' F Wl Q :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => h.run c hin _ hK hA hrip hW
    fun j' _ _ _ hq _ _ hKY hAY hrY hg hf => (h' j').run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k⟩

/-- `jmp` to the `tgt`-th byte. -/
theorem Sp.jmp {j rel len tgt : Nat} (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.rel rel] len))
    (hj : j < code.length) (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length) :
    Sp prof code e' j fun _ _ Q g f V => Q tgt g (rfz f) V := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hin X t V Q hK hA hrip hW k
  refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧
    Y.cpu.rflags = rfz X.cpu.rflags) hK hA hin hj hrip (fun M hK' hA' htf _ => ?_)
    (fun Y t' hKY hAY ⟨h1, h2, h3⟩ => k _ _ _ _ hW Y t' hKY hAY h1 h2 h3)
  have hca := ((c.codeAt hK' hin) tgt ht).1
  have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
    rw [withMem_cpu, hrip]; exact addr_rel htgt
  exact ⟨_, _, jmp_rel (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl, rfl⟩

/-- `jcc` to the `tgt`-th byte, or on. -/
theorem Sp.jcc {j rel len tgt : Nat} {cc : Cond} (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (hj : j < code.length) (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length) :
    Sp prof code e' j fun _ _ Q g f V =>
      (f.cond cc = true → Q tgt g (rfz f) V) ∧ (f.cond cc = false → Q (j + len) g (rfz f) V) := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hin X t V Q hK hA hrip hW k
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = rfz X.cpu.rflags) hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf
        (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩)
      (fun Y t' hKY hAY ⟨h1, h2, h3⟩ => k _ _ _ _ (hW.2 hcc) Y t' hKY hAY h1 h2 h3)
  · refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = rfz X.cpu.rflags) hK hA hin hj hrip (fun M hK' hA' htf _ => ?_)
      (fun Y t' hKY hAY ⟨h1, h2, h3⟩ => k _ _ _ _ (hW.1 hcc) Y t' hKY hAY h1 h2 h3)
    have hca := ((c.codeAt hK' hin) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
      rw [withMem_cpu, hrip]; exact addr_rel htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hin hrip hd) hcc (by rw [ha]; exact hca),
      hK'.upd rfl rfl rfl, hA', ha, rfl, rfl⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte}

/-- The run from a cut point `ℓ` with `Inv ℓ n` reaches `Fin`: every cut point has its `Sp`, whose condition follows
from the invariant with, at the exits, `Fin` or the invariant with a smaller measure. -/
theorem cfg (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {W : Nat → Wpt}
    (hsp : ∀ ℓ, Sp prof code e' ℓ (W ℓ)) (Inv : Nat → Nat → Gprs → Rflags → (Addr → Byte) → Prop) (Fin : Post)
    (vc : ∀ ℓ n g f V, Inv ℓ n g f V →
      W ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv j' n' g' f' V') ∨ Fin j' g' f' V') g f V)
    (hfin : ∀ j' g fl V', Fin j' g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = e'.add j' → Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') :
    ∀ (n ℓ : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add ℓ → Inv ℓ n X.cpu.gpr X.cpu.rflags V → GoG prof L o gev gP gE X t := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro ℓ X t V hK hA hrip hI
    refine (hsp ℓ).run c hin _ hK hA hrip (vc ℓ n _ _ _ hI) ?_
    rintro j' g fl V' (⟨n', hn, hI'⟩ | hF) Y t' hKY hAY hrY hg hf
    · exact ih n' hn j' hKY hAY hrY (hg ▸ hf ▸ hI')
    · exact hfin _ _ _ _ hF Y t' hKY hAY hrY hg hf

end FV7z.Fn.Seg
