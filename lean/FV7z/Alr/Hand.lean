import FV7z.Alr.Holds
import FV7z.Lemmas.Lock2
/-!
# `CArchiveLink::Release` (PLAN.md §M, M1): the `Release` in line and the arcs' loop, part 2

From 270 (`R237`'s `h270`: the arc's `CMyComPtr` `b` not null, its `Release` the one in line, `0x5db1e0`) to 463,
and the loop over the arcs by induction (`L64`). The bytes by invariants the caller chooses (`Eh`), indexed by the
step `k`, the arc `p` and `b`: from `J k p` with `b` at `p` to `H` (`hH`); `sub dword [b + 0x10], 1` and the stores
of the vtables (at `b`, `b + 8`) are where `Ok` holds and keep `H` (`hcl`); with the count not yet 0 the `jne` (275)
to 463 with `J k p` (`hX`); else the `Release` of `[b + 0x30]` unless null (317, `kQ`), the items (`n` = the 32 bits
at `b + 0x20`, `_items` the 8 bytes at `b + 0x18`) from the last: at the item `i` (`rbx` = `8 i`) `Hi`, the item `it`
(`iA`) null to `Hd` (`hP0`), else `Hj` (`hj`), kept by the `delete []` of its strings (`kDi`) and given up for `Hd` by
`operator delete (it, 0x80)` (421, `kI`); `Hd (i + 1)` gives `Hi i` (`hds`), `Hd 0` gives `Hx` (`hd0`), as does a
count 0 (`hH0`); then `delete [] _items` unless null (445, `kDx`) and `operator delete (b, 0x38)` (458, `kF`), back
to `J k p` at 463.

- `Fh`: the frame (`Fa`, `r14` = `b`); `IA`: an item's strings readable; `Eh`: the hypotheses.
- `H270`, `H275`, `H320`; the items: `B344`, `R368`, `R383`, `R398`, `R413`, `R426`, `S430`, `I344`, `L344`;
  `R440`, `R450`; `Rel270` (270 by `H270`), `Arc` (99 to 476 for the arc `p`), `L64` (the head at every step).

Left: the start (0–64: `ClearErrors`, the `Z1` stores, the count at `this + 8`, 0 to 493) and `alr_ok`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Alr
set_option linter.unusedVariables false

open FV7z.Fr40 (KS)
open FV7z.Ocv (rbx0 rbx0_eq rb_step rb_ne rb_last)

/-- The frame in the `Release` in line: `Fa`, `r14` = `b`. -/
abbrev Fh (S : Addr) (g0 : Gprs) (p b : Addr) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.r13 = g0.rdi ∧ g.r15 = g0.r15 ∧ g.rbp = p ∧ g.r14 = b

theorem Fh.fr {S : Addr} {g0 : Gprs} {p b : Addr} {g g' : Gprs} (h : Fh S g0 p b g) (h' : Fr g g') :
    Fh S g0 p b g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.2.trans h.2.2.1, h'.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.2.1.trans h.2.2.2.2⟩

theorem Fh.fb {S : Addr} {g0 : Gprs} {p b : Addr} {g g' : Gprs} (h : Fh S g0 p b g) (h' : Fb g g') :
    Fh S g0 p b g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.trans h.2.2.1, h'.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2⟩

theorem Fh.fc {S : Addr} {g0 : Gprs} {p b : Addr} {g g' : Gprs} (h : Fh S g0 p b g) (h' : Fc g g') :
    Fh S g0 p b g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.trans h.2.2.1, h'.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2⟩

theorem fh_ret {S : Addr} {g0 : Gprs} {p b : Addr} {g g' : Gprs} (h : Fh S g0 p b g) (hs : g'.rsp = aR S)
    (hk : KS g g') : Fh S g0 p b g' :=
  ⟨hs, hk.2.2.2.1.trans h.2.1, hk.2.2.2.2.2.trans h.2.2.1, hk.2.1.trans h.2.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.2⟩

theorem Fh.fa {S : Addr} {g0 : Gprs} {p b : Addr} {g : Gprs} (h : Fh S g0 p b g) : Fa S g0 p g :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem fr_fb {g g' : Gprs} (h : Fr g g') : Fb g g' :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The item `i` (`_items` at `b + 0x18`). -/
abbrev iA (W : Addr → Byte) (b : Addr) (i : Nat) : Addr := rdq(W, rdq(W, b + 24#64) + BitVec.ofNat 64 (8 * i))

/-- An item's strings readable: at `0x48`, `0x38`, `0x20`, `0x10`. -/
structure IA (F : Footprint) (it : Addr) : Prop where
  f16 : ∀ i < 8, Foot F.data (Addr.add (it + 16#64) i)
  f32 : ∀ i < 8, Foot F.data (Addr.add (it + 32#64) i)
  f56 : ∀ i < 8, Foot F.data (Addr.add (it + 56#64) i)
  f72 : ∀ i < 8, Foot F.data (Addr.add (it + 72#64) i)

/-- In the item `it` (the item `i`): `Hj`, the frame, `rbx` = `8 i`, `r12` = `it`. -/
abbrev PJ (S : Addr) (g0 : Gprs) (Hj : Nat → Addr → Addr → Nat → Addr → (Addr → Byte) → Prop) (k : Nat)
    (p b : Addr) (i : Nat) (it : Addr) : Gprs → (Addr → Byte) → Prop :=
  fun g W => Hj k p b i it W ∧ Fh S g0 p b g ∧ g.rbx = BitVec.ofNat 64 (8 * i) ∧ g.r12 = it

/-- The hypotheses of the `Release` in line (`J` as in `Ev`; `H`, `Hi`, `Hj`, `Hd`, `Hx` the invariants of the
bytes, `Ok` the stores that keep `H`). -/
structure Eh (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : Nat → Addr → (Addr → Byte) → Prop) (H Hx : Nat → Addr → Addr → (Addr → Byte) → Prop)
    (Hi : Nat → Addr → Addr → Nat → (Addr → Byte) → Prop)
    (Hj : Nat → Addr → Addr → Nat → Addr → (Addr → Byte) → Prop)
    (Hd : Nat → Addr → Addr → Nat → (Addr → Byte) → Prop) (Ok : Addr → Nat → Prop) : Prop where
  hH : ∀ k p W, J k p W → rdq(W, p) ≠ 0 → H k p (rdq(W, p)) W
  hX : ∀ k p b W, H k p b W → J k p W
  w16 : ∀ k p b W, H k p b W → ∀ i < 4, Foot Wl (Addr.add (b + 16#64) i)
  o16 : ∀ k p b W, H k p b W → Ok (b + 16#64) 4
  w0 : ∀ k p b W, H k p b W → ∀ i < 8, Foot Wl (Addr.add b i)
  w8 : ∀ k p b W, H k p b W → ∀ i < 8, Foot Wl (Addr.add (b + 8#64) i)
  o0 : ∀ k p b W, H k p b W → Ok b 8
  o8 : ∀ k p b W, H k p b W → Ok (b + 8#64) 8
  hcl : ∀ k p b (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → H k p b W →
    H k p b (Vst W a bs)
  f48 : ∀ k p b W, H k p b W → ∀ i < 8, Foot F.data (Addr.add (b + 48#64) i)
  hQ : ∀ k p b W W', H k p b W → H k p b W' → ¬rdq(W, b + 48#64) = 0 → Com F L W' (rdq(W, b + 48#64))
  kQ : ∀ k p b W v j, H k p b W → Com F L W v →
    KC prof F Wl L s₀ o gev gP gE S (rdq(W, rdq(W, v) + 16#64)) j W (fun g => g.rdi = v) (H k p b)
  f32 : ∀ k p b W, H k p b W → ∀ i < 4, Foot F.data (Addr.add (b + 32#64) i)
  f24 : ∀ k p b W, H k p b W → ∀ i < 8, Foot F.data (Addr.add (b + 24#64) i)
  hH0 : ∀ k p b W, H k p b W → rdd(W, b + 32#64) = 0 → Hx k p b W
  hHi : ∀ k p b W, H k p b W → rdd(W, b + 32#64) ≠ 0 → Hi k p b ((rdd(W, b + 32#64)).toNat - 1) W
  fi : ∀ k p b i W, Hi k p b i W → ∀ j < 8, Foot F.data (Addr.add (rdq(W, b + 24#64) + BitVec.ofNat 64 (8 * i)) j)
  hP0 : ∀ k p b i W, Hi k p b i W → iA W b i = 0 → Hd k p b i W
  hj : ∀ k p b i W, Hi k p b i W → iA W b i ≠ 0 → Hj k p b i (iA W b i) W
  ia : ∀ k p b i it W, Hj k p b i it W → IA F it
  kDi : ∀ k p b i it W j, Hj k p b i it W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 j W (fun _ => True) (Hj k p b i it)
  kI : ∀ k p b i it W, Hj k p b i it W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 426 W (fun g => g.rdi = it ∧ g.rsi = 128#64) (Hd k p b i)
  fdD : ∀ k p b i W, Hd k p b i W → ∀ j < 8, Foot F.data (Addr.add (b + 24#64) j)
  hd0 : ∀ k p b W, Hd k p b 0 W → Hx k p b W
  hds : ∀ k p b i W, Hd k p b (i + 1) W → Hi k p b i W
  kDx : ∀ k p b W j, Hx k p b W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 j W (fun _ => True) (Hx k p b)
  kF : ∀ k p b W, Hx k p b W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 463 W (fun g => g.rdi = b ∧ g.rsi = 56#64) (J k p)

section Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I D : Nat → (Addr → Byte) → Prop}
  {J : Nat → Addr → (Addr → Byte) → Prop} {H Hx : Nat → Addr → Addr → (Addr → Byte) → Prop}
  {Hi Hd : Nat → Addr → Addr → Nat → (Addr → Byte) → Prop}
  {Hj : Nat → Addr → Addr → Nat → Addr → (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-! ## From 275 to the items -/

/-- 275 (`H`): the count not 0 to 463 with `J k p` (`hX`); else the vtables stored, `[b + 0x30]` released unless
null (317, `kQ`), to 320. -/
theorem H275 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr)
    (h463 : AtJ prof F Wl L s₀ o gev gP gE 463 (PA S g0 J k p)) (h320 : AtJ prof F Wl L s₀ o gev gP gE 320 fun g W =>
      H k p b W ∧ Fh S g0 p b g) :
    AtJ prof F Wl L s₀ o gev gP gE 275 fun g W => H k p b W ∧ Fh S g0 p b g := by
  rintro Y W t hK hA hr ⟨hH, hm⟩
  have h14 : Y.cpu.gpr.r14 = b := hm.2.2.2.2
  refine (c_275 prof).run E.c E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ ((j' = 463 ∧ V' = W) ∨
      (j' = 320 ∧ H k p b V') ∨ (j' = 317 ∧ H k p b V' ∧ ¬rdq(W, b + 48#64) = 0 ∧ g'.rdi = rdq(W, b + 48#64) ∧
        g'.rax = rdq(V', rdq(W, b + 48#64))))) hK hA hr
    (vc_275 (q := rdq(W, b + 48#64)) (by rw [h14]; exact X.w0 k p b W hH) (by rw [h14]; exact X.w8 k p b W hH)
      (by rw [h14]; exact X.o0 k p b W hH) (by rw [h14]; exact X.o8 k p b W hH) hH (X.hcl k p b)
      (by rw [h14]; exact X.f48 k p b W hH) (by rw [h14]) (fun hq => (X.hQ k p b W W hH hH hq).1)
      (fun _ x _ => ⟨x, Or.inl ⟨rfl, rfl⟩⟩) (fun _ _ hI _ x _ => ⟨x, Or.inr (Or.inl ⟨rfl, hI⟩)⟩)
      (fun _ _ hI hq x y z _ => ⟨x, Or.inr (Or.inr ⟨rfl, hI, hq, y, z⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fh.fr hm gf
  rcases hj with ⟨rfl, hV⟩ | ⟨rfl, hI⟩ | ⟨rfl, hI, hq, gdi, gax⟩
  · rw [hV] at hAU
    exact h463 U W t₁ hKU hAU hrU ⟨X.hX k p b W hH, hmU.fa⟩
  · exact h320 U V₁ t₁ hKU hAU hrU ⟨hI, hmU⟩
  · refine callMK E hKU hAU hrU hmU.1 (lt_len (by decide)) (callm_317 _) gax (X.hQ k p b W V₁ hH hI hq)
      (X.kQ k p b V₁ _ _ hI (X.hQ k p b W V₁ hH hI hq)) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hHZ
    exact h320 Z W' t₃ hKZ hAZ hrZ ⟨hHZ, fh_ret hmU hsZ hkZ⟩

/-- 270: `sub dword [b + 0x10], 1` (`H` from `J k p`, `hH`; kept, `o16`), to 275. -/
theorem H270 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (hb0 : b ≠ 0)
    (h275 : AtJ prof F Wl L s₀ o gev gP gE 275 fun g W => H k p b W ∧ Fh S g0 p b g) :
    AtJ prof F Wl L s₀ o gev gP gE 270 fun g W => J k p W ∧ Fa S g0 p g ∧ g.r14 = b ∧ rdq(W, p) = b := by
  rintro Y W t hK hA hr ⟨hJ, hm, h14, hpb⟩
  have hH : H k p b W := by
    rw [← hpb]
    exact X.hH k p W hJ (by rw [hpb]; exact hb0)
  have he : eaD Y 14 16 = b + 16#64 := by
    show Y.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 16 = _
    rw [show Y.cpu.gpr.get (regOf 14) = Y.cpu.gpr.r14 from rfl, h14]
  refine E.c.s_sub_mi32 hK hA E.hin (lt_len (by decide)) hr (sb_270 _) (by rw [he]; exact X.w16 k p b W hH) ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  exact h275 Y₁ _ t₁ hK₁ hA₁ hr₁
    ⟨X.hcl k p b W _ 4 _ (toBytesLE_length _ _) (by rw [he]; exact X.o16 k p b W hH) hH,
      by rw [hg₁]; exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, h14⟩⟩

/-- 320 (`H`): the count `n` 0 to 440 (`hH0`); else to the item `n - 1` at 344 (`hHi`, `Ocv.rbx0_eq`). -/
theorem H320 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr)
    (hlp : ∀ i, i < 4294967296 →
      AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i))
    (h440 : AtJ prof F Wl L s₀ o gev gP gE 440 fun g W => Hx k p b W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64)) :
    AtJ prof F Wl L s₀ o gev gP gE 320 fun g W => H k p b W ∧ Fh S g0 p b g := by
  rintro Y W t hK hA hr ⟨hH, hm⟩
  have h14 : Y.cpu.gpr.r14 = b := hm.2.2.2.2
  refine (c_320 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fb Y.cpu.gpr g' ∧ g'.rdi = rdq(W, b + 24#64) ∧
      ((j' = 440 ∧ rdd(W, b + 32#64) = 0) ∨
        (j' = 344 ∧ rdd(W, b + 32#64) ≠ 0 ∧ g'.rbx = rbx0 (rdd(W, b + 32#64))))) hK hA hr
    (vc_320 (n := rdd(W, b + 32#64)) (d := rdq(W, b + 24#64)) (by rw [h14]; exact X.f32 k p b W hH)
      (by rw [h14]; exact X.f24 k p b W hH) (by rw [h14]) (by rw [h14])
      (fun h0 _ x y _ => ⟨rfl, fr_fb x, y, Or.inl ⟨rfl, h0⟩⟩)
      (fun h0 _ x y z _ => ⟨rfl, x, y, Or.inr ⟨rfl, h0, z⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, gdi, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fb hm gf
  rcases hj with ⟨rfl, h0⟩ | ⟨rfl, h0, gbx⟩
  · exact h440 U W t₁ hKU hAU hrU ⟨X.hH0 k p b W hH h0, hmU, gdi⟩
  · have hlt : (rdd(W, b + 32#64)).toNat - 1 < 4294967296 := by
      have := (rdd(W, b + 32#64)).isLt
      simp only [Nat.reducePow] at this
      omega
    exact hlp _ hlt U W t₁ hKU hAU hrU ⟨X.hHi k p b W hH h0, hmU, gdi, by rw [gbx, rbx0_eq h0]⟩

/-! ## The items -/

/-- 344 at the item `i`: the item `it` null to 430 (`hP0`), else its chars at `0x48` freed unless null (363, `kDi`)
and to 368 (`hj`). -/
theorem B344 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat)
    (h430 : AtJ prof F Wl L s₀ o gev gP gE 430 fun g W => Hd k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i)) (h368 : ∀ it, AtJ prof F Wl L s₀ o gev gP gE 368 (PJ S g0 Hj k p b i it)) :
    AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i) := by
  rintro Y W t hK hA hr ⟨hI, hm, hdi, hbx⟩
  refine (c_344 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fc Y.cpu.gpr g' ∧ g'.r12 = iA W b i ∧
      ((j' = 430 ∧ iA W b i = 0 ∧ g'.rdi = Y.cpu.gpr.rdi) ∨ (j' = 368 ∧ iA W b i ≠ 0) ∨
        (j' = 363 ∧ iA W b i ≠ 0))) hK hA hr
    (vc_344 (p := iA W b i) (q := rdq(W, iA W b i + 72#64)) (by rw [hdi, hbx]; exact X.fi k p b i W hI)
      (by rw [hdi, hbx]) rfl (fun h0 => (X.ia k p b i _ W (X.hj k p b i W hI h0)).f72)
      (fun h0 _ x y z _ => ⟨rfl, x, y, Or.inl ⟨rfl, h0, z⟩⟩)
      (fun h0 _ _ x y _ => ⟨rfl, x, y, Or.inr (Or.inl ⟨rfl, h0⟩)⟩)
      (fun h0 _ _ x y _ _ => ⟨rfl, x, y, Or.inr (Or.inr ⟨rfl, h0⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, g12, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fc hm gf
  have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * i) := gf.2.1.trans hbx
  rcases hj with ⟨rfl, h0, gdi⟩ | ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · exact h430 U W t₁ hKU hAU hrU ⟨X.hP0 k p b i W hI h0, hmU, gdi.trans hdi, hbU⟩
  · exact h368 _ U W t₁ hKU hAU hrU ⟨X.hj k p b i W hI h0, hmU, hbU, g12⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_363 _) tgt_363 E.cD
      (X.kDi k p b i _ W _ (X.hj k p b i W hI h0)) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact h368 _ Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fh_ret hmU hsZ hkZ, hkZ.1.trans hbU, hkZ.2.2.1.trans g12⟩

/-- 368: the item's chars at `0x38` freed unless null (378, `kDi`), to 383. -/
theorem R368 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (it : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 383 (PJ S g0 Hj k p b i it)) : AtJ prof F Wl L s₀ o gev gP gE 368 (PJ S g0 Hj
      k p b i it) := by
  rintro Y W t hK hA hr ⟨hJ, hm, hbx, h12⟩
  refine (c_368 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 383 ∨ j' = 378)) hK hA hr
    (vc_368 (by rw [h12]; exact (X.ia k p b i it W hJ).f56) (fun _ _ x _ => ⟨rfl, x, Or.inl rfl⟩)
      (fun _ _ x _ _ => ⟨rfl, x, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  have hbU := gf.2.1.trans hbx
  have h12U := gf.2.2.2.1.trans h12
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU, hbU, h12U⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_378 _) tgt_378 E.cD (X.kDi k p b i it W _ hJ)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fh_ret hmU hsZ hkZ, hkZ.1.trans hbU, hkZ.2.2.1.trans h12U⟩

/-- 383: the item's chars at `0x20` freed unless null (393, `kDi`), to 398. -/
theorem R383 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (it : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 398 (PJ S g0 Hj k p b i it)) : AtJ prof F Wl L s₀ o gev gP gE 383 (PJ S g0 Hj
      k p b i it) := by
  rintro Y W t hK hA hr ⟨hJ, hm, hbx, h12⟩
  refine (c_383 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 398 ∨ j' = 393)) hK hA hr
    (vc_383 (by rw [h12]; exact (X.ia k p b i it W hJ).f32) (fun _ _ x _ => ⟨rfl, x, Or.inl rfl⟩)
      (fun _ _ x _ _ => ⟨rfl, x, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  have hbU := gf.2.1.trans hbx
  have h12U := gf.2.2.2.1.trans h12
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU, hbU, h12U⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_393 _) tgt_393 E.cD (X.kDi k p b i it W _ hJ)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fh_ret hmU hsZ hkZ, hkZ.1.trans hbU, hkZ.2.2.1.trans h12U⟩

/-- 398: the item's chars at `0x10` freed unless null (408, `kDi`), to 413. -/
theorem R398 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (it : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 413 (PJ S g0 Hj k p b i it)) : AtJ prof F Wl L s₀ o gev gP gE 398 (PJ S g0 Hj
      k p b i it) := by
  rintro Y W t hK hA hr ⟨hJ, hm, hbx, h12⟩
  refine (c_398 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 413 ∨ j' = 408)) hK hA hr
    (vc_398 (by rw [h12]; exact (X.ia k p b i it W hJ).f16) (fun _ _ x _ => ⟨rfl, x, Or.inl rfl⟩)
      (fun _ _ x _ _ => ⟨rfl, x, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  have hbU := gf.2.1.trans hbx
  have h12U := gf.2.2.2.1.trans h12
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU, hbU, h12U⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_408 _) tgt_408 E.cD (X.kDi k p b i it W _ hJ)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fh_ret hmU hsZ hkZ, hkZ.1.trans hbU, hkZ.2.2.1.trans h12U⟩

/-- 413: `operator delete (it, 0x80)` (421, `kI`), from its return to 426 with `Hd`. -/
theorem R413 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (it : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 426 fun g W => Hd k p b i W ∧ Fh S g0 p b g ∧
      g.rbx = BitVec.ofNat 64 (8 * i)) :
    AtJ prof F Wl L s₀ o gev gP gE 413 (PJ S g0 Hj k p b i it) := by
  rintro Y W t hK hA hr ⟨hJ, hm, hbx, h12⟩
  refine (c_413 prof).run E.c E.hin (fun j' g' _ V' => j' = 421 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.r12 ∧ g'.rsi = 128#64) hK hA hr (vc_413 fun _ x y z _ => ⟨rfl, rfl, x, y, z⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  have hbU := gf.2.1.trans hbx
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_421 _) tgt_421 E.cE (X.kI k p b i it W hJ)
    ⟨gdi.trans h12, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hDZ
  exact hn Z W' t₃ hKZ hAZ hrZ ⟨hDZ, fh_ret hmU hsZ hkZ, hkZ.1.trans hbU⟩

/-- 426: `rdi` = `_items` again, to 430. -/
theorem R426 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 430 fun g W => Hd k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i)) :
    AtJ prof F Wl L s₀ o gev gP gE 426 fun g W => Hd k p b i W ∧ Fh S g0 p b g ∧ g.rbx = BitVec.ofNat 64 (8 * i) := by
  rintro Y W t hK hA hr ⟨hD, hm, hbx⟩
  have h14 : Y.cpu.gpr.r14 = b := hm.2.2.2.2
  refine (c_426 prof).run E.c E.hin (fun j' g' _ V' => j' = 430 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = rdq(W, Y.cpu.gpr.r14 + 24#64)) hK hA hr
    (vc_426 (by rw [h14]; exact X.fdD k p b i W hD) fun _ x y _ => ⟨rfl, rfl, x, y⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact hn U W t₁ hKU hAU hrU ⟨hD, Fh.fr hm gf, by rw [gdi, h14], gf.2.1.trans hbx⟩

/-- 430 at the item `i`: `rbx` -= 8; after the item 0 to 440 (`hd0`), else to 344 with the item `i - 1` (`hds`). -/
theorem S430 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (hi : i < 4294967296)
    (hnx : ∀ i', i = i' + 1 →
      AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i' W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i'))
    (h440 : AtJ prof F Wl L s₀ o gev gP gE 440 fun g W => Hx k p b W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64)) :
    AtJ prof F Wl L s₀ o gev gP gE 430 fun g W => Hd k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i) := by
  rintro Y W t hK hA hr ⟨hD, hm, hdi, hbx⟩
  cases i with
  | zero =>
    refine (c_430 prof).run E.c E.hin (fun j' g' _ V' => j' = 440 ∧ V' = W ∧ Fb Y.cpu.gpr g' ∧
        g'.rdi = Y.cpu.gpr.rdi) hK hA hr
      (vc_430 (fun _ _ x y _ => ⟨rfl, rfl, x, y⟩)
        (fun hne => absurd (show Y.cpu.gpr.rbx - 8#64 = 18446744073709551608#64 by rw [hbx]; exact rb_last) hne))
      ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact h440 U W t₁ hKU hAU hrU ⟨X.hd0 k p b W hD, Fh.fb hm gf, gdi.trans hdi⟩
  | succ i =>
    have hne : ¬Y.cpu.gpr.rbx - 8#64 = 18446744073709551608#64 := by
      rw [hbx, rb_step i (by omega)]; exact rb_ne i (by omega)
    refine (c_430 prof).run E.c E.hin (fun j' g' _ V' => j' = 344 ∧ V' = W ∧ Fb Y.cpu.gpr g' ∧
        g'.rbx = Y.cpu.gpr.rbx - 8#64 ∧ g'.rdi = Y.cpu.gpr.rdi) hK hA hr
      (vc_430 (fun hc => absurd hc hne) fun _ _ x y z _ => ⟨rfl, rfl, x, y, z⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbx, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact hnx i rfl U W t₁ hKU hAU hrU ⟨X.hds k p b i W hD, Fh.fb hm gf, gdi.trans hdi,
      by rw [gbx, hbx]; exact rb_step i (by omega)⟩

/-- The item `i`, from 344 to 344 with the item `i - 1` (`hnx`) or to 440. -/
theorem I344 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (i : Nat) (hi : i < 4294967296)
    (hnx : ∀ i', i = i' + 1 →
      AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i' W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i'))
    (h440 : AtJ prof F Wl L s₀ o gev gP gE 440 fun g W => Hx k p b W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64)) :
    AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i) :=
  B344 E X k p b i (S430 E X k p b i hi hnx h440) fun it =>
    R368 E X k p b i it (R383 E X k p b i it (R398 E X k p b i it (R413 E X k p b i it
      (R426 E X k p b i (S430 E X k p b i hi hnx h440)))))

/-- The items' loop, by induction on the item. -/
theorem L344 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr) (h440 : AtJ prof F Wl L s₀ o gev gP gE 440 fun g W => Hx k p b W ∧
    Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64)) :
    ∀ i, i < 4294967296 →
      AtJ prof F Wl L s₀ o gev gP gE 344 fun g W => Hi k p b i W ∧ Fh S g0 p b g ∧ g.rdi = rdq(W, b + 24#64) ∧
      g.rbx = BitVec.ofNat 64 (8 * i) := by
  intro i
  induction i with
  | zero => exact fun hi => I344 E X k p b 0 hi (fun i' h => absurd h (by omega)) h440
  | succ i ih =>
    exact fun hi => I344 E X k p b (i + 1) hi
      (fun i' h => by obtain rfl := Nat.add_right_cancel h; exact ih (by omega)) h440

/-! ## The tail of the `Release` in line -/

/-- 440: `delete [] _items` unless null (445, `kDx`), to 450. -/
theorem R440 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 450 fun g W => Hx k p b W ∧
      Fh S g0 p b g) : AtJ prof F Wl L s₀ o gev gP gE 440 fun g W => Hx k p b W ∧ Fh S g0 p b g ∧
      g.rdi = rdq(W, b + 24#64) := by
  rintro Y W t hK hA hr ⟨hx, hm, hdi⟩
  refine (c_440 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 450 ∨ j' = 445)) hK hA hr
    (vc_440 (fun _ _ x _ => ⟨rfl, x, Or.inl rfl⟩) (fun _ _ x _ _ => ⟨rfl, x, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hx, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_445 _) tgt_445 E.cD (X.kDx k p b W _ hx) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hxZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hxZ, fh_ret hmU hsZ hkZ⟩

/-- 450: `operator delete (b, 0x38)` (458, `kF`), from its return to 463 with `J k p`. -/
theorem R450 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p b : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 463 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 450 fun g W => Hx k p b
      W ∧ Fh S g0 p b g := by
  rintro Y W t hK hA hr ⟨hx, hm⟩
  refine (c_450 prof).run E.c E.hin (fun j' g' _ V' => j' = 458 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.r14 ∧ g'.rsi = 56#64) hK hA hr (vc_450 fun _ x y z _ => ⟨rfl, rfl, x, y, z⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fh.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_458 _) tgt_458 E.cE (X.kF k p b W hx)
    ⟨gdi.trans hm.2.2.2.2, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
  exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, (fh_ret hmU hsZ hkZ).fa⟩

/-! ## The arcs -/

/-- 270 for every `b` not null: the `Release` in line, to 463. -/
theorem Rel270 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi
    Hj Hd Hx Ok) (k : Nat) (p : Addr) (h463 : AtJ prof F Wl L s₀ o gev gP gE 463 (PA S g0 J k p)) :
    ∀ b : Addr, b ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 270 fun g W => J k p W ∧ Fa S g0 p g ∧ g.r14 = b ∧ rdq(W, p) = b := fun b hb =>
  have h440 := R440 E X k p b (R450 E X k p b h463)
  H270 E X k p b hb (H275 E X k p b h463 (H320 E X k p b (L344 E X k p b h440) h440))

/-- The arc `p` at the step `k`: from 99 to 476 with `D k`. -/
theorem Arc (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) (k : Nat) (p : Addr) (h476 : AtJ prof F Wl L s₀ o gev gP gE 476 fun g W => D k W ∧ Fm S g0 g) :
    AtJ prof F Wl L s₀ o gev gP gE 99 (PA S g0 J k p) :=
  have h463 := R463 E k p h476
  R99 E k p (R116 E k p (R133 E k p (R150 E k p (R164 E k p (R178 E k p (R192 E k p (R207 E k p (R222 E k p
    (R237 E k p h463 (Rel270 E X k p h463))))))))))

/-- The loop's head at every step, by induction. -/
theorem L64 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (X : Eh prof F Wl L s₀ o gev gP gE S J H Hi Hj
    Hd Hx Ok) : ∀ k, k + 1 < 4294967296 →
    AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k + 1) W ∧ Fm S g0 g ∧
      g.rax = BitVec.setWidth 64 (BitVec.ofNat 32 (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h476 := S476 E 0 hk fun k' h => absurd h (by omega)
    exact B64 E 0 h476 fun p => Arc E X 0 p h476
  | succ k ih =>
    intro hk
    have h476 := S476 E (k + 1) hk fun k' h => by obtain rfl := Nat.add_right_cancel h; exact ih (by omega)
    exact B64 E (k + 1) h476 fun p => Arc E X (k + 1) p h476

end Runs

end FV7z.Alr
