import FV7z.Memset.Erms
import FV7z.Strrchr.Head
/-!
# `__memset_sse2_unaligned(_erms)` (PLAN.md M, the PLT contracts of `launch_to_main`)

From `+0` (`0x65c650` in `7zzs`) and `+112` (`0x65c6c0`): `xmm0` the byte `sil` 16 times (`movd`, `punpcklbw`,
`punpcklwd`, `pshufd 0`), `rax = rdi`, then by `n = rdx`:
* `n < 16` (`+293`, `p293`): `rcx` the low 8 bytes of `xmm0`; two overlapping stores of 8, 4 or 2 bytes, one of 1, or
  none;
* `16 ≤ n ≤ 32` (`p16`): `xmm0` at `rdi + n - 16` and at `rdi`;
* `32 < n ≤ 64` (`+172`, `p172`): at `rdi`, `rdi + 16`, `rdi + n - 16`, `rdi + n - 32`;
* `n > 64` (`+200`, `p200`): the first 64 bytes and the last 64, then `movdqa` 64 bytes a time from the first multiple
  of 64 past `rdi` up to the last one at or below `rdi + n` (`round`, `rounds`);
* `_erms` with `n > 2048`: `rep stosb` (`from93`).

The stores are tracked by `FillP` (`Lemmas/StoreX.lean`) of `rdi`, `n` and `sil`: each one adds its offsets, and at the
`ret` they cover all `n` (`fin`). `setAtD_sse2u`, `setAtD_sse2ue`: a call at `+0` or `+112` does what `SetAtD` says.
-/

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `s_jccV`, with the flags kept when not taken (two `jcc`s after one `cmp`). -/
theorem s_jccF (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {rel len tgt : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true → ContG prof F Wl L s₀ o gev gP gE V fun Y =>
      Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec)
    (fall : X.cpu.rflags.cond cc = false → ContG prof F Wl L s₀ o gev gP gE V fun Y =>
      Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec ∧
        Y.cpu.rflags = rfz X.cpu.rflags) :
    GoG prof L o gev gP gE X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf
      (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl, rfl⟩) (fall hcc)
  · exact c.s_jccV hK hA hin hj hrip hd htgt ht (fun _ => taken hcc)
      (fun h => absurd (hcc.symm.trans h) (by decide))

end FV7z.Fn.Seg

namespace FV7z.Memset
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

/-- An offset inside `ms2`. -/
macro "ms2_lt" : tactic => `(tactic| (rw [ms2_length]; omega))
/-- The stores cover every offset below `n`. -/
macro "fill_cov" : tactic => `(tactic| (intro i hi; try dsimp only; omega))

/-- What a call with registers `g₀` and bytes `V` grants the stores: `SetAtD`'s hypotheses. -/
structure Ctx (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V : Addr → Byte) (g₀ : Gprs) : Prop where
  st : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i)
  ov : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64
  sp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat
  sp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  ret : RetS prof F Wl L s₀ o gev gP gE V g₀

/-- The bytes `V₂`: `V` outside the `rdx` bytes from `rdi`, `sil` at those of them at the offsets `P`. -/
abbrev FillG (V V₂ : Addr → Byte) (g₀ : Gprs) (P : Nat → Prop) : Prop :=
  FillP V V₂ g₀.rdi g₀.rdx.toNat (g₀.rsi.setWidth 8) P

/-- What the stores keep: the registers a call keeps, `rax` and `rdi` as `rdi` at the call, `xmm0` the spread byte. -/
def Inv (g₀ : Gprs) (Y : State) : Prop :=
  KpS g₀ Y.cpu.gpr ∧ Y.cpu.gpr.rax = g₀.rdi ∧ Y.cpu.gpr.rdi = g₀.rdi ∧
    xsOf Y.cpu.vec.zmm (xmmOf 0) = Strrchr.Bc g₀.rsi

section
variable {g₀ : Gprs} {Y Y' : State}

theorem Inv.ofx (h : Inv g₀ Y) (hg : Y'.cpu.gpr = Y.cpu.gpr) (hv : xsOf Y'.cpu.vec.zmm = xsOf Y.cpu.vec.zmm) :
    Inv g₀ Y' := by
  unfold Inv; rw [hg, hv]; exact h

theorem Inv.of (h : Inv g₀ Y) (hg : Y'.cpu.gpr = Y.cpu.gpr) (hv : Y'.cpu.vec = Y.cpu.vec) : Inv g₀ Y' :=
  h.ofx hg (by rw [hv])

theorem Inv.rcx {v : BitVec 64} (h : Inv g₀ Y) (hg : Y'.cpu.gpr = { Y.cpu.gpr with rcx := v })
    (hv : xsOf Y'.cpu.vec.zmm = xsOf Y.cpu.vec.zmm) : Inv g₀ Y' := by
  unfold Inv; rw [hg, hv]; exact h

theorem Inv.rdx {v : BitVec 64} (h : Inv g₀ Y) (hg : Y'.cpu.gpr = { Y.cpu.gpr with rdx := v })
    (hv : xsOf Y'.cpu.vec.zmm = xsOf Y.cpu.vec.zmm) : Inv g₀ Y' := by
  unfold Inv; rw [hg, hv]; exact h

theorem xmm_bytes (hI : Inv g₀ Y) : ∀ x ∈ toBytesLE (xlo Y 0) 16, x = g₀.rsi.setWidth 8 := by
  have hx : xlo Y 0 = Strrchr.Bc g₀.rsi := hI.2.2.2
  rw [hx]
  exact (ByteAll.bcast g₀.rsi).bytes (by decide)

end

theorem rcx_bytes {g : Gprs} {c : BitVec 64} (h : g.rcx = (Strrchr.Bc c).setWidth 64) {w n : Nat} (hw : w ≤ 64)
    (hn : 8 * n ≤ w) : ∀ x ∈ toBytesLE (gv g w 1) n, x = c.setWidth 8 := by
  have e : gv g w 1 = ((Strrchr.Bc c).setWidth 64).setWidth w := by
    show g.rcx.setWidth w = _
    rw [h]
  rw [e]
  exact (((ByteAll.bcast c).setWidth (by decide)).setWidth hw).bytes hn

theorem fillG {g₀ : Gprs} {V V₁ : Addr → Byte} {P : Nat → Prop} (hF : FillG V V₁ g₀ P)
    (hov : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) {o k : Nat} {bs : List Byte} (hl : bs.length = k)
    (ho : o + k ≤ g₀.rdx.toNat) (hb : ∀ x ∈ bs, x = g₀.rsi.setWidth 8) :
    FillG V (Vst V₁ (g₀.rdi.add o) bs) g₀ fun i => P i ∨ (o ≤ i ∧ i < o + k) :=
  FillP.st hF (Nat.le_of_lt hov) hl ho hb

/-! ## Addresses and conditions -/

theorem ea_back (a d : Addr) {k D : Nat} (hD : D + k = 2 ^ 64) (hk : k ≤ d.toNat) :
    a + d + BitVec.ofNat 64 D = a.add (d.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  have := d.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem eaG_back {g : Gprs} {a d : Addr} (h7 : g.rdi = a) (h2 : g.rdx = d) {k D : Nat} (hD : D + k = 2 ^ 64)
    (hk : k ≤ d.toNat) : eaG g (some 7) (some 2) 1 D = a.add (d.toNat - k) := by
  rw [← ea_back a d hD hk, ← h7, ← h2]
  apply BitVec.eq_of_toNat_eq
  simp [eaG, optV, get7, get2]

theorem eaG_0 {g : Gprs} {a : Addr} (h7 : g.rdi = a) : eaG g (some 7) none 1 0 = a.add 0 := by
  rw [← h7]
  apply BitVec.eq_of_toNat_eq
  simp [eaG, optV, get7, Addr.add]

theorem eaG_64 {g : Gprs} {a : Addr} (h7 : g.rdi = a) (hf : a.toNat + 64 < 2 ^ 64) :
    (eaG g (some 7) none 1 64).toNat = a.toNat + 64 := by
  have e : eaG g (some 7) none 1 64 = a.add 64 := by
    rw [← h7]
    apply BitVec.eq_of_toNat_eq
    simp [eaG, optV, get7, Addr.add]
  rw [e, toNat_add_of_fits (n := 65) (by omega) (by omega)]

/-- `and r, -64` of `a + k`, `k ≥ 64`: `a` and an offset, the next multiple of 64 at or below `a + k`. -/
theorem and_al {x a : Addr} {k : Nat} (hx : x.toNat = a.toNat + k) (hk : a.toNat + k < 2 ^ 64) (h64 : 64 ≤ k) :
    x &&& BitVec.ofNat 64 18446744073709551552 = a.add ((a.toNat + k) / 64 * 64 - a.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_m64, hx]
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem jae_t {w : Nat} {a b : BitVec w} (h : (!decide (a.toNat < b.toNat)) = true) : b.toNat ≤ a.toNat := by
  cases hc : decide (a.toNat < b.toNat)
  · exact Nat.le_of_not_lt (of_decide_eq_false hc)
  · rw [hc] at h; exact absurd h (by decide)

theorem jae_f {w : Nat} {a b : BitVec w} (h : (!decide (a.toNat < b.toNat)) = false) : a.toNat < b.toNat := by
  cases hc : decide (a.toNat < b.toNat)
  · rw [hc] at h; exact absurd h (by decide)
  · exact of_decide_eq_true hc

theorem ja_t {w : Nat} {a b : BitVec w} (h : (!(decide (a.toNat < b.toNat) || decide (a = b))) = true) :
    b.toNat < a.toNat := by
  by_cases h1 : a.toNat < b.toNat
  · rw [decide_eq_true h1, Bool.true_or] at h; exact absurd h (by decide)
  · by_cases h2 : a = b
    · rw [decide_eq_true h2, Bool.or_true] at h; exact absurd h (by decide)
    · have h3 : a.toNat ≠ b.toNat := fun h3 => h2 (BitVec.eq_of_toNat_eq h3)
      omega

theorem ja_f {w : Nat} {a b : BitVec w} (h : (!(decide (a.toNat < b.toNat) || decide (a = b))) = false) :
    a.toNat ≤ b.toNat := by
  by_cases h1 : a.toNat < b.toNat
  · exact Nat.le_of_lt h1
  · by_cases h2 : a = b
    · rw [h2]; exact Nat.le_refl _
    · rw [decide_eq_false h1, decide_eq_false h2] at h
      exact absurd h (by decide)

theorem nb_f {p : Prop} [Decidable p] (h : (!decide p) = false) : p :=
  Decidable.byContradiction fun hp => by rw [decide_eq_false hp] at h; exact absurd h (by decide)

/-- A low byte of `rdx` below 16, as a number. -/
theorem dl_toNat {d : Addr} (h : d.toNat < 16) : (d.setWidth 8).toNat = d.toNat := by
  rw [BitVec.toNat_setWidth]; omega

section
variable {F : Footprint} {Wl : List Rgn}

theorem wpV_st {n : Nat} {ea : Gprs → Addr} {val : Gprs → List Byte} {h : Gprs → Gprs} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    {a : Addr} (he : ea g = a) (hl : (val g).length = n) (hf : ∀ i < n, Foot Wl (a.add i))
    (k : wpV F Wl ops Q (h g) (rfz f) x (Vst V a (val g))) : wpV F Wl (.op (.store n ea val h) :: ops) Q g f x V := by
  subst he; exact ⟨rfl, hl, hf, k⟩

end

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-! ## The stores and the `ret` -/

/-- The `ret` once the stores cover all `n` bytes. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j len : Nat} (hj : j < ms2.length)
    (hd : Dec prof.feat ms2 j (FV7z.mk .ret 64 [] len)) {g₀ : Gprs} (C : Ctx prof F Wl L s₀ o gev gP gE V g₀)
    {Y : State} {t : Nat} {V₁ : Addr → Byte} {P : Nat → Prop} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V₁) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y) (hF : FillG V V₁ g₀ P)
    (hall : ∀ i < g₀.rdx.toNat, P i) : GoG prof L o gev gP gE Y t := by
  refine ret_atS c hin hj hd hK hA hrip hI.1 hI.2.1 (fun i hi => hF.2 _ fun h => ?_)
    (fun i hi => hF.1 i hi (hall i hi)) hF.2 C.ret
  rw [toNat_add_of_fits (n := 8) hi C.sp8] at h
  rcases C.sp with h' | h' <;> omega

/-- `movdqu [rdi + d], xmm0`. -/
theorem stD (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j len d : Nat} (hj : j < ms2.length)
    (hd : Dec prof.feat ms2 j (FV7z.mk (.sse .movdqu) 32 [.mem (mbd 7 d 128), .xmm 0] len)) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} {V₁ : Addr → Byte} {P : Nat → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y)
    (hF : FillG V V₁ g₀ P) (ho : d + 16 ≤ g₀.rdx.toNat)
    (K : ∀ Y' t' V₂, KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem V₂ → Y'.cpu.rip = e.add (j + len) →
      Y'.cpu.gpr = Y.cpu.gpr → Inv g₀ Y' → FillG V V₂ g₀ (fun i => P i ∨ (d ≤ i ∧ i < d + 16)) →
      GoG prof L o gev gP gE Y' t') : GoG prof L o gev gP gE Y t := by
  have he : eaD Y 7 d = g₀.rdi.add d := by
    show Y.cpu.gpr.get (regOf 7) + _ = _
    rw [get7, hI.2.2.1]; rfl
  refine c.s_movdqu_std hK hA hin hj hrip hd (fun i hi => ?_) ?_
  · rw [he, addr_add_add]; exact C.st _ (by omega)
  · rintro Y' t' hK' hA' ⟨hr', hg', hv'⟩
    rw [he] at hA'
    exact K Y' t' _ hK' hA' hr' hg' (hI.of hg' hv') (fillG hF C.ov (toBytesLE_length _ _) ho (xmm_bytes hI))

/-- `movdqu [rdi + rdx - k], xmm0`. -/
theorem stI (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j len D : Nat} (hj : j < ms2.length)
    (hd : Dec prof.feat ms2 j (FV7z.mk (.sse .movdqu) 32 [.mem (mbi 7 2 D 128), .xmm 0] len)) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} {V₁ : Addr → Byte} {P : Nat → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y)
    (hF : FillG V V₁ g₀ P) (hdx : Y.cpu.gpr.rdx = g₀.rdx) {k : Nat} (hD : D + k = 2 ^ 64)
    (hk : k ≤ g₀.rdx.toNat) (h16 : 16 ≤ k)
    (K : ∀ Y' t' V₂, KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem V₂ → Y'.cpu.rip = e.add (j + len) →
      Y'.cpu.gpr = Y.cpu.gpr → Inv g₀ Y' →
      FillG V V₂ g₀ (fun i => P i ∨ (g₀.rdx.toNat - k ≤ i ∧ i < g₀.rdx.toNat - k + 16)) →
      GoG prof L o gev gP gE Y' t') : GoG prof L o gev gP gE Y t := by
  have he : eaI Y 7 2 D = g₀.rdi.add (g₀.rdx.toNat - k) := by
    show Y.cpu.gpr.get (regOf 7) + Y.cpu.gpr.get (regOf 2) + _ = _
    rw [get7, get2, hI.2.2.1, hdx]; exact ea_back _ _ hD hk
  refine c.s_movdqu_sti hK hA hin hj hrip hd (fun i hi => ?_) ?_
  · rw [he, addr_add_add]; exact C.st _ (by omega)
  · rintro Y' t' hK' hA' ⟨hr', hg', hv'⟩
    rw [he] at hA'
    exact K Y' t' _ hK' hA' hr' hg' (hI.of hg' hv')
      (fillG hF C.ov (toBytesLE_length _ _) (by omega) (xmm_bytes hI))

/-- `movdqa [rcx + d], xmm0`, `rcx = rdi + R` a multiple of 16. -/
theorem stA (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j len d : Nat} (hj : j < ms2.length)
    (hd : Dec prof.feat ms2 j (FV7z.mk (.sse .movdqa) 16 [.mem (mbd 1 d 128), .xmm 0] len)) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} {V₁ : Addr → Byte} {P : Nat → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y)
    (hF : FillG V V₁ g₀ P) {R : Nat} (hcx : Y.cpu.gpr.rcx = g₀.rdi.add R) (hal : (g₀.rdi.toNat + R) % 16 = 0)
    (hd16 : d % 16 = 0) (ho : R + d + 16 ≤ g₀.rdx.toNat)
    (K : ∀ Y' t' V₂, KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem V₂ → Y'.cpu.rip = e.add (j + len) →
      Y'.cpu.gpr = Y.cpu.gpr → Inv g₀ Y' → FillG V V₂ g₀ (fun i => P i ∨ (R + d ≤ i ∧ i < R + d + 16)) →
      GoG prof L o gev gP gE Y' t') : GoG prof L o gev gP gE Y t := by
  have he : eaD Y 1 d = g₀.rdi.add (R + d) := by
    show Y.cpu.gpr.get (regOf 1) + _ = _
    rw [get1, hcx, ← addr_add_add]; rfl
  refine c.s_movdqa_std hK hA hin hj hrip hd ?_ (fun i hi => ?_) ?_
  · rw [he, toNat_add_of_fits (i := R + d) (n := g₀.rdx.toNat) (by omega) (Nat.le_of_lt C.ov)]; omega
  · rw [he, addr_add_add]; exact C.st _ (by omega)
  · rintro Y' t' hK' hA' ⟨hr', hg', hv'⟩
    rw [he] at hA'
    exact K Y' t' _ hK' hA' hr' hg' (hI.of hg' hv') (fillG hF C.ov (toBytesLE_length _ _) ho (xmm_bytes hI))

/-! ## Fewer than 16 bytes -/

/-- Two stores of the low `w` bits of `rcx`, at `rdi + n - w/8` and at `rdi`, then `ret`: `w/8 ≤ n ≤ 2·(w/8)`. -/
theorem pair (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j j' w D : Nat}
    (hb : BlkV prof ms2 j j' [VOp.op (Op.st w (some 7) (some 2) 1 D 1), VOp.op (Op.st w (some 7) none 1 0 1)])
    (hj : j' < ms2.length) (hd : Dec prof.feat ms2 j' (FV7z.mk .ret 64 [] 1)) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y) (hdx : Y.cpu.gpr.rdx = g₀.rdx)
    (hcx : Y.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64) (hD : D + w / 8 = 2 ^ 64) (hw : w ≤ 64)
    (hlo : w / 8 ≤ g₀.rdx.toNat) (hhi : g₀.rdx.toNat ≤ 2 * (w / 8)) : GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin hb hK hA hrip ?_
  refine wpV_st (eaG_back hI.2.2.1 hdx hD hlo) (toBytesLE_length _ _) (fun i hi => ?_)
    (wpV_st (eaG_0 hI.2.2.1) (toBytesLE_length _ _) (fun i hi => ?_) (wpV_nil ?_))
  · rw [addr_add_add]; exact C.st _ (by omega)
  · rw [addr_add_add]; exact C.st _ (by omega)
  · intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
    refine fin c hin hj hd C hK₁ hA₁ hr₁ (hI.ofx hg₁ hv₁)
      (fillG (fillG (FillP.start _ _ _ _) C.ov (toBytesLE_length _ _) (by omega) (rcx_bytes hcx hw (by omega)))
        C.ov (toBytesLE_length _ _) (by omega) (rcx_bytes hcx hw (by omega))) (by fill_cov)

/-- From `+293`, `n < 16`: `movq rcx, xmm0`, then by `dl`: 8 bytes twice, 4 twice, 2 twice, 1, or none. -/
theorem p293 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 293) (hI : Inv g₀ Y) (hdx : Y.cpu.gpr.rdx = g₀.rdx)
    (hn : g₀.rdx.toNat < 16) : GoG prof L o gev gP gE Y t := by
  have hd8 : ∀ {Z : State}, Z.cpu.gpr.rdx = g₀.rdx → (Z.cpu.gpr.rdx.setWidth 8).toNat = g₀.rdx.toNat :=
    fun h => by rw [h]; exact dl_toNat hn
  -- `movq rcx, xmm0`, `cmp dl, 8`
  refine c.s_blkV hin (b293 prof) hK hA hrip ?_
  refine wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [gv, Src.val, set_rcx, get2] at hg₁ hP
  have hI₁ : Inv g₀ Y₁ := hI.rcx hg₁ hv₁
  have hdx₁ : Y₁.cpu.gpr.rdx = g₀.rdx := by rw [hg₁]; exact hdx
  have hcx₁ : Y₁.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by
    rw [hg₁]
    show (xsOf Y.cpu.vec.zmm (xmmOf 0)).setWidth 64 = _
    rw [hI.2.2.2]
  refine c.s_jccV hK₁ hA₁ hin (by ms2_lt) hr₁ (d301 prof.feat) (tgt := 318) rfl (by ms2_lt) ?_ ?_
  · -- `n ≥ 8`
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hf₁, hP, cond_3, subF_cf] at htk
    have h8 := jae_t htk
    simp only [hd8 hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h8
    exact pair c hin (b318 prof) (by ms2_lt) (d326 prof.feat) C hK₂ hA₂ hr₂ (hI₁.of hg₂ hv₂)
      (by rw [hg₂]; exact hdx₁) (by rw [hg₂]; exact hcx₁) rfl (by omega) (by omega) (by omega)
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  rw [hf₁, hP, cond_3, subF_cf] at hfa
  have h8 := jae_f hfa
  simp only [hd8 hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h8
  have hI₂ := hI₁.of hg₂ hv₂
  have hdx₂ : Y₂.cpu.gpr.rdx = g₀.rdx := by rw [hg₂]; exact hdx₁
  have hcx₂ : Y₂.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₂]; exact hcx₁
  -- `cmp dl, 4`
  refine c.s_blkV hin (b303 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ hv₃
  simp only [gv, Src.val, get2] at hP
  have hI₃ := hI₂.ofx hg₃ hv₃
  have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdx := by rw [hg₃]; exact hdx₂
  have hcx₃ : Y₃.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₃]; exact hcx₂
  refine c.s_jccV hK₃ hA₃ hin (by ms2_lt) hr₃ (d306 prof.feat) (tgt := 327) rfl (by ms2_lt) ?_ ?_
  · -- `4 ≤ n < 8`
    intro htk Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
    rw [hf₃, hP, cond_3, subF_cf] at htk
    have h4 := jae_t htk
    simp only [hd8 hdx₂, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h4
    exact pair c hin (b327 prof) (by ms2_lt) (d333 prof.feat) C hK₄ hA₄ hr₄ (hI₃.of hg₄ hv₄)
      (by rw [hg₄]; exact hdx₃) (by rw [hg₄]; exact hcx₃) rfl (by omega) (by omega) (by omega)
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
  rw [hf₃, hP, cond_3, subF_cf] at hfa
  have h4 := jae_f hfa
  simp only [hd8 hdx₂, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h4
  have hI₄ := hI₃.of hg₄ hv₄
  have hdx₄ : Y₄.cpu.gpr.rdx = g₀.rdx := by rw [hg₄]; exact hdx₃
  have hcx₄ : Y₄.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₄]; exact hcx₃
  -- `cmp dl, 1`
  refine c.s_blkV hin (b308 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ hv₅
  simp only [gv, Src.val, get2] at hP
  have hI₅ := hI₄.ofx hg₅ hv₅
  have hdx₅ : Y₅.cpu.gpr.rdx = g₀.rdx := by rw [hg₅]; exact hdx₄
  have hcx₅ : Y₅.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₅]; exact hcx₄
  refine c.s_jccF hK₅ hA₅ hin (by ms2_lt) hr₅ (d311 prof.feat) (tgt := 334) rfl (by ms2_lt) ?_ ?_
  · -- `2 ≤ n < 4`
    intro htk Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, hP, cond_7, subF_cf, subF_zf] at htk
    have h1 := ja_t htk
    simp only [hd8 hdx₄, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
    exact pair c hin (b334 prof) (by ms2_lt) (d342 prof.feat) C hK₆ hA₆ hr₆ (hI₅.of hg₆ hv₆)
      (by rw [hg₆]; exact hdx₅) (by rw [hg₆]; exact hcx₅) rfl (by omega) (by omega) (by omega)
  intro hfa Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆, hf₆⟩
  have hcf : Y₆.cpu.rflags.cf = decide (g₀.rdx.toNat < 1) := by
    rw [hf₆, rfz_cf, hf₅, hP, subF_cf]
    simp only [hd8 hdx₄, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hI₆ := hI₅.of hg₆ hv₆
  have hcx₆ : Y₆.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₆]; exact hcx₅
  refine c.s_jccV hK₆ hA₆ hin (by ms2_lt) hr₆ (d313 prof.feat) (tgt := 317) rfl (by ms2_lt) ?_ ?_
  · -- `n = 0`
    intro htk Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, hv₇⟩
    rw [cond_2, hcf] at htk
    have h0 := of_decide_eq_true htk
    exact fin c hin (by ms2_lt) (d317 prof.feat) C hK₇ hA₇ hr₇ (hI₆.of hg₇ hv₇) (FillP.start _ _ _ _)
      (by fill_cov)
  · -- `n = 1`: `mov [rdi], cl`
    intro hfa' Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, hv₇⟩
    rw [hf₅, hP, cond_7, subF_cf, subF_zf] at hfa
    have h1 := ja_f hfa
    simp only [hd8 hdx₄, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
    rw [cond_2, hcf] at hfa'
    have h0 := Nat.le_of_not_lt (of_decide_eq_false hfa')
    have hI₇ := hI₆.of hg₇ hv₇
    have hcx₇ : Y₇.cpu.gpr.rcx = (Strrchr.Bc g₀.rsi).setWidth 64 := by rw [hg₇]; exact hcx₆
    refine c.s_blkV hin (b315 prof) hK₇ hA₇ hr₇ ?_
    refine wpV_st (eaG_0 hI₇.2.2.1) (toBytesLE_length _ _) (fun i hi => ?_) (wpV_nil ?_)
    · rw [addr_add_add]; exact C.st _ (by omega)
    · intro Y₈ t₈ hK₈ hA₈ hr₈ hg₈ _ hv₈
      exact fin c hin (by ms2_lt) (d317 prof.feat) C hK₈ hA₈ hr₈ (hI₇.ofx hg₈ hv₈)
        (fillG (FillP.start _ _ _ _) C.ov (toBytesLE_length _ _) (by omega)
          (rcx_bytes hcx₇ (by decide) (by decide))) (by fill_cov)

/-! ## 16 to 64 bytes -/

/-- `16 ≤ n ≤ 32`: `xmm0` at `rdi + n - 16` and at `rdi`, `ret` (at `+44` and at `+152`). -/
theorem p16 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j : Nat} (hj : j + 10 < ms2.length)
    (hd1 : Dec prof.feat ms2 j
      (FV7z.mk (.sse .movdqu) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 0] 6))
    (hd2 : Dec prof.feat ms2 (j + 6) (FV7z.mk (.sse .movdqu) 32 [.mem (mbd 7 0 128), .xmm 0] 4))
    (hd3 : Dec prof.feat ms2 (j + 6 + 4) (FV7z.mk .ret 64 [] 1)) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add j) (hI : Inv g₀ Y) (hdx : Y.cpu.gpr.rdx = g₀.rdx)
    (h16 : 16 ≤ g₀.rdx.toNat) (h32 : g₀.rdx.toNat ≤ 32) : GoG prof L o gev gP gE Y t := by
  refine stI c hin (by omega) hd1 C hK hA hrip hI (FillP.start _ _ _ _) hdx (k := 16) rfl h16 (Nat.le_refl _) ?_
  intro Y₁ t₁ V₁ hK₁ hA₁ hr₁ _ hI₁ hF₁
  refine stD c hin (by omega) hd2 C hK₁ hA₁ hr₁ hI₁ hF₁ (by omega) ?_
  intro Y₂ t₂ V₂ hK₂ hA₂ hr₂ _ hI₂ hF₂
  exact fin c hin (by omega) hd3 C hK₂ hA₂ hr₂ hI₂ hF₂ (by fill_cov)

/-- The loop's round from `+263`: `movdqa` of 64 bytes from `rdi + R`, `add rcx, 64`, `cmp rdx, rcx`, `jne +263`. -/
theorem round (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} {V₁ : Addr → Byte} {R E : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hrip : Y.cpu.rip = e.add 263) (hI : Inv g₀ Y)
    (hcx : Y.cpu.gpr.rcx = g₀.rdi.add R) (hdx : Y.cpu.gpr.rdx = g₀.rdi.add E) (hal : (g₀.rdi.toNat + R) % 64 = 0)
    (hRE : R + 64 ≤ E) (hEn : E ≤ g₀.rdx.toNat) (hF : FillG V V₁ g₀ fun i => i < R ∨ g₀.rdx.toNat - 64 ≤ i)
    (K : ∀ Y' t' V₂, KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem V₂ → Inv g₀ Y' →
      Y'.cpu.gpr.rcx = g₀.rdi.add (R + 64) → Y'.cpu.gpr.rdx = g₀.rdi.add E →
      FillG V V₂ g₀ (fun i => i < R + 64 ∨ g₀.rdx.toNat - 64 ≤ i) →
      (Y'.cpu.rip = e.add 263 ∧ E ≠ R + 64) ∨ (Y'.cpu.rip = e.add 291 ∧ E = R + 64) →
      GoG prof L o gev gP gE Y' t') : GoG prof L o gev gP gE Y t := by
  have h16 : (g₀.rdi.toNat + R) % 16 = 0 := by omega
  refine stA c hin (by ms2_lt) (d263 prof.feat) C hK hA hrip hI hF hcx h16 (by decide) (by omega) ?_
  intro Y₁ t₁ V₂ hK₁ hA₁ hr₁ hg₁ hI₁ hF₁
  have hcx₁ : Y₁.cpu.gpr.rcx = g₀.rdi.add R := by rw [hg₁]; exact hcx
  have hdx₁ : Y₁.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₁]; exact hdx
  refine stA c hin (by ms2_lt) (d267 prof.feat) C hK₁ hA₁ hr₁ hI₁ hF₁ hcx₁ h16 (by decide) (by omega) ?_
  intro Y₂ t₂ V₃ hK₂ hA₂ hr₂ hg₂ hI₂ hF₂
  have hcx₂ : Y₂.cpu.gpr.rcx = g₀.rdi.add R := by rw [hg₂]; exact hcx₁
  have hdx₂ : Y₂.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₂]; exact hdx₁
  refine stA c hin (by ms2_lt) (d272 prof.feat) C hK₂ hA₂ hr₂ hI₂ hF₂ hcx₂ h16 (by decide) (by omega) ?_
  intro Y₃ t₃ V₄ hK₃ hA₃ hr₃ hg₃ hI₃ hF₃
  have hcx₃ : Y₃.cpu.gpr.rcx = g₀.rdi.add R := by rw [hg₃]; exact hcx₂
  have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₃]; exact hdx₂
  refine stA c hin (by ms2_lt) (d277 prof.feat) C hK₃ hA₃ hr₃ hI₃ hF₃ hcx₃ h16 (by decide) (by omega) ?_
  intro Y₄ t₄ V₅ hK₄ hA₄ hr₄ hg₄ hI₄ hF₄
  have hcx₄ : Y₄.cpu.gpr.rcx = g₀.rdi.add R := by rw [hg₄]; exact hcx₃
  have hdx₄ : Y₄.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₄]; exact hdx₃
  have hF₅ : FillG V V₅ g₀ fun i => i < R + 64 ∨ g₀.rdx.toNat - 64 ≤ i :=
    FillP.mono hF₄ fun i _ h => by omega
  -- `add rcx, 64`, `cmp rdx, rcx`
  refine c.s_blkV hin (b282 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ hv₅
  simp only [wr, gv, Src.val, get1, get2, set_rcx, addR_eq, BitVec.setWidth_eq] at hg₅ hP
  have hc' : Y₄.cpu.gpr.rcx + BitVec.ofNat 64 64 = g₀.rdi.add (R + 64) := by
    rw [hcx₄, ← addr_add_add]; rfl
  have hI₅ : Inv g₀ Y₅ := hI₄.rcx hg₅ hv₅
  have hcx₅ : Y₅.cpu.gpr.rcx = g₀.rdi.add (R + 64) := by rw [hg₅]; exact hc'
  have hdx₅ : Y₅.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₅]; exact hdx₄
  have hz : fl.zf = decide (g₀.rdi.add E = g₀.rdi.add (R + 64)) := by
    rw [hP, subF_zf, hdx₄]; exact congrArg (fun y => decide (g₀.rdi.add E = y)) hc'
  refine c.s_jccV hK₅ hA₅ hin (by ms2_lt) hr₅ (d289 prof.feat) (tgt := 263) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, cond_5, hz] at htk
    exact K Y₆ t₆ V₅ hK₆ hA₆ (hI₅.of hg₆ hv₆) (by rw [hg₆]; exact hcx₅) (by rw [hg₆]; exact hdx₅) hF₅
      (.inl ⟨hr₆, fun h => by rw [h] at htk; simp at htk⟩)
  · intro hfa Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, cond_5, hz] at hfa
    have heq := congrArg BitVec.toNat (nb_f hfa)
    rw [toNat_add_of_fits (a := g₀.rdi) (i := E) (n := g₀.rdx.toNat + 1) (by omega) (by have := C.ov; omega),
      toNat_add_of_fits (a := g₀.rdi) (i := R + 64) (n := g₀.rdx.toNat + 1) (by omega)
        (by have := C.ov; omega)] at heq
    exact K Y₆ t₆ V₅ hK₆ hA₆ (hI₅.of hg₆ hv₆) (by rw [hg₆]; exact hcx₅) (by rw [hg₆]; exact hdx₅) hF₅
      (.inr ⟨hr₆, by omega⟩)

/-- The loop from `+263`, `m + 1` rounds to go: every byte below `rdi + E` from `rdi + R` filled, then `ret`. -/
theorem rounds (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) (m : Nat) : ∀ {Y : State} {t : Nat} {V₁ : Addr → Byte} {R E : Nat},
    KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V₁ → Y.cpu.rip = e.add 263 → Inv g₀ Y →
    Y.cpu.gpr.rcx = g₀.rdi.add R → Y.cpu.gpr.rdx = g₀.rdi.add E → (g₀.rdi.toNat + R) % 64 = 0 →
    E = R + 64 * (m + 1) → E ≤ g₀.rdx.toNat → g₀.rdx.toNat < E + 64 →
    FillG V V₁ g₀ (fun i => i < R ∨ g₀.rdx.toNat - 64 ≤ i) → GoG prof L o gev gP gE Y t := by
  induction m with
  | zero =>
    intro Y t V₁ R E hK hA hrip hI hcx hdx hal hE hEn hnE hF
    refine round c hin C hK hA hrip hI hcx hdx hal (by omega) hEn hF ?_
    intro Y' t' V₂ hK' hA' hI' _ _ hF' h
    rcases h with ⟨_, h⟩ | ⟨hr', hE'⟩
    · exact absurd (show E = R + 64 by omega) h
    · exact fin c hin (by ms2_lt) (d291 prof.feat) C hK' hA' hr' hI' hF' (by fill_cov)
  | succ m ih =>
    intro Y t V₁ R E hK hA hrip hI hcx hdx hal hE hEn hnE hF
    refine round c hin C hK hA hrip hI hcx hdx hal (by omega) hEn hF ?_
    intro Y' t' V₂ hK' hA' hI' hcx' hdx' hF' h
    rcases h with ⟨hr', _⟩ | ⟨_, h⟩
    · exact ih hK' hA' hr' hI' hcx' hdx' (by omega) (by omega) hEn hnE hF'
    · exact absurd h (by omega)

/-- From `+172`, `n > 32`: above 64 to `+200` (`p200`), else four stores of `xmm0` and `ret`. -/
theorem p200 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 200) (hI : Inv g₀ Y) (hdx : Y.cpu.gpr.rdx = g₀.rdx)
    (hn : 64 < g₀.rdx.toNat) : GoG prof L o gev gP gE Y t := by
  have hov := C.ov
  -- `lea rcx, [rdi + 64]`
  refine c.s_blkV hin (b200 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, BitVec.setWidth_eq, set_rcx] at hg₁
  have hI₁ : Inv g₀ Y₁ := hI.rcx hg₁ hv₁
  have hdx₁ : Y₁.cpu.gpr.rdx = g₀.rdx := by rw [hg₁]; exact hdx
  have hcx₁ : Y₁.cpu.gpr.rcx.toNat = g₀.rdi.toNat + 64 := by rw [hg₁]; exact eaG_64 hI.2.2.1 (by omega)
  -- `movdqu [rdi], xmm0`
  refine stD c hin (by ms2_lt) (d204 prof.feat) C hK₁ hA₁ hr₁ hI₁ (FillP.start _ _ _ _) (by omega) ?_
  intro Y₂ t₂ V₂ hK₂ hA₂ hr₂ hg₂ hI₂ hF₂
  -- `and rcx, -64`
  refine c.s_blkV hin (b208 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  simp only [wr, gv, Src.val, get1, set_rcx, BitVec.setWidth_eq] at hg₃
  have hI₃ : Inv g₀ Y₃ := hI₂.rcx hg₃ hv₃
  have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdx := by rw [hg₃]; show Y₂.cpu.gpr.rdx = _; rw [hg₂]; exact hdx₁
  have hcx₃ : Y₃.cpu.gpr.rcx = g₀.rdi.add ((g₀.rdi.toNat + 64) / 64 * 64 - g₀.rdi.toNat) := by
    rw [hg₃]
    exact and_al (by rw [hg₂]; exact hcx₁) (by omega) (Nat.le_refl _)
  generalize hR0 : (g₀.rdi.toNat + 64) / 64 * 64 - g₀.rdi.toNat = R0 at hcx₃
  -- the last 64 bytes and the first 64
  refine stI c hin (by ms2_lt) (d212 prof.feat) C hK₃ hA₃ hr₃ hI₃ hF₂ hdx₃ (k := 16) rfl (by omega) (by omega) ?_
  intro Y₄ t₄ V₄ hK₄ hA₄ hr₄ hg₄ hI₄ hF₄
  refine stD c hin (by ms2_lt) (d218 prof.feat) C hK₄ hA₄ hr₄ hI₄ hF₄ (by omega) ?_
  intro Y₅ t₅ V₅ hK₅ hA₅ hr₅ hg₅ hI₅ hF₅
  have hdx₅ : Y₅.cpu.gpr.rdx = g₀.rdx := by rw [hg₅, hg₄]; exact hdx₃
  refine stI c hin (by ms2_lt) (d223 prof.feat) C hK₅ hA₅ hr₅ hI₅ hF₅ hdx₅ (k := 32) rfl (by omega) (by omega) ?_
  intro Y₆ t₆ V₆ hK₆ hA₆ hr₆ hg₆ hI₆ hF₆
  refine stD c hin (by ms2_lt) (d229 prof.feat) C hK₆ hA₆ hr₆ hI₆ hF₆ (by omega) ?_
  intro Y₇ t₇ V₇ hK₇ hA₇ hr₇ hg₇ hI₇ hF₇
  have hdx₇ : Y₇.cpu.gpr.rdx = g₀.rdx := by rw [hg₇, hg₆]; exact hdx₅
  refine stI c hin (by ms2_lt) (d234 prof.feat) C hK₇ hA₇ hr₇ hI₇ hF₇ hdx₇ (k := 48) rfl (by omega) (by omega) ?_
  intro Y₈ t₈ V₈ hK₈ hA₈ hr₈ hg₈ hI₈ hF₈
  refine stD c hin (by ms2_lt) (d240 prof.feat) C hK₈ hA₈ hr₈ hI₈ hF₈ (by omega) ?_
  intro Y₉ t₉ V₉ hK₉ hA₉ hr₉ hg₉ hI₉ hF₉
  have hdx₉ : Y₉.cpu.gpr.rdx = g₀.rdx := by rw [hg₉, hg₈]; exact hdx₇
  refine stI c hin (by ms2_lt) (d245 prof.feat) C hK₉ hA₉ hr₉ hI₉ hF₉ hdx₉ (k := 64) rfl (by omega) (by omega) ?_
  intro Y₁₀ t₁₀ V₁₀ hK₁₀ hA₁₀ hr₁₀ hg₁₀ hI₁₀ hF₁₀
  have hdx₁₀ : Y₁₀.cpu.gpr.rdx = g₀.rdx := by rw [hg₁₀]; exact hdx₉
  have hcx₁₀ : Y₁₀.cpu.gpr.rcx = g₀.rdi.add R0 := by
    rw [hg₁₀, hg₉, hg₈, hg₇, hg₆, hg₅, hg₄]; exact hcx₃
  -- `add rdx, rdi`, `and rdx, -64`, `cmp rcx, rdx`
  refine c.s_blkV hin (b251 prof) hK₁₀ hA₁₀ hr₁₀ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ hg₁₁ hf₁₁ hv₁₁
  simp only [wr, gv, Src.val, get1, get2, get7, set_rdx, addR_eq, BitVec.setWidth_eq] at hg₁₁ hP
  have hE : (Y₁₀.cpu.gpr.rdx + Y₁₀.cpu.gpr.rdi) &&& BitVec.ofNat 64 18446744073709551552 =
      g₀.rdi.add ((g₀.rdi.toNat + g₀.rdx.toNat) / 64 * 64 - g₀.rdi.toNat) :=
    and_al (by rw [hdx₁₀, hI₁₀.2.2.1, BitVec.toNat_add]; omega) (by omega) (by omega)
  generalize hE0 : (g₀.rdi.toNat + g₀.rdx.toNat) / 64 * 64 - g₀.rdi.toNat = E at hE
  have hI₁₁ : Inv g₀ Y₁₁ := hI₁₀.rdx hg₁₁ hv₁₁
  have hdx₁₁ : Y₁₁.cpu.gpr.rdx = g₀.rdi.add E := by rw [hg₁₁]; exact hE
  have hcx₁₁ : Y₁₁.cpu.gpr.rcx = g₀.rdi.add R0 := by rw [hg₁₁]; exact hcx₁₀
  have hz : fl.zf = decide (g₀.rdi.add R0 = g₀.rdi.add E) := by
    rw [hP, subF_zf, hcx₁₀]; exact congrArg (fun y => decide (g₀.rdi.add R0 = y)) hE
  have hR0n : R0 < g₀.rdx.toNat + 1 := by omega
  have hEn : E < g₀.rdx.toNat + 1 := by omega
  refine c.s_jccV hK₁₁ hA₁₁ hin (by ms2_lt) hr₁₁ (d261 prof.feat) (tgt := 199) rfl (by ms2_lt) ?_ ?_
  · -- `rcx = rdx`: no round, `n < 128`
    intro htk Y₁₂ t₁₂ hK₁₂ hA₁₂ ⟨hr₁₂, hg₁₂, hv₁₂⟩
    rw [hf₁₁, cond_4, hz] at htk
    have heq := congrArg BitVec.toNat (of_decide_eq_true htk)
    rw [toNat_add_of_fits (a := g₀.rdi) (i := R0) hR0n (by omega),
      toNat_add_of_fits (a := g₀.rdi) (i := E) hEn (by omega)] at heq
    exact fin c hin (by ms2_lt) (d199 prof.feat) C hK₁₂ hA₁₂ hr₁₂ (hI₁₁.of hg₁₂ hv₁₂) hF₁₀ (by fill_cov)
  · intro hfa Y₁₂ t₁₂ hK₁₂ hA₁₂ ⟨hr₁₂, hg₁₂, hv₁₂⟩
    rw [hf₁₁, cond_4, hz] at hfa
    have hne : R0 ≠ E := fun h => by rw [h] at hfa; simp at hfa
    exact rounds c hin C ((E - R0) / 64 - 1) hK₁₂ hA₁₂ hr₁₂ (hI₁₁.of hg₁₂ hv₁₂) (by rw [hg₁₂]; exact hcx₁₁)
      (by rw [hg₁₂]; exact hdx₁₁) (by omega) (by omega) (by omega) (by omega)
      (FillP.mono hF₁₀ fun i _ h => by omega)

/-- From `+172`, `n > 32`: above 64 to `+200` (`p200`), else four stores of `xmm0` and `ret`. -/
theorem p172 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {g₀ : Gprs}
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 172) (hI : Inv g₀ Y) (hdx : Y.cpu.gpr.rdx = g₀.rdx)
    (hn : 32 < g₀.rdx.toNat) : GoG prof L o gev gP gE Y t := by
  -- `cmp rdx, 64`
  refine c.s_blkV hin (b172 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have hI₁ := hI.ofx hg₁ hv₁
  have hdx₁ : Y₁.cpu.gpr.rdx = g₀.rdx := by rw [hg₁]; exact hdx
  refine c.s_jccV hK₁ hA₁ hin (by ms2_lt) hr₁ (d176 prof.feat) (tgt := 200) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hf₁, hP, cond_7, subF_cf, subF_zf, hdx] at htk
    have h := ja_t htk
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    exact p200 c hin C hK₂ hA₂ hr₂ (hI₁.of hg₂ hv₂) (by rw [hg₂]; exact hdx₁) h
  · intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hf₁, hP, cond_7, subF_cf, subF_zf, hdx] at hfa
    have h := ja_f hfa
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have hI₂ := hI₁.of hg₂ hv₂
    have hdx₂ : Y₂.cpu.gpr.rdx = g₀.rdx := by rw [hg₂]; exact hdx₁
    refine stD c hin (by ms2_lt) (d178 prof.feat) C hK₂ hA₂ hr₂ hI₂ (FillP.start _ _ _ _) (by omega) ?_
    intro Y₃ t₃ V₃ hK₃ hA₃ hr₃ hg₃ hI₃ hF₃
    refine stD c hin (by ms2_lt) (d182 prof.feat) C hK₃ hA₃ hr₃ hI₃ hF₃ (by omega) ?_
    intro Y₄ t₄ V₄ hK₄ hA₄ hr₄ hg₄ hI₄ hF₄
    have hdx₄ : Y₄.cpu.gpr.rdx = g₀.rdx := by rw [hg₄, hg₃]; exact hdx₂
    refine stI c hin (by ms2_lt) (d187 prof.feat) C hK₄ hA₄ hr₄ hI₄ hF₄ hdx₄ (k := 16) rfl (by omega) (by omega) ?_
    intro Y₅ t₅ V₅ hK₅ hA₅ hr₅ hg₅ hI₅ hF₅
    refine stI c hin (by ms2_lt) (d193 prof.feat) C hK₅ hA₅ hr₅ hI₅ hF₅ (by rw [hg₅]; exact hdx₄) (k := 32) rfl
      (by omega) (by omega) ?_
    intro Y₆ t₆ V₆ hK₆ hA₆ hr₆ _ hI₆ hF₆
    exact fin c hin (by ms2_lt) (d199 prof.feat) C hK₆ hA₆ hr₆ hI₆ hF₆ (by fill_cov)

/-! ## The entries -/

/-- `endbr64`, the spread into `xmm0`, `rax = rdi`, `cmp rdx, 16` (at `+0` and at `+112`). -/
theorem head (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j : Nat} (hb1 : BlkV prof ms2 j (j + 15) o0)
    (hb2 : BlkV prof ms2 (j + 15) (j + 28) o15) {X : State} {t : Nat} {g₀ : Gprs} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add j) (hg : X.cpu.gpr = g₀)
    (K : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e.add (j + 28) → Inv g₀ Y →
      Y.cpu.gpr.rdx = g₀.rdx → Y.cpu.gpr.rsi = g₀.rsi → Y.cpu.rflags.cf = decide (g₀.rdx.toNat < 16) →
      GoG prof L o gev gP gE Y t') : GoG prof L o gev gP gE X t := by
  refine c.s_blkV hin hb1 hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_v0 (wpV_nil ?_))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, get6, get7, BitVec.setWidth_eq] at hg₁ hv₁
  refine c.s_blkV hin hb2 hK₁ hA₁ hr₁ ?_
  refine wpV_v0 (wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP hg₂
  refine K Y₂ t₂ hK₂ hA₂ hr₂ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hg₂, hg₁, hg]
  · simp only [hg₂, hg₁, hg]
  · simp only [hg₂, hg₁, hg]
  · rw [hv₂, hv₁, ← hg]
    simp (disch := decide) only [xset_same]
  · simp only [hg₂, hg₁, hg]
  · simp only [hg₂, hg₁, hg]
  · rw [hf₂, hP, subF_cf]
    simp only [hg₁, hg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

/-- `__memset_sse2_unaligned` from `+0`, called with registers `g₀`. -/
theorem sse2u (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 0) (hg : X.cpu.gpr = g₀)
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) : GoG prof L o gev gP gE X t := by
  refine head c hin (j := 0) (b0 prof) (b15 prof) hK hA hrip hg ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hI₂ hdx₂ _ hcf
  refine c.s_jccV hK₂ hA₂ hin (by ms2_lt) hr₂ (d28 prof.feat) (tgt := 293) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [cond_2, hcf] at htk
    exact p293 c hin C hK₃ hA₃ hr₃ (hI₂.of hg₃ hv₃) (by rw [hg₃]; exact hdx₂) (of_decide_eq_true htk)
  intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
  rw [cond_2, hcf] at hfa
  have h16 := Nat.le_of_not_lt (of_decide_eq_false hfa)
  have hI₃ := hI₂.of hg₃ hv₃
  have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdx := by rw [hg₃]; exact hdx₂
  -- `cmp rdx, 32`
  refine c.s_blkV hin (b34 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ hv₄
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have hI₄ := hI₃.ofx hg₄ hv₄
  have hdx₄ : Y₄.cpu.gpr.rdx = g₀.rdx := by rw [hg₄]; exact hdx₃
  refine c.s_jccV hK₄ hA₄ hin (by ms2_lt) hr₄ (d38 prof.feat) (tgt := 172) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
    rw [hf₄, hP, cond_7, subF_cf, subF_zf, hdx₃] at htk
    have h := ja_t htk
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    exact p172 c hin C hK₅ hA₅ hr₅ (hI₄.of hg₅ hv₅) (by rw [hg₅]; exact hdx₄) h
  · intro hfa Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
    rw [hf₄, hP, cond_7, subF_cf, subF_zf, hdx₃] at hfa
    have h := ja_f hfa
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    exact p16 c hin (by ms2_lt) (d44 prof.feat) (d50 prof.feat) (d54 prof.feat) C hK₅ hA₅ hr₅ (hI₄.of hg₅ hv₅)
      (by rw [hg₅]; exact hdx₄) h16 h

/-- `__memset_sse2_unaligned_erms` from `+112`, called with registers `g₀`. -/
theorem sse2ue (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 112) (hg : X.cpu.gpr = g₀)
    (C : Ctx prof F Wl L s₀ o gev gP gE V g₀) (hdf₀ : s₀.cpu.rflags.df = false) : GoG prof L o gev gP gE X t := by
  refine head c hin (j := 112) (b112 prof) (b127 prof) hK hA hrip hg ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hI₂ hdx₂ hsi₂ hcf
  refine c.s_jccV hK₂ hA₂ hin (by ms2_lt) hr₂ (d140 prof.feat) (tgt := 293) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [cond_2, hcf] at htk
    exact p293 c hin C hK₃ hA₃ hr₃ (hI₂.of hg₃ hv₃) (by rw [hg₃]; exact hdx₂) (of_decide_eq_true htk)
  intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
  rw [cond_2, hcf] at hfa
  have h16 := Nat.le_of_not_lt (of_decide_eq_false hfa)
  have hI₃ := hI₂.of hg₃ hv₃
  have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdx := by rw [hg₃]; exact hdx₂
  have hsi₃ : Y₃.cpu.gpr.rsi = g₀.rsi := by rw [hg₃]; exact hsi₂
  -- `cmp rdx, 32`
  refine c.s_blkV hin (b146 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ hv₄
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have hI₄ := hI₃.ofx hg₄ hv₄
  have hdx₄ : Y₄.cpu.gpr.rdx = g₀.rdx := by rw [hg₄]; exact hdx₃
  have hsi₄ : Y₄.cpu.gpr.rsi = g₀.rsi := by rw [hg₄]; exact hsi₃
  refine c.s_jccV hK₄ hA₄ hin (by ms2_lt) hr₄ (d150 prof.feat) (tgt := 163) rfl (by ms2_lt) ?_ ?_
  · intro htk Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
    rw [hf₄, hP, cond_7, subF_cf, subF_zf, hdx₃] at htk
    have h := ja_t htk
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have hI₅ := hI₄.of hg₅ hv₅
    have hdx₅ : Y₅.cpu.gpr.rdx = g₀.rdx := by rw [hg₅]; exact hdx₄
    have hsi₅ : Y₅.cpu.gpr.rsi = g₀.rsi := by rw [hg₅]; exact hsi₄
    -- `cmp rdx, 2048`
    refine c.s_blkV hin (b163 prof) hK₅ hA₅ hr₅ ?_
    refine wpV_reg fun fl hP => wpV_nil ?_
    intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ hf₆ hv₆
    simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
    have hI₆ := hI₅.ofx hg₆ hv₆
    have hdx₆ : Y₆.cpu.gpr.rdx = g₀.rdx := by rw [hg₆]; exact hdx₅
    have hsi₆ : Y₆.cpu.gpr.rsi = g₀.rsi := by rw [hg₆]; exact hsi₅
    refine c.s_jccV hK₆ hA₆ hin (by ms2_lt) hr₆ (d170 prof.feat) (tgt := 93) rfl (by ms2_lt) ?_ ?_
    · -- more than 2048 bytes: `rep stosb`
      intro htk Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, hv₇⟩
      rw [hf₆, hP, cond_7, subF_cf, subF_zf, hdx₅] at htk
      have h' := ja_t htk
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h'
      obtain ⟨k, hk⟩ : ∃ k, g₀.rdx.toNat = k + 1 := ⟨g₀.rdx.toNat - 1, by omega⟩
      have hI₇ := hI₆.of hg₇ hv₇
      exact from93 c hin hK₇ hA₇ hr₇ hI₇.1 hI₇.2.2.1 (by rw [hg₇]; exact hsi₆) (by rw [hg₇]; exact hdx₆) hk C.st
        (Nat.le_of_lt C.ov) C.sp hdf₀ C.sp8 C.ret
    · intro hfa Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, hv₇⟩
      exact p172 c hin C hK₇ hA₇ hr₇ (hI₆.of hg₇ hv₇) (by rw [hg₇]; exact hdx₆) h
  · intro hfa Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
    rw [hf₄, hP, cond_7, subF_cf, subF_zf, hdx₃] at hfa
    have h := ja_f hfa
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    exact p16 c hin (by ms2_lt) (d152 prof.feat) (d158 prof.feat) (d162 prof.feat) C hK₅ hA₅ hr₅
      (hI₄.of hg₅ hv₅) (by rw [hg₅]; exact hdx₄) h16 h

/-- A call of `__memset_sse2_unaligned` does what `SetAtD` says. -/
theorem setAtD_sse2u {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e ms2) : SetAtD prof L o (e.add 0) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j c hK hA hrip _ hin₂ hj hra hl hst hov hsp hdf hsp8 K
  exact sse2u (g₀ := X.cpu.gpr) c hin hK hA hrip rfl ⟨hst, hov, hsp, hsp8, hl, e', code, j, hin₂, hj, hra, K⟩

/-- A call of `__memset_sse2_unaligned_erms` does what `SetAtD` says. -/
theorem setAtD_sse2ue {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e ms2) : SetAtD prof L o (e.add 112) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j c hK hA hrip _ hin₂ hj hra hl hst hov hsp hdf hsp8 K
  exact sse2ue (g₀ := X.cpu.gpr) c hin hK hA hrip rfl ⟨hst, hov, hsp, hsp8, hl, e', code, j, hin₂, hj, hra, K⟩
    (hK.df.symm.trans hdf)

end FV7z.Memset
