import FV7z.Dtu.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Signed
/-!
# `do_tunable_update_val` (PLAN.md G3, startup)

glibc 2.31's `do_tunable_update_val (cur, valp)` at `0x66ed50` in `7zzs` (`elf/dl-tunables.c`; `objdump -d`), a leaf
without a frame, for the tunable at `p` = `rdi` and the value at `rsi`. Its type is the 4 bytes at `p + 8`:

- 3 (a string): `rsi` itself stored at `p + 32` (52).
- otherwise the value `v`, the 8 bytes at `rsi` (into `rdx`), against the bounds `lo` and `hi` at `p + 16` and
  `p + 24`: as signed numbers for the type 0 (`jl`/`jg`, 56 to 76) and unsigned for the others (`jb`/`ja`, 18 to 38).
  In range (`InR`): `v` stored at `p + 32` and the byte 1 at `p + 40` (`initialized`); otherwise nothing.

`Mo` is the bytes after it, `gO` the registers at the `ret` (`rax` the type zero-extended, `rdx` the value but for
strings). Three `ret`s (38, 52, 76).

- `P0`: what the code from the entry leaves at the cut point 18 (an unsigned type, `rax` and `rdx` loaded) or at a
  `ret`; `vc_0` proves it. `P18`, `vc_18`: from 18 to a `ret`. The closers `k*` and `m*` each take one path's
  conditions as `wpx` leaves them (with `decide` turned into propositions).
- `subF_l64`, `subF_g64`: `jl`, `jg` after a 64-bit `cmp` (the 32-bit `subF_g32`'s proof).
- `dtu_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dtu

set_option linter.unusedSimpArgs false

/-- `jg` after `cmp x, y` (64 bits): signed greater. -/
theorem subF_g64 (f : Rflags) (x y : BitVec 64) : (subF f x y).cond 15 = decide (y.toInt < x.toInt) := by
  rw [cond_15, subF_zf', subF_sf, subF_of, overflowSub]
  have ex := BitVec.msb_eq_decide x
  have ey := BitVec.msb_eq_decide y
  have er := BitVec.msb_eq_decide (x - y)
  have hz : (x - y == 0) = decide (x.toNat = y.toNat) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    exact ⟨fun h => by bv_omega, fun h => by bv_omega⟩
  rw [hz, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  rw [BitVec.toNat_sub] at er
  have hx := x.isLt
  have hy := y.isLt
  cases hmx : x.msb <;> cases hmy : y.msb <;> cases hmr : (x - y).msb <;> rw [hmx] at ex <;> rw [hmy] at ey <;>
    rw [hmr] at er <;>
    simp only [Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq] at ex ey er <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

/-- `jl` after `cmp x, y` (64 bits): signed less. -/
theorem subF_l64 (f : Rflags) (x y : BitVec 64) : (subF f x y).cond 12 = decide (x.toInt < y.toInt) := by
  have e : (subF f x y).cond 12 = ((subF f x y).sf != (subF f x y).of) := rfl
  rw [e, subF_sf, subF_of, overflowSub]
  have ex := BitVec.msb_eq_decide x
  have ey := BitVec.msb_eq_decide y
  have er := BitVec.msb_eq_decide (x - y)
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  rw [BitVec.toNat_sub] at er
  have hx := x.isLt
  have hy := y.isLt
  cases hmx : x.msb <;> cases hmy : y.msb <;> cases hmr : (x - y).msb <;> rw [hmx] at ex <;> rw [hmy] at ey <;>
    rw [hmr] at er <;>
    simp only [Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq] at ex ey er <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr_38 : pret <+: dtu.drop 38 := by decide +kernel
theorem wr_52 : pret <+: dtu.drop 52 := by decide +kernel
theorem wr_76 : pret <+: dtu.drop 76 := by decide +kernel
theorem ret_j (feat : Features) {j : Nat} (hj : j = 38 ∨ j = 52 ∨ j = 76) : Dec feat dtu j (FV7z.mk .ret 64 [] 1) := by
  rcases hj with rfl | rfl | rfl
  · exact Dec.shift (j := 38) (k := 0) (pret_0 feat) wr_38 (Nat.zero_le _)
  · exact Dec.shift (j := 52) (k := 0) (pret_0 feat) wr_52 (Nat.zero_le _)
  · exact Dec.shift (j := 76) (k := 0) (pret_0 feat) wr_76 (Nat.zero_le _)

/-- The type, at `p + 8`. -/
local notation "dty(" V ", " g ")" => ofBytesLE 32 (List.map V (byteAddrs (Gprs.rdi g + 8#64) 4))
/-- The value, at `rsi`. -/
local notation "dv(" V ", " g ")" => ofBytesLE 64 (List.map V (byteAddrs (Gprs.rsi g) 8))
/-- The lower bound, at `p + 16`. -/
local notation "dlo(" V ", " g ")" => ofBytesLE 64 (List.map V (byteAddrs (Gprs.rdi g + 16#64) 8))
/-- The upper bound, at `p + 24`. -/
local notation "dhi(" V ", " g ")" => ofBytesLE 64 (List.map V (byteAddrs (Gprs.rdi g + 24#64) 8))

/-- The value in range: signed for the type 0, unsigned for the others. -/
def InR (V : Addr → Byte) (g : Gprs) : Bool :=
  if dty(V, g) = 0#32 then
    decide (BitVec.toInt dlo(V, g) ≤ BitVec.toInt dv(V, g) ∧ BitVec.toInt dv(V, g) ≤ BitVec.toInt dhi(V, g))
  else decide (BitVec.toNat dlo(V, g) ≤ BitVec.toNat dv(V, g) ∧ BitVec.toNat dv(V, g) ≤ BitVec.toNat dhi(V, g))

/-- The bytes after it. -/
def Mo (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if dty(V, g) = 3#32 then Vst V (g.rdi + 32#64) (toBytesLE g.rsi 8)
  else if InR V g then Vst (Vst V (g.rdi + 32#64) (toBytesLE dv(V, g) 8)) (g.rdi + 40#64) (toBytesLE 1#8 1)
  else V

/-- The registers at the `ret`. -/
def gO (V : Addr → Byte) (g : Gprs) : Gprs :=
  if dty(V, g) = 3#32 then { g with rax := BitVec.setWidth 64 dty(V, g) }
  else { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) }

theorem gO_rsp {V : Addr → Byte} {g : Gprs} : (gO V g).rsp = g.rsp := by
  unfold gO
  split <;> rfl

theorem gO_n {V : Addr → Byte} {g : Gprs} (h3 : dty(V, g) ≠ 3#32) :
    gO V g = { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } := by
  rw [gO, if_neg h3]

/-- The bytes read and stored. -/
structure Ft (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (g : Gprs) : Prop where
  f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)
  fs : dty(V, g) ≠ 3#32 → ∀ i < 8, Foot F.data (Addr.add g.rsi i)
  f16 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i)
  f24 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i)
  w32 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 32#64) i)
  w40 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 40#64) i)

/-! ## The range -/

section
variable {V : Addr → Byte} {g : Gprs}

theorem InR_s_in (h0 : dty(V, g) = 0#32) (hl : ¬ BitVec.toInt dv(V, g) < BitVec.toInt dlo(V, g))
    (hh : ¬ BitVec.toInt dhi(V, g) < BitVec.toInt dv(V, g)) : InR V g = true := by
  rw [InR, if_pos h0]
  exact decide_eq_true ⟨Int.not_lt.mp hl, Int.not_lt.mp hh⟩

theorem InR_s_lo (h0 : dty(V, g) = 0#32) (hl : BitVec.toInt dv(V, g) < BitVec.toInt dlo(V, g)) :
    InR V g = false := by
  rw [InR, if_pos h0]
  exact decide_eq_false (fun h => Int.not_le.mpr hl h.1)

theorem InR_s_hi (h0 : dty(V, g) = 0#32) (hh : BitVec.toInt dhi(V, g) < BitVec.toInt dv(V, g)) :
    InR V g = false := by
  rw [InR, if_pos h0]
  exact decide_eq_false (fun h => Int.not_le.mpr hh h.2)

theorem InR_u_in (h0 : ¬ dty(V, g) = 0#32) (hl : ¬ BitVec.toNat dv(V, g) < BitVec.toNat dlo(V, g))
    (hh : BitVec.toNat dv(V, g) < BitVec.toNat dhi(V, g) ∨ dv(V, g) = dhi(V, g)) : InR V g = true := by
  rw [InR, if_neg h0]
  refine decide_eq_true ⟨Nat.not_lt.mp hl, ?_⟩
  rcases hh with h | h
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq (congrArg BitVec.toNat h)

theorem InR_u_lo (h0 : ¬ dty(V, g) = 0#32) (hl : BitVec.toNat dv(V, g) < BitVec.toNat dlo(V, g)) :
    InR V g = false := by
  rw [InR, if_neg h0]
  exact decide_eq_false (fun h => Nat.not_le.mpr hl h.1)

theorem InR_u_hi (h0 : ¬ dty(V, g) = 0#32) (hh : ¬ BitVec.toNat dv(V, g) < BitVec.toNat dhi(V, g))
    (he : ¬ dv(V, g) = dhi(V, g)) : InR V g = false := by
  rw [InR, if_neg h0]
  exact decide_eq_false (fun h => he (BitVec.eq_of_toNat_eq (Nat.le_antisymm h.2 (Nat.not_lt.mp hh))))

theorem Mo_in (h3 : ¬ dty(V, g) = 3#32) (hr : InR V g = true) :
    Mo V g = Vst (Vst V (g.rdi + 32#64) (toBytesLE dv(V, g) 8)) (g.rdi + 40#64) (toBytesLE 1#8 1) := by
  rw [Mo, if_neg h3, if_pos hr]

theorem Mo_out (h3 : ¬ dty(V, g) = 3#32) (hr : InR V g = false) : Mo V g = V := by
  rw [Mo, if_neg h3, if_neg (fun h => absurd (hr.symm.trans h) Bool.false_ne_true)]

/-- The type 0 after `cmp eax, 1` and `jbe` taken. -/
theorem ty0 {x : BitVec 32} (h1 : ¬ x = 1#32) (h : x.toNat < 1 ∨ x = 1#32) : x = 0#32 := by
  rcases h with h | h
  · exact BitVec.eq_of_toNat_eq (by have e : (0#32 : BitVec 32).toNat = 0 := rfl; omega)
  · exact absurd h h1

end

/-! ## From the entry -/

/-- From the entry: at 18 with an unsigned type, `rax` and `rdx` loaded; or at a `ret`, done. -/
def P0 (V : Addr → Byte) (g : Gprs) (j : Nat) (g' : Gprs) (V' : Addr → Byte) : Prop :=
  (j = 18 ∧ dty(V, g) ≠ 0#32 ∧ dty(V, g) ≠ 3#32 ∧
    g' = { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } ∧ V' = V) ∨
  ((j = 38 ∨ j = 52 ∨ j = 76) ∧ g' = gO V g ∧ V' = Mo V g)

section
variable {V : Addr → Byte} {g : Gprs}

/-- A string (52). -/
theorem k48 (h : dty(V, g) = 3#32) :
    P0 V g 52 { g with rax := BitVec.setWidth 64 dty(V, g) } (Vst V (g.rdi + 32#64) (toBytesLE g.rsi 8)) :=
  Or.inr ⟨by decide, by rw [gO, if_pos h], by rw [Mo, if_pos h]⟩

/-- The type 1 (to 18). -/
theorem k14 (h3 : ¬ dty(V, g) = 3#32) (h1 : dty(V, g) = 1#32) :
    P0 V g 18 { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } V :=
  Or.inl ⟨rfl, fun h0 => absurd (h0.symm.trans h1) (by decide), h3, rfl, rfl⟩

/-- A type above 1 (to 18). -/
theorem k16 (h3 : ¬ dty(V, g) = 3#32) (h : ¬ BitVec.toNat dty(V, g) < 1) :
    P0 V g 18 { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } V :=
  Or.inl ⟨rfl, fun h0 => h (by rw [h0]; decide), h3, rfl, rfl⟩

/-- The type 0, below `lo` (52). -/
theorem k60 (h3 : ¬ dty(V, g) = 3#32) (h1 : ¬ dty(V, g) = 1#32)
    (h0 : BitVec.toNat dty(V, g) < 1 ∨ dty(V, g) = 1#32)
    (hl : BitVec.toInt dv(V, g) < BitVec.toInt dlo(V, g)) :
    P0 V g 52 { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } V :=
  Or.inr ⟨by decide, by rw [gO, if_neg h3], (Mo_out h3 (InR_s_lo (ty0 h1 h0) hl)).symm⟩

/-- The type 0, above `hi` (52). -/
theorem k66 (h3 : ¬ dty(V, g) = 3#32) (h1 : ¬ dty(V, g) = 1#32)
    (h0 : BitVec.toNat dty(V, g) < 1 ∨ dty(V, g) = 1#32)
    (hh : BitVec.toInt dhi(V, g) < BitVec.toInt dv(V, g)) :
    P0 V g 52 { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) } V :=
  Or.inr ⟨by decide, by rw [gO, if_neg h3], (Mo_out h3 (InR_s_hi (ty0 h1 h0) hh)).symm⟩

/-- The type 0, in range (76). -/
theorem k68 (h3 : ¬ dty(V, g) = 3#32) (h1 : ¬ dty(V, g) = 1#32)
    (h0 : BitVec.toNat dty(V, g) < 1 ∨ dty(V, g) = 1#32)
    (hl : ¬ BitVec.toInt dv(V, g) < BitVec.toInt dlo(V, g))
    (hh : ¬ BitVec.toInt dhi(V, g) < BitVec.toInt dv(V, g)) :
    P0 V g 76 { g with rax := BitVec.setWidth 64 dty(V, g), rdx := dv(V, g) }
      (Vst (Vst V (g.rdi + 32#64) (toBytesLE dv(V, g) 8)) (g.rdi + 40#64) (toBytesLE 1#8 1)) :=
  Or.inr ⟨by decide, by rw [gO, if_neg h3], (Mo_in h3 (InR_s_in (ty0 h1 h0) hl hh)).symm⟩

end

/-! ## From 18 -/

/-- From 18 (an unsigned type, `rdx` the value): at a `ret`, done. -/
def P18 (V : Addr → Byte) (g : Gprs) (j : Nat) (g' : Gprs) (V' : Addr → Byte) : Prop :=
  (j = 38 ∨ j = 52) ∧ g' = g ∧ V' = Mo V g

section
variable {V : Addr → Byte} {g : Gprs}

/-- Below `lo` (52). -/
theorem m22 (h0 : ¬ dty(V, g) = 0#32) (h3 : ¬ dty(V, g) = 3#32)
    (hl : BitVec.toNat dv(V, g) < BitVec.toNat dlo(V, g)) : P18 V g 52 g V :=
  ⟨Or.inr rfl, rfl, (Mo_out h3 (InR_u_lo h0 hl)).symm⟩

/-- Above `hi` (52). -/
theorem m28 (h0 : ¬ dty(V, g) = 0#32) (h3 : ¬ dty(V, g) = 3#32)
    (hh : ¬ BitVec.toNat dv(V, g) < BitVec.toNat dhi(V, g)) (he : ¬ dv(V, g) = dhi(V, g)) : P18 V g 52 g V :=
  ⟨Or.inr rfl, rfl, (Mo_out h3 (InR_u_hi h0 hh he)).symm⟩

/-- In range (38). -/
theorem m30 (h0 : ¬ dty(V, g) = 0#32) (h3 : ¬ dty(V, g) = 3#32)
    (hl : ¬ BitVec.toNat dv(V, g) < BitVec.toNat dlo(V, g))
    (hh : BitVec.toNat dv(V, g) < BitVec.toNat dhi(V, g) ∨ dv(V, g) = dhi(V, g)) :
    P18 V g 38 g (Vst (Vst V (g.rdi + 32#64) (toBytesLE dv(V, g) 8)) (g.rdi + 40#64) (toBytesLE 1#8 1)) :=
  ⟨Or.inl rfl, rfl, (Mo_in h3 (InR_u_in h0 hl hh)).symm⟩

end

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 800000 in
/-- From the entry to 18 or a `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hF : Ft F Wl V g) :
    W_0 F Wl (fun j' g' _ V' => P0 V g j' g' V') g f V := by
  obtain ⟨f8, fs, f16, f24, w32, w40⟩ := hF
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 fs f16 f24 w32 w40 ⊢
  wpx [W_0, W_8, W_16, W_48, W_56, W_62, W_68, o0, o1, o2, o3, o4, o5, subF_l64, subF_g64,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.or_eq_true, Bool.or_eq_false_iff, Bool.not_eq_true',
    Bool.not_eq_false', and_imp]
  all_goals repeat'
    (first
      | exact k48 ‹_›
      | exact k14 ‹_› ‹_›
      | exact k16 ‹_› ‹_›
      | exact k60 ‹_› ‹_› ‹_› ‹_›
      | exact k66 ‹_› ‹_› ‹_› ‹_›
      | exact k68 ‹_› ‹_› ‹_› ‹_› ‹_›
      | exact rfl
      | exact trivial
      | assumption
      | exact fs ‹_›
      | apply And.intro
      | intro _)

set_option maxHeartbeats 800000 in
/-- From 18 to a `ret`. -/
theorem vc_18 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hF : Ft F Wl V g) (h0 : dty(V, g) ≠ 0#32)
    (h3 : dty(V, g) ≠ 3#32) (hd : g.rdx = dv(V, g)) :
    W_18 F Wl (fun j' g' _ V' => P18 V g j' g' V') g f V := by
  obtain ⟨f8, fs, f16, f24, w32, w40⟩ := hF
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 fs f16 f24 w32 w40 h0 h3 hd ⊢
  subst hd
  wpx [W_18, W_24, W_30, o2, o3, o4, decide_eq_true_eq, decide_eq_false_iff_not, Bool.or_eq_true,
    Bool.or_eq_false_iff, Bool.not_eq_true', Bool.not_eq_false', and_imp]
  all_goals repeat'
    (first
      | exact m22 ‹_› ‹_› ‹_›
      | exact m28 ‹_› ‹_› ‹_› ‹_›
      | exact m30 ‹_› ‹_› ‹_› ‹_›
      | exact rfl
      | exact trivial
      | assumption
      | apply And.intro
      | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- At a `ret` with the registers `gO` and the bytes `Mo`: to the return address. -/
theorem dret (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dtu_at dtu) {g : Gprs} {Y : State}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem (Mo V g)) {j : Nat} (hj : j = 38 ∨ j = 52 ∨ j = 76)
    (hr : Y.cpu.rip = dtu_at.add j) (hg : Y.cpu.gpr = gO V g)
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Mo V g, g.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mo V g) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (gO V g).set 4 (g.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hsp : Y.cpu.gpr.rsp = g.rsp := by rw [hg]; exact gO_rsp
  refine c.s_ret hK hA hin (lt_len (by rcases hj with rfl | rfl | rfl <;> decide)) hr (ret_j _ hj)
    (by rw [hsp]; exact hl) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₃ hKZ hAZ hrZ (by rw [hgZ, hsp, hg])

/-- `do_tunable_update_val (cur, valp)` from its entry to the return address: the bytes `Mo`, the registers `gO` but
`rsp`. -/
theorem dtu_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dtu_at dtu) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dtu_at) (hF : Ft F Wl V X.cpu.gpr)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Mo V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mo V X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (gO V X.cpu.gpr).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => P0 V X.cpu.gpr j' g' V') hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hF) ?_
  rintro j' g fl V₁ hP Y t₁ hKY hAY hrY hgY -
  rcases hP with ⟨rfl, h0, h3, hg, rfl⟩ | ⟨hj, hg, rfl⟩
  · have e1 : Y.cpu.gpr = { X.cpu.gpr with rax := BitVec.setWidth 64 dty(V, X.cpu.gpr),
        rdx := dv(V, X.cpu.gpr) } := hgY.trans hg
    have hF' : Ft F Wl V Y.cpu.gpr := by
      rw [e1]
      exact ⟨hF.f8, hF.fs, hF.f16, hF.f24, hF.w32, hF.w40⟩
    refine (c_18 prof).run c hin (fun j' g' _ V' => P18 V Y.cpu.gpr j' g' V') hKY hAY hrY
      (vc_18 hF' (by rw [e1]; exact h0) (by rw [e1]; exact h3) (by rw [e1]; try rfl)) ?_
    rintro j₁ g₂ fl₂ V₂ ⟨hj, hg₂, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hgY₂ -
    have eM : Mo V Y.cpu.gpr = Mo V X.cpu.gpr := by
      rw [e1]
      try rfl
    rw [eM] at hA₂
    exact dret c hin hK₂ hA₂ (hj.elim Or.inl (fun h => Or.inr (Or.inl h))) hr₂
      (by rw [hgY₂, hg₂, e1, gO_n h3]) hl hin₂ h₂ hra k
  · exact dret c hin hKY hAY hj hrY (hgY.trans hg) hl hin₂ h₂ hra k

end FV7z.Dtu
