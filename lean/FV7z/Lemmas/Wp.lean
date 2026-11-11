import FV7z.Lemmas.Sp
/-!
# Evaluating `wp` (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

`wp` of a list of effects from registers given as sixteen values (`Gprs.mk`): `simp only` with the lemmas here
(`wpx`) runs the effects one after the other, each on the registers the one before left (the arguments are
simplified first, so no effect is applied to a state not yet computed), and leaves the accesses' side conditions and
the continuation on the registers, flags and bytes computed.
-/
namespace FV7z
open ZellicX86 Decode

/-! ## Registers -/

theorem gk0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 0) = a0 := rfl
theorem gk1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 1) = a1 := rfl
theorem gk2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 2) = a2 := rfl
theorem gk3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 3) = a3 := rfl
theorem gk4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 4) = a4 := rfl
theorem gk5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 5) = a5 := rfl
theorem gk6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 6) = a6 := rfl
theorem gk7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 7) = a7 := rfl
theorem gk8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 8) = a8 := rfl
theorem gk9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 9) = a9 := rfl
theorem gk10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 10) = a10 := rfl
theorem gk11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 11) = a11 := rfl
theorem gk12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 12) = a12 := rfl
theorem gk13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 13) = a13 := rfl
theorem gk14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 14) = a14 := rfl
theorem gk15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).get (regOf 15) = a15 := rfl
theorem sk0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 0) v = Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 1) v = Gprs.mk a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 2) v = Gprs.mk a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 3) v = Gprs.mk a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 4) v = Gprs.mk a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 5) v = Gprs.mk a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 6) v = Gprs.mk a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 7) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 8) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14 a15 := rfl
theorem sk9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 9) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14 a15 := rfl
theorem sk10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 10) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14 a15 := rfl
theorem sk11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 11) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14 a15 := rfl
theorem sk12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 12) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14 a15 := rfl
theorem sk13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 13) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14 a15 := rfl
theorem sk14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 14) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v a15 := rfl
theorem sk15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set (regOf 15) v = Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 v := rfl
theorem sk4' (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) : (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 4 v = Gprs.mk a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl
theorem rsp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsp = a4 := rfl

/-! ## Widths -/

theorem sw_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_64_16 (x : BitVec 32) : (x.setWidth 64).setWidth 16 = x.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_64_8 (x : BitVec 32) : (x.setWidth 64).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_64_64 (x : BitVec 64) : x.setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_32_32 (x : BitVec 32) : x.setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem sx_64_32 (x : BitVec 32) : (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_signExtend]
  have hx := x.isLt
  cases x.msb <;> simp <;> omega

theorem add_z64 (x : BitVec 64) : x + (0 : BitVec 64) = x := by simp
theorem z_mul64 (x : BitVec 64) : (0 : BitVec 64) * x = 0 := by simp
theorem z_add64 (x : BitVec 64) : (0 : BitVec 64) + x = x := by simp

/-- `imul r32, r32`: the low half of the signed product is the product. -/
theorem imul32 (x y : BitVec 32) : (x.signExtend 64 * y.signExtend 64).setWidth 32 = x * y := by
  rw [BitVec.setWidth_mul _ _ (by decide), sx_64_32, sx_64_32]

/-! ## Flags -/

theorem cond_2 (f : Rflags) : f.cond 2 = f.cf := rfl
theorem cond_3 (f : Rflags) : f.cond 3 = !f.cf := rfl
theorem cond_4 (f : Rflags) : f.cond 4 = f.zf := rfl
theorem cond_5 (f : Rflags) : f.cond 5 = !f.zf := rfl
theorem cond_6 (f : Rflags) : f.cond 6 = (f.cf || f.zf) := rfl
theorem cond_7 (f : Rflags) : f.cond 7 = !(f.cf || f.zf) := rfl
theorem cond_8 (f : Rflags) : f.cond 8 = f.sf := rfl
theorem cond_9 (f : Rflags) : f.cond 9 = !f.sf := rfl
theorem rfz_cf (f : Rflags) : (rfz f).cf = f.cf := rfl
theorem rfz_zf (f : Rflags) : (rfz f).zf = f.zf := rfl
theorem rfz_sf (f : Rflags) : (rfz f).sf = f.sf := rfl
theorem rfz_rfz (f : Rflags) : rfz (rfz f) = rfz f := rfl
theorem arith_sf {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).sf = r.msb := rfl
theorem subF_sf {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).sf = (x - y).msb := by
  simp [subF, Rflags.arith]
theorem addF_zf {w : Nat} (f : Rflags) (x y : BitVec w) : (addF f x y).zf = (x + y == 0) := by
  simp [addF, Rflags.arith]
theorem subF_zf' {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).zf = (x - y == 0) := by
  simp [subF, Rflags.arith]

/-- The flags a logical instruction leaves, one for each value of `AF`. -/
theorem forall_LogF {w : Nat} (f : Rflags) (r : BitVec w) (P : Rflags → Prop) :
    (∀ fl, LogF f r fl → P fl) ↔ ∀ af, P ((rfz f).arith r false false af) :=
  ⟨fun h af => h _ ⟨af, rfl⟩, fun h _ ⟨af, e⟩ => e ▸ h af⟩

/-! ## The tactic -/

/-- Runs `wp` of a list of effects (unfolded, or given among the extra lemmas) from registers given as `Gprs.mk`. -/
macro "wpx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [wp, Op.sub, Op.cmp, Op.add, Op.add8, Op.and, Op.or, Op.xor, Op.test, Op.inc, Op.dec, Op.neg,
    Op.sbb, Op.mov, Op.cmov32, Op.cmov64, Op.imul, Op.nop, Op.shl, Op.shr, Op.sar, Op.lea, Op.lea32a, Op.ld, Op.ld8,
    Op.ldzx, Op.subm, Op.cmpm, Op.addm, Op.andm, Op.pop, Op.st, Op.sti, Op.push,
    Src.val, gv, wr, wrLo, eaG, optV,
    gk0, gk1, gk2, gk3, gk4, gk5, gk6, gk7, gk8, gk9, gk10, gk11, gk12, gk13, gk14, gk15,
    sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15, sk4', rsp_mk,
    sw_64_32, sw_64_16, sw_64_8, sw_64_64, sw_32_32, imul32,
    cond_2, cond_3, cond_4, cond_5, cond_6, cond_7, cond_8, cond_9, rfz_cf, rfz_zf, rfz_sf, rfz_rfz,
    arith_cf, arith_zf, arith_sf, subF_cf, subF_zf, subF_sf, addF_zf, subR_eq, addR_eq, forall_LogF,
    toBytesLE_length, forall_eq, forall_const, true_and, and_true, true_implies,
    BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reducePow, BitVec.mul_one, BitVec.add_zero, add_z64, z_mul64, z_add64,
    $ls,*])

end FV7z

namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

variable {prof : Profile} {code : List Byte} {e' : Addr}

/-- One piece, then from its exit `r` another. -/
theorem Sp.then_at {j r : Nat} {W W' : Wpt} (h : Sp prof code e' j W) (h' : Sp prof code e' r W') :
    Sp prof code e' j fun F Wl Q => W F Wl fun j' g f V => if j' = r then W' F Wl Q g f V else Q j' g f V :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => h.run c hin _ hK hA hrip hW
    fun j' _ _ _ hq Y t' hKY hAY hrY hg hf => by
      by_cases e : j' = r
      · subst e
        simp only [↓reduceIte] at hq
        exact h'.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k
      · simp only [e, ↓reduceIte] at hq
        exact k _ _ _ _ hq Y t' hKY hAY hrY hg hf⟩

/-- A jump, then a piece from its target. -/
theorem Sp.jmp_then {j t : Nat} {W : Wpt} (h : Sp prof code e' j fun _ _ Q g f V => Q t g (rfz f) V)
    (h1 : Sp prof code e' t W) : Sp prof code e' j fun F Wl Q g f V => W F Wl Q g (rfz f) V := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hin X t' V Q hK hA hrip hW k
  refine h.run c hin (fun j' g f V => j' = t ∧ W F Wl Q g f V) hK hA hrip ⟨rfl, hW⟩ ?_
  rintro j' g fl V' ⟨rfl, hq⟩ Y t'' hKY hAY hrY hg hf
  exact h1.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k

/-- A conditional jump, then a piece from each of its two exits. -/
theorem Sp.jcc_then {j t n : Nat} {cc : Cond} {W1 W2 : Wpt}
    (h : Sp prof code e' j fun _ _ Q g f V =>
      (f.cond cc = true → Q t g (rfz f) V) ∧ (f.cond cc = false → Q n g (rfz f) V))
    (h1 : Sp prof code e' t W1) (h2 : Sp prof code e' n W2) :
    Sp prof code e' j fun F Wl Q g f V =>
      (f.cond cc = true → W1 F Wl Q g (rfz f) V) ∧ (f.cond cc = false → W2 F Wl Q g (rfz f) V) := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hin X t' V Q hK hA hrip hW k
  refine h.run c hin (fun j' g f V => (j' = t ∧ W1 F Wl Q g f V) ∨ (j' = n ∧ W2 F Wl Q g f V)) hK hA hrip
    ⟨fun hc => .inl ⟨rfl, hW.1 hc⟩, fun hc => .inr ⟨rfl, hW.2 hc⟩⟩ ?_
  rintro j' g fl V' (⟨rfl, hq⟩ | ⟨rfl, hq⟩) Y t'' hKY hAY hrY hg hf
  · exact h1.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k
  · exact h2.run c hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k

/-- The `Sp` of a table of pieces by their offsets, one more entry. -/
theorem Sp.table {ℓ k : Nat} {W W' : Wpt} (h : Sp prof code e' k W) (h' : Sp prof code e' ℓ W') :
    Sp prof code e' ℓ (if ℓ = k then W else W') := by
  split
  · next e => subst e; exact h
  · exact h'

end FV7z
