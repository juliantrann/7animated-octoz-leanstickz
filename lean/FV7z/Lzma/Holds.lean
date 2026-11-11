import FV7z.Lzma.Table
import FV7z.Lzma.Ret
import FV7z.Spec.LzmaDec
import FV7z.Lemmas.Apart
/-!
# `LzmaDec_DecodeReal_3` keeps its contract (PLAN.md G2.2)

`ctx`: the call's context, from the state at the call. From the contract's precondition and footprint
(`FV7z/Spec/LzmaDec.lean`): `ctx_ok` (the regions fit, apart from each other), `ctx_env` (what may be read and
written), `ctx_pre` (the invariant at the entry). `dr3Run`: by `Seg.cfg` over the 66 cut points (`spAll`, `vcAll`) the
run reaches the `ret` with `Ret`, which gives the callee-saved registers and the postcondition. `dr3_holds`: every
call of the code, wherever it lies, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Lzma
namespace FV7z.Lzma

theorem and_m128 (x : BitVec 64) : (x &&& 18446744073709551488#64).toNat = x.toNat - x.toNat % 128 := by
  have h : x &&& 18446744073709551488#64 = (x >>> 7) <<< 7 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have e : ∀ i, i < 64 → (18446744073709551488#64).getLsbD i = decide (7 ≤ i) := by decide
    simp only [BitVec.getLsbD_and, e i hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h7 : 7 ≤ i
    · simp [h7, hi, show ¬ i < 7 by omega, show 7 + (i - 7) = i by omega]
    · simp [h7, show i < 7 by omega]
  rw [h, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The call's context, from the state at the call. -/
def ctx (s : State) : Ctx where
  sp := s.cpu.gpr.rsp - 48#64 + 18446744073709551488#64 &&& 18446744073709551488#64
  sq := s.cpu.gpr.rsp - 48#64
  p := s.cpu.gpr.rdi
  P := LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi
  pbn := (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat - 3328
  np := LzmaDec.numProbs s.proc.mm.mem s.cpu.gpr.rdi
  dic := LzmaDec.dic s.proc.mm.mem s.cpu.gpr.rdi
  dbs := LzmaDec.dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  lim := s.cpu.gpr.rsi.toNat
  dp0 := LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi
  bl := s.cpu.gpr.rdx
  b0 := (LzmaDec.buf s.proc.mm.mem s.cpu.gpr.rdi).toNat
  lc := LzmaDec.lc s.proc.mm.mem s.cpu.gpr.rdi
  lpm := 256#32 <<< (LzmaDec.lp s.proc.mm.mem s.cpu.gpr.rdi % 32) -
    256#32 >>> (LzmaDec.lc s.proc.mm.mem s.cpu.gpr.rdi % 32)
  pbm := 1#32 <<< (LzmaDec.pb s.proc.mm.mem s.cpu.gpr.rdi % 32) - 1
  ckd := ofBytesLE 32 (readBytes s.proc.mm.mem (s.cpu.gpr.rdi + 68) 4)
  ppb := if LzmaDec.checkDicSize s.proc.mm.mem s.cpu.gpr.rdi = 0 then
      LzmaDec.processedPos s.proc.mm.mem s.cpu.gpr.rdi +
        (s.cpu.gpr.rsi.toNat - LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi)
    else 0
  sv i := [s.cpu.gpr.r15, s.cpu.gpr.r14, s.cpu.gpr.r13, s.cpu.gpr.r12, s.cpu.gpr.rbp, s.cpu.gpr.rbx].getD i.val 0

theorem lit_bound : ∀ lc, lc ≤ 8 → ∀ lp, lp ≤ 4 →
    0x7c0 + 3 * (256#32 <<< (lp % 32) - 256#32 >>> (lc % 32)).toNat * 2 ^ lc + 0x300 ≤ 1984 + 768 * 2 ^ (lc + lp) := by
  decide

theorem pb_bound : ∀ pb, pb ≤ 4 → (1#32 <<< (pb % 32) - 1).toNat ≤ 15 := by decide

variable {s : State}

set_option maxHeartbeats 2000000 in
theorem ctx_ok (hp : LzmaDec.Pre s) (hfr : (frame s 303).Fits) (hf1 : (LzmaDec.rProbs s).Fits)
    (hf2 : (LzmaDec.rDic s).Fits) (hf3 : (LzmaDec.rDec s).Fits) : (ctx s).Ok := by
  have ⟨h1, h2⟩ := Call.frame_arith hfr
  simp only [Rgn.Fits, LzmaDec.rProbs, LzmaDec.rDic, LzmaDec.rDec, LzmaDec.probsBase] at hf1 hf2 hf3
  have hpr := hp.probs
  have e1 : (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi - 3328).toNat =
      (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat - 3328 := by bv_omega
  rw [e1] at hf1
  have hsq : (s.cpu.gpr.rsp - 48#64).toNat = s.cpu.gpr.rsp.toNat - 48 := by bv_omega
  have hs0 : (s.cpu.gpr.rsp - 48#64 + 18446744073709551488#64).toNat = s.cpu.gpr.rsp.toNat - 176 := by bv_omega
  have hsp : (s.cpu.gpr.rsp - 48#64 + 18446744073709551488#64 &&& 18446744073709551488#64).toNat =
      s.cpu.gpr.rsp.toNat - 176 - (s.cpu.gpr.rsp.toNat - 176) % 128 := by
    rw [and_m128, hs0]
  have hnp : 1 ≤ 2 ^ (LzmaDec.lc s.proc.mm.mem s.cpu.gpr.rdi + LzmaDec.lp s.proc.mm.mem s.cpu.gpr.rdi) :=
    Nat.one_le_two_pow
  have hnp' : 2 ^ (LzmaDec.lc s.proc.mm.mem s.cpu.gpr.rdi + LzmaDec.lp s.proc.mm.mem s.cpu.gpr.rdi) ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by decide) (by have := hp.lc; have := hp.lp; omega)
  have hpos := hp.pos; have hlim := hp.limit
  have d1 := ends_of_disjoint (hp.apartFrame _ (.head _) _ (.head _)) (by simp [frame])
    (by simp only [LzmaDec.rProbs, LzmaDec.numProbs]; omega)
  have d2 := ends_of_disjoint (hp.apartFrame _ (.head _) _ (.tail _ (.head _))) (by simp [frame])
    (by simp only [LzmaDec.rDic]; omega)
  have d3 := ends_of_disjoint (hp.apartFrame _ (.head _) _ (.tail _ (.tail _ (.head _)))) (by simp [frame])
    (by simp [LzmaDec.rDec])
  have d4 := ends_of_disjoint (hp.apartProbs _ (.head _) _ (.head _))
    (by simp only [LzmaDec.rProbs, LzmaDec.numProbs]; omega) (by simp only [LzmaDec.rDic]; omega)
  have d5 := ends_of_disjoint (hp.apartProbs _ (.head _) _ (.tail _ (.head _)))
    (by simp only [LzmaDec.rProbs, LzmaDec.numProbs]; omega) (by simp [LzmaDec.rDec])
  have d6 := ends_of_disjoint (hp.apartDic _ (.head _) _ (.head _)) (by simp only [LzmaDec.rDic]; omega)
    (by simp [LzmaDec.rDec])
  simp only [frame, LzmaDec.rProbs, LzmaDec.rDic, LzmaDec.rDec, LzmaDec.probsBase, e1] at d1 d2 d3 d4 d5 d6
  have hck := hp.check; have hpp := hp.processed; have hbl := hp.bufLimit
  have hn : LzmaDec.numProbs s.proc.mm.mem s.cpu.gpr.rdi = 1984 + 768 * 2 ^ (LzmaDec.lc s.proc.mm.mem s.cpu.gpr.rdi + LzmaDec.lp s.proc.mm.mem s.cpu.gpr.rdi) := rfl
  refine ⟨?_, ?_, ?_, hf2, hlim, ?_, hp.buf, hck, ?_, ?_, ?_, hf3, ?_, ?_, ?_, ?_, ?_, ?_, hp.lc, pb_bound _ hp.pb, ?_,
    Nat.le_of_lt hpos, ?_, lit_bound _ hp.lc _ hp.lp⟩
  all_goals dsimp only [ctx]
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d1 d2 d3 d4 d5 d6; omega
  · clear d2 d3 d4 d5 d6; omega
  · clear d1 d3 d4 d5 d6; omega
  · clear d1 d2 d4 d5 d6; omega
  · clear d1 d2 d3 d5 d6 hsp hs0 hsq; omega
  · clear d1 d2 d3 d4 d6 hsp hs0 hsq; omega
  · clear d1 d2 d3 d4 d5 hsp hs0 hsq; omega
  · clear d1 d2 d3 d4 d5 d6
    split
    · next h => exact hpp h
    · omega
  · clear d1 d2 d3 d4 d5 d6; omega

theorem ofNat_toNat64 (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem ctx_in (hp : LzmaDec.Pre s) (hf1 : (LzmaDec.rProbs s).Fits) : In (ctx s) s.proc.mm.mem.readByte where
  sp := rfl
  lc := rfl
  lpm := rfl
  pbm := rfl
  P := rfl
  dic := rfl
  dbs := ofNat_toNat64 _
  dp0 := ofNat_toNat64 _
  dpl := hp.pos
  b0 := Nat.le_refl _
  bl := hp.buf
  rng := hp.range
  pp := fun h => by
    show _ ≤ if LzmaDec.checkDicSize s.proc.mm.mem s.cpu.gpr.rdi = 0 then _ else 0
    split
    · exact Nat.le_refl _
    · next hn => exact absurd h hn
  ckd := rfl
  r0 := hp.reps 0 (by decide)
  r1 := hp.reps 1 (by decide)
  r2 := hp.reps 2 (by decide)
  r3 := hp.reps 3 (by decide)
  st := hp.state
  pr := by
    intro a ⟨i, hi, hai⟩
    have hv := hp.valid i hi
    have hpr := hp.probs
    simp only [Rgn.Fits, LzmaDec.rProbs] at hf1
    have e1 : (LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).toNat =
        (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat - 3328 := by
      show (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi - 3328).toNat = _
      bv_omega
    have hi' : i < LzmaDec.numProbs s.proc.mm.mem s.cpu.gpr.rdi := hi
    have ea : a = (LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).add (2 * i) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_of_fits (n := 2 * LzmaDec.numProbs s.proc.mm.mem s.cpu.gpr.rdi) (by omega) hf1, hai, e1]
      rfl
    subst ea
    have hlt := (ofBytesLE 16 (List.map s.proc.mm.mem.readByte
      (byteAddrs ((LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).add (2 * i)) 2))).isLt
    show 31 ≤ (BitVec.setWidth 32 _).toNat ∧ (BitVec.setWidth 32 _).toNat ≤ 2017
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact hv

theorem ctx_pre (hp : LzmaDec.Pre s) (hfr : (frame s 303).Fits) (hf1 : (LzmaDec.rProbs s).Fits) :
    Pre (ctx s) (2 ^ 20 * (s.cpu.gpr.rsi.toNat - LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi) + 10000) s.cpu.gpr
      s.proc.mm.mem.readByte := by
  have ⟨h1, h2⟩ := Call.frame_arith hfr
  exact ⟨by show s.cpu.gpr.rsp = s.cpu.gpr.rsp - 48#64 + 48#64; bv_omega, rfl, ofNat_toNat64 _, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, ctx_in hp hf1, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {ra e : Addr} {o : Oracle}

theorem ctx_env (c : Call prof 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post e L s ra o)
    (hK : (ctx s).Ok) (hfr : (frame s 303).Fits) :
    Env (ctx s) (fp 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post L s) (ws 303 LzmaDec.writes s) := by
  have hp : LzmaDec.Pre s := c.call.pre
  have ⟨h1, h2⟩ := Call.frame_arith hfr
  have hsq := hK.hsq; have hsp1 := hK.hsp1; have hsp2 := hK.hsp2; have hP := hK.hP; have hnp := hK.hnp
  have hdic := hK.hdic; have hlim := hK.hlim; have hpp := hK.hp; have hbl := hK.hbl
  have hpos := hp.pos; have hbuf := hp.buf; have hpr := hp.probs
  dsimp only [ctx] at hsq hsp1 hsp2 hP hnp hdic hlim hpp hbl
  have e0 : (s.cpu.gpr.rsp - 48#64).toNat = s.cpu.gpr.rsp.toNat - 48 := by bv_omega
  have e1 : (LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).toNat =
      (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat - 3328 := by
    show (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi - 3328).toNat = _
    bv_omega
  have e2 : (LzmaDec.dic s.proc.mm.mem s.cpu.gpr.rdi +
      BitVec.ofNat 64 (LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi)).toNat =
      (LzmaDec.dic s.proc.mm.mem s.cpu.gpr.rdi).toNat + LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi := by bv_omega
  have e3 : (s.cpu.gpr.rdi + 40).toNat = s.cpu.gpr.rdi.toNat + 40 := by bv_omega
  refine ⟨c.hws, fun y a1 a2 => ⟨below s 303, .head _, ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rProbs s, .tail _ (.tail _ (.head _)), ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rOut s, .tail _ (.head _), ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rDic s, by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads], ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rIn s, by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads], ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rDecW s, .tail _ (.tail _ (.tail _ (.head _))), ?_⟩,
    fun y a1 a2 => ⟨LzmaDec.rDec s, by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads], ?_⟩⟩
  all_goals dsimp only [ctx] at a1 a2
  all_goals simp only [Rgn.Mem, below, LzmaDec.rProbs, LzmaDec.rOut, LzmaDec.rDic, LzmaDec.rIn, LzmaDec.rDecW,
    LzmaDec.rDec, e1, e2, e3]
  all_goals omega

/-- A call runs to its return, as the contract says. -/
theorem dr3Run (c : Call prof 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post e L s ra o)
    (hin : CodeIn L e dr3) (t : Nat) :
    Go prof 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post L s ra o s t := by
  have hp : LzmaDec.Pre s := c.call.pre
  have hfit : ∀ r, r ∈ (fp 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post L s).data → r.Fits :=
    fun r hr => c.foot.fits r (List.mem_append_left _ hr)
  have hfr := hfit (frame s 303) (by simp [Footprint.data, Contract.footprint, fn])
  have hf1 := hfit (LzmaDec.rProbs s) (by simp [Footprint.data, Contract.footprint, fn, LzmaDec.writes])
  have hf2 := hfit (LzmaDec.rDic s) (by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads])
  have hf3 := hfit (LzmaDec.rDec s) (by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads])
  have hK := ctx_ok hp hfr hf1 hf2 hf3
  have hE := ctx_env c hK hfr
  refine c.toSeg.cfg hin (spAll prof _) (fun ℓ n g _ V => InvT (ctx s) ℓ n g V)
    (fun j' g' _ V' => j' = 4718 ∧ Ret (ctx s) g' V') (fun ℓ n g f V h => vcAll hK hE ℓ n g f V h) ?_ _ 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1) (ctx_pre hp hfr hf1)
  rintro j' g fl V' ⟨rfl, hR⟩ Y t' hKY hAY hrY rfl rfl
  obtain ⟨hsp, h15, h14, h13, h12, hbp, hbx, hax, hpv, ⟨dq, hdq, hd0, hd1, hdp⟩, hb0, hb1, hrng, hst, hok, herr⟩ := hR
  have ⟨k1, k2⟩ := Call.frame_arith hfr
  refine c.ret hKY ⟨hbx, hsp.trans ?_, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_4718 _) fun M hM => ?_
  · show s.cpu.gpr.rsp - 48#64 + 48#64 = s.cpu.gpr.rsp
    bv_omega
  have hA := c.agreeK hKY hAY hM
  have hpp : s.cpu.gpr.rdi.toNat + 0x60 ≤ 2 ^ 64 := hK.hp
  have rdp : ∀ (c n : Nat) (a : Addr), a.toNat = s.cpu.gpr.rdi.toNat + c → c + n ≤ 0x60 →
      readBytes M a n = List.map V' (byteAddrs a n) := by
    intro c n a ha hc
    refine hA.read fun i hi => ?_
    have e := toNat_add_of_fits (a := a) hi (by omega)
    exact hE.prd _ (by show s.cpu.gpr.rdi.toNat ≤ _; omega) (by show _ < s.cpu.gpr.rdi.toNat + 0x60; omega)
  have hdl : s.cpu.gpr.rsi.toNat ≤ LzmaDec.dicBufSize s.proc.mm.mem s.cpu.gpr.rdi := hK.hlim
  have hdb : (LzmaDec.dic s.proc.mm.mem s.cpu.gpr.rdi).toNat + LzmaDec.dicBufSize s.proc.mm.mem s.cpu.gpr.rdi ≤
      2 ^ 64 := hK.hdic
  have hd1' : dq ≤ s.cpu.gpr.rsi.toNat := hd1
  have q40 := rdp 40 8 (s.cpu.gpr.rdi + 40) (by bv_omega) (by omega)
  have q48 := rdp 48 8 (s.cpu.gpr.rdi + 48) (by bv_omega) (by omega)
  have q56 := rdp 56 4 (s.cpu.gpr.rdi + 56) (by bv_omega) (by omega)
  have q64 := rdp 64 4 (s.cpu.gpr.rdi + 64) (by bv_omega) (by omega)
  have q72 := rdp 72 4 (s.cpu.gpr.rdi + 72) (by bv_omega) (by omega)
  have q76 := rdp 76 4 (s.cpu.gpr.rdi + 76) (by bv_omega) (by omega)
  have q80 := rdp 80 4 (s.cpu.gpr.rdi + 80) (by bv_omega) (by omega)
  have q84 := rdp 84 4 (s.cpu.gpr.rdi + 84) (by bv_omega) (by omega)
  have q88 := rdp 88 4 (s.cpu.gpr.rdi + 88) (by bv_omega) (by omega)
  have q92 := rdp 92 4 (s.cpu.gpr.rdi + 92) (by bv_omega) (by omega)
  have edq : LzmaDec.dicPos M s.cpu.gpr.rdi = dq := by
    show (ofBytesLE 64 (readBytes M (s.cpu.gpr.rdi + 40) 8)).toNat = dq
    rw [q40]
    have h := congrArg BitVec.toNat hdq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
    exact h
  refine ⟨hax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Rgn.Fits, LzmaDec.rProbs] at hf1
    have hpr := hp.probs
    have e1 : (LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).toNat =
        (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat - 3328 := by
      show (LzmaDec.probs1664 s.proc.mm.mem s.cpu.gpr.rdi - 3328).toNat = _
      bv_omega
    have hi' : InPr (ctx s) ((LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).add (2 * i)) :=
      ⟨i, hi, by rw [toNat_add_of_fits (n := 2 * LzmaDec.numProbs s.proc.mm.mem s.cpu.gpr.rdi) (by omega) hf1, e1]; rfl⟩
    have hv := hpv _ hi'
    have hlt := (ofBytesLE 16 (List.map V'
      (byteAddrs ((LzmaDec.probsBase s.proc.mm.mem s.cpu.gpr.rdi).add (2 * i)) 2))).isLt
    show 31 ≤ (ofBytesLE 16 (readBytes M _ 2)).toNat ∧ (ofBytesLE 16 (readBytes M _ 2)).toNat ≤ 2017
    rw [hA.read (hE.rd_pr hK hi')]
    have hv' : 31 ≤ (BitVec.setWidth 32 _).toNat ∧ (BitVec.setWidth 32 _).toNat ≤ 2017 := hv
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hv'
    exact hv'
  · show LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi ≤ LzmaDec.dicPos M s.cpu.gpr.rdi ∧
      LzmaDec.dicPos M s.cpu.gpr.rdi ≤ _
    rw [edq]; exact ⟨hd0, hd1⟩
  · show _ ≤ (ofBytesLE 64 (readBytes M (s.cpu.gpr.rdi + 48) 8)).toNat ∧
      (ofBytesLE 64 (readBytes M (s.cpu.gpr.rdi + 48) 8)).toNat ≤ _
    rw [q48]; exact ⟨hb0, hb1⟩
  · show _ ≤ (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 56) 4)).toNat
    rw [q56]; exact hrng
  · show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 88) 4)).toNat < _
    rw [q88]; exact hst
  · intro h
    have h' := hdp h
    have ep : (ctx s).ppb = LzmaDec.processedPos s.proc.mm.mem s.cpu.gpr.rdi +
        (s.cpu.gpr.rsi.toNat - LzmaDec.dicPos s.proc.mm.mem s.cpu.gpr.rdi) := by
      show (if LzmaDec.checkDicSize s.proc.mm.mem s.cpu.gpr.rdi = 0 then _ else 0) = _
      split
      · rfl
      · next hn => exact absurd h hn
    rw [ep] at h'
    show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 64) 4)).toNat +
      (s.cpu.gpr.rsi.toNat - LzmaDec.dicPos M s.cpu.gpr.rdi) ≤ _
    rw [q64, edq]; exact h'
  · intro h i hi
    obtain ⟨r0, r1, r2, r3⟩ := hok h
    match i, hi with
    | 0, _ => show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 72) 4)).toNat ≤ _; rw [q72]; exact r0
    | 1, _ => show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 76) 4)).toNat ≤ _; rw [q76]; exact r1
    | 2, _ => show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 80) 4)).toNat ≤ _; rw [q80]; exact r2
    | 3, _ => show (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 84) 4)).toNat ≤ _; rw [q84]; exact r3
  · intro h
    show _ ≤ (ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 92) 4)).toNat
    rw [q92]; exact herr h

/-- `LzmaDec_DecodeReal_3`, wherever its code lies, on every processor: every call returns as its contract says. -/
theorem dr3_holds (L : List (Addr × List Byte)) (prof : Profile) (e : Addr) (hin : CodeIn L e dr3) :
    ImplementsCall prof e L LzmaDec.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof e L (fn 303 LzmaDec.writes LzmaDec.reads LzmaDec.Pre LzmaDec.Post) s₀ ra := hcall
  have hp : LzmaDec.Pre s₀ := hcall'.pre
  have hfr := Call.frame_arith (k := 303) (s := s₀)
    (hcall'.foot.fits (frame s₀ 303) (by simp [Footprint.data, Contract.footprint, fn]))
  have hf2 : (LzmaDec.rDic s₀).Fits :=
    hcall'.foot.fits _ (by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads])
  have hf3 : (LzmaDec.rDec s₀).Fits :=
    hcall'.foot.fits _ (by simp [Footprint.data, Contract.footprint, fn, LzmaDec.reads])
  have hslot : ∀ i < 8, ¬ Foot (LzmaDec.writes s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    have hy : (frame s₀ 303).Mem (Addr.add s₀.cpu.gpr.rsp i) := by
      simp only [frame, Rgn.Mem, toNat_add_of_fits hi hfr.2]
      omega
    have hpos := hp.pos; have hlim := hp.limit
    simp only [Rgn.Fits, LzmaDec.rDic, LzmaDec.rDec] at hf2 hf3
    simp only [LzmaDec.writes, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine hp.apartFrame _ (.head _) _ (.tail _ (.head _)) _ hy ?_
      have e2 : (LzmaDec.dic s₀.proc.mm.mem s₀.cpu.gpr.rdi +
          BitVec.ofNat 64 (LzmaDec.dicPos s₀.proc.mm.mem s₀.cpu.gpr.rdi)).toNat =
          (LzmaDec.dic s₀.proc.mm.mem s₀.cpu.gpr.rdi).toNat + LzmaDec.dicPos s₀.proc.mm.mem s₀.cpu.gpr.rdi := by
        bv_omega
      simp only [LzmaDec.rOut, LzmaDec.rDic, Rgn.Mem, e2] at hm ⊢
      omega
    · exact hp.apartFrame _ (.head _) _ (.head _) _ hy hm
    · refine hp.apartFrame _ (.head _) _ (.tail _ (.tail _ (.head _))) _ hy ?_
      have e3 : (s₀.cpu.gpr.rdi + 40).toNat = s₀.cpu.gpr.rdi.toNat + 40 := by bv_omega
      simp only [LzmaDec.rDecW, LzmaDec.rDec, Rgn.Mem, e3] at hm ⊢
      omega
  exact reachOrEndsIn_of_runsFrom fun o ho t => dr3Run (Call.of hcall' ho hslot) hin t

end FV7z.Lzma
