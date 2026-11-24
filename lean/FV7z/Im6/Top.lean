import FV7z.Im2.RunN
/-!
# `_int_malloc` from `use_top` for any size (PLAN.md G3, `malloc`; ctor 102)

`Im2.vc_2549n` and `Im2.im_from2549` without their bound `nb ≤ 8192` (their proofs never use it; the request 72704 of
ctor 102 is above it): `vc_2549w`, `im_from2549w`, the same proofs. Here and not in `Im2/Top.lean`: a change there
rebuilds every module after `malloc`; the two go back into `Im2` (and the bound out) with the next change there.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at pops rd_off rd_off_self add_n stk_in ret_950 lt_len)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
theorem vc_2549w {fb T szw sm nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbx : g.rbx = 7940672#64)
    (h13 : g.r13 = nb) (h32 : 32 ≤ nb.toNat)
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ g.rsp.toNat)
    (hsp2 : g.rsp.toNat + 256 < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hWl : ∀ i < 8, Foot Wl (Addr.add (7940768#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i))
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hsd : ∀ i < 184, Foot F.data (Addr.add g.rsp i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat) :
    W_2549 fb F Wl (fun j' g' _ V' => j' = 950 ∧ V' = VspN T szw nb V ∧ g'.rax = T + 16#64 ∧
      g'.rsp = g.rsp + 184#64 ∧
      g'.rbx = rdq(V, g.rsp + 136#64) ∧ g'.rbp = rdq(V, g.rsp + 144#64) ∧ g'.r12 = rdq(V, g.rsp + 152#64) ∧
      g'.r13 = rdq(V, g.rsp + 160#64) ∧ g'.r14 = rdq(V, g.rsp + 168#64) ∧ g'.r15 = rdq(V, g.rsp + 176#64))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h13 hTS hsp2 hsd ⊢
  subst hbx h13
  have a1 : (7940672#64 + 96#64 : Addr) = 7940768#64 := by decide
  have a2 : (7940672#64 + 2184#64 : Addr) = 7942856#64 := by decide
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := pops rsp
  have a3 : T + 16#64 + 18446744073709551608#64 = T + 8#64 := by bv_omega
  have hT' : T.toNat + r13.toNat + 16 < 2 ^ 64 := by omega
  have r0 : rdd(VspN T szw r13 V, 8013220#64) = 0 :=
    (congrArg (ofBytesLE 32) (VspN_rd V hT' (by decide) (.inr (by decide)) (.inl (by simp; omega)) (by omega))).trans
      hp0
  have rk : ∀ d, 136 ≤ d → d ≤ 176 →
      rdq(VspN T szw r13 V, rsp + BitVec.ofNat 64 d) = rdq(V, rsp + BitVec.ofNat 64 d) :=
    fun d h1 h2 => by
      have e : (rsp + BitVec.ofNat 64 d).toNat = rsp.toNat + d := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact congrArg (ofBytesLE 64) (VspN_rd V hT' (by omega) (.inr (by omega)) (.inr (by omega)) (by omega))
  have t1 : decide (sm.toNat < (szw &&& 18446744073709551608#64).toNat) = false := decide_eq_false (by omega)
  have e32 : (r13 + 32#64).toNat = r13.toNat + 32 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t2 : (decide ((r13 + 32#64).toNat < (szw &&& 18446744073709551608#64).toNat) ||
      decide (r13 + 32#64 = szw &&& 18446744073709551608#64)) = true := by
    rcases Nat.lt_or_eq_of_le hge with h | h
    · rw [decide_eq_true (by rw [e32]; exact h)]; rfl
    · have : r13 + 32#64 = szw &&& 18446744073709551608#64 := BitVec.eq_of_toNat_eq (by rw [e32, ← h])
      rw [decide_eq_true this, Bool.or_true]
  wpx [W_2549, W_2574, W_3191, W_930, o22, o23, o24, o7, Op.cmpmr, Op.lda, Op.zxr, Op.setcc, Op.shl64, a1, a2, a3,
    htop, hsz, hsm, b1, b2, b3, b4, b5, b6, t1, t2, r0, Nat.reduceSub, Nat.reduceMul, BitVec.reduceNot,
    BitVec.ofBool_false, BitVec.ofBool_true, BitVec.zero_or,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  repeat' first
    | apply And.intro
    | intro (_ : Rflags)
    | rfl
    | with_reducible exact hWl
    | with_reducible exact htf
    | with_reducible exact htw
    | with_reducible exact hrw
    | with_reducible exact hpb
    | with_reducible exact D _ _ (by decide) (by decide)
    | exact off_ft hsd _ rfl (by decide)
    | exact rk _ (by decide) (by decide)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `im_from2549` for any `nb ≥ 32`. -/
theorem im_from2549w {fb S T szw sm nb : Addr} {G : Gprs} {M : Addr → Byte} {Y : State} {t₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem M) (hr : Y.cpu.rip = imm_at.add 2549)
    (hbx : Y.cpu.gpr.rbx = 7940672#64) (h13 : Y.cpu.gpr.r13 = nb) (hsp : Y.cpu.gpr.rsp = S) (hfr : Fr S G V M)
    (h32 : 32 ≤ nb.toNat) (hS : S.toNat + 256 < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw nb M) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = G.rbx ∧ Z.cpu.gpr.rbp = G.rbp ∧
        Z.cpu.gpr.r12 = G.r12 ∧ Z.cpu.gpr.r13 = G.r13 ∧ Z.cpu.gpr.r14 = G.r14 ∧ Z.cpu.gpr.r15 = G.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₂ := by
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hsw i (by omega))
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  have T2 : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map M (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h =>
    rd_eq (by omega) fun a _ h2 => hfr.out a (.inl (by omega))
  refine (c_2549 prof fb).run c hfs hin _ hK hA hr
    (vc_2549w (sm := sm) hbx h13 h32 hT (by rw [hsp]; omega) (by rw [hsp]; exact hS) hWd
      (fun i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => c.hws _ (htw i hi)) htw hrw (by rw [hsp]; exact hsd) hpb
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hp0)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact htop)
      (by rw [T2 _ _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hsz)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hsm) hle hge) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hax₃, hsp₃, hbx₃, hbp, h12, h13₃, h14, h15⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst hg₃
  rw [hsp] at hsp₃ hbx₃ hbp h12 h13₃ h14 h15
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_950 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₃]
    exact c.hws _ (off_ft hsw 184 rfl (by decide) i hi)
  · rw [hsp₃]
    have e : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
    rw [congrArg (ofBytesLE 64) (VspN_rd _ (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (by omega)),
      congrArg (ofBytesLE 64) (rd_eq (by rw [e]; omega) fun a h _ => hfr.out a (.inr (by rw [e] at h; omega)))]
    exact hra
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg']; exact hax₃) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg']
    show Y₃.cpu.gpr.rsp + 8 = _
    rw [hsp₃]
    bv_omega
  · rw [hg']; exact hbx₃.trans hfr.bx
  · rw [hg']; exact hbp.trans hfr.bp
  · rw [hg']; exact h12.trans hfr.r12
  · rw [hg']; exact h13₃.trans hfr.r13
  · rw [hg']; exact h14.trans hfr.r14
  · rw [hg']; exact h15.trans hfr.r15

end FV7z.Im2
