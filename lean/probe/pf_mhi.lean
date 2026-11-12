import FV7z.Mhi.Tail
import FV7z.Im2.RunN
/-! Probe: the hook's `vc_236` and `vc_130` for every fastbin size `nb` (32 … 128), one `wpx` per `nb`;
`mhi_tailn`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at add_n)
open FV7z.Im2 (VspN VspN_rd V2n V2n_out im_secondn clsB)
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

theorem vc_236n {fb C nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64)
    (hbx : g.rbx = (nb + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 7, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfn : ∀ i < 7, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)) :
    W_236 fb F Wl (fun j' g' _ V' => j' = 99 ∧
      g' = { g with rax := C, rcx := C + 2#64 * ((nb + 18446744073709551599#64) >>> 4), rdx := 0#64 } ∧ V' = V)
      g f V := by
  have e0 : C + BitVec.ofNat 64 (2 * 0) = C := by simp
  have n0 : ofBytesLE 16 ((byteAddrs C 2).map V) = 0#16 := e0 ▸ hn 0 (by decide)
  have n1 : ofBytesLE 16 ((byteAddrs (C + 2#64) 2).map V) = 0#16 := hn 1 (by decide)
  have n2 : ofBytesLE 16 ((byteAddrs (C + 4#64) 2).map V) = 0#16 := hn 2 (by decide)
  have n3 : ofBytesLE 16 ((byteAddrs (C + 6#64) 2).map V) = 0#16 := hn 3 (by decide)
  have n4 : ofBytesLE 16 ((byteAddrs (C + 8#64) 2).map V) = 0#16 := hn 4 (by decide)
  have n5 : ofBytesLE 16 ((byteAddrs (C + 10#64) 2).map V) = 0#16 := hn 5 (by decide)
  have n6 : ofBytesLE 16 ((byteAddrs (C + 12#64) 2).map V) = 0#16 := hn 6 (by decide)
  have f0 : ∀ j < 2, Foot F.data (Addr.add C j) := e0 ▸ hfn 0 (by decide)
  have f1 : ∀ j < 2, Foot F.data (Addr.add (C + 2#64) j) := hfn 1 (by decide)
  have f2 : ∀ j < 2, Foot F.data (Addr.add (C + 4#64) j) := hfn 2 (by decide)
  have f3 : ∀ j < 2, Foot F.data (Addr.add (C + 6#64) j) := hfn 3 (by decide)
  have f4 : ∀ j < 2, Foot F.data (Addr.add (C + 8#64) j) := hfn 4 (by decide)
  have f5 : ∀ j < 2, Foot F.data (Addr.add (C + 10#64) j) := hfn 5 (by decide)
  have f6 : ∀ j < 2, Foot F.data (Addr.add (C + 12#64) j) := hfn 6 (by decide)
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  rcases hnb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_236, W_249, W_267, W_272, o12, o13, o14, o15, Op.cmpmra, Op.ldf, Op.ldzx, htb, htc, hC',
      n0, n1, n2, n3, n4, n5, n6,
      BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
    first
      | exact ⟨hfb, hft, f0⟩
      | exact ⟨hfb, hft, f1⟩
      | exact ⟨hfb, hft, f2⟩
      | exact ⟨hfb, hft, f3⟩
      | exact ⟨hfb, hft, f4⟩
      | exact ⟨hfb, hft, f5⟩
      | exact ⟨hfb, hft, f6⟩
      | (trace_state; sorry))

theorem vc_130n {fb nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64)
    (hax : g.rax ≠ 0#64)
    (hsz : rdq(V, g.rax + 18446744073709551608#64) = nb ||| 1#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 180 ∧ g' = { g with rax := nb ||| 1#64, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  rcases hnb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_130, W_142, W_150, o6, o7, o8, hax', hsz, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
    first | exact hfz | (trace_state; sorry))

/-- The size class of `9 ≤ n ≤ 120`: a fastbin size. -/
theorem nb_cases {n : Addr} (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 120) :
    (n + 23#64 &&& 18446744073709551600#64) = 32#64 ∨ (n + 23#64 &&& 18446744073709551600#64) = 48#64 ∨
      (n + 23#64 &&& 18446744073709551600#64) = 64#64 ∨ (n + 23#64 &&& 18446744073709551600#64) = 80#64 ∨
      (n + 23#64 &&& 18446744073709551600#64) = 96#64 ∨ (n + 23#64 &&& 18446744073709551600#64) = 112#64 ∨
      (n + 23#64 &&& 18446744073709551600#64) = 128#64 := by
  obtain ⟨-, -, -, k₀, hk1, hk2, enb⟩ := clsB hn hn'
  rw [enb]
  rcases (show k₀ = 2 ∨ k₀ = 3 ∨ k₀ = 4 ∨ k₀ = 5 ∨ k₀ = 6 ∨ k₀ = 7 ∨ k₀ = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The chunk's size word after the split: `nb ||| 1`. -/
theorem VspN_hd {T szw nb : Addr} (V : Addr → Byte) (hT : T.toNat + nb.toNat + 16 < 2 ^ 64) (h8 : 8 ≤ nb.toNat) :
    rdq(VspN T szw nb V, T + 8#64) = nb ||| 1#64 := by
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold VspN
  rw [rd_Vst _ _ _ _ _ (by rw [l, e72]; omega) (by omega) (by rw [l, e72]; omega),
    rd_Vst_self _ _ _ (l _) (by omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- Outside the frame of `_int_malloc`, the bytes after the second call are those of the split on the bytes
before. -/
theorem VspN_far {S T szw nb : Addr} (g : Gprs) (n : Addr) (V : Addr → Byte) (r : List Byte) (hr : r.length = 8)
    (hS : S.toNat + 256 < 2 ^ 64) {a : Addr} (ha : a.toNat < S.toNat + 8 ∨ S.toNat + 192 ≤ a.toNat) :
    VspN T szw nb (V2n S g n nb (Vst V (S + 184#64) r)) a = VspN T szw nb V a := by
  have e : V2n S g n nb (Vst V (S + 184#64) r) a = V a := by
    rw [V2n_out S g n nb _ hS (by omega), Vst_out _ _ _ _ (by rw [hr, add_n _ _ (by omega)]; omega)
      (by rw [hr, add_n _ _ (by omega)]; omega)]
  unfold VspN
  exact vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ e))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `mhi_tail` for every request `9 ≤ n ≤ 120` (`nb` = `n + 23 &&& -16`): from offset 236 (`rbx` the tcache
index of `nb`, `rbp` = `n`) to the return address with `T + 16` in `rax`. -/
theorem mhi_tailn {fb S T szw sm C n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mhi_at mhi) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hnb : n + 23#64 &&& 18446744073709551600#64 = nb) (hn9 : 9 ≤ n.toNat) (hn120 : n.toNat ≤ 120)
    (hrip : X.cpu.rip = mhi_at.add 236) (hbx : X.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4)
    (hbp : X.cpu.gpr.rbp = n)
    (hrsp : X.cpu.gpr.rsp = S + 192#64) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 7, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfn : ∀ i < 7, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j))
    (h1 : rdd(V, fb + 24#64) = 0#32) (hf1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i))
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 8 →
      rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 224, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + 144 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat) (hge : 160 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 216#64) = e₂.add j₂)
    (k : ∀ (M : Addr → Byte) Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem M →
      (∀ a : Addr, a.toNat < S.toNat + 8 ∨ S.toNat + 192 ≤ a.toNat → M a = VspN T szw nb V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 224#64 ∧ Z.cpu.gpr.rbx = rdq(V, S + 192#64) ∧ Z.cpu.gpr.rbp = rdq(V, S + 200#64) ∧
        Z.cpu.gpr.r12 = rdq(V, S + 208#64)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hcase : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64 := by
    rw [← hnb]; exact nb_cases hn9 hn120
  have hnbt : 32 ≤ nb.toNat ∧ nb.toNat ≤ 128 := by
    rcases hcase with h | h | h | h | h | h | h <;> subst h <;> decide
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  -- 236 → 99
  refine (c_236 prof fb).run c hfs hin _ hK hA hrip
    (vc_236n hcase hbx htb htc hC hn (fun i hi => hWd _ (by simp only [Addr.add]; bv_omega)
      (by simp only [Addr.add]; bv_omega)) htf hfn) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hv₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hv₁] at hA₁
  -- 99 → 125
  refine (c_99 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_99 h1 hf1) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hv₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  rw [hv₂] at hA₂
  have esp : Y₂.cpu.gpr.rsp = S + 192#64 := by rw [hg₂, hg₁]; exact hrsp
  have e184 : S + 192#64 - 8 = S + 184#64 := by bv_omega
  -- the call
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_125 _) hinI (Imm.lt_len (j := 0) (by decide)) tgt_125
    (by rw [esp, e184]; exact off_ft hsw 184 rfl (by decide)) ?_
  rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
  rw [esp, e184] at hA₀
  -- `_int_malloc`
  have l8 : (toBytesLE (mhi_at.add (125 + 5)) 8).length = 8 := toBytesLE_length _ _
  have s184 : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
  have P : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map (Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8)) (byteAddrs x m) =
        List.map V (byteAddrs x m) := fun x m h =>
    rd_Vst _ _ _ _ _ (by rw [l8, s184]; omega) (by omega) (.inr (by rw [s184]; omega))
  have q : ∀ x : Addr, x.toNat + 8 ≤ S.toNat → rdq(Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8), x) =
      rdq(V, x) := fun x h => congrArg (ofBytesLE 64) (P x 8 h)
  have d : ∀ x : Addr, x.toNat + 4 ≤ S.toNat → rdd(Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8), x) =
      rdd(V, x) := fun x h => congrArg (ofBytesLE 32) (P x 4 h)
  have n8 : ∀ (x : Nat), x + 8 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 8 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have n4 : ∀ (x : Nat), x + 4 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 4 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have hT8 : (T + 8#64).toNat + 8 ≤ S.toNat := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine im_secondn (S := S) (T := T) (szw := szw) (sm := sm) (n := n) c hfs hinI hK₀ hA₀ hr₀
    (by rw [hg₀]; show Y₂.cpu.gpr.rsp - 8 = _; rw [esp, e184])
    (by rw [hg₀, hg₂]; show Y₁.cpu.gpr.rbp = _; rw [hg₁]; exact hbp)
    (by rw [hg₀, hg₂]; rfl) hn9 hn120 hS hlo hfb
    (by rw [q _ (n8 _ (by omega))]; exact hgm)
    (fun k hk => by rw [q _ (n8 _ (by omega))]; exact hfz k hk)
    (fun i i1 i2 => by rw [q _ (n8 _ (by omega))]; exact hbk i i1 i2)
    (by rw [q _ hfb, htc]; exact hC)
    (by rw [q _ (n8 _ (by omega))]; exact htb) (by rw [q _ (n8 _ (by omega))]; exact hun)
    (by rw [d _ (n4 _ (by omega))]; exact hm0) (by rw [d _ (n4 _ (by omega))]; exact hm1)
    (by rw [d _ (n4 _ (by omega))]; exact hm2) (by rw [d _ (n4 _ (by omega))]; exact hm3)
    hW hgf htf (fun i hi => hsw i (by omega)) hT hTS htw (by rw [hnb]; exact hrw) hpb
    (by rw [d _ (n4 _ (by omega))]; exact hp0)
    (by rw [q _ (n8 _ (by omega))]; exact htop) (by rw [q _ hT8]; exact hsz)
    (by rw [q _ (n8 _ (by omega))]; exact hsm) hle hge
    hin (lt_len (j := 125 + 5) (by decide)) (by
      rw [rd_Vst_self _ _ _ l8 (by rw [s184]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  rintro Z₁ t₃ hK₃ hA₃ hr₃ hax₃ ⟨sp₃, bx₃, bp₃, r12₃, -, -, -⟩
  rw [hnb] at hA₃
  have hT' : T.toNat + nb.toNat + 16 < 2 ^ 64 := by omega
  -- the bytes above the frame
  have FAR : ∀ (x : Addr) (m : Nat), S.toNat + 192 ≤ x.toNat → x.toNat + m ≤ 2 ^ 64 →
      List.map (VspN T szw nb (V2n S Z₀.cpu.gpr n nb (Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8))))
        (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h1 h2 => by
    rw [← VspN_rd (T := T) (szw := szw) (nb := nb) V hT' h2 (.inr (by omega)) (.inr (by omega)) (by omega)]
    exact rd_eq h2 fun a ha _ => VspN_far _ _ _ _ l8 hS (.inr (by omega))
  -- 130 → 180
  have e8 : T + 16#64 + 18446744073709551608#64 = T + 8#64 := by bv_omega
  have hT0 : T + 16#64 ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    simp at this
    omega
  refine (c_130 prof fb).run c hfs hin _ hK₃ hA₃ (by rw [hr₃])
    (vc_130n hcase (by rw [hax₃]; exact hT0) (by rw [hax₃, e8]; exact VspN_hd _ hT' (by omega))
      (by rw [hax₃, e8]; exact fun i hi => c.hws _ (htw i hi))) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hv₄⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hv₄] at hA₄
  have sp₄ : Y₄.cpu.gpr.rsp = S + 192#64 := by rw [hg₄]; exact sp₃
  -- 180 → 187
  refine (c_180 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
    (vc_180 (by rw [sp₄]; exact fun i hi => c.hws _ (off_ft hsw 192 rfl (by decide) i hi))) ?_
  rintro j' g fl V₅ ⟨rfl, hv₅, ax₅, sp₅, bx₅, bp₅, r12₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  subst hg₅
  rw [hv₅] at hA₅
  have e216 : S + 192#64 + 8 + 8 + 8 = S + 216#64 := by bv_omega
  have e200 : S + 192#64 + 8 = S + 200#64 := by bv_omega
  have e208 : S + 192#64 + 8 + 8 = S + 208#64 := by bv_omega
  rw [sp₄] at sp₅ bx₅ bp₅ r12₅
  rw [e216] at sp₅
  rw [e200] at bp₅
  rw [e208] at r12₅
  -- the `ret`
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_187 _)
    (by rw [sp₅]; exact fun i hi => c.hws _ (off_ft hsw 216 rfl (by decide) i hi)) hin₂ h₂
    (by rw [sp₅, FAR _ _ (by omega) (by omega)]; exact hra) ?_
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k _ Z t' hK' hA' (fun a ha => VspN_far _ _ _ _ l8 hS ha) hr'
    (by rw [hg']; exact ax₅.trans (by rw [hg₄]; exact hax₃))
    ⟨by rw [hg']; show Y₅.cpu.gpr.rsp + 8 = _; rw [sp₅]; bv_omega, ?_, ?_, ?_⟩
  · rw [hg']
    exact bx₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact bp₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact r12₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))

end FV7z.Mhi
