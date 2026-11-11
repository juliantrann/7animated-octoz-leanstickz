import FV7z.Imm.Tail
/-!
# `_int_malloc`: from `use_top` to the `call` of `sysmalloc` (PLAN.md G3, `malloc`)

- `vc_2549`: what the pieces from offset 2549 need on the way of the first call: `av` the main arena, the top's
  size not above `av->system_mem` and below `nb + MINSIZE`, no fast chunks. They end at the `call` (offset 3280)
  with `av` in `rsi`, `nb` in `rdi`; the one store is of `r11` in the frame.
- `im_b`: the run from offset 2549 to the entry of `sysmalloc`, the return address pushed.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Imm
variable {F : Footprint} {Wl : List Rgn}

/-- From `use_top` with `av` the main arena (`rbx`), `nb` in `r13`, the top `tp` with size word `szw`: when the
size is not above `av->system_mem` (`sm`), is below `nb + 32` and `av->have_fastchunks` is 0, the pieces reach the
`call` of `sysmalloc` at offset 3280 with `rsi` the arena, `rdi` `nb` and `rbp` read from the frame. -/
theorem vc_2549 {fb tp szw sm : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbx : g.rbx = 7940672#64)
    (hsp : 8029888 ≤ g.rsp.toNat) (hsp2 : g.rsp.toNat + 40 ≤ 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (htf : ∀ i < 8, Foot F.data (Addr.add (tp + 8#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i))
    (hsd : ∀ i < 40, Foot F.data (Addr.add g.rsp i))
    (htop : rdq(V, 7940768#64) = tp) (hsz : rdq(V, tp + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hlt : (szw &&& 18446744073709551608#64).toNat < (g.r13 + 32#64).toNat)
    (hfc : rdd(V, 7940680#64) = 0) :
    W_2549 fb F Wl (fun j' g' _ V' => j' = 3280 ∧ V' = Vst V (g.rsp + 24#64) (toBytesLE g.r11 8) ∧
      g'.rsi = 7940672#64 ∧ g'.rdi = g.r13 ∧ g'.rbp = rdq(V, g.rsp + 32#64) ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧
      g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx hsp hsp2 hst hsd hlt ⊢
  subst hbx
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 → ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  have a1 : (7940672#64 + 96#64 : Addr) = 7940768#64 := by decide
  have a2 : (7940672#64 + 2184#64 : Addr) = 7942856#64 := by decide
  have a3 : (7940672#64 + 8#64 : Addr) = 7940680#64 := by decide
  have s24 : (rsp + 24#64).toNat = rsp.toNat + 24 := by bv_omega
  have s32 : (rsp + 32#64).toNat = rsp.toNat + 32 := by bv_omega
  have l8 : (toBytesLE r11 8).length = 8 := toBytesLE_length _ _
  have e1 : rdd(Vst V (rsp + 24#64) (toBytesLE r11 8), 7940680#64) = 0 :=
    (congrArg (ofBytesLE 32) (rd_Vst _ _ _ _ _ (by omega) (by decide)
      (.inr (by rw [s24]; exact Nat.le_trans (by decide) (Nat.le_trans hsp (Nat.le_add_right _ _)))))).trans hfc
  have e2 : rdq(Vst V (rsp + 24#64) (toBytesLE r11 8), rsp + 32#64) = rdq(V, rsp + 32#64) :=
    congrArg (ofBytesLE 64) (rd_Vst _ _ _ _ _ (by omega) (by omega) (.inl (by omega)))
  wpx [W_2549, W_2574, W_2587, W_3269, o19, o20, o21, o22, Op.cmpmr, a1, a2, a3, htop, hsz, hsm, e1, e2]
  refine ⟨D _ 8 (by decide) (by decide), htf, D _ 8 (by decide) (by decide),
    fun h => absurd (of_decide_eq_true h) (by omega), fun _ => ⟨fun h => ?_, fun _ => ⟨hst, D _ 4 (by decide)
      (by decide), fun _ => off_ft hsd 32 rfl (by decide), fun h => absurd h (by decide)⟩⟩⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · rw [h] at hlt
    omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- From offset 2549 (`use_top`) under `vc_2549`'s conditions: the run reaches the entry of `sysmalloc` with the
arena in `rsi`, `nb` in `rdi`, the return address (offset 3285) pushed; the bytes are those before with `r11` in the
frame and the return address below it. -/
theorem im_b {fb tp szw sm : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hinS : CodeIn L Smm.smm_at Smm.smm) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at.add 2549) (hbx : X.cpu.gpr.rbx = 7940672#64)
    (hsp : 8029888 ≤ X.cpu.gpr.rsp.toNat) (hsp2 : X.cpu.gpr.rsp.toNat + 40 ≤ 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (htf : ∀ i < 8, Foot F.data (Addr.add (tp + 8#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (hsd : ∀ i < 40, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hlr : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (htop : rdq(V, 7940768#64) = tp) (hsz : rdq(V, tp + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hlt : (szw &&& 18446744073709551608#64).toNat < (X.cpu.gpr.r13 + 32#64).toNat)
    (hfc : rdd(V, 7940680#64) = 0)
    (k : ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp + 24#64) (toBytesLE X.cpu.gpr.r11 8))
        (X.cpu.gpr.rsp - 8) (toBytesLE (imm_at.add (3280 + 5)) 8)) →
      Z.cpu.rip = Smm.smm_at → Z.cpu.gpr.rsi = 7940672#64 → Z.cpu.gpr.rdi = X.cpu.gpr.r13 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 ∧ Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 32#64) ∧
        Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
        Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_2549 prof fb).run c hfs hin _ hK hA hrip
    (vc_2549 hbx hsp hsp2 hW htf hst hsd htop hsz hsm hle hlt hfc) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hsi, hdi, hbp, hsp₁, hbx₁, h12, h13, h14, h15⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_3280 _) hinS (Smm.lt_len (j := 0) (by decide))
    tgt_3280 (by rw [hsp₁]; exact hlr) ?_
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  rw [hsp₁] at hA' hg'
  refine k Z t' hK' hA' hr' (by rw [hg']; exact hsi) (by rw [hg']; exact hdi) ⟨by rw [hg']; rfl,
    by rw [hg']; exact hbp, by rw [hg']; exact hbx₁, by rw [hg']; exact h12, by rw [hg']; exact h13,
    by rw [hg']; exact h14, by rw [hg']; exact h15⟩

end FV7z.Imm
