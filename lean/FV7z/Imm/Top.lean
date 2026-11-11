import FV7z.Imm.Tail
/-!
# `_int_malloc`: from `use_top` to the `call` of `sysmalloc` (PLAN.md G3, `malloc`)

- `vc_2549`: what the pieces from offset 2549 need on the way of the first call: `av` the main arena, the top's
  size not above `av->system_mem` and below `nb + MINSIZE`, no fast chunks. They end at the `call` (offset 3280)
  with `av` in `rsi`, `nb` in `rdi`; the one store is of `r11` in the frame.
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
end FV7z.Imm
