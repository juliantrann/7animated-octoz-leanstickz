import FV7z.C103.VcA
/-!
# `init_cacheinfo`: the branches between the cut points (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` for the pieces that branch on `test`/`cmp`: the reads of
`cpu_features` (`rep_movsb_threshold` and the non-temporal threshold's inputs), the stores of the four sizes into
the globals, the leaf-4 loop's body (cache type and level, `threads` from `EAX[25:14]`), the leaf-`0xB` loop's
head and tail, and the `threads` checks before the `idiv`s.
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-! ## The sizes from `cpu_features` and their stores -/

theorem vc_3569 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3569 n g V) : W_3569 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hs, hm⟩ := h
  wpx [W_3569, W_3574, o5, o6, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh,
    Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by decide, rfl, hs, hm⟩, fun _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩),
    fun _ _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩), fGw hT (Or.inl ⟨by decide, by decide⟩),
    fun _ _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩), Or.inl ⟨_, by decide, rfl, hs, ?_⟩⟩⟩⟩⟩
  exact st_G (st_G (st_G (st_G hm _ _ (gw8 _ _ ⟨by decide, by decide⟩)) _ _ (gw8 _ _ ⟨by decide, by decide⟩)) _ _
    (gw8 _ _ ⟨by decide, by decide⟩)) _ _ (gw8 _ _ ⟨by decide, by decide⟩)

theorem vc_3632 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3632 n g V) : W_3632 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hs, hm⟩ := h
  wpx [W_3632, W_3637, o9, o10, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh,
    Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by decide, rfl, hs, hm⟩, fun _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩),
    fun _ _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩), fGw hT (Or.inl ⟨by decide, by decide⟩),
    fun _ _ => ⟨fGw hT (Or.inl ⟨by decide, by decide⟩), Or.inl ⟨_, by decide, rfl, hs, ?_⟩⟩⟩⟩⟩
  exact st_G (st_G (st_G (st_G hm _ _ (gw8 _ _ ⟨by decide, by decide⟩)) _ _ (gw8 _ _ ⟨by decide, by decide⟩)) _ _
    (gw8 _ _ ⟨by decide, by decide⟩)) _ _ (gw8 _ _ ⟨by decide, by decide⟩)

theorem vc_3617 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3617 n g V) : W_3617 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3617, o7, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact ⟨fC hT (by decide) (by decide), fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun _ => Or.inl ⟨_, by decide, rfl, hm⟩⟩⟩

theorem vc_3680 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3680 n g V) : W_3680 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3680, W_3692, o11, o12, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx,
    Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf,
    Op.shr32z]
  exact ⟨fC hT (by decide) (by decide), fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun _ => ⟨fGd hT (Or.inl ⟨by decide, by decide⟩), fun _ => Or.inl ⟨_, by decide, rfl, hm, by d_ec, rfl⟩⟩⟩⟩

theorem vc_4014 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 4014 n g V) : W_4014 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4014, W_4030, o42, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh,
    Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact ⟨fC hT (by decide) (by decide), fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun _ => Or.inl ⟨_, by decide, rfl, hm⟩⟩⟩

/-! ## `threads_l2` or `threads_l3`, and the leaf-4 loop -/

theorem vc_3789 (h : Ih g₀ V₀ 3789 n g V) : W_3789 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3789, W_3801, W_3934, o18, o19, o32, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr,
    Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf,
    Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ _ => Or.inl ⟨_, by decide, rfl, hm, Or.inl ⟨by d_ec, ?_⟩⟩,
    fun _ _ => Or.inl ⟨_, by decide, rfl, hm, Or.inr ⟨by d_ec, ?_⟩⟩⟩
  · show ((rdi.setWidth 32 ||| 4294967295#32).setWidth 64).setWidth 32 = 4294967295#32
    rw [sw_64_32, or_ones]
  · show ((rdi.setWidth 32 ^^^ rdi.setWidth 32).setWidth 64).setWidth 32 = 0#32
    rw [sw_64_32, BitVec.xor_self]

theorem vc_3809 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3809 n g V) : W_3809 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, hr⟩ := h
  try dsimp only at hr
  have h15 : R15 r15 := hr.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  wpx [W_3809, W_3822, W_3828, W_4241, W_3951, o20, o21, o22, o33, o63, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32,
    Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia,
    Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  refine ⟨fC hT (by decide) (by decide), fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun _ => ⟨fun _ _ => Or.inl ⟨_, by decide, rfl, hm, by x_om⟩, fun _ _ => ⟨fun _ _ => ?_, fun hz => ?_⟩⟩⟩⟩
  · refine Or.inl ⟨_, by decide, rfl, hm, h15, fun _ => ⟨?_, Or.inl (by d_ec)⟩⟩
    show ((rdi.setWidth 32 ||| 4294967295#32).setWidth 64).setWidth 32 = 4294967295#32
    rw [sw_64_32, or_ones]
  · refine Or.inl ⟨_, by decide, rfl, hm, h15, fun e => ?_⟩
    rcases hr with ⟨-, e'⟩ | ⟨e2, -⟩
    · rw [e'] at hz
      exact absurd hz (by decide)
    · have e3 : r15 = 2#64 := e
      rw [e2] at e3
      exact absurd e3 (by decide)

theorem vc_3867 (h : Ih g₀ V₀ 3867 n g V) : W_3867 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hL, h8, hx⟩ := h
  try dsimp only at hn h8 hx
  subst hn
  obtain ⟨h15, h9, h10, h2⟩ := id hL
  try dsimp only at h9 h10 h2
  wpx [W_3867, W_3871, W_3888, W_3893, W_3899, W_4163, W_4173, o25, o26, o27, o28, o29, o56, o57, Op.lda, Op.sta,
    Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma,
    Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by omega, rfl, hm, show (r9.setWidth 32).toNat ≤ 1024 by omega⟩, fun h1 => ?_⟩
  have r8le : (r8.setWidth 32).toNat ≤ 64 := by
    refine Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h8 fun e => ?_)
    rw [hx e] at h1
    exact absurd h1 (by decide)
  intro _ _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · intro _
    refine ⟨fun _ => Or.inl ⟨_, by c_om, rfl, hm, hL, r8le⟩, fun _ => ?_⟩
    intro _ _ _
    refine Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, ?_, h10, fun e => ⟨(h2 e).1, ?_⟩⟩, r8le⟩
    · show (((rax.setWidth 32 >>> 14 &&& 1023#32).setWidth 64).setWidth 32).toNat ≤ 1023
      rw [sw_64_32]
      exact Nat.le_trans (and_le_r _ _) (by decide)
    · rcases (h2 e).2 with e' | e' <;> (subst e'; d_ec)
  · refine ⟨fun _ => Or.inl ⟨_, by c_om, rfl, hm, hL, r8le⟩, fun _ => ?_⟩
    intro _
    refine ⟨fun _ => Or.inl ⟨_, by c_om, rfl, hm, hL, r8le⟩, fun h4 => ?_⟩
    intro _ _ _ _ _
    refine Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, h9, h10, fun e => ?_⟩, r8le⟩
    rcases (h2 e).2 with e' | e' <;> (rw [e'] at h4; exact absurd h4 (by decide))

/-! ## `threads` before the `idiv`s -/

theorem vc_3967 (h : Ih g₀ V₀ 3967 n g V) : W_3967 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h9, hd⟩ := h
  try dsimp only at hd
  wpx [W_3967, W_3972, W_3976, o9, o35, o36, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr,
    Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf,
    Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm, h9⟩, fun _ _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm, h9⟩,
    fun hz => Or.inl ⟨_, by decide, rfl, hm, h9, fun e => ?_, msb_lt _ hd, rfl⟩⟩⟩
  have e' : rdi = 0#64 := e
  rw [e'] at hz
  exact absurd hz (by decide)

theorem vc_3987 (h : Ih g₀ V₀ 3987 n g V) : W_3987 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h9⟩ := h
  wpx [W_3987, W_3992, W_3997, o37, o38, o39, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr,
    Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf,
    Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩, fun _ _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun hz => ?_⟩⟩
  have h0 : r9.setWidth 32 ≠ 0#32 := fun e => by
    rw [e] at hz
    exact absurd hz (by decide)
  exact Or.inl ⟨_, by decide, rfl, hm, sext_ne _ h0 h9, sext_msb _ h9, rfl⟩

/-! ## The AMD leaves -/

theorem vc_4081 (h : Ih g₀ V₀ 4081 n g V) : W_4081 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4081, W_4088, W_4095, W_4192, o46, o47, o48, o58, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc,
    Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr,
    Op.xormf, Op.ldf, Op.shr32z]
  intro _
  exact ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩, fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩,
    fun _ => Or.inl ⟨_, by decide, rfl, hm⟩⟩⟩

theorem vc_4102 (h : Ih g₀ V₀ 4102 n g V) : W_4102 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4102, W_4112, o49, o50, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx,
    Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf,
    Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩, fun _ _ _ => ⟨fun hb => Or.inl ⟨_, by decide, rfl, hm, ?_⟩,
    fun _ => Or.inl ⟨_, by decide, rfl, hm⟩⟩⟩
  show ((rbx.setWidth 32 >>> 16 &&& 255#32).setWidth 64).setWidth 32 ≠ 0#32
  rw [sw_64_32]
  intro e
  rw [e] at hb
  exact absurd hb (by decide)

theorem vc_4128 (h : Ih g₀ V₀ 4128 n g V) : W_4128 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4128, W_4136, o52, o53, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx,
    Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf,
    Op.shr32z]
  exact ⟨fun _ => Or.inl ⟨_, by decide, rfl, hm⟩, fun _ => Or.inl ⟨_, by decide, rfl, hm⟩⟩

/-! ## The leaf-`0xB` loop -/

theorem vc_4332 (h : Ih g₀ V₀ 4332 n g V) : W_4332 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hB, hs⟩ := h
  try dsimp only at hn hs
  subst hn
  obtain ⟨-, h9, h13, -⟩ := id hB
  try dsimp only at h9 h13
  have e := inc64 rsi hs
  wpx [W_4332, W_4337, o70, o71, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx,
    Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf,
    Op.shr32z]
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by omega, rfl, hm, h9⟩,
    fun _ => Or.inl ⟨_, by c_om, rfl, hm, hB, by c_om, hs, ?_, ?_⟩⟩
  · show ((r13.setWidth 32).setWidth 64).setWidth 32 = 11#32
    rw [sw_64_32, h13] <;> decide
  · show ((rsi.setWidth 32).setWidth 64).setWidth 32 = rsi.setWidth 32
    rw [sw_64_32]

theorem vc_4384 (h : Ih g₀ V₀ 4384 n g V) : W_4384 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hB, h10, h8, hb1, hb2⟩ := h
  try dsimp only at hn h10 h8 hb1 hb2
  subst hn
  obtain ⟨h15, -, h13, -, hc2, hc3⟩ := id hB
  wpx [W_4384, o76, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  have r9b : (((~~~((r9.setWidth 32 ||| 4294967295#32) <<< ((((rcx.setWidth 32 + 1#32)).setWidth 8).toNat % 32)) &&&
      (rbx + 18446744073709551615#64).setWidth 32).setWidth 64).setWidth 32).toNat ≤ 1023 := by
    rw [sw_64_32]
    exact Nat.le_trans (and_le_r _ _) (by rw [dec64 rbx hb1]; omega)
  rcases h8 with rfl | rfl
  · exact Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, r9b, h13, by d_ec, fun h => absurd h (by d_ec),
      fun h => absurd h (by d_ec)⟩, h10⟩
  · exact Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, r9b, h13, by d_ec, fun h => absurd h (by d_ec),
      fun _ => ⟨fun e => (hc3 (Or.inr rfl)).1 e,
        fun e => absurd (e.symm.trans (hc2 (Or.inr rfl)).1) (by decide)⟩⟩, h10⟩

theorem vc_4457 (h : Ih g₀ V₀ 4457 n g V) : W_4457 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hP⟩ := h
  try dsimp only at hn
  subst hn
  wpx [W_4457, o82, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  exact Or.inl ⟨_, by c_om, rfl, hm, hP⟩

theorem vc_4598 (h : Ih g₀ V₀ 4598 n g V) : W_4598 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hP, h8, hb⟩ := h
  try dsimp only at hn h8 hb
  subst hn
  obtain ⟨h15, -, h13, h10, -⟩ := id hP
  wpx [W_4598, o91, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  refine Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, ?_, h13, h10, Or.inl h8⟩⟩
  show (((~~~((r9.setWidth 32 ||| 4294967295#32) <<< ((((rcx.setWidth 32 + 1#32)).setWidth 8).toNat % 32)) &&&
      rbx.setWidth 32).setWidth 64).setWidth 32).toNat ≤ 1023
  rw [sw_64_32]
  exact Nat.le_trans (and_le_r _ _) (by omega)

end FV7z.C103
