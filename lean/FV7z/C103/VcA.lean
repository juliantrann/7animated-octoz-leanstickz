import FV7z.C103.Lem
import FV7z.Lemmas.BlkOps21
/-!
# `init_cacheinfo`: the moves between the cut points and the stops (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` for the pieces that only move registers (the calls' arguments and
results, the subleaf counters, the `threads` arithmetic's steps), and for the instructions the pieces stop at: the
calls of `handle_intel` and `handle_amd`, the `cpuid`s (leaf 4 and leaf `0xB` end by subleaf 64,
`Glibc.CacheEnds`), the `idiv`s and the `bsr`s.
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

macro "x_om" : tactic => `(tactic| ((try dsimp only) <;> (try simp only [sw_64_32, xs]) <;> omega))
macro "d_ec" : tactic => `(tactic| ((try dsimp only) <;> decide))

/-! ## Register moves -/

theorem vc_3566 (h : Ih g₀ V₀ 3566 n g V) : W_3566 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3566, o4, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_3629 (h : Ih g₀ V₀ 3629 n g V) : W_3629 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3629, o8, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_3763 (h : Ih g₀ V₀ 3763 n g V) : W_3763 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3763, o16, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, by d_ec⟩

theorem vc_3776 (h : Ih g₀ V₀ 3776 n g V) : W_3776 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_3776, o17, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, by d_ec⟩

theorem vc_4045 (h : Ih g₀ V₀ 4045 n g V) : W_4045 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4045, o16, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, by d_ec⟩

theorem vc_4058 (h : Ih g₀ V₀ 4058 n g V) : W_4058 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4058, o44, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, by d_ec⟩

theorem vc_4071 (h : Ih g₀ V₀ 4071 n g V) : W_4071 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4071, o45, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_3984 (h : Ih g₀ V₀ 3984 n g V) : W_3984 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h9⟩ := h
  wpx [W_3984, o8, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, h9⟩

theorem vc_4008 (h : Ih g₀ V₀ 4008 n g V) : W_4008 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4008, o40, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_4011 (h : Ih g₀ V₀ 4011 n g V) : W_4011 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4011, o41, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_4125 (h : Ih g₀ V₀ 4125 n g V) : W_4125 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4125, o51, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_4226 (h : Ih g₀ V₀ 4226 n g V) : W_4226 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4226, o61, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm⟩

theorem vc_4570 (h : Ih g₀ V₀ 4570 n g V) : W_4570 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h9⟩ := h
  wpx [W_4570, o90, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, h9, by d_ec⟩

theorem vc_4216 (h : Ih g₀ V₀ 4216 n g V) : W_4216 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, hc⟩ := h
  try dsimp only at hc
  wpx [W_4216, o60, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by decide, rfl, hm, sw_ne _ hc, sw_msb _, rfl⟩

theorem vc_4199 (h : Ih g₀ V₀ 4199 n g V) : W_4199 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm⟩ := h
  wpx [W_4199, o59, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  exact Or.inl ⟨_, by decide, rfl, hm, by dsimp only; rw [sw_64_32]; exact sh1 _⟩

/-! ## The leaf-4 loop's counter -/

theorem vc_3841 (h : Ih g₀ V₀ 3841 n g V) : W_3841 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h15, h2⟩ := h
  wpx [W_3841, o23, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  exact Or.inl ⟨_, by x_om, rfl, hm, ⟨h15, by x_om, by d_ec, h2⟩, by x_om⟩

theorem vc_3858 (h : Ih g₀ V₀ 3858 n g V) : W_3858 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hL, hc⟩ := h
  try dsimp only at hn hc
  subst hn
  have e := inc64 rcx hc
  have h10 : r10 = 4#64 := by obtain ⟨-, -, h, -⟩ := hL; exact h
  wpx [W_3858, o24, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by c_om, rfl, hm, hL, by c_om, hc, by subst h10; d_ec⟩

theorem vc_3929 (h : Ih g₀ V₀ 3929 n g V) : W_3929 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hL, h8⟩ := h
  try dsimp only at hn h8
  subst hn
  wpx [W_3929, o31, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by c_om, rfl, hm, hL, by c_om⟩

/-! ## The leaf-`0xB` loop's counter and flags -/

theorem vc_4306 (h : Ih g₀ V₀ 4306 n g V) : W_4306 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h15, h9, hs, hax, hdx, hd1, ha1⟩ := h
  try dsimp only at h9 hs hax hdx hd1 ha1
  have e0 : (rsi.setWidth 32).toNat = 0 := by simp [hs]
  wpx [W_4306, o67, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _
  exact Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, h9, by d_ec, bits06 hax hdx hd1 ha1⟩, by c_om⟩

theorem vc_4329 (h : Ih g₀ V₀ 4329 n g V) : W_4329 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hB, h10⟩ := h
  try dsimp only at hn h10
  subst hn
  wpx [W_4329, o69, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact Or.inl ⟨_, by c_om, rfl, hm, hB, by c_om⟩

theorem vc_4469 (h : Ih g₀ V₀ 4469 n g V) : W_4469 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, h15, h9, h13, h10, h8⟩ := h
  try dsimp only at hn h9 h13 h10 h8
  subst hn
  wpx [W_4469, o83, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _
  rcases h8 with rfl | ⟨rfl, rfl, hz⟩
  · exact Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, h9, h13, by d_ec, fun h => absurd h (by d_ec),
      fun h => absurd h (by d_ec)⟩, h10⟩
  · exact Or.inl ⟨_, by c_om, rfl, hm, ⟨h15, h9, h13, by d_ec, fun _ => ⟨rfl, hz⟩,
      fun h => absurd h (by d_ec)⟩, h10⟩

/-! ## Reads and stores of the globals -/

theorem vc_3960 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3960 n g V) : W_3960 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hm, h9⟩ := h
  wpx [W_3960, o34, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact ⟨fC hT (by decide) (by decide), Or.inl ⟨_, by decide, rfl, hm, h9, sw_lt _⟩⟩

theorem vc_4148 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 4148 n g V) : W_4148 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hs, hm⟩ := h
  wpx [W_4148, o55, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  exact ⟨fGw hT (Or.inr ⟨by decide, by decide⟩),
    Or.inl ⟨_, by decide, rfl, hs, st_G hm _ _ (Or.inr ⟨by decide, by decide⟩)⟩⟩

/-! ## The calls -/

theorem vc_3758 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 3758 n g V) :
    CallK Wl sti_at 3763 (Hin.Te F Wl L fb) Hin.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact hin_call hT hin (lt_len (by decide)) hm (Or.inl hd) fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

theorem vc_3771 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 3771 n g V) :
    CallK Wl sti_at 3776 (Hin.Te F Wl L fb) Hin.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact hin_call hT hin (lt_len (by decide)) hm (Or.inr (Or.inl hd))
    fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

theorem vc_3784 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 3784 n g V) :
    CallK Wl sti_at 3789 (Hin.Te F Wl L fb) Hin.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact hin_call hT hin (lt_len (by decide)) hm (Or.inr (Or.inr hd))
    fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

theorem vc_4040 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 4040 n g V) :
    CallK Wl sti_at 4045 (Hca.Te F Wl L) Hca.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact ham_call hT hin (lt_len (by decide)) hm (Or.inl hd) fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

theorem vc_4053 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 4053 n g V) :
    CallK Wl sti_at 4058 (Hca.Te F Wl L) Hca.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact ham_call hT hin (lt_len (by decide)) hm (Or.inr (Or.inl hd))
    fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

theorem vc_4066 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (h : Ih g₀ V₀ 4066 n g V) :
    CallK Wl sti_at 4071 (Hca.Te F Wl L) Hca.Rh (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd⟩ := h
  exact ham_call hT hin (lt_len (by decide)) hm (Or.inr (Or.inr hd))
    fun g' V' hm' _ => Or.inl ⟨_, by decide, rfl, hm'⟩

/-! ## The `cpuid`s -/

theorem vc_3865 (hC : Glibc.CacheEnds prof) (h : Ih g₀ V₀ 3865 n g V) :
    Cp prof 3865 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hL, h8, hc, ha⟩ := h
  try dsimp only at hn h8 hc ha
  subst hn
  intro cpu hcpu _
  refine Or.inl ⟨60000 + 10 * (66 - (r8.setWidth 32).toNat) + 4, by omega, rfl, cp_mf hm, hL,
    show (r8.setWidth 32).toNat ≤ 65 by omega, fun e => ?_⟩
  have e' : (r8.setWidth 32).toNat = 65 := e
  show ((prof.cpuid cpu (rax.setWidth 32) (rcx.setWidth 32)).eax.setWidth 64).setWidth 8 &&& 31#8 = 0#8
  rw [ha]
  exact and31 _ (hC.leaf4 cpu hcpu _ (by omega))

theorem vc_4346 (hC : Glibc.CacheEnds prof) (h : Ih g₀ V₀ 4346 n g V) :
    Cp prof 4346 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hB, h10, hs, ha, hc⟩ := h
  try dsimp only at hn h10 hs ha hc
  subst hn
  intro cpu hcpu _
  refine Or.inl ⟨40000 + 20 * (66 - (r10.setWidth 32).toNat) + 15, by omega, rfl, cp_mf hm, hB,
    show (r10.setWidth 32).toNat ≤ 65 by omega, fun e => ?_⟩
  have e' : (r10.setWidth 32).toNat = 65 := e
  show ((prof.cpuid cpu (rax.setWidth 32) (rcx.setWidth 32)).ecx.setWidth 64).setWidth 32 &&& 65280#32 = 0#32
  rw [sw_64_32, ha]
  exact hC.leafB cpu hcpu _ (by rw [hc]; omega)

theorem vc_4079 (h : Ih g₀ V₀ 4079 n g V) : Cp prof 4079 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm⟩ := h
  intro _ _ _
  exact Or.inl ⟨_, by decide, rfl, cp_mf hm⟩

theorem vc_4100 (h : Ih g₀ V₀ 4100 n g V) : Cp prof 4100 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm⟩ := h
  intro _ _ _
  exact Or.inl ⟨_, by decide, rfl, cp_mf hm⟩

theorem vc_4141 (h : Ih g₀ V₀ 4141 n g V) : Cp prof 4141 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm⟩ := h
  intro _ _ _
  exact Or.inl ⟨_, by decide, rfl, cp_mf hm⟩

theorem vc_4197 (h : Ih g₀ V₀ 4197 n g V) : Cp prof 4197 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm⟩ := h
  intro _ _ _
  exact Or.inl ⟨_, by decide, rfl, cp_mf hm⟩

/-! ## The `idiv`s: the divisors positive -/

theorem dv_mf {d : BitVec 64} (h : Mf g₀ V₀ g V) : Mf g₀ V₀ (idivG g d) V := by cases g; exact h

theorem vc_3707 (h : Ih g₀ V₀ 3707 n g V) : Dv 3707 1 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hc, hq⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hc
  subst hc
  exact ⟨hq, show (4#64 : BitVec 64).setWidth 64 ≠ 0 by decide,
    show ((4#64 : BitVec 64).setWidth 64).msb = false by decide, fun _ => Or.inl ⟨_, by decide, rfl, dv_mf hm⟩⟩

theorem vc_3981 (h : Ih g₀ V₀ 3981 n g V) : Dv 3981 7 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, h9, hd, hp, hq⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  exact ⟨hq, show rdi.setWidth 64 ≠ 0 by rw [BitVec.setWidth_eq]; exact hd,
    show (rdi.setWidth 64).msb = false by rw [BitVec.setWidth_eq]; exact hp,
    fun _ => Or.inl ⟨_, by decide, rfl, dv_mf hm, h9⟩⟩

theorem vc_4005 (h : Ih g₀ V₀ 4005 n g V) : Dv 4005 9 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd, hp, hq⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  exact ⟨hq, show r9.setWidth 64 ≠ 0 by rw [BitVec.setWidth_eq]; exact hd,
    show (r9.setWidth 64).msb = false by rw [BitVec.setWidth_eq]; exact hp,
    fun _ => Or.inl ⟨_, by decide, rfl, dv_mf hm⟩⟩

theorem vc_4223 (h : Ih g₀ V₀ 4223 n g V) : Dv 4223 1 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hm, hd, hp, hq⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  exact ⟨hq, show rcx.setWidth 64 ≠ 0 by rw [BitVec.setWidth_eq]; exact hd,
    show (rcx.setWidth 64).msb = false by rw [BitVec.setWidth_eq]; exact hp,
    fun _ => Or.inl ⟨_, by decide, rfl, dv_mf hm⟩⟩

/-! ## The `bsr`s: the sources not 0 -/

theorem vc_4380 (h : Ih g₀ V₀ 4380 n g V) : Bs 4380 1 9 4 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hB, h10, h8, hb1, hb2⟩ := h
  try dsimp only at hn h10 h8 hb1 hb2
  subst hn
  have hz : r9.setWidth 32 ≠ 0#32 := by
    obtain ⟨-, -, -, -, h1, -⟩ := hB
    exact (h1 h8).2
  exact ⟨hz, fun _ => Or.inl ⟨40000 + 20 * (66 - (r10.setWidth 32).toNat) + 11, by omega, rfl, hm, hB, h10, h8,
    hb1, hb2⟩⟩

theorem vc_4454 (h : Ih g₀ V₀ 4454 n g V) : Bs 4454 1 7 3 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hP, -, hz⟩ := h
  try dsimp only at hn hz
  subst hn
  exact ⟨hz, fun _ => Or.inl ⟨40000 + 20 * (66 - (r10.setWidth 32).toNat) + 11, by omega, rfl, hm, hP⟩⟩

theorem vc_4594 (h : Ih g₀ V₀ 4594 n g V) : Bs 4594 1 9 4 (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hm, hP, h8, hz, hb⟩ := h
  try dsimp only at hn h8 hz hb
  subst hn
  exact ⟨hz, fun _ => Or.inl ⟨40000 + 20 * (66 - (r10.setWidth 32).toNat) + 11, by omega, rfl, hm, hP, h8, hb⟩⟩

end FV7z.C103
