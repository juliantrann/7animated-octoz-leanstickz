import FV7z.Icw.Inv
/-!
# `intel_check_word`: `cpuid` leaf 4 (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` for the walk over leaf 4's subleaves: the first `cpuid` (773, 775), the
loop for `r9` 6 or 9 (821–1048, `cpuid` at 829), the loop for `r9` 3 (1230–1260, `cpuid` at 1258), and the size at 885.
At the `cpuid`s, H-CPU-cache keeps the subleaf below 64 while the type is not 0.
-/
namespace FV7z.Icw
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length lt_len)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

set_option hygiene false in
/-- An exit of the leaf-4 loops: to a loop's next cut point, or to 885, or to 717. -/
macro "icw_lk" : tactic => `(tactic| first
  | exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩
  | exact Or.inl ⟨3, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, hrd⟩
  | exact Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, m4⟩)

theorem vc_773 (h : Ih g₀ V₀ 773 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx g₀ V₀ n 775 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hM, hrd⟩ := h
  intro cpu _ fl
  exact Or.inl ⟨990, by decide, rfl, cp_mid hM, cp_rd hrd⟩

theorem vc_775 (h : Ih g₀ V₀ 775 n g V) : W_775 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨m1, m2, m3, m4⟩, hrd⟩ := h
  try dsimp only at hn m1 m2 m3 hrd
  subst hn
  wpx [W_775, W_782, W_794, W_803, W_1152, W_1224, o24, o25, o26, o27, o45, Op.zxr, Op.sxr, Op.imul3, Op.shr64,
    Op.cmpmi, Op.setcc, Op.shr32z]
  intro _
  exact ⟨fun _ => Or.inl ⟨2, by decide, rfl, m1, m2, m3, m4⟩,
    fun _ _ => ⟨fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, sw_64_32 _⟩, by icw_om⟩,
      fun _ _ => ⟨fun h => absurd h (by rcases hrd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
        fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, sw_64_32 _⟩, by icw_om⟩⟩⟩⟩

theorem vc_821 (h : Ih g₀ V₀ 821 n g V) : W_821 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  have hi := inc32 _ hs
  wpx [W_821, o29, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, by icw_om, (sw_64_32 _).trans hk, rfl⟩

theorem vc_829 (hC : Glibc.CacheEnds prof) (h : Ih g₀ V₀ 829 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx g₀ V₀ n 831 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hL, hs, hax, hcx⟩ := h
  intro cpu hc fl
  refine Or.inl ⟨10 * (64 - (g.rsi.setWidth 32).toNat) + 8, by omega, by rw [cp_rsi], cp_lk hL,
    by rw [cp_rsi]; exact hs, fun hb => ?_⟩
  rw [cp_rsi]
  exact cp_type hC hc hax hcx fun e => by rw [e] at hb; exact absurd hb (by decide)

theorem vc_831 (h : Ih g₀ V₀ 831 n g V) : W_831 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs, ht⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs ht
  subst hn
  wpx [W_831, o24, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro _
  exact ⟨fun _ => Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, m4⟩,
    fun h0 => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, ht h0⟩⟩

theorem vc_838 (h : Ih g₀ V₀ 838 n g V) : W_838 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_838, W_816, o30, o28, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_856 (h : Ih g₀ V₀ 856 n g V) : W_856 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_856, W_861, o31, o28, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_866 (h : Ih g₀ V₀ 866 n g V) : W_866 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_866, W_875, o32, o33, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_1033 (h : Ih g₀ V₀ 1033 n g V) : W_1033 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_1033, W_1038, o41, o8, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_1048 (h : Ih g₀ V₀ 1048 n g V) : W_1048 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_1048, W_1057, W_1067, o42, o43, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_885 (h : Ih g₀ V₀ 885 n g V) : W_885 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨m1, m2, m3, m4⟩, hrd⟩ := h
  try dsimp only at hn m1 m2 m3 hrd
  subst hn
  wpx [W_885, W_896, W_905, W_914, W_1072, W_974, o34, o35, o32, o36, o44, o39, Op.zxr, Op.sxr, Op.imul3,
    Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  refine ⟨fun _ => ?_, fun h => absurd h (by rcases hrd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)⟩
  intros
  exact Or.inl ⟨1, by decide, rfl, m1, m2, m3, m4⟩

theorem vc_1230 (h : Ih g₀ V₀ 1230 n g V) : W_1230 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  wpx [W_1230, W_1241, o49, o50, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  repeat' (first | intro _ | apply And.intro)
  all_goals icw_lk

theorem vc_1250 (h : Ih g₀ V₀ 1250 n g V) : W_1250 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs
  subst hn
  have hi := inc32 _ hs
  wpx [W_1250, o47, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, by icw_om, (sw_64_32 _).trans hk, rfl⟩

theorem vc_1258 (hC : Glibc.CacheEnds prof) (h : Ih g₀ V₀ 1258 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx g₀ V₀ n 1260 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hL, hs, hax, hcx⟩ := h
  intro cpu hc fl
  refine Or.inl ⟨10 * (64 - (g.rsi.setWidth 32).toNat) + 8, by omega, by rw [cp_rsi], cp_lt hL,
    by rw [cp_rsi]; exact hs, fun hb => ?_⟩
  rw [cp_rsi]
  exact cp_type hC hc hax hcx fun e => by rw [e] at hb; exact absurd hb (by decide)

theorem vc_1260 (h : Ih g₀ V₀ 1260 n g V) : W_1260 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, hs, ht⟩ := h
  try dsimp only at hn m1 m2 m3 hrd hk hs ht
  subst hn
  wpx [W_1260, W_1267, o24, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro _
  exact ⟨fun h0 => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, hrd, hk⟩, ht h0⟩,
    fun _ => Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, m4⟩⟩

end FV7z.Icw
