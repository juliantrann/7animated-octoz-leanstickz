import FV7z.Hin.Inv
/-!
# `handle_intel`: after the calls of `intel_check_word`, the loop's test and the epilogue (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` after each call (1427, 1462, 1494, 1527: a result ends the loop at 1568,
else the next call's arguments), the loop's test at 1532 (`maxidx` above the round's count: one more round), and the
epilogue at 1568 (the canary's check, its failing way to 1619 refuted, the six `pop`s up to the `ret` at 1598).
-/
namespace FV7z.Hin
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

theorem vc_1427 (h : Ih fb g₀ V₀ 1427 n g V) : W_1427 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  have hl' := hl
  obtain ⟨hmf, hb, h12, h13, -, -⟩ := hl'
  wpx [W_1427, W_1436, o7, o8, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  intro _
  exact ⟨fun _ => Or.inl ⟨2, by hin_om, rfl, hmf⟩,
    fun _ => Or.inl ⟨_, by hin_om, rfl, hl, rd_of hb, h13, h12, rfl, rfl⟩⟩

theorem vc_1462 (h : Ih fb g₀ V₀ 1462 n g V) : W_1462 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  have hl' := hl
  obtain ⟨hmf, hb, h12, h13, -, -⟩ := hl'
  wpx [W_1462, W_1467, o7, o9, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  intro _
  exact ⟨fun _ => Or.inl ⟨2, by hin_om, rfl, hmf⟩,
    fun _ => Or.inl ⟨_, by hin_om, rfl, hl, rd_of hb, h13, h12, rfl, rfl⟩⟩

theorem vc_1494 (hT : Te F Wl L fb g₀ V₀) (h : Ih fb g₀ V₀ 1494 n g V) :
    W_1494 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  have hl' := hl
  obtain ⟨hmf, hb, h12, h13, -, -⟩ := hl'
  have hmf' := hmf
  obtain ⟨hs, -⟩ := hmf'
  try dsimp only at hs
  wpx [W_1494, W_1499, o7, o10, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  subst hs
  have lo := hT.lo
  have hi := hT.hi
  have e8 := tc 8 (t_fr _ lo) (by omega)
  intro _
  exact ⟨fun _ => Or.inl ⟨2, by hin_om, rfl, hmf⟩,
    fun _ => ⟨fD hT (by omega) (by omega), Or.inl ⟨_, by hin_om, rfl, hl, rd_of hb, h13, h12, rfl, rfl⟩⟩⟩

theorem vc_1527 (hT : Te F Wl L fb g₀ V₀) (h : Ih fb g₀ V₀ 1527 n g V) :
    W_1527 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  have hl' := hl
  obtain ⟨hmf, hb, h12, h13, h14, hM⟩ := hl'
  have hmf' := hmf
  obtain ⟨hs, -⟩ := hmf'
  try dsimp only at hs hb h12 h13 h14 hM
  wpx [W_1527, W_1532, W_1368, W_1547, W_1600, W_1558, o7, o11, o2, o12, o16, o13, Op.zxr, Op.cmpmi, Op.cmpmia,
    Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  subst hs
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e12 := tc 12 e0 (by omega)
  have e22 := tc 22 e0 (by omega)
  have hw := sw32n r14 h14
  intro _
  refine ⟨fun _ => Or.inl ⟨2, by hin_om, rfl, hmf⟩, fun _ => ⟨fD hT (by omega) (by omega), fun hc => ?_,
    fun _ => ⟨fun _ => ⟨fD hT (by omega) (by omega), Or.inl ⟨2, by hin_om, rfl, hmf⟩⟩,
      fun _ => Or.inl ⟨2, by hin_om, rfl, hmf⟩⟩⟩⟩
  have hlt := orfw (Icw.nt hc)
  have h1 := inc8 r14 (by omega)
  exact Or.inl ⟨_, by hin_om, rfl, hmf, hb, h12, h13, by hin_om, hM⟩

theorem vc_1568 (hT : Te F Wl L fb g₀ V₀) (h : Ih fb g₀ V₀ 1568 n g V) :
    W_1568 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨-, hs, hm⟩ := h
  try dsimp only at hs
  wpx [W_1568, W_1584, o14, o15, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  subst hs
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e24 := tc 24 e0 (by omega)
  have a0 := tc 40 e0 (by omega)
  have a1 := t8 a0 (by omega)
  have a2 := t8 a1 (by omega)
  have a3 := t8 a2 (by omega)
  have a4 := t8 a3 (by omega)
  have a5 := t8 a4 (by omega)
  have hc := canary hT hm
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pops hT hm
  obtain ⟨q, -⟩ := q_all _ lo
  refine ⟨fD hT (by omega) (by omega), hT.cn, fun _ => ⟨fun h => ?_, fun _ => ⟨fD hT (by omega) (by omega),
    fD hT (by omega) (by omega), fD hT (by omega) (by omega), fD hT (by omega) (by omega),
    fD hT (by omega) (by omega), fD hT (by omega) (by omega),
    Or.inr ⟨rfl, q, p1, p2, p3, p4, p5, p6, keepH_of hT hm⟩⟩⟩⟩
  rw [hc] at h
  simp at h

end FV7z.Hin
