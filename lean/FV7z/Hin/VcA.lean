import FV7z.Hin.Inv
/-!
# `handle_intel`: the entry, `cpuid(2)` and the calls of `intel_check_word` (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` for the entry (1280: the `push`es, the canary's store, `max_cpuid < 2`),
the loop's head (1371, 1376, 1378: `cpuid(2)`, `maxidx` on the first round, `edx` saved), the arguments (1403) and the
four calls (1422, 1457, 1489, 1522).
-/
namespace FV7z.Hin
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

theorem vc_1280 (hT : Te F Wl L fb g₀ V₀) (h : Ih fb g₀ V₀ 1280 n g V) :
    W_1280 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hr := hT.rdi
  have hx := hT.mx
  have hc := hT.cn
  have hm := ent_mf hT
  have hM := ent_m hT (W := Vst (Vst (Vh fb g V) (fr g.rsp + 22#64) (toBytesLE (0#8) 1)) (fr g.rsp + 23#64)
    (toBytesLE (0#8) 1))
  obtain ⟨f1, f2, f3, f4, f5, f6, f24, f22, f23, f12⟩ := ent_foot hT
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hr' : rdi = 188#64 ∨ rdi = 191#64 ∨ rdi = 194#64 := hr
  wpx [W_1280, W_1610, W_1323, o0, o17, o1, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  refine ⟨f1, f2, f3, f4, f5, f6, hc, f24, fun _ => ⟨hx, fun _ => ?_, fun _ => ⟨f22, f23, f12, ?_⟩⟩⟩
  · exact Or.inl ⟨2, by decide, rfl, rfl, fun _ _ => rfl⟩
  · exact Or.inl ⟨_, m1280, rfl, ⟨rfl, hm⟩, rd_of hr', rfl, rfl, r1, hM⟩

theorem vc_1371 (h : Ih fb g₀ V₀ 1371 n g V) : W_1371 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  wpx [W_1371, o3, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  exact Or.inl ⟨_, by hin_om, rfl, hl⟩

theorem vc_1376 (h : Ih fb g₀ V₀ 1376 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx fb g₀ V₀ n 1378 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hl⟩ := h
  intro cpu _ fl
  exact Or.inl ⟨_, mlt cp_r14 (by decide), rfl, cp_lp hl⟩

theorem vc_1378 (hT : Te F Wl L fb g₀ V₀) (h : Ih fb g₀ V₀ 1378 n g V) :
    W_1378 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨hs, hm⟩, hb, h12, h13, h14, hM⟩ := h
  try dsimp only at hn hs hm hb h12 h13 h14 hM
  subst hn
  wpx [W_1378, W_1393, o4, o5, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  subst hs h12 h13
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e8 := tc 8 e0 (by omega)
  have e12 := tc 12 e0 (by omega)
  have m1 := mf_st hm (fr g₀.rsp + 8#64) (toBytesLE (BitVec.setWidth 32 rdx) 4) (by simp only [toBytesLE_length]; omega)
    (fun a ha => by simp only [Out, On, toBytesLE_length] at ha ⊢; omega)
  refine ⟨fW hT (by omega) (by omega), fun _ => Or.inl ⟨_, by hin_om, rfl, ⟨rfl, m1⟩, hb, rfl, rfl, h14, ?_⟩,
    fun _ _ => ⟨fW hT (by omega) (by omega), Or.inl ⟨_, by hin_om, rfl, ⟨rfl, mf_st m1 _ _
      (by simp only [toBytesLE_length]; omega) (fun a ha => by simp only [Out, On, toBytesLE_length] at ha ⊢; omega)⟩,
      hb, rfl, rfl, h14, ?_⟩⟩⟩
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (Or.inl (by rw [toBytesLE_length]; omega))]
    exact hM
  · rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (w := 32) (n := 4) rfl]
    exact sw8_le _

theorem vc_1403 (h : Ih fb g₀ V₀ 1403 n g V) : W_1403 fb F Wl (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, hl⟩ := h
  try dsimp only at hn
  subst hn
  have hl' := hl
  obtain ⟨-, hb, h12, h13, -, -⟩ := hl'
  wpx [W_1403, o6, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  exact Or.inl ⟨_, by hin_om, rfl, hl, rd_of hb, h13, h12, rfl, rfl⟩

theorem vc_1422 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) (h : Ih fb g₀ V₀ 1422 n g V) :
    CallK Wl hca_at 1427 (Icw.Te F Wl L) Icw.Rh (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rfl, hl, hc⟩ := h
  exact call_vc hT hin (lt_len (by decide)) hl hc fun g' V' hl' e _ =>
    Or.inl ⟨_, mlt e (by decide), rfl, hl'⟩

theorem vc_1457 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) (h : Ih fb g₀ V₀ 1457 n g V) :
    CallK Wl hca_at 1462 (Icw.Te F Wl L) Icw.Rh (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rfl, hl, hc⟩ := h
  exact call_vc hT hin (lt_len (by decide)) hl hc fun g' V' hl' e _ =>
    Or.inl ⟨_, mlt e (by decide), rfl, hl'⟩

theorem vc_1489 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) (h : Ih fb g₀ V₀ 1489 n g V) :
    CallK Wl hca_at 1494 (Icw.Te F Wl L) Icw.Rh (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rfl, hl, hc⟩ := h
  exact call_vc hT hin (lt_len (by decide)) hl hc fun g' V' hl' e _ =>
    Or.inl ⟨_, mlt e (by decide), rfl, hl'⟩

theorem vc_1522 (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) (h : Ih fb g₀ V₀ 1522 n g V) :
    CallK Wl hca_at 1527 (Icw.Te F Wl L) Icw.Rh (Nx fb g₀ V₀ n) g f V := by
  obtain ⟨rfl, hl, hc⟩ := h
  exact call_vc hT hin (lt_len (by decide)) hl hc fun g' V' hl' e _ =>
    Or.inl ⟨_, mlt e (by decide), rfl, hl'⟩

end FV7z.Hin
