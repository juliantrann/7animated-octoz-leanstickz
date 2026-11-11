import FV7z.Csu.Holds
import FV7z.Ini.Holds
/-!
# `_init` as `__libc_csu_init` calls it (PLAN.md G3, startup)

The section `.init` of `7zzs` (`_init` at `0x401000`, the function 1 of `Csu.csu_ok`): `__gmon_start__` is 0 in the
file (`mov $0, %rax`), so the function stores nothing and returns.

- `vc_i`: the verification condition of its blocks.
- `ini_runs`: `Runs` for the function 1, for any invariant with `I 1 V → I 2 V`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Csu

variable {F : Footprint} {Wl : List Rgn}

/-- `_init`: to its `ret`, the stack pointer and the registers a call keeps as they were, no store. -/
theorem vc_i {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    Ini.W_0 F Wl (fun j' g' _ V' => j' = 26 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e : rsp - 8 + 8 = rsp := by bv_omega
  wpx [Ini.W_0, Ini.W_22, Ini.o0, Ini.o1]
  exact ⟨fun _ => e, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {I : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}

/-- `_init` is a function as `csu_ok` asks: it keeps every byte. -/
theorem ini_runs (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L sp tg) (hin : CodeIn L Ini.ini_at Ini.ini)
    (h12 : ∀ V, I 1 V → I 2 V) : Runs prof F Wl L s₀ o gev gP gE I sp a₀ a₁ a₂ 1 (tg 1) := by
  intro X t V j₂ hK hA hI1 hr hsp _ hj hra k
  refine (Ini.c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hr.trans hE.ini) vc_i ?_
  rintro j' g fl V₁ ⟨rfl, h1, h2, h3, h4, h5, h6, h7, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  refine c.s_ret hK₁ hA₁ hin (Ini.lt_len (by decide)) hr₁ (Ini.ret_26 _)
    (fun i hi => by rw [h1, hsp]; exact c.hws _ (hE.st i (by omega))) hE.code hj (by rw [h1, hsp]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' _ hKZ hAZ (h12 _ hI1) (fun _ _ => rfl) (fun _ _ => rfl) hrZ ?_
  rw [hgZ]
  refine ⟨?_, h2, h3, h4, h5, h6, h7⟩
  show Y₁.cpu.gpr.rsp + 8 = _
  rw [h1]
  rfl

end FV7z.Csu
