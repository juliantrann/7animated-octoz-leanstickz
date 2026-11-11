import FV7z.Ini.Cuts
import FV7z.Spec.InitFn
import FV7z.Tun.Inv
/-!
# `_init` keeps its contract (PLAN.md G3, startup)

One cut point, the entry. `rax` is `&__gmon_start__`, 0, so the `call` through it (20) is not reached, and the run
ends at the `ret` (26) with `rsp` back. `iniRun`: by `Seg.cfg` the run reaches the `ret` with the registers as at the
call. `ini_holds`: every call of the code at its place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Ini
namespace FV7z.Ini

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_26 : pret <+: ini.drop 26 := by decide +kernel
theorem ret_26 (feat : Features) : Dec feat ini 26 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 26) (k := 0) (pret_0 feat) w_26 (Nat.zero_le _)

/-- The registers a call keeps are as at the call. -/
def R (s : State) (g : Gprs) : Prop :=
  g.rsp = s.cpu.gpr.rsp ∧ g.rbx = s.cpu.gpr.rbx ∧ g.rbp = s.cpu.gpr.rbp ∧ g.r12 = s.cpu.gpr.r12 ∧
    g.r13 = s.cpu.gpr.r13 ∧ g.r14 = s.cpu.gpr.r14 ∧ g.r15 = s.cpu.gpr.r15

/-- The invariant at the cut point. -/
def Inv (s : State) (ℓ : Nat) (n : Nat) (g : Gprs) (_ : Addr → Byte) : Prop := ℓ = 0 ∧ n = 0 ∧ R s g

variable {s : State} {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : R s g) :
    W_0 F Wl (fun j' g' _ V' => (∃ m', m' < 0 ∧ Inv s j' m' g' V') ∨ (j' = 26 ∧ R s g')) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := h
  wpx [W_0, W_22, o0, o1]
  have hsp' : rsp = s.cpu.gpr.rsp := hsp
  refine ⟨fun _ => Or.inr ⟨?_, hbx, hbp, h12, h13, h14, h15⟩, fun h => absurd h (by decide)⟩
  show rsp - 8#64 + 8#64 = s.cpu.gpr.rsp
  rw [← hsp']
  bv_omega

theorem vcAll (ℓ : Nat) :
    ∀ n g f V, Inv s ℓ n g V → Wt ℓ F Wl (fun j' g' _ V' => (∃ m', m' < n ∧ Inv s j' m' g' V') ∨ (j' = 26 ∧ R s g'))
      g f V := by
  rintro n g f V ⟨rfl, rfl, h⟩
  exact vc_0 h

variable {prof : Profile} {L : List (Addr × List Byte)} {ra : Addr} {o : Oracle}

/-- A call runs to its return, as the contract says. -/
theorem iniRun (c : Call prof 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True) ini_at L s ra o)
    (hin : CodeIn L ini_at ini) (t : Nat) :
    Go prof 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True) L s ra o s t := by
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => Inv s ℓ n g V)
    (fun j' g' _ _ => j' = 26 ∧ R s g') (fun ℓ n g f V h => vcAll ℓ n g f V h) ?_ 0 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15⟩ Y t' hKY hAY hrY rfl rfl
  exact c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_26 _) fun M hM => trivial

/-- `_init`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem ini_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L ini_at ini) :
    ImplementsCall prof ini_at L InitFn.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof ini_at L (fn 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True)) s₀ ra :=
    hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    iniRun (Call.of hcall' ho (by rintro i hi ⟨r, hr, hm⟩; cases hr)) hin t

end FV7z.Ini
