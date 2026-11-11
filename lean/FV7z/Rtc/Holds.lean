import FV7z.Rtc.Cuts
import FV7z.Spec.RegTm
import FV7z.Tun.Inv
/-!
# `register_tm_clones` keeps its contract (PLAN.md G3, startup)

One cut point, the entry. `rsi` is the table's size (its end less its begin, both `0x793d10`: 0) in entries, halved
(`(x >> 63) + (x >>ₛ 3)`, then `>>ₛ 1`: 0), so `ZF` is set by the last `sar`, the first `je` (29) is taken, the `jmp`
through `_ITM_registerTMCloneTable` (46) is not reached, and the run ends at the `ret` (48) with `rsp` as at the call.
`rtcRun`: by `Seg.cfg` the run reaches the `ret` with the registers as at the
call. `rtc_holds`: every call of the code at its place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Rtc
namespace FV7z.Rtc

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: rtc.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat rtc 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)

/-- The registers a call keeps are as at the call. -/
def R (s : State) (g : Gprs) : Prop :=
  g.rsp = s.cpu.gpr.rsp ∧ g.rbx = s.cpu.gpr.rbx ∧ g.rbp = s.cpu.gpr.rbp ∧ g.r12 = s.cpu.gpr.r12 ∧
    g.r13 = s.cpu.gpr.r13 ∧ g.r14 = s.cpu.gpr.r14 ∧ g.r15 = s.cpu.gpr.r15

/-- The invariant at the cut point. -/
def Inv (s : State) (ℓ : Nat) (n : Nat) (g : Gprs) (_ : Addr → Byte) : Prop := ℓ = 0 ∧ n = 0 ∧ R s g

variable {s : State} {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : R s g) :
    W_0 F Wl (fun j' g' _ V' => (∃ m', m' < 0 ∧ Inv s j' m' g' V') ∨ (j' = 48 ∧ R s g')) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := h
  wpx [W_0, W_31, W_41, o0, o1, o2, Op.shr64, Op.sar64]
  intro _ _ _ _ fl hz
  have hz' : fl.zf = true := by rw [hz (by decide)]; decide
  exact ⟨fun _ => Or.inr ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩, fun h => absurd hz' (by rw [h]; decide)⟩

theorem vcAll (ℓ : Nat) :
    ∀ n g f V, Inv s ℓ n g V → Wt ℓ F Wl (fun j' g' _ V' => (∃ m', m' < n ∧ Inv s j' m' g' V') ∨ (j' = 48 ∧ R s g'))
      g f V := by
  rintro n g f V ⟨rfl, rfl, h⟩
  exact vc_0 h

variable {prof : Profile} {L : List (Addr × List Byte)} {ra : Addr} {o : Oracle}

/-- A call runs to its return, as the contract says. -/
theorem rtcRun (c : Call prof 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True) rtc_at L s ra o)
    (hin : CodeIn L rtc_at rtc) (t : Nat) :
    Go prof 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True) L s ra o s t := by
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => Inv s ℓ n g V)
    (fun j' g' _ _ => j' = 48 ∧ R s g') (fun ℓ n g f V h => vcAll ℓ n g f V h) ?_ 0 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15⟩ Y t' hKY hAY hrY rfl rfl
  exact c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_48 _) fun M hM => trivial

/-- `register_tm_clones`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem rtc_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L rtc_at rtc) :
    ImplementsCall prof rtc_at L RegTm.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof rtc_at L (fn 0 (fun _ => []) (fun _ => []) (fun _ => True) (fun _ _ => True)) s₀ ra :=
    hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    rtcRun (Call.of hcall' ho (by rintro i hi ⟨r, hr, hm⟩; cases hr)) hin t

end FV7z.Rtc
