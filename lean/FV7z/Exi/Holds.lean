import FV7z.Exi.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `exit` (PLAN.md §M, M1)

glibc's `exit (int status)` at `0x623410` in `7zzs` (`stdlib/exit.c`; `objdump -d`), which does not return: `push rax;
pop rax`, `mov ecx, 1; mov edx, 1; lea rsi, __exit_funcs; sub rsp, 8`, then `call __run_exit_handlers` (27, `reh_at` =
`0x623150`) with `edi` = `status`, `rsi` = `&__exit_funcs` (`0x7924b0`), `ecx` = `edx` = 1 (`run_list_atexit`,
`run_dtors`).

The callee is a hypothesis (`kf`), a continuation at its entry, as in `FV7z/Act/Holds.lean`; it does not return either,
so there is no continuation after the `call`. The `push rax` (part of the frame alignment) stores `rax` 8 below the
entry's `rsp` (`V0`); the `pop` takes it back, and `rax` at the `call` is left open (`gS`).

- `gS`, `V0`: the registers and the bytes at the `call`.
- `vc_0`: the verification condition of the one piece.
- `exi_ok`: from the entry to the callee's entry, with `gS` and `V0` and the return address `exi_at + 32` stored 16
  below the entry's `rsp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Exi

/-- The callee, `__run_exit_handlers`. -/
abbrev reh_at : Addr := 0x623150

/-- The `call` to `__run_exit_handlers`. -/
def pcall : List Byte := [0xe8, 0x20, 0xfd, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709550880] 5) := by dec_rfl
theorem wc_27 : pcall <+: exi.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat exi 27 (FV7z.mk .call 64 [.rel 18446744073709550880] 5) :=
  Dec.shift (j := 27) (k := 0) (pcall_0 feat) wc_27 (Nat.zero_le _)
theorem tgt_27 :
    exi_at.add (27 + 5) + BitVec.ofNat 64 18446744073709550880 = reh_at.add 0 := by decide

/-- The registers at the `call`: `ecx` = `edx` = 1, `rsi` the list, `rdi` the status as it was, `rsp` 8 below the
entry's, `rax` left open (`a`). -/
abbrev gS (g : Gprs) (a : BitVec 64) : Gprs :=
  { g with rax := a, rcx := BitVec.setWidth 64 (BitVec.ofNat 32 1),
           rdx := BitVec.setWidth 64 (BitVec.ofNat 32 1), rsp := g.rsp - 8, rsi := 7938992#64 }

/-- The bytes at the `call`: `rax` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rax 8)

variable {F : Footprint} {Wl : List Rgn}

/-- The straight-line code to the `call` at 27. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8) i))
    (h : ∀ a fl, Q 27 (gS g a) fl (V0 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e8 : rsp - 8 + 8 = rsp := BitVec.sub_add_cancel _ _
  dsimp only [gS, V0] at hs1 h8 h ⊢
  wpx [W_0, o0]
  all_goals repeat'
    first
    | exact h _ _
    | (rw [e8]; exact h _ _)
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `exit (int status)` from its entry: the run reaches the callee's entry with the registers `gS` (some `rax`), `rsp`
16 below the entry's, and the bytes `V0` with the return address `exi_at + 32` stored at `rsp - 16` (`kf`). -/
theorem exi_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L exi_at exi)
    {cT : List Byte} (hinT : CodeIn L reh_at cT) (hT : 0 < cT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = exi_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (kf : ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (exi_at.add 32) 8)) →
      Y.cpu.rip = reh_at → Y.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 16) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = exi_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 27 ∧ (∃ a, g' = gS X.cpu.gpr a) ∧ V' = V0 V X.cpu.gpr)
    hK hA hrip' (vc_0 hs1 h8 fun a _ => ⟨rfl, ⟨a, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_27 _) hinT (tgt := 0) hT tgt_27 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gS X.cpu.gpr a).set 4 v) e16
  exact kf a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂'

end FV7z.Exi
