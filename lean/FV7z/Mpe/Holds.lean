import FV7z.Mpe.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `malloc_printerr` (PLAN.md §M, M1)

glibc's `malloc_printerr (const char *str)` at `0x62e490` in `7zzs` (`malloc/malloc.c`; `objdump -d`), which does not
return: `push rax; pop rax` (no `endbr64`), `lea rsi, fmt; xor eax, eax; mov rdx, rdi; sub rsp, 8; mov edi, 1`, then
`call __libc_message` (23, `lms_at` = `0x627710`) with `rdi` = 1 (`do_abort`), `rsi` = the format `"%s\n"` (`0x70679f`),
`rdx` = `str`.

The callee is a hypothesis (`kf`), a continuation at its entry, as in `FV7z/Act/Holds.lean`; it does not return either,
so there is no continuation after the `call`. The `push rax` (part of the frame alignment) stores `rax` 8 below the
entry's `rsp` (`V0`); the `pop` takes it back, and `rax` at the `call` is left open (`gS`).

- `gS`, `V0`: the registers and the bytes at the `call`.
- `vc_0`: the verification condition of the one piece.
- `mpe_ok`: from the entry to the callee's entry, with `gS` and `V0` and the return address `mpe_at + 28` stored 16
  below the entry's `rsp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mpe

/-- The callee, `__libc_message`. -/
abbrev lms_at : Addr := 0x627710

/-- The `call` to `__libc_message`. -/
def pcall : List Byte := [0xe8, 0x64, 0x92, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709523556] 5) := by dec_rfl
theorem wc_23 : pcall <+: mpe.drop 23 := by decide +kernel
theorem call_23 (feat : Features) : Dec feat mpe 23 (FV7z.mk .call 64 [.rel 18446744073709523556] 5) :=
  Dec.shift (j := 23) (k := 0) (pcall_0 feat) wc_23 (Nat.zero_le _)
theorem tgt_23 :
    mpe_at.add (23 + 5) + BitVec.ofNat 64 18446744073709523556 = lms_at.add 0 := by decide

/-- The registers at the `call`: `rdi` 1, `rsi` the format, `rdx` the message, `rsp` 8 below the entry's, `rax` left
open (`a`). -/
abbrev gS (g : Gprs) (a : BitVec 64) : Gprs :=
  { g with rax := a, rdx := g.rdi, rsp := g.rsp - 8, rsi := 7366559#64,
           rdi := BitVec.setWidth 64 (BitVec.ofNat 32 1) }

/-- The bytes at the `call`: `rax` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rax 8)

variable {F : Footprint} {Wl : List Rgn}

/-- The straight-line code to the `call` at 23. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8) i))
    (h : ∀ a fl, Q 23 (gS g a) fl (V0 V g)) : W_0 F Wl Q g f V := by
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

/-- `malloc_printerr (const char *str)` from its entry: the run reaches the callee's entry with the registers `gS` (some
`rax`), `rsp` 16 below the entry's, and the bytes `V0` with the return address `mpe_at + 28` stored at `rsp - 16`
(`kf`). -/
theorem mpe_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L mpe_at mpe)
    {cT : List Byte} (hinT : CodeIn L lms_at cT) (hT : 0 < cT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mpe_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (kf : ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (mpe_at.add 28) 8)) →
      Y.cpu.rip = lms_at → Y.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 16) →
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
  have hrip' : X.cpu.rip = mpe_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 23 ∧ (∃ a, g' = gS X.cpu.gpr a) ∧ V' = V0 V X.cpu.gpr)
    hK hA hrip' (vc_0 hs1 h8 fun a _ => ⟨rfl, ⟨a, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_23 _) hinT (tgt := 0) hT tgt_23 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gS X.cpu.gpr a).set 4 v) e16
  exact kf a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂'

end FV7z.Mpe
