import FV7z.Ffl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `__fortify_fail` (PLAN.md §M, M1)

glibc's `__fortify_fail (const char *msg)` at `0x669810` in `7zzs` (`debug/fortify_fail.c`; `objdump -d`), which
does not return: `push rbp; lea rbp, fmt; push rbx; mov rbx, rdi; sub rsp, 8`, then a loop (24) of `mov rdx, rbx;
mov rsi, rbp; mov edi, 1; xor eax, eax; call __libc_message` (37, `lms_at` = `0x627710`) with `rdi` = 1
(`do_abort`), `rsi` = the format `"*** %s ***: terminated\n"` (`0x6f2cb1`), `rdx` = `msg`. The `jmp` back to 24
after the `call` is never reached: the callee does not return.

The callee is a hypothesis (`kf`), a continuation at its entry, as in `FV7z/Scf/Holds.lean` (whose callee this is).
`rax` at the `call` (`xor eax, eax`) is left open (`gS`).

- `gS`, `V0`: the registers and the bytes at the `call` (`rbp`, `rbx` pushed 8 and 16 below the entry's `rsp`).
- `vc_0`: the verification condition of the one piece (0 to 37, through the label at 24).
- `ffl_ok`: from the entry to the callee's entry, with `gS` and `V0` and the return address `ffl_at + 42` stored 32
  below the entry's `rsp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ffl

/-- The callee, `__libc_message`. -/
abbrev lms_at : Addr := 0x627710

/-- The `call` to `__libc_message`. -/
def pcall : List Byte := [0xe8, 0xd6, 0xde, 0xfb, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709280982] 5) := by dec_rfl
theorem wc_37 : pcall <+: ffl.drop 37 := by decide +kernel
theorem call_37 (feat : Features) : Dec feat ffl 37 (FV7z.mk .call 64 [.rel 18446744073709280982] 5) :=
  Dec.shift (j := 37) (k := 0) (pcall_0 feat) wc_37 (Nat.zero_le _)
theorem tgt_37 :
    ffl_at.add (37 + 5) + BitVec.ofNat 64 18446744073709280982 = lms_at.add 0 := by decide

/-- The registers at the `call`: `rdi` 1, `rsi` = `rbp` the format, `rdx` = `rbx` the message, `rsp` 24 below the
entry's, `rax` left open (`a`). -/
abbrev gS (g : Gprs) (a : BitVec 64) : Gprs :=
  { g with
      rax := a,
      rdx := g.rdi,
      rbx := g.rdi,
      rsp := g.rsp - 8 - 8 - 8,
      rbp := 7285937#64,
      rsi := 7285937#64,
      rdi := BitVec.setWidth 64 (BitVec.ofNat 32 1) }

/-- The bytes at the `call`: `rbp`, then `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

variable {F : Footprint} {Wl : List Rgn}

/-- The straight-line code to the `call` at 37. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ a fl, Q 37 (gS g a) fl (V0 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gS, V0] at hs1 hs2 h ⊢
  wpx [W_0, W_24, o0, o1]
  all_goals repeat'
    first
    | exact h _ _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__fortify_fail (const char *msg)` from its entry: the run reaches the callee's entry with the registers `gS`
(some `rax`), `rsp` 32 below the entry's, and the bytes `V0` with the return address `ffl_at + 42` stored at
`rsp - 32` (`kf`). -/
theorem ffl_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ffl_at ffl)
    {cT : List Byte} (hinT : CodeIn L lms_at cT) (hT : 0 < cT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ffl_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (kf : ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ffl_at.add 42) 8)) →
      Y.cpu.rip = lms_at → Y.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 32) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have t1 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (X.cpu.gpr.rsp - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 24 := by
    rw [BitVec.toNat_sub, t2]; simp <;> omega
  have t4 : (X.cpu.gpr.rsp - 8 - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 32 := by
    rw [BitVec.toNat_sub, t3]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := BitVec.eq_of_toNat_eq (by rw [t2, tn16])
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := BitVec.eq_of_toNat_eq (by rw [t4, tn32])
  have hs2' : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := by rw [e16]; exact hs2
  have hrip' : X.cpu.rip = ffl_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧ (∃ a, g' = gS X.cpu.gpr a) ∧ V' = V0 V X.cpu.gpr)
    hK hA hrip' (vc_0 hs1 hs2' fun a _ => ⟨rfl, ⟨a, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_37 _) hinT (tgt := 0) hT tgt_37 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gS X.cpu.gpr a).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gS X.cpu.gpr a).set 4 v) e32
  exact kf a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂'

end FV7z.Ffl
