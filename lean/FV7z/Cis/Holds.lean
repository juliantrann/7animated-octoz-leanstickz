import FV7z.Cis.Cuts
import FV7z.C64.Code
import FV7z.C64.Blocks
import FV7z.Lemmas.LeafRet
/-!
# `ConvertInt64ToString` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertInt64ToString (val, s)` at `0x44aea0` in `7zzs` (`CPP/Common/IntToString.cpp`; `objdump -d`),
`val` in `rdi`, `s` in `rsi`: a negative `val` (its top bit set, `jns` not taken) gives the byte '-' (45) at `s`, then
`rdi` = `-val` (`0 - val`) and `rsi` = `s + 1` (9); then a tail jump (19) to `ConvertUInt64ToString` (`C64.c64_at`).

The callee is a hypothesis (`kf`), as in `FV7z/Sos/Holds.lean`; `C64.c64_ok` is its contract.

- `gC`, `VC`: the registers and the bytes at the jump.
- `vc_0`: from the entry to the jump; `cis_ok`: from the entry to `ConvertUInt64ToString`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cis

set_option linter.unusedSimpArgs false

/-- The jump to `ConvertUInt64ToString`. -/
def pjm : List Byte := [0xe9, 0x78, 0xfd, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709550968] 5) := by dec_rfl
theorem wj_19 : pjm <+: cis.drop 19 := by decide +kernel
theorem jmp_19 (feat : Features) : Dec feat cis 19 (FV7z.mk .jmp 64 [.rel 18446744073709550968] 5) :=
  Dec.shift (j := 19) (k := 0) (pjm_0 feat) wj_19 (Nat.zero_le _)

/-- The registers at the jump: `-val` and `s + 1` for a negative `val`. -/
def gC (g : Gprs) : Gprs :=
  if g.rdi.msb = true then { g with rdi := 0 - g.rdi, rsi := g.rsi + 1#64 } else g

/-- The bytes at the jump: '-' at `s` for a negative `val`. -/
def VC (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if g.rdi.msb = true then Vst V g.rsi (toBytesLE 45#8 1) else V

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the jump. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ws : g.rdi.msb = true → ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 19 ∧ g' = gC g ∧ V' = VC V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ws
  cases hm : rdi.msb
  · simp only [gC, VC, hm, Bool.false_eq_true, ↓reduceIte]
    wpx [W_0, W_9, o0, o1, BitVec.and_self, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, eq_self_iff_true, and_self, implies_true, true_implies]
    all_goals repeat' (first | exact rfl | exact trivial | assumption | apply And.intro | intro _)
  · simp only [gC, VC, hm, eq_self_iff_true, ↓reduceIte]
    have ws' := ws hm
    wpx [W_0, W_9, o0, o1, BitVec.and_self, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, eq_self_iff_true, and_self, implies_true, true_implies]
    all_goals repeat' (first | exact rfl | exact trivial | assumption | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `ConvertInt64ToString (val, s)` from its entry to `ConvertUInt64ToString`'s entry: the registers `gC`, the bytes
`VC`. -/
theorem cis_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cis_at cis) (hinC : CodeIn L C64.c64_at C64.c64)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cis_at)
    (ws : X.cpu.gpr.rdi.msb = true → ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (VC V X.cpu.gpr) →
      Y.cpu.rip = C64.c64_at → Y.cpu.gpr = gC X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 19 ∧ g' = gC X.cpu.gpr ∧ V' = VC V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 ws) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_19 _) hinC (C64.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Cis
