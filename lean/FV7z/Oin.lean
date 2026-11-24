import FV7z.Ctor.Cx90
/-!
# The constructor at `0x59ea30` of the object at `0x79ece0` (PLAN.md G3, constructors)

`csuTg 95` calls the function at `0x59ea30` of `7zzs` with `rdi = O = 0x79ece0`. It stores `0` in the words at
`O + 0x48` and `O + 0x50`, `1` in the byte at `O + 0x58`, `0` in the dword at `O + 0x5c`, then clears the 16 bytes
from `O + 0x60` to `O + 0x70` one at a time (`rax` from `O + 0x60`, `rdx = O + 0x70`) and returns. It touches
only the 40 bytes from `O + 0x48` (`7990568` to `7990608`), `rax`, `rdx` and the flags.

- `oin`, `oin_pin`: the 61 bytes, the file's (by the kernel's evaluation of Zellic's ELF reader).
- `blk_0`, `blk_48`, `spj_58`: the two blocks and the loop's `jne`; `W_0`, `W_48`, `Wt`, `spAll`: the cut points
  `0` (the entry) and `48` (the loop's head), for `Seg.cfg`.
- `Inv`: at `48`, `rax` inside the 16 bytes, `rdx` their end, the registers a call keeps and the bytes outside the 40
  as at the entry (`Out`); the measure is the count of bytes left.
- `oin_ok`: called with `rdi = O`, the run reaches the return address, the registers a call keeps as at the entry
  (`Osv.Back`), the bytes outside the 40 as they were.
-/
namespace FV7z.Oin
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Ctor

/-! ## The code -/

/-- The function, `0x59ea30` to `0x59ea6d` of `7zzs`. -/
def oin : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0x47, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x47, 0x60,
  0x48, 0x8d, 0x57, 0x70, 0x48, 0xc7, 0x47, 0x50, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x47, 0x58, 0x01,
  0xc7, 0x47, 0x5c, 0x00, 0x00, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0xc6, 0x00, 0x00, 0x48, 0x83, 0xc0, 0x01, 0x48, 0x39, 0xd0, 0x75, 0xf4, 0xc3]

theorem oin_pin : Exe.bytesAt V2606.zzs.blob 0x59ea30 61 = some oin := by decide +kernel
theorem oin_length : oin.length = 61 := by decide +kernel

/-- Where the code lies in `7zzs`. -/
abbrev oin_at : Addr := 0x59ea30

theorem lt_len {j : Nat} (h : j < 61) : j < oin.length := oin_length ▸ h

theorem oin_0 : ∀ feat, Dec feat oin 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem oin_4 : ∀ feat, Dec feat oin 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 72 64), .imm 64 0] 8) := by
  dec_rfl
theorem oin_12 : ∀ feat, Dec feat oin 12 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 96 0)] 4) := by
  dec_rfl
theorem oin_16 : ∀ feat, Dec feat oin 16 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 7) none 1 112 0)] 4) := by
  dec_rfl
theorem oin_20 : ∀ feat, Dec feat oin 20 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 80 64), .imm 64 0] 8) := by
  dec_rfl
theorem oin_28 : ∀ feat, Dec feat oin 28 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 88 8), .imm 8 1] 4) := by
  dec_rfl
theorem oin_32 : ∀ feat, Dec feat oin 32 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 92 32), .imm 32 0] 7) := by
  dec_rfl
theorem oin_39 : ∀ feat, Dec feat oin 39 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl
theorem oin_48 : ∀ feat, Dec feat oin 48 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem oin_51 : ∀ feat, Dec feat oin 51 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem oin_55 : ∀ feat, Dec feat oin 55 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem oin_58 : ∀ feat, Dec feat oin 58 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551604] 2) := by dec_rfl
theorem oin_60 : ∀ feat, Dec feat oin 60 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-! ## The blocks and the cut points -/

/-- The stores before the loop. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 64 (some 7) none 1 72 0,
  Op.lea 64 0 (some 7) none 1 96,
  Op.lea 64 2 (some 7) none 1 112,
  Op.sti 64 (some 7) none 1 80 0,
  Op.sti 8 (some 7) none 1 88 1,
  Op.sti 32 (some 7) none 1 92 0,
  Op.nop]

theorem blk_0 (prof : Profile) : Blk prof oin 0 48 o0 :=
  .cons (oin_0 _) (OpI.endbr) (by decide) <|
  .cons (oin_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (oin_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (oin_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (oin_20 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (oin_28 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (oin_32 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (oin_39 _) (OpI.nop) (by decide) <|
  .nil 48

/-- The loop's body: a byte cleared, `rax` one more, compared with `rdx`. -/
def o1 : List Op := [
  Op.sti 8 (some 0) none 1 0 0,
  Op.add 64 0 (.i 1),
  Op.cmp 64 0 (.r 2)]

theorem blk_48 (prof : Profile) : Blk prof oin 48 58 o1 :=
  .cons (oin_48 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (oin_51 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (oin_55 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 58

theorem spj_58 (prof : Profile) : Sp prof oin oin_at 58 fun _ _ Q g f V =>
    (f.cond 5 = true → Q 48 g (rfz f) V) ∧ (f.cond 5 = false → Q 60 g (rfz f) V) :=
  Sp.jcc (j := 58) (tgt := 48) (oin_58 _) (lt_len (by decide)) (by decide) (lt_len (by decide))

def W_0 : Wpt := fun F Wl Q => wp F Wl o0 (Q 48)
theorem c_0 (prof : Profile) : Sp prof oin oin_at 0 W_0 := Sp.blk_then (blk_0 prof) (Sp.skip 48)

def W_48 : Wpt := fun F Wl Q => wp F Wl o1 fun g f V =>
    (f.cond 5 = true → Q 48 g (rfz f) V) ∧
    (f.cond 5 = false → Q 60 g (rfz f) V)
theorem c_48 (prof : Profile) : Sp prof oin oin_at 48 W_48 :=
  Sp.blk_then (blk_48 prof) (Sp.jcc_then (spj_58 prof) (Sp.skip 48) (Sp.skip 60))

/-- What the code from a cut point needs for `Q` at the next ones. -/
def Wt (ℓ : Nat) : Wpt :=
  if ℓ = 0 then W_0 else
  if ℓ = 48 then W_48 else
  fun _ _ _ _ _ _ => False

theorem spAll (prof : Profile) (ℓ : Nat) : Sp prof oin oin_at ℓ (Wt ℓ) :=
  Sp.table (c_0 prof) <|
  Sp.table (c_48 prof) <|
  Sp.never ℓ

/-! ## The invariant -/

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes outside the 40 from `O + 0x48` as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7990568 (7990568 + 40) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 17 ∧ g = g₀ ∧ g.rdi = 7990496#64 ∧ V = V₀) ∨
  (ℓ = 48 ∧ 7990592 ≤ g.rax.toNat ∧ g.rax.toNat < 7990608 ∧ n = 7990608 - g.rax.toNat ∧ g.rdx = 7990608#64 ∧
    Kp g₀ g ∧ Out V₀ V)

/-- `rax` one more, not yet `rdx`. -/
theorem inc_lt {x : BitVec 64} (h1 : 7990592 ≤ x.toNat) (h2 : x.toNat < 7990608) (hne : ¬ x + 1#64 = 7990608#64) :
    7990592 ≤ (x + 1#64).toNat ∧ (x + 1#64).toNat < 7990608 ∧ 7990608 - (x + 1#64).toNat < 7990608 - x.toNat := by
  bv_omega

/-- From the entry to the loop's head: the four stores, `rax = O + 0x60`, `rdx = O + 0x70`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi = 7990496#64)
    (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i)) (Q : Post)
    (hQ : ∀ g' f' V', g'.rax = 7990592#64 → g'.rdx = 7990608#64 → Kp g g' → Out V V' → Q 48 g' f' V') :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi
  subst hdi
  wpx -implicitDefEqProofs [W_0, o0]
  intros
  refine ⟨ft_at hw (by decide) (by decide) (by decide), ft_at hw (by decide) (by decide) (by decide),
    ft_at hw (by decide) (by decide) (by decide), ft_at hw (by decide) (by decide) (by decide), ?_⟩
  intros
  refine hQ _ _ _ (by decide) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  refine out_at (out_at (out_at (out_at (fun _ _ => rfl) ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_ <;>
    first | exact toBytesLE_length _ _ | decide

/-- One round of the loop: the byte at `rax` cleared, then back to the head with `rax` one more, or on to the `ret`
after the last. -/
theorem vc_48 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (h1 : 7990592 ≤ g.rax.toNat)
    (h2 : g.rax.toNat < 7990608) (hdx : g.rdx = 7990608#64) (hK : Kp g₀ g) (hO : Out V₀ V)
    (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i)) (Q : Post)
    (hQ1 : ∀ g' f' V', 7990592 ≤ g'.rax.toNat → g'.rax.toNat < 7990608 →
      7990608 - g'.rax.toNat < 7990608 - g.rax.toNat → g'.rdx = 7990608#64 → Kp g₀ g' → Out V₀ V' →
      Q 48 g' f' V')
    (hQ2 : ∀ g' f' V', Kp g₀ g' → Out V₀ V' → Q 60 g' f' V') : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 hdx hQ1
  subst hdx
  wpx -implicitDefEqProofs [W_48, o1]
  intros
  refine ⟨ft_at hw (by decide) (by omega) (by omega), fun h => ?_, fun _ => ?_⟩
  · have hne : ¬ rax + 1#64 = 7990608#64 := by simpa using h
    have hi := inc_lt h1 h2 hne
    exact hQ1 _ _ _ hi.1 hi.2.1 hi.2.2 rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by decide))
  · exact hQ2 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by decide))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the 40 as at the entry. -/
theorem vc (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 60 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, hdi, rfl⟩ | ⟨rfl, h1, h2, rfl, hdx, hK, hO⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    refine vc_0 hdi hw _ fun g' f' V' ha hd hK hO => Or.inl ⟨16, by decide, Or.inr ⟨rfl, ?_, ?_, ?_, hd, hK, hO⟩⟩
    all_goals (rw [ha]; decide)
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_48 h1 h2 hdx hK hO hw
    · intro g' f' V' h1' h2' hlt hd hK' hO'
      exact Or.inl ⟨_, hlt, Or.inr ⟨rfl, h1', h2', rfl, hd, hK', hO'⟩⟩
    · intro g' f' V' hK' hO'
      exact Or.inr ⟨rfl, hK', hO'⟩

/-! ## The call -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- The function at `0x59ea30` from its entry with `rdi = O` and the stack pointer at the return address: the run
reaches the return address, the registers a call keeps as at the entry, the bytes outside the 40 from `O + 0x48` as
they were. -/
theorem oin_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L oin_at oin) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = oin_at) (hdi : X.cpu.gpr.rdi = 7990496#64)
    (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i)) (hlr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsd : X.cpu.gpr.rsp.toNat + 8 ≤ 7990568 ∨ 7990608 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Out V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (spAll prof) (Inv X.cpu.gpr V)
    (fun j' g' _ V' => j' = 60 ∧ Kp X.cpu.gpr g' ∧ Out V V') (vc hw X.cpu.gpr V) ?_ 17 0 hK hA
    (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, hdi, rfl⟩)
  rintro j' g fl V' ⟨rfl, hKp, hO⟩ Y t' hKY hAY hrY rfl -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := hKp.1
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (oin_60 _) (by rw [hsY]; exact hlr) hin₂ h₂ ?_ ?_
  · rw [hsY]
    exact (rdq_eq hs8 fun a h1 h2 => hO a (by omega)).trans hra
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k V' Z t'' hKZ hAZ hO hrZ ?_
  rw [hgZ]
  refine ⟨?_, hKp.2.1, hKp.2.2.1, hKp.2.2.2.1, hKp.2.2.2.2.1, hKp.2.2.2.2.2.1, hKp.2.2.2.2.2.2⟩
  show Y.cpu.gpr.rsp + 8 = _
  rw [hsY]
  rfl

end FV7z.Oin
