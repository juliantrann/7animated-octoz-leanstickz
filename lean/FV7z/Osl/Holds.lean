import FV7z.Osl.Cuts
import FV7z.Ftr.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Lock2
/-!
# `NWindows::NFile::NIO::COutFile::SetLength (length)` (PLAN.md §M, M1)

7-Zip 26.06's `COutFile::SetLength (length)` at `0x456390` in `7zzs` (`CPP/Windows/FileIO.cpp`; `objdump -d`),
`this` in `rdi`, `length` in `rsi`: `return ftruncate (_handle, length) == 0;` as `sub rsp, 8; mov edi, [rdi]`, the
`call` (10) of `ftruncate64` (`Ftr.ftr_at`), then `test eax, eax; sete al; add rsp, 8; ret` (24). As
`FV7z/Fls/Holds.lean`, the same shape.

The callee is a hypothesis (`kf`): a continuation at its entry, given the run from its return (`osl_at + 15`, `rsp` 8
below the entry's, the return address left as it was, and the callee's own post `Pc`) to the return address (`kr`),
with `al` = 1 if `ftruncate`'s `eax` is 0, else 0 (bits 63–8 of `rax` whatever `sete` leaves).

- `gC`: the registers at the `call`, `edi` = `_handle` (the 4 bytes at `this`).
- `vc_0`, `vc_15z`, `vc_15n`: the verification conditions of the pieces (`eax` 0 or not after the call).
- `osl_ok`: from the entry, through `ftruncate64`, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Osl

/-- The `call` to `ftruncate64`. -/
def pcall : List Byte := [0xe8, 0x51, 0x01, 0x21, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 2163025] 5) := by dec_rfl
theorem wc_10 : pcall <+: osl.drop 10 := by decide +kernel
theorem call_10 (feat : Features) : Dec feat osl 10 (FV7z.mk .call 64 [.rel 2163025] 5) :=
  Dec.shift (j := 10) (k := 0) (pcall_0 feat) wc_10 (Nat.zero_le _)

theorem tgt_10 : osl_at.add (10 + 5) + BitVec.ofNat 64 2163025 = Ftr.ftr_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_24 : pret <+: osl.drop 24 := by decide +kernel
theorem ret_24 (feat : Features) : Dec feat osl 24 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 24) (k := 0) (pret_0 feat) w_24 (Nat.zero_le _)

/-- The registers at the `call`: `rsp` 8 lower, `edi` = `_handle`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rsp := g.rsp - 8#64,
      rdi := (rdd(V, g.rdi)).setWidth 64 }

theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := by bv_omega

/-- A low byte made of a `wrLo` (`setcc`), bit by bit: equal to a literal (as in `FV7z/Dde/Holds.lean`). -/
local macro "lob" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8; mov edi, [rdi]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (h : ∀ fl, Q 10 (gC V g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | exact f1 | apply And.intro | intro _)

/-- Back from `ftruncate64` with `eax` 0: `test eax, eax; sete al; add rsp, 8` to the `ret` at 24, `al` 1. -/
theorem vc_15z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 = 0#32)
    (h : ∀ ra fl, ra.setWidth 8 = 1#8 → Q 24 { g with rax := ra, rsp := g.rsp + 8#64 } fl V) :
    W_15 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_15, o1, Op.setcc, e, BitVec.and_self, decide_true, BitVec.ofBool_true, BitVec.reduceSetWidth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ _ (by lob) | apply And.intro | intro _)

/-- Back from `ftruncate64` with `eax` not 0: as `vc_15z`, `al` 0. -/
theorem vc_15n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 ≠ 0#32)
    (h : ∀ ra fl, ra.setWidth 8 = 0#8 → Q 24 { g with rax := ra, rsp := g.rsp + 8#64 } fl V) :
    W_15 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_15, o1, Op.setcc, e, BitVec.and_self, BitVec.ofBool_false, BitVec.reduceSetWidth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ _ (by lob) | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COutFile::SetLength (length)` (`this` = `rdi`) from its entry. At `ftruncate64`'s entry the registers are `gC`
with `rsp` 16 below the entry's and the return address into `SetLength` pushed (`kf`); if `ftruncate64` returns to
`osl_at + 15` with `rsp` as at its call and `SetLength`'s return address as it was, the run reaches that return
address with `rsp` restored and `al` = 1 if `ftruncate64`'s `eax` is 0, else 0 (`kr`). -/
theorem osl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L osl_at osl)
    (hinC : CodeIn L Ftr.ftr_at Ftr.ftr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = osl_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (osl_at.add 15) 8)) →
      Y.cpu.rip = Ftr.ftr_at.add 0 → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = osl_at.add 15 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat) (ra : BitVec 64), Pc Z V' →
      ra.setWidth 8 = (if Z.cpu.gpr.rax.setWidth 32 = 0#32 then 1#8 else 0#8) → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 10 ∧ g' = gC V X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 f1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY0 : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hsY0]; exact q16 _
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_10 _) hinC (tgt := 0)
    (by rw [Ftr.ftr_length]; decide) tgt_10 (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from `ftruncate64`
  intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
  by_cases hz : Z.cpu.gpr.rax.setWidth 32 = 0#32
  · refine (c_15 prof).run c hin (fun j' g' _ V'' => j' = 24 ∧
        (∃ ra : BitVec 64, g' = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp } ∧ ra.setWidth 8 = 1#8) ∧
        V'' = V') hKZ hAZ hrZ (vc_15z hz fun ra _ hra => ⟨rfl, ⟨ra, by rw [hzs, sa8], hra⟩, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, ⟨ra, rfl, hra⟩, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_24 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ ra hPc (by rw [if_pos hz]; exact hra) hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl
  · refine (c_15 prof).run c hin (fun j' g' _ V'' => j' = 24 ∧
        (∃ ra : BitVec 64, g' = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp } ∧ ra.setWidth 8 = 0#8) ∧
        V'' = V') hKZ hAZ hrZ (vc_15n hz fun ra _ hra => ⟨rfl, ⟨ra, by rw [hzs, sa8], hra⟩, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, ⟨ra, rfl, hra⟩, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_24 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ ra hPc (by rw [if_neg hz]; exact hra) hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl

end FV7z.Osl
