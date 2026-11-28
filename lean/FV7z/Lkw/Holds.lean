import FV7z.Lkw.Cuts
import FV7z.Lnk.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Lock2
/-!
# `NWindows::NFile::NIO::SetSymLink (from, to)` (PLAN.md §M, M1)

7-Zip 26.06's `NIO::SetSymLink (from, to)` at `0x455880` in `7zzs` (`CPP/Windows/FileDir.cpp`; `objdump -d`;
its bytes folded with one other wrapper), `from` in `rdi`, `to` in `rsi`: `mov r8, rdi; sub rsp, 8;
mov rdi, rsi; mov rsi, r8` (the arguments swapped), the `call` (17) of `link` (`Lnk.lnk_at`), then
`test eax, eax; sete al; add rsp, 8; ret` (31). As `FV7z/Osl/Holds.lean`, the same shape.

The callee is a hypothesis (`kf`): a continuation at its entry, given the run from its return (`lkw_at + 22`, `rsp` 8
below the entry's, the return address left as it was, and the callee's own post `Pc`) to the return address (`kr`),
with `al` = 1 if `link`'s `eax` is 0, else 0 (bits 63–8 of `rax` whatever `sete` leaves).

- `gC`: the registers at the `call`.
- `vc_0`, `vc_22z`, `vc_22n`: the verification conditions of the pieces (`eax` 0 or not after the call).
- `lkw_ok`: from the entry, through `link`, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lkw

/-- The `call` to `link`. -/
def pcall : List Byte := [0xe8, 0xda, 0x04, 0x21, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 2163930] 5) := by dec_rfl
theorem wc_17 : pcall <+: lkw.drop 17 := by decide +kernel
theorem call_17 (feat : Features) : Dec feat lkw 17 (FV7z.mk .call 64 [.rel 2163930] 5) :=
  Dec.shift (j := 17) (k := 0) (pcall_0 feat) wc_17 (Nat.zero_le _)

theorem tgt_17 : lkw_at.add (17 + 5) + BitVec.ofNat 64 2163930 = Lnk.lnk_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_31 : pret <+: lkw.drop 31 := by decide +kernel
theorem ret_31 (feat : Features) : Dec feat lkw 31 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 31) (k := 0) (pret_0 feat) w_31 (Nat.zero_le _)

/-- The registers at the `call`: `rsp` 8 lower, `rdi` and `rsi` swapped, `r8` = the entry's `rdi`. -/
abbrev gC (g : Gprs) : Gprs := { g with r8 := g.rdi, rsp := g.rsp - 8#64, rdi := g.rsi, rsi := g.rdi }

theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := by bv_omega

/-- A low byte made of a `wrLo` (`setcc`), bit by bit: equal to a literal (as in `FV7z/Dde/Holds.lean`). -/
local macro "lob" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

variable {F : Footprint} {Wl : List Rgn}

/-- `mov r8, rdi; sub rsp, 8; mov rdi, rsi; mov rsi, r8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 17 (gC g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- Back from `link` with `eax` 0: `test eax, eax; sete al; add rsp, 8` to the `ret` at 31, `al` 1. -/
theorem vc_22z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 = 0#32)
    (h : ∀ ra fl, ra.setWidth 8 = 1#8 → Q 31 { g with rax := ra, rsp := g.rsp + 8#64 } fl V) :
    W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_22, o1, Op.setcc, e, BitVec.and_self, decide_true, BitVec.ofBool_true, BitVec.reduceSetWidth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ _ (by lob) | apply And.intro | intro _)

/-- Back from `link` with `eax` not 0: as `vc_22z`, `al` 0. -/
theorem vc_22n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 ≠ 0#32)
    (h : ∀ ra fl, ra.setWidth 8 = 0#8 → Q 31 { g with rax := ra, rsp := g.rsp + 8#64 } fl V) :
    W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_22, o1, Op.setcc, e, BitVec.and_self, BitVec.ofBool_false, BitVec.reduceSetWidth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ _ (by lob) | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NWindows::NFile::NIO::SetSymLink (from, to)` from its entry. At `link`'s entry the registers are `gC`
with `rsp` 16 below the entry's and the return address into `SetSymLink` pushed (`kf`); if `link` returns to
`lkw_at + 22` with `rsp` as at its call and `SetSymLink`'s return address as it was, the run reaches that return
address with `rsp` restored and `al` = 1 if `link`'s `eax` is 0, else 0 (`kr`). -/
theorem lkw_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lkw_at lkw)
    (hinC : CodeIn L Lnk.lnk_at Lnk.lnk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lkw_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (lkw_at.add 22) 8)) →
      Y.cpu.rip = Lnk.lnk_at.add 0 → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = lkw_at.add 22 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat) (ra : BitVec 64), Pc Z V' →
      ra.setWidth 8 = (if Z.cpu.gpr.rax.setWidth 32 = 0#32 then 1#8 else 0#8) → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 17 ∧ g' = gC X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY0 : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hsY0]; exact q16 _
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_17 _) hinC (tgt := 0)
    (by rw [Lnk.lnk_length]; decide) tgt_17 (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from `link`
  intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
  by_cases hz : Z.cpu.gpr.rax.setWidth 32 = 0#32
  · refine (c_22 prof).run c hin (fun j' g' _ V'' => j' = 31 ∧
        (∃ ra : BitVec 64, g' = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp } ∧ ra.setWidth 8 = 1#8) ∧
        V'' = V') hKZ hAZ hrZ (vc_22z hz fun ra _ hra => ⟨rfl, ⟨ra, by rw [hzs, sa8], hra⟩, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, ⟨ra, rfl, hra⟩, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_31 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ ra hPc (by rw [if_pos hz]; exact hra) hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl
  · refine (c_22 prof).run c hin (fun j' g' _ V'' => j' = 31 ∧
        (∃ ra : BitVec 64, g' = { Z.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp } ∧ ra.setWidth 8 = 0#8) ∧
        V'' = V') hKZ hAZ hrZ (vc_22n hz fun ra _ hra => ⟨rfl, ⟨ra, by rw [hzs, sa8], hra⟩, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, ⟨ra, rfl, hra⟩, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_31 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ ra hPc (by rw [if_neg hz]; exact hra) hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl

end FV7z.Lkw
