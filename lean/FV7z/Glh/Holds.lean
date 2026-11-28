import FV7z.Glh.Cuts
import FV7z.Gle.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.Signed
/-!
# `GetLastError_noZero_HRESULT ()` (PLAN.md §M, M1)

7-Zip 26.06's `GetLastError_noZero_HRESULT ()` at `0x456000` in `7zzs` (`CPP/Windows/FileIO.cpp`; `objdump -d`):
`sub rsp, 8`, the `call` at 8 to `GetLastError` (`Gle.gle_at`), then `test eax, eax; je` (13, 15): for 0,
`mov eax, 0x80004005` (`E_FAIL`, 40) and `jmp` (45) back to 31; else `movzx edx, ax; or edx, 0x88000000;
test eax, eax; cmovg eax, edx` (17: `HRESULT_FROM_WIN32` for a positive code, the code itself for a negative one);
from 31 `add rsp, 8; ret` (35).

`GetLastError` is a hypothesis, as `__errno_location` in `FV7z/Gle/Holds.lean`: `ke` is a continuation at its
entry, given the run from its return (`rsp` 8 below the entry's, the return address as it was) and its own post `Pe`.

- `hrw`: the 32-bit result for the `rax` that `GetLastError` returns, as the code computes it.
- `vc_0`, `vc_13`, `vc_31`: the verification conditions of the pieces (`vc_13` through both ways to 31, `edx`
  whatever the `movzx`/`or` leave on the second).
- `glh_ok`: from the entry, through `GetLastError`, to the return address with `rax` = `hrw` of its result.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Glh

/-- The `call` to `GetLastError`. -/
def pcg : List Byte := [0xe8, 0xf3, 0xa1, 0x14, 0x00]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 1352179] 5) := by dec_rfl
theorem wc_8 : pcg <+: glh.drop 8 := by decide +kernel
theorem call_8 (feat : Features) : Dec feat glh 8 (FV7z.mk .call 64 [.rel 1352179] 5) :=
  Dec.shift (j := 8) (k := 0) (pcg_0 feat) wc_8 (Nat.zero_le _)
theorem tgt_8 : glh_at.add (8 + 5) + BitVec.ofNat 64 1352179 = Gle.gle_at.add 0 := by decide

theorem gle_lt : 0 < Gle.gle.length := by rw [Gle.gle_length]; decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_35 : pret <+: glh.drop 35 := by decide +kernel
theorem ret_35 (feat : Features) : Dec feat glh 35 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 35) (k := 0) (pret_0 feat) w_35 (Nat.zero_le _)

theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := by bv_omega
theorem ao {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).of = of := rfl

/-- The result for `GetLastError`'s `rax` = `a`: `E_FAIL` (`0x80004005`) for `eax` 0, `eax` itself if negative,
else `(ax) | 0x88000000`. -/
def hrw (a : BitVec 64) : BitVec 32 :=
  if a.setWidth 32 = 0#32 then 2147500037#32
  else if (a.setWidth 32).msb = true then a.setWidth 32
  else (a.setWidth 16).setWidth 32 ||| 2281701376#32

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8` to the `call` at 8. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 8 { g with rsp := g.rsp - 8#64 } fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- Back from `GetLastError`: both ways to 31, `rax` = `hrw` of the returned `rax`, `rdx` whatever. -/
theorem vc_13 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ rd fl, Q 31 { g with rax := (hrw g.rax).setWidth 64, rdx := rd } fl V) : W_13 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  by_cases hz : BitVec.setWidth 32 rax = 0#32
  · simp only [hrw, if_pos hz] at h
    have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
    wpx [W_13, W_40, W_17, o1, o2, o4, Op.zxr16, e, BitVec.and_self, Bool.true_eq_false, Bool.false_eq_true,
      false_implies, eq_self_iff_true, true_implies, implies_true]
    all_goals repeat' (first | exact h _ _ | apply And.intro | intro _)
  · have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
    by_cases hm : (BitVec.setWidth 32 rax).msb = true
    · simp only [hrw, if_neg hz, if_pos hm] at h
      wpx [W_13, W_40, W_17, o1, o2, o4, Op.zxr16, e, hm, cond_15, ao, BitVec.and_self, Bool.false_or,
        Bool.bne_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true, false_implies, eq_self_iff_true,
        true_implies, implies_true, ite_false, ite_true]
      all_goals repeat' (first | exact h _ _ | apply And.intro | intro _)
    · have hm' : (BitVec.setWidth 32 rax).msb = false := by simpa using hm
      simp only [hrw, if_neg hz, if_neg hm] at h
      wpx [W_13, W_40, W_17, o1, o2, o4, Op.zxr16, e, hm', cond_15, ao, BitVec.and_self, Bool.false_or,
        Bool.bne_false, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, eq_self_iff_true,
        true_implies, implies_true, ite_false, ite_true]
      all_goals repeat' (first | exact h _ _ | apply And.intro | intro _)

/-- `add rsp, 8` to the `ret` at 35. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 35 { g with rsp := g.rsp + 8#64 } fl V) : W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_31, o3]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `GetLastError_noZero_HRESULT ()` from its entry. At `GetLastError`'s entry the registers are the entry's with
`rsp` 16 below, the bytes with the return address pushed (`ke`); back at `glh_at + 13` (`Pe`), at the return address
with `rax` = `hrw` of the `rax` `GetLastError` returned, `rdx` some value, `rsp` 8 above the entry's (`kr`). -/
theorem glh_ok {Pe : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L glh_at glh) (hinE : CodeIn L Gle.gle_at Gle.gle)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = glh_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ke : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (glh_at.add 13) 8)) →
      Y.cpu.rip = Gle.gle_at →
      Y.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8#64 }.set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = glh_at.add 13 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V₁, X.cpu.gpr.rsp) = e₂.add j₂ → Pe Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat) (rd : BitVec 64), Pe Z V₁ →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V₁ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr =
        { Z.cpu.gpr with rax := (hrw Z.cpu.gpr.rax).setWidth 64, rdx := rd, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- to the `call` of `GetLastError`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 8 ∧ g' = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8#64 } ∧
      V' = V) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY0 : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hsY0]; exact q16 _
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_8 _) hinE (tgt := 0) gle_lt tgt_8
    (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine ke Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, hgY]) ?_
  -- back from `GetLastError`: both ways to 31
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hra hPe
  refine (c_13 prof).run c hin (fun j' g' _ V' => j' = 31 ∧
      (∃ rd, g' = { Z.cpu.gpr with rax := (hrw Z.cpu.gpr.rax).setWidth 64, rdx := rd }) ∧ V' = V₁)
    hKZ hAZ hrZ (vc_13 fun rd _ => ⟨rfl, ⟨rd, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, ⟨rd, rfl⟩, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  -- `add rsp, 8` to the `ret`
  have e31 : { U.cpu.gpr with rsp := U.cpu.gpr.rsp + 8#64 } =
      { Z.cpu.gpr with rax := (hrw Z.cpu.gpr.rax).setWidth 64, rdx := rd, rsp := X.cpu.gpr.rsp } := by
    rw [hgU, ← sa8 X.cpu.gpr.rsp, ← hzs]
    try rfl
  refine (c_31 prof).run c hin (fun j' g' _ V' => j' = 35 ∧
      g' = { Z.cpu.gpr with rax := (hrw Z.cpu.gpr.rax).setWidth 64, rdx := rd, rsp := X.cpu.gpr.rsp } ∧ V' = V₁)
    hKU hAU hrU (vc_31 fun _ => ⟨rfl, e31, rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ W t₅ hKW hAW hrW hgW -
  subst V₃
  have hsW : W.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgW]
  refine c.s_ret hKW hAW hin (lt_len (by decide)) hrW (ret_35 _) (by rw [hsW]; exact hl) hin₂ h₂
    (by rw [hsW]; exact hra) ?_
  rintro Z' t₆ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V₁ Z' t₆ rd hPe hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgW]
  try rfl

end FV7z.Glh
