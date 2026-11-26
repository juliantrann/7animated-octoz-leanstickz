import FV7z.Uc4.Cuts
import FV7z.Usl.Code
import FV7z.Usl.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::UString (const wchar_t *s1, unsigned num1, const wchar_t *s2, unsigned num2)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (s1, num1, s2, num2)` at `0x44d2e0` in `7zzs` (`CPP/Common/MyString.cpp`), `this`
in `rdi`, `s1` in `rsi`, `num1` in `edx`, `s2` in `rcx`, `num2` in `r8d`: `SetStartLen (num1 + num2)` (`call` at 30
to `Usl.usl_at`), `wmemcpy (_chars, s1, num1)` (`call` at 48 to `Wmc.wmc_at`; `_chars` the 8 bytes at `this`), then
a tail jump (71) to `wmemcpy (_chars + num1, s2, num2 + 1)`. `push r14; push r13; push r12; push rbp; push rbx`,
`r14` = `s1`, `r13` = `s2`, `r12` = `this` (then `_chars`), `rbp` = `num2`, `rbx` = `num1` across the calls, the five
popped before the jump.

The callees are hypotheses (`ku`, `kw`, `kr`), as in `FV7z/Ucc/Holds.lean`: a continuation at each entry, given the
run from its return (`rsp` 40 below the entry's, the kept registers as the caller left them, the saved registers as
they were: `Sv`) and the callee's own post (`Pu`, `Pw`).

- `zw`, `V0`, `gC`: a 32-bit value zero-extended; the bytes and the registers at the first `call`.
- `gW`: the registers at the `call` of `wmemcpy`.
- `Sv`: the saved `rbx`, `rbp`, `r12`, `r13`, `r14` in the bytes.
- `vc_0`, `vc_35`, `vc_53`: the verification conditions of the pieces.
- `uc4_ok`: from the entry, through the callees, to the second `wmemcpy`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uc4

/-- The `call`s to `SetStartLen` and `wmemcpy`. -/
def pcu : List Byte := [0xe8, 0x5d, 0xfd, 0xff, 0xff]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 18446744073709550941] 5) := by dec_rfl
theorem wc_30 : pcu <+: uc4.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat uc4 30 (FV7z.mk .call 64 [.rel 18446744073709550941] 5) :=
  Dec.shift (j := 30) (k := 0) (pcu_0 feat) wc_30 (Nat.zero_le _)
theorem tgt_30 : uc4_at.add (30 + 5) + BitVec.ofNat 64 18446744073709550941 = Usl.usl_at.add 0 := by decide
def pcw : List Byte := [0xe8, 0xeb, 0xff, 0x20, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2162667] 5) := by dec_rfl
theorem wc_48 : pcw <+: uc4.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat uc4 48 (FV7z.mk .call 64 [.rel 2162667] 5) :=
  Dec.shift (j := 48) (k := 0) (pcw_0 feat) wc_48 (Nat.zero_le _)
theorem tgt_48 : uc4_at.add (48 + 5) + BitVec.ofNat 64 2162667 = Wmc.wmc_at.add 0 := by decide

/-- The jump to `wmemcpy`. -/
def pjm : List Byte := [0xe9, 0xd4, 0xff, 0x20, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2162644] 5) := by dec_rfl
theorem wj_71 : pjm <+: uc4.drop 71 := by decide +kernel
theorem jmp_71 (feat : Features) : Dec feat uc4 71 (FV7z.mk .jmp 64 [.rel 2162644] 5) :=
  Dec.shift (j := 71) (k := 0) (pjm_0 feat) wj_71 (Nat.zero_le _)
theorem tgt_71 : uc4_at.add (71 + 5) + BitVec.ofNat 64 2162644 = Wmc.wmc_at.add 0 := by decide

/-- A 32-bit register value zero-extended. -/
abbrev zw (x : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 x)

/-- The bytes at the first `call`: `r14`, `r13`, `r12`, `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `r14` = `s1`, `r13` = `s2`, `r12` = `this`, `rbp` = `num2`, `rbx` = `num1`,
`esi` = `num1 + num2`, 40 below the entry. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with r14 := g.rsi, r13 := g.rcx, r12 := g.rdi, rbp := zw g.r8, rbx := zw g.rdx,
           rsi := zw (zw g.rdx + g.r8), rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The registers at the `call` of `wmemcpy` for the bytes `V` (`z` the registers back from `SetStartLen`, `x` the
entry's): `rdi` = `r12` = `_chars`, `rsi` = `s1`, `rdx` = `num1`. -/
abbrev gW (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with r12 := rdq(V, x.rdi), rdx := z.rbx, rsi := z.r14, rdi := rdq(V, x.rdi) }

/-- The saved `rbx`, `rbp`, `r12`, `r13`, `r14` (the entry's `x`) in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) : Prop :=
  rdq(V, x.rsp - 40) = x.rbx ∧ rdq(V, x.rsp - 32) = x.rbp ∧ rdq(V, x.rsp - 24) = x.r12 ∧
    rdq(V, x.rsp - 16) = x.r13 ∧ rdq(V, x.rsp - 8) = x.r14

variable {F : Footprint} {Wl : List Rgn}

/-- `push r14; mov r14, rsi; push r13; mov r13, rcx; push r12; mov r12, rdi; push rbp; mov ebp, r8d; push rbx;
mov ebx, edx; lea esi, [rbx + r8]` to the `call` at 30. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 hs5 ⊢
  wpx [W_0, o0, V0, gC, zw]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov r12, [r12]; mov rdx, rbx; mov rsi, r14; mov rdi, r12` to the `call` at 48. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (h12 : g.r12 = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i))
    (h : ∀ fl, Q 48 { g with r12 := rdq(V, p), rdx := g.rbx, rsi := g.r14, rdi := rdq(V, p) } fl V) :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 fp h ⊢
  subst h12
  wpx [W_35, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `wmemcpy`: `lea rdi, [r12 + rbx * 4]; lea edx, [rbp + 1]; pop rbx; mov rsi, r13; pop rbp; pop r12;
pop r13; pop r14` to the jump at 71. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 71
      { g with
          rdi := g.r12 + g.rbx * 4#64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rbp + 1#64)),
          rbx := rdq(V, g.rsp),
          rsi := g.r13,
          rbp := rdq(V, g.rsp + 8),
          r12 := rdq(V, g.rsp + 8 + 8),
          r13 := rdq(V, g.rsp + 8 + 8 + 8),
          r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 + 8 + 8 } fl V) :
    W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl0 hl1 hl2 hl3 hl4 h ⊢
  wpx [W_53, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (s1, num1, s2, num2)` from its entry. At `SetStartLen`'s entry the registers are `gC`, `rsp` 48
below the entry's, the bytes `V0` with the return address pushed (`ku`); back at `uc4_at + 35` (`Sv`, `Pu`), at
`wmemcpy`'s entry with the registers `gW` (`kw`); back at `uc4_at + 53` (`Pw`), at `wmemcpy`'s entry again with
`rdi` = `_chars + 4 num1`, `rsi` = `s2`, `edx` = `num2 + 1` and the saved registers back (`kr`). -/
theorem uc4_ok {Pu : State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uc4_at uc4) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uc4_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uc4_at.add 35) 8)) →
      Y.cpu.rip = Usl.usl_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = uc4_at.add 35 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        Sv V₁ X.cpu.gpr → Pu Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (uc4_at.add 53) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = uc4_at.add 53 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Sv V₂ X.cpu.gpr → Pw Z Zw V₂ →
        GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z Zw : State) (V₂ : Addr → Byte) (Y : State) (t' : Nat), Pw Z Zw V₂ → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V₂ → Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Zw.cpu.gpr with
          rdi := Zw.cpu.gpr.r12 + Zw.cpu.gpr.rbx * 4#64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (Zw.cpu.gpr.rbp + 1#64)),
          rbx := X.cpu.gpr.rbx, rsi := Zw.cpu.gpr.r13, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, r14 := X.cpu.gpr.r14, rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have a32 : X.cpu.gpr.rsp - 40 + 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have a24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40) i) := fun i hi => c.hws _ (hs5 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = uc4_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `SetStartLen`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
      (by rw [e40]; exact hs5)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_30 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_30 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c48] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) := by rw [hg₂, hsY, c48, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `SetStartLen`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hz12 hsv1 hPu
  refine (c_35 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ g' = gW V₁ Z.cpu.gpr X.cpu.gpr ∧ V' = V₁) hKZ hAZ hrZ
    (vc_35 hz12 fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₃]; exact hzs
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3', c48]; exact hs6
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_48 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
    tgt_48 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', c48] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₄, hs3', c48, hg₃]
  refine kw Z V₁ hPu Y₄ t₅ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from `wmemcpy`
  intro Zw V₂ t₆ hKw hAw hrw hws hsv2 hPw
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hsv2
  refine (c_53 prof).run c hin (fun j' g' _ V' => j' = 71 ∧
      g' = { Zw.cpu.gpr with
          rdi := Zw.cpu.gpr.r12 + Zw.cpu.gpr.rbx * 4#64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (Zw.cpu.gpr.rbp + 1#64)),
          rbx := X.cpu.gpr.rbx, rsi := Zw.cpu.gpr.r13, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, r14 := X.cpu.gpr.r14, rsp := X.cpu.gpr.rsp } ∧ V' = V₂) hKw hAw hrw
    (vc_53 (by rw [hws]; exact h40) (by rw [hws, a32]; exact h32) (by rw [hws, a32, a24]; exact h24)
      (by rw [hws, a32, a24, a16]; exact h16) (by rw [hws, a32, a24, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hws, a32, a24, a16, a8, e8, hb1, hb2, hb3, hb4, hb5], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
  subst V₃
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_71 _) hinW (Wmc.lt_len (j := 0) (by decide))
    tgt_71 ?_
  rintro Y₅ t₈ hK₅ hA₅ ⟨hr₅, hg₅⟩
  exact kr Z Zw V₂ Y₅ t₈ hPw hK₅ hA₅ (by rw [hr₅, addr_add_zero]) (by rw [hg₅, hgU])

end FV7z.Uc4
