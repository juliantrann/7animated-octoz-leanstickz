import FV7z.Usl.Cuts
import FV7z.Onw
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `AString::SetStartLen` (PLAN.md §M, M1)

7-Zip 26.06's `UString::SetStartLen (len)` at `0x44d060` in `7zzs` (`CPP/Common/MyString.cpp`): `_chars` (the 8
bytes at `this`) = NULL, `_chars = new wchar_t[len + 1]` (`call` at 33 to `operator new`, `Onw.onw_at + 64`, with
`4 len + 4` bytes), then `_len` (the 4 bytes at `this + 8`) and `_limit` (at `this + 12`) = `len`. `push rbp; push
rbx; sub rsp, 8`, `rbx` = `this` and `rbp` = `len` across the call, `add rsp, 8; pop rbx; pop rbp; ret` (53).
As `FV7z/Asl/Holds.lean` (`AString`'s), but for the size and `rax` = `len` at the call.

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`usl_at + 38`, `rsp` 24 below the entry's, `rbx` = `this`, `rbp` = `len`, the saved `rbx`, `rbp` and the return
address left as they were, and the callee's own post `Pc`) to the return address.

- `zl`, `gC`, `V0`: `len` zero-extended; the registers and the bytes at the `call`.
- `V1`: the bytes after the stores of `_len`, `_limit` and `_chars`.
- `vc_0`, `vc_38`: the verification conditions of the two pieces.
- `usl_ok`: from the entry, through the callee, to the return address with `_len` = `_limit` = `len`, `_chars` =
  the callee's `rax`, and `rbx`, `rbp`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Usl

/-- The `call` to `operator new`. -/
def pcall : List Byte := [0xe8, 0x2a, 0x59, 0x1b, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1792298] 5) := by dec_rfl
theorem wc_33 : pcall <+: usl.drop 33 := by decide +kernel
theorem call_33 (feat : Features) : Dec feat usl 33 (FV7z.mk .call 64 [.rel 1792298] 5) :=
  Dec.shift (j := 33) (k := 0) (pcall_0 feat) wc_33 (Nat.zero_le _)
theorem tgt_33 : usl_at.add (33 + 5) + BitVec.ofNat 64 1792298 = Onw.onw_at.add 64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_53 : pret <+: usl.drop 53 := by decide +kernel
theorem ret_53 (feat : Features) : Dec feat usl 53 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)

/-- `len` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers at the `call`: `rax` = `rbp` = `len`, `rbx` = `this`, `rdi` = `4 len + 4`, `rbp`, `rbx` pushed,
8 more. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      rax := zl g,
      rbx := g.rdi,
      rbp := zl g,
      rsp := g.rsp - 8 - 8 - 8,
      rdi := zl g * 4#64 + 4#64 }

/-- The bytes at the `call`: `rbp`, `rbx` pushed, `_chars` = 0. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE 0#64 8)

/-- The bytes after `_len` = `_limit` = `v` and `_chars` = `p` for the object at `b`. -/
abbrev V1 (V : Addr → Byte) (b : Addr) (v : BitVec 32) (p : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (b + 8#64) (toBytesLE v 4)) (b + 12#64) (toBytesLE v 4)) b (toBytesLE p 8)

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov eax, esi; push rbx; mov rbx, rdi; mov rbp, rax; sub rsp, 8; mov qword [rdi], 0;
lea rdi, [rax * 4 + 4]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 fw ⊢
  wpx [W_0, o0, gC, V0, zl]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from the callee: `mov [rbx + 8], ebp; mov [rbx + 12], ebp; mov [rbx], rax; add rsp, 8; pop rbx; pop rbp`
to the `ret` at 53. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw8 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 53
      { g with
          rbx := rdq(V1 V g.rbx (BitVec.setWidth 32 g.rbp) g.rax, g.rsp + 8#64),
          rbp := rdq(V1 V g.rbx (BitVec.setWidth 32 g.rbp) g.rax, g.rsp + 8#64 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 } fl
      (V1 V g.rbx (BitVec.setWidth 32 g.rbp) g.rax)) :
    W_38 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw8 hw12 hw0 hl1 hl2 h ⊢
  wpx [W_38, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::SetStartLen (len)` (`this` = `rdi`, `len` = `esi`) from its entry. At `operator new`'s entry the
registers are `gC` with `rsp` 32 below the entry's and the bytes `V0` with the return address into `SetStartLen`
pushed (`kf`); if the callee returns to `usl_at + 38` with `rsp`, `rbx`, `rbp` as at its entry, and the saved `rbx`,
`rbp` and the return address of `SetStartLen` as they were, the run reaches that return address with `_len` =
`_limit` = `len`, `_chars` = the callee's `rax` (`V1`), and `rbx`, `rbp`, `rsp` restored (`kr`). -/
theorem usl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L usl_at usl)
    (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = usl_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = usl_at.add 38 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl X.cpu.gpr → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
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
  have r16 : X.cpu.gpr.rsp - 24 + 8#64 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have r8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes outside the object as they were after the stores of `_len`, `_limit` and `_chars`
  have m1 : ∀ (W : Addr → Byte) (v : BitVec 32) (p : BitVec 64) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (V1 W X.cpu.gpr.rdi v p) = (byteAddrs x 8).map W := by
    intro W v p x hx h
    have a1 := Tun.rd_Vst (Vst (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 4)) (X.cpu.gpr.rdi + 12#64)
      (toBytesLE v 4)) X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    have a2 := Tun.rd_Vst (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 4)) (X.cpu.gpr.rdi + 12#64)
      (toBytesLE v 4) x 8 (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega)
    have a3 := Tun.rd_Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 4) x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)
    exact a1.trans (a2.trans a3)
  have hrip' : X.cpu.rip = usl_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 33 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) fw0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_33 _) hinW (tgt := 64) (Onw.lt_len (by decide))
    tgt_33 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC X.cpu.gpr).set 4 v) e32
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hb hp' hr' hPc
  have hb1 : rdq(V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp - 16) =
      X.cpu.gpr.rbx := by
    rw [m1 V' _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hb
  have hb2 : rdq(V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp - 8) =
      X.cpu.gpr.rbp := by
    rw [m1 V' _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact hp'
  have hr'' : rdq(V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp) =
      e₂.add j₂ := by
    rw [m1 V' _ _ X.cpu.gpr.rsp hp8 (by omega)]
    exact hr'
  have hv : BitVec.setWidth 32 Z.cpu.gpr.rbp = BitVec.setWidth 32 X.cpu.gpr.rsi := by
    rw [hzp]
    exact sw_64_32 _
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_38 prof).run c hin (fun j' g' _ V'' => j' = 53 ∧
      g' = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp } ∧
      V'' = V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax) hKZ hAZ hrZ
    (vc_38 (by rw [hzb]; exact fw8) (by rw [hzb]; exact fw12) (by rw [hzb]; exact fw0)
      (by rw [hzs, r16]; exact h16) (by rw [hzs, r16, r8]; exact h8)
      fun _ => ⟨rfl, by rw [hzb, hv, hzs, r16, r8, e8, hb1, hb2], by rw [hzb, hv]⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_53 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr'') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Usl
