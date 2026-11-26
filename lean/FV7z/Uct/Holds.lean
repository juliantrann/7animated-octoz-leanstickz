import FV7z.Uct.Cuts
import FV7z.Onw
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `UString::UString ()` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString ()` at `0x44d3e0` in `7zzs` (`CPP/Common/MyString.cpp`): `_chars` (the 8 bytes at
`this`) = NULL, `_chars = new wchar_t[4]` (`call` at 20 to `operator new`, `Onw.onw_at + 64`, with 16 bytes), then
`_len` = 0 and `_limit` = 3 (the 8 bytes at `this + 8`, `0x300000000`) and `_chars[0]` = 0 (4 bytes). `push rbx`,
`rbx` = `this` across the call, `pop rbx; ret` (49).

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`uct_at + 25`, `rsp` 8 below the entry's, `rbx` = `this`, the saved `rbx` and the return address left as they
were, 4 bytes at `rax` the run may store into apart from the frame, and the callee's own post `Pc`) to the return
address.

- `gC`, `V0`: the registers and the bytes at the `call`.
- `V1`: the bytes after the stores of `_chars`, `_len`, `_limit` and `_chars[0]`.
- `vc_0`, `vc_25`: the verification conditions of the two pieces.
- `uct_ok`: from the entry, through the callee, to the return address with `_chars` = the callee's `rax`, `_len` = 0,
  `_limit` = 3, `_chars[0]` = 0, `rdx` = `0x300000000` and `rbx`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uct

/-- The `call` to `operator new`. -/
def pcall : List Byte := [0xe8, 0xb7, 0x55, 0x1b, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1791415] 5) := by dec_rfl
theorem wc_20 : pcall <+: uct.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat uct 20 (FV7z.mk .call 64 [.rel 1791415] 5) :=
  Dec.shift (j := 20) (k := 0) (pcall_0 feat) wc_20 (Nat.zero_le _)
theorem tgt_20 : uct_at.add (20 + 5) + BitVec.ofNat 64 1791415 = Onw.onw_at.add 64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_49 : pret <+: uct.drop 49 := by decide +kernel
theorem ret_49 (feat : Features) : Dec feat uct 49 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)

/-- The registers at the `call`: `rbx` = `this`, `rdi` = 16, `rbx` pushed. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rsp := g.rsp - 8,
      rdi := BitVec.setWidth 64 (BitVec.ofNat 32 16) }

/-- The bytes at the `call`: `rbx` pushed, `_chars` = 0. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE 0#64 8)

/-- The bytes after `_chars` = `p`, `_len` = 0, `_limit` = 3 and `_chars[0]` = 0 for the object at `b`. -/
abbrev V1 (V : Addr → Byte) (b : Addr) (p : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V b (toBytesLE p 8)) (b + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#32 4)

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rbx, rdi; mov qword [rdi], 0; mov edi, 16`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fw : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 20 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 fw ⊢
  wpx [W_0, o0, gC, V0]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from the callee: `mov rdx, 0x300000000; mov [rbx], rax; mov [rbx + 8], rdx; mov dword [rax], 0; pop rbx`
to the `ret` at 49. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (hw8 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (hwa : ∀ i < 4, Foot Wl (Addr.add g.rax i)) (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 49
      { g with
          rdx := 12884901888#64,
          rbx := rdq(V1 V g.rbx g.rax, g.rsp),
          rsp := g.rsp + 8 } fl
      (V1 V g.rbx g.rax)) :
    W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw8 hwa hl h ⊢
  wpx [W_25, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString ()` (`this` = `rdi`) from its entry. At `operator new`'s entry the registers are `gC` with
`rsp` 16 below the entry's and the bytes `V0` with the return address into the constructor pushed (`kf`); if the
callee returns to `uct_at + 25` with `rsp`, `rbx` as at its entry, the saved `rbx` and the return address of the
constructor as they were, and 4 bytes at `rax` to store into apart from the frame, the run reaches that return address
with `_chars` = the callee's `rax`, `_len` = 0, `_limit` = 3 and `_chars[0]` = 0 (`V1`), and `rbx`, `rsp` restored
(`kr`). -/
theorem uct_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uct_at uct)
    (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uct_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = uct_at.add 25 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        (∀ i < 4, Foot Wl (Addr.add Z.cpu.gpr.rax i)) → Z.cpu.gpr.rax.toNat + 4 ≤ 2 ^ 64 →
        (Z.cpu.gpr.rax.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ Z.cpu.gpr.rax.toNat) →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rdx := 12884901888#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the frame's bytes as they were after the stores of `_chars`, `_len`, `_limit` and `_chars[0]`
  have m1 : ∀ (W : Addr → Byte) (p : BitVec 64) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 → p.toNat + 4 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (p.toNat + 4 ≤ x.toNat ∨ x.toNat + 8 ≤ p.toNat) →
      (byteAddrs x 8).map (V1 W X.cpu.gpr.rdi p) = (byteAddrs x 8).map W := by
    intro W p x hx hp4 h hpd
    have a1 := Tun.rd_Vst (Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 8#64)
      (toBytesLE 12884901888#64 8)) p (toBytesLE 0#32 4) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    have a2 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 8#64)
      (toBytesLE 12884901888#64 8) x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)
    have a3 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    exact a1.trans (a2.trans a3)
  have hrip' : X.cpu.rip = uct_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 fw0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_20 _) hinW (tgt := 64) (Onw.lt_len (by decide))
    tgt_20 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC X.cpu.gpr).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hwa hpa hda hPc
  have hb1 : rdq(V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [m1 V' Z.cpu.gpr.rax (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) hpa (by rw [tn8]; omega)
      (by rw [tn8]; omega)]
    exact hb
  have hr'' : rdq(V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m1 V' Z.cpu.gpr.rax X.cpu.gpr.rsp hp8 hpa (by omega) (by omega)]
    exact hr'
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_25 prof).run c hin (fun j' g' _ V'' => j' = 49 ∧
      g' = { Z.cpu.gpr with rdx := 12884901888#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
      V'' = V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax) hKZ hAZ hrZ
    (vc_25 (by rw [hzb]; exact fw0) (by rw [hzb]; exact fw8) hwa (by rw [hzs]; exact h8)
      fun _ => ⟨rfl, by rw [hzb, hzs, e8, hb1], by rw [hzb]⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_49 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr'') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Uct
