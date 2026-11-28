import FV7z.Aui.Cuts
import FV7z.Agr.Code
import FV7z.Agr.Blocks
import FV7z.U2s.Code
import FV7z.U2s.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `AString::Add_UInt32 (unsigned v)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Add_UInt32 (v)` at `0x44c980` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `v`
in `esi`: `Grow (10)` (`call` at 20 to `Agr.agr_at`), `end = ConvertUInt32ToString (v, _chars + _len)` (`call` at 33
to `U2s.u2s_at`; `_chars` the 8 bytes at `this`, `_len` the 4 at `this + 8`, both read after the first call), then
`_len = end - _chars` (`_chars` read again after the second call). `push rbp; push rbx; sub rsp, 8`, `rbp` = `v`,
`rbx` = `this` across the calls, `add rsp, 8; pop rbx; pop rbp; ret` (50).

The callees are hypotheses (`ku`, `kw`), as in `FV7z/Ucu/Holds.lean`: a continuation at each entry, given the run
from its return (`rsp` 24 below the entry's, the registers the caller keeps across it as it left them, the saved
registers and the return address as they were: `Sv`) and the callee's own post (`Pu`, `Pw`). `_len`'s 4 bytes are
writable and clear of the saved registers and the return address (`hw8`, `hd`).

- `zl`: `v` zero-extended.
- `V0`, `gC`: the bytes and the registers at the first `call`; `gW`: the registers at the `call` of
  `ConvertUInt32ToString`.
- `Vl`: the bytes after `_len = a - _chars`; `rd_Vl`: 8 bytes apart from `_len` read as before.
- `Sv`: the saved `rbx`, `rbp` and the return address in the bytes.
- `vc_0`, `vc_25`, `vc_38`: the verification conditions of the pieces.
- `aui_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aui

/-- The `call`s to `AString::Grow` and `ConvertUInt32ToString`. -/
def pcg : List Byte := [0xe8, 0x47, 0xf7, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709549383] 5) := by dec_rfl
theorem wc_20 : pcg <+: aui.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat aui 20 (FV7z.mk .call 64 [.rel 18446744073709549383] 5) :=
  Dec.shift (j := 20) (k := 0) (pcg_0 feat) wc_20 (Nat.zero_le _)
theorem tgt_20 : aui_at.add (20 + 5) + BitVec.ofNat 64 18446744073709549383 = Agr.agr_at.add 0 := by decide
def pcc : List Byte := [0xe8, 0xca, 0xe1, 0xff, 0xff]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 18446744073709543882] 5) := by dec_rfl
theorem wc_33 : pcc <+: aui.drop 33 := by decide +kernel
theorem call_33 (feat : Features) : Dec feat aui 33 (FV7z.mk .call 64 [.rel 18446744073709543882] 5) :=
  Dec.shift (j := 33) (k := 0) (pcc_0 feat) wc_33 (Nat.zero_le _)
theorem tgt_33 : aui_at.add (33 + 5) + BitVec.ofNat 64 18446744073709543882 = U2s.u2s_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_50 : pret <+: aui.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat aui 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)

/-- `v` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The bytes at the first `call`: `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `rbp` = `v`, `esi` = 10, `rbx` = `this`, 24 below the entry. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with rbp := zl g, rsi := BitVec.setWidth 64 10#32, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8 }

/-- The registers at the `call` of `ConvertUInt32ToString` for the bytes `V` (`z` the registers back from `Grow`,
`x` the entry's): `rsi` = `_chars + _len`, `edi` = `v`. -/
abbrev gW (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with
      rsi := (rdd(V, x.rdi + 8#64)).setWidth 64 + rdq(V, x.rdi),
      rdi := BitVec.setWidth 64 (BitVec.setWidth 32 z.rbp) }

/-- The bytes after `_len = a - _chars` for the object at `p`. -/
abbrev Vl (V : Addr → Byte) (p a : BitVec 64) : Addr → Byte :=
  Vst V (p + 8#64) (toBytesLE (BitVec.setWidth 32 (a - rdq(V, p))) 4)

/-- The saved `rbx`, `rbp` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 16) = x.rbx ∧ rdq(V, x.rsp - 8) = x.rbp ∧ rdq(V, x.rsp) = r

theorem rd_Vl (V : Addr → Byte) (p a : BitVec 64) (y : Addr) (hp : p.toNat + 12 ≤ 2 ^ 64)
    (hy : y.toNat + 8 ≤ 2 ^ 64) (h : p.toNat + 12 ≤ y.toNat ∨ y.toNat + 8 ≤ p.toNat + 8) :
    (byteAddrs y 8).map (Vl V p a) = (byteAddrs y 8).map V := by
  have t8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  exact Tun.rd_Vst V (p + 8#64) _ y 8 (by rw [toBytesLE_length, t8]; omega) hy (by rw [toBytesLE_length, t8]; omega)

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov ebp, esi; mov esi, 10; push rbx; mov rbx, rdi; sub rsp, 8` to the `call` at 20. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 20 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 ⊢
  wpx [W_0, o0, V0, gC, zl]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `Grow`: `mov esi, [rbx + 8]; mov edi, ebp; add rsi, [rbx]` to the `call` at 33. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h : ∀ fl, Q 33
      { g with
          rsi := (rdd(V, p + 8#64)).setWidth 64 + rdq(V, p),
          rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp) } fl V) :
    W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx f8 f0 h ⊢
  subst hbx
  wpx [W_25, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `ConvertUInt32ToString`: `sub rax, [rbx]; mov [rbx + 8], eax; add rsp, 8; pop rbx; pop rbp` to the
`ret` at 50. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (w8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 50
      { g with
          rax := g.rax - rdq(V, p),
          rbx := rdq(Vl V p g.rax, g.rsp + 8#64),
          rbp := rdq(Vl V p g.rax, g.rsp + 8#64 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 } fl
      (Vl V p g.rax)) :
    W_38 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx f0 w8 hl1 hl2 h ⊢
  subst hbx
  wpx [W_38, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Add_UInt32 (v)` (`this` = `rdi`, `v` = `esi`) from its entry. At `Grow`'s entry the registers are `gC`
with `esi` = 10, `rsp` 32 below the entry's, the bytes `V0` with the return address pushed (`ku`); back at
`aui_at + 25` (`Sv`, `Pu`), at `ConvertUInt32ToString`'s entry with the registers `gW` (`kw`); back at `aui_at + 38`
(`Pw`), at the return address with `_len = rax - _chars` (`Vl`), `rax` = that difference and `rbx`, `rbp`, `rsp`
restored (`kr`). -/
theorem aui_ok {Pu : State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aui_at aui) (hinG : CodeIn L Agr.agr_at Agr.agr)
    (hinC : CodeIn L U2s.u2s_at U2s.u2s)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aui_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (ft8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (ft0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (aui_at.add 25) 8)) →
      Y.cpu.rip = Agr.agr_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = aui_at.add 25 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl X.cpu.gpr → Sv V₁ X.cpu.gpr (e₂.add j₂) → Pu Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 32) (toBytesLE (aui_at.add 38) 8)) →
      Y.cpu.rip = U2s.u2s_at → Y.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = aui_at.add 38 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zw.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Sv V₂ X.cpu.gpr (e₂.add j₂) → Pw Z Zw V₂ → GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Z Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with
          rax := Zw.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8 } →
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
  have c32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8#64 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = aui_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `Grow`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_20 _) hinG (tgt := 0) (Agr.lt_len (by decide))
    tgt_20 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hsY, c32, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `Grow`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzb _ _ hPu
  refine (c_25 prof).run c hin (fun j' g' _ V' => j' = 33 ∧ g' = gW V₁ Z.cpu.gpr X.cpu.gpr ∧ V' = V₁) hKZ hAZ hrZ
    (vc_25 hzb ft8 ft0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact hzs
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3', c32]; exact hs4
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_33 _) hinC (tgt := 0) (U2s.lt_len (by decide))
    tgt_33 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', c32] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₄, hs3', c32, hg₃]
  refine kw Z V₁ hPu Y₄ t₅ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from `ConvertUInt32ToString`
  intro Zw V₂ t₆ hKw hAw hrw hws hwb hsv2 hPw
  have hb1 : rdq(Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [rd_Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax (X.cpu.gpr.rsp - 16) hq (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hsv2.1
  have hb2 : rdq(Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
    rw [rd_Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax (X.cpu.gpr.rsp - 8) hq (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact hsv2.2.1
  have hb3 : rdq(Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [rd_Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax X.cpu.gpr.rsp hq hp8 (by omega)]
    exact hsv2.2.2
  refine (c_38 prof).run c hin (fun j' g' _ V' => j' = 50 ∧
      g' = { Zw.cpu.gpr with
          rax := Zw.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp } ∧
      V' = Vl V₂ X.cpu.gpr.rdi Zw.cpu.gpr.rax) hKw hAw hrw
    (vc_38 hwb ft0 hw8 (by rw [hws, a16]; exact h16) (by rw [hws, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hws, a16, a8, e8, hb1, hb2], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
  subst V₃
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_50 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hb3) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z Zw V₂ Z' t₈ hPw hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Aui
