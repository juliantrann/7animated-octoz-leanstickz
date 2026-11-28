import FV7z.Uch.Cuts
import FV7z.Usl.Code
import FV7z.Usl.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `UString::UString (const UString &s, wchar_t c)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (s, c)` at `0x44d280` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `&s`
in `rsi`, `c` in `edx`: `SetStartLen (s._len + 1)` (`call` at 29 to `Usl.usl_at`; `_len` the 4 bytes at `&s + 8`),
`wmemcpy (_chars, s._chars, s._len)` (`call` at 51 to `Wmc.wmc_at`; `_chars` the 8 bytes at `this`, `s._chars`
those at `&s`, `s._len` read again after the first call), then `_chars[s._len] = c`, `_chars[s._len + 1] = 0`.
`push r13; push r12; push rbp; push rbx; sub rsp, 8`, `r13` = `c`, `rbp` = `this`, `rbx` = `&s` across the first
call, `rbp` = `_chars`, `r12` = `s._len` across the second, `add rsp, 8; pop rbx; pop rbp; pop r12; pop r13; ret`
(80).

The callees are hypotheses (`ku`, `kw`), as in `FV7z/Ucu/Holds.lean`: a continuation at each entry, given the run
from its return (`rsp` 40 below the entry's, the registers the caller keeps across it as it left them, the saved
registers and the return address as they were: `Sv`) and the callee's own post (`Pu`, `Pw`). `pw`: the 8 bytes of
`_chars[s._len]`, `_chars[s._len + 1]` writable, clear of the saved registers and the return address.

- `zl`: `c` zero-extended; `ln`: `s._len` zero-extended in the bytes `V`; `aw`: the address of `_chars[s._len]`.
- `V0`, `gC`: the bytes and the registers at the first `call`; `gW`: the registers at the `call` of `wmemcpy`.
- `Vz`: the bytes after the two stores; `rd_Vz`: 8 bytes apart from them read as before.
- `Sv`: the saved `rbx`, `rbp`, `r12`, `r13` and the return address in the bytes.
- `vc_0`, `vc_34`, `vc_56`: the verification conditions of the pieces.
- `uch_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uch

/-- The `call`s to `SetStartLen` and `wmemcpy`. -/
def pcu : List Byte := [0xe8, 0xbe, 0xfd, 0xff, 0xff]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 18446744073709551038] 5) := by dec_rfl
theorem wc_29 : pcu <+: uch.drop 29 := by decide +kernel
theorem call_29 (feat : Features) : Dec feat uch 29 (FV7z.mk .call 64 [.rel 18446744073709551038] 5) :=
  Dec.shift (j := 29) (k := 0) (pcu_0 feat) wc_29 (Nat.zero_le _)
theorem tgt_29 : uch_at.add (29 + 5) + BitVec.ofNat 64 18446744073709551038 = Usl.usl_at.add 0 := by decide
def pcw : List Byte := [0xe8, 0x48, 0x00, 0x21, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2162760] 5) := by dec_rfl
theorem wc_51 : pcw <+: uch.drop 51 := by decide +kernel
theorem call_51 (feat : Features) : Dec feat uch 51 (FV7z.mk .call 64 [.rel 2162760] 5) :=
  Dec.shift (j := 51) (k := 0) (pcw_0 feat) wc_51 (Nat.zero_le _)
theorem tgt_51 : uch_at.add (51 + 5) + BitVec.ofNat 64 2162760 = Wmc.wmc_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_80 : pret <+: uch.drop 80 := by decide +kernel
theorem ret_80 (feat : Features) : Dec feat uch 80 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 80) (k := 0) (pret_0 feat) w_80 (Nat.zero_le _)

/-- `c` (`edx`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)

/-- `s._len` (the 4 bytes at `&s + 8`, `&s` = `x.rsi`) zero-extended in the bytes `V`. -/
abbrev ln (V : Addr → Byte) (x : Gprs) : BitVec 64 := (rdd(V, x.rsi + 8#64)).setWidth 64

/-- The address of `_chars[s._len]` in the bytes `V` (`this` = `x.rdi`). -/
abbrev aw (V : Addr → Byte) (x : Gprs) : Addr := rdq(V, x.rdi) + ln V x * 4#64

/-- The bytes at the first `call`: `r13`, `r12`, `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call` for `s._len` = `n`: `r13` = `c`, `rbp` = `this`, `rbx` = `&s`, `eax` = `n`,
`esi` = `n + 1`, 40 below the entry. -/
abbrev gC (g : Gprs) (n : BitVec 32) : Gprs :=
  { g with
      rax := n.setWidth 64,
      rbx := g.rsi,
      rbp := g.rdi,
      r13 := zl g,
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 (n.setWidth 64 + 1#64)),
      rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The registers at the `call` of `wmemcpy` for the bytes `V` (`z` the registers back from `SetStartLen`, `x` the
entry's): `rdi` = `rbp` = `_chars`, `rsi` = `s._chars`, `rdx` = `r12` = `s._len`. -/
abbrev gW (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with r12 := ln V x, rbp := rdq(V, x.rdi), rsi := rdq(V, x.rsi), rdx := ln V x, rdi := rdq(V, x.rdi) }

/-- The bytes after `a[b] = c` and `a[b + 1] = 0` (4-byte characters). -/
abbrev Vz (V : Addr → Byte) (a b : BitVec 64) (c : BitVec 32) : Addr → Byte :=
  Vst (Vst V (a + b * 4#64) (toBytesLE c 4)) (a + b * 4#64 + 4#64) (toBytesLE 0#32 4)

/-- The saved `rbx`, `rbp`, `r12`, `r13` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 32) = x.rbx ∧ rdq(V, x.rsp - 24) = x.rbp ∧ rdq(V, x.rsp - 16) = x.r12 ∧
    rdq(V, x.rsp - 8) = x.r13 ∧ rdq(V, x.rsp) = r

theorem tn_add4 (a : Addr) (h : a.toNat + 8 ≤ 2 ^ 64) : (a + 4#64).toNat = a.toNat + 4 := by
  rw [BitVec.toNat_add]; simp; omega

theorem rd_Vz (V : Addr → Byte) (a b : BitVec 64) (c : BitVec 32) (y : Addr)
    (ha : (a + b * 4#64).toNat + 8 ≤ 2 ^ 64) (hy : y.toNat + 8 ≤ 2 ^ 64)
    (h : (a + b * 4#64).toNat + 8 ≤ y.toNat ∨ y.toNat + 8 ≤ (a + b * 4#64).toNat) :
    (byteAddrs y 8).map (Vz V a b c) = (byteAddrs y 8).map V := by
  have t4 := tn_add4 _ ha
  exact (Tun.rd_Vst (Vst V (a + b * 4#64) (toBytesLE c 4)) (a + b * 4#64 + 4#64) (toBytesLE 0#32 4) y 8
    (by rw [toBytesLE_length, t4]; omega) hy (by rw [toBytesLE_length, t4]; omega)).trans
    (Tun.rd_Vst V (a + b * 4#64) (toBytesLE c 4) y 8 (by rw [toBytesLE_length]; omega) hy
      (by rw [toBytesLE_length]; omega))

variable {F : Footprint} {Wl : List Rgn}

/-- `push r13; mov r13d, edx; push r12; push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 8;
mov eax, [rsi + 8]; lea esi, [rax + 1]` to the `call` at 29. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (fr : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 29 ∧ g' = gC g (rdd(V0 V g, g.rsi + 8#64)) ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 fr ⊢
  wpx [W_0, o0, V0, gC, zl]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov r12d, [rbx + 8]; mov rbp, [rbp]; mov rsi, [rbx]; mov rdx, r12; mov rdi, rbp` to
the `call` at 51. -/
theorem vc_34 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : Addr} (hbx : g.rbx = p)
    (hbp : g.rbp = q) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (fq : ∀ i < 8, Foot F.data (Addr.add q i))
    (h : ∀ fl, Q 51
      { g with
          r12 := (rdd(V, p + 8#64)).setWidth 64,
          rbp := rdq(V, q),
          rsi := rdq(V, p),
          rdx := (rdd(V, p + 8#64)).setWidth 64,
          rdi := rdq(V, q) } fl V) :
    W_34 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx hbp f8 f0 fq h ⊢
  subst hbx hbp
  wpx [W_34, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `wmemcpy`: `mov [rbp + r12 * 4], r13d; mov dword [rbp + r12 * 4 + 4], 0; add rsp, 8; pop rbx;
pop rbp; pop r12; pop r13` to the `ret` at 80. -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w1 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + g.r12 * 4#64) i))
    (w2 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + g.r12 * 4#64 + 4#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 80
      { g with
          rbx := rdq(Vz V g.rbp g.r12 (BitVec.setWidth 32 g.r13), g.rsp + 8#64),
          rbp := rdq(Vz V g.rbp g.r12 (BitVec.setWidth 32 g.r13), g.rsp + 8#64 + 8),
          r12 := rdq(Vz V g.rbp g.r12 (BitVec.setWidth 32 g.r13), g.rsp + 8#64 + 8 + 8),
          r13 := rdq(Vz V g.rbp g.r12 (BitVec.setWidth 32 g.r13), g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl
      (Vz V g.rbp g.r12 (BitVec.setWidth 32 g.r13))) :
    W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w1 w2 hl1 hl2 hl3 hl4 h ⊢
  wpx [W_56, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (s, c)` (`this` = `rdi`, `&s` = `rsi`, `c` = `edx`) from its entry. At `SetStartLen`'s entry
the registers are `gC` with `esi` = `s._len + 1`, `rsp` 48 below the entry's, the bytes `V0` with the return address
pushed (`ku`); back at `uch_at + 34` (`Sv`, `Pu`), at `wmemcpy`'s entry with the registers `gW` (`kw`); back at
`uch_at + 56` (`Pw`), at the return address with `_chars[s._len] = c`, `_chars[s._len + 1] = 0` (`Vz`) and `rbx`,
`rbp`, `r12`, `r13`, `rsp` restored (`kr`). -/
theorem uch_ok {Pu : State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uch_at uch) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uch_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fr8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rsi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat + 8)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uch_at.add 34) 8)) →
      Y.cpu.rip = Usl.usl_at →
      Y.cpu.gpr = (gC X.cpu.gpr (rdd(V, X.cpu.gpr.rsi + 8#64))).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = uch_at.add 34 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.r13 = zl X.cpu.gpr → Sv V₁ X.cpu.gpr (e₂.add j₂) → Pu Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (uch_at.add 56) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = uch_at.add 56 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 →
        Zw.cpu.gpr.rbp = rdq(V₁, X.cpu.gpr.rdi) → Zw.cpu.gpr.r12 = ln V₁ X.cpu.gpr →
        Zw.cpu.gpr.r13 = zl X.cpu.gpr → Sv V₂ X.cpu.gpr (e₂.add j₂) → Pw Z Zw V₂ →
        GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (pw : ∀ (Z : State) (V₁ : Addr → Byte) (Zw : State) (V₂ : Addr → Byte), Pu Z V₁ → Pw Z Zw V₂ →
      (∀ i < 4, Foot Wl (Addr.add (rdq(V₁, X.cpu.gpr.rdi) + ln V₁ X.cpu.gpr * 4#64) i)) ∧
      (∀ i < 4, Foot Wl (Addr.add (rdq(V₁, X.cpu.gpr.rdi) + ln V₁ X.cpu.gpr * 4#64 + 4#64) i)) ∧
      (rdq(V₁, X.cpu.gpr.rdi) + ln V₁ X.cpu.gpr * 4#64).toNat + 8 ≤ 2 ^ 64 ∧
      ((rdq(V₁, X.cpu.gpr.rdi) + ln V₁ X.cpu.gpr * 4#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32 ∨
        X.cpu.gpr.rsp.toNat + 8 ≤ (rdq(V₁, X.cpu.gpr.rdi) + ln V₁ X.cpu.gpr * 4#64).toNat))
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat),
      Pu Z V₁ → Pw Z Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr))) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
          rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
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
  have a32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
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
  have t8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- `s._len` as it was before the pushes
  have x8 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) = rdd(V, X.cpu.gpr.rsi + 8#64) := by
    have a1 := Tun.rd_Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8))
      (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsi + 8#64) 4
      (by rw [toBytesLE_length, e32, tn32]; omega) (by rw [t8]; omega)
      (by rw [toBytesLE_length, e32, tn32, t8]; omega)
    have a2 := Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rsi + 8#64) 4
      (by rw [toBytesLE_length, e24, tn24]; omega) (by rw [t8]; omega)
      (by rw [toBytesLE_length, e24, tn24, t8]; omega)
    have a3 := Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8) (X.cpu.gpr.rsi + 8#64) 4 (by rw [toBytesLE_length, e16, tn16]; omega)
      (by rw [t8]; omega) (by rw [toBytesLE_length, e16, tn16, t8]; omega)
    have a4 := Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8) (X.cpu.gpr.rsi + 8#64) 4
      (by rw [toBytesLE_length, tn8]; omega) (by rw [t8]; omega) (by rw [toBytesLE_length, tn8, t8]; omega)
    exact congrArg (ofBytesLE 32) (a1.trans (a2.trans (a3.trans a4)))
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = uch_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `SetStartLen`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 29 ∧
      g' = gC X.cpu.gpr (rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64)) ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) fr8) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rw [x8] at hgY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_29 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_29 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c48] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr (rdd(V, X.cpu.gpr.rsi + 8#64))).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₂, hsY, c48, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `SetStartLen`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzb hzp hz13 hsv1 hPu
  refine (c_34 prof).run c hin (fun j' g' _ V' => j' = 51 ∧ g' = gW V₁ Z.cpu.gpr X.cpu.gpr ∧ V' = V₁) hKZ hAZ hrZ
    (vc_34 hzb hzp fr8 fr0 fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₃]; exact hzs
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3', c48]; exact hs6
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_51 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
    tgt_51 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', c48] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₄, hs3', c48, hg₃]
  refine kw Z V₁ hPu Y₄ t₅ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from `wmemcpy`
  intro Zw V₂ t₆ hKw hAw hrw hws hwp hw12 hw13 hsv2 hPw
  obtain ⟨fa, fa4, ha8, hda⟩ := pw Z V₁ Zw V₂ hPu hPw
  have hb1 : rdq(Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr)),
      X.cpu.gpr.rsp - 32) = X.cpu.gpr.rbx := by
    rw [rd_Vz V₂ _ _ _ (X.cpu.gpr.rsp - 32) ha8 (by rw [tn32]; omega) (by rw [tn32]; omega)]
    exact hsv2.1
  have hb2 : rdq(Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr)),
      X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbp := by
    rw [rd_Vz V₂ _ _ _ (X.cpu.gpr.rsp - 24) ha8 (by rw [tn24]; omega) (by rw [tn24]; omega)]
    exact hsv2.2.1
  have hb3 : rdq(Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr)),
      X.cpu.gpr.rsp - 16) = X.cpu.gpr.r12 := by
    rw [rd_Vz V₂ _ _ _ (X.cpu.gpr.rsp - 16) ha8 (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hsv2.2.2.1
  have hb4 : rdq(Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr)),
      X.cpu.gpr.rsp - 8) = X.cpu.gpr.r13 := by
    rw [rd_Vz V₂ _ _ _ (X.cpu.gpr.rsp - 8) ha8 (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact hsv2.2.2.2.1
  have hb5 : rdq(Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr)),
      X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [rd_Vz V₂ _ _ _ X.cpu.gpr.rsp ha8 hp8 (by omega)]
    exact hsv2.2.2.2.2
  refine (c_56 prof).run c hin (fun j' g' _ V' => j' = 80 ∧
      g' = { Zw.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
          rsp := X.cpu.gpr.rsp } ∧
      V' = Vz V₂ (rdq(V₁, X.cpu.gpr.rdi)) (ln V₁ X.cpu.gpr) (BitVec.setWidth 32 (zl X.cpu.gpr))) hKw hAw hrw
    (vc_56 (by rw [hwp, hw12]; exact fa) (by rw [hwp, hw12]; exact fa4) (by rw [hws, a32]; exact h32)
      (by rw [hws, a32, a24]; exact h24) (by rw [hws, a32, a24, a16]; exact h16)
      (by rw [hws, a32, a24, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hws, hwp, hw12, hw13, a32, a24, a16, a8, e8, hb1, hb2, hb3, hb4],
        by rw [hwp, hw12, hw13]⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
  subst V₃
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_80 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hb5) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V₁ Zw V₂ Z' t₈ hPu hPw hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Uch
