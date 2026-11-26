import FV7z.Ucu.Cuts
import FV7z.Usl.Code
import FV7z.Usl.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.CmovLd
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `UString::UString (unsigned num, const UString &s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (num, s)` at `0x44d240` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`num` in `esi`, `&s` in `rdx`: `num` capped at `s._len` (the 4 bytes at `&s + 8`; `cmp [rdx + 8], esi; cmovbe`),
`SetStartLen (num)` (`call` at 27 to `Usl.usl_at`), `wmemcpy (_chars, s._chars, num)` (`call` at 43 to
`Wmc.wmc_at`; `_chars` the 8 bytes at `this`, `s._chars` those at `&s`), then `_chars[num] = 0`. `push r12; push rbp;
push rbx`, `r12` = `&s`, `rbp` = `this`, `rbx` = `num` across the calls, `pop rbx; pop rbp; pop r12; ret` (63).

The callees are hypotheses (`ku`, `kw`), as in `FV7z/Ura/Holds.lean`: a continuation at each entry, given the run
from its return (`rsp` 24 below the entry's, `rbx`, `rbp` and `r12` as the caller left them, the saved registers and
the return address as they were: `Sv`) and the callee's own post (`Pu`, `Pw`). `pw`: the 4 bytes of `_chars[num]`
writable, clear of the saved registers and the return address.

- `mn`: what `cmovbe` leaves, the smaller of `s._len` and `num` (`mn_toNat`).
- `V0`, `gC`: the bytes and the registers at the first `call`; `gW`: the registers at the `call` of `wmemcpy`.
- `Sv`: the saved `rbx`, `rbp`, `r12` and the return address in the bytes.
- `vc_0`, `vc_32`, `vc_48`: the verification conditions of the pieces.
- `ucu_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ucu

/-- The `call`s to `SetStartLen` and `wmemcpy`. -/
def pcu : List Byte := [0xe8, 0x00, 0xfe, 0xff, 0xff]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 18446744073709551104] 5) := by dec_rfl
theorem wc_27 : pcu <+: ucu.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat ucu 27 (FV7z.mk .call 64 [.rel 18446744073709551104] 5) :=
  Dec.shift (j := 27) (k := 0) (pcu_0 feat) wc_27 (Nat.zero_le _)
theorem tgt_27 : ucu_at.add (27 + 5) + BitVec.ofNat 64 18446744073709551104 = Usl.usl_at.add 0 := by decide
def pcw : List Byte := [0xe8, 0x90, 0x00, 0x21, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2162832] 5) := by dec_rfl
theorem wc_43 : pcw <+: ucu.drop 43 := by decide +kernel
theorem call_43 (feat : Features) : Dec feat ucu 43 (FV7z.mk .call 64 [.rel 2162832] 5) :=
  Dec.shift (j := 43) (k := 0) (pcw_0 feat) wc_43 (Nat.zero_le _)
theorem tgt_43 : ucu_at.add (43 + 5) + BitVec.ofNat 64 2162832 = Wmc.wmc_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_63 : pret <+: ucu.drop 63 := by decide +kernel
theorem ret_63 (feat : Features) : Dec feat ucu 63 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 63) (k := 0) (pret_0 feat) w_63 (Nat.zero_le _)

/-- What `cmp [rdx + 8], esi; cmovbe ebx, [rdx + 8]` leaves in `ebx` (`l` = `s._len`, `n` = `num`). -/
def mn (l n : BitVec 32) : BitVec 32 := if (decide (l.toNat < n.toNat) || decide (l = n)) = true then l else n

theorem mn_toNat (l n : BitVec 32) : (mn l n).toNat = min l.toNat n.toNat := by
  unfold mn
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · omega
    · rw [h]; omega
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
    have : l.toNat ≠ n.toNat := fun e => h.2 (BitVec.eq_of_toNat_eq e)
    omega

/-- The bytes at the first `call`: `r12`, `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers at the first `call` for the count `m`: `r12` = `&s`, `rbp` = `this`, `rbx` = `esi` = `m`, 24
below the entry. -/
abbrev gC (g : Gprs) (m : BitVec 32) : Gprs :=
  { g with r12 := g.rdx, rbp := g.rdi, rbx := m.setWidth 64, rsi := m.setWidth 64, rsp := g.rsp - 8 - 8 - 8 }

/-- The registers at the `call` of `wmemcpy` for the bytes `V` (`z` the registers back from `SetStartLen`, `x` the
entry's): `rdi` = `_chars`, `rsi` = `s._chars`, `rdx` = the count. -/
abbrev gW (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with rsi := rdq(V, x.rdx), rdi := rdq(V, x.rdi), rdx := z.rbx }

/-- The saved `rbx`, `rbp`, `r12` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 24) = x.rbx ∧ rdq(V, x.rsp - 16) = x.rbp ∧ rdq(V, x.rsp - 8) = x.r12 ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdx; push rbp; mov rbp, rdi; push rbx; mov ebx, esi; cmp [rdx + 8], esi; cmovbe ebx,
[rdx + 8]; mov esi, ebx; mov ebx, ebx` to the `call` at 27. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (fr : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 27 ∧
      g' = gC g (mn (rdd(V0 V g, g.rdx + 8#64)) (BitVec.setWidth 32 g.rsi)) ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 fr ⊢
  wpx [W_0, o0, V0, gC, mn, Op.cmpmr, Op.cmovld32]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov rsi, [r12]; mov rdi, [rbp]; mov rdx, rbx` to the `call` at 43. -/
theorem vc_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : Addr} (hr12 : g.r12 = p)
    (hbp : g.rbp = q) (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (fq : ∀ i < 8, Foot F.data (Addr.add q i))
    (h : ∀ fl, Q 43 { g with rsi := rdq(V, p), rdi := rdq(V, q), rdx := g.rbx } fl V) :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr12 hbp f0 fq h ⊢
  subst hr12 hbp
  wpx [W_32, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The bytes after `_chars[m] = 0` for `_chars` = `a` and `rbx` = `b`. -/
abbrev Vz (V : Addr → Byte) (a b : BitVec 64) : Addr → Byte := Vst V (a + b * 4#64) (toBytesLE 0#32 4)

/-- Back from `wmemcpy`: `mov rax, [rbp]; mov dword [rax + rbx * 4], 0; pop rbx; pop rbp; pop r12` to the `ret` at
63. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {q : Addr} (hbp : g.rbp = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add q i)) (w : ∀ i < 4, Foot Wl (Addr.add (rdq(V, q) + g.rbx * 4#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 63
      { g with
          rax := rdq(V, q),
          rbx := rdq(Vz V (rdq(V, q)) g.rbx, g.rsp),
          rbp := rdq(Vz V (rdq(V, q)) g.rbx, g.rsp + 8),
          r12 := rdq(Vz V (rdq(V, q)) g.rbx, g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl
      (Vz V (rdq(V, q)) g.rbx)) :
    W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp fq w hl0 hl1 hl2 h ⊢
  subst hbp
  wpx [W_48, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (num, s)` (`this` = `rdi`, `num` = `esi`, `&s` = `rdx`) from its entry, `m` = `mn s._len num`.
At `SetStartLen`'s entry the registers are `gC` with `esi` = `m`, `rsp` 32 below the entry's, the bytes `V0` with the
return address pushed (`ku`); back at `ucu_at + 32` (`Sv`, `Pu`), at `wmemcpy`'s entry with the registers `gW` (`kw`);
back at `ucu_at + 48` (`Pw`), at the return address with `_chars[m] = 0` (`Vz`) and `rax` = `_chars` (`kr`). -/
theorem ucu_ok {Pu : State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ucu_at ucu) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucu_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fr8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdx.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdx.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdx.toNat + 8)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucu_at.add 32) 8)) →
      Y.cpu.rip = Usl.usl_at →
      Y.cpu.gpr = (gC X.cpu.gpr (mn (rdd(V, X.cpu.gpr.rdx + 8#64)) (BitVec.setWidth 32 X.cpu.gpr.rsi))).set 4
        (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = ucu_at.add 32 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 →
        Z.cpu.gpr.rbx = (mn (rdd(V, X.cpu.gpr.rdx + 8#64)) (BitVec.setWidth 32 X.cpu.gpr.rsi)).setWidth 64 →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.r12 = X.cpu.gpr.rdx → Sv V₁ X.cpu.gpr (e₂.add j₂) → Pu Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 32) (toBytesLE (ucu_at.add 48) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = ucu_at.add 48 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 →
        Zw.cpu.gpr.rbx = (mn (rdd(V, X.cpu.gpr.rdx + 8#64)) (BitVec.setWidth 32 X.cpu.gpr.rsi)).setWidth 64 →
        Zw.cpu.gpr.rbp = X.cpu.gpr.rdi → Sv V₂ X.cpu.gpr (e₂.add j₂) → Pw Z Zw V₂ →
        GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (pw : ∀ (Z Zw : State) (V₂ : Addr → Byte), Pw Z Zw V₂ →
      (∀ i < 4, Foot Wl (Addr.add (rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64) i)) ∧
      (rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64).toNat + 4 ≤ 2 ^ 64 ∧
      ((rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨
        X.cpu.gpr.rsp.toNat + 8 ≤ (rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64).toNat))
    (kr : ∀ (Z Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Z Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with
          rax := rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
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
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rdx + 8#64).toNat = X.cpu.gpr.rdx.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- `s._len` as it was before the pushes
  have x8 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdx + 8#64) = rdd(V, X.cpu.gpr.rdx + 8#64) := by
    have a1 := Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rdx + 8#64) 4
      (by rw [toBytesLE_length, e24, tn24]; omega) (by rw [t8]; omega)
      (by rw [toBytesLE_length, e24, tn24, t8]; omega)
    have a2 := Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rdx + 8#64) 4 (by rw [toBytesLE_length, e16, tn16]; omega)
      (by rw [t8]; omega) (by rw [toBytesLE_length, e16, tn16, t8]; omega)
    have a3 := Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) (X.cpu.gpr.rdx + 8#64) 4
      (by rw [toBytesLE_length, tn8]; omega) (by rw [t8]; omega) (by rw [toBytesLE_length, tn8, t8]; omega)
    exact congrArg (ofBytesLE 32) (a1.trans (a2.trans a3))
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = ucu_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `SetStartLen`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 27 ∧
      g' = gC X.cpu.gpr (mn (rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdx + 8#64)) (BitVec.setWidth 32 X.cpu.gpr.rsi)) ∧
      V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) fr8) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rw [x8] at hgY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_27 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_27 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr (mn (rdd(V, X.cpu.gpr.rdx + 8#64)) (BitVec.setWidth 32 X.cpu.gpr.rsi))).set
      4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hsY, c32, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `SetStartLen`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzb hzp hz12 hsv1 hPu
  refine (c_32 prof).run c hin (fun j' g' _ V' => j' = 43 ∧ g' = gW V₁ Z.cpu.gpr X.cpu.gpr ∧ V' = V₁) hKZ hAZ hrZ
    (vc_32 hz12 hzp fr0 fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact hzs
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3', c32]; exact hs4
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_43 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
    tgt_43 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', c32] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gW V₁ Z.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₄, hs3', c32, hg₃]
  refine kw Z V₁ hPu Y₄ t₅ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from `wmemcpy`
  intro Zw V₂ t₆ hKw hAw hrw hws hwb hwp hsv2 hPw
  obtain ⟨fa, ha4, hda⟩ := pw Z Zw V₂ hPw
  have mz : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 →
      ((rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64).toNat + 4 ≤ y.toNat ∨
        y.toNat + 8 ≤ (rdq(V₂, X.cpu.gpr.rdi) + Zw.cpu.gpr.rbx * 4#64).toNat) →
      (byteAddrs y 8).map (Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx) = (byteAddrs y 8).map V₂ :=
    fun y hy h => Tun.rd_Vst V₂ _ (toBytesLE 0#32 4) y 8 (by rw [toBytesLE_length]; omega) hy
      (by rw [toBytesLE_length]; omega)
  have hb1 : rdq(Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx, X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx := by
    rw [mz _ (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact hsv2.1
  have hb2 : rdq(Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp := by
    rw [mz _ (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact hsv2.2.1
  have hb3 : rdq(Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
    rw [mz _ (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hsv2.2.2.1
  have hb4 : rdq(Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [mz _ hp8 (by omega)]; exact hsv2.2.2.2
  refine (c_48 prof).run c hin (fun j' g' _ V' => j' = 63 ∧
      g' = { Zw.cpu.gpr with
          rax := rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          rsp := X.cpu.gpr.rsp } ∧
      V' = Vz V₂ (rdq(V₂, X.cpu.gpr.rdi)) Zw.cpu.gpr.rbx) hKw hAw hrw
    (vc_48 hwp fd0 fa (by rw [hws]; exact h24) (by rw [hws, a16]; exact h16) (by rw [hws, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hws, a16, a8, e8, hb1, hb2, hb3], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
  subst V₃
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_63 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hb4) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z Zw V₂ Z' t₈ hPw hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Ucu
