import FV7z.Udl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SubMr
import FV7z.Tun.Inv
/-!
# `UString::Delete` (PLAN.md §M, M1)

7-Zip 26.06's `UString::Delete (index, count)` at `0x44e0b0` in `7zzs` (`CPP/Common/MyString.cpp`): `push rbp; push
rbx; sub rsp, 8`, `count` (`ebx`) cut to `_len - index` (the 4 bytes at `this + 8`) when `index + count > _len`
(`cmova`); if it is 0, `add rsp, 8; pop rbx; pop rbp; ret` (37); else `memmove (_chars + index, _chars + index +
count, 4 (_len - index - count + 1))` (`call` at 79 to the PLT's entry `0x401020`, `rbp` = `this`, `rbx` = `count`
across it), `_len -= count` (`sub [rbp + 8], ebx` at 84), `add rsp, 8; pop rbx; pop rbp; ret` (93).

The callee is a hypothesis, as in `FV7z/Vcl/Holds.lean`: a continuation at its entry (`kf`), given the run from its
return. `Pc` is what it leaves.

- `ln`, `A`, `cnt`, `ix`: `_len`; `index + count` (32 bits); `count` after the cut; `index + count` after it.
- `V0`, `gZ`, `gM`: the bytes with `rbp`, `rbx` pushed; the registers at the first `ret` and at the `call`.
- `vc_z`, `vc_nz`: the verification conditions of the piece from the entry, one for each way; `vc_87`: of the one
  after the `sub`.
- `udl_ok`: with `count` 0, at the return address with no byte changed but the frame's (`kn`); else through the
  callee, the `sub` and the return, with `_len` less `count` and `rbx`, `rbp`, `rsp` restored (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Udl

/-- The PLT's entry for `memmove`. -/
abbrev plt_memmove : Addr := 0x401020

/-- The `call` to `memmove`. -/
def pcall : List Byte := [0xe8, 0x1c, 0x2f, 0xfb, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709235996] 5) := by dec_rfl
theorem wc_79 : pcall <+: udl.drop 79 := by decide +kernel
theorem call_79 (feat : Features) : Dec feat udl 79 (FV7z.mk .call 64 [.rel 18446744073709235996] 5) :=
  Dec.shift (j := 79) (k := 0) (pcall_0 feat) wc_79 (Nat.zero_le _)
theorem tgt_79 : udl_at.add (79 + 5) + BitVec.ofNat 64 18446744073709235996 = plt_memmove := by decide

/-- The `sub [rbp + 8], ebx`. -/
def psub : List Byte := [0x29, 0x5d, 0x08]
theorem psub_0 : ∀ feat, Dec feat psub 0 (FV7z.mk .sub 32 [.mem (mbd 5 8 32), gr 32 3] 3) := by dec_rfl
theorem ws_84 : psub <+: udl.drop 84 := by decide +kernel
theorem sub_84 (feat : Features) : Dec feat udl 84 (FV7z.mk .sub 32 [.mem (mbd 5 8 32), gr 32 3] 3) :=
  Dec.shift (j := 84) (k := 0) (psub_0 feat) ws_84 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_37 : pret <+: udl.drop 37 := by decide +kernel
theorem ret_37 (feat : Features) : Dec feat udl 37 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 37) (k := 0) (pret_0 feat) w_37 (Nat.zero_le _)
theorem w_93 : pret <+: udl.drop 93 := by decide +kernel
theorem ret_93 (feat : Features) : Dec feat udl 93 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 93) (k := 0) (pret_0 feat) w_93 (Nat.zero_le _)

/-- `_len`. -/
abbrev ln (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rdi + 8#64)

/-- `index + count`, 32 bits. -/
abbrev A (g : Gprs) : BitVec 32 := BitVec.setWidth 32 (g.rsi + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx))

/-- `count`, cut to `_len - index` when `index + count > _len` (`cmova`). -/
abbrev cnt (V : Addr → Byte) (g : Gprs) : BitVec 32 :=
  if (!(decide ((A g).toNat < (ln V g).toNat) || decide (A g = ln V g))) = true then
    ln V g - BitVec.setWidth 32 g.rsi
  else BitVec.setWidth 32 g.rdx

/-- `index + count` with `count` cut. -/
abbrev ix (V : Addr → Byte) (g : Gprs) : BitVec 32 :=
  BitVec.setWidth 32 (BitVec.setWidth 64 (cnt V g) + g.rsi)

/-- The bytes with `rbp` and `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call`: `rdi` = `_chars + index`, `rsi` = `r8` = `_chars + index + count`, `rdx` =
`4 (_len + 1 - index - count)`, `rbx` = `count`, `rbp` = `this`. -/
abbrev gM (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rax := BitVec.setWidth 64 (ix V g),
      rcx := rdq(V, g.rdi),
      rdx := BitVec.setWidth 64 (ln V g + 1#32 - ix V g) <<< 2,
      rbx := BitVec.setWidth 64 (cnt V g),
      rbp := g.rdi,
      rsp := g.rsp - 8 - 8 - 8,
      rsi := rdq(V, g.rdi) + BitVec.setWidth 64 (ix V g) * 4#64,
      rdi := rdq(V, g.rdi) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi) * 4#64,
      r8 := rdq(V, g.rdi) + BitVec.setWidth 64 (ix V g) * 4#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `count` 0: the entry's code, the `jne` not taken, `add rsp, 8; pop rbx; pop rbp` to the `ret` at 37. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (cnt V g == 0) = true)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 + 8#64 + 8) i))
    (hx : rdd(Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), g.rdi + 8#64) =
      rdd(V, g.rdi + 8#64))
    (h : ∀ fl, Q 37
      { g with
          rax := BitVec.setWidth 64 (ln V g - BitVec.setWidth 32 g.rsi),
          rcx := BitVec.setWidth 64 (A g),
          rdx := BitVec.setWidth 64 (ln V g),
          rbx := rdq(V0 V g, g.rsp - 8 - 8 - 8 + 8#64),
          rbp := rdq(V0 V g, g.rsp - 8 - 8 - 8 + 8#64 + 8),
          rsp := g.rsp - 8 - 8 - 8 + 8#64 + 8 + 8 } fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cnt, ln, A] at hz hs1 hs2 fl hl1 hl2 hx h ⊢
  wpx [W_0, W_31, W_48, o0, o1, o2, hx, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true,
      false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact h _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `count` not 0: the entry's code, the `jne` taken, up to the `call` at 79. -/
theorem vc_nz {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (cnt V g == 0) = false)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hx : rdd(Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), g.rdi + 8#64) =
      rdd(V, g.rdi + 8#64))
    (hx2 : rdq(Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), g.rdi) =
      rdq(V, g.rdi))
    (h : ∀ fl, Q 79 (gM V g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gM, ix, cnt, ln, A] at hz hs1 hs2 fl fa hx hx2 h ⊢
  wpx [W_0, W_31, W_48, o0, o1, o2, hx, hx2, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true,
      false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact h _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- After the `sub`: `add rsp, 8; pop rbx; pop rbp` to the `ret` at 93. -/
theorem vc_87 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 93
      { g with
          rbx := rdq(V, g.rsp + 8#64),
          rbp := rdq(V, g.rsp + 8#64 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 } fl V) :
    W_87 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_87, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::Delete (index, count)` (`this` = `rdi`, `index` = `esi`, `count` = `edx`) from its entry. With `count`
(cut to `_len - index`) 0, at the return address with `rbx`, `rbp`, `rsp` restored and no byte changed but the
pushed ones (`kn`). Else at `memmove`'s PLT entry with the registers `gM` (`rsp` 32 below the entry's) and the bytes
`V0` with the return address `udl_at + 84` pushed (`kf`); if `memmove` returns there with `rsp`, `rbx`, `rbp` as at
its entry and the saved `rbx`, `rbp` and the return address as they were, the run reaches the return address with
`_len` less `count` and `rbx`, `rbp`, `rsp` restored (`kr`). -/
theorem udl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L udl_at udl)
    {codeP : List Byte} (hinP : CodeIn L plt_memmove codeP) (hP : 0 < codeP.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = udl_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : cnt V X.cpu.gpr = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (V0 V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
          rax := BitVec.setWidth 64 (ln V X.cpu.gpr - BitVec.setWidth 32 X.cpu.gpr.rsi),
          rcx := BitVec.setWidth 64 (A X.cpu.gpr),
          rdx := BitVec.setWidth 64 (ln V X.cpu.gpr),
          rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : cnt V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (udl_at.add 84) 8)) →
      Y.cpu.rip = plt_memmove → Y.cpu.gpr = (gM V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = udl_at.add 84 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbx = BitVec.setWidth 64 (cnt V X.cpu.gpr) → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V', X.cpu.gpr.rdi + 8#64) - cnt V X.cpu.gpr) 4)) →
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
  have e32b : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by rw [e24, e32b]
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
  -- the bytes outside the pushed `rbp` and `rbx`
  have m0 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (V0 V X.cpu.gpr) = (byteAddrs x n).map V := by
    intro x n hx h
    have a1 := Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) x n (by rw [toBytesLE_length, e16, tn16]; omega) hx
      (by rw [toBytesLE_length, e16, tn16]; omega)
    have a2 := Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) x n
      (by rw [toBytesLE_length, tn8]; omega) hx (by rw [toBytesLE_length, tn8]; omega)
    exact a1.trans a2
  have hx : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = rdd(V, X.cpu.gpr.rdi + 8#64) := by
    rw [m0 (X.cpu.gpr.rdi + 8#64) 4 (by rw [t8]; omega) (by rw [t8]; omega)]
  have fl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i) := fun i hi => c.hws _ (fw8 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = udl_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : cnt V X.cpu.gpr = 0
  · -- `count` 0: to the `ret` at 37
    have hz : (cnt V X.cpu.gpr == 0) = true := beq_iff_eq.2 h0
    have hb1 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
      dsimp only [V0]
      rw [e16, Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8) (toBytesLE_length _ _) (by rw [tn16]; omega), ofBytesLE_toBytesLE rfl]
    have hb2 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
      dsimp only [V0]
      rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
          (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8 (by rw [toBytesLE_length, e16, tn16]; omega)
          (by rw [tn8]; omega) (by rw [toBytesLE_length, e16, tn16, tn8]; omega),
        Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (toBytesLE_length _ _)
          (by rw [tn8]; omega), ofBytesLE_toBytesLE rfl]
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧
        g' = { X.cpu.gpr with
          rax := BitVec.setWidth 64 (ln V X.cpu.gpr - BitVec.setWidth 32 X.cpu.gpr.rsi),
          rcx := BitVec.setWidth 64 (A X.cpu.gpr),
          rdx := BitVec.setWidth 64 (ln V X.cpu.gpr) } ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_z hz hs1 (by rw [e16]; exact hs2) fl (by rw [e24, r16]; exact h16) (by rw [e24, r16, r8]; exact h8) hx
        fun _ => ⟨rfl, by rw [e24, r16, r8, e8, hb1, hb2], rfl⟩) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_37 _) (by rw [hsp]; exact hl) hin₂ h₂
      (by rw [hsp, m0 _ 8 hp8 (Or.inr (Nat.le_refl _))]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn h0 Z t' hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- `count` not 0: to the `call`
    have hz : (cnt V X.cpu.gpr == 0) = false := beq_eq_false_iff_ne.2 h0
    have hx2 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by
      rw [m0 X.cpu.gpr.rdi 8 (by omega) (by omega)]
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 79 ∧ g' = gM V X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_nz hz hs1 (by rw [e16]; exact hs2) fl fa hx hx2 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_79 _) hinP hP tgt_79 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gM V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gM V X.cpu.gpr).set 4 v) e32
    refine kf h0 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `memmove`: the `sub`
    intro Z V' t'' hKZ hAZ hrZ hzs hzp hzb hc1 hc2 hcr hPc
    have hea : eaD Z 5 8 = X.cpu.gpr.rdi + 8#64 := by
      show Z.cpu.gpr.get (regOf 5) + BitVec.ofNat 64 8 = _
      rw [show Z.cpu.gpr.get (regOf 5) = Z.cpu.gpr.rbp from rfl, hzp]
    have hrv : rv Z 32 3 = cnt V X.cpu.gpr := by
      show (Z.cpu.gpr.get (regOf 3)).setWidth 32 = _
      rw [show Z.cpu.gpr.get (regOf 3) = Z.cpu.gpr.rbx from rfl, hzb, sw_64_32]
    refine c.s_sub_mr32 hKZ hAZ hin (lt_len (by decide)) hrZ (sub_84 _) (by rw [hea]; exact fw8) ?_
    rintro U t₃ hKU hAU ⟨hrU, hgU⟩
    rw [hea, hrv] at hAU
    -- the bytes outside `_len`
    have m2 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
        (x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8 ∨ X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat) →
        (byteAddrs x 8).map
          (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V', X.cpu.gpr.rdi + 8#64) - cnt V X.cpu.gpr) 4)) =
        (byteAddrs x 8).map V' := by
      intro x hx h
      exact Tun.rd_Vst V' (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (rdd(V', X.cpu.gpr.rdi + 8#64) - cnt V X.cpu.gpr) 4) x 8
        (by rw [toBytesLE_length, t8]; omega) hx (by rw [toBytesLE_length, t8]; omega)
    have hc1' := m2 (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)
    have hc2' := m2 (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)
    have hcr' := m2 X.cpu.gpr.rsp hp8 (by omega)
    have hrU' : U.cpu.rip = udl_at.add 87 := hrU
    refine (c_87 prof).run c hin (fun j' g' _ V₃ => j' = 93 ∧
        g' = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp } ∧
        V₃ = Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V', X.cpu.gpr.rdi + 8#64) - cnt V X.cpu.gpr) 4))
      hKU hAU hrU'
      (vc_87 (by rw [hgU, hzs, r16]; exact h16) (by rw [hgU, hzs, r16, r8]; exact h8)
        fun _ => ⟨rfl, by rw [hgU, hzs, r16, r8, e8, hc1', hc2', hc1, hc2], rfl⟩) ?_
    rintro j' g fl₂ V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₄
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_93 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂, hcr']; exact hcr) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₂]
    try rfl

end FV7z.Udl
