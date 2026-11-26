import FV7z.Acs.Cuts
import FV7z.Asl.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `AString::AString (s1, num1, s2, num2)` (PLAN.md §M, M1)

7-Zip's `AString (const char *s1, unsigned num1, const char *s2, unsigned num2)` at `0x44c260` in `7zzs`
(`CPP/Common/MyString.cpp`): with `this` in `rdi`, `s1` in `rsi`, `num1` in `edx`, `s2` in `rcx` and `num2` in `r8d`,
`SetStartLen (num1 + num2)` (`call` at 30 to `Asl.asl_at`, proved in `FV7z/Asl/Holds.lean`), `memcpy (_chars, s1,
num1)` (`call` at 45 to the PLT entry at `0x401070`), then a tail jump at 70 to `memcpy (_chars + num1, s2, num2 + 1)`.
`push r14; push r13; push r12; push rbp; push rbx`; `r14` = `s1`, `r13` = `s2`, `r12` = `this`, `rbp` = `num2`,
`rbx` = `num1` across the calls; the five `pop`s before the jump.

`SetStartLen` is run by `Asl.asl_ok`; its own callee (`operator new`) is a hypothesis (`kf`) in the form `asl_ok`
takes, with the post `r12`, `r13`, `r14` as they were and `P1`. `memcpy` is a hypothesis (`km`), as in
`FV7z/Arl/Holds.lean`: a continuation at its entry, given the run from its return (`rsp` 40 below the entry's, `rbx`,
`rbp`, `r13` as they were, the saved registers as they were (`Sv`), and the callee's post `P2`) on. The tail jump is
a continuation (`kj`) at `0x401070`.

- `zd`, `zr`, `nl`: `num1`, `num2` zero-extended; `num1 + num2` (32 bits).
- `gS`, `V0`: the registers and the bytes at the `call` of `SetStartLen`; `gY`, `VY`: at its entry.
- `gT`: the registers at the jump; `Sv`: the saved registers.
- `vc_0`, `vc_35`, `vc_50`: the verification conditions of the three pieces.
- `acs_ok`: from the entry, through `SetStartLen` and `memcpy`, to the jump.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Acs

/-- The `call`s to `SetStartLen` and `memcpy`'s PLT entry. -/
def pcs : List Byte := [0xe8, 0xdd, 0xfd, 0xff, 0xff]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 18446744073709551069] 5) := by dec_rfl
theorem wc_30 : pcs <+: acs.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat acs 30 (FV7z.mk .call 64 [.rel 18446744073709551069] 5) :=
  Dec.shift (j := 30) (k := 0) (pcs_0 feat) wc_30 (Nat.zero_le _)
def pcm : List Byte := [0xe8, 0xde, 0x4d, 0xfb, 0xff]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 18446744073709243870] 5) := by dec_rfl
theorem wc_45 : pcm <+: acs.drop 45 := by decide +kernel
theorem call_45 (feat : Features) : Dec feat acs 45 (FV7z.mk .call 64 [.rel 18446744073709243870] 5) :=
  Dec.shift (j := 45) (k := 0) (pcm_0 feat) wc_45 (Nat.zero_le _)

/-- The tail jump to `memcpy`'s PLT entry. -/
def pjm : List Byte := [0xe9, 0xc5, 0x4d, 0xfb, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709243845] 5) := by dec_rfl
theorem wj_70 : pjm <+: acs.drop 70 := by decide +kernel
theorem jmp_70 (feat : Features) : Dec feat acs 70 (FV7z.mk .jmp 64 [.rel 18446744073709243845] 5) :=
  Dec.shift (j := 70) (k := 0) (pjm_0 feat) wj_70 (Nat.zero_le _)

/-- `num1` (`edx`) zero-extended. -/
abbrev zd (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)
/-- `num2` (`r8d`) zero-extended. -/
abbrev zr (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.r8)
/-- `num1 + num2`, 32 bits. -/
abbrev nl (g : Gprs) : BitVec 32 := BitVec.setWidth 32 g.rdx + BitVec.setWidth 32 g.r8

/-- The registers at the `call` of `SetStartLen`: `r14` = `s1`, `r13` = `s2`, `r12` = `this`, `rbp` = `num2`, `rbx`
= `num1`, `esi` = `num1 + num2` (`lea esi, [rbx + r8]`), five pushed. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with
      r14 := g.rsi
      r13 := g.rcx
      r12 := g.rdi
      rbp := zr g
      rbx := zd g
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 (zd g + g.r8 * BitVec.ofNat 64 1 + BitVec.ofNat 64 0))
      rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The bytes at the `call` of `SetStartLen`: `r14`, `r13`, `r12`, `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at `SetStartLen`'s entry. -/
abbrev gY (g : Gprs) : Gprs := (gS g).set 4 (g.rsp - 48)
/-- The bytes at `SetStartLen`'s entry: the return address `acs_at + 35` pushed. -/
abbrev VY (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 48) (toBytesLE (acs_at.add 35) 8)

/-- The registers at the jump: `edx` = `num2 + 1` (`lea edx, [rbp + 1]`), `rsi` = `s2`, `rdi` = `rax + num1`, the
five `pop`s. -/
abbrev gT (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rbp + optV g none * BitVec.ofNat 64 1 + BitVec.ofNat 64 1))
      rsi := g.r13
      rdi := g.rax + g.rbx
      rbx := rdq(V, g.rsp)
      rbp := rdq(V, g.rsp + 8)
      r12 := rdq(V, g.rsp + 8 + 8)
      r13 := rdq(V, g.rsp + 8 + 8 + 8)
      r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8)
      rsp := g.rsp + 8 + 8 + 8 + 8 + 8 }

/-- The saved `r14`, `r13`, `r12`, `rbp`, `rbx`, for the registers `g` at the entry. -/
def Sv (V : Addr → Byte) (g : Gprs) : Prop :=
  rdq(V, g.rsp - 8) = g.r14 ∧ rdq(V, g.rsp - 16) = g.r13 ∧ rdq(V, g.rsp - 24) = g.r12 ∧
    rdq(V, g.rsp - 32) = g.rbp ∧ rdq(V, g.rsp - 40) = g.rbx

/-- `SetStartLen`'s `len`. -/
theorem lnE (g : Gprs) : BitVec.setWidth 32 (gS g).rsi = nl g := by
  show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
    (zd g + g.r8 * BitVec.ofNat 64 1 + BitVec.ofNat 64 0))) = nl g
  rw [sw_64_32, BitVec.mul_one, BitVec.add_zero, BitVec.setWidth_add _ _ (by decide), sw_64_32]

/-- `lea edx, [rbp + 1]` with `rbp` a zero-extended `x`. -/
theorem lea1 (g : Gprs) (x : BitVec 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 x + optV g none * BitVec.ofNat 64 1 +
      BitVec.ofNat 64 1)) = BitVec.setWidth 64 (x + 1#32) := by
  have h0 : optV g none = 0#64 := rfl
  have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 1) = 1#32 := by decide
  rw [h0, BitVec.zero_mul, BitVec.add_zero, BitVec.setWidth_add _ _ (by decide), sw_64_32, h1]

/-- `_chars` after `SetStartLen`. -/
theorem rd1 (V : Addr → Byte) (b : Addr) (v : BitVec 32) (p : BitVec 64) (hb : b.toNat + 8 ≤ 2 ^ 64) :
    rdq(Asl.V1 V b v p, b) = p := by
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hb, ofBytesLE_toBytesLE (n := 8) rfl]

variable {F : Footprint} {Wl : List Rgn}

/-- `push r14; mov r14, rsi; push r13; mov r13, rcx; push r12; mov r12, rdi; push rbp; mov ebp, r8d; push rbx;
mov ebx, edx; lea esi, [rbx + r8]`, to the `call` at 30. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 hs5 ⊢
  wpx [W_0, o0, gS, V0, zd, zr]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov rdi, [r12]; mov rdx, rbx; mov rsi, r14`, to the `call` at 45. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ fl, Q 45 { g with rdi := rdq(V, g.r12), rdx := g.rbx, rsi := g.r14 } fl V) :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  wpx [W_35, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `memcpy`: `lea edx, [rbp + 1]; mov rsi, r13; mov rdi, rax; add rdi, rbx` and the five `pop`s, to the
jump at 70. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (l0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i)) :
    W_50 F Wl (fun j' g' _ V' => j' = 70 ∧ g' = gT V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l0 l1 l2 l3 l4 ⊢
  wpx [W_50, o2, gT]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString (s1, num1, s2, num2)` (`this` = `rdi`, `s1` = `rsi`, `num1` = `edx`, `s2` = `rcx`, `num2` = `r8d`) from
its entry. `SetStartLen (num1 + num2)` runs with the registers `gY` and the bytes `VY` at its entry; its callee is
`kf`, in the form `Asl.asl_ok` takes, whose post keeps `r12`, `r13`, `r14` and gives `P1`. Back at 35, at `memcpy`'s
entry `rdi` = the new `_chars` (the callee's `rax`), `rsi` = `s1`, `rdx` = `num1`, and the bytes have `_chars`,
`_len`, `_limit` as `SetStartLen` stores them (`Asl.V1`) (`km`); back at 50 (`rbx`, `rbp`, `r13` kept, `Sv`, `P2`),
the run jumps to `memcpy`'s entry with `rdi` = `rax + num1`, `rsi` = `s2`, `edx` = `num2 + 1` and `rbx`, `rbp`,
`r12`, `r13`, `r14`, `rsp` restored (`kj`). -/
theorem acs_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L acs_at acs)
    (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw)
    {codeM : List Byte} (hinM : CodeIn L 0x401070#64 codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acs_at)
    (hp : 80 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hs7 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56) i))
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 64) i))
    (hs10 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 80) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V0 (VY V X.cpu.gpr) (gY X.cpu.gpr)) ((gY X.cpu.gpr).rsp - 32) (toBytesLE (Asl.asl_at.add 34) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (Asl.gC (gY X.cpu.gpr)).set 4 ((gY X.cpu.gpr).rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Asl.asl_at.add 34 → Z.cpu.gpr.rsp = (gY X.cpu.gpr).rsp - 24 →
        Z.cpu.gpr.rbx = (gY X.cpu.gpr).rdi → Z.cpu.gpr.rbp = Asl.zl (gY X.cpu.gpr) →
        rdq(V', (gY X.cpu.gpr).rsp - 16) = (gY X.cpu.gpr).rbx →
        rdq(V', (gY X.cpu.gpr).rsp - 8) = (gY X.cpu.gpr).rbp → rdq(V', (gY X.cpu.gpr).rsp) = acs_at.add 35 →
        (Z.cpu.gpr.r12 = X.cpu.gpr.rdi ∧ Z.cpu.gpr.r13 = X.cpu.gpr.rcx ∧ Z.cpu.gpr.r14 = X.cpu.gpr.rsi ∧
          P1 Z V') →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (km : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V1 V' X.cpu.gpr.rdi (nl X.cpu.gpr) Z.cpu.gpr.rax) (X.cpu.gpr.rsp - 48)
          (toBytesLE (acs_at.add 50) 8)) →
      Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        ({ Z.cpu.gpr with
            rbx := zd X.cpu.gpr
            rbp := zr X.cpu.gpr
            rdi := Z.cpu.gpr.rax
            rdx := zd X.cpu.gpr
            rsi := X.cpu.gpr.rsi } : Gprs).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = acs_at.add 50 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = zd X.cpu.gpr →
        Z₂.cpu.gpr.rbp = zr X.cpu.gpr → Z₂.cpu.gpr.r13 = X.cpu.gpr.rcx → Sv V'' X.cpu.gpr → P2 Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kj : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V'' → Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        { Z₂.cpu.gpr with
            rdx := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.r8 + 1#32)
            rsi := X.cpu.gpr.rcx
            rdi := Z₂.cpu.gpr.rax + zd X.cpu.gpr
            rbx := X.cpu.gpr.rbx
            rbp := X.cpu.gpr.rbp
            r12 := X.cpu.gpr.r12
            r13 := X.cpu.gpr.r13
            r14 := X.cpu.gpr.r14
            rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn56 : (X.cpu.gpr.rsp - 56).toNat = X.cpu.gpr.rsp.toNat - 56 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn64 : (X.cpu.gpr.rsp - 64).toNat = X.cpu.gpr.rsp.toNat - 64 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn80 : (X.cpu.gpr.rsp - 80).toNat = X.cpu.gpr.rsp.toNat - 80 := by rw [BitVec.toNat_sub]; simp <;> omega
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
  have e48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have e56 : X.cpu.gpr.rsp - 48 - 8 = X.cpu.gpr.rsp - 56 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn48, tn56]
    simp <;> omega
  have e64 : X.cpu.gpr.rsp - 48 - 16 = X.cpu.gpr.rsp - 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn48, tn64]
    simp <;> omega
  have e80 : X.cpu.gpr.rsp - 48 - 32 = X.cpu.gpr.rsp - 80 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn48, tn80]
    simp <;> omega
  have q40 : X.cpu.gpr.rsp - 48 + 8 = X.cpu.gpr.rsp - 40 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn48, tn40]
    simp <;> omega
  have q32 : X.cpu.gpr.rsp - 40 + 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have q24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have q16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have q8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have q0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hrip' : X.cpu.rip = acs_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40 - 8) i) := by rw [e48]; exact hs6
  -- to the `call` of `SetStartLen`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = gS X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
      (by rw [e40]; exact hs5)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_30 _) hinS (by decide) (by decide) (by rw [hsY]; exact hst)
    ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e48] at hA₂
  have hg2 : Y₂.cpu.gpr = gY X.cpu.gpr := by rw [hg₂, hsY, e48, hgY]
  have hY2s : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 48 := by rw [hg2]; rfl
  have hrdi : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg2]; rfl
  have hrsi : BitVec.setWidth 32 Y₂.cpu.gpr.rsi = nl X.cpu.gpr := by rw [hg2]; exact lnE _
  -- `SetStartLen`
  refine Asl.asl_ok (Pc := fun Z V' => Z.cpu.gpr.r12 = X.cpu.gpr.rdi ∧ Z.cpu.gpr.r13 = X.cpu.gpr.rcx ∧
      Z.cpu.gpr.r14 = X.cpu.gpr.rsi ∧ P1 Z V') c hinS hinW hK₂ hA₂ hr₂
    (by rw [hY2s, tn48]; omega) (by rw [hY2s, tn48]; omega)
    (by rw [hY2s, e56]; exact hs7) (by rw [hY2s, e64]; exact hs8) (by rw [hY2s, e80]; exact hs10)
    (by rw [hY2s]; exact fun i hi => c.hws _ (hs6 i hi))
    (by rw [hrdi]; exact fw0) (by rw [hrdi]; exact fw8) (by rw [hrdi]; exact fw12) (by rw [hrdi]; exact hq)
    (by rw [hrdi, hY2s, tn48]; omega) (e₂ := acs_at) hin (j₂ := 35) (by decide)
    (by rw [hg2]; exact kf) ?_
  -- back from `SetStartLen`, to the `call` of `memcpy`
  rintro Z V' Z' t₃ ⟨h12, h13, h14, hP1⟩ hKZ' hAZ' hrZ' hgZ'
  rw [hrdi, hrsi] at hAZ'
  have hZ'r12 : Z'.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgZ']; exact h12
  have hZ's : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgZ', hg2]; exact q40
  have hrd : rdq(Asl.V1 V' X.cpu.gpr.rdi (nl X.cpu.gpr) Z.cpu.gpr.rax, Z'.cpu.gpr.r12) = Z.cpu.gpr.rax := by
    rw [hZ'r12]; exact rd1 _ _ _ _ (by omega)
  refine (c_35 prof).run c hin (fun j' g' _ V'' => j' = 45 ∧
      g' = { Z'.cpu.gpr with rdi := rdq(V'', Z'.cpu.gpr.r12), rdx := Z'.cpu.gpr.rbx, rsi := Z'.cpu.gpr.r14 } ∧
      V'' = Asl.V1 V' X.cpu.gpr.rdi (nl X.cpu.gpr) Z.cpu.gpr.rax) hKZ' hAZ' hrZ'
    (vc_35 (by rw [hZ'r12]; exact fun i hi => c.hws _ (fw0 i hi)) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₃]; exact hZ's
  refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_45 _) hinM hM (by decide) (by rw [hs3']; exact hst) ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', e48] at hA₄
  have hg₄' : Y₄.cpu.gpr =
      ({ Z.cpu.gpr with
          rbx := zd X.cpu.gpr
          rbp := zr X.cpu.gpr
          rdi := Z.cpu.gpr.rax
          rdx := zd X.cpu.gpr
          rsi := X.cpu.gpr.rsi } : Gprs).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₄, hs3', e48, hg₃, hrd, hgZ', hg2]
    simp only [h14] <;> rfl
  refine km Z V' hP1 Y₄ t₅ hK₄ hA₄ hr₄ hg₄' ?_
  -- back from `memcpy`: the `pop`s and the jump
  intro Z₂ V'' t₆ hK₅ hA₅ hr₅ hz2s hz2b hz2p hz2c hSv hP2
  obtain ⟨v14, v13, v12, vbp, vbx⟩ := hSv
  have h40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40) i) := fun i hi => c.hws _ (hs5 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_50 prof).run c hin (fun j' g' _ V₃ => j' = 70 ∧ g' = gT V'' Z₂.cpu.gpr ∧ V₃ = V'') hK₅ hA₅ hr₅
    (vc_50 (by rw [hz2s]; exact h40) (by rw [hz2s, q32]; exact h32) (by rw [hz2s, q32, q24]; exact h24)
      (by rw [hz2s, q32, q24, q16]; exact h16) (by rw [hz2s, q32, q24, q16, q8]; exact h8)) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Y₅ t₇ hK₆ hA₆ hr₆ hg₆ -
  subst V₃
  refine c.s_jmp_x hK₆ hA₆ hin (lt_len (by decide)) hr₆ (jmp_70 _) hinM hM (by decide) ?_
  rintro Y₆ t₈ hK₇ hA₇ ⟨hr₇, hg₇⟩
  refine kj Z₂ V'' hP2 Y₆ t₈ hK₇ hA₇ (by rw [hr₇, addr_add_zero]) ?_
  rw [hg₇, hg₆]
  dsimp only [gT]
  simp only [hz2b, hz2p, hz2c, hz2s, q32, q24, q16, q8, q0, vbx, vbp, v12, v13, v14, lea1] <;> rfl

end FV7z.Acs
