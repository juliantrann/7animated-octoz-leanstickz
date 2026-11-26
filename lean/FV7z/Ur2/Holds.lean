import FV7z.Ur2.Cuts
import FV7z.Onw
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::ReAlloc2` (PLAN.md §M, M1)

7-Zip 26.06's `UString::ReAlloc2 (newLimit)` at `0x44d010` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`newLimit` in `esi`: above `0x3ffffffe` (`ja` at 14) to the throw stub at `0x4013c2`, else `newBuf = new
wchar_t[newLimit + 1]` (`call` at 35 to `operator new`, `Onw.onw_at + 64`, with `4 newLimit + 4` bytes),
`newBuf[0] = 0`, `delete [] _chars` unless null (`call` at 57 to the thunk at `0x6014f0`; `_chars` the 8 bytes at
`this`), then `_chars = newBuf`, `_limit` (the 4 bytes at `this + 12`) = `newLimit` and `_len` (the 4 at `this + 8`)
= 0. `push r12; push rbp; push rbx`, `rbx` = `this`, `rbp` = `newLimit` across the calls and `r12` = `newBuf` after
the first, `pop rbx; pop rbp; pop r12; ret` (79).

The callees are hypotheses (`kt`, `kn`, `kd`), as in `FV7z/Ura/Holds.lean`: a continuation at each entry, given the
run from its return (`rsp` 24 below the entry's, `rbx`, `rbp` and `r12` as the caller left them, the saved registers
and the return address as they were: `Sv`) and the callee's own post (`Pn`, `Pd`). `pn`: `newBuf`'s first 4 bytes
writable, clear of the saved registers and the return address.

- `zl`, `gN`, `VN`: `newLimit` zero-extended; the registers and the bytes at the first `call`.
- `Vz`: the bytes after `newBuf[0] = 0`; `VE`: after the stores of `_chars`, `_limit` and `_len`.
- `Sv`: the saved `rbx`, `rbp`, `r12` and the return address in the bytes.
- `vc_0`, `vc_20`, `vc_40`, `vc_62`: the verification conditions of the pieces.
- `ur2_ok`: from the entry, through the callees, to the return address (`kr0` for a null `_chars`, else `kr1`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ur2

/-- The `ja` to the throw stub. -/
def pja : List Byte := [0x0f, 0x87, 0x9e, 0x43, 0xfb, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709241246] 6) := by dec_rfl
theorem wj_14 : pja <+: ur2.drop 14 := by decide +kernel
theorem ja_14 (feat : Features) : Dec feat ur2 14 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709241246] 6) :=
  Dec.shift (j := 14) (k := 0) (pja_0 feat) wj_14 (Nat.zero_le _)
theorem tgt_14 : ur2_at.add (14 + 6) + BitVec.ofNat 64 18446744073709241246 = (0x4013c2#64).add 0 := by decide

/-- The `call`s to `operator new` and the thunk of `operator delete []`. -/
def pcn : List Byte := [0xe8, 0x78, 0x59, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1792376] 5) := by dec_rfl
theorem wc_35 : pcn <+: ur2.drop 35 := by decide +kernel
theorem call_35 (feat : Features) : Dec feat ur2 35 (FV7z.mk .call 64 [.rel 1792376] 5) :=
  Dec.shift (j := 35) (k := 0) (pcn_0 feat) wc_35 (Nat.zero_le _)
theorem tgt_35 : ur2_at.add (35 + 5) + BitVec.ofNat 64 1792376 = Onw.onw_at.add 64 := by decide
def pcd : List Byte := [0xe8, 0xa2, 0x44, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1787042] 5) := by dec_rfl
theorem wc_57 : pcd <+: ur2.drop 57 := by decide +kernel
theorem call_57 (feat : Features) : Dec feat ur2 57 (FV7z.mk .call 64 [.rel 1787042] 5) :=
  Dec.shift (j := 57) (k := 0) (pcd_0 feat) wc_57 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_79 : pret <+: ur2.drop 79 := by decide +kernel
theorem ret_79 (feat : Features) : Dec feat ur2 79 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 79) (k := 0) (pret_0 feat) w_79 (Nat.zero_le _)

/-- `newLimit` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers at the first `call`: `rax` = `rbp` = `newLimit`, `rbx` = `this`, `rdi` = `4 newLimit + 4`, 24
below the entry. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with rax := zl g, rbp := zl g, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8, rdi := zl g * 4#64 + 4#64 }

/-- The bytes after the pushes of `r12`, `rbp`, `rbx`. -/
abbrev VN (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The bytes after `newBuf[0] = 0` for `newBuf` at `a`. -/
abbrev Vz (V : Addr → Byte) (a : Addr) : Addr → Byte := Vst V a (toBytesLE 0#32 4)

/-- The bytes after `_chars` = `p`, `_limit` = `v` and `_len` = 0 for the object at `b`. -/
abbrev VE (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)) (b + 8#64) (toBytesLE 0#32 4)

/-- The saved `rbx`, `rbp`, `r12` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 24) = x.rbx ∧ rdq(V, x.rsp - 16) = x.rbp ∧ rdq(V, x.rsp - 8) = x.r12 ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; push rbp; push rbx; cmp esi, 0x3ffffffe` to the `ja` at 14 (taken only above `0x3ffffffe`). -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' f' V' => j' = 14 ∧ g' = { g with rsp := g.rsp - 8 - 8 - 8 } ∧ V' = VN V g ∧
      (f'.cond 7 = true → 1073741822 < (BitVec.setWidth 32 g.rsi).toNat)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 ⊢
  wpx [W_0, o0, VN]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _
    | (rename_i h
       simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
       bv_omega)
    | (rename_i h; simp at h; bv_omega)

/-- `mov eax, esi; mov rbx, rdi; mov ebp, esi; lea rdi, [rax * 4 + 4]` to the `call` at 35. -/
theorem vc_20 {g x : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hg : g = { x with rsp := x.rsp - 8 - 8 - 8 })
    (h : ∀ fl, Q 35 (gN x) fl V) : W_20 F Wl Q g f V := by
  subst hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := x
  dsimp only at h ⊢
  wpx [W_20, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new`: `mov rdi, [rbx]; mov dword [rax], 0; mov r12, rax; test rdi, rdi; je 62`, else to the
`call` at 57. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p a : Addr} (hbx : g.rbx = p)
    (hax : g.rax = a) (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (fa : ∀ i < 4, Foot Wl (Addr.add a i))
    (h62 : rdq(V, p) = 0 → ∀ fl, Q 62 { g with rdi := rdq(V, p), r12 := a } fl (Vz V a))
    (h57 : rdq(V, p) ≠ 0 → ∀ fl, Q 57 { g with rdi := rdq(V, p), r12 := a } fl (Vz V a)) :
    W_40 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx hax f0 fa h62 h57 ⊢
  subst hbx hax
  by_cases h1 : rdq(V, rbx) = 0
  · have hb : (rdq(V, rbx) == 0) = true := beq_iff_eq.2 h1
    wpx [W_40, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h62 h1 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rdq(V, rbx) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_40, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h57 h1 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `mov [rbx], r12; mov [rbx + 12], ebp; mov dword [rbx + 8], 0; pop rbx; pop rbp; pop r12` to the `ret` at 79. -/
theorem vc_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 79
      { g with
          rbx := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp),
          rbp := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8),
          r12 := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl
      (VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp))) :
    W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w12 w8 hl0 hl1 hl2 h ⊢
  wpx [W_62, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::ReAlloc2 (newLimit)` (`this` = `rdi`, `newLimit` = `esi`) from its entry. Above `0x3ffffffe`, at the
throw stub with `rsp` 24 below the entry's and the bytes `VN` (`kt`). Else at `operator new`'s entry with the
registers `gN`, `rsp` 32 below the entry's, the bytes `VN` with the return address pushed (`kn`); back at
`ur2_at + 40` (`Sv`, `Pn`), at the return address with `newBuf[0] = 0` (`Vz`), `_chars` = `newBuf`, `_limit` =
`newLimit`, `_len` = 0 (`VE`) if `_chars` was null (`kr0`), else at the thunk of `operator delete []` with `rdi` =
`_chars` (`kd`), and back at `ur2_at + 62` (`Pd`) at the return address likewise (`kr1`). -/
theorem ur2_ok {Pn : State → (Addr → Byte) → Prop} {Pd : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ur2_at ur2) (hinN : CodeIn L Onw.onw_at Onw.onw)
    {codeT : List Byte} (hinT : CodeIn L 0x4013c2#64 codeT) (hT : 0 < codeT.length)
    {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ur2_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (t' : Nat), 1073741822 < (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (VN V X.cpu.gpr) → Y.cpu.rip = 0x4013c2#64 →
      Y.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 24 } → GoG prof L o gev gP gE Y t')
    (kn : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VN V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ur2_at.add 40) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = ur2_at.add 40 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zn.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbp = zl X.cpu.gpr → Sv V₁ X.cpu.gpr (e₂.add j₂) → Pn Zn V₁ → GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (pn : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → (∀ i < 4, Foot Wl (Addr.add Zn.cpu.gpr.rax i)) ∧
      Zn.cpu.gpr.rax.toNat + 4 ≤ 2 ^ 64 ∧
      (Zn.cpu.gpr.rax.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ Zn.cpu.gpr.rax.toNat))
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vz V₁ Zn.cpu.gpr.rax) (X.cpu.gpr.rsp - 32) (toBytesLE (ur2_at.add 62) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 32) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = ur2_at.add 62 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zd.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbp = zl X.cpu.gpr → Zd.cpu.gpr.r12 = Zn.cpu.gpr.rax → Sv V₃ X.cpu.gpr (e₂.add j₂) →
        Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kr0 : ∀ (Zn : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), Pn Zn V₁ →
      rdq(V₁, X.cpu.gpr.rdi) = 0 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (VE (Vz V₁ Zn.cpu.gpr.rax) X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zn.cpu.gpr with
          rdi := rdq(V₁, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), Pd Zn Zd V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VE V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zd.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
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
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes outside the object as they were after the stores of `_chars`, `_limit` and `_len`
  have m1 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (y : Addr), y.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ y.toNat ∨ y.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs y 8).map (VE W X.cpu.gpr.rdi p v) = (byteAddrs y 8).map W := by
    intro W p v y hy h
    have a0 := Tun.rd_Vst (Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4))
      (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#32 4) y 8
      (by rw [toBytesLE_length, t8]; omega) hy (by rw [toBytesLE_length, t8]; omega)
    have a1 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) y 8
      (by rw [toBytesLE_length, t12]; omega) hy (by rw [toBytesLE_length, t12]; omega)
    have a2 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) y 8 (by rw [toBytesLE_length]; omega) hy
      (by rw [toBytesLE_length]; omega)
    exact a0.trans (a1.trans a2)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 62 to the return address, either way
  have fin : ∀ (U : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = ur2_at.add 62 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.rbx = X.cpu.gpr.rdi →
      U.cpu.gpr.rbp = zl X.cpu.gpr → Sv W X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
        Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = { U.cpu.gpr with
            rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U W t' hKU hAU hrU hus hub hup hsv k
    have hv : BitVec.setWidth 32 U.cpu.gpr.rbp = BitVec.setWidth 32 X.cpu.gpr.rsi := by
      rw [hup]
      exact sw_64_32 _
    have hb1 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 24) =
        X.cpu.gpr.rbx := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]
      exact hsv.1
    have hb2 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 16) =
        X.cpu.gpr.rbp := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
      exact hsv.2.1
    have hb3 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 8) =
        X.cpu.gpr.r12 := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
      exact hsv.2.2.1
    have hb4 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [m1 W _ _ X.cpu.gpr.rsp hp8 (by omega)]
      exact hsv.2.2.2
    refine (c_62 prof).run c hin (fun j' g' _ V' => j' = 79 ∧
        g' = { U.cpu.gpr with
            rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp } ∧
        V' = VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) hKU hAU hrU
      (vc_62 (by rw [hub]; exact fw0) (by rw [hub]; exact fw12) (by rw [hub]; exact fw8) (by rw [hus]; exact h24)
        (by rw [hus, a16]; exact h16) (by rw [hus, a16, a8]; exact h8)
        fun _ => ⟨rfl, by rw [hub, hv, hus, a16, a8, e8, hb1, hb2, hb3], by rw [hub, hv]⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_79 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hb4) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₅ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  have hrip' : X.cpu.rip = ur2_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the pushes and `cmp esi, 0x3ffffffe`
  refine (c_0 prof).run c hin (fun j' g' f' V' => j' = 14 ∧ g' = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8 - 8 - 8 } ∧
      V' = VN V X.cpu.gpr ∧ (f'.cond 7 = true → 1073741822 < (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat)) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁, hja⟩ Y t₁ hKY hAY hrY hgY hfY
  subst V₁
  -- `ja` to the throw stub
  refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_14 _) hinT (tgt := 0) hT tgt_14 ?_ ?_
  · intro hc
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine kt Y₂ t₂ (hja (by rw [← hfY]; exact hc)) hK₂ hA₂ (by rw [hr₂, addr_add_zero]) ?_
    rw [hg₂, hgY, e24]
  intro _
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  -- to the `call` of `operator new`
  refine (c_20 prof).run c hin (fun j' g' _ V' => j' = 35 ∧ g' = gN X.cpu.gpr ∧ V' = VN V X.cpu.gpr) hK₂ hA₂ hr₂
    (vc_20 (hg₂.trans hgY) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₁
  have hsY : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_35 _) hinN (tgt := 64) (Onw.lt_len (by decide))
    tgt_35 hst ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsY, c32] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₄, hsY, c32, hg₃]
  refine kn Y₄ t₄ hK₄ hA₄ hr₄ hg₄' ?_
  -- back from `operator new`
  intro Zn V₁ t₅ hKn hAn hrn hns hnb hnp hsv1 hPn
  obtain ⟨fa, ha4, hda⟩ := pn Zn V₁ hPn
  -- the saved registers and the return address past `newBuf[0] = 0`
  have mz : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 →
      (Zn.cpu.gpr.rax.toNat + 4 ≤ y.toNat ∨ y.toNat + 8 ≤ Zn.cpu.gpr.rax.toNat) →
      (byteAddrs y 8).map (Vz V₁ Zn.cpu.gpr.rax) = (byteAddrs y 8).map V₁ := fun y hy h =>
    Tun.rd_Vst V₁ Zn.cpu.gpr.rax (toBytesLE 0#32 4) y 8 (by rw [toBytesLE_length]; omega) hy
      (by rw [toBytesLE_length]; omega)
  have hsvz : Sv (Vz V₁ Zn.cpu.gpr.rax) X.cpu.gpr (e₂.add j₂) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mz _ (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact hsv1.1
    · rw [mz _ (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact hsv1.2.1
    · rw [mz _ (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hsv1.2.2.1
    · rw [mz _ hp8 (by omega)]; exact hsv1.2.2.2
  refine (c_40 prof).run c hin (fun j' g' _ V' => V' = Vz V₁ Zn.cpu.gpr.rax ∧
      g' = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax } ∧
      ((j' = 62 ∧ rdq(V₁, X.cpu.gpr.rdi) = 0) ∨ (j' = 57 ∧ rdq(V₁, X.cpu.gpr.rdi) ≠ 0))) hKn hAn hrn
    (vc_40 hnb rfl fr0 fa (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
  rintro j' g fl V₂ ⟨hV₂, rfl, h⟩ U t₆ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hns
  have hbU : U.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgU]; exact hnb
  have hpU : U.cpu.gpr.rbp = zl X.cpu.gpr := by rw [hgU]; exact hnp
  rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · -- a null `_chars`: no `delete []`
    refine fin U (Vz V₁ Zn.cpu.gpr.rax) t₆ hKU hAU hrU hsU hbU hpU hsvz ?_
    intro Z' t₇ hKZ' hAZ' hrZ' hgZ'
    have hr12 : U.cpu.gpr.r12 = Zn.cpu.gpr.rax := by rw [hgU]
    rw [hr12] at hAZ'
    refine kr0 Zn V₁ Z' t₇ hPn h0 hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl
  · -- `delete [] _chars`
    have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c32]; exact hs4
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_57 _) hinD hD (by decide) hst5 ?_
    rintro Y₅ t₈ hK₅ hA₅ ⟨hr₅, hg₅⟩
    rw [hsU, c32] at hA₅
    have hg₅' : Y₅.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 32) := by
      rw [hg₅, hsU, c32, hgU]
    refine kd Zn V₁ hPn h0 Y₅ t₈ hK₅ hA₅ hr₅ hg₅' ?_
    intro Zd V₃ t₉ hKd hAd hrd hds hdb hdp hd12 hsv3 hPd
    refine fin Zd V₃ t₉ hKd hAd hrd hds hdb hdp hsv3 ?_
    intro Z' t₁₀ hKZ' hAZ' hrZ' hgZ'
    rw [hd12] at hAZ'
    exact kr1 Zn Zd V₃ Z' t₁₀ hPd hKZ' hAZ' hrZ' hgZ'

end FV7z.Ur2
