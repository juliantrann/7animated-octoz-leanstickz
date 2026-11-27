import FV7z.Usb.Cuts
import FV7z.Uau.Holds
import FV7z.Ssl.Holds
/-!
# `UString::SetFromBstr (LPCOLESTR s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::SetFromBstr (s)` at `0x44d820` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `s`
in `rsi`: `len = SysStringLen (s)` (`call` at 23 to `Ssl.ssl_at`, whose contract `Ssl.ssl_ok` is used here); if
`len > _limit` (the 4 bytes at `this + 12`; `jb` at 33) `newBuf = new wchar_t[len + 1]` (`call` at 82 to
`operator new`, `Onw.onw_at + 64`), `delete [] _chars` unless null (`call` at 99 to the thunk at `0x6014f0`),
`_chars = newBuf`, `_limit = len` (104); then `_len = len` (39), the saved registers back, and a tail jump (61) to
`wmemcpy (_chars, s, len + 1)`. `push r13; push r12; push rbp; push rbx; sub rsp, 8`, `r12` = `s`, `rbp` = `this`,
`rbx` = `len`, `r13` = `_chars` (or `newBuf`).

`operator new`, `operator delete []` and `wmemcpy` are hypotheses, as in `FV7z/Uau/Holds.lean`: a continuation at
each entry (`kn`, `kd`; `kmA`, `km0`, `km1` at `wmemcpy`'s entry after each of the three ways to 39, `Kt`), given
the run from the return and the callee's own post (`Pn`, `Pd`), which keeps the saved registers (`S4`).

- `bl`: `SysStringLen (s)`; `g28`: the registers back from it; `gN`, `gA`: at the `call` of `operator new` and at
  39 without it; `W23`: the bytes at `SysStringLen`'s entry (the pushes and the return address).
- `S4`: the saved `rbx`, `rbp`, `r12`, `r13` in the bytes; `s4_st`: kept by a store apart from them.
- `gT`: the registers at `wmemcpy`'s entry; `Kt`: the continuation there.
- `vc_0`, `vc_28`, `vc_39`, `vc_87`, `vc_104`: the verification conditions of the pieces.
- `usb_ok`: from the entry, through the callees, to `wmemcpy`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Usb
open FV7z.Uau (zl VB VL V0 tlm rq_self)

/-- The `call`s to `SysStringLen`, `operator new` and the thunk of `operator delete []`. -/
def pcs : List Byte := [0xe8, 0xc4, 0x28, 0x15, 0x00]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 1386692] 5) := by dec_rfl
theorem wc_23 : pcs <+: usb.drop 23 := by decide +kernel
theorem call_23 (feat : Features) : Dec feat usb 23 (FV7z.mk .call 64 [.rel 1386692] 5) :=
  Dec.shift (j := 23) (k := 0) (pcs_0 feat) wc_23 (Nat.zero_le _)
theorem tgt_23 : usb_at.add (23 + 5) + BitVec.ofNat 64 1386692 = Ssl.ssl_at.add 0 := by decide
def pcn : List Byte := [0xe8, 0x39, 0x51, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1790265] 5) := by dec_rfl
theorem wc_82 : pcn <+: usb.drop 82 := by decide +kernel
theorem call_82 (feat : Features) : Dec feat usb 82 (FV7z.mk .call 64 [.rel 1790265] 5) :=
  Dec.shift (j := 82) (k := 0) (pcn_0 feat) wc_82 (Nat.zero_le _)
theorem tgt_82 : usb_at.add (82 + 5) + BitVec.ofNat 64 1790265 = Onw.onw_at.add 64 := by decide
def pcd : List Byte := [0xe8, 0x68, 0x3c, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1784936] 5) := by dec_rfl
theorem wc_99 : pcd <+: usb.drop 99 := by decide +kernel
theorem call_99 (feat : Features) : Dec feat usb 99 (FV7z.mk .call 64 [.rel 1784936] 5) :=
  Dec.shift (j := 99) (k := 0) (pcd_0 feat) wc_99 (Nat.zero_le _)

/-- The tail jump to `wmemcpy`. -/
def pjw : List Byte := [0xe9, 0x9e, 0xfa, 0x20, 0x00]
theorem pjw_0 : ∀ feat, Dec feat pjw 0 (FV7z.mk .jmp 64 [.rel 2161310] 5) := by dec_rfl
theorem wj_61 : pjw <+: usb.drop 61 := by decide +kernel
theorem jmp_61 (feat : Features) : Dec feat usb 61 (FV7z.mk .jmp 64 [.rel 2161310] 5) :=
  Dec.shift (j := 61) (k := 0) (pjw_0 feat) wj_61 (Nat.zero_le _)

/-! ## Registers and bytes -/

/-- `SysStringLen (s)`: 0 for a null `s`, else the length stored before it. -/
def bl (V : Addr → Byte) (s : Addr) : BitVec 32 := if s = 0 then 0 else Ssl.sLen V s

/-- The registers after `sub rsp, 8`: `r12` = `s`, `rbp` = `this`, `rdi` = `s`, 40 below the entry. -/
abbrev g0 (g : Gprs) : Gprs := { g with r12 := g.rsi, rbp := g.rdi, rdi := g.rsi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }

/-- The registers back from `SysStringLen`: `rax` = `len`. -/
abbrev g28 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with r12 := g.rsi, rbp := g.rdi, rdi := g.rsi, rax := zl (bl V g.rsi), rsp := g.rsp - 40 }

/-- The registers at the `call` of `operator new`: `rbx` = `rax` = `len`, `rdi` = `4 len + 4`. -/
abbrev gN (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g28 g V with rbx := zl (bl V g.rsi), rdi := zl (bl V g.rsi) * 4#64 + 4#64 }

/-- The registers at 39 without `operator new`: `rbx` = `len`, `r13` = `_chars`. -/
abbrev gA (g : Gprs) (V : Addr → Byte) : Gprs := { g28 g V with rbx := zl (bl V g.rsi), r13 := rdq(V, g.rdi) }

/-- The bytes at `SysStringLen`'s entry: the pushes and the return address. -/
abbrev W23 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (V0 V g) (g.rsp - 48) (toBytesLE (usb_at.add (23 + 5)) 8)

/-- The saved `rbx`, `rbp`, `r12`, `r13` (the entry's `x`) in the bytes `V`. -/
abbrev S4 (V : Addr → Byte) (x : Gprs) : Prop :=
  rdq(V, x.rsp - 32) = x.rbx ∧ rdq(V, x.rsp - 24) = x.rbp ∧ rdq(V, x.rsp - 16) = x.r12 ∧ rdq(V, x.rsp - 8) = x.r13

/-- The registers at `wmemcpy`'s entry from those `g` at 39 (`x` the entry's, `l` = `len`): `rdi` = `_chars`,
`rsi` = `s`, `edx` = `len + 1`, the saved ones back, `rsp` the entry's. -/
abbrev gT (g x : Gprs) (l : BitVec 32) : Gprs :=
  { g with rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (zl l + 1#64)), rsi := x.rsi, rdi := g.r13, rbx := x.rbx,
           rbp := x.rbp, r12 := x.r12, r13 := x.r13, rsp := x.rsp }

/-- A quad word apart from a store. -/
theorem rq_st (W : Addr → Byte) (a y : Addr) (bs : List Byte) (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hy : y.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ y.toNat ∨ y.toNat + 8 ≤ a.toNat) :
    rdq(Vst W a bs, y) = rdq(W, y) :=
  congrArg (ofBytesLE 64) (Tun.rd_Vst W a bs y 8 ha hy h)

/-- The saved registers kept by a store apart from them. -/
theorem s4_st {W : Addr → Byte} {x : Gprs} {a : Addr} {bs : List Byte} (hp : 32 ≤ x.rsp.toNat)
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (hd : a.toNat + bs.length ≤ x.rsp.toNat - 32 ∨ x.rsp.toNat ≤ a.toNat)
    (h : S4 W x) : S4 (Vst W a bs) x := by
  have hlt := x.rsp.isLt
  have t8 : (x.rsp - 8).toNat = x.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t16 : (x.rsp - 16).toNat = x.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t24 : (x.rsp - 24).toNat = x.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t32 : (x.rsp - 32).toNat = x.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(rq_st W a _ bs ha (by rw [t32]; omega) (by rw [t32]; omega)).trans h1,
    (rq_st W a _ bs ha (by rw [t24]; omega) (by rw [t24]; omega)).trans h2,
    (rq_st W a _ bs ha (by rw [t16]; omega) (by rw [t16]; omega)).trans h3,
    (rq_st W a _ bs ha (by rw [t8]; omega) (by rw [t8]; omega)).trans h4⟩

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push r13; push r12; mov r12, rsi; push rbp; mov rbp, rdi; mov rdi, rsi; push rbx; sub rsp, 8` to the `call`
at 23. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h : ∀ fl, Q 23 (g0 g) fl (V0 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `SysStringLen`: `mov ebx, eax; cmp [rbp + 12], eax; jb`: if `_limit < len`, `mov eax, eax;
lea rdi, [rax * 4 + 4]` to the `call` at 82, else `mov r13, [rbp]` to 39. -/
theorem vc_28 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64} {l m : BitVec 32}
    (hax : g.rax = zl l) (hbp : g.rbp = p) (hm : rdd(V, p + 12#64) = m) (hq : rdq(V, p) = q)
    (f12 : ∀ i < 4, Foot F.data (Addr.add (p + 12#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h82 : m.toNat < l.toNat → ∀ fl, Q 82 { g with rbx := zl l, rax := zl l, rdi := zl l * 4#64 + 4#64 } fl V)
    (h39 : ¬ m.toNat < l.toNat → ∀ fl, Q 39 { g with rbx := zl l, r13 := q } fl V) :
    W_28 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hbp hm hq f12 f0 h82 h39 ⊢
  subst hax hbp
  by_cases hc : m.toNat < l.toNat
  · have hb : decide (m.toNat < l.toNat) = true := decide_eq_true hc
    wpx [W_28, W_72, W_35, o1, o4, o2, Op.cmpmr, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h82 hc _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : decide (m.toNat < l.toNat) = false := decide_eq_false hc
    wpx [W_28, W_72, W_35, o1, o4, o2, Op.cmpmr, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h39 hc _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [rbp + 8], ebx; add rsp, 8; lea edx, [rbx + 1]; mov rsi, r12; pop rbx; mov rdi, r13; pop rbp; pop r12;
pop r13` to the tail jump at 61. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : BitVec 64} {l : BitVec 32}
    (hbp : g.rbp = p) (hbx : g.rbx = zl l) (w8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 61
      { g with
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (zl l + 1#64)),
          rsi := g.r12,
          rdi := g.r13,
          rbx := rdq(VL V p l, g.rsp + 8#64),
          rbp := rdq(VL V p l, g.rsp + 8#64 + 8),
          r12 := rdq(VL V p l, g.rsp + 8#64 + 8 + 8),
          r13 := rdq(VL V p l, g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl (VL V p l)) :
    W_39 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp hbx w8 hl0 hl1 hl2 hl3 h ⊢
  subst hbp hbx
  wpx [W_39, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new`: `mov rdi, [rbp]; mov r13, rax; test rdi, rdi; je 104`, else to the `call` at 99. -/
theorem vc_87 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbp : g.rbp = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h104 : rdq(V, p) = 0 → ∀ fl, Q 104 { g with rdi := rdq(V, p), r13 := g.rax } fl V)
    (h99 : rdq(V, p) ≠ 0 → ∀ fl, Q 99 { g with rdi := rdq(V, p), r13 := g.rax } fl V) :
    W_87 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp f0 h104 h99 ⊢
  subst hbp
  by_cases h1 : rdq(V, rbp) = 0
  · have hb : (rdq(V, rbp) == 0) = true := beq_iff_eq.2 h1
    wpx [W_87, o5, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h104 h1 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (rdq(V, rbp) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_87, o5, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h99 h1 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [rbp], r13; mov [rbp + 12], ebx` and the jump to 39. -/
theorem vc_104 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64} {l : BitVec 32}
    (hbp : g.rbp = p) (h13 : g.r13 = q) (hbx : g.rbx = zl l) (w0 : ∀ i < 8, Foot Wl (Addr.add p i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (p + 12#64) i)) (h : ∀ fl, Q 39 g fl (VB V p q l)) :
    W_104 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp h13 hbx w0 w12 h ⊢
  subst hbp h13 hbx
  wpx [W_104, o6]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- At `wmemcpy`'s entry from 39 with the registers `g` and the bytes `W` there (`x` the entry's registers, `l` =
`len`): the registers `gT`, the bytes `VL` (`_len = len`). -/
def Kt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (Wl : List Rgn) (F : Footprint)
    (s₀ : State) (x : Gprs) (l : BitVec 32) (g : Gprs) (W : Addr → Byte) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (VL W x.rdi l) → Y.cpu.rip = Wmc.wmc_at →
    Y.cpu.gpr = gT g x l → GoG prof L o gev gP gE Y t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::SetFromBstr (s)` (`this` = `rdi`, `s` = `rsi`) from its entry, through `SysStringLen`. If `_limit <
len`, at `operator new`'s entry with the registers `gN` (`kn`); back at `usb_at + 87` (`Pn`), at the thunk of
`operator delete []` with `rdi` = `_chars` unless null (`kd`), back at `usb_at + 104` (`Pd`); then, and also without
`operator new`, at `wmemcpy`'s entry (`kmA`, `km0`, `km1`: `Kt`) by the tail jump. -/
theorem usb_ok {Pn : State → (Addr → Byte) → Prop} {Pd : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L usb_at usb) (hinS : CodeIn L Ssl.ssl_at Ssl.ssl)
    (hinN : CodeIn L Onw.onw_at Onw.onw) (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte}
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = usb_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fa : X.cpu.gpr.rsi ≠ 0 → ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 18446744073709551612#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hsd : X.cpu.gpr.rsi ≠ 0 → (X.cpu.gpr.rsi + 18446744073709551612#64).toNat + 4 ≤ 2 ^ 64 ∧
      ((X.cpu.gpr.rsi + 18446744073709551612#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 48 ∨
        X.cpu.gpr.rsp.toNat ≤ (X.cpu.gpr.rsi + 18446744073709551612#64).toNat))
    (kn : ∀ (Y : State) (t' : Nat), (tlm V X.cpu.gpr).toNat < (bl V X.cpu.gpr.rsi).toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (W23 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add 87) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gN X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = usb_at.add 87 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zn.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbx = zl (bl V X.cpu.gpr.rsi) → Zn.cpu.gpr.r12 = X.cpu.gpr.rsi → S4 V₁ X.cpu.gpr →
        Pn Zn V₁ → GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add 104) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = usb_at.add 104 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = zl (bl V X.cpu.gpr.rsi) → Zd.cpu.gpr.r12 = X.cpu.gpr.rsi →
        Zd.cpu.gpr.r13 = Zn.cpu.gpr.rax → S4 V₃ X.cpu.gpr → Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : ¬ (tlm V X.cpu.gpr).toNat < (bl V X.cpu.gpr.rsi).toNat →
      Kt prof L o gev gP gE Wl F s₀ X.cpu.gpr (bl V X.cpu.gpr.rsi) (gA X.cpu.gpr V) (W23 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kt prof L o gev gP gE Wl F s₀ X.cpu.gpr (bl V X.cpu.gpr.rsi)
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (bl V X.cpu.gpr.rsi)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kt prof L o gev gP gE Wl F s₀ X.cpu.gpr (bl V X.cpu.gpr.rsi) Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (bl V X.cpu.gpr.rsi))) :
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
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have c40 : X.cpu.gpr.rsp - 48 + 8 = X.cpu.gpr.rsp - 40 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn48, tn40]
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
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have td8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have td12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- from 39 to `wmemcpy`'s entry
  have run39 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = usb_at.add 39 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.rbp = X.cpu.gpr.rdi → g.rbx = zl (bl V X.cpu.gpr.rsi) → g.r12 = X.cpu.gpr.rsi → S4 W X.cpu.gpr →
      Kt prof L o gev gP gE Wl F s₀ X.cpu.gpr (bl V X.cpu.gpr.rsi) g W →
      GoG prof L o gev gP gE U t' := by
    intro U g W t' hKU hAU hrU hgU hs hbp hbx h12 hS k
    subst hgU
    obtain ⟨b1, b2, b3, b4⟩ := s4_st (W := W) (a := X.cpu.gpr.rdi + 8#64)
      (bs := toBytesLE (bl V X.cpu.gpr.rsi) 4) (by omega) (by rw [toBytesLE_length, td8]; omega)
      (by rw [toBytesLE_length, td8]; omega) hS
    refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 61 ∧
        g' = gT U.cpu.gpr X.cpu.gpr (bl V X.cpu.gpr.rsi) ∧ V' = VL W X.cpu.gpr.rdi (bl V X.cpu.gpr.rsi))
      hKU hAU hrU
      (vc_39 hbp hbx fw8 (by rw [hs, a32]; exact h32) (by rw [hs, a32, a24]; exact h24)
        (by rw [hs, a32, a24, a16]; exact h16) (by rw [hs, a32, a24, a16, a8]; exact h8)
        fun _ => ⟨rfl, by rw [hs, a32, a24, a16, a8, e8, h12, b1, b2, b3, b4], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ Y t₄ hKY hAY hrY hgY -
    subst V₄
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_61 _) hinW (Wmc.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])
  -- from 104 (`_chars = newBuf; _limit = len`) to 39
  have run104 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (q : BitVec 64) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = usb_at.add 104 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.rbp = X.cpu.gpr.rdi → g.rbx = zl (bl V X.cpu.gpr.rsi) → g.r12 = X.cpu.gpr.rsi → g.r13 = q →
      S4 W X.cpu.gpr →
      Kt prof L o gev gP gE Wl F s₀ X.cpu.gpr (bl V X.cpu.gpr.rsi) g
        (VB W X.cpu.gpr.rdi q (bl V X.cpu.gpr.rsi)) →
      GoG prof L o gev gP gE U t' := by
    intro U g W q t' hKU hAU hrU hgU hs hbp hbx h12 h13 hS k
    subst hgU
    have hS' : S4 (VB W X.cpu.gpr.rdi q (bl V X.cpu.gpr.rsi)) X.cpu.gpr :=
      s4_st (by omega) (by rw [toBytesLE_length, td12]; omega) (by rw [toBytesLE_length, td12]; omega)
        (s4_st (by omega) (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega) hS)
    refine (c_104 prof).run c hin (fun j' g' _ V' => j' = 39 ∧ g' = U.cpu.gpr ∧
        V' = VB W X.cpu.gpr.rdi q (bl V X.cpu.gpr.rsi)) hKU hAU hrU
      (vc_104 hbp h13 hbx fw0 fw12 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    exact run39 U' U.cpu.gpr _ t₄ hKU' hAU' hrU' hgU' hs hbp hbx h12 hS' k
  -- the bytes at `SysStringLen`'s entry: the loads there, the length, the saved registers
  have hm23 : rdd(W23 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = tlm V X.cpu.gpr :=
    congrArg (ofBytesLE 32) ((Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add (23 + 5)) 8)
      (X.cpu.gpr.rdi + 12#64) 4 (by rw [toBytesLE_length, tn48]; omega)
      (by rw [td12]; omega) (by rw [toBytesLE_length, tn48, td12]; omega)).trans
      (Uau.m0 (V := V) (g := X.cpu.gpr) (by omega) _ 4 (by rw [td12]; omega) (by rw [td12]; omega)))
  have hq23 : rdq(W23 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) :=
    congrArg (ofBytesLE 64) ((Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add (23 + 5)) 8)
      X.cpu.gpr.rdi 8 (by rw [toBytesLE_length, tn48]; omega)
      (by omega) (by rw [toBytesLE_length, tn48]; omega)).trans
      (Uau.m0 (V := V) (g := X.cpu.gpr) (by omega) _ 8 (by omega) (by omega)))
  have hsl : X.cpu.gpr.rsi ≠ 0 → Ssl.sLen (W23 V X.cpu.gpr) X.cpu.gpr.rsi = Ssl.sLen V X.cpu.gpr.rsi := by
    intro h0
    obtain ⟨b1, b2⟩ := hsd h0
    have e1 := Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add (23 + 5)) 8)
      (X.cpu.gpr.rsi + 18446744073709551612#64) 4 (by rw [toBytesLE_length, tn48]; omega) b1
      (by rw [toBytesLE_length, tn48]; omega)
    have e2 := Uau.m0 (V := V) (g := X.cpu.gpr) (by omega) (X.cpu.gpr.rsi + 18446744073709551612#64) 4 b1
      (by omega)
    show ofBytesLE 32 (List.map (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usb_at.add (23 + 5)) 8))
        (byteAddrs (X.cpu.gpr.rsi + 18446744073709551612#64) 4)) >>> 2 =
      ofBytesLE 32 (List.map V (byteAddrs (X.cpu.gpr.rsi + 18446744073709551612#64) 4)) >>> 2
    rw [e1, e2]
  have hif : (if X.cpu.gpr.rsi = 0 then (0 : BitVec 64)
      else (Ssl.sLen (W23 V X.cpu.gpr) X.cpu.gpr.rsi).setWidth 64) = zl (bl V X.cpu.gpr.rsi) := by
    by_cases h0 : X.cpu.gpr.rsi = 0
    · unfold bl
      rw [if_pos h0, if_pos h0]
      try (first | rfl | decide)
    · unfold bl
      rw [if_neg h0, if_neg h0, hsl h0]
  have hS23 : S4 (W23 V X.cpu.gpr) X.cpu.gpr := by
    obtain ⟨b1, b2, b3, b4, -⟩ := Uau.sv0 (V := V) (g := X.cpu.gpr) (r := rdq(V, X.cpu.gpr.rsp)) (by omega) hp8 rfl
    exact s4_st (by omega) (by rw [toBytesLE_length, tn48]; omega) (by rw [toBytesLE_length, tn48]; omega)
      ⟨b1, b2, b3, b4⟩
  have hrip' : X.cpu.rip = usb_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the pushes, to the `call` of `SysStringLen` at 23
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 23 ∧ g' = g0 X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
      fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_23 _) hinS (tgt := 0) (Ssl.lt_len (by decide))
    tgt_23 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c48] at hA₂
  have hA₂' : Agree F Y₂.proc.mm.mem (W23 V X.cpu.gpr) := hA₂
  have hdi2 : Y₂.cpu.gpr.rdi = X.cpu.gpr.rsi := by rw [hg₂, hgY]; try rfl
  have hs2' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 48 := by rw [hg₂, hsY, c48]; try rfl
  -- `SysStringLen (s)`
  refine Ssl.ssl_ok (j₂ := 28) c hinS hK₂ hA₂' (by rw [hr₂, addr_add_zero]) (by rw [hdi2]; exact fa)
    (by rw [hs2']; exact fun i hi => c.hws _ (hs6 i hi)) hin (lt_len (by decide))
    (by rw [hs2']; exact rq_self _ _ _ (by rw [tn48]; omega)) ?_
  intro Z t₃ hKZ hAZ hrZ hgZ
  rw [hdi2, hs2', hif, c40, hg₂, hgY] at hgZ
  have hgZ' : Z.cpu.gpr = g28 X.cpu.gpr V := hgZ.trans rfl
  -- `cmp [rbp + 12], eax; jb`: on to 82 or 39
  refine (c_28 prof).run c hin (fun j' g' _ V' => V' = W23 V X.cpu.gpr ∧
      ((j' = 82 ∧ (tlm V X.cpu.gpr).toNat < (bl V X.cpu.gpr.rsi).toNat ∧ g' = gN X.cpu.gpr V) ∨
       (j' = 39 ∧ ¬ (tlm V X.cpu.gpr).toNat < (bl V X.cpu.gpr.rsi).toNat ∧ g' = gA X.cpu.gpr V)))
    hKZ hAZ hrZ
    (by
      rw [hgZ']
      exact vc_28 rfl rfl hm23 hq23 fd12 fd0 (fun hc _ => ⟨rfl, .inl ⟨rfl, hc, rfl⟩⟩)
        (fun hc _ => ⟨rfl, .inr ⟨rfl, hc, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, hc, rfl⟩ | ⟨rfl, hc, rfl⟩
  · -- `new wchar_t[len + 1]`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_82 _) hinN (tgt := 64) (Onw.lt_len (by decide))
      tgt_82 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine kn Y₂ t₂ hc hK₂ hA₂ hr₂ (by rw [hg₂, hsY, c48, hgY]) ?_
    -- back from `operator new`
    intro Zn V₁ t₃ hKn hAn hrn hns hnbp hnbx hn12 hS1 hPn
    refine (c_87 prof).run c hin (fun j' g' _ V' => V' = V₁ ∧
        g' = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax } ∧
        ((j' = 104 ∧ rdq(V₁, X.cpu.gpr.rdi) = 0) ∨ (j' = 99 ∧ rdq(V₁, X.cpu.gpr.rdi) ≠ 0))) hKn hAn hrn
      (vc_87 hnbp fd0 (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
    rintro j' g fl V₂ ⟨hV₂, rfl, h⟩ U t₄ hKU hAU hrU hgU -
    subst V₂
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- a null `_chars`: no `delete []`
      exact run104 U _ V₁ Zn.cpu.gpr.rax t₄ hKU hAU hrU hgU hns hnbp hnbx hn12 rfl hS1 (km0 Zn V₁ hPn h0)
    · -- `delete [] _chars`
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgU]; exact hns
      have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c48]; exact hs6
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_99 _) hinD hD (by decide) hst5 ?_
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hsU, c48] at hA₅
      refine kd Zn V₁ hPn h0 Y₅ t₅ hK₅ hA₅ hr₅ (by rw [hg₅, hsU, c48, hgU]) ?_
      intro Zd V₃ t₆ hKd hAd hrd hds' hdbp hdbx hd12 hd13 hS3 hPd
      exact run104 Zd Zd.cpu.gpr V₃ Zn.cpu.gpr.rax t₆ hKd hAd hrd rfl hds' hdbp hdbx hd12 hd13 hS3
        (km1 Zn Zd V₃ hPd)
  · -- `_limit ≥ len`: the buffer as it is
    exact run39 Y (gA X.cpu.gpr V) (W23 V X.cpu.gpr) t₁ hKY hAY hrY hgY rfl rfl rfl rfl hS23 (kmA hc)

end FV7z.Usb
