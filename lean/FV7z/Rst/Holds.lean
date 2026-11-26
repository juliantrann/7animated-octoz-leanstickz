import FV7z.Rst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.AddMr64
import FV7z.Tun.Inv
/-!
# `ReadStream` (PLAN.md §M, M1)

7-Zip 26.06's `ReadStream (stream, data, size)` at `0x4632b0` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`;
`objdump -d`), `S` the stack pointer at the entry: six pushes (`r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`, `P6`), a
frame of 24 bytes (`aR S` = `S - 72`); `rbx` = `*size` (read after the pushes), the stack guard (`fs:0x28`) stored at
`aR S + 8`, `*size` = 0 (`Vp`); `processed` (4 bytes) at `aR S + 4`. `*size` 0: `eax` = 0 (168) and on to the
epilogue (131). Else `r15` = `stream`, `r13` = `data`, `r14` = `size`, `rbp` = `0x80000000`, `r12` = `&processed`
(`gL`) and the loop from 89: `rax` = the vtable (the 8 bytes at `stream`), `edx` = `min (rbx, rbp)` (`cmp`, `cmovb`,
`sz`), `call qword [rax + 24]` (111, `Seg.s_callM`, registers `gC`), back at 114: `edx` = `processed` (`pd`),
`*size += rdx` (118, `Seg.s_add_mr64`, the bytes `Va`), `data` and the size left moved by it (`g121`); the answer not
0 or `processed` 0: returned (131); the size left 0: `eax` 0 (168); else again from 89. The epilogue (131): the stack
guard checked, the frame dropped, the six pops, the `ret` (161).

- `rst_entry`: from the entry to 131 (`*size` 0, `k0`) or to the loop's head 89 (`k1`);
- `rst_call`: from 89 to the callee's entry, the return address `rst_at + 114` below `rsp`;
- `rst_back`: from 114 to 131 (`k131`, `rax` as `R121` says) or to 89 (`k89`), `*size` moved (`Va`);
- `rst_tail`: from 131 to the return address (at `rsp + 72`), the pops read back.

Not covered: the stack guard failing (`__stack_chk_fail`, 172).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rst

/-- The `call` through the vtable. -/
def pcall : List Byte := [0xff, 0x50, 0x18]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) := by intro feat f; rfl
theorem wc_111 : pcall <+: rst.drop 111 := by decide +kernel
theorem call_111 (feat : Features) : Dec feat rst 111 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 111) (k := 0) (pcall_0 feat) wc_111 (Nat.zero_le _)

/-- `add qword [r14], rdx`. -/
def padd : List Byte := [0x49, 0x01, 0x16]
theorem padd_0 : ∀ feat, Dec feat padd 0 (FV7z.mk .add 64 [.mem (mbd 14 0 64), gr 64 2] 3) := by intro feat f; rfl
theorem wa_118 : padd <+: rst.drop 118 := by decide +kernel
theorem add_118 (feat : Features) : Dec feat rst 118 (FV7z.mk .add 64 [.mem (mbd 14 0 64), gr 64 2] 3) :=
  Dec.shift (j := 118) (k := 0) (padd_0 feat) wa_118 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_161 : pret <+: rst.drop 161 := by decide +kernel
theorem ret_161 (feat : Features) : Dec feat rst 161 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 161) (k := 0) (pret_0 feat) w_161 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 24`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64

/-- The bytes after the six `push`es. -/
abbrev P6 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- `*size`, read after the pushes. -/
abbrev n0 (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(P6 V g, g.rdx)

/-- The bytes after the prologue: the stack guard `cn` stored at `aR S + 8`, then `*size` = 0. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vst (P6 V g) (aR g.rsp + 8#64) (toBytesLE cn 8)) g.rdx (toBytesLE 0#64 8)

/-- At the loop's head (89) from the entry: `rax` 0, `rbx` = `*size` as it was, `rbp` = `0x80000000`, `r12` =
`&processed`, `r13` = `data`, `r14` = `size`, `r15` = `stream`. -/
abbrev gL (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := 0#64
    rbx := n0 V g
    rsp := aR g.rsp
    rbp := 2147483648#64
    r12 := aR g.rsp + 4#64
    r13 := g.rsi
    r14 := g.rdx
    r15 := g.rdi }

/-- The size of one call: `rbx` capped by `rbp` (`cmp rbx, rbp; cmovb rdx, rbx`). -/
abbrev sz (g : Gprs) : BitVec 64 := if g.rbx.toNat < g.rbp.toNat then g.rbx else g.rbp

/-- At the `call` (111): `rax` the vtable, `rcx` = `&processed`, `rdx` the size, `rsi` = `data`, `rdi` = `stream`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V, g.r15), rcx := g.r12, rdx := sz g, rsi := g.r13, rdi := g.r15 }

/-- `processed`, read at 114. -/
abbrev pd (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rsp + 4#64)

/-- The bytes after `*size += processed` (118). -/
abbrev Va (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V g.r14 (toBytesLE (rdq(V, g.r14) + (pd V g).setWidth 64) 8)

/-- After 121's block: `data` (`r13`) and the size left (`rbx`) moved by `rdx`. -/
abbrev gA (g : Gprs) : Gprs := { g with rbx := g.rbx - g.rdx, r13 := g.r13 + g.rdx }

/-- At 121's block's end from 114: `rdx` = `processed`. -/
abbrev g121 (V : Addr → Byte) (g : Gprs) : Gprs := gA { g with rdx := (pd V g).setWidth 64 }

/-- `rax` at 131 from 114: the callee's answer when its low half is not 0 or `processed` is 0; 0 when the size is
left 0. -/
def R121 (V : Addr → Byte) (g : Gprs) (r : BitVec 64) : Prop :=
  (g.rax.setWidth 32 ≠ 0#32 ∧ r = g.rax) ∨
  (g.rax.setWidth 32 = 0#32 ∧ pd V g = 0#32 ∧ r = g.rax) ∨
  (g.rax.setWidth 32 = 0#32 ∧ pd V g ≠ 0#32 ∧ g.rbx - (pd V g).setWidth 64 = 0#64 ∧ r = 0#64)

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem s31 : BitVec.setWidth 64 2147483648#32 = 2147483648#64 := by decide
theorem a32 (x : Addr) : x + 24#64 + 8 = x + 32#64 := by bv_omega
theorem a40 (x : Addr) : x + 32#64 + 8 = x + 40#64 := by bv_omega
theorem a48 (x : Addr) : x + 40#64 + 8 = x + 48#64 := by bv_omega
theorem a56 (x : Addr) : x + 48#64 + 8 = x + 56#64 := by bv_omega
theorem a64 (x : Addr) : x + 56#64 + 8 = x + 64#64 := by bv_omega
theorem a72 (x : Addr) : x + 64#64 + 8 = x + 72#64 := by bv_omega
theorem a80 (x : Addr) : x + 72#64 + 8 = x + 80#64 := by bv_omega

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry, `*size` 0: the prologue, `eax` 0, to 168. -/
theorem vc_0z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn n : BitVec 64}
    (hn : rdq(P6 V g, g.rdx) = n) (hz : n = 0#64) (hcn : rdq(P6 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (fd : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (wd : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 168 ∧ g' = { g with rax := 0#64, rbx := n, rsp := aR g.rsp } ∧
      V' = Vp V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, P6, aR] at hn hcn w1 w2 w3 w4 w5 w6 fd wd wc ⊢
  have e : (n == 0) = true := beq_iff_eq.2 hz
  wpx [W_0, W_49, o0, o1, Op.ldf, Op.sti, hn, hcn, xz, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From the entry, `*size` not 0: the prologue, the loop's registers `gL`, to 89. -/
theorem vc_0n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64} (hz : n0 V g ≠ 0#64)
    (hcn : rdq(P6 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (fd : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (wd : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 89 ∧ g' = gL V g ∧ V' = Vp V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, P6, aR, gL, n0] at hz hcn w1 w2 w3 w4 w5 w6 fd wd wc ⊢
  have e : (rdq(Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
      (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
      (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8), rdx) == 0) =
      false := beq_eq_false_iff_ne.2 hz
  wpx [W_0, W_49, o0, o1, Op.ldf, Op.sti, hcn, xz, s31, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- 168: `eax` 0, to 131. -/
theorem vc_168 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_168 fb F Wl (fun j' g' _ V' => j' = 131 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_168, o9, xz]
  all_goals vfin

/-- From 89: the vtable, the size, the arguments, to the `call` (111). -/
theorem vc_89 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fr : ∀ i < 8, Foot F.data (Addr.add g.r15 i)) :
    W_89 fb F Wl (fun j' g' _ V' => j' = 111 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, sz] at fr ⊢
  by_cases hcf : rbx.toNat < rbp.toNat
  · have hd : decide (rbx.toNat < rbp.toNat) = true := decide_eq_true hcf
    wpx [W_89, o4, hd, hcf, decide_true, ↓reduceIte, eq_self_iff_true]
    all_goals vfin
  · have hd : decide (rbx.toNat < rbp.toNat) = false := decide_eq_false hcf
    wpx [W_89, o4, hd, hcf, decide_false, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true]
    all_goals vfin

/-- 114: `edx` = `processed`, to the `add` (118). -/
theorem vc_114 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_114 fb F Wl (fun j' g' _ V' => j' = 118 ∧ g' = { g with rdx := (pd V g).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pd] at f4 ⊢
  wpx [W_114, o5]
  all_goals vfin

/-- From 121, the callee's answer not 0: to 131. -/
theorem vc_121a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 ≠ 0#32) :
    W_121 fb F Wl (fun j' g' _ V' => j' = 131 ∧ g' = gA g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gA] at ha ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 ha
  wpx [W_121, W_80, W_84, o6, o2, o3, e, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 121, the answer 0 and `processed` 0: to 131. -/
theorem vc_121b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : g.rdx.setWidth 32 = 0#32) :
    W_121 fb F Wl (fun j' g' _ V' => j' = 131 ∧ g' = gA g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gA] at ha hp ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (BitVec.setWidth 32 rdx == 0) = true := beq_iff_eq.2 hp
  wpx [W_121, W_80, W_84, o6, o2, o3, e, e2, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 121, the answer 0, `processed` not 0, the size left 0: to 168. -/
theorem vc_121c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : g.rdx.setWidth 32 ≠ 0#32) (hb : g.rbx - g.rdx = 0#64) :
    W_121 fb F Wl (fun j' g' _ V' => j' = 168 ∧ g' = gA g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gA] at ha hp hb ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (BitVec.setWidth 32 rdx == 0) = false := beq_eq_false_iff_ne.2 hp
  have e3 : (rbx - rdx == 0) = true := beq_iff_eq.2 hb
  wpx [W_121, W_80, W_84, o6, o2, o3, e, e2, e3, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 121, the answer 0, `processed` not 0, the size not left 0: to 89. -/
theorem vc_121d {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : g.rdx.setWidth 32 ≠ 0#32) (hb : g.rbx - g.rdx ≠ 0#64) :
    W_121 fb F Wl (fun j' g' _ V' => j' = 89 ∧ g' = gA g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gA] at ha hp hb ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (BitVec.setWidth 32 rdx == 0) = false := beq_eq_false_iff_ne.2 hp
  have e3 : (rbx - rdx == 0) = false := beq_eq_false_iff_ne.2 hb
  wpx [W_121, W_80, W_84, o6, o2, o3, e, e2, e3, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 131: the stack guard checked, the frame dropped, the six pops, to the `ret` (161). -/
theorem vc_131 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (p6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_131 fb F Wl (fun j' g' _ V' => j' = 161 ∧
      (∃ rs, g' = { g with
        rbx := rdq(V, g.rsp + 24#64)
        rbp := rdq(V, g.rsp + 24#64 + 8)
        rsi := rs
        r12 := rdq(V, g.rsp + 24#64 + 8 + 8)
        r13 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8)
        r14 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8)
        r15 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8)
        rsp := g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 p1 p2 p3 p4 p5 p6 ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_131, W_147, o7, o8, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `ReadStream (stream, data, size)` from its entry, the stack guard's 8 bytes at `fs:0x28` and `*size` readable,
the pushes' slots, the guard's slot and `*size` in what the run may store into: the prologue run (`Vp`, the guard and
`*size` as read after the pushes); `*size` 0: at 131 with `rax` 0 (`k0`); else at the loop's head 89 with the
registers `gL` (`k1`). -/
theorem rst_entry {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L rst_at rst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rst_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (wd : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (k0 : n0 V X.cpu.gpr = 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vp V X.cpu.gpr rdq(P6 V X.cpu.gpr, fb + 40#64)) → Y.cpu.rip = rst_at.add 131 →
      Y.cpu.gpr = { X.cpu.gpr with rax := 0#64, rbx := n0 V X.cpu.gpr, rsp := aR X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t')
    (k1 : n0 V X.cpu.gpr ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vp V X.cpu.gpr rdq(P6 V X.cpu.gpr, fb + 40#64)) → Y.cpu.rip = rst_at.add 89 →
      Y.cpu.gpr = gL V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have fd : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i) := fun i hi => c.hws _ (wd i hi)
  by_cases hz : n0 V X.cpu.gpr = 0#64
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0z rfl hz rfl w1 w2 w3 w4 w5 w6 fd wd hcl wc) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine (c_168 prof fb).run c hfs hin _ hKY hAY hrY (vc_168 (g := Y.cpu.gpr)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    exact k0 hz U t₂ hKU hAU hrU (by rw [hgU, hgY]; try rfl)
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0n hz rfl w1 w2 w3 w4 w5 w6 fd wd hcl wc) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k1 hz Y t₁ hKY hAY hrY hgY

/-- From the loop's head (89), `stream`'s 8 bytes (`r15`) and its vtable's at `+ 24` readable, the latter the
callee's entry `eR`, the return address's slot in what the run may store into: at `eR` with the registers `gC`, `rsp`
8 lower, the return address `rst_at + 114` stored below `rsp`. -/
theorem rst_call {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L rst_at rst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = rst_at.add 89) (fr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.r15 i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, X.cpu.gpr.r15) + 24#64) i))
    {eR : Addr} {codeR : List Byte} (hinR : CodeIn L eR codeR) (hR0 : 0 < codeR.length)
    (htgt : rdq(V, rdq(V, X.cpu.gpr.r15) + 24#64) = eR)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (rst_at.add 114) 8)) → Y.cpu.rip = eR →
      Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_89 prof fb).run c hfs hin _ hK hA hrip (vc_89 fr) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have he : eaD Y 0 24 = rdq(V, X.cpu.gpr.r15) + 24#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
    rw [hgY]
    rfl
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_111 _) (by rw [he]; exact fv) hinR hR0
    (by rw [he]; exact htgt) (by rw [hsY]; exact hst) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From the callee's return (114), `processed`'s 4 bytes (`rsp + 4`) readable, `*size`'s 8 (`r14`) in what the run
may store into: `*size` moved by `processed` (`Va`); at 131 with the registers `g121` and `rax` as `R121` says
(`k131`), or, the answer 0, `processed` not 0, the size not left 0, at the loop's head 89 with the registers `g121`
(`k89`). -/
theorem rst_back {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L rst_at rst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = rst_at.add 114) (f4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 4#64) i))
    (w14 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.r14 i))
    (k131 : ∀ (r : BitVec 64), R121 V X.cpu.gpr r → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Va V X.cpu.gpr) → Y.cpu.rip = rst_at.add 131 →
      Y.cpu.gpr = { g121 V X.cpu.gpr with rax := r } → GoG prof L o gev gP gE Y t')
    (k89 : X.cpu.gpr.rax.setWidth 32 = 0#32 → pd V X.cpu.gpr ≠ 0#32 →
      X.cpu.gpr.rbx - (pd V X.cpu.gpr).setWidth 64 ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Va V X.cpu.gpr) → Y.cpu.rip = rst_at.add 89 → Y.cpu.gpr = g121 V X.cpu.gpr →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_114 prof fb).run c hfs hin _ hK hA hrip (vc_114 f4) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have he : eaD Y 14 0 = X.cpu.gpr.r14 := by
    show Y.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 0 = _
    rw [hgY]
    exact BitVec.add_zero _
  have hv : rv Y 64 2 = (pd V X.cpu.gpr).setWidth 64 := by
    show (Y.cpu.gpr.get (regOf 2)).setWidth 64 = _
    rw [hgY]
    exact BitVec.setWidth_eq _
  refine c.s_add_mr64 hKY hAY hin (lt_len (by decide)) hrY (add_118 _) (by rw [he]; exact w14) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [he, hv] at hA₂
  have hr₂' : Y₂.cpu.rip = rst_at.add 121 := hr₂
  have hax : Y₂.cpu.gpr.rax = X.cpu.gpr.rax := by rw [hg₂, hgY]
  have hdx : Y₂.cpu.gpr.rdx = (pd V X.cpu.gpr).setWidth 64 := by rw [hg₂, hgY]
  have hbx : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [hg₂, hgY]
  have hgA : gA Y₂.cpu.gpr = g121 V X.cpu.gpr := by rw [hg₂, hgY]
  have hd32 : Y₂.cpu.gpr.rdx.setWidth 32 = pd V X.cpu.gpr := by rw [hdx]; exact sw_64_32 _
  by_cases ha : X.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases hp : pd V X.cpu.gpr = 0#32
    · refine (c_121 prof fb).run c hfs hin _ hK₂ hA₂ hr₂'
        (vc_121b (g := Y₂.cpu.gpr) (by rw [hax]; exact ha) (by rw [hd32]; exact hp)) ?_
      rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₃ hKU hAU hrU hgU -
      subst V₃
      exact k131 _ (Or.inr (Or.inl ⟨ha, hp, rfl⟩)) U t₃ hKU hAU hrU (by rw [hgU, hgA]; try rfl)
    · by_cases hb : X.cpu.gpr.rbx - (pd V X.cpu.gpr).setWidth 64 = 0#64
      · refine (c_121 prof fb).run c hfs hin _ hK₂ hA₂ hr₂'
          (vc_121c (g := Y₂.cpu.gpr) (by rw [hax]; exact ha) (by rw [hd32]; exact hp)
            (by rw [hbx, hdx]; exact hb)) ?_
        rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₃ hKU hAU hrU hgU -
        subst V₃
        refine (c_168 prof fb).run c hfs hin _ hKU hAU hrU (vc_168 (g := U.cpu.gpr)) ?_
        rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
        subst V₄
        exact k131 _ (Or.inr (Or.inr ⟨ha, hp, hb, rfl⟩)) U' t₄ hKU' hAU' hrU' (by rw [hgU', hgU, hgA])
      · refine (c_121 prof fb).run c hfs hin _ hK₂ hA₂ hr₂'
          (vc_121d (g := Y₂.cpu.gpr) (by rw [hax]; exact ha) (by rw [hd32]; exact hp)
            (by rw [hbx, hdx]; exact hb)) ?_
        rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₃ hKU hAU hrU hgU -
        subst V₃
        exact k89 ha hp hb U t₃ hKU hAU hrU (by rw [hgU, hgA])
  · refine (c_121 prof fb).run c hfs hin _ hK₂ hA₂ hr₂' (vc_121a (g := Y₂.cpu.gpr) (by rw [hax]; exact ha)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₃ hKU hAU hrU hgU -
    subst V₃
    exact k131 _ (Or.inl ⟨ha, rfl⟩) U t₃ hKU hAU hrU (by rw [hgU, hgA]; try rfl)

/-- From 131 to the return address (at `rsp + 72`), the stack guard at `rsp + 8` the one at `fs:0x28`: `rbx`, `rbp`,
`r12`, `r13`, `r14`, `r15` popped from `rsp + 24` … `rsp + 64`, `rsp` 80 above, `rsi` some value, the others as at
131. -/
theorem rst_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L rst_at rst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = rst_at.add 131) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 32#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 40#64) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 48#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 56#64) i))
    (f64 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 64#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 72#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 8#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 72#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ rs, Z.cpu.gpr = { X.cpu.gpr with
        rbx := rdq(V, X.cpu.gpr.rsp + 24#64)
        rbp := rdq(V, X.cpu.gpr.rsp + 32#64)
        rsi := rs
        r12 := rdq(V, X.cpu.gpr.rsp + 40#64)
        r13 := rdq(V, X.cpu.gpr.rsp + 48#64)
        r14 := rdq(V, X.cpu.gpr.rsp + 56#64)
        r15 := rdq(V, X.cpu.gpr.rsp + 64#64)
        rsp := X.cpu.gpr.rsp + 80#64 }) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_131 prof fb).run c hfs hin _ hK hA hrip
    (vc_131 (g := X.cpu.gpr) hc f8 hcl f24 (by rw [a32]; exact f32) (by rw [a32, a40]; exact f40)
      (by rw [a32, a40, a48]; exact f48) (by rw [a32, a40, a48, a56]; exact f56)
      (by rw [a32, a40, a48, a56, a64]; exact f64)) ?_
  rintro j' g fl V₃ ⟨rfl, ⟨rs, rfl⟩, rfl⟩ Y t₃ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 72#64 := by rw [hgY, a32, a40, a48, a56, a64, a72]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_161 _) (by rw [hsY]; exact f72) hin₂ h₂
    (by rw [hsY]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₄ hKZ hAZ hrZ ⟨rs, ?_⟩
  rw [hgZ]
  show Y.cpu.gpr.set 4 (Y.cpu.gpr.rsp + 8) = _
  rw [hsY, a80, hgY, a32, a40, a48, a56, a64, a72]
  try rfl

end FV7z.Rst
