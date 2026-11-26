import FV7z.Wst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `WriteStream` (PLAN.md §M, M1)

7-Zip 26.06's `WriteStream (stream, data, size)` at `0x463420` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`;
`objdump -d`), `S` the stack pointer at the entry: five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`, `P5`), a frame of
16 bytes (`aR S` = `S - 56`) with the stack guard (`fs:0x28`) at `aR S + 8` (`Vp`) and `processed` (4 bytes) at
`aR S + 4`. `size` 0: `eax` = 0 (144) and on to the epilogue (112). Else `r14` = `stream`, `rbp` = `data`, `rbx` =
`size`, `r12` = `0x80000000`, `r13` = `&processed` (`gL`) and the loop from 73: `rax` = the vtable (the 8 bytes at
`stream`), `edx` = `min (size, r12)` (`cmp`, `cmovb`, `sz`), `call qword [rax + 24]` (95, `Seg.s_callM`, registers
`gC`), back at 98: `data`, `size` moved by `processed` (`pd`, `g98`); the answer not 0 (returned), `processed` 0
(`E_FAIL` = `0x80004005` returned, 152), `size` 0 (`eax` 0, 144), else again from 73. The epilogue (112): the stack
guard checked, the frame dropped, the five pops, the `ret` (140).

- `wst_entry`: from the entry to 112 (`size` 0, `k0`) or to the loop's head 73 (`k1`);
- `wst_call`: from 73 to the callee's entry, the return address `wst_at + 98` below `rsp`;
- `wst_back`: from 98 to 112 (`k112`, `rax` as `R98` says) or to 73 (`k73`);
- `wst_tail`: from 112 to the return address (at `rsp + 56`), the pops read back.

Not covered: the stack guard failing (`__stack_chk_fail`, 159).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Wst

/-- The `call` through the vtable. -/
def pcall : List Byte := [0xff, 0x50, 0x18]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) := by intro feat f; rfl
theorem wc_95 : pcall <+: wst.drop 95 := by decide +kernel
theorem call_95 (feat : Features) : Dec feat wst 95 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 95) (k := 0) (pcall_0 feat) wc_95 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_140 : pret <+: wst.drop 140 := by decide +kernel
theorem ret_140 (feat : Features) : Dec feat wst 140 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 140) (k := 0) (pret_0 feat) w_140 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes and `sub rsp, 16`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 16#64

/-- The bytes after the five `push`es. -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the stack guard `cn` stored at `aR S + 8`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (P5 V g) (aR g.rsp + 8#64) (toBytesLE cn 8)

/-- At the loop's head (73) from the entry: `rax` 0, `rbx` = `size`, `rbp` = `data`, `r12` = `0x80000000`, `r13` =
`&processed`, `r14` = `stream`. -/
abbrev gL (g : Gprs) : Gprs :=
  { g with
    rax := 0#64
    rbx := g.rdx
    rsp := aR g.rsp
    rbp := g.rsi
    r12 := 2147483648#64
    r13 := aR g.rsp + 4#64
    r14 := g.rdi }

/-- The size of one call: `rbx` capped by `r12` (`cmp rbx, r12; cmovb rdx, rbx`). -/
abbrev sz (g : Gprs) : BitVec 64 := if g.rbx.toNat < g.r12.toNat then g.rbx else g.r12

/-- At the `call` (95): `rax` the vtable, `rcx` = `&processed`, `rdx` the size, `rsi` = `data`, `rdi` = `stream`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V, g.r14), rcx := g.r13, rdx := sz g, rsi := g.rbp, rdi := g.r14 }

/-- `processed`, read at 98. -/
abbrev pd (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rsp + 4#64)

/-- After 98's block: `rdx` = `processed`, `data` and `size` moved by it. -/
abbrev g98 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rdx := (pd V g).setWidth 64
    rbx := g.rbx - (pd V g).setWidth 64
    rbp := g.rbp + (pd V g).setWidth 64 }

/-- `rax` at 112 from 98: the callee's answer when its low half is not 0; `E_FAIL` when `processed` is 0; 0 when
`size` is left 0. -/
def R98 (V : Addr → Byte) (g : Gprs) (r : BitVec 64) : Prop :=
  (g.rax.setWidth 32 ≠ 0#32 ∧ r = g.rax) ∨
  (g.rax.setWidth 32 = 0#32 ∧ pd V g = 0#32 ∧ r = 2147500037#64) ∨
  (g.rax.setWidth 32 = 0#32 ∧ pd V g ≠ 0#32 ∧ g.rbx - (pd V g).setWidth 64 = 0#64 ∧ r = 0#64)

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem s31 : BitVec.setWidth 64 2147483648#32 = 2147483648#64 := by decide
theorem s85 : BitVec.setWidth 64 2147500037#32 = 2147500037#64 := by decide
theorem a24 (x : Addr) : x + 16#64 + 8 = x + 24#64 := by bv_omega
theorem a32 (x : Addr) : x + 24#64 + 8 = x + 32#64 := by bv_omega
theorem a40 (x : Addr) : x + 32#64 + 8 = x + 40#64 := by bv_omega
theorem a48 (x : Addr) : x + 40#64 + 8 = x + 48#64 := by bv_omega
theorem a56 (x : Addr) : x + 48#64 + 8 = x + 56#64 := by bv_omega
theorem a64 (x : Addr) : x + 56#64 + 8 = x + 64#64 := by bv_omega

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry, `size` 0: the prologue, `eax` 0, to 144. -/
theorem vc_0z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64} (hz : g.rdx = 0#64)
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 144 ∧ g' = { g with rax := 0#64, rsp := aR g.rsp } ∧ V' = Vp V g cn)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, P5, aR] at hz hcn w1 w2 w3 w4 w5 wc ⊢
  have e : (rdx == 0) = true := beq_iff_eq.2 hz
  wpx [W_0, W_37, o0, o1, Op.ldf, hcn, xz, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From the entry, `size` not 0: the prologue, the loop's registers `gL`, to 73. -/
theorem vc_0n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64} (hz : g.rdx ≠ 0#64)
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 73 ∧ g' = gL g ∧ V' = Vp V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, P5, aR, gL] at hz hcn w1 w2 w3 w4 w5 wc ⊢
  have e : (rdx == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_0, W_37, o0, o1, Op.ldf, hcn, xz, s31, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- 144: `eax` 0, to 112. -/
theorem vc_144 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_144 fb F Wl (fun j' g' _ V' => j' = 112 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_144, o8, xz]
  all_goals vfin

/-- From 73: the vtable, the size, the arguments, to the `call` (95). -/
theorem vc_73 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fr : ∀ i < 8, Foot F.data (Addr.add g.r14 i)) :
    W_73 fb F Wl (fun j' g' _ V' => j' = 95 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, sz] at fr ⊢
  by_cases hcf : rbx.toNat < r12.toNat
  · have hd : decide (rbx.toNat < r12.toNat) = true := decide_eq_true hcf
    wpx [W_73, o4, hd, hcf, decide_true, ↓reduceIte, eq_self_iff_true]
    all_goals vfin
  · have hd : decide (rbx.toNat < r12.toNat) = false := decide_eq_false hcf
    wpx [W_73, o4, hd, hcf, decide_false, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true]
    all_goals vfin

/-- From 98, the callee's answer not 0: to 112. -/
theorem vc_98a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 ≠ 0#32)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 112 ∧ g' = g98 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g98, pd] at ha f4 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 ha
  wpx [W_98, W_64, W_152, W_68, o5, o2, o3, o9, e, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 98, the answer 0 and `processed` 0: `eax` = `E_FAIL`, to 112. -/
theorem vc_98b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : pd V g = 0#32) (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 112 ∧ g' = { g98 V g with rax := 2147500037#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g98, pd] at ha hp f4 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (rdd(V, rsp + 4#64) == 0) = true := beq_iff_eq.2 hp
  wpx [W_98, W_64, W_152, W_68, o5, o2, o3, o9, e, e2, s85, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 98, the answer 0, `processed` not 0, `size` left 0: to 144. -/
theorem vc_98c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : pd V g ≠ 0#32) (hb : g.rbx - (pd V g).setWidth 64 = 0#64)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 144 ∧ g' = g98 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g98, pd] at ha hp hb f4 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (rdd(V, rsp + 4#64) == 0) = false := beq_eq_false_iff_ne.2 hp
  have e3 : (rbx - BitVec.setWidth 64 rdd(V, rsp + 4#64) == 0) = true := beq_iff_eq.2 hb
  wpx [W_98, W_64, W_152, W_68, o5, o2, o3, o9, e, e2, e3, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 98, the answer 0, `processed` not 0, `size` not left 0: to 73. -/
theorem vc_98d {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax.setWidth 32 = 0#32)
    (hp : pd V g ≠ 0#32) (hb : g.rbx - (pd V g).setWidth 64 ≠ 0#64)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 73 ∧ g' = g98 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g98, pd] at ha hp hb f4 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 ha
  have e2 : (rdd(V, rsp + 4#64) == 0) = false := beq_eq_false_iff_ne.2 hp
  have e3 : (rbx - BitVec.setWidth 64 rdd(V, rsp + 4#64) == 0) = false := beq_eq_false_iff_ne.2 hb
  wpx [W_98, W_64, W_152, W_68, o5, o2, o3, o9, e, e2, e3, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 112: the stack guard checked, the frame dropped, the five pops, to the `ret` (140). -/
theorem vc_112 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8 + 8 + 8) i)) :
    W_112 fb F Wl (fun j' g' _ V' => j' = 140 ∧
      (∃ rs, g' = { g with
        rbx := rdq(V, g.rsp + 16#64)
        rbp := rdq(V, g.rsp + 16#64 + 8)
        rsi := rs
        r12 := rdq(V, g.rsp + 16#64 + 8 + 8)
        r13 := rdq(V, g.rsp + 16#64 + 8 + 8 + 8)
        r14 := rdq(V, g.rsp + 16#64 + 8 + 8 + 8 + 8)
        rsp := g.rsp + 16#64 + 8 + 8 + 8 + 8 + 8 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 p1 p2 p3 p4 p5 ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_112, W_128, o6, o7, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `WriteStream (stream, data, size)` from its entry, the stack guard's 8 bytes at `fs:0x28` readable, the pushes'
slots and the guard's slot in what the run may store into: the prologue run (`Vp`, the guard as read after the
pushes); `size` 0: at 112 with `rax` 0 (`k0`); else at the loop's head 73 with the registers `gL` (`k1`). -/
theorem wst_entry {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L wst_at wst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = wst_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (k0 : X.cpu.gpr.rdx = 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vp V X.cpu.gpr rdq(P5 V X.cpu.gpr, fb + 40#64)) → Y.cpu.rip = wst_at.add 112 →
      Y.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := aR X.cpu.gpr.rsp } → GoG prof L o gev gP gE Y t')
    (k1 : X.cpu.gpr.rdx ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vp V X.cpu.gpr rdq(P5 V X.cpu.gpr, fb + 40#64)) → Y.cpu.rip = wst_at.add 73 →
      Y.cpu.gpr = gL X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases hz : X.cpu.gpr.rdx = 0#64
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0z hz rfl w1 w2 w3 w4 w5 hcl wc) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine (c_144 prof fb).run c hfs hin _ hKY hAY hrY (vc_144 (g := Y.cpu.gpr)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    exact k0 hz U t₂ hKU hAU hrU (by rw [hgU, hgY]; try rfl)
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0n hz rfl w1 w2 w3 w4 w5 hcl wc) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k1 hz Y t₁ hKY hAY hrY hgY

/-- From the loop's head (73), `stream`'s 8 bytes (`r14`) and its vtable's at `+ 24` readable, the latter the
callee's entry `eW`, the return address's slot in what the run may store into: at `eW` with the registers `gC`, `rsp`
8 lower, the return address `wst_at + 98` stored below `rsp`. -/
theorem wst_call {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L wst_at wst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = wst_at.add 73) (fr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.r14 i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, X.cpu.gpr.r14) + 24#64) i))
    {eW : Addr} {codeW : List Byte} (hinW : CodeIn L eW codeW) (hW0 : 0 < codeW.length)
    (htgt : rdq(V, rdq(V, X.cpu.gpr.r14) + 24#64) = eW)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (wst_at.add 98) 8)) → Y.cpu.rip = eW →
      Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_73 prof fb).run c hfs hin _ hK hA hrip (vc_73 fr) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have he : eaD Y 0 24 = rdq(V, X.cpu.gpr.r14) + 24#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
    rw [hgY]
    rfl
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_95 _) (by rw [he]; exact fv) hinW hW0
    (by rw [he]; exact htgt) (by rw [hsY]; exact hst) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From the callee's return (98), `processed`'s 4 bytes (`rsp + 4`) readable: at 112 with the registers `g98` and
`rax` as `R98` says (`k112`), or, the answer 0, `processed` not 0, `size` not left 0, at the loop's head 73 with the
registers `g98` (`k73`); the bytes as at 98. -/
theorem wst_back {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L wst_at wst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = wst_at.add 98) (f4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 4#64) i))
    (k112 : ∀ (r : BitVec 64), R98 V X.cpu.gpr r → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = wst_at.add 112 → Y.cpu.gpr = { g98 V X.cpu.gpr with rax := r } →
      GoG prof L o gev gP gE Y t')
    (k73 : X.cpu.gpr.rax.setWidth 32 = 0#32 → pd V X.cpu.gpr ≠ 0#32 →
      X.cpu.gpr.rbx - (pd V X.cpu.gpr).setWidth 64 ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = wst_at.add 73 → Y.cpu.gpr = g98 V X.cpu.gpr →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases ha : X.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases hp : pd V X.cpu.gpr = 0#32
    · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98b ha hp f4) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
      subst V₁
      exact k112 _ (Or.inr (Or.inl ⟨ha, hp, rfl⟩)) Y t₁ hKY hAY hrY hgY
    · by_cases hb : X.cpu.gpr.rbx - (pd V X.cpu.gpr).setWidth 64 = 0#64
      · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98c ha hp hb f4) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
        subst V₁
        refine (c_144 prof fb).run c hfs hin _ hKY hAY hrY (vc_144 (g := Y.cpu.gpr)) ?_
        rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
        subst V₂
        exact k112 _ (Or.inr (Or.inr ⟨ha, hp, hb, rfl⟩)) U t₂ hKU hAU hrU (by rw [hgU, hgY])
      · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98d ha hp hb f4) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
        subst V₁
        exact k73 ha hp hb Y t₁ hKY hAY hrY hgY
  · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98a ha f4) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k112 _ (Or.inl ⟨ha, rfl⟩) Y t₁ hKY hAY hrY (by rw [hgY]; try rfl)

/-- From 112 to the return address (at `rsp + 56`), the stack guard at `rsp + 8` the one at `fs:0x28`: `rbx`, `rbp`,
`r12`, `r13`, `r14` popped from `rsp + 16` … `rsp + 48`, `rsp` 64 above, `rsi` some value, the others as at 112. -/
theorem wst_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L wst_at wst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = wst_at.add 112) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 16#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 32#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 40#64) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 48#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 56#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 8#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 56#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ rs, Z.cpu.gpr = { X.cpu.gpr with
        rbx := rdq(V, X.cpu.gpr.rsp + 16#64)
        rbp := rdq(V, X.cpu.gpr.rsp + 24#64)
        rsi := rs
        r12 := rdq(V, X.cpu.gpr.rsp + 32#64)
        r13 := rdq(V, X.cpu.gpr.rsp + 40#64)
        r14 := rdq(V, X.cpu.gpr.rsp + 48#64)
        rsp := X.cpu.gpr.rsp + 64#64 }) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_112 prof fb).run c hfs hin _ hK hA hrip
    (vc_112 (g := X.cpu.gpr) hc f8 hcl f16 (by rw [a24]; exact f24) (by rw [a24, a32]; exact f32)
      (by rw [a24, a32, a40]; exact f40) (by rw [a24, a32, a40, a48]; exact f48)) ?_
  rintro j' g fl V₃ ⟨rfl, ⟨rs, rfl⟩, rfl⟩ Y t₃ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 56#64 := by rw [hgY, a24, a32, a40, a48, a56]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_140 _) (by rw [hsY]; exact f56) hin₂ h₂
    (by rw [hsY]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₄ hKZ hAZ hrZ ⟨rs, ?_⟩
  rw [hgZ]
  show Y.cpu.gpr.set 4 (Y.cpu.gpr.rsp + 8) = _
  rw [hsY, a64, hgY, a24, a32, a40, a48, a56]
  try rfl

end FV7z.Wst
