import FV7z.Mbu.Holds
import FV7z.Uca.Holds
import FV7z.Ffp.Holds
/-!
# `MultiByteToUnicodeString2`: from the return from `mbstowcs` (121) to the return address (PLAN.md §M, M1)

`W` the state back from `mbstowcs` at 121, `S` the stack pointer at the function's entry: `rsp` = `gq S`, `rbx` = `d`
(`dest._chars` before the call), `rbp` = `dest`, `r12` = `src`, `rax` = what `mbstowcs` returned.

- `rax` = -1 (`m1`, the `je` at 125): the fallback at 344, each byte of `s` = `src._chars` stored as 4 at `d` up to
  the first 0 byte (the loop at 368, `floop`, by induction), 4 bytes 0 after them, `dest._len` = the count (391),
  on to 400 (`mbu_fb`). The bytes read are the ones in memory at the time (`Uca.Cw`): `FbOk` asks for the first 0.
- Else (131): `d'` = `dest._chars` read back, `dest._len` = `eax`, `d' [eax]` = 0 (`VN`), then the scan for a
  character in `[0x10000, 0x10ffff]` (`Spr`; 160 to 195, the loop at 176, `sloop`, by induction): none before the
  first 0 to 400 (`mbu_ns`), else at 207 on to the `UString (const wchar_t *)` call at 210 (`kS`, a hypothesis: the
  surrogate loop from 215 is not covered yet).
- `mbu_121`: both; `mbu_ok`: `mbu_pre` with `mbstowcs` a hypothesis (`kms`, back at 121 with its post `PM`) and
  `mbu_121` after it: every path from the entry to the return address, but the surrogate path (`kS`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mbu

/-- `mbstowcs`'s failure, `(size_t) -1`. -/
def m1 : BitVec 64 := 18446744073709551615#64

/-- The address of the `j`-th 4-byte character at `d`. -/
theorem idx4m (d : Addr) (j : Nat) : d + BitVec.ofNat 64 j * 4#64 = Addr.add d (4 * j) := by
  show d + BitVec.ofNat 64 j * BitVec.ofNat 64 4 = d + BitVec.ofNat 64 (4 * j)
  rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]

/-- The next 4-byte character. -/
theorem nxt4 (a : Addr) (k : Nat) : Addr.add a (4 * k) + 4#64 = Addr.add a (4 * (k + 1)) := by
  have e : 4 * (k + 1) = 4 * k + 4 := by omega
  show a + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 4 = a + BitVec.ofNat 64 (4 * (k + 1))
  rw [e, Mys.ptr_step]

theorem z4 (a : Addr) : Addr.add a (4 * 0) = a := by rw [Nat.mul_zero, addr_add_zero]

/-- A character `c` that needs a surrogate pair: `c - 0x10000 ≤ 0xfffff` (unsigned). -/
abbrev Spr (c : BitVec 32) : Prop := (c - 65536#32).toNat ≤ 1048575

theorem spT {c : BitVec 32} (h : Spr c) :
    (decide ((c - 65536#32).toNat < 1048575) || decide (c - 65536#32 = 1048575#32)) = true := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · rw [decide_eq_true h, Bool.true_or]
  · have e : c - 65536#32 = 1048575#32 := BitVec.eq_of_toNat_eq h
    rw [decide_eq_true e, Bool.or_true]

theorem spF {c : BitVec 32} (h : ¬ Spr c) :
    (decide ((c - 65536#32).toNat < 1048575) || decide (c - 65536#32 = 1048575#32)) = false := by
  have h1 : ¬ (c - 65536#32).toNat < 1048575 := fun h' => h (Nat.le_of_lt h')
  have h2 : ¬ c - 65536#32 = 1048575#32 := fun e => h (show (c - 65536#32).toNat ≤ 1048575 by rw [e]; decide)
  rw [decide_eq_false h1, decide_eq_false h2, Bool.or_false]

/-- The bytes at 400 on the fallback path: the bytes at `s` up to the first 0 (`m` of them) stored as 4 each at `d`,
4 bytes 0 after them (`Uca.Mf`), `dest._len` (at `p + 8`) = `m`. -/
abbrev VF (V : Addr → Byte) (s d p : Addr) (m : Nat) : Addr → Byte :=
  Vst (Uca.Mf V s d m) (p + 8#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 m)) 4)

/-- The bytes from 131 on: `dest._len` (at `p + 8`) = `eax`, `d' [eax]` = 0. -/
abbrev VN (V : Addr → Byte) (p d' : Addr) (ax : BitVec 64) : Addr → Byte :=
  Vst (Vst V (p + 8#64) (toBytesLE (BitVec.setWidth 32 ax) 4))
    (d' + BitVec.setWidth 64 (BitVec.setWidth 32 ax) * 4#64) (toBytesLE 0#32 4)

/-- What the fallback path needs (`V` the bytes at 121): `m` bytes at `s` not 0 then a 0, as read in turn, readable;
`4 m + 4` bytes at `d` writable; the frame in the bytes at the end. -/
structure FbOk (F : Footprint) (Wl : List Rgn) (S fb : Addr) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte)
    (s d p : Addr) (m : Nat) : Prop where
  lt : m < 2 ^ 32
  rd : ∀ i ≤ m, Foot F.data (Addr.add s i)
  wr : ∀ i < 4 * m + 4, Foot Wl (Addr.add d i)
  nz : ∀ i < m, Uca.Cw V s d i (Addr.add s i) ≠ 0#8
  z : Uca.Cw V s d m (Addr.add s m) = 0#8
  fm : Fr S fb g₀ ra (VF V s d p m)

/-- What the path from 131 needs: the 4 bytes at `d' [eax]` writable, `m` characters at `d'` not 0 then a 0 in
`VN`, readable; the frame in `VN`. -/
structure NsOk (F : Footprint) (Wl : List Rgn) (S fb : Addr) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte)
    (p d' : Addr) (ax : BitVec 64) (m : Nat) : Prop where
  we : ∀ i < 4, Foot Wl (Addr.add (d' + BitVec.setWidth 64 (BitVec.setWidth 32 ax) * 4#64) i)
  rd : ∀ k ≤ m, ∀ i < 4, Foot F.data (Addr.add (Addr.add d' (4 * k)) i)
  nz : ∀ k < m, rdd(VN V p d' ax, Addr.add d' (4 * k)) ≠ 0#32
  z : rdd(VN V p d' ax, Addr.add d' (4 * m)) = 0#32
  fm : Fr S fb g₀ ra (VN V p d' ax)

/-- At the return address: `rbx`, `rbp`, `r12`, `r13` of `g₀`, `rsp` = `S + 8`, `r14`, `r15` of `G`. -/
abbrev Rt (g₀ : Gprs) (S : Addr) (G g : Gprs) : Prop :=
  g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.rsp = S + 8 ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = G.r14 ∧
    g.r15 = G.r15

/-- The bytes at the return address from those at 121 (`V`, the registers `g` there). -/
abbrev Out (V : Addr → Byte) (g : Gprs) (V'' : Addr → Byte) : Prop :=
  (g.rax = m1 ∧ ∃ m, V'' = VF V (rdq(V, g.r12)) g.rbx g.rbp m) ∨
    (g.rax ≠ m1 ∧ V'' = VN V g.rbp (rdq(V, g.rbp)) g.rax)

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- 121 for `rax` = -1: 344, `rsi` = `src._chars` (`s`), `edx` = 0, the byte at `s`; 0 to 391, else (`ecx` = 0) to
368. -/
theorem vc_121m {Q : Post} {s : Addr} (hm : g.rax = m1) (hs : rdq(V, g.r12) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.r12 i)) (f0 : ∀ i < 1, Foot F.data (Addr.add s i))
    (hZ : V s = 0#8 → ∀ fl,
      Q 391 { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V s)), rdx := 0#64, rsi := s } fl V)
    (hN : V s ≠ 0#8 → ∀ fl,
      Q 368 { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V s)), rcx := 0#64, rdx := 0#64, rsi := s }
        fl V) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm hs fp hZ hN ⊢
  subst hm
  have e1 : decide (m1 = 18446744073709551615#64) = true := decide_eq_true rfl
  by_cases hz : V s = 0#8
  · have e : (V s == 0) = true := beq_iff_eq.2 hz
    wpx [W_121, W_344, W_357, o5, o19, o20, e1, hs, e, Tun.rd1, Mys.sw8b, Mys.sw8a, BitVec.and_self, Ucw.xz,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true]
    all_goals repeat' (first
      | exact hZ hz _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)
  · have e : (V s == 0) = false := beq_eq_false_iff_ne.2 hz
    wpx [W_121, W_344, W_357, o5, o19, o20, e1, hs, e, Tun.rd1, Mys.sw8b, Mys.sw8a, BitVec.and_self, Ucw.xz,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true]
    all_goals repeat' (first
      | exact hN hz _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)

set_option maxHeartbeats 1000000 in
/-- The fallback loop at the index `j` (`rcx` = `rdx` = `j`, `al` = the byte `b`) with the next byte not 0: `b`
stored as 4 at `rbx + 4 j`, the next byte read, back to 368. -/
theorem vc_368n {j : Nat} {b : Byte} (hj : j + 1 < 2 ^ 32)
    (ha : g.rax = BitVec.setWidth 64 (BitVec.setWidth 32 b)) (hc : g.rcx = BitVec.ofNat 64 j)
    (hd : g.rdx = BitVec.ofNat 64 j)
    (fw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + BitVec.ofNat 64 j * 4#64) i))
    (fr : ∀ i < 1, Foot F.data (Addr.add (g.rsi + BitVec.ofNat 64 (j + 1)) i))
    (hn : Vst V (g.rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4)
      (g.rsi + BitVec.ofNat 64 (j + 1)) ≠ 0#8) :
    W_368 fb F Wl (fun j' g' _ V' => j' = 368 ∧
      V' = Vst V (g.rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4) ∧
      g' = { g with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V' (g.rsi + BitVec.ofNat 64 (j + 1)))),
        rcx := BitVec.ofNat 64 (j + 1),
        rdx := BitVec.ofNat 64 (j + 1) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hc hd fw fr hn ⊢
  subst ha hc hd
  have e : (Vst V (rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4)
      (rsi + BitVec.ofNat 64 (j + 1)) == 0) = false := beq_eq_false_iff_ne.2 hn
  wpx [W_368, W_387, o21, o22, Op.zxr, Mys.sw8b, Mys.sw8a, Tun.rd1, BitVec.and_self, Ffp.inc32 hj, Ffp.sw32 hj, e,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- The fallback loop at the index `j` with the next byte 0: `b` stored, `rbx` = `rbx + 4 (j + 1)`, to 391. -/
theorem vc_368z {j : Nat} {b : Byte} (hj : j + 1 < 2 ^ 32)
    (ha : g.rax = BitVec.setWidth 64 (BitVec.setWidth 32 b)) (hc : g.rcx = BitVec.ofNat 64 j)
    (hd : g.rdx = BitVec.ofNat 64 j)
    (fw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + BitVec.ofNat 64 j * 4#64) i))
    (fr : ∀ i < 1, Foot F.data (Addr.add (g.rsi + BitVec.ofNat 64 (j + 1)) i))
    (hz : Vst V (g.rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4)
      (g.rsi + BitVec.ofNat 64 (j + 1)) = 0#8) :
    W_368 fb F Wl (fun j' g' _ V' => j' = 391 ∧
      V' = Vst V (g.rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4) ∧
      g' = { g with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V' (g.rsi + BitVec.ofNat 64 (j + 1)))),
        rcx := BitVec.ofNat 64 (j + 1),
        rdx := BitVec.ofNat 64 (j + 1),
        rbx := g.rbx + BitVec.ofNat 64 (j + 1) * 4#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hc hd fw fr hz ⊢
  subst ha hc hd
  have e : (Vst V (rbx + BitVec.ofNat 64 j * 4#64) (toBytesLE (BitVec.setWidth 32 b) 4)
      (rsi + BitVec.ofNat 64 (j + 1)) == 0) = true := beq_iff_eq.2 hz
  wpx [W_368, W_387, o21, o22, Op.zxr, Mys.sw8b, Mys.sw8a, Tun.rd1, BitVec.and_self, Ffp.inc32 hj, Ffp.sw32 hj, e,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

/-- 391: 4 bytes 0 at `rbx`, `dest._len` = `edx`, to 400. -/
theorem vc_391 (fw0 : ∀ i < 4, Foot Wl (Addr.add g.rbx i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i)) :
    W_391 fb F Wl (fun j' g' _ V' => j' = 400 ∧ g' = g ∧
      V' = Vst (Vst V g.rbx (toBytesLE 0#32 4)) (g.rbp + 8#64) (toBytesLE (BitVec.setWidth 32 g.rdx) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw0 fw8 ⊢
  wpx [W_391, o23]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- 121 for `rax` not -1: 131, `r12` = `d'` = `dest._chars`, `dest._len` = `eax`, `d' [eax]` = 0 (`VN`), the first
character; 0 to 400, else (160: `rsi` = `d'`, `ebx` = 0) to 195. -/
theorem vc_121n {Q : Post} {d' : Addr} (hm : g.rax ≠ m1) (hd' : rdq(V, g.rbp) = d')
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (f8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i))
    (fe : ∀ i < 4, Foot Wl (Addr.add (d' + BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) * 4#64) i))
    (f0 : ∀ i < 4, Foot F.data (Addr.add d' i))
    (hZ : rdd(VN V g.rbp d' g.rax, d') = 0#32 → ∀ fl,
      Q 400 { g with rax := BitVec.setWidth 64 (rdd(VN V g.rbp d' g.rax, d')), r12 := d' } fl
        (VN V g.rbp d' g.rax))
    (hN : rdd(VN V g.rbp d' g.rax, d') ≠ 0#32 → ∀ fl,
      Q 195 { g with rax := BitVec.setWidth 64 (rdd(VN V g.rbp d' g.rax, d')), rbx := 0#64, rsi := d', r12 := d' }
        fl (VN V g.rbp d' g.rax)) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm hd' fp f8 fe hZ hN ⊢
  have e1 : decide (rax = 18446744073709551615#64) = false := decide_eq_false hm
  by_cases hz : rdd(VN V rbp d' rax, d') = 0#32
  · have e : (rdd(VN V rbp d' rax, d') == 0) = true := beq_iff_eq.2 hz
    dsimp only [VN] at e
    wpx [W_121, W_131, W_160, o5, o6, o7, e1, hd', e, Ucw.xz, BitVec.and_self,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true]
    all_goals repeat' (first
      | exact hZ hz _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)
  · have e : (rdd(VN V rbp d' rax, d') == 0) = false := beq_eq_false_iff_ne.2 hz
    dsimp only [VN] at e
    wpx [W_121, W_131, W_160, o5, o6, o7, e1, hd', e, Ucw.xz, BitVec.and_self,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true]
    all_goals repeat' (first
      | exact hN hz _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)

set_option maxHeartbeats 1000000 in
/-- The scan at 195 (`eax` = the character `c`) with `c` not in `Spr` and the next character not 0: on to it
(176: `rsi` + 4, `rbx` + 1), back to 195. -/
theorem vc_195n {c : BitVec 32} (ha : g.rax = BitVec.setWidth 64 c) (hs : ¬ Spr c)
    (fr : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 4#64) i)) (hn : rdd(V, g.rsi + 4#64) ≠ 0#32) :
    W_195 fb F Wl (fun j' g' _ V' => j' = 195 ∧ V' = V ∧
      g' = { g with rax := BitVec.setWidth 64 (rdd(V, g.rsi + 4#64)), rsi := g.rsi + 4#64, rbx := g.rbx + 1#64 })
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha fr hn ⊢
  subst ha
  have e7 := spF hs
  have e : (rdd(V, rsi + 4#64) == 0) = false := beq_eq_false_iff_ne.2 hn
  wpx [W_195, W_176, W_207, o8, o9, o10, e7, e, BitVec.and_self,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- The scan at 195 with `c` not in `Spr` and the next character 0: to 400. -/
theorem vc_195z {c : BitVec 32} (ha : g.rax = BitVec.setWidth 64 c) (hs : ¬ Spr c)
    (fr : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 4#64) i)) (hz : rdd(V, g.rsi + 4#64) = 0#32) :
    W_195 fb F Wl (fun j' g' _ V' => j' = 400 ∧ V' = V ∧
      g' = { g with rax := BitVec.setWidth 64 (rdd(V, g.rsi + 4#64)), rsi := g.rsi + 4#64, rbx := g.rbx + 1#64 })
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha fr hz ⊢
  subst ha
  have e7 := spF hs
  have e : (rdd(V, rsi + 4#64) == 0) = true := beq_iff_eq.2 hz
  wpx [W_195, W_176, W_207, o8, o9, o10, e7, e, BitVec.and_self,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

/-- The scan at 195 with `c` in `Spr`: 207, `rdi` = `rsp`, to the `call` at 210. -/
theorem vc_195s {c : BitVec 32} (ha : g.rax = BitVec.setWidth 64 c) (hs : Spr c) :
    W_195 fb F Wl (fun j' g' _ V' => j' = 210 ∧ V' = V ∧
      g' = { g with rax := BitVec.setWidth 64 (c - 65536#32), rdi := g.rsp }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha ⊢
  subst ha
  have e7 := spT hs
  wpx [W_195, W_176, W_207, o8, o9, o10, e7,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true]
  all_goals repeat' (first | exact rfl | with_reducible assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The loops -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The fallback loop from 368 at the index `j` (`j + 1 ≤ m`) of the bytes at `s` (`rsi`) to `d` (`rbx`), the bytes
`Cw W s d j`: on to 391 with all `m` stored, `rbx` = `d + 4 m`, `rdx` = `m`. By induction on `m - j - 1`. -/
theorem floop {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu)
    {W : Addr → Byte} {s d : Addr} {m : Nat} {G : Gprs} (hm : m < 2 ^ 32)
    (fr : ∀ i ≤ m, Foot F.data (Addr.add s i)) (fw : ∀ i < 4 * m, Foot Wl (Addr.add d i))
    (hb : ∀ i < m, Uca.Cw W s d i (Addr.add s i) ≠ 0#8) (h0 : Uca.Cw W s d m (Addr.add s m) = 0#8)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Uca.Cw W s d m) →
      Z.cpu.rip = mbu_at.add 391 →
      Z.cpu.gpr = { G with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 (Uca.Cw W s d m (Addr.add s m))),
          rcx := BitVec.ofNat 64 m,
          rdx := BitVec.ofNat 64 m,
          rsi := s,
          rbx := Addr.add d (4 * m) } →
      GoG prof L o gev gP gE Z t') :
    ∀ (r j : Nat), j + 1 + r = m → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Uca.Cw W s d j) → X.cpu.rip = mbu_at.add 368 →
      X.cpu.gpr = { G with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 (Uca.Cw W s d j (Addr.add s j))),
          rcx := BitVec.ofNat 64 j,
          rdx := BitVec.ofNat 64 j,
          rsi := s,
          rbx := d } →
      GoG prof L o gev gP gE X t := by
  intro r
  induction r with
  | zero =>
    intro j hj X t hK hA hrip hg
    obtain rfl : m = j + 1 := by omega
    have hx : X.cpu.gpr.rbx = d := by rw [hg]; try rfl
    have hs' : X.cpu.gpr.rsi = s := by rw [hg]; try rfl
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rbx + BitVec.ofNat 64 j * 4#64) i) := fun i hi => by
      rw [hx, idx4m, addr_add_add]
      exact fw _ (by omega)
    have hr1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + BitVec.ofNat 64 (j + 1)) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hs']
      exact fr (j + 1) (Nat.le_refl _)
    have hz : Vst (Uca.Cw W s d j) (X.cpu.gpr.rbx + BitVec.ofNat 64 j * 4#64)
        (toBytesLE (BitVec.setWidth 32 (Uca.Cw W s d j (Addr.add s j))) 4)
        (X.cpu.gpr.rsi + BitVec.ofNat 64 (j + 1)) = 0#8 := by
      rw [hx, hs', idx4m]
      exact h0
    refine (c_368 prof fb).run c hfs hin _ hK hA hrip
      (vc_368z (j := j) (b := Uca.Cw W s d j (Addr.add s j)) hm (by rw [hg]; try rfl) (by rw [hg]; try rfl)
        (by rw [hg]; try rfl) hw4 hr1 hz) ?_
    rintro j' g fl V₁ ⟨rfl, hV, hg'⟩ Y t₁ hKY hAY hrY hgY -
    subst hV
    rw [hx, idx4m] at hAY
    refine k Y t₁ hKY hAY hrY ?_
    rw [hgY, hg', hx, hs', idx4m, idx4m, hg]
    try rfl
  | succ r ih =>
    intro j hj X t hK hA hrip hg
    have hx : X.cpu.gpr.rbx = d := by rw [hg]; try rfl
    have hs' : X.cpu.gpr.rsi = s := by rw [hg]; try rfl
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rbx + BitVec.ofNat 64 j * 4#64) i) := fun i hi => by
      rw [hx, idx4m, addr_add_add]
      exact fw _ (by omega)
    have hr1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + BitVec.ofNat 64 (j + 1)) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hs']
      exact fr (j + 1) (by omega)
    have hn : Vst (Uca.Cw W s d j) (X.cpu.gpr.rbx + BitVec.ofNat 64 j * 4#64)
        (toBytesLE (BitVec.setWidth 32 (Uca.Cw W s d j (Addr.add s j))) 4)
        (X.cpu.gpr.rsi + BitVec.ofNat 64 (j + 1)) ≠ 0#8 := by
      rw [hx, hs', idx4m]
      exact hb (j + 1) (by omega)
    refine (c_368 prof fb).run c hfs hin _ hK hA hrip
      (vc_368n (j := j) (b := Uca.Cw W s d j (Addr.add s j)) (by omega) (by rw [hg]; try rfl) (by rw [hg]; try rfl)
        (by rw [hg]; try rfl)
        hw4 hr1 hn) ?_
    rintro j' g fl V₁ ⟨rfl, hV, hg'⟩ Y t₁ hKY hAY hrY hgY -
    subst hV
    rw [hx, idx4m] at hAY
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_
    rw [hgY, hg', hx, hs', idx4m, hg]
    try rfl

/-- The scan from 195 at the `k`-th (`k + 1 ≤ m`) of the characters at `p` in the bytes `U` (`rsi` = `p + 4 k`, `rbx`
= `k`): to 210 at the first in `Spr` (`kS`), else to 400 at the `m`-th, 0 (`kE`). By induction on `m - k - 1`. -/
theorem sloop {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu)
    {U : Addr → Byte} {p : Addr} {m : Nat} {G : Gprs}
    (fr : ∀ k ≤ m, ∀ i < 4, Foot F.data (Addr.add (Addr.add p (4 * k)) i))
    (hb : ∀ k < m, rdd(U, Addr.add p (4 * k)) ≠ 0#32) (h0 : rdd(U, Addr.add p (4 * m)) = 0#32)
    (kS : ∀ k < m, Spr (rdd(U, Addr.add p (4 * k))) → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem U → Z.cpu.rip = mbu_at.add 210 →
      Z.cpu.gpr = { G with
          rax := BitVec.setWidth 64 (rdd(U, Addr.add p (4 * k)) - 65536#32),
          rbx := BitVec.ofNat 64 k,
          rsi := Addr.add p (4 * k),
          rdi := G.rsp } →
      GoG prof L o gev gP gE Z t')
    (kE : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem U → Z.cpu.rip = mbu_at.add 400 →
      Z.cpu.gpr = { G with
          rax := BitVec.setWidth 64 (rdd(U, Addr.add p (4 * m))),
          rbx := BitVec.ofNat 64 m,
          rsi := Addr.add p (4 * m) } →
      GoG prof L o gev gP gE Z t') :
    ∀ (r k : Nat), k + 1 + r = m → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem U →
      X.cpu.rip = mbu_at.add 195 →
      X.cpu.gpr = { G with
          rax := BitVec.setWidth 64 (rdd(U, Addr.add p (4 * k))),
          rbx := BitVec.ofNat 64 k,
          rsi := Addr.add p (4 * k) } →
      GoG prof L o gev gP gE X t := by
  intro r
  induction r with
  | zero =>
    intro k hk X t hK hA hrip hg
    obtain rfl : m = k + 1 := by omega
    have hsi : X.cpu.gpr.rsi + 4#64 = Addr.add p (4 * (k + 1)) := by rw [hg]; exact nxt4 p k
    have hbx : X.cpu.gpr.rbx + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [hg]; exact (BitVec.ofNat_add k 1).symm
    rcases Classical.em (Spr (rdd(U, Addr.add p (4 * k)))) with hsp | hsp
    · refine (c_195 prof fb).run c hfs hin _ hK hA hrip (vc_195s (by rw [hg]; try rfl) hsp) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine kS k (by omega) hsp Y t₁ hKY hAY hrY ?_
      rw [hgY, hg]
      try rfl
    · refine (c_195 prof fb).run c hfs hin _ hK hA hrip
        (vc_195z (by rw [hg]; try rfl) hsp (by rw [hsi]; exact fr (k + 1) (Nat.le_refl _)) (by rw [hsi]; exact h0)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine kE Y t₁ hKY hAY hrY ?_
      rw [hgY, hsi, hbx, hg]
      try rfl
  | succ r ih =>
    intro k hk X t hK hA hrip hg
    have hsi : X.cpu.gpr.rsi + 4#64 = Addr.add p (4 * (k + 1)) := by rw [hg]; exact nxt4 p k
    have hbx : X.cpu.gpr.rbx + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [hg]; exact (BitVec.ofNat_add k 1).symm
    rcases Classical.em (Spr (rdd(U, Addr.add p (4 * k)))) with hsp | hsp
    · refine (c_195 prof fb).run c hfs hin _ hK hA hrip (vc_195s (by rw [hg]; try rfl) hsp) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine kS k (by omega) hsp Y t₁ hKY hAY hrY ?_
      rw [hgY, hg]
      try rfl
    · refine (c_195 prof fb).run c hfs hin _ hK hA hrip
        (vc_195n (by rw [hg]; try rfl) hsp (by rw [hsi]; exact fr (k + 1) (by omega))
          (by rw [hsi]; exact hb (k + 1) (by omega)))
        ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (k + 1) (by omega) Y t₁ hKY hAY hrY ?_
      rw [hgY, hsi, hbx, hg]
      try rfl

/-! ## The paths -/

/-- From 121 for `rax` = -1 (`s` = `src._chars`, `d` = `rbx`, `p` = `dest`): the fallback copy, on to the return
address with the bytes `VF` (`k`). -/
theorem mbu_fb {fb S s d p : Addr} {g₀ : Gprs} {W : State} {m : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu) (hK : KeptW Wl s₀ W)
    (hA : Agree F W.proc.mm.mem V) (hrip : W.cpu.rip = mbu_at.add 121) (hs : W.cpu.gpr.rsp = gq S)
    (hax : W.cpu.gpr.rax = m1) (hp : W.cpu.gpr.rbp = p) (hd : W.cpu.gpr.rbx = d)
    (hsrc : rdq(V, W.cpu.gpr.r12) = s) (fp : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.r12 i))
    (f8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (h : FbOk F Wl S fb g₀ (e₂.add j₂) V s d p m) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (w4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq S + 24#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (VF V s d p m) →
      Z'.cpu.rip = e₂.add j₂ → Rt g₀ S W.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE W t := by
  obtain ⟨hm, fr, fw, hb, h0, hF⟩ := h
  have k391 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Uca.Cw V s d m) →
      Z.cpu.rip = mbu_at.add 391 → Z.cpu.gpr.rbx = Addr.add d (4 * m) → Z.cpu.gpr.rdx = BitVec.ofNat 64 m →
      Z.cpu.gpr.rbp = p → Z.cpu.gpr.rsp = gq S → Z.cpu.gpr.r14 = W.cpu.gpr.r14 → Z.cpu.gpr.r15 = W.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t' := by
    intro Z t' hKZ hAZ hrZ hbx hdx hpz hsz h14 h15
    refine (c_391 prof fb).run c hfs hin (fun j' g' _ V' => j' = 400 ∧ g' = Z.cpu.gpr ∧
        V' = Vst (Vst (Uca.Cw V s d m) Z.cpu.gpr.rbx (toBytesLE 0#32 4)) (Z.cpu.gpr.rbp + 8#64)
          (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rdx) 4)) hKZ hAZ hrZ
      (vc_391 (fun i hi => by rw [hbx, addr_add_add]; exact fw _ (by omega)) (by rw [hpz]; exact f8)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    rw [hbx, hpz, hdx] at hV₁
    subst V₁
    exact mbu_tail c hfs hin hKY hAY hrY (by rw [hgY]; exact hsz) hin₂ h₂ hF fc w1 w2 w3 w4 w5 hl
      fun ra Z' t'' hKZ' hAZ' hrZ' hgZ' => k Z' t'' hKZ' hAZ' hrZ'
        (by rw [hgZ', hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, h14, h15⟩)
  have hs0 : ∀ i < 1, Foot F.data (Addr.add s i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    exact fr 0 (Nat.zero_le _)
  cases m with
  | zero =>
    have hz : V s = 0#8 := by
      have h' := h0
      rw [addr_add_zero] at h'
      exact h'
    refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 391 ∧ V' = V ∧
        g' = { W.cpu.gpr with rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V s)), rdx := 0#64, rsi := s })
      hK hA hrip (vc_121m hax hsrc fp hs0 (fun _ _ => ⟨rfl, rfl, rfl⟩) fun h' => absurd hz h') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact k391 Y t₁ hKY hAY hrY (by rw [hgY, z4]; exact hd) (by rw [hgY]; try rfl) (by rw [hgY]; exact hp)
      (by rw [hgY]; exact hs) (by rw [hgY]; try rfl) (by rw [hgY]; try rfl)
  | succ j =>
    have hn : V s ≠ 0#8 := by
      have h' := hb 0 (Nat.succ_pos j)
      rw [addr_add_zero] at h'
      exact h'
    refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 368 ∧ V' = V ∧
        g' = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 (V s)), rcx := 0#64, rdx := 0#64, rsi := s })
      hK hA hrip (vc_121m hax hsrc fp hs0 (fun h' => absurd h' hn) fun _ _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine floop (G := W.cpu.gpr) c hfs hin hm fr (fun i hi => fw i (by omega)) hb h0
      ?_ j 0 (by omega) Y t₁ hKY hAY hrY ?_
    · intro Z t' hKZ hAZ hrZ hgZ
      exact k391 Z t' hKZ hAZ hrZ (by rw [hgZ]; try rfl) (by rw [hgZ]; try rfl) (by rw [hgZ]; exact hp)
        (by rw [hgZ]; exact hs)
        (by rw [hgZ]; try rfl) (by rw [hgZ]; try rfl)
    · rw [hgY, addr_add_zero]
      subst hd
      try rfl

/-- From 121 for `rax` not -1 (`d'` = `dest._chars` read back): to the return address with the bytes `VN` (`k`)
when no character before the first 0 is in `Spr`, else to the `call` at 210 (`kS`). -/
theorem mbu_ns {fb S d' : Addr} {g₀ : Gprs} {W : State} {m : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu) (hK : KeptW Wl s₀ W)
    (hA : Agree F W.proc.mm.mem V) (hrip : W.cpu.rip = mbu_at.add 121) (hs : W.cpu.gpr.rsp = gq S)
    (hax : W.cpu.gpr.rax ≠ m1) (hd' : rdq(V, W.cpu.gpr.rbp) = d')
    (fp : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.rbp i))
    (f8 : ∀ i < 4, Foot Wl (Addr.add (W.cpu.gpr.rbp + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (h : NsOk F Wl S fb g₀ (e₂.add j₂) V W.cpu.gpr.rbp d' W.cpu.gpr.rax m)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (w4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq S + 24#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax) →
      Z'.cpu.rip = e₂.add j₂ → Rt g₀ S W.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t')
    (kS : ∀ k < m, Spr (rdd(VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax, Addr.add d' (4 * k))) →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax) →
      Z.cpu.rip = mbu_at.add 210 →
      Z.cpu.gpr = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (rdd(VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax, Addr.add d' (4 * k)) - 65536#32),
          rbx := BitVec.ofNat 64 k,
          rsi := Addr.add d' (4 * k),
          rdi := W.cpu.gpr.rsp,
          r12 := d' } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE W t := by
  obtain ⟨fe, fr, hb, h0, hF⟩ := h
  have kT : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax) → Z.cpu.rip = mbu_at.add 400 →
      Z.cpu.gpr.rsp = gq S → Z.cpu.gpr.r14 = W.cpu.gpr.r14 → Z.cpu.gpr.r15 = W.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t' := by
    intro Z t' hKZ hAZ hrZ hsZ h14 h15
    exact mbu_tail c hfs hin hKZ hAZ hrZ hsZ hin₂ h₂ hF fc w1 w2 w3 w4 w5 hl
      fun ra Z' t'' hKZ' hAZ' hrZ' hgZ' => k Z' t'' hKZ' hAZ' hrZ'
        (by rw [hgZ']; exact ⟨rfl, rfl, rfl, rfl, rfl, h14, h15⟩)
  have f0 : ∀ i < 4, Foot F.data (Addr.add d' i) := fun i hi => by
    have h' := fr 0 (Nat.zero_le _) i hi
    rw [z4] at h'
    exact h'
  rcases Classical.em (rdd(VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax, d') = 0#32) with hz | hz
  · refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 400 ∧ V' = VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax ∧
        g' = { W.cpu.gpr with rax := BitVec.setWidth 64 (rdd(VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax, d')), r12 := d' })
      hK hA hrip (vc_121n hax hd' fp f8 fe f0 (fun _ _ => ⟨rfl, rfl, rfl⟩) fun h' => absurd hz h') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact kT Y t₁ hKY hAY hrY (by rw [hgY]; exact hs) (by rw [hgY]; try rfl) (by rw [hgY]; try rfl)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h' | h'
    · subst h'
      rw [z4] at h0
      exact absurd h0 hz
    · exact h'
  refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 195 ∧ V' = VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax ∧
      g' = { W.cpu.gpr with
        rax := BitVec.setWidth 64 (rdd(VN V W.cpu.gpr.rbp d' W.cpu.gpr.rax, d')), rbx := 0#64, rsi := d', r12 := d' })
    hK hA hrip (vc_121n hax hd' fp f8 fe f0 (fun h' => absurd h' hz) fun _ _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine sloop (G := { W.cpu.gpr with r12 := d' }) c hfs hin fr hb h0 ?_ ?_ (m - 1) 0 (by omega) Y t₁ hKY hAY hrY ?_
  · intro k' hk hsp Z t' hKZ hAZ hrZ hgZ
    refine kS k' hk hsp Z t' hKZ hAZ hrZ ?_
    rw [hgZ]
    try rfl
  · intro Z t' hKZ hAZ hrZ hgZ
    exact kT Z t' hKZ hAZ hrZ (by rw [hgZ]; exact hs) (by rw [hgZ]; try rfl) (by rw [hgZ]; try rfl)
  · rw [hgY, z4]
    try rfl

/-- From 121, back from `mbstowcs` with the bytes `V`: `mbu_fb` for `rax` = -1, `mbu_ns` else. -/
theorem mbu_121 {fb S : Addr} {g₀ : Gprs} {W : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu) (hK : KeptW Wl s₀ W)
    (hA : Agree F W.proc.mm.mem V) (hrip : W.cpu.rip = mbu_at.add 121) (hs : W.cpu.gpr.rsp = gq S)
    (fp : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.r12 i)) (fq : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.rbp i))
    (f8 : ∀ i < 4, Foot Wl (Addr.add (W.cpu.gpr.rbp + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hFB : W.cpu.gpr.rax = m1 →
      ∃ m, FbOk F Wl S fb g₀ (e₂.add j₂) V (rdq(V, W.cpu.gpr.r12)) W.cpu.gpr.rbx W.cpu.gpr.rbp m)
    (hNS : W.cpu.gpr.rax ≠ m1 →
      ∃ m, NsOk F Wl S fb g₀ (e₂.add j₂) V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax m)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (w4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq S + 24#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (k : ∀ (V'' : Addr → Byte) (Z' : State) (t' : Nat), Out V W.cpu.gpr V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ → Rt g₀ S W.cpu.gpr Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t')
    (kS : ∀ (m k : Nat), NsOk F Wl S fb g₀ (e₂.add j₂) V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax m →
      k < m → Spr (rdd(VN V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax,
        Addr.add (rdq(V, W.cpu.gpr.rbp)) (4 * k))) →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (VN V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax) →
      Z.cpu.rip = mbu_at.add 210 →
      Z.cpu.gpr = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (rdd(VN V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax,
            Addr.add (rdq(V, W.cpu.gpr.rbp)) (4 * k)) - 65536#32),
          rbx := BitVec.ofNat 64 k,
          rsi := Addr.add (rdq(V, W.cpu.gpr.rbp)) (4 * k),
          rdi := W.cpu.gpr.rsp,
          r12 := rdq(V, W.cpu.gpr.rbp) } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE W t := by
  rcases Classical.em (W.cpu.gpr.rax = m1) with hm | hm
  · obtain ⟨m, hF⟩ := hFB hm
    exact mbu_fb c hfs hin hK hA hrip hs hm rfl rfl rfl fp f8 hin₂ h₂ hF fc w1 w2 w3 w4 w5 hl
      fun Z' t' hKZ hAZ hrZ hRt => k (VF V (rdq(V, W.cpu.gpr.r12)) W.cpu.gpr.rbx W.cpu.gpr.rbp m) Z' t'
        (Or.inl ⟨hm, m, rfl⟩) hKZ hAZ hrZ hRt
  · obtain ⟨m, hF⟩ := hNS hm
    exact mbu_ns c hfs hin hK hA hrip hs hm rfl fq f8 hin₂ h₂ hF fc w1 w2 w3 w4 w5 hl
      (fun Z' t' hKZ hAZ hrZ hRt => k (VN V W.cpu.gpr.rbp (rdq(V, W.cpu.gpr.rbp)) W.cpu.gpr.rax) Z' t'
        (Or.inr ⟨hm, rfl⟩) hKZ hAZ hrZ hRt)
      fun k' hk hsp => kS m k' hF hk hsp

/-- `MultiByteToUnicodeString2 (dest, src, codePage)` from its entry to the return address: `mbu_pre` up to
`mbstowcs`'s entry, `mbstowcs` a hypothesis (`kms`: back at 121 with `rsp`, `rbp`, `r12` kept and its post `PM`),
then `mbu_121` (`hPM`: what `PM` gives for it). The return address is reached (`kr0`, `kr1`, `kr2`) on every path
but the one with a character in `Spr` (`kS`: on to the `UString (const wchar_t *)` call at 210). -/
theorem mbu_ok {fb : Addr} {cn d : BitVec 64} {n : BitVec 32} {P PR PM : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu)
    (hinU : CodeIn L U8u.u8u_at U8u.u8u)
    {cR cM : List Byte} (hinR : CodeIn L ra2_at cR) (hR : 0 < cR.length) (hinM : CodeIn L mbs_at cM)
    (hM : 0 < cM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mbu_at)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fg : ∀ i < 1, Foot F.data (Addr.add 7938424#64 i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 24#64) i))
    (wd8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i)) (wb : ∀ i < 4, Foot Wl (Addr.add d i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcn : rdq(Vp V X.cpu.gpr, fb + 40#64) = cn) (hd : rdq(Vp V X.cpu.gpr, X.cpu.gpr.rdi) = d)
    (hn : rdd(Vd V X.cpu.gpr cn, X.cpu.gpr.rsi + 8#64) = n)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hFE : n = 0#32 → Fr X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) (VE V X.cpu.gpr cn d))
    (kr0 : ∀ (ra : BitVec 64) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VE V X.cpu.gpr cn d) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = { X.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kfu : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VE V X.cpu.gpr cn d) (gq X.cpu.gpr.rsp - 8) (toBytesLE (mbu_at.add 443) 8)) →
      Y.cpu.rip = U8u.u8u_at →
      (∃ ra rd, Y.cpu.gpr = ({ X.cpu.gpr with
          rax := ra,
          rdx := rd,
          rbx := d,
          rsp := gq X.cpu.gpr.rsp,
          rbp := X.cpu.gpr.rdi,
          rsi := X.cpu.gpr.rdi,
          rdi := X.cpu.gpr.rsi,
          r12 := X.cpu.gpr.rsi }).set 4 (gq X.cpu.gpr.rsp - 8)) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = mbu_at.add 443 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp →
        Fr X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) V'' → P W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (W : State) (V'' : Addr → Byte) (ra : BitVec 64) (Z' : State) (t' : Nat), P W V'' →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := ra,
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8,
          r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13 } →
      GoG prof L o gev gP gE Z' t')
    (kfr : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VE V X.cpu.gpr cn d) (gq X.cpu.gpr.rsp - 8) (toBytesLE (mbu_at.add 456) 8)) →
      Y.cpu.rip = ra2_at → Y.cpu.gpr = (gR X.cpu.gpr d n).set 4 (gq X.cpu.gpr.rsp - 8) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = mbu_at.add 456 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp → W.cpu.gpr.rbp = X.cpu.gpr.rdi →
        W.cpu.gpr.r12 = X.cpu.gpr.rsi → W.cpu.gpr.r13 = nn n → PR W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kms : ∀ (G : Gprs) (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V' (gq X.cpu.gpr.rsp - 8) (toBytesLE (mbu_at.add 121) 8)) →
      Z.cpu.rip = mbs_at → Z.cpu.gpr = ({ G with rsi := rdq(V', G.r12), rdx := G.r13, rdi := G.rbx }).set 4
        (gq X.cpu.gpr.rsp - 8) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = mbu_at.add 121 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp → W.cpu.gpr.rbp = G.rbp →
        W.cpu.gpr.r12 = G.r12 → PM W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Z t')
    (hPM : ∀ (W : State) (V'' : Addr → Byte), PM W V'' →
      (W.cpu.gpr.rax = m1 → ∃ m, FbOk F Wl X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) V''
        (rdq(V'', W.cpu.gpr.r12)) W.cpu.gpr.rbx W.cpu.gpr.rbp m) ∧
      (W.cpu.gpr.rax ≠ m1 → ∃ m, NsOk F Wl X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) V'' W.cpu.gpr.rbp
        (rdq(V'', W.cpu.gpr.rbp)) W.cpu.gpr.rax m))
    (kr2 : ∀ (W : State) (V₁ V'' : Addr → Byte) (Z' : State) (t' : Nat), PM W V₁ → Out V₁ W.cpu.gpr V'' →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Rt X.cpu.gpr X.cpu.gpr.rsp W.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t')
    (kS : ∀ (W : State) (V₁ : Addr → Byte) (m k : Nat) (Z : State) (t' : Nat), PM W V₁ →
      NsOk F Wl X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) V₁ W.cpu.gpr.rbp (rdq(V₁, W.cpu.gpr.rbp)) W.cpu.gpr.rax m →
      k < m → Spr (rdd(VN V₁ W.cpu.gpr.rbp (rdq(V₁, W.cpu.gpr.rbp)) W.cpu.gpr.rax,
        Addr.add (rdq(V₁, W.cpu.gpr.rbp)) (4 * k))) →
      KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VN V₁ W.cpu.gpr.rbp (rdq(V₁, W.cpu.gpr.rbp)) W.cpu.gpr.rax) →
      Z.cpu.rip = mbu_at.add 210 →
      Z.cpu.gpr = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (rdd(VN V₁ W.cpu.gpr.rbp (rdq(V₁, W.cpu.gpr.rbp)) W.cpu.gpr.rax,
            Addr.add (rdq(V₁, W.cpu.gpr.rbp)) (4 * k)) - 65536#32),
          rbx := BitVec.ofNat 64 k,
          rsi := Addr.add (rdq(V₁, W.cpu.gpr.rbp)) (4 * k),
          rdi := W.cpu.gpr.rsp,
          r12 := rdq(V₁, W.cpu.gpr.rbp) } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine mbu_pre c hfs hin hinU hinR hR hinM hM hK hA hrip fc fa fs8 fs f12 fg w1 w2 w3 w4 w5 wd8 wb w6 hl hcn hd hn
    hin₂ h₂ hFE kr0 kfu kr1 kfr ?_
  intro G V' Z t' hG hKZ hAZ hrZ hgZ
  have hG2 : G.rbp = X.cpu.gpr.rdi ∧ G.r12 = X.cpu.gpr.rsi := by
    rcases hG with ⟨rfl, -⟩ | ⟨W', -, -, hb', hc', -, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨hb', hc'⟩
  refine kms G V' Z t' hKZ hAZ hrZ hgZ ?_
  intro W V'' t'' hKW hAW hrW hsW hpW h12W hPW
  obtain ⟨hFB, hNS⟩ := hPM W V'' hPW
  have fp : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.r12 i) := by rw [h12W, hG2.2]; exact fs
  have fq : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.rbp i) := by rw [hpW, hG2.1]; exact fa
  have f8 : ∀ i < 4, Foot Wl (Addr.add (W.cpu.gpr.rbp + 8#64) i) := by rw [hpW, hG2.1]; exact wd8
  exact mbu_121 c hfs hin hKW hAW hrW hsW fp fq f8 hin₂ h₂ hFB hNS fc w1 w2 w3 w4 w5 hl
    (fun V₂ Z' t₂ hO hKZ' hAZ' hrZ' hRt => kr2 W V'' V₂ Z' t₂ hPW hO hKZ' hAZ' hrZ' hRt)
    fun m k hF hk hsp Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ => kS W V'' m k Z₂ t₂ hPW hF hk hsp hKZ₂ hAZ₂ hrZ₂ hgZ₂

end FV7z.Mbu
