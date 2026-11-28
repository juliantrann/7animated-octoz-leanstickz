import FV7z.Nlc.Steps
import FV7z.Mcn.Vc
import FV7z.Stm.Vc
/-!
# `_nl_normalize_codeset`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `_nl_normalize_codeset (codeset, name_len)` (at `0x619f30`; `rdi = s`, `rsi = n`).
The counting loop (48–83): `rbx` the table `__ctype_b` (`[0x7914c8]`), `rbp = s`, `r12 = n`, `rdx` the byte,
`r8 = s + n`, `r9 = 0`, `esi` "only digits", `rdi` the count. The copy loop (140–180): `r8` the table
`__ctype_tolower` (`[0x7914d0]`), `rdx` the index, `rax` where the next byte goes, `r9` the result. The calls of
`malloc` (91, 196, 245) and the `ret`s (190, 234) are steps of their own.

- `vc_0e` (`n = 0`): the three pushes, `edi = 4`, to the `call` at 245. `vc_0n`: the pushes and the loop's
  registers, to 48.
- `vc_48n` (the byte not alnum): to 74. `vc_48d`, `vc_48x` (alnum; a digit or not): `rdi + 1`, `esi` kept or `r9d`
  (`cmov` zero-extends either way), to 74.
- `vc_74l` (`r8 ≠ rdx + 1`): to 48. `vc_74d` (`esi ≠ 0`): `rdi + 4`, to the `call` at 196. `vc_74n`: `rdi + 1`, to
  the `call` at 91.
- `vc_96z`, `vc_201z`, `vc_250z` (`malloc` gave 0): to 224. `vc_224`: `r9d = 0`, the pops, `rax = 0`, to the `ret`
  at 234.
- `vc_96n`: `r9 = rax`, to 104. `vc_201n`, `vc_250n`: `"iso\0"` stored, `rax = p + 3`, to 104 or 180. `vc_104`:
  `r8 = [0x7914d0]`, `edx = 0`, to 140.
- `vc_140a` (alpha): the low byte of `[r8 + c·4]` stored at `rax`, `rax + 1`, to 131. `vc_140s` (not a digit): to
  131. `vc_140dl`, `vc_140de` (a digit stored; `rdx + 1 < r12` or not): to 140 or 180.
- `vc_131l`, `vc_131e` (`rdx + 1 < r12` or not): to 140 or 180. `vc_180`: the 0 stored, `rax = r9`, the pops, to
  the `ret` at 190.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (fr3 fr3_rd)
namespace FV7z.Nlc

/-- The byte at `a`. -/
abbrev rb (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs a 1).map V)

/-- A byte zero-extended, as `movzx r32` leaves it. -/
abbrev zb (x : BitVec 8) : Addr := (x.setWidth 32).setWidth 64

/-- `c - '0'` in 32 bits: below 10 just for a digit. -/
abbrev d32 (x : BitVec 8) : BitVec 32 := x.setWidth 32 - 48#32

theorem sw8 (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by bv_omega

/-- Not a digit: neither below 9 nor 9 (the flags of `cmp r32, 9`). -/
theorem nd9 {x : BitVec 32} (h : ¬ x.toNat < 10) : ¬ x.toNat < 9 ∧ ¬ x = 9#32 :=
  ⟨by omega, fun e => h (by rw [e]; decide)⟩

/-- A digit: below 9 or 9. -/
theorem dg9 {x : BitVec 32} (h : x.toNat < 10) : x.toNat < 9 ∨ (¬ x.toNat < 9 ∧ x = 9#32) := by
  by_cases h9 : x.toNat < 9
  · exact .inl h9
  · exact .inr ⟨h9, by bv_omega⟩

/-- `y < x` in 64 bits: `x` neither below `y` nor `y` (the flags of `cmp x, y` for `ja`, `jbe`). -/
theorem lt64 {x y : BitVec 64} (h : y.toNat < x.toNat) : ¬ x.toNat < y.toNat ∧ ¬ x = y :=
  ⟨by omega, fun e => by rw [e] at h; omega⟩

/-- Not `y < x`: `x` below `y`, or `y`. -/
theorem nlt64 {x y : BitVec 64} (h : ¬ y.toNat < x.toNat) :
    x.toNat < y.toNat ∨ (¬ x.toNat < y.toNat ∧ x = y) := by
  by_cases hl : x.toNat < y.toNat
  · exact .inl hl
  · exact .inr ⟨hl, by bv_omega⟩

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- `n = 0`: the three pushes, `edi = 4`; to the `call` of `malloc` (245). -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rsi == 0) = true)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 245 ∧ V' = fr3 V g.rsp g.r12 g.rbp g.rbx ∧
      g' = { g with rsp := g.rsp - 8 - 8 - 8, rdi := 4#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h1 h2 h3 ⊢
  mcx +contextual [W_0, W_240, W_17, o0, o20, o1, fr3, hz, h1, h2, h3]

set_option maxHeartbeats 2000000 in
/-- `n ≠ 0`: the three pushes, `rbx` the table `__ctype_b`, `rbp = rdx = s`, `r12 = n`, `r8 = s + n`, `r9 = 0`,
`esi = 1`, `edi = 0`; to the loop (48). -/
theorem vc_0n {T : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rsi == 0) = false)
    (hS : 32 ≤ g.rsp.toNat) (d1 : 7935184 ≤ g.rsp.toNat - 24) (hT : rdq(V, 7935176#64) = T)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add 7935176#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ V' = fr3 V g.rsp g.r12 g.rbp g.rbx ∧
      g' = { g with
        rsp := g.rsp - 8 - 8 - 8, rbx := T, rbp := g.rdi, r12 := g.rsi, rdx := g.rdi,
        r8 := g.rsi + g.rdi, r9 := 0#64, rsi := 1#64, rdi := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hS d1 h1 h2 h3 ⊢
  have k1 := fr3_rd V rsp r12 rbp rbx (x := 7935176#64) (n := 8) hS (by simp only [BitVec.toNat_ofNat]; omega)
    (.inl (by simp only [BitVec.toNat_ofNat]; omega))
  mcx +contextual [W_0, W_240, W_17, o0, o20, o1, fr3, k1, hT, hz, h1, h2, h3, f1]

set_option maxHeartbeats 2000000 in
/-- The byte `c` at `rdx` not alnum: to 74. -/
theorem vc_48n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (rb V (g.rbx + zb (rb V g.rdx) * 2#64) &&& 8#8 == 0) = true)
    (fc : ∀ i < 1, Foot F.data (Addr.add g.rdx i))
    (ft : ∀ i < 1, Foot F.data (Addr.add (g.rbx + zb (rb V g.rdx) * 2#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 74 ∧ V' = V ∧
      g' = { g with rcx := zb (rb V g.rdx), rax := zb (rb V g.rdx) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb, zb] at hb fc ft ⊢
  mcx +contextual [W_48, W_60, o2, o3, hb, fc, ft]

set_option maxHeartbeats 2000000 in
/-- `c` a digit: `rdi + 1`, `esi` kept (zero-extended); to 74. -/
theorem vc_48d {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (rb V (g.rbx + zb (rb V g.rdx) * 2#64) &&& 8#8 == 0) = false) (hd : (d32 (rb V g.rdx)).toNat < 10)
    (fc : ∀ i < 1, Foot F.data (Addr.add g.rdx i))
    (ft : ∀ i < 1, Foot F.data (Addr.add (g.rbx + zb (rb V g.rdx) * 2#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 74 ∧ V' = V ∧
      g' = { g with
        rcx := zb (rb V g.rdx), rax := (d32 (rb V g.rdx)).setWidth 64, rdi := g.rdi + 1#64,
        rsi := (g.rsi.setWidth 32).setWidth 64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb, zb, d32] at hb hd fc ft ⊢
  have hd' := eq_true hd
  mcx +contextual [W_48, W_60, o2, o3, hb, hd', fc, ft]

set_option maxHeartbeats 2000000 in
/-- `c` alnum, not a digit: `rdi + 1`, `esi = r9d`; to 74. -/
theorem vc_48x {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (rb V (g.rbx + zb (rb V g.rdx) * 2#64) &&& 8#8 == 0) = false) (hd : ¬ (d32 (rb V g.rdx)).toNat < 10)
    (fc : ∀ i < 1, Foot F.data (Addr.add g.rdx i))
    (ft : ∀ i < 1, Foot F.data (Addr.add (g.rbx + zb (rb V g.rdx) * 2#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 74 ∧ V' = V ∧
      g' = { g with
        rcx := zb (rb V g.rdx), rax := (d32 (rb V g.rdx)).setWidth 64, rdi := g.rdi + 1#64,
        rsi := (g.r9.setWidth 32).setWidth 64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb, zb, d32] at hb hd fc ft ⊢
  have hd' := eq_false hd
  mcx +contextual [W_48, W_60, o2, o3, hb, hd', fc, ft]

/-- Not the last byte: to 48. -/
theorem vc_74l {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ¬ g.r8 = g.rdx + 1#64) :
    W_74 F Wl (fun j' g' _ V' => j' = 48 ∧ V' = V ∧ g' = { g with rdx := g.rdx + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  have hl' := eq_false hl
  mcx +contextual [W_74, W_83, o4, o5, hl']

set_option maxHeartbeats 2000000 in
/-- The last byte, only digits: `rdi + 4`; to the `call` of `malloc` (196). -/
theorem vc_74d {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.r8 = g.rdx + 1#64)
    (hs : (g.rsi.setWidth 32 == 0) = false) :
    W_74 F Wl (fun j' g' _ V' => j' = 196 ∧ V' = V ∧
      g' = { g with rdx := g.rdx + 1#64, rdi := g.rdi + 4#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hs ⊢
  have he' := eq_true he
  mcx +contextual [W_74, W_83, W_192, W_87, o4, o5, o16, o6, he', hs]

set_option maxHeartbeats 2000000 in
/-- The last byte, not only digits: `rdi + 1`; to the `call` of `malloc` (91). -/
theorem vc_74n {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.r8 = g.rdx + 1#64)
    (hs : (g.rsi.setWidth 32 == 0) = true) :
    W_74 F Wl (fun j' g' _ V' => j' = 91 ∧ V' = V ∧
      g' = { g with rdx := g.rdx + 1#64, rdi := g.rdi + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hs ⊢
  have he' := eq_true he
  mcx +contextual [W_74, W_83, W_192, W_87, o4, o5, o16, o6, he', hs]

/-- `malloc` gave 0: to 224. -/
theorem vc_96z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = true) :
    W_96 F Wl (fun j' g' _ V' => j' = 224 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_96, W_101, o7, o8, hz]

/-- `malloc` gave `p`: `r9 = p`; to 104. -/
theorem vc_96n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false) :
    W_96 F Wl (fun j' g' _ V' => j' = 104 ∧ V' = V ∧ g' = { g with r9 := g.rax }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_96, W_101, o7, o8, hz]

/-- `r8` the table `__ctype_tolower`, `edx = 0`; to the copy loop (140). -/
theorem vc_104 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f1 : ∀ i < 8, Foot F.data (Addr.add 7935184#64 i)) :
    W_104 F Wl (fun j' g' _ V' => j' = 140 ∧ V' = V ∧
      g' = { g with r8 := rdq(V, 7935184#64), rdx := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_104, o9, f1]

/-- The bytes after `"iso\0"` is stored at `p`. -/
abbrev Vi (V : Addr → Byte) (p : Addr) : Addr → Byte := Vst V p (toBytesLE 7304041#32 4)

set_option maxHeartbeats 2000000 in
/-- `malloc` (`len + 4`) gave 0: `r9 = 0`; to 224. -/
theorem vc_201z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = true) :
    W_201 F Wl (fun j' g' _ V' => j' = 224 ∧ V' = V ∧ g' = { g with r9 := g.rax }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_201, W_209, o17, o18, hz]

set_option maxHeartbeats 2000000 in
/-- `malloc` (`len + 4`) gave `p`: `"iso\0"` at `p`, `r9 = p`, `rax = p + 3`; to 104. -/
theorem vc_201n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false)
    (w : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_201 F Wl (fun j' g' _ V' => j' = 104 ∧ V' = Vi V g.rax ∧
      g' = { g with r9 := g.rax, rax := g.rax + 3#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vi] at hz w ⊢
  mcx +contextual [W_201, W_209, o17, o18, hz, w]

set_option maxHeartbeats 2000000 in
/-- `malloc (4)` gave 0: `r9 = 0`; to 224. -/
theorem vc_250z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = true) :
    W_250 F Wl (fun j' g' _ V' => j' = 224 ∧ V' = V ∧ g' = { g with r9 := g.rax }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_250, W_258, o17, o21, hz]

set_option maxHeartbeats 2000000 in
/-- `malloc (4)` gave `p`: `"iso\0"` at `p`, `r9 = p`, `rax = p + 3`; to 180. -/
theorem vc_250n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false)
    (w : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_250 F Wl (fun j' g' _ V' => j' = 180 ∧ V' = Vi V g.rax ∧
      g' = { g with r9 := g.rax, rax := g.rax + 3#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vi] at hz w ⊢
  mcx +contextual [W_250, W_258, o17, o21, hz, w]

/-- The byte `c` of the name at `rbp + rdx`. -/
abbrev cn (V : Addr → Byte) (g : Gprs) : BitVec 8 := rb V (g.rbp + g.rdx)

/-- Its entry in `__ctype_b`, the high byte (`_ISalpha` is its bit 2). -/
abbrev ca (V : Addr → Byte) (g : Gprs) : Addr := g.rbx + zb (cn V g) * 2#64 + 1#64

/-- Its entry in `__ctype_tolower`. -/
abbrev cl (V : Addr → Byte) (g : Gprs) : Addr := g.r8 + zb (cn V g) * 4#64

set_option maxHeartbeats 2000000 in
/-- `c` alpha: its `tolower` stored at `rax`, `rax + 1`; to 131. -/
theorem vc_140a {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : (rb V (ca V g) &&& 4#8 == 0) = false)
    (fc : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (fa : ∀ i < 1, Foot F.data (Addr.add (ca V g) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (cl V g) i))
    (w : ∀ i < 1, Foot Wl (Addr.add (g.rax + 1#64 + 18446744073709551615#64) i)) :
    W_140 F Wl (fun j' g' _ V' => j' = 131 ∧
      V' = Vst V (g.rax + 1#64 + 18446744073709551615#64) (toBytesLE ((rdd(V, cl V g)).setWidth 8) 1) ∧
      g' = { g with rdi := zb (cn V g), rcx := (rdd(V, cl V g)).setWidth 64, rax := g.rax + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cn, ca, cl, rb, zb] at ha fc fa fl w ⊢
  mcx +contextual [W_140, W_120, W_152, o12, o10, o13, Op.zxr, sw8, ha, fc, fa, fl, w]

set_option maxHeartbeats 2000000 in
/-- `c` neither alpha nor a digit: to 131. -/
theorem vc_140s {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : (rb V (ca V g) &&& 4#8 == 0) = true)
    (hd : ¬ (d32 (cn V g)).toNat < 10)
    (fc : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (fa : ∀ i < 1, Foot F.data (Addr.add (ca V g) i)) :
    W_140 F Wl (fun j' g' _ V' => j' = 131 ∧ V' = V ∧
      g' = { g with rdi := zb (cn V g), rsi := (d32 (cn V g)).setWidth 64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cn, ca, d32, rb, zb] at ha hd fc fa ⊢
  obtain ⟨h1, h2⟩ := nd9 hd
  have h1' := eq_false h1
  have h2' := eq_false h2
  mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', h2', fc, fa]

set_option maxHeartbeats 2000000 in
/-- `c` a digit, stored at `rax`; `rdx + 1 < r12`: to 140. -/
theorem vc_140dl {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : (rb V (ca V g) &&& 4#8 == 0) = true)
    (hd : (d32 (cn V g)).toNat < 10) (hl : (g.rdx + 1#64).toNat < g.r12.toNat)
    (fc : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (fa : ∀ i < 1, Foot F.data (Addr.add (ca V g) i))
    (w : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_140 F Wl (fun j' g' _ V' => j' = 140 ∧ V' = Vst V g.rax (toBytesLE (cn V g) 1) ∧
      g' = { g with
        rdi := zb (cn V g), rsi := (d32 (cn V g)).setWidth 64, rdx := g.rdx + 1#64,
        rax := g.rax + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cn, ca, d32, rb, zb] at ha hd hl fc fa w ⊢
  obtain ⟨l1, l2⟩ := lt64 hl
  have l1' := eq_false l1
  have l2' := eq_false l2
  rcases dg9 hd with h1 | ⟨h1, h2⟩
  · have h1' := eq_true h1
    mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', l1', l2', fc, fa, w]
  · have h1' := eq_false h1
    have h2' := eq_true h2
    mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', h2', l1', l2', fc, fa,
      w]

set_option maxHeartbeats 2000000 in
/-- `c` a digit, stored at `rax`; `rdx + 1` not below `r12`: to 180. -/
theorem vc_140de {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : (rb V (ca V g) &&& 4#8 == 0) = true)
    (hd : (d32 (cn V g)).toNat < 10) (hl : ¬ (g.rdx + 1#64).toNat < g.r12.toNat)
    (fc : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (fa : ∀ i < 1, Foot F.data (Addr.add (ca V g) i))
    (w : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_140 F Wl (fun j' g' _ V' => j' = 180 ∧ V' = Vst V g.rax (toBytesLE (cn V g) 1) ∧
      g' = { g with
        rdi := zb (cn V g), rsi := (d32 (cn V g)).setWidth 64, rdx := g.rdx + 1#64,
        rax := g.rax + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cn, ca, d32, rb, zb] at ha hd hl fc fa w ⊢
  rcases nlt64 hl with l1 | ⟨l1, l2⟩
  · have l1' := eq_true l1
    rcases dg9 hd with h1 | ⟨h1, h2⟩
    · have h1' := eq_true h1
      mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', l1', fc, fa, w]
    · have h1' := eq_false h1
      have h2' := eq_true h2
      mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', h2', l1', fc, fa, w]
  · have l1' := eq_false l1
    have l2' := eq_true l2
    rcases dg9 hd with h1 | ⟨h1, h2⟩
    · have h1' := eq_true h1
      mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', l1', l2', fc, fa, w]
    · have h1' := eq_false h1
      have h2' := eq_true h2
      mcx +contextual [W_140, W_120, W_152, W_164, o12, o10, o13, o14, Op.zxr, sw8, ha, h1', h2', l1', l2', fc,
        fa, w]

/-- `rdx + 1 < r12`: to 140. -/
theorem vc_131l {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : (g.rdx + 1#64).toNat < g.r12.toNat) :
    W_131 F Wl (fun j' g' _ V' => j' = 140 ∧ V' = V ∧ g' = { g with rdx := g.rdx + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  obtain ⟨l1, l2⟩ := lt64 hl
  have l1' := eq_false l1
  have l2' := eq_false l2
  mcx +contextual [W_131, o11, l1', l2']

/-- `rdx + 1` not below `r12`: to 180. -/
theorem vc_131e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ¬ (g.rdx + 1#64).toNat < g.r12.toNat) :
    W_131 F Wl (fun j' g' _ V' => j' = 180 ∧ V' = V ∧ g' = { g with rdx := g.rdx + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  rcases nlt64 hl with l1 | ⟨l1, l2⟩
  · have l1' := eq_true l1
    mcx +contextual [W_131, o11, l1']
  · have l1' := eq_false l1
    have l2' := eq_true l2
    mcx +contextual [W_131, o11, l1', l2']

set_option maxHeartbeats 2000000 in
/-- The 0 stored at `rax`, `rax = r9`, the pops; to the `ret` (190). -/
theorem vc_180 {g : Gprs} {f : Rflags} {V : Addr → Byte} (w : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_180 F Wl (fun j' g' _ V' => j' = 190 ∧ V' = Vst V g.rax (toBytesLE 0#8 1) ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧
      g'.rax = g.r9 ∧ g'.rbx = rdq(Vst V g.rax (toBytesLE 0#8 1), g.rsp) ∧
      g'.rbp = rdq(Vst V g.rax (toBytesLE 0#8 1), g.rsp + 8) ∧
      g'.r12 = rdq(Vst V g.rax (toBytesLE 0#8 1), g.rsp + 8 + 8) ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
      g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w p0 p1 p2 ⊢
  mcx +contextual [W_180, o15, w, p0, p1, p2]

set_option maxHeartbeats 2000000 in
/-- `malloc` failed: `rax = 0`, the pops; to the `ret` (234). -/
theorem vc_224 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_224 F Wl (fun j' g' _ V' => j' = 234 ∧ V' = V ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧ g'.rax = 0#64 ∧
      g'.rbx = rdq(V, g.rsp) ∧ g'.rbp = rdq(V, g.rsp + 8) ∧ g'.r12 = rdq(V, g.rsp + 8 + 8) ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 ⊢
  mcx +contextual [W_224, o19, p0, p1, p2]

end FV7z.Nlc
