import FV7z.Fmi.Steps
import FV7z.Mcn.Vc
import FV7z.Auxv.Vc
/-!
# `find_module_idx`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `find_module_idx (str, idxp)` (at `0x67ce30`; `rdi = str`, `rsi = idxp`). `r14` is the
cache `gconv_cache` (`[0x7a4bb0]`), `r12` its `hash_offset`, `rbx` its `hash_size`, `rbp` first `hval`, then the
probe step; `r13` the probe index; `[rsp + 4]` the bound on the names' offsets (`cache_size - string_offset`),
`[rsp + 8]` `string_offset`, `[rsp + 16]` `str`, `[rsp + 24]` `idxp`. A `div` (66, 78) and the calls (46: the hash,
118: `strcmp`) are steps of their own.

- `vc_0`: the six pushes, the cache's header and the saved arguments, to the `call` of `__hash_string` (46).
- `vc_51`: `hash_size`, `cache_size`, to the `div` (66). `vc_68`: `hash_size - 2`, the first index, to the `div` (78).
- `vc_80`: the bound and the step, to the probe (147).
- `vc_147e`: an empty slot: the epilogue with `eax = -1`, to the `ret` (186). `vc_147s`: the name's offset out of
  bounds, to the next index (127). `vc_147c`: to the `call` of `strcmp` (118).
- `vc_123f`: `strcmp` gave 0: `*idxp` the slot's index, the epilogue, to the `ret` (219). `vc_123n`: to 127.
- `vc_127`: the next index (`nxt`), to the probe (147).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6)
namespace FV7z.Fmi

/-- The 16-bit word at `a`. -/
abbrev rw16 (V : Addr → Byte) (a : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs a 2).map V)

/-- A word zero-extended, as `movzx r32` leaves it. -/
abbrev zw (x : BitVec 16) : Addr := (x.setWidth 32).setWidth 64

/-- The body's stack pointer: the six pushes and `sub rsp, 40`. -/
abbrev bR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 40#64

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx
/-- The cache (`gconv_cache`, at `0x7a4bb0`). -/
abbrev cC (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, 8014768#64)
/-- The bytes after `str` is saved. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V1 V g) (bR g.rsp + 16#64) (toBytesLE g.rdi 8)
/-- The cache's `string_offset` and `hash_offset`. -/
abbrev so0 (V : Addr → Byte) (g : Gprs) : BitVec 16 := rw16 (V2 V g) (cC V g + 4#64)
abbrev ho0 (V : Addr → Byte) (g : Gprs) : BitVec 16 := rw16 (V2 V g) (cC V g + 6#64)
/-- The bytes at the `call` of `__hash_string` (before its return address). -/
abbrev V4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (V2 V g) (bR g.rsp + 24#64) (toBytesLE g.rsi 8)) (bR g.rsp + 8#64) (toBytesLE (zw (so0 V g)) 8)

/-- The slot's offset in the cache, `hash_offset + 4 * index`, and the slot. -/
abbrev sx (g : Gprs) : Addr := g.r12 + (g.r13.setWidth 32).setWidth 64 * 4#64
abbrev sl (g : Gprs) : Addr := g.r14 + sx g

/-- The next probe index: `r + st`, less `h` when not below it. -/
def nxt (r st h : BitVec 32) : BitVec 32 :=
  if h.toNat < (r + st).toNat ∨ h = r + st then r + st - h else r + st

/-- The registers the loop keeps. -/
abbrev Kp (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp

/-- The bytes after `*idxp` is stored. -/
abbrev Vf (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V (rdq(V, g.rsp + 24#64)) (toBytesLE (zw (rw16 V (g.r15 + 2#64))) 8)

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- The six pushes, `r14` the cache, `eax = string_offset`, `r12 = hash_offset`, `str`, `idxp` and
`string_offset` saved; to the `call` of `__hash_string` (46). -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (fA : ∀ i < 8, Foot F.data (Addr.add 8014768#64 i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (bR g.rsp + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (bR g.rsp + 24#64) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (bR g.rsp + 8#64) i))
    (f4 : ∀ i < 2, Foot F.data (Addr.add (cC V g + 4#64) i))
    (f6 : ∀ i < 2, Foot F.data (Addr.add (cC V g + 6#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 46 ∧ V' = V4 V g ∧
      g' = { g with rsp := bR g.rsp, r14 := cC V g, rax := zw (so0 V g), r12 := zw (ho0 V g) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bR, V4, V2, V1, cC, so0, ho0, zw, rw16] at w1 w2 w3 w4 w5 w6 w16 w24 w8 f4 f6 ⊢
  mcx +contextual [W_0, o0, fr6, w1, w2, w3, w4, w5, w6, fA, w16, w24, w8, f4, f6]

/-- `ebx = hash_size`, `edx = 0`, `edi = cache_size`, `ebp = hval`; to the `div` (66). -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f8 : ∀ i < 2, Foot F.data (Addr.add (g.r14 + 8#64) i))
    (fZ : ∀ i < 4, Foot F.data (Addr.add 8014760#64 i)) :
    W_51 F Wl (fun j' g' _ V' => j' = 66 ∧ V' = V ∧ g' = { g with
      rbx := zw (rw16 V (g.r14 + 8#64)), rdx := 0#64, rdi := (rdd(V, 8014760#64)).setWidth 64,
      rbp := (g.rax.setWidth 32).setWidth 64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [zw, rw16] at f8 ⊢
  mcx +contextual [W_51, o1, f8, fZ]

/-- `esi = hash_size - 2`, `eax = hval`, `r13d` the first index, `edx = 0`; to the `div` (78). -/
theorem vc_68 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_68 F Wl (fun j' g' _ V' => j' = 78 ∧ V' = V ∧ g' = { g with
      rsi := ((g.rbx + 18446744073709551614#64).setWidth 32).setWidth 64, rax := (g.rbp.setWidth 32).setWidth 64,
      r13 := (g.rdx.setWidth 32).setWidth 64, rdx := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_68, o2]

/-- `[rsp + 4]` the bound `cache_size - string_offset`, `ebp` the step; to the probe (147). -/
theorem vc_80 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f4 : ∀ i < 2, Foot F.data (Addr.add (g.r14 + 4#64) i))
    (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 4#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 147 ∧
      V' = Vst V (g.rsp + 4#64) (toBytesLE (g.rdi.setWidth 32 - (rw16 V (g.r14 + 4#64)).setWidth 32) 4) ∧
      g' = { g with
        rax := zw (rw16 V (g.r14 + 4#64)),
        rdi := (g.rdi.setWidth 32 - (rw16 V (g.r14 + 4#64)).setWidth 32).setWidth 64,
        rbp := ((g.rdx + 1#64).setWidth 32).setWidth 64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [zw, rw16] at f4 w4 ⊢
  mcx +contextual [W_80, o3, f4, w4]

set_option maxHeartbeats 2000000 in
/-- An empty slot: the epilogue with `eax = -1`; to the `ret` (186). -/
theorem vc_147e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rw16 V (sl g) == 0) = true)
    (fN : ∀ i < 2, Foot F.data (Addr.add (sl g) i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_147 F Wl (fun j' g' _ V' => j' = 186 ∧ V' = V ∧ g'.rsp = g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rax = 4294967295#64 ∧ g'.rbx = rdq(V, g.rsp + 40#64) ∧ g'.rbp = rdq(V, g.rsp + 40#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 40#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [sl, sx, rw16] at hz fN p0 p1 p2 p3 p4 p5 ⊢
  mcx +contextual [W_147, W_167, o8, o9, Auxv.sw16b, hz, fN, p0, p1, p2, p3, p4, p5]

set_option maxHeartbeats 2000000 in
/-- The name's offset not below the bound: to the next index (127). -/
theorem vc_147s {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rw16 V (sl g) == 0) = false)
    (hc : ¬ ((rw16 V (sl g)).setWidth 32).toNat < (rdd(V, g.rsp + 4#64)).toNat)
    (fN : ∀ i < 2, Foot F.data (Addr.add (sl g) i)) (fL : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i)) :
    W_147 F Wl (fun j' g' _ V' => j' = 127 ∧ V' = V ∧ Kp g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [sl, sx, rw16, Kp] at hz hc fN fL ⊢
  have hc' := eq_false hc
  mcx +contextual [W_147, W_96, o8, o4, Op.zxr16, Auxv.sw16b, hz, hc', fN, fL]

set_option maxHeartbeats 2000000 in
/-- The name's offset below the bound: `rdi = str`, `rsi` the name (`cache + string_offset + offset`); to the
`call` of `strcmp` (118). -/
theorem vc_147c {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rw16 V (sl g) == 0) = false)
    (hc : ((rw16 V (sl g)).setWidth 32).toNat < (rdd(V, g.rsp + 4#64)).toNat)
    (fN : ∀ i < 2, Foot F.data (Addr.add (sl g) i)) (fL : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_147 F Wl (fun j' g' _ V' => j' = 118 ∧ V' = V ∧ Kp g g' ∧ g'.rdi = rdq(V, g.rsp + 16#64) ∧
      g'.rsi = zw (rw16 V (sl g)) + rdq(V, g.rsp + 8#64) + g.r14 ∧ g'.r15 = sl g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [sl, sx, rw16, zw, Kp] at hz hc fN fL f8 f16 ⊢
  have hc' := eq_true hc
  mcx +contextual [W_147, W_96, W_105, o8, o4, o5, Op.zxr16, Auxv.sw16b, hz, hc', fN, fL, f8, f16]

set_option maxHeartbeats 2000000 in
/-- `strcmp` gave 0: `*idxp` the slot's index, the epilogue; to the `ret` (219). -/
theorem vc_123f {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : (g.rax.setWidth 32 == 0) = true)
    (f2 : ∀ i < 2, Foot F.data (Addr.add (g.r15 + 2#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (wI : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 24#64)) i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_123 F Wl (fun j' g' _ V' => j' = 219 ∧ V' = Vf V g ∧ g'.rsp = g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rax = g.rax ∧ g'.rbx = rdq(Vf V g, g.rsp + 40#64) ∧ g'.rbp = rdq(Vf V g, g.rsp + 40#64 + 8) ∧
      g'.r12 = rdq(Vf V g, g.rsp + 40#64 + 8 + 8) ∧ g'.r13 = rdq(Vf V g, g.rsp + 40#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(Vf V g, g.rsp + 40#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = rdq(Vf V g, g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vf, zw, rw16] at h0 f2 f24 wI p0 p1 p2 p3 p4 p5 ⊢
  mcx +contextual [W_123, W_192, o6, o10, h0, f2, f24, wI, p0, p1, p2, p3, p4, p5]

/-- `strcmp` did not give 0: to the next index (127). -/
theorem vc_123n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : (g.rax.setWidth 32 == 0) = false) :
    W_123 F Wl (fun j' g' _ V' => j' = 127 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0 ⊢
  mcx +contextual [W_123, o6, h0]

set_option maxHeartbeats 2000000 in
/-- The next index: `r13d = nxt r13d ebp ebx`; to the probe (147). -/
theorem vc_127 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_127 F Wl (fun j' g' _ V' => j' = 147 ∧ V' = V ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r14 = g.r14 ∧
      g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧
      g'.r13 = (nxt (g.r13.setWidth 32) (g.rbp.setWidth 32) (g.rbx.setWidth 32)).setWidth 64) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [nxt]
  by_cases h1 : (rbx.setWidth 32).toNat < (r13.setWidth 32 + rbp.setWidth 32).toNat
  · have h1' := eq_true h1
    mcx +contextual [W_127, o7, h1']
  · have h1' := eq_false h1
    by_cases h2 : rbx.setWidth 32 = r13.setWidth 32 + rbp.setWidth 32
    · have h2' := eq_true h2
      mcx +contextual [W_127, o7, h1', h2']
    · have h2' := eq_false h2
      mcx +contextual [W_127, o7, h1', h2']

end FV7z.Fmi
