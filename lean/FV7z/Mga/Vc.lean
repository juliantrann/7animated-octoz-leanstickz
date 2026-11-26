import FV7z.Mga.Steps
import FV7z.Mcn.Holds
/-!
# `_int_memalign`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `_int_memalign (av, alignment, bytes)` (at `0x631bc0`; `rdi = av`, `rsi = alignment`,
`rdx = bytes`). In the body `rbp = av`, `rbx = alignment`, `r15 = nb`, `r12` the chunk's memory `m` (later the
result), `rsi` the chunk `p = m - 16`, `r13` the aligned chunk `newp` (`brk`), `rcx` its offset `leadsize`, `r14`
`newsize`.

- `nbv`: `checked_request2size (bytes)` as the code computes it; `nmf`: `NON_MAIN_ARENA` of `av`; `brk`: the first
  aligned spot.
- `vc_0n`: the six pushes, `nb`, to the `call` of `_int_malloc` (58); `vc_0e`: `bytes` too big, `errno = ENOMEM`,
  `r12 = 0`, to 341.
- `vc_63z`, `vc_63n`: `_int_malloc` gave 0 (to 341), or not: `p`, to the `div` (81).
- `vc_84a`: `m` aligned, to 254; `vc_84s`, `vc_84b`: `newp` the first aligned spot with room for a chunk before
  it (`leadsize` small: one `alignment` more), to 127.
- `vc_127m`: `p` mmapped: `newp`'s `prev_size` and size, to 341; `vc_127n`: `newsize`, its head with the arena's
  bit, to 175. `vc_175`: `newp`'s head stored, to the `or` (186). `vc_192`: `p`'s head, to the `call` of
  `_int_free` (216).
- `vc_221`: `newsize ≥ nb`, `r12 = newp + 16`, to the `div` (239). `vc_242`: aligned, `p = newp`, to 254.
- `vc_254m`, `vc_254k`: `p` mmapped or no room for a remainder, to 341; `vc_254s`: the remainder split off, to the
  `call` of `_int_free` (336).
- `vc_341`: the epilogue, to the `ret` (358).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6)
namespace FV7z.Mga

/-- `checked_request2size (n)` as the code computes it: `n + 23` with its low 4 bits clear, at least 32. -/
def nbv (n : Addr) : Addr := if (n + 23#64).toNat ≤ 31 then 32#64 else n + 23#64 &&& 18446744073709551600#64

/-- `NON_MAIN_ARENA` for the arena `av` (`main_arena` at `0x792a40`). -/
def nmf (av : Addr) : Addr := if av = 7940672#64 then 0#64 else 4#64

/-- The first spot from `m` aligned to `al`, as a chunk: `((m + al - 1) & -al) - 16`. -/
abbrev brk (m al : Addr) : Addr := (m + al + 18446744073709551615#64 &&& 0 - al) - 16#64

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- The six pushes, `nb`, `rsi = nb + alignment + MINSIZE`; to the `call` of `_int_malloc` (58). -/
theorem vc_0n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) (hms : g.rdx.msb = false) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 58 ∧ V' = fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 ∧ g'.rdi = g.rdi ∧ g'.rsi = nbv g.rdx + g.rsi + 32#64 ∧
      g'.rbx = g.rsi ∧ g'.rbp = g.rdi ∧ g'.r15 = nbv g.rdx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w1 w2 w3 w4 w5 w6 hms ⊢
  by_cases h1 : (rdx + 23#64).toNat < 31
  · have hc : (rdx + 23#64).toNat ≤ 31 := by omega
    have h1' := eq_true h1
    mcx +contextual [W_0, W_23, o0, o1, fr6, nbv, h1', hc, hms, w1, w2, w3, w4, w5, w6]
  · have h1' := eq_false h1
    by_cases h2 : rdx + 23#64 = 31#64
    · have hc : (rdx + 23#64).toNat ≤ 31 := by rw [h2]; decide
      have h2' := eq_true h2
      mcx +contextual [W_0, W_23, o0, o1, fr6, nbv, h1', h2', hc, hms, w1, w2, w3, w4, w5, w6]
    · have hc : ¬ (rdx + 23#64).toNat ≤ 31 := fun h =>
        h2 (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega))
      have h2' := eq_false h2
      mcx +contextual [W_0, W_23, o0, o1, fr6, nbv, h1', h2', hc, hms, w1, w2, w3, w4, w5, w6]

set_option maxHeartbeats 2000000 in
/-- `bytes` above `PTRDIFF_MAX`: `errno = ENOMEM` (`fs:-0x48`), `r12 = 0`; to 341. -/
theorem vc_0e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (we : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i)) (hms : g.rdx.msb = true) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 341 ∧
      V' = Vst (fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx) (fb + 18446744073709551544#64)
        (toBytesLE 12#32 4) ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 ∧ g'.r12 = 0#64) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w1 w2 w3 w4 w5 w6 hms ⊢
  mcx +contextual [W_0, W_368, o0, o18, Op.stfi, fr6, hms, w1, w2, w3, w4, w5, w6, we]

/-- `_int_malloc` gave 0: to 341 (`r12 = 0`). -/
theorem vc_63z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax = 0#64) :
    W_63 fb F Wl (fun j' g' _ V' => j' = 341 ∧ V' = V ∧ g' = { g with r12 := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  mcx +contextual [W_63, o2]

/-- `_int_malloc` gave `m`, not 0: `r12 = m`, `rdx = 0`, `rsi = p`; to the `div` (81). -/
theorem vc_63n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false) :
    W_63 fb F Wl (fun j' g' _ V' => j' = 81 ∧ V' = V ∧
      g' = { g with r12 := g.rax, rdx := 0#64, rsi := g.rax + 18446744073709551600#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_63, W_75, o2, o3, hz]

/-- `m` aligned: to 254. -/
theorem vc_84a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rdx = 0#64) :
    W_84 fb F Wl (fun j' g' _ V' => j' = 254 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  mcx +contextual [W_84, o4]

/-- `m` not aligned, `brk - p ≤ 31`: `newp = brk + alignment`, `leadsize = newp - p`; to 127. -/
theorem vc_84s {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rdx == 0) = false)
    (hc : (brk g.r12 g.rbx - g.rsi).toNat ≤ 31) :
    W_84 fb F Wl (fun j' g' _ V' => j' = 127 ∧ V' = V ∧ g'.r13 = brk g.r12 g.rbx + g.rbx ∧
      g'.rcx = brk g.r12 g.rbx + g.rbx - g.rsi ∧ g'.r12 = g.r12 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧
      g'.r15 = g.r15 ∧ g'.rsi = g.rsi ∧ g'.rsp = g.rsp ∧ g'.rdi = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [brk] at hz hc ⊢
  by_cases h1 : ((r12 + rbx + 18446744073709551615#64 &&& 0 - rbx) - 16#64 - rsi).toNat < 31
  · have h1' := eq_true h1
    mcx +contextual [W_84, W_93, W_392, o4, o5, o19, hz, h1']
  · have h1' := eq_false h1
    have h2 : (r12 + rbx + 18446744073709551615#64 &&& 0 - rbx) - 16#64 - rsi = 31#64 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
    have h2' := eq_true h2
    mcx +contextual [W_84, W_93, W_392, o4, o5, o19, hz, h1', h2']

/-- `m` not aligned, `brk - p > 31`: `newp = brk`, `leadsize = newp - p`; to 127. -/
theorem vc_84b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rdx == 0) = false)
    (hc : ¬ (brk g.r12 g.rbx - g.rsi).toNat ≤ 31) :
    W_84 fb F Wl (fun j' g' _ V' => j' = 127 ∧ V' = V ∧ g'.r13 = brk g.r12 g.rbx ∧
      g'.rcx = brk g.r12 g.rbx - g.rsi ∧ g'.r12 = g.r12 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧
      g'.r15 = g.r15 ∧ g'.rsi = g.rsi ∧ g'.rsp = g.rsp ∧ g'.rdi = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [brk] at hz hc ⊢
  have h1' := eq_false (show ¬ ((r12 + rbx + 18446744073709551615#64 &&& 0 - rbx) - 16#64 - rsi).toNat < 31 by
    omega)
  have h2' := eq_false (show ¬ (r12 + rbx + 18446744073709551615#64 &&& 0 - rbx) - 16#64 - rsi = 31#64 from
    fun h => hc (by rw [h]; decide))
  mcx +contextual [W_84, W_93, o4, o5, hz, h1', h2']

/-- `p` mmapped (`Z` its size word): `newp->prev_size = prev_size (p) + leadsize`, `newp`'s size
`newsize | IS_MMAPPED`, `r12 = newp + 16`; to 341. -/
theorem vc_127m {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hZ : rdq(V, g.r12 + 18446744073709551608#64) = Z) (hb : (Z.setWidth 32 &&& 2#32 == 0) = false)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 18446744073709551608#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 18446744073709551600#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add g.r13 i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.r13 + 8#64) i)) :
    W_127 fb F Wl (fun j' g' _ V' => j' = 341 ∧
      V' = Vst (Vst V g.r13 (toBytesLE (g.rcx + rdq(V, g.r12 + 18446744073709551600#64)) 8)) (g.r13 + 8#64)
        (toBytesLE ((Z &&& 18446744073709551608#64) - g.rcx ||| 2#64) 8) ∧
      g'.r12 = g.r13 + 16#64 ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hZ f1 f2 w1 w2 ⊢
  mcx +contextual [W_127, W_416, o6, o20, hZ, hb, f1, f2, w1, w2]

set_option maxHeartbeats 2000000 in
/-- `p` not mmapped: `newsize`, `rdx = newsize | NON_MAIN_ARENA`; to 175. -/
theorem vc_127n {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hZ : rdq(V, g.r12 + 18446744073709551608#64) = Z) (hb : (Z.setWidth 32 &&& 2#32 == 0) = true)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 18446744073709551608#64) i)) :
    W_127 fb F Wl (fun j' g' _ V' => j' = 175 ∧ V' = V ∧ g'.rax = nmf g.rbp ∧
      g'.rdx = (Z &&& 18446744073709551608#64) - g.rcx ||| nmf g.rbp ∧
      g'.r14 = (Z &&& 18446744073709551608#64) - g.rcx ∧ g'.rcx = g.rcx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧
      g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r15 = g.r15 ∧ g'.rsi = g.rsi ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hZ f1 ⊢
  have hb0 : Z.setWidth 32 &&& 2#32 = 0#32 := by simpa using hb
  by_cases ha : rbp = 7940672#64
  · subst ha
    mcx +contextual [W_127, W_151, W_166, o6, o7, o8, nmf, hZ, hb, hb0, f1, not_true_eq_false]
  · mcx +contextual [W_127, W_151, W_166, o6, o7, o8, nmf, hZ, hb, hb0, ha, f1, not_true_eq_false]

/-- `set_head (newp, newsize | PREV_INUSE | …)`, `rdi = av`; to the `or` (186). -/
theorem vc_175 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.r13 + 8#64) i)) :
    W_175 fb F Wl (fun j' g' _ V' => j' = 186 ∧ V' = Vst V (g.r13 + 8#64) (toBytesLE (g.rdx ||| 1#64) 8) ∧
      g' = { g with rdx := g.rdx ||| 1#64, rdi := g.rbp }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w1 ⊢
  mcx +contextual [W_175, o9, w1]

/-- `set_head_size (p, leadsize | …)` (`p`'s low bits kept), `rdx = 1`; to the `call` of `_int_free` (216). -/
theorem vc_192 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 18446744073709551608#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 18446744073709551608#64) i)) :
    W_192 fb F Wl (fun j' g' _ V' => j' = 216 ∧
      V' = Vst V (g.r12 + 18446744073709551608#64) (toBytesLE (g.rax |||
        ((rdq(V, g.r12 + 18446744073709551608#64).setWidth 32 &&& 7#32).setWidth 64 ||| g.rcx)) 8) ∧
      g' = { g with rdx := 1#64, rax := g.rax |||
        ((rdq(V, g.r12 + 18446744073709551608#64).setWidth 32 &&& 7#32).setWidth 64 ||| g.rcx) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 w1 ⊢
  mcx +contextual [W_192, o10, f1, w1]

/-- `newsize ≥ nb`: `r12 = newp + 16`, `rdx = 0`; to the `div` (239). -/
theorem vc_221 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hge : g.r15.toNat ≤ g.r14.toNat) :
    W_221 fb F Wl (fun j' g' _ V' => j' = 239 ∧ V' = V ∧
      g' = { g with r12 := g.r13 + 16#64, rdx := 0#64, rax := g.r13 + 16#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hge ⊢
  have hlt : ¬ r14.toNat < r15.toNat := by omega
  mcx +contextual [W_221, W_230, o11, o12, hlt]

/-- `newp + 16` aligned: `p = newp`; to 254. -/
theorem vc_242 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rdx = 0#64) :
    W_242 fb F Wl (fun j' g' _ V' => j' = 254 ∧ V' = V ∧ g' = { g with rsi := g.r13 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  mcx +contextual [W_242, W_251, o4, o13]

/-- `p` mmapped (`Z` its size word): to 341. -/
theorem vc_254m {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hZ : rdq(V, g.rsi + 8#64) = Z) (hb : (Z.setWidth 8 &&& 2#8 == 0) = false)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_254 fb F Wl (fun j' g' _ V' => j' = 341 ∧ V' = V ∧ g' = { g with rax := Z }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hZ f1 ⊢
  mcx +contextual [W_254, o14, hZ, hb, f1]

/-- `p` not mmapped, `size ≤ nb + MINSIZE`: to 341. -/
theorem vc_254k {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hZ : rdq(V, g.rsi + 8#64) = Z) (hb : (Z.setWidth 8 &&& 2#8 == 0) = true)
    (hk : (Z &&& 18446744073709551608#64).toNat ≤ (g.r15 + 32#64).toNat)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_254 fb F Wl (fun j' g' _ V' => j' = 341 ∧ V' = V ∧
      g' = { g with rax := Z &&& 18446744073709551608#64, rdx := g.r15 + 32#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hZ hk f1 ⊢
  have hlt : ¬ (r15 + 32#64).toNat < (Z &&& 18446744073709551608#64).toNat := by omega
  mcx +contextual [W_254, W_262, o14, o15, hZ, hb, hlt, f1]

set_option maxHeartbeats 2000000 in
/-- `size > nb + MINSIZE`: the remainder `p + nb` with head `size - nb | PREV_INUSE | …`, `p`'s size `nb` (its low
bits kept), `rsi` the remainder, `rdi = av`, `rdx = 1`; to the `call` of `_int_free` (336). -/
theorem vc_254s {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hZ : rdq(V, g.rsi + 8#64) = Z) (hb : (Z.setWidth 8 &&& 2#8 == 0) = true)
    (hs : (g.r15 + 32#64).toNat < (Z &&& 18446744073709551608#64).toNat)
    (hZ' : rdq(Vst V (g.rsi + g.r15 + 8#64)
      (toBytesLE ((Z &&& 18446744073709551608#64) - g.r15 ||| nmf g.rbp ||| 1#64) 8), g.rsi + 8#64) = Z)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsi + 8#64) i)) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsi + 8#64) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsi + g.r15 + 8#64) i)) :
    W_254 fb F Wl (fun j' g' _ V' => j' = 336 ∧
      V' = Vst (Vst V (g.rsi + g.r15 + 8#64)
        (toBytesLE ((Z &&& 18446744073709551608#64) - g.r15 ||| nmf g.rbp ||| 1#64) 8)) (g.rsi + 8#64)
        (toBytesLE (g.r15 ||| (Z.setWidth 32 &&& 7#32).setWidth 64) 8) ∧
      g'.rsi = g.rsi + g.r15 ∧ g'.rdi = g.rbp ∧ g'.rdx = 1#64 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧
      g'.r12 = g.r12 ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hZ hs hZ' f1 w1 w2 ⊢
  have hlt : ¬ (r15 + 32#64).toNat ≥ (Z &&& 18446744073709551608#64).toNat := by omega
  by_cases ha : rbp = 7940672#64
  · subst ha
    simp only [nmf, ite_true, eq_self_iff_true, BitVec.or_zero] at hZ' w2 ⊢
    mcx +contextual [W_254, W_262, W_275, o14, o15, o16, hZ, hZ', hb, hs, hlt, f1, w1, w2]
  · simp only [nmf, ha, ite_false] at hZ' w2 ⊢
    mcx +contextual [W_254, W_262, W_275, o14, o15, o16, hZ, hZ', hb, hs, hlt, ha, f1, w1, w2]

set_option maxHeartbeats 2000000 in
/-- The epilogue: `rax = r12`, the pops; to the `ret` (358). -/
theorem vc_341 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_341 fb F Wl (fun j' g' _ V' => j' = 358 ∧ V' = V ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rax = g.r12 ∧ g'.rbx = rdq(V, g.rsp + 8#64) ∧ g'.rbp = rdq(V, g.rsp + 8#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 p3 p4 p5 ⊢
  mcx +contextual [W_341, o17, p0, p1, p2, p3, p4, p5]

end FV7z.Mga
