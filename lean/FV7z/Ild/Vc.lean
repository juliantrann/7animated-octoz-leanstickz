import FV7z.Ild.Steps
import FV7z.Mcn.Vc
/-!
# `_nl_intern_locale_data`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `_nl_intern_locale_data (category, data, datasize)` (at `0x615210`; `edi = c`,
`rsi = data`, `rdx = datasize`). After the prologue (six pushes, `sub rsp, 8`): `rbx = data`, `r12 = datasize`,
`ebp = c`; from 65 on `r13 = N` (the u32 at `data + 4`), `r14 = sext c`. In the loop (196–341) `rax` is the new
block, `rcx` the index `cnt`, `rdx` the jump table (`0x6ee9e0`), `r9 = c`, `r10` the table `_nl_value_types`
(`0x7804c0`).

- `vc_0e` (`datasize ≤ 7`): the pushes, to 248. `vc_0n`: the pushes, `rbx`, `r12`, `ebp`, to the magic check (65).
- `vc_65a`, `vc_65b`, `vc_65c`: a wrong magic, `N` below `_nl_category_num_items[c]`, `4N + 8 ≥ datasize`; to 248.
  `vc_65d`: to the `call` of `malloc` (122) with `rdi = 8N + 64`.
- `vc_127z` (`malloc` gave 0): to 264. `vc_127e`, `vc_127n`: the header stored (`Vh`); `N = 0`: to 264; else the
  loop's registers, to 196.
- `vc_196b` (the offset `idx` past `datasize`): to 240. `vc_196c`, `vc_217`: through the jump table to a case.
- the cases (`vc_ℓt`, `vc_ℓf`): `cnt` against the category's bound, to 288 (or 324, 299) or 240.
- `vc_288a`, `vc_288b`: the value's type a word (5), to 336; else to 299. `vc_299`: the string's address stored.
  `vc_336a`, `vc_336b`: a misaligned word, to 240; else the word stored. `vc_307l`, `vc_307e`: the next `cnt`, or
  the end (264).
- `vc_240`: `rdi = rax`, to the `call` of `free` (243). `vc_248`: `errno = EINVAL`, `rax = 0`. `vc_264`: the pops,
  to the `ret` (278).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6)
namespace FV7z.Ild

/-- `N`, the u32 at `data + 4` (`rbx = data`), zero-extended. -/
abbrev nN (V : Addr → Byte) (g : Gprs) : Addr :=
  BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (g.rbx + 4#64) 4)))

/-- The entry of `_nl_category_num_items` for `c = ebp` (`0x6ef020 + 8c`), and its value. -/
abbrev ia (g : Gprs) : Addr := 7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g.rbp) * 8#64
abbrev nI (V : Addr → Byte) (g : Gprs) : Addr := ofBytesLE 64 (List.map V (byteAddrs (ia g) 8))

/-- The header stored at the new block `rax`. -/
abbrev Vh (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rax + 8#64) (toBytesLE g.rbx 8)) (g.rax + 16#64) (toBytesLE g.r12 8))
    (g.rax + 32#64) (toBytesLE (0#64) 8)) (g.rax + 40#64) (toBytesLE (0#64) 8)) (g.rax + 48#64) (toBytesLE (0#64) 8))
    (g.rax + 56#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4)

/-- The `cnt`-th offset `idx`, the u32 at `data + 8 + 4cnt` (`rcx = cnt`), zero-extended. -/
abbrev ix (V : Addr → Byte) (g : Gprs) : Addr :=
  BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (g.rbx + g.rcx * 4#64 + 8#64) 4)))

/-- The category's type table `_nl_value_types[c]` (read at `r10 + 8 r14`). -/
abbrev tT (V : Addr → Byte) (g : Gprs) : Addr := ofBytesLE 64 (List.map V (byteAddrs (g.r10 + g.r14 * 8#64) 8))

/-- The `cnt`-th value's type. -/
abbrev ty (V : Addr → Byte) (g : Gprs) : BitVec 32 :=
  ofBytesLE 32 (List.map V (byteAddrs (tT V g + g.rcx * 4#64) 4))

/-- The word at `data + idx`. -/
abbrev wd (V : Addr → Byte) (g : Gprs) : BitVec 32 := ofBytesLE 32 (List.map V (byteAddrs (g.rbx + g.rdi) 4))

/-- `c ≤ 12`: the `ja` of `cmp ebp, 12` not taken. -/
theorem nja12 {w : BitVec 32} (h : w.toNat ≤ 12) : (!(decide (w.toNat < 12) || decide (w = 12#32))) = false := by
  by_cases h1 : w.toNat < 12
  · simp [h1]
  · have h2 : w = 12#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    simp [h2]

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- `datasize ≤ 7`: the pushes, to 248. -/
theorem vc_0e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hd : (decide (g.rdx.toNat < 7) || decide (g.rdx = 7#64)) = true)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 248 ∧ V' = fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd w1 w2 w3 w4 w5 w6 ⊢
  mcx +contextual [W_0, o0, fr6, hd, w1, w2, w3, w4, w5, w6]

set_option maxHeartbeats 2000000 in
/-- `datasize > 7`: the pushes, `r12 = datasize`, `ebp = c`, `rbx = data`; to the magic check (65). -/
theorem vc_0n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hd : (decide (g.rdx.toNat < 7) || decide (g.rdx = 7#64)) = false)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add g.rsi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 65 ∧ V' = fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 ∧ g'.rbx = g.rsi ∧ g'.r12 = g.rdx ∧
      g'.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd w1 w2 w3 w4 w5 w6 f1 ⊢
  mcx +contextual [W_0, W_28, W_48, o0, o1, o2, fr6, hd, w1, w2, w3, w4, w5, w6, f1]

/-- A wrong magic: to 248. -/
theorem vc_65a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : ¬ BitVec.setWidth 32 g.rdx = BitVec.setWidth 32 g.rax) :
    W_65 fb F Wl (fun j' g' _ V' => j' = 248 ∧ V' = V ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  mcx +contextual [W_65, o3, hm]

set_option maxHeartbeats 2000000 in
/-- `N` below `_nl_category_num_items[c]`: to 248. -/
theorem vc_65b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : BitVec.setWidth 32 g.rdx = BitVec.setWidth 32 g.rax) (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 4#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (ia g) i)) (hi : (nN V g).toNat < (nI V g).toNat) :
    W_65 fb F Wl (fun j' g' _ V' => j' = 248 ∧ V' = V ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [nN, ia, nI] at hm f1 f2 hi ⊢
  mcx +contextual [W_65, W_73, o3, o4, Op.sxr, not_true_eq_false, hm, f1, f2, hi]

set_option maxHeartbeats 2000000 in
/-- `4N + 8 ≥ datasize`: to 248. -/
theorem vc_65c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : BitVec.setWidth 32 g.rdx = BitVec.setWidth 32 g.rax) (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 4#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (ia g) i)) (hi : ¬ (nN V g).toNat < (nI V g).toNat)
    (h4 : ¬ (nN V g * 4#64 + 8#64).toNat < g.r12.toNat) :
    W_65 fb F Wl (fun j' g' _ V' => j' = 248 ∧ V' = V ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [nN, ia, nI] at hm f1 f2 hi h4 ⊢
  mcx +contextual [W_65, W_73, W_97, o3, o4, o5, Op.sxr, hm, f1, f2, hi, h4]

set_option maxHeartbeats 2000000 in
/-- All checks passed: `r13 = N`, `r14 = sext c`, `rdi = 8N + 64`; to the `call` of `malloc` (122). -/
theorem vc_65d {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : BitVec.setWidth 32 g.rdx = BitVec.setWidth 32 g.rax) (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 4#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (ia g) i)) (hi : ¬ (nN V g).toNat < (nI V g).toNat)
    (h4 : (nN V g * 4#64 + 8#64).toNat < g.r12.toNat) :
    W_65 fb F Wl (fun j' g' _ V' => j' = 122 ∧ V' = V ∧ g' = { g with
      rax := nN V g * 4#64 + 8#64, rdi := nN V g * 8#64 + 64#64, r13 := nN V g,
      r14 := BitVec.signExtend 64 (BitVec.setWidth 32 g.rbp) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [nN, ia, nI] at hm f1 f2 hi h4 ⊢
  mcx +contextual [W_65, W_73, W_97, W_114, o3, o4, o5, o6, Op.sxr, hm, f1, f2, hi, h4]

/-- `malloc` gave 0: to 264. -/
theorem vc_127z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = true) :
    W_127 fb F Wl (fun j' g' _ V' => j' = 264 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_127, o7, hz]

set_option maxHeartbeats 2000000 in
/-- The header stored; `N = 0`: to 264. -/
theorem vc_127e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false)
    (hn : (g.r13 == 0) = true) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 16#64) i)) (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 32#64) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 40#64) i)) (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 48#64) i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (g.rax + 56#64) i)) :
    W_127 fb F Wl (fun j' g' _ V' => j' = 264 ∧ V' = Vh V g ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vh] at hz hn w1 w2 w3 w4 w5 w6 ⊢
  mcx +contextual [W_127, W_136, o7, o8, hz, hn, w1, w2, w3, w4, w5, w6]

set_option maxHeartbeats 2000000 in
/-- The header stored; `N ≠ 0`: `cnt = 0`, the tables; to the loop (196). -/
theorem vc_127n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rax == 0) = false)
    (hn : (g.r13 == 0) = false) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 16#64) i)) (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 32#64) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 40#64) i)) (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 48#64) i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (g.rax + 56#64) i)) :
    W_127 fb F Wl (fun j' g' _ V' => j' = 196 ∧ V' = Vh V g ∧ g' = { g with
      rcx := 0#64, rdx := 7268832#64, r9 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp),
      r10 := 7865536#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vh] at hz hn w1 w2 w3 w4 w5 w6 ⊢
  mcx +contextual [W_127, W_136, W_177, o7, o8, o9, hz, hn, w1, w2, w3, w4, w5, w6]

/-- `idx` past `datasize`: to 240. -/
theorem vc_196b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hb : g.r12.toNat < (ix V g).toNat)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + g.rcx * 4#64 + 8#64) i)) :
    W_196 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = { g with rsi := ix V g, rdi := ix V g }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ix] at hb f1 ⊢
  mcx +contextual [W_196, o10, hb, f1]

/-- `idx ≤ datasize`, `c ≤ 12`: on to the jump (217). -/
theorem vc_196c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hb : ¬ g.r12.toNat < (ix V g).toNat) (hc : (BitVec.setWidth 32 g.rbp).toNat ≤ 12)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + g.rcx * 4#64 + 8#64) i))
    (hk : ∀ fl, W_217 fb F Wl Q { g with rsi := ix V g, rdi := ix V g } fl V) :
    W_196 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ix] at hb hc f1 hk ⊢
  have hj := nja12 hc
  mcx +contextual [W_196, W_208, o10, o11, hb, hj, f1]
  -- `hj` is not used by `simp` (the generated literal `12#32` differs); unify by `Eq.trans`
  exact ⟨fun h => absurd (h.symm.trans hj).symm Bool.false_ne_true, fun _ => hk _⟩

/-- The jump through the table to `ℓ`. -/
theorem vc_217 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {ℓ : Nat}
    (hf : ∀ i < 4, Foot F.data (Addr.add (g.rdx + g.r9 * 4#64) i))
    (ht : BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (g.rdx + g.r9 * 4#64) 4))) + g.rdx =
      Addr.add ild_at ℓ) (hℓ : ℓ < ild.length) (hq : ∀ fl, Q ℓ { g with r8 := Addr.add ild_at ℓ } fl V) :
    W_217 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf ht hq ⊢
  wpx [W_217, o12, Op.ldsx]
  refine ⟨hf, ℓ, hℓ, ht, ?_⟩
  rw [ht]
  exact hq _

/-! ## The cases: `cnt` against the category's bound -/

/-- `228`: `cnt ≤ 1`: to 288. -/
theorem vc_228t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 1) || decide (g.rcx = 1#64)) = true) :
    W_228 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_228, W_234, o13, o14, h]

/-- `228`: `cnt > 1`: to 240. -/
theorem vc_228f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 1) || decide (g.rcx = 1#64)) = false) :
    W_228 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_228, W_234, o13, o14, h]

/-- `279`: `cnt ≤ 4`: to 288. -/
theorem vc_279t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 4) || decide (g.rcx = 4#64)) = true) :
    W_279 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_279, W_285, o18, o19, h]

/-- `279`: `cnt > 4`: to 240. -/
theorem vc_279f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 4) || decide (g.rcx = 4#64)) = false) :
    W_279 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_279, W_285, o18, o19, h]

/-- `350`: `cnt ≤ 6`: to 288. -/
theorem vc_350t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 6) || decide (g.rcx = 6#64)) = true) :
    W_350 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_350, W_356, o27, h]

/-- `350`: `cnt > 6`: to 240. -/
theorem vc_350f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 6) || decide (g.rcx = 6#64)) = false) :
    W_350 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_350, W_356, o27, h]

/-- `358`: `cnt ≤ 2`: to 288. -/
theorem vc_358t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 2) || decide (g.rcx = 2#64)) = true) :
    W_358 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_358, W_364, o28, h]

/-- `358`: `cnt > 2`: to 240. -/
theorem vc_358f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 2) || decide (g.rcx = 2#64)) = false) :
    W_358 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_358, W_364, o28, h]

/-- `369`: `cnt ≤ 15`: to 288. -/
theorem vc_369t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 15) || decide (g.rcx = 15#64)) = true) :
    W_369 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_369, W_375, o29, h]

/-- `369`: `cnt > 15`: to 240. -/
theorem vc_369f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 15) || decide (g.rcx = 15#64)) = false) :
    W_369 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_369, W_375, o29, h]

/-- `380`: `cnt ≤ 45`: to 288. -/
theorem vc_380t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 45) || decide (g.rcx = 45#64)) = true) :
    W_380 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_380, W_386, o30, h]

/-- `380`: `cnt > 45`: to 240. -/
theorem vc_380f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 45) || decide (g.rcx = 45#64)) = false) :
    W_380 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_380, W_386, o30, h]

/-- `391`: `cnt ≤ 18`: to 288. -/
theorem vc_391t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 18) || decide (g.rcx = 18#64)) = true) :
    W_391 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_391, W_397, o31, h]

/-- `391`: `cnt > 18`: to 240. -/
theorem vc_391f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 18) || decide (g.rcx = 18#64)) = false) :
    W_391 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_391, W_397, o31, h]

/-- `402`: `cnt ≤ 158`: to 288. -/
theorem vc_402t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 158) || decide (g.rcx = 158#64)) = true) :
    W_402 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_402, W_415, o32, h]

/-- `402`: `cnt > 158`: to 240. -/
theorem vc_402f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 158) || decide (g.rcx = 158#64)) = false) :
    W_402 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_402, W_415, o32, h]

/-- `420`: `cnt ≤ 5`: to 288. -/
theorem vc_420t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 5) || decide (g.rcx = 5#64)) = true) :
    W_420 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_420, W_430, o33, h]

/-- `420`: `cnt > 5`: to 240. -/
theorem vc_420f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 5) || decide (g.rcx = 5#64)) = false) :
    W_420 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_420, W_430, o33, h]

/-- `318` (`c = 9`): `cnt > 12`: to 240. -/
theorem vc_318f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 12) || decide (g.rcx = 12#64)) = false) :
    W_318 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  mcx +contextual [W_318, o23, h]

set_option maxHeartbeats 2000000 in
/-- `318`: `cnt ≤ 12`, the type a word: to 336. -/
theorem vc_318a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 12) || decide (g.rcx = 12#64)) = true)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r10 + g.r14 * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (tT V g + g.rcx * 4#64) i)) (ht : ty V g = 5#32) :
    W_318 fb F Wl (fun j' g' _ V' => j' = 336 ∧ V' = V ∧ g' = { g with r8 := tT V g }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ty, tT] at h f1 f2 ht ⊢
  mcx +contextual [W_318, W_324, W_335, o23, o20, o24, Op.cmpmi, h, f1, f2, ht]

set_option maxHeartbeats 2000000 in
/-- `318`: `cnt ≤ 12`, the type not a word: to 299. -/
theorem vc_318b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (decide (g.rcx.toNat < 12) || decide (g.rcx = 12#64)) = true)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r10 + g.r14 * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (tT V g + g.rcx * 4#64) i)) (ht : ¬ ty V g = 5#32) :
    W_318 fb F Wl (fun j' g' _ V' => j' = 299 ∧ V' = V ∧ g' = { g with r8 := tT V g }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ty, tT] at h f1 f2 ht ⊢
  mcx +contextual [W_318, W_324, o23, o20, Op.cmpmi, h, f1, f2, ht]

/-- `435` (`c = 0`): `cnt > 85`: to 299. -/
theorem vc_435a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 32 g.rbp == 0) = true)
    (h : (decide (g.rcx.toNat < 85) || decide (g.rcx = 85#64)) = false) :
    W_435 fb F Wl (fun j' g' _ V' => j' = 299 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  mcx +contextual [W_435, W_439, o34, o35, hz, h]
  -- `h` is not used by `simp` (as `hj` in `vc_196c`)
  intro af hC
  have e : (!(decide (rcx.toNat < 85) || decide (rcx = 85#64))) = true := by simp only [h, Bool.not_false]
  exact absurd (hC.symm.trans e) Bool.false_ne_true

/-- `435` (`c = 0`): `cnt ≤ 85`: to 288. -/
theorem vc_435b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 32 g.rbp == 0) = true)
    (h : (decide (g.rcx.toNat < 85) || decide (g.rcx = 85#64)) = true) :
    W_435 fb F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  mcx +contextual [W_435, W_439, W_449, o34, o35, hz, h]
  intro hC
  have e : (!(decide (rcx.toNat < 85) || decide (rcx = 85#64))) = false := by simp only [h, Bool.not_true]
  exact absurd (hC.symm.trans e).symm Bool.false_ne_true

/-! ## The value -/

set_option maxHeartbeats 2000000 in
/-- The type a word: to 336. -/
theorem vc_288a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r10 + g.r14 * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (tT V g + g.rcx * 4#64) i)) (ht : ty V g = 5#32) :
    W_288 fb F Wl (fun j' g' _ V' => j' = 336 ∧ V' = V ∧ g' = { g with r8 := tT V g }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ty, tT] at f1 f2 ht ⊢
  mcx +contextual [W_288, o20, Op.cmpmi, f1, f2, ht]

set_option maxHeartbeats 2000000 in
/-- The type not a word (a string): to 299. -/
theorem vc_288b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r10 + g.r14 * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (tT V g + g.rcx * 4#64) i)) (ht : ¬ ty V g = 5#32) :
    W_288 fb F Wl (fun j' g' _ V' => j' = 299 ∧ V' = V ∧ g' = { g with r8 := tT V g }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ty, tT] at f1 f2 ht ⊢
  mcx +contextual [W_288, o20, Op.cmpmi, f1, f2, ht]

/-- A string: `data + idx` stored at `rax + 8cnt + 64`; to 307. -/
theorem vc_299 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w : ∀ i < 8, Foot Wl (Addr.add (g.rax + g.rcx * 8#64 + 64#64) i)) :
    W_299 fb F Wl (fun j' g' _ V' => j' = 307 ∧
      V' = Vst V (g.rax + g.rcx * 8#64 + 64#64) (toBytesLE (g.rdi + g.rbx) 8) ∧
      g' = { g with rdi := g.rdi + g.rbx }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w ⊢
  mcx +contextual [W_299, o21, w]

/-- A misaligned word: to 240. -/
theorem vc_336a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : (BitVec.setWidth 32 g.rsi &&& 3#32 == 0) = false) :
    W_336 fb F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧
      g' = { g with rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi &&& 3#32) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  mcx +contextual [W_336, o25, hm]

set_option maxHeartbeats 2000000 in
/-- An aligned word: the u32 at `data + idx` stored at `rax + 8cnt + 64`; to 307. -/
theorem vc_336b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : (BitVec.setWidth 32 g.rsi &&& 3#32 == 0) = true) (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + g.rdi) i))
    (w : ∀ i < 4, Foot Wl (Addr.add (g.rax + g.rcx * 8#64 + 64#64) i)) :
    W_336 fb F Wl (fun j' g' _ V' => j' = 307 ∧
      V' = Vst V (g.rax + g.rcx * 8#64 + 64#64) (toBytesLE (wd V g) 4) ∧
      g' = { g with rsi := BitVec.setWidth 64 (wd V g) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [wd] at hm f1 w ⊢
  mcx +contextual [W_336, W_341, o25, o26, hm, f1, w]

/-- Not the last value: `cnt + 1`, to 196. -/
theorem vc_307l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ¬ g.r13 = g.rcx + 1#64) :
    W_307 fb F Wl (fun j' g' _ V' => j' = 196 ∧ V' = V ∧ g' = { g with rcx := g.rcx + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  mcx +contextual [W_307, o22, hl]

/-- The last value: to 264. -/
theorem vc_307e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.r13 = g.rcx + 1#64) :
    W_307 fb F Wl (fun j' g' _ V' => j' = 264 ∧ V' = V ∧ g' = { g with rcx := g.rcx + 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  mcx +contextual [W_307, W_316, o22, he]

/-! ## The way out -/

/-- `rdi = rax`: to the `call` of `free` (243). -/
theorem vc_240 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_240 fb F Wl (fun j' g' _ V' => j' = 243 ∧ V' = V ∧ g' = { g with rdi := g.rax }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_240, o15]

/-- `errno = EINVAL` (22, at `fs - 0x48`), `rax = 0`: to 264. -/
theorem vc_248 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ef : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i)) :
    W_248 fb F Wl (fun j' g' _ V' => j' = 264 ∧ V' = Vst V (fb + 18446744073709551544#64) (toBytesLE (22#32) 4) ∧
      g' = { g with rax := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ef ⊢
  mcx +contextual [W_248, o16, Op.stfi, ef]

set_option maxHeartbeats 2000000 in
/-- `add rsp, 8`, the pops; to the `ret` (278). -/
theorem vc_264 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_264 fb F Wl (fun j' g' _ V' => j' = 278 ∧ V' = V ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rax = g.rax ∧ g'.rbx = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64) 8)) ∧
      g'.rbp = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64 + 8) 8)) ∧
      g'.r12 = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64 + 8 + 8) 8)) ∧
      g'.r13 = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64 + 8 + 8 + 8) 8)) ∧
      g'.r14 = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64 + 8 + 8 + 8 + 8) 8)) ∧
      g'.r15 = ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8) 8))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 p3 p4 p5 ⊢
  mcx +contextual [W_264, o17, p0, p1, p2, p3, p4, p5]

end FV7z.Ild
