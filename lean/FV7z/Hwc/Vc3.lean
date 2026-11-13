import FV7z.Hwc.Vc
import FV7z.Lemmas.Ksplit
/-!
# `_dl_important_hwcaps`: the lengths and the pointers of the result, the return (PLAN.md G3, startup)

After the strings (`Vc2`), with `E = 2^cnt` entries of 16 bytes at `r14` (the result `P`):

- `vc_1392l`, `vc_1392e`: `result[i].len = 0` for `i < E`; after the last, `2^cnt` (`rbp - 0x88`, not 0) and
  `16 cnt` (`rbp - 0x98`) back, `rbx = &temp[cnt]`, to the loop over the capabilities (1448).
- `vc_1448`: the capability `c - 1` (`rcx = c`), its mask `2^(c-1)` in `rsi`, `rax = E`, `rdx = P` (1465).
- `vc_1465`, `vc_1478`: one entry, `rax - 1` (`m`), `rdx + 16`: if bit `c - 1` of `m` is set, `len += temp.len + 1`
  (1478, the run of entries with it set); to 1508 when it is clear.
- `vc_1508l`, `vc_1508e`: `m ≠ 0`: the next entry (1465); `m = 0`: `rbx - 16`, the next capability (1448) or none
  (1522).
- `vc_1522`: `2^cnt - 2` (`rbp - 0x8c`), `2^(cnt-1)` (`rbp - 0x78` the byte `cnt - 1`), `rsi = rax = P + 32` (1568).
- `vc_1568o`, `vc_1568e`: the entry at `rax`: `str = [rax - 32] + [rax - 24]` (`n - 1` odd) or `[rax - 16]` (even);
  to 1568 or, at `2^(cnt-1)`, 1602.
- `vc_1602`, `vc_1612`: the second half: `rsi` to its first entry, `rdx = -16·2^(cnt-1)`, `rdi = temp[cnt-1].len + 1`
  (1632).
- `vc_1632l`, `vc_1632e`: `str = [rsi + rdx] + rdi`; after the last, `*max_capstrlen = result[0].len`, the frame
  popped: to the `ret` (1681) with `rax = P`.

The branches are decided by the literals (`ksplit`, `rcases`) or by a `by_cases` on the `test` (`if` in the post).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

set_option maxRecDepth 100000

variable {F : Footprint} {Wl : List Rgn} {fb : Addr}

/-- `result[i].len = 0`, `i + 1 < E`: on to `i + 1` (1392). -/
theorem vc_1392l {g : Gprs} {f : Rflags} {V : Addr → Byte} {i E : Nat}
    (hE : E = 8 ∧ i ≤ 6 ∨ E = 16 ∧ i ≤ 14) (ha : g.rax = BitVec.ofNat 64 i) (hc : g.rcx = BitVec.ofNat 64 E)
    (hs : ∀ k < 8, Foot Wl (Addr.add (g.r14 + BitVec.ofNat 64 (16 * i + 8)) k)) :
    W_1392 fb F Wl (fun j' g' _ V' => j' = 1392 ∧
      g' = { g with rax := BitVec.ofNat 64 (i + 1), rdx := BitVec.ofNat 64 (16 * i) } ∧
      V' = Vst V (g.r14 + BitVec.ofNat 64 (16 * i + 8)) (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hc hs ⊢
  subst ha hc
  have h0 := Nat.zero_le i
  rcases hE with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · ksplit i from 0 to 6 using h0 hi
    all_goals
      simp only [Nat.reduceMul, Nat.reduceAdd] at hs ⊢
      hwx [W_1392, o32, Op.shl64]
      hcl
  · ksplit i from 0 to 14 using h0 hi
    all_goals
      simp only [Nat.reduceMul, Nat.reduceAdd] at hs ⊢
      hwx [W_1392, o32, Op.shl64]
      hcl

/-- The last `result[E-1].len = 0`: `2^cnt = E` (`rbp - 0x88`) and `16 cnt = D` (`rbp - 0x98`) back,
`rbx + D` (`&temp[cnt]`), `rdi = 1`, `rcx = cnt` (`r12`): to the loop over the capabilities (1448). -/
theorem vc_1392e {g : Gprs} {f : Rflags} {V : Addr → Byte} {E D : Nat} (hE : E = 8 ∧ D = 48 ∨ E = 16 ∧ D = 64)
    (ha : g.rax = BitVec.ofNat 64 (E - 1)) (hc : g.rcx = BitVec.ofNat 64 E)
    (hR : rdq(Vst V (g.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (toBytesLE 0#64 8),
      g.rbp + 18446744073709551480#64) = BitVec.ofNat 64 E)
    (hD : rdq(Vst V (g.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (toBytesLE 0#64 8),
      g.rbp + 18446744073709551464#64) = BitVec.ofNat 64 D)
    (hs : ∀ k < 8, Foot Wl (Addr.add (g.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) k))
    (hf1 : ∀ k < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551480#64) k))
    (hf2 : ∀ k < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551464#64) k)) :
    W_1392 fb F Wl (fun j' g' _ V' => j' = 1448 ∧
      g' = { g with
        rax := BitVec.ofNat 64 E, rcx := g.r12, rdx := BitVec.ofNat 64 (16 * (E - 1)),
        rbx := g.rbx + BitVec.ofNat 64 D, rdi := 1#64, r10 := BitVec.ofNat 64 E } ∧
      V' = Vst V (g.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hc hR hD hs hf1 hf2 ⊢
  subst ha hc
  rcases hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hR hD hs ⊢
    hwx [W_1392, W_1417, W_1429, o32, o33, o34, Op.shl64, hR, hD]
    hcl

/-- The capability `c - 1` (`rcx = c`, `rdi = 1`): the mask `2^(c-1)` (`shl esi, cl`, `movsxd`), `rdx = P`,
`rax = E` (`r10`): to the first entry (1465). -/
theorem vc_1448 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c : Nat} (hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4)
    (hr : g.rcx = BitVec.ofNat 64 c) (hd : g.rdi = 1#64) :
    W_1448 fb F Wl (fun j' g' _ V' => j' = 1465 ∧
      g' = { g with
        rax := g.r10, rcx := BitVec.ofNat 64 (c - 1), rdx := g.r14,
        rsi := BitVec.ofNat 64 (2 ^ (c - 1)) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hd ⊢
  subst hr hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals
    hwx [W_1448, o35, Op.shl, Op.sxr]
    hcl

/-- One entry (`rax - 1 = m`, `rdx + 16`): bit `c - 1` of `m` clear: to 1508; set: to 1478. -/
theorem vc_1465 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1465 fb F Wl (fun j' g' _ V' =>
      j' = (if g.rsi &&& (g.rax - 1#64) = 0#64 then 1508 else 1478) ∧
      g' = { g with rax := g.rax - 1#64, rdx := g.rdx + 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only
  by_cases hz : rsi &&& (rax - 1#64) = 0#64
  · have hz' : (rsi &&& (rax - 1#64) == 0#64) = true := by simp only [hz, beq_self_eq_true]
    hwx [W_1465, o36, hz', hz, eq_self_iff_true]
    hcl
  · have hz' : (rsi &&& (rax - 1#64) == 0#64) = false := by simp only [beq_eq_false_iff_ne]; exact hz
    hwx [W_1465, o36, hz', hz]
    hcl

/-- An entry with bit `c - 1` set: `len` (`L` at `rdx - 8`) plus `temp.len` (`T` at `rbx - 8`) plus 1; the next
(`rax - 1`, `rdx + 16`): set, again (1478); clear, to 1508. -/
theorem vc_1478 {g : Gprs} {f : Rflags} {V : Addr → Byte} {L T : Addr}
    (hL : rdq(V, g.rdx + 18446744073709551608#64) = L) (hT : rdq(V, g.rbx + 18446744073709551608#64) = T)
    (hf1 : ∀ k < 8, Foot F.data (Addr.add (g.rdx + 18446744073709551608#64) k))
    (hf2 : ∀ k < 8, Foot F.data (Addr.add (g.rbx + 18446744073709551608#64) k))
    (hs : ∀ k < 8, Foot Wl (Addr.add (g.rdx + 18446744073709551608#64) k)) :
    W_1478 fb F Wl (fun j' g' _ V' =>
      j' = (if g.rsi &&& (g.rax - 1#64) = 0#64 then 1508 else 1478) ∧
      g' = { g with rax := g.rax - 1#64, rdx := g.rdx + 16#64, r8 := L + T + 1#64, r9 := L } ∧
      V' = Vst V (g.rdx + 18446744073709551608#64) (toBytesLE (L + T + 1#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hL hT hf1 hf2 hs ⊢
  by_cases hz : rsi &&& (rax - 1#64) = 0#64
  · have hz' : (rsi &&& (rax - 1#64) == 0#64) = true := by simp only [hz, beq_self_eq_true]
    hwx [W_1478, o37, hL, hT, hz', hz, eq_self_iff_true]
    hcl
  · have hz' : (rsi &&& (rax - 1#64) == 0#64) = false := by simp only [beq_eq_false_iff_ne]; exact hz
    hwx [W_1478, o37, hL, hT, hz', hz]
    hcl

/-- Entries remain (`rax ≠ 0`): the next (1465). -/
theorem vc_1508l {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax ≠ 0#64) :
    W_1508 fb F Wl (fun j' g' _ V' => j' = 1465 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha ⊢
  have ha' : (rax == 0#64) = false := beq_eq_false_iff_ne.2 ha
  hwx [W_1508, o38, ha']
  hcl

/-- The entries done (`rax = 0`): `rbx - 16` (the next `temp`); a capability left (`rcx ≠ 0`): 1448; else 1522. -/
theorem vc_1508e {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : g.rax = 0#64) :
    W_1508 fb F Wl (fun j' g' _ V' => j' = (if g.rcx = 0#64 then 1522 else 1448) ∧
      g' = { g with rbx := g.rbx - 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha ⊢
  subst ha
  by_cases hz : rcx = 0#64
  · subst hz
    hwx [W_1508, W_1513, o38, o39, eq_self_iff_true]
    hcl
  · have hz' : (rcx == 0#64) = false := beq_eq_false_iff_ne.2 hz
    hwx [W_1508, W_1513, o38, o39, hz', hz]
    hcl

/-- The pointers: `r8 = E - 2` (`rbp - 0x8c`, 32 bits), `rcx = 2^(cnt-1)` (the byte `cnt - 1` at `rbp - 0x78`),
`rsi = rax = P + 32` (`&result[2]`), `rdx = E - 2`: not equal, to the loop (1568). -/
theorem vc_1522 {g : Gprs} {f : Rflags} {V : Addr → Byte} {n E : Nat} (hn : n = 3 ∧ E = 8 ∨ n = 4 ∧ E = 16)
    (hE : rdd(V, g.rbp + 18446744073709551476#64) = BitVec.ofNat 32 E)
    (hm : ofBytesLE 8 (List.map V (byteAddrs (g.rbp + 18446744073709551496#64) 1)) = BitVec.ofNat 8 (n - 1))
    (hf1 : ∀ k < 4, Foot F.data (Addr.add (g.rbp + 18446744073709551476#64) k))
    (hf2 : ∀ k < 1, Foot F.data (Addr.add (g.rbp + 18446744073709551496#64) k)) :
    W_1522 fb F Wl (fun j' g' _ V' => j' = 1568 ∧
      g' = { g with
        rax := g.r14 + 32#64, rcx := BitVec.ofNat 64 (2 ^ (n - 1)), rdx := BitVec.ofNat 64 (E - 2),
        rsi := g.r14 + 32#64, r8 := BitVec.ofNat 64 (E - 2) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hE hm hf1 hf2 ⊢
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Nat.reduceSub] at hm ⊢
    hwx [W_1522, W_1560, o40, o41, Op.shl64, Op.sxr, hE, hm]
    hcl

/-- `rdx = d`, `d - 1` odd: `result[i].str = result[i-2].str + result[i-2].len` (`S`, `L` at `rax - 32`,
`rax - 24`), stored at `rax`; `rax + 16`; `d - 1 ≠ 2^(cnt-1)`: on (1568). -/
theorem vc_1568o {g : Gprs} {f : Rflags} {V : Addr → Byte} {c d : Nat} {S L : Addr}
    (hd : c = 4 ∧ d = 6 ∨ c = 8 ∧ (d = 14 ∨ d = 12 ∨ d = 10))
    (hr : g.rdx = BitVec.ofNat 64 d) (hc : g.rcx = BitVec.ofNat 64 c)
    (hL : rdq(V, g.rax + 18446744073709551592#64) = L) (hS : rdq(V, g.rax + 18446744073709551584#64) = S)
    (hf1 : ∀ k < 8, Foot F.data (Addr.add (g.rax + 18446744073709551592#64) k))
    (hf2 : ∀ k < 8, Foot F.data (Addr.add (g.rax + 18446744073709551584#64) k))
    (hs : ∀ k < 8, Foot Wl (Addr.add g.rax k)) :
    W_1568 fb F Wl (fun j' g' _ V' => j' = 1568 ∧
      g' = { g with rax := g.rax + 16#64, rdx := BitVec.ofNat 64 (d - 1), rdi := L + S } ∧
      V' = Vst V g.rax (toBytesLE (L + S) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hc hL hS hf1 hf2 hs ⊢
  subst hr hc
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
  all_goals
    hwx [W_1568, W_1581, o42, o43, Op.addm, hL, hS]
    hcl

/-- `rdx = d`, `d - 1` even: `result[i].str = result[i-1].str` (`S` at `rax - 16`), stored at `rax`; `rax + 16`;
on (1568), or to the second half (1602) at `d - 1 = 2^(cnt-1)`. -/
theorem vc_1568e {g : Gprs} {f : Rflags} {V : Addr → Byte} {c d : Nat} {S : Addr}
    (hd : c = 4 ∧ d = 5 ∨ c = 8 ∧ (d = 13 ∨ d = 11 ∨ d = 9))
    (hr : g.rdx = BitVec.ofNat 64 d) (hc : g.rcx = BitVec.ofNat 64 c)
    (hS : rdq(V, g.rax + 18446744073709551600#64) = S)
    (hf : ∀ k < 8, Foot F.data (Addr.add (g.rax + 18446744073709551600#64) k))
    (hs : ∀ k < 8, Foot Wl (Addr.add g.rax k)) :
    W_1568 fb F Wl (fun j' g' _ V' => j' = (if d = c + 1 then 1602 else 1568) ∧
      g' = { g with rax := g.rax + 16#64, rdx := BitVec.ofNat 64 (d - 1), rdi := S } ∧
      V' = Vst V g.rax (toBytesLE S 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hc hS hf hs ⊢
  subst hr hc
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
  all_goals
    hwx [W_1568, W_2040, W_2061, o42, o59, hS]
    hcl

/-- The second half: `rsi + 16 (E - 2 - 2^(cnt-1))` (`r8 = E - 2`, `rcx = 2^(cnt-1)`): to 1612. -/
theorem vc_1602 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c E : Nat} (hn : c = 4 ∧ E = 8 ∨ c = 8 ∧ E = 16)
    (h8 : g.r8 = BitVec.ofNat 64 (E - 2)) (hc : g.rcx = BitVec.ofNat 64 c) :
    W_1602 fb F Wl (fun j' g' _ V' => j' = 1612 ∧
      g' = { g with rsi := g.rsi + BitVec.ofNat 64 (16 * (E - 2 - c)), r8 := BitVec.ofNat 64 (16 * (E - 2 - c)) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hc ⊢
  subst h8 hc
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Nat.reduceSub, Nat.reduceMul]
    hwx [W_1602, o44, Op.shl64]
    hcl

/-- `rdx = -16·2^(cnt-1)` (`rbp - 0x68`, 32 bits, negated, sign-extended), `rdi = T + 1` (`temp[cnt-1].len` at
`rbp - 0x50`): to the loop of the second half (1632). -/
theorem vc_1612 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c : Nat} {T : Addr} (hc : c = 4 ∨ c = 8)
    (hq : rdd(V, g.rbp + 18446744073709551512#64) = BitVec.ofNat 32 c)
    (hT : rdq(V, g.rbp + 18446744073709551536#64) = T)
    (hf1 : ∀ k < 4, Foot F.data (Addr.add (g.rbp + 18446744073709551512#64) k))
    (hf2 : ∀ k < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551536#64) k)) :
    W_1612 fb F Wl (fun j' g' _ V' => j' = 1632 ∧
      g' = { g with rdx := 0#64 - BitVec.ofNat 64 (16 * c), rdi := T + 1#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq hT hf1 hf2 ⊢
  rcases hc with rfl | rfl
  all_goals
    simp only [Nat.reduceMul]
    hwx [W_1612, o45, Op.sxr, Op.shl64, hq, hT]
    hcl

/-- `result[i].str = result[i - 2^(cnt-1)].str + rdi` (`X` at `rsi + rdx`), stored at `rsi`; `rcx = k` left,
`k - 1 ≠ 0`: again (1632). -/
theorem vc_1632l {g : Gprs} {f : Rflags} {V : Addr → Byte} {k : Nat} {X : Addr} (hk1 : 2 ≤ k) (hk2 : k ≤ 8)
    (hc : g.rcx = BitVec.ofNat 64 k) (hX : rdq(V, g.rsi + g.rdx) = X)
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rsi + g.rdx) i)) (hs : ∀ i < 8, Foot Wl (Addr.add g.rsi i)) :
    W_1632 fb F Wl (fun j' g' _ V' => j' = 1632 ∧
      g' = { g with rax := X + g.rdi, rcx := BitVec.ofNat 64 (k - 1), rsi := g.rsi + 16#64 } ∧
      V' = Vst V g.rsi (toBytesLE (X + g.rdi) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hX hf hs ⊢
  subst hc
  ksplit k from 2 to 8 using hk1 hk2
  all_goals
    simp only [Nat.reduceSub]
    hwx [W_1632, o46, hX]
    hcl

/-- The last (`rcx = 1`): then `*max_capstrlen = result[0].len` (`M` at `P + 8`, the pointer `Q` at
`rbp - 0x70`), `rsp = rbp - 0x28`, `rax = P`, `rbx`, `r12` … `r15`, `rbp` popped (`B0` … `B5`): to the `ret`
(1681) with `rsp = rbp + 8`. -/
theorem vc_1632e {g : Gprs} {f : Rflags} {V : Addr → Byte} {X M Q B0 B1 B2 B3 B4 B5 : Addr}
    (hc : g.rcx = 1#64) (hX : rdq(V, g.rsi + g.rdx) = X)
    (hM : rdq(Vst V g.rsi (toBytesLE (X + g.rdi) 8), g.r14 + 8#64) = M)
    (hQ : rdq(Vst V g.rsi (toBytesLE (X + g.rdi) 8), g.rbp + 18446744073709551504#64) = Q)
    (h0 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp + 18446744073709551576#64) = B0)
    (h1 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp + 18446744073709551584#64) = B1)
    (h2 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp + 18446744073709551592#64) = B2)
    (h3 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp + 18446744073709551600#64) = B3)
    (h4 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp + 18446744073709551608#64) = B4)
    (h5 : rdq(Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8), g.rbp) = B5)
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rsi + g.rdx) i)) (hs : ∀ i < 8, Foot Wl (Addr.add g.rsi i))
    (hfM : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 8#64) i))
    (hfQ : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551504#64) i))
    (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hf0 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551576#64) i))
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551584#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551592#64) i))
    (hf3 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551600#64) i))
    (hf4 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551608#64) i))
    (hf5 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) :
    W_1632 fb F Wl (fun j' g' _ V' => j' = 1681 ∧
      g' = { g with
        rax := g.r14, rcx := 0#64, rsi := g.rsi + 16#64, rbx := B0, r12 := B1, r13 := B2, r14 := B3,
        r15 := B4, rbp := B5, rsp := g.rbp + 8#64 } ∧
      V' = Vst (Vst V g.rsi (toBytesLE (X + g.rdi) 8)) Q (toBytesLE M 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hX hM hQ h0 h1 h2 h3 h4 h5 hf hs hfM hfQ hsQ hf0 hf1 hf2 hf3 hf4 hf5 ⊢
  subst hc
  hwx [W_1632, W_1653, W_1664, o46, o47, o48, Op.pop, hX, hM, hQ, h0, h1, h2, h3, h4, h5]
  hcl

end FV7z.Hwc
