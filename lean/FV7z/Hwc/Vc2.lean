import FV7z.Hwc.Vc
/-!
# `_dl_important_hwcaps`: the strings of the combinations (PLAN.md G3, startup)

The loop from 1248 to 1365 writes, for `n` from `2^(cnt-1) - 2` down to 0 (step 2), the strings
`temp[cnt-1]`, `temp[m]` for the bits `m` of `n` (`cnt - 2 ≥ m ≥ 1`), `temp[0]`, each followed by `/`, through
`mempcpy` (the `call`s at 1260, 1325, 1350). The pieces between the `call`s; each reads the frame and `temp` by
hypotheses on the bytes, and stores only the `/` (one byte at `rax`, in the result).

- `vc_1248`: `temp[cnt-1]` (`rbp - 0x58`, `rbp - 0x50`), `n - 2`, to the `call` (1260).
- `vc_1265`: `/`, `m = cnt - 2` (`rbp - 0x60`), to 1294.
- `vc_1294c`: bit `m` of `n` clear, `m - 1`: to 1343 (`m = 1`) or 1294; `vc_1294s`: set: `temp[m]`, to the `call`
  (1325).
- `vc_1330`: `/`, `m - 1`: to 1294 or 1343.
- `vc_1343`: `temp[0]` (`rbp - 0x48`, `r15`), to the `call` (1350).
- `vc_1355l`: `/`, `n ≠ 0`: to 1248; `vc_1355e`: `n = 0`: `cnt`, the result, `2^cnt` back from the frame, to the loop
  that zeroes the lengths (1392).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

set_option maxRecDepth 100000

variable {F : Footprint} {Wl : List Rgn} {fb : Addr}

/-- `temp[cnt-1]` (string `S`, length `L`) from the frame, `n - 2`: to the `call` of `mempcpy` (1260). -/
theorem vc_1248 {g : Gprs} {f : Rflags} {V : Addr → Byte} {r : Nat} {S L : Addr}
    (hr : g.r12 = BitVec.ofNat 64 r) (hr2 : r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 8)
    (hL : rdq(V, g.rbp + 18446744073709551536#64) = L) (hS : rdq(V, g.rbp + 18446744073709551528#64) = S)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551536#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551528#64) i)) :
    W_1248 fb F Wl (fun j' g' _ V' => j' = 1260 ∧
      g' = { g with rdx := L, rsi := S, r12 := BitVec.ofNat 64 (r - 2) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hL hS hf1 hf2 ⊢
  subst hr
  rcases hr2 with rfl | rfl | rfl | rfl
  all_goals
    hwx [W_1248, o22, hL, hS]
    hcl

/-- After `mempcpy` (`rax` the end): `/` there, `rdi` after it, `m = q` (`cnt - 2`, `rbp - 0x60`): to 1294. -/
theorem vc_1265 {g : Gprs} {f : Rflags} {V : Addr → Byte} {q : Addr}
    (hq : rdq(V, g.rbp + 18446744073709551520#64) = q)
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551520#64) i))
    (hs : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_1265 fb F Wl (fun j' g' _ V' => j' = 1294 ∧
      g' = { g with rdi := g.rax + 1#64, r14 := q } ∧ V' = Vst V g.rax (toBytesLE 47#8 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq hf hs ⊢
  hwx [W_1265, o23, hq]
  hcl

/-- Bit `m` of `n` (`r12 = r`) clear: `m - 1`; to `j` (1343 when `m = 1`, else 1294). -/
theorem vc_1294c {g : Gprs} {f : Rflags} {V : Addr → Byte} {m r j : Nat}
    (hc : m = 1 ∧ (r = 0 ∨ r = 4) ∧ j = 1343 ∨ m = 2 ∧ (r = 0 ∨ r = 2) ∧ j = 1294)
    (h13 : g.r13 = 1#64) (h14 : g.r14 = BitVec.ofNat 64 m) (hr : g.r12 = BitVec.ofNat 64 r) :
    W_1294 fb F Wl (fun j' g' _ V' => j' = j ∧
      g' = { g with rax := BitVec.ofNat 64 (2 ^ m), rcx := BitVec.ofNat 64 m, r14 := BitVec.ofNat 64 (m - 1) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h13 h14 hr ⊢
  subst h13 h14 hr
  rcases hc with ⟨rfl, rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl⟩
  all_goals
    hwx [W_1294, W_1288, o25, o24, Op.shl, Op.cdqe]
    hcl

/-- Bit `m` of `n` set: `temp[m]` (string `S`, length `L` at `rbx + 16 m`): to the `call` of `mempcpy` (1325). -/
theorem vc_1294s {g : Gprs} {f : Rflags} {V : Addr → Byte} {m r : Nat} {S L : Addr}
    (hc : m = 1 ∧ (r = 2 ∨ r = 6) ∨ m = 2 ∧ (r = 4 ∨ r = 6))
    (h13 : g.r13 = 1#64) (h14 : g.r14 = BitVec.ofNat 64 m) (hr : g.r12 = BitVec.ofNat 64 r)
    (hL : rdq(V, g.rbx + BitVec.ofNat 64 (16 * m + 8)) = L) (hS : rdq(V, g.rbx + BitVec.ofNat 64 (16 * m)) = S)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + BitVec.ofNat 64 (16 * m + 8)) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + BitVec.ofNat 64 (16 * m)) i)) :
    W_1294 fb F Wl (fun j' g' _ V' => j' = 1325 ∧
      g' = { g with rax := BitVec.ofNat 64 (16 * m), rcx := BitVec.ofNat 64 m, rdx := L, rsi := S } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h13 h14 hr hL hS hf1 hf2 ⊢
  subst h13 h14 hr
  rcases hc with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  all_goals
    simp only [Nat.reduceMul, Nat.reduceAdd] at hL hS hf1 hf2
    hwx [W_1294, W_1309, o25, o26, Op.shl, Op.cdqe, Op.shl64, hL, hS]
    hcl

/-- After `mempcpy`: `/` at `rax`, `rdi` after it, `m - 1`; to `j` (1343 when `m = 1`, else 1294). -/
theorem vc_1330 {g : Gprs} {f : Rflags} {V : Addr → Byte} {m j : Nat}
    (hm : m = 1 ∧ j = 1343 ∨ m = 2 ∧ j = 1294) (h14 : g.r14 = BitVec.ofNat 64 m)
    (hs : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_1330 fb F Wl (fun j' g' _ V' => j' = j ∧
      g' = { g with rdi := g.rax + 1#64, r14 := BitVec.ofNat 64 (m - 1) } ∧
      V' = Vst V g.rax (toBytesLE 47#8 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h14 hs ⊢
  subst h14
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    hwx [W_1330, o27]
    hcl

/-- `temp[0]` (length `L` at `rbp - 0x48`, string `r15`): to the `call` of `mempcpy` (1350). -/
theorem vc_1343 {g : Gprs} {f : Rflags} {V : Addr → Byte} {L : Addr}
    (hL : rdq(V, g.rbp + 18446744073709551544#64) = L)
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551544#64) i)) :
    W_1343 fb F Wl (fun j' g' _ V' => j' = 1350 ∧ g' = { g with rdx := L, rsi := g.r15 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hL hf ⊢
  hwx [W_1343, o28, hL]
  hcl

/-- After `mempcpy`: `/` at `rax`, `rdi` after it, `n ≠ 0`: the next combination (1248). -/
theorem vc_1355l {g : Gprs} {f : Rflags} {V : Addr → Byte} {r : Nat} (hr : g.r12 = BitVec.ofNat 64 r)
    (hr2 : r = 2 ∨ r = 4 ∨ r = 6) (hs : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_1355 fb F Wl (fun j' g' _ V' => j' = 1248 ∧ g' = { g with rdi := g.rax + 1#64 } ∧
      V' = Vst V g.rax (toBytesLE 47#8 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hs ⊢
  subst hr
  rcases hr2 with rfl | rfl | rfl
  all_goals
    hwx [W_1355, o29]
    hcl

/-- After the last `mempcpy`: `/` at `rax`, `n = 0`: `cnt` (`rbp - 0xa0`), the result (`rbp - 0xa8`), `2^cnt`
(`rbp - 0x80`) back; to the loop that zeroes the lengths (1392) with `rax = 0`. -/
theorem vc_1355e {g : Gprs} {f : Rflags} {V : Addr → Byte} {c P E : Addr} (hr : g.r12 = 0#64)
    (hc : rdq(Vst V g.rax (toBytesLE 47#8 1), g.rbp + 18446744073709551456#64) = c)
    (hP : rdq(Vst V g.rax (toBytesLE 47#8 1), g.rbp + 18446744073709551448#64) = P)
    (hE : rdq(Vst V g.rax (toBytesLE 47#8 1), g.rbp + 18446744073709551488#64) = E)
    (hs : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551456#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551448#64) i))
    (hf3 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551488#64) i)) :
    W_1355 fb F Wl (fun j' g' _ V' => j' = 1392 ∧
      g' = { g with rax := 0#64, rcx := E, rdi := g.rax + 1#64, r12 := c, r14 := P } ∧
      V' = Vst V g.rax (toBytesLE 47#8 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hc hP hE hs hf1 hf2 hf3 ⊢
  subst hr
  hwx [W_1355, W_1367, W_1381, o29, o30, o31, hc, hP, hE]
  hcl

end FV7z.Hwc
