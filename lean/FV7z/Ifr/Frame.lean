import FV7z.Tun.Inv
import FV7z.Sbrk.Next
import FV7z.Tls.Mem
/-!
# `_int_free` to the tcache put: the bytes it leaves (PLAN.md G3, `free`)

The frame of glibc 2.31's `_int_free` (`0x62f990`, `Ifr.ifr_at`) on its way to the tcache put, `S` the stack pointer at
the entry: the six pushes (`Tls.P6`, below `S`), then the canary stored at `S - 64` (`Vc`); the put (`Vput`): the
chunk's `key` (`p + 24`) set to the tcache `C`, its `next` (`p + 16`) to the bin's old head `E`, the bin's head
(`C + 128 + 8 * idx`) to `p + 16`, the bin's count (`C + 2 * idx`) to `c`.

- `tAdd`, `tSub`, `stk`, `stq`: `toNat` of the stack slots; `ix2`, `ix8`: of the count and the head of bin `idx`.
- `P6_out`, `Vc_out`, `Vput_rd`: the bytes outside what was stored; `P6_rd`, `Vc_rd`: reads there.
- `pops`: the canary and the six registers read back from `Vc`.
- `cnt_inc`, `sw16`: the count's widenings.
- `footR`: a range of the footprint gives each address of a slot in it.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Ifr

theorem tAdd (x : BitVec 64) (k : Nat) (hk : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tSub (x : BitVec 64) (k : Nat) (hk : k ≤ x.toNat) : (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The slots of the six pushes and the stack pointer after `sub rsp, 72`. -/
theorem stk (S : BitVec 64) (h : 120 ≤ S.toNat) :
    (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧ (S - 8 - 8 - 8).toNat = S.toNat - 24 ∧
      (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 ∧ (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 ∧
      (S - 8 - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 48 ∧
      (S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64).toNat = S.toNat - 120 := by
  have b1 : (S - 8).toNat = S.toNat - 8 := tSub S 8 (by omega)
  have b2 : (S - 8 - 8).toNat = S.toNat - 16 := (tSub (S - 8) 8 (by omega)).trans (by omega)
  have b3 : (S - 8 - 8 - 8).toNat = S.toNat - 24 := (tSub (S - 8 - 8) 8 (by omega)).trans (by omega)
  have b4 : (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 := (tSub (S - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b5 : (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 :=
    (tSub (S - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b6 : (S - 8 - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 48 :=
    (tSub (S - 8 - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b7 : (S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64).toNat = S.toNat - 120 :=
    (tSub (S - 8 - 8 - 8 - 8 - 8 - 8) 72 (by omega)).trans (by omega)
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

/-- From the stack pointer `Q = S - 120` after `sub rsp, 72`: the canary's slot and the pops'. -/
theorem stq {S Q : BitVec 64} (hQ : Q.toNat = S.toNat - 120) (h : 120 ≤ S.toNat) :
    (Q + 56#64).toNat = S.toNat - 64 ∧ (Q + 72#64).toNat = S.toNat - 48 ∧ (Q + 72#64 + 8).toNat = S.toNat - 40 ∧
      (Q + 72#64 + 8 + 8).toNat = S.toNat - 32 ∧ (Q + 72#64 + 8 + 8 + 8).toNat = S.toNat - 24 ∧
      (Q + 72#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧ (Q + 72#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 ∧
      (Q + 72#64 + 8 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat := by
  have hS := S.isLt
  have a0 : (Q + 56#64).toNat = S.toNat - 64 := (tAdd Q 56 (by omega)).trans (by omega)
  have a1 : (Q + 72#64).toNat = S.toNat - 48 := (tAdd Q 72 (by omega)).trans (by omega)
  have a2 : (Q + 72#64 + 8).toNat = S.toNat - 40 := (tAdd (Q + 72#64) 8 (by omega)).trans (by omega)
  have a3 : (Q + 72#64 + 8 + 8).toNat = S.toNat - 32 := (tAdd (Q + 72#64 + 8) 8 (by omega)).trans (by omega)
  have a4 : (Q + 72#64 + 8 + 8 + 8).toNat = S.toNat - 24 :=
    (tAdd (Q + 72#64 + 8 + 8) 8 (by omega)).trans (by omega)
  have a5 : (Q + 72#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 :=
    (tAdd (Q + 72#64 + 8 + 8 + 8) 8 (by omega)).trans (by omega)
  have a6 : (Q + 72#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 :=
    (tAdd (Q + 72#64 + 8 + 8 + 8 + 8) 8 (by omega)).trans (by omega)
  have a7 : (Q + 72#64 + 8 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat :=
    (tAdd (Q + 72#64 + 8 + 8 + 8 + 8 + 8) 8 (by omega)).trans (by omega)
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩

/-- The count and the head of bin `ix` of the tcache `C`. -/
theorem ix2 {C ix : BitVec 64} (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) :
    (C + ix * 2#64).toNat = C.toNat + ix.toNat * 2 := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl]
  rw [Nat.mod_eq_of_lt (a := ix.toNat * 2) (by omega)]
  omega

theorem ix8 {C ix : BitVec 64} (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) :
    (C + ix * 8#64 + 128#64).toNat = C.toNat + ix.toNat * 8 + 128 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl,
    show (128#64 : BitVec 64).toNat = 128 from rfl]
  rw [Nat.mod_eq_of_lt (a := ix.toNat * 8) (by omega), Nat.mod_eq_of_lt (a := C.toNat + ix.toNat * 8) (by omega)]
  omega

/-- The bytes after the canary's store, `cn` at `S - 64`. -/
abbrev Vc (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) : Addr → Byte :=
  Vst (Tls.P6 V g) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 56#64) (toBytesLE cn 8)

/-- The four stores of the tcache put: `e->key = tcache`, `e->next = E`, the bin's head `p + 16`, its count `c`. -/
abbrev Vput (V : Addr → Byte) (p C ix E : Addr) (c : BitVec 16) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (p + 24#64) (toBytesLE C 8)) (p + 16#64) (toBytesLE E 8)) (C + ix * 8#64 + 128#64)
    (toBytesLE (p + 16#64) 8)) (C + ix * 2#64) (toBytesLE c 2)

theorem P6_out (V : Addr → Byte) (g : Gprs) (h : 120 ≤ g.rsp.toNat) (a : Addr)
    (ha : a.toNat < g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ a.toNat) : Tls.P6 V g a = V a := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := stk g.rsp h
  have := g.rsp.isLt
  dsimp only [Tls.P6]
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length, e1, e2, e3, e4, e5, e6])
  all_goals omega

theorem Vc_out (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 120 ≤ g.rsp.toNat) (a : Addr)
    (ha : a.toNat < g.rsp.toNat - 64 ∨ g.rsp.toNat ≤ a.toNat) : Vc g cn V a = V a := by
  obtain ⟨-, -, -, -, -, -, e7⟩ := stk g.rsp h
  obtain ⟨q56, -⟩ := stq e7 h
  have := g.rsp.isLt
  dsimp only [Vc]
  rw [Vst_out]
  · exact P6_out V g h a (by omega)
  all_goals (try simp only [toBytesLE_length, q56])
  all_goals omega

theorem P6_rd (V : Addr → Byte) (g : Gprs) (h : 120 ≤ g.rsp.toNat) {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ x.toNat) :
    List.map (Tls.P6 V g) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Sbrk.rd_eq hx fun a h1 h2 => P6_out V g h a (by omega)

theorem Vc_rd (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 120 ≤ g.rsp.toNat) {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ g.rsp.toNat - 64 ∨ g.rsp.toNat ≤ x.toNat) :
    List.map (Vc g cn V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Sbrk.rd_eq hx fun a h1 h2 => Vc_out g cn V h a (by omega)

/-- A read outside the chunk's `next` and `key` and outside the tcache. -/
theorem Vput_rd (U : Addr → Byte) (p C ix E : Addr) (c : BitVec 16) (hp : p.toNat + 32 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ p.toNat + 16 ∨ p.toNat + 32 ≤ x.toNat)
    (h2 : x.toNat + n ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat) :
    List.map (Vput U p C ix E c) (byteAddrs x n) = List.map U (byteAddrs x n) := by
  have e24 : (p + 24#64).toNat = p.toNat + 24 := tAdd p 24 (by omega)
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  dsimp only [Vput]
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  all_goals (try simp only [toBytesLE_length, e24, e16, e8, e2])
  all_goals omega

/-- The canary and the six registers, read back by the epilogue from `Vc`. -/
theorem pops (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 120 ≤ g.rsp.toNat) :
    rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 56#64) = cn ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64) = g.rbx ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8) = g.rbp ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8) = g.r12 ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8) = g.r13 ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8) = g.r14 ∧
      rdq(Vc g cn V, g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 + 8) = g.r15 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := stk g.rsp h
  obtain ⟨q56, q72, q80, q88, q96, q104, q112, -⟩ := stq e7 h
  have := g.rsp.isLt
  have a0 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q72, e6])
  have a1 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 = g.rsp - 8 - 8 - 8 - 8 - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q80, e5])
  have a2 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 = g.rsp - 8 - 8 - 8 - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q88, e4])
  have a3 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 = g.rsp - 8 - 8 - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q96, e3])
  have a4 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 = g.rsp - 8 - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q104, e2])
  have a5 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 + 8 = g.rsp - 8 :=
    BitVec.eq_of_toNat_eq (by rw [q112, e1])
  rw [a5, a4, a3, a2, a1, a0]
  dsimp only [Vc, Tls.P6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56])
    all_goals omega
  · rw [rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega
  · rw [rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega
  · rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega
  · rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega
  · rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega
  · rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, q56, e1, e2, e3, e4, e5, e6])
    all_goals omega

/-- `add ecx, 1` on the count `movzx`ed to `rcx`, stored back as a word: the count plus one. -/
theorem cnt_inc (c : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c)) + 1#32) = c + 1#16 := by
  apply BitVec.eq_of_toNat_eq
  have : c.toNat < 65536 := c.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem sw16 (x : BitVec 16) : (BitVec.setWidth 64 (BitVec.setWidth 32 x)).toNat = x.toNat := by
  have : x.toNat < 65536 := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- A range of the footprint gives the addresses of a slot in it. -/
theorem footR {R : List Rgn} {lo hi : Nat} (h : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → Foot R a) {y : Addr}
    {m n : Nat} (hy : y.toNat = m) (h1 : lo ≤ m) (h2 : m + n ≤ hi) (h3 : hi ≤ 2 ^ 64) :
    ∀ i < n, Foot R (Addr.add y i) := fun i hi' => by
  have e := toNat_add_of_fits (a := y) hi' (by omega)
  exact h _ (by omega) (by omega)

end FV7z.Ifr
