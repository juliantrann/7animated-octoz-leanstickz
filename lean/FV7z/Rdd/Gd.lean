import FV7z.Rdd.Ok
/-!
# `__readdir`: the buffer used up, `__getdents` (PLAN.md §M, M1)

From 109 with the offset at the size: `vc_109g`, the `call __getdents (fd, buf, allocation)` (128, `s_call`), then
`Gdn.gdn_ok` with the return address `rdd_at + 133`; after it the run goes on from the state after the `syscall`.

- `ino_dn`: the first entry's `d_ino` read back from the buffer `getdents64` filled.
- `gst`: a store into the frame, the `DIR` or `errno`, apart from the saved registers and the `DIR`'s fields from
  `p + 4` to `p + 32`, keeps `RSv`, `RFr` and `Dir`.
- `gdZ`, `set0K`: the registers after `__getdents` returns.

Next (the design of `rdd_gd`): an error (`CloseErr`): `errno` `ENOENT` by `vc_133e` then `vc_162`, else `vc_133o`;
then `fin176` with `RS` left (`Dir … n n` kept by `gst`). Otherwise `dn_ret` (the sum `≤ A` from `dentsRes_sum`):
0 by `vc_133z`, `vc_162`, `fin176`; positive by `vc_133p` (`dst` for the size), then `n80` at `k = 0` with the new
segment (`ch_dn`, `ino_dn`, `NzIno`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}

/-- The first entry's `d_ino`, read back from the buffer at `p + 48` the entries were written to. -/
theorem ino_dn {N : Nat} (hp : p.toNat + 48 + N ≤ 2 ^ 64) (V : Addr → Byte) (e : Dirent) (es : List Dirent)
    (hs : ((e :: es).map Dirent.reclen).sum ≤ N) :
    rdq(vRuns V (p.add 48) (direntRuns (e :: es) 0), p.add 48) = e.ino := by
  simp only [List.map_cons, List.sum_cons] at hs
  have hr24 := reclen_ge e
  have hb : (p.add 48).toNat = p.toNat + 48 := tna p 48 (by omega)
  have hbN : (p.add 48).toNat + N ≤ 2 ^ 64 := by omega
  have hlen := bytes_len e
  have hbl := dirent_bytes_le e
  show rdq(vRuns (Vst V ((p.add 48).add 0) e.bytes) (p.add 48) (direntRuns es (0 + e.reclen)), p.add 48) = e.ino
  have hm : List.map (vRuns (Vst V ((p.add 48).add 0) e.bytes) (p.add 48) (direntRuns es (0 + e.reclen)))
      (byteAddrs (p.add 48) 8) = List.map (Vst V ((p.add 48).add 0) e.bytes) (byteAddrs (p.add 48) 8) := by
    apply List.map_congr_left
    intro y hy
    obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
    exact vRuns_apart _ _ _ _ fun r hr i hi => by
      have := direntRuns_in es (0 + e.reclen) r hr
      exact add_ne hbN (by omega) (by omega) (by omega)
  rw [hm, addr_add_zero, bytes_split, Cxa.Vst_append (toBytesLE e.ino 8 ++ toBytesLE e.off 8),
    Cxa.Vst_append (toBytesLE e.ino 8)]
  have h16 : (toBytesLE e.ino 8 ++ toBytesLE e.off 8).length = 16 := by simp [toBytesLE_length]
  rw [h16, toBytesLE_length]
  have x16 : ((p.add 48).add 16).toNat = p.toNat + 64 := (tna (p.add 48) 16 (by omega)).trans (by omega)
  have x8 : ((p.add 48).add 8).toNat = p.toNat + 56 := (tna (p.add 48) 8 (by omega)).trans (by omega)
  have hrest : (toBytesLE (BitVec.ofNat 16 e.reclen) 2 ++ ([BitVec.ofNat 8 e.type.val] ++ e.name ++ [0])).length =
      4 + e.name.length := by
    simp only [List.length_append, toBytesLE_length, List.length_cons, List.length_nil]
    omega
  rw [rd_Vst _ ((p.add 48).add 16)
      (toBytesLE (BitVec.ofNat 16 e.reclen) 2 ++ ([BitVec.ofNat 8 e.type.val] ++ e.name ++ [0])) (p.add 48) 8
      (by rw [hrest, x16]; omega) (by omega) (.inr (by rw [x16]; omega)),
    rd_Vst _ ((p.add 48).add 8) (toBytesLE e.off 8) (p.add 48) 8 (by rw [toBytesLE_length, x8]; omega) (by omega)
      (.inr (by rw [x8]; omega)),
    rd_Vst_self V (p.add 48) (toBytesLE e.ino 8) (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (by decide)]

/-- A store into the frame, the `DIR` or `errno`, apart from the saved registers and from the `DIR`'s fields. -/
theorem gst {g0 : Gprs} {V₀ W : Addr → Byte} {w : BitVec 32} {n k : Nat} (a : Addr) (bs : List Byte)
    (C : RdC F Wl S p fb A) (hal : a.toNat + bs.length ≤ 2 ^ 64)
    (h1 : a.toNat + bs.length ≤ S.toNat - 40 ∨ S.toNat ≤ a.toNat)
    (h2 : ∀ x : Addr, a.toNat ≤ x.toNat → x.toNat < a.toNat + bs.length →
      (S.toNat - 48 ≤ x.toNat ∧ x.toNat < S.toNat) ∨ (p.toNat ≤ x.toNat ∧ x.toNat < p.toNat + 48 + A) ∨ Opd.ER fb x)
    (h3 : a.toNat + bs.length ≤ p.toNat + 4 ∨ p.toNat + 32 ≤ a.toNat)
    (hsv : RSv S g0 W) (hfr : RFr S p fb A V₀ W) (hD : Dir W p A w n k) :
    RSv S g0 (Vst W a bs) ∧ RFr S p fb A V₀ (Vst W a bs) ∧ Dir (Vst W a bs) p A w n k := by
  obtain ⟨b5, -, -, a1, a2, a3, a4⟩ := stR S C.h48
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have t4 : (p + 4#64).toNat = p.toNat + 4 := Opd.tAdd p 4 (by omega)
  have t8 : (p + 8#64).toNat = p.toNat + 8 := Opd.tAdd p 8 (by omega)
  have t16 : (p + 16#64).toNat = p.toNat + 16 := Opd.tAdd p 16 (by omega)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  have sl : ∀ x : Addr, S.toNat - 40 ≤ x.toNat → x.toNat + 8 ≤ S.toNat → rdq(Vst W a bs, x) = rdq(W, x) :=
    fun x x1 x2 => by rw [rd_Vst W a bs x 8 hal (by omega) (by omega)]
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsv
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, hD.nA, ?_⟩⟩
  · rw [sl (S - 8 - 8 - 8 - 8 - 8) (by omega) (by omega)]; exact s1
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8) (by omega) (by omega)]; exact s2
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) (by omega) (by omega)]; exact s3
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) (by omega) (by omega)]; exact s4
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) (by omega) (by omega)]; exact s5
  · intro x x1 x2 x3
    by_cases hx : a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + bs.length
    · exfalso
      rcases h2 x hx.1 hx.2 with h | h | h
      · omega
      · omega
      · exact x3 h
    · rw [Vst_out W a bs x hal (by omega)]
      exact hfr x x1 x2 x3
  · rw [rd_Vst W a bs (p + 4#64) 4 hal (by omega) (by omega)]; exact hD.lk
  · rw [rd_Vst W a bs (p + 8#64) 8 hal (by omega) (by omega)]; exact hD.al
  · rw [rd_Vst W a bs (p + 16#64) 8 hal (by omega) (by omega)]; exact hD.sz
  · rw [rd_Vst W a bs (p + 24#64) 8 hal (by omega) (by omega)]; exact hD.of

/-- The registers after `__getdents` returns: `rsp`, those a call keeps, `rax`. -/
theorem gdZ (Y : State) (r v : BitVec 64) :
    (((sysGpr Y 2).set 0 r).set 4 v).rsp = v ∧ Opd.Keeps Y.cpu.gpr (((sysGpr Y 2).set 0 r).set 4 v) ∧
      (((sysGpr Y 2).set 0 r).set 4 v).rax = r ∧ ((Lseek.lsErrG ((sysGpr Y 2).set 0 r)).set 4 v).rsp = v ∧
      Opd.Keeps Y.cpu.gpr ((Lseek.lsErrG ((sysGpr Y 2).set 0 r)).set 4 v) ∧
      ((Lseek.lsErrG ((sysGpr Y 2).set 0 r)).set 4 v).rax = 18446744073709551615#64 := by
  unfold sysGpr Lseek.lsErrG Opd.Keeps
  generalize Y.cpu.gpr = G
  cases G
  exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem set0K (G : Gprs) (v : BitVec 64) : Opd.Keeps G (G.set 0 v) ∧ (G.set 0 v).rsp = G.rsp := by
  unfold Opd.Keeps
  cases G
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end FV7z.Rdd
