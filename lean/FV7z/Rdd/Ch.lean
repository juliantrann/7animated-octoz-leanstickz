import FV7z.Lemmas.SysDents
import FV7z.Lemmas.Frame
import FV7z.Lemmas.FnSteps
import FV7z.Cxa.Holds
import FV7z.Tun.Inv
/-!
# The entries in a `DIR`'s buffer (PLAN.md §M, M1)

glibc 2.31's `struct __dirstream` at `p` (`sysdeps/posix/dirstream.h`): `fd` (4 bytes at `p`), `lock` (`p + 4`),
`allocation` (`p + 8`), `size` (`p + 16`), `offset` (`p + 24`), `filepos` (`p + 32`), `errcode` (`p + 40`), the
buffer `data` from `p + 48`. `__readdir` walks the buffer from `offset` to `size` by `d_reclen`, the 2 bytes at 16 in
each `struct linux_dirent64`.

- `rl`: the `d_reclen` of the entry at offset `k`; `Ent`: at least 18 bytes (the fields read), a NUL in the name.
- `Ch`: from `k` the entries follow one another up to `n` exactly (the walk ends and reads only entries).
- `Ch.le`, `Ch.congr`: `k ≤ n`; only the `n` bytes of the buffer matter.
- `ch_runs`, `ch_dn`: the entries `getdents64` writes (`direntRuns`, `dnBuf`) make a chain from 0 to their size.
-/
open ZellicX86 Decode FV7z
namespace FV7z.Rdd

/-- `d_reclen` of the entry at offset `k` of the buffer of the `DIR` at `p`: the 2 bytes at `p + 48 + k + 16`. -/
def rl (V : Addr → Byte) (p : Addr) (k : Nat) : Nat := (ofBytesLE 16 ((byteAddrs (p.add (k + 64)) 2).map V)).toNat

/-- The entry at offset `k`: its `d_reclen` covers the 18 bytes read, a NUL in its name (from byte 19 on). -/
abbrev Ent (V : Addr → Byte) (p : Addr) (k : Nat) : Prop :=
  18 ≤ rl V p k ∧ ∃ i, 19 ≤ i ∧ i < rl V p k ∧ V (p.add (k + 48 + i)) = 0

/-- From offset `k`, entries one after the other (`d_reclen` apart) up to offset `n` exactly. -/
inductive Ch (V : Addr → Byte) (p : Addr) (n : Nat) : Nat → Prop
  | fin : Ch V p n n
  | step {k : Nat} : Ent V p k → k + rl V p k ≤ n → Ch V p n (k + rl V p k) → Ch V p n k

theorem Ch.le {V : Addr → Byte} {p : Addr} {n k : Nat} (h : Ch V p n k) : k ≤ n := by
  induction h with
  | fin => exact Nat.le_refl _
  | step _ h1 _ _ => omega

theorem rl_congr {V V' : Addr → Byte} {p : Addr} {k : Nat}
    (h : ∀ i < 2, V' (p.add (k + 64 + i)) = V (p.add (k + 64 + i))) : rl V' p k = rl V p k := by
  unfold rl
  congr 2
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  rw [addr_add_add]
  exact h j hj

/-- Only the `n` bytes of the buffer matter. -/
theorem Ch.congr {V V' : Addr → Byte} {p : Addr} {n k : Nat}
    (h : ∀ i < n, V' (p.add (48 + i)) = V (p.add (48 + i))) (hc : Ch V p n k) : Ch V' p n k := by
  induction hc with
  | fin => exact Ch.fin
  | @step k he hle _ ih =>
    obtain ⟨h18, i, hi1, hi2, hi3⟩ := he
    have hr : rl V' p k = rl V p k := rl_congr fun j hj => by
      rw [show k + 64 + j = 48 + (k + 16 + j) by omega]
      exact h (k + 16 + j) (by omega)
    refine Ch.step ⟨by rw [hr]; exact h18, i, hi1, by rw [hr]; exact hi2, ?_⟩ (by rw [hr]; exact hle)
      (by rw [hr]; exact ih)
    rw [show k + 48 + i = 48 + (k + i) by omega, h (k + i) (by omega)]
    rw [show 48 + (k + i) = k + 48 + i by omega]
    exact hi3

theorem tna (a : Addr) (i : Nat) (h : a.toNat + i < 2 ^ 64) : (a.add i).toNat = a.toNat + i :=
  toNat_add_of_fits (n := i + 1) (by omega) (by omega)

theorem tna_le (a : Addr) (i : Nat) : (a.add i).toNat ≤ a.toNat + i := by
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)

/-- Two offsets of a region that fits are two addresses. -/
theorem add_ne {b : Addr} {N m m' : Nat} (hf : b.toNat + N ≤ 2 ^ 64) (hm : m < N) (hm' : m' < N) (h : m ≠ m') :
    b.add m ≠ b.add m' := fun e => by
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hm hf, toNat_add_of_fits hm' hf] at this
  omega

/-- An entry's size fits in `d_reclen`'s 16 bits. -/
theorem reclen_lt (e : Dirent) : e.reclen < 2 ^ 16 := by
  show e.reclen < 65536
  have := e.nameOk.2.1
  unfold Dirent.reclen
  omega

theorem reclen_ge (e : Dirent) : 24 ≤ e.reclen := by
  have := e.nameOk.1
  unfold Dirent.reclen
  omega

/-- An entry's bytes: the 16 before `d_reclen`, `d_reclen`, the rest. -/
theorem bytes_split (e : Dirent) : e.bytes = (toBytesLE e.ino 8 ++ toBytesLE e.off 8) ++
    (toBytesLE (BitVec.ofNat 16 e.reclen) 2 ++ ([BitVec.ofNat 8 e.type.val] ++ e.name ++ [0])) := by
  simp [Dirent.bytes]

/-- An entry's bytes: the name's NUL last, after `19 + name.length` bytes. -/
theorem bytes_nul (e : Dirent) : e.bytes = (toBytesLE e.ino 8 ++ toBytesLE e.off 8 ++
    toBytesLE (BitVec.ofNat 16 e.reclen) 2 ++ [BitVec.ofNat 8 e.type.val] ++ e.name) ++ [0] := rfl

theorem bytes_len (e : Dirent) : e.bytes.length = 20 + e.name.length := by
  simp only [Dirent.bytes, List.length_append, toBytesLE_length, List.length_cons, List.length_nil]
  omega

/-- The entries `es` written from offset `o` of the buffer at `p + 48`, within `N` bytes: a chain from `o` to `o`
plus their size. -/
theorem ch_runs {p : Addr} {N : Nat} (hp : p.toNat + 48 + N ≤ 2 ^ 64) :
    ∀ (es : List Dirent) (o : Nat) (V : Addr → Byte), o + (es.map Dirent.reclen).sum ≤ N →
      Ch (vRuns V (p.add 48) (direntRuns es o)) p (o + (es.map Dirent.reclen).sum) o
  | [], o, V, _ => Ch.fin
  | e :: es, o, V, hs => by
    simp only [List.map_cons, List.sum_cons] at hs ⊢
    have hr24 := reclen_ge e
    have hb : (p.add 48).toNat = p.toNat + 48 := tna p 48 (by omega)
    have hbN : (p.add 48).toNat + N ≤ 2 ^ 64 := by omega
    have hlen := bytes_len e
    have hbl := dirent_bytes_le e
    have ih := ch_runs hp es (o + e.reclen) (Vst V ((p.add 48).add o) e.bytes) (by omega)
    -- the run of the rest leaves the entry's bytes alone
    have hap : ∀ m, m < o + e.reclen →
        vRuns (Vst V ((p.add 48).add o) e.bytes) (p.add 48) (direntRuns es (o + e.reclen)) ((p.add 48).add m) =
          Vst V ((p.add 48).add o) e.bytes ((p.add 48).add m) := fun m hm =>
      vRuns_apart _ _ _ _ fun r hr i hi => by
        have := direntRuns_in es (o + e.reclen) r hr
        exact add_ne hbN (by omega) (by omega) (by omega)
    show Ch (vRuns (Vst V ((p.add 48).add o) e.bytes) (p.add 48) (direntRuns es (o + e.reclen))) p
      (o + (e.reclen + (es.map Dirent.reclen).sum)) o
    -- `d_reclen` read back
    have hrl : rl (vRuns (Vst V ((p.add 48).add o) e.bytes) (p.add 48) (direntRuns es (o + e.reclen))) p o =
        e.reclen := by
      unfold rl
      have hm : (byteAddrs (p.add (o + 64)) 2).map
          (vRuns (Vst V ((p.add 48).add o) e.bytes) (p.add 48) (direntRuns es (o + e.reclen))) =
          (byteAddrs (p.add (o + 64)) 2).map (Vst V ((p.add 48).add o) e.bytes) := by
        apply List.map_congr_left
        intro y hy
        obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
        rw [addr_add_add p (o + 64) j, show o + 64 + j = 48 + (o + 16 + j) by omega, ← addr_add_add p 48]
        exact hap (o + 16 + j) (by omega)
      rw [hm, bytes_split, Cxa.Vst_append (toBytesLE e.ino 8 ++ toBytesLE e.off 8),
        Cxa.Vst_append (toBytesLE (BitVec.ofNat 16 e.reclen) 2)]
      have hl16 : (toBytesLE e.ino 8 ++ toBytesLE e.off 8).length = 16 := by simp [toBytesLE_length]
      have ha16 : ((p.add 48).add o).add (toBytesLE e.ino 8 ++ toBytesLE e.off 8).length = p.add (o + 64) := by
        rw [hl16, addr_add_add, addr_add_add, show 48 + (o + 16) = o + 64 by omega]
      rw [ha16, toBytesLE_length]
      have hx : (p.add (o + 64)).toNat = p.toNat + 48 + o + 16 := (tna p (o + 64) (by omega)).trans (by omega)
      have hx2 : ((p.add (o + 64)).add 2).toNat = p.toNat + 48 + o + 18 :=
        (tna (p.add (o + 64)) 2 (by rw [hx]; omega)).trans (by rw [hx])
      rw [Tun.rd_Vst _ ((p.add (o + 64)).add 2) ([BitVec.ofNat 8 e.type.val] ++ e.name ++ [0]) (p.add (o + 64)) 2
          (by rw [hx2]; simp only [List.length_append, List.length_cons, List.length_nil] <;> omega)
          (by rw [hx]; omega) (.inr (by rw [hx, hx2]; omega)),
        Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hx]; omega), ofBytesLE_toBytesLE (by decide),
        BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (reclen_lt e)
    refine Ch.step ⟨by rw [hrl]; omega, 19 + e.name.length, by omega, by rw [hrl]; omega, ?_⟩ (by rw [hrl]; omega)
      (by rw [hrl, ← Nat.add_assoc]; exact ih)
    -- the name's NUL
    rw [show o + 48 + (19 + e.name.length) = 48 + (o + (19 + e.name.length)) by omega,
      ← addr_add_add p 48 (o + (19 + e.name.length)), hap (o + (19 + e.name.length)) (by omega),
      ← addr_add_add (p.add 48) o (19 + e.name.length), bytes_nul, Cxa.Vst_append]
    have hl : (toBytesLE e.ino 8 ++ toBytesLE e.off 8 ++ toBytesLE (BitVec.ofNat 16 e.reclen) 2 ++
        [BitVec.ofNat 8 e.type.val] ++ e.name).length = 19 + e.name.length := by
      simp only [List.length_append, toBytesLE_length, List.length_cons, List.length_nil] <;> omega
    rw [hl]
    show upd1 _ _ _ _ = _
    simp [upd1]

/-- The entries of `r` in the buffer at `p + 48` of `n` bytes (`dnBuf`): a chain from 0 to their size. -/
theorem ch_dn {p : Addr} {n : Nat} {r : DnOut} (V : Addr → Byte) (hp : p.toNat + 48 + n ≤ 2 ^ 64)
    (hs : (r.es.map Dirent.reclen).sum ≤ n) :
    Ch (Vst V (p.add 48) (dnBuf V (p.add 48) n r)) p (r.es.map Dirent.reclen).sum 0 := by
  have hb := tna_le p 48
  rw [← dn_one (V := V) (a := p.add 48) hs (by omega)]
  have := ch_runs hp r.es 0 V (by omega)
  rwa [Nat.zero_add] at this

end FV7z.Rdd
