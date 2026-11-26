import FV7z.Mcn.Vc
import FV7z.Ulk.Holds
import FV7z.Stm.Holds
/-!
# `malloc_consolidate`: what it does (PLAN.md §M, M1)

glibc 2.31's `malloc_consolidate (av)` (`rdi = av`, `S` the stack pointer at the entry): it clears
`av->have_fastchunks`, then for each of the ten fastbins (`fbk av k`) takes the bin's list (`xchg` with 0) and for
each chunk `p` of it (`nextp` its `fd`, read first): with the previous chunk free (`prev_inuse` clear) `p` the
previous chunk, unlinked (`unlink_chunk`); then either the next chunk is the top, and `p` the new top, or the next
chunk, unlinked when free (else its `prev_inuse` cleared), is merged and `p` goes first in the unsorted bin
(`fd_nextsize`, `bk_nextsize` cleared for a large one) with its head and foot set. The checks the code makes (the
fastbin index, the previous chunk's size) are hypotheses here (`CPre`), so the run does not reach
`malloc_printerr`.

The code keeps `nextp` at `[rsp]` across the calls (`mB S` the stack pointer of the body) and `unsorted_chunks
(av)` at `[rsp + 8]`; the calls push their return address under it. The bytes here are the run's: the frame's words
are in them (`psh`).

- `csz`, `cnx`, …: the words of a chunk step; `cstep`: the bytes after one chunk.
- `bfold`, `mbins`: the bytes after a bin's list, after the bins from the `k`-th; `BCh`, `MCh`: what they need.
- `Ow`, `Kf`: stores apart from the frame, bytes kept; `kf_ulk`: `unlink_chunk`'s stores apart from the frame keep
  it; `kf_cstep`, `kf_bfold`, `kf_mbins`: the frame's upper 64 bytes kept.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Ulk (ulkV usz ufd ubk ufdn ubkn uff uqa uac ubc UlkPre)
namespace FV7z.Mcn

/-- The stack pointer in the body. -/
abbrev mB (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64

/-- `n` bytes from `a`, not wrapping, apart from the frame `[S - 80, S)`. -/
abbrev Ow (S a : Addr) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64 ∧ (a.toNat + n ≤ S.toNat - 80 ∨ S.toNat ≤ a.toNat)

/-- The bytes in `[lo, up)` kept. -/
abbrev Kf (lo up : Nat) (V V' : Addr → Byte) : Prop := ∀ a : Addr, lo ≤ a.toNat → a.toNat < up → V' a = V a

/-- `n` bytes in the footprint. -/
abbrev Fd (F : Footprint) (a : Addr) (n : Nat) : Prop := ∀ i < n, Foot F.data (Addr.add a i)

/-- `n` bytes written: in the run's writable bytes, apart from the frame. -/
abbrev Wr (Wl : List Rgn) (S a : Addr) (n : Nat) : Prop := (∀ i < n, Foot Wl (Addr.add a i)) ∧ Ow S a n

theorem Kf.refl (lo up : Nat) (V : Addr → Byte) : Kf lo up V V := fun _ _ _ => rfl

theorem Kf.trans {lo up : Nat} {V V' V'' : Addr → Byte} (h1 : Kf lo up V V') (h2 : Kf lo up V' V'') :
    Kf lo up V V'' := fun a h h' => (h2 a h h').trans (h1 a h h')

theorem Kf.mono {lo up lo' up' : Nat} {V V' : Addr → Byte} (h : Kf lo up V V') (h1 : lo ≤ lo') (h2 : up' ≤ up) :
    Kf lo' up' V V' := fun a a1 a2 => h a (by omega) (by omega)

/-- A store apart from `[lo, up)` keeps it. -/
theorem kf_st {lo up : Nat} {V : Addr → Byte} {a : Addr} {w n : Nat} {v : BitVec w} (h1 : a.toNat + n ≤ 2 ^ 64)
    (h2 : a.toNat + n ≤ lo ∨ up ≤ a.toNat) : Kf lo up V (Vst V a (toBytesLE v n)) := fun x x1 x2 =>
  Vst_out _ _ _ _ (by rw [toBytesLE_length]; exact h1) (by rw [toBytesLE_length]; omega)

/-- A store apart from the frame keeps it. -/
theorem kf_ow {S : Addr} {V : Addr → Byte} {a : Addr} {w n : Nat} {v : BitVec w} (h : Ow S a n) :
    Kf (S.toNat - 80) S.toNat V (Vst V a (toBytesLE v n)) := kf_st h.1 h.2

/-! ## `unlink_chunk`'s stores -/

/-- `unlink_chunk (av, p)`'s stores apart from the frame. -/
structure UlkOut (S : Addr) (V : Addr → Byte) (p : Addr) : Prop where
  o1 : Ow S (ufd V p + 24#64) 8
  o2 : Ow S (ubk V p + 16#64) 8
  la : ¬ ((usz V p).toNat ≤ 1023 ∨ ufdn V p = 0#64) → uff V p ≠ 0#64 →
    Ow S (ufdn V p + 40#64) 8 ∧ Ow S (uqa V p + 32#64) 8
  lb : ¬ ((usz V p).toNat ≤ 1023 ∨ ufdn V p = 0#64) → uff V p = 0#64 → Ow S (ufd V p + 32#64) 16
  lc : ¬ ((usz V p).toNat ≤ 1023 ∨ ufdn V p = 0#64) → uff V p = 0#64 → p ≠ ufdn V p →
    Ow S (uac V p + 40#64) 8 ∧ Ow S (ubc V p + 32#64) 8

theorem kf_ulk {S : Addr} {V : Addr → Byte} {p : Addr} (h : UlkOut S V p) :
    Kf (S.toNat - 80) S.toNat V (ulkV V p) := by
  have k1 : Kf (S.toNat - 80) S.toNat V (Ulk.uV1 V p) := Kf.trans (kf_ow h.o1) (kf_ow h.o2)
  unfold ulkV
  by_cases hs : (usz V p).toNat ≤ 1023 ∨ ufdn V p = 0#64
  · rw [if_pos hs]; exact k1
  rw [if_neg hs]
  by_cases hf : uff V p ≠ 0#64
  · rw [if_pos hf]
    obtain ⟨a1, a2⟩ := h.la hs hf
    have k2 : Kf (S.toNat - 80) S.toNat V (Ulk.uVa V p) := k1.trans (kf_ow a1)
    exact k2.trans (kf_ow a2)
  rw [if_neg hf]
  have hf' : uff V p = 0#64 := Decidable.of_not_not hf
  have k3 : Kf (S.toNat - 80) S.toNat V (Ulk.uVc V p) := k1.trans (kf_ow (h.lb hs hf'))
  by_cases he : p = ufdn V p
  · rw [if_pos he]; exact k1.trans (kf_ow (h.lb hs hf'))
  rw [if_neg he]
  obtain ⟨a1, a2⟩ := h.lc hs hf' he
  have k4 : Kf (S.toNat - 80) S.toNat V (Ulk.uVc2 V p) := k3.trans (kf_ow a1)
  exact k4.trans (kf_ow a2)

/-! ## One chunk -/

/-- The frame's words at a call: `nextp` at `[rsp]`, the return address under it. -/
def psh (S : Addr) (V : Addr → Byte) (x ra : Addr) : Addr → Byte :=
  Vst (Vst V (mB S) (toBytesLE x 8)) (mB S - 8) (toBytesLE ra 8)

/-- The size word. -/
def csz (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 8#64)
/-- `nextp`, the chunk's `fd`. -/
def cnx (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 16#64)
/-- The size. -/
def cs0 (V : Addr → Byte) (p : Addr) : Addr := csz V p &&& 18446744073709551608#64
/-- `nextchunk`. -/
def cnc (V : Addr → Byte) (p : Addr) : Addr := p + cs0 V p
/-- `nextsize`. -/
def cns (V : Addr → Byte) (p : Addr) : Addr := rdq(V, cnc V p + 8#64) &&& 18446744073709551608#64
/-- `prev_size`. -/
def cpv (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p)
/-- `prev_inuse (p)` clear. -/
def cpf (V : Addr → Byte) (p : Addr) : Bool := (csz V p).setWidth 8 &&& 1#8 == 0
/-- `p` after the backward merge. -/
def cp1 (V : Addr → Byte) (p : Addr) : Addr := if cpf V p then p - cpv V p else p
/-- The size after the backward merge. -/
def cz1 (V : Addr → Byte) (p : Addr) : Addr := if cpf V p then cs0 V p + cpv V p else cs0 V p
/-- The bytes after the backward merge. -/
def cV1 (S : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  if cpf V p then ulkV (psh S V (cnx V p) (mcn_at.add (247 + 5))) (p - cpv V p) else V
/-- `nextchunk` the top chunk. -/
abbrev ctop (S av : Addr) (V : Addr → Byte) (p : Addr) : Prop := rdq(cV1 S V p, av + 96#64) = cnc V p
/-- `nextchunk` free (its next chunk's `prev_inuse` clear). -/
def cnf (S : Addr) (V : Addr → Byte) (p : Addr) : Bool :=
  ofBytesLE 8 ((byteAddrs (cnc V p + cns V p + 8#64) 1).map (cV1 S V p)) &&& 1#8 == 0
/-- The size after the forward merge. -/
def cz2 (S : Addr) (V : Addr → Byte) (p : Addr) : Addr := if cnf S V p then cz1 V p + cns V p else cz1 V p
/-- The bytes after the forward merge (or `clear_inuse_bit_at_offset (nextchunk, 0)`). -/
def cV2 (S : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  if cnf S V p then ulkV (psh S (cV1 S V p) (cnx V p) (mcn_at.add (298 + 5))) (cnc V p)
  else Vst (cV1 S V p) (cnc V p + 8#64)
    (toBytesLE (rdq(cV1 S V p, cnc V p + 8#64) &&& 18446744073709551614#64) 8)
/-- Where the foot goes (`p + size`). -/
def cft (S : Addr) (V : Addr → Byte) (p : Addr) : Addr := if cnf S V p then cp1 V p + cz2 S V p else cnc V p
/-- `first_unsorted`. -/
def cfu (S av : Addr) (V : Addr → Byte) (p : Addr) : Addr := rdq(cV2 S V p, av + 112#64)
/-- The bytes after `unsorted_bin->fd = p`, `first_unsorted->bk = p`. -/
def cV3 (S av : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (cV2 S V p) (av + 112#64) (toBytesLE (cp1 V p) 8)) (cfu S av V p + 24#64) (toBytesLE (cp1 V p) 8)
/-- The bytes after `p->fd_nextsize = p->bk_nextsize = NULL` for a large chunk. -/
def cV4 (S av : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  if (cz2 S V p).toNat ≤ 1023 then cV3 S av V p else Vst (cV3 S av V p) (cp1 V p + 32#64) (toBytesLE 0#128 16)
/-- The bytes after `set_head (p, size | PREV_INUSE)`, `p->bk = unsorted_bin`, `p->fd = first_unsorted`,
`set_foot (p, size)`. -/
def cV7 (S av : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (cV4 S av V p) (cp1 V p + 8#64) (toBytesLE (cz2 S V p ||| 1#64) 8)) (cp1 V p + 16#64)
    (toBytesLE (cfu S av V p) 8)) (cp1 V p + 16#64 + 8#64) (toBytesLE (av + 96#64) 8)) (cft S V p)
    (toBytesLE (cz2 S V p) 8)
/-- The bytes after the chunk `p`. -/
def cstep (S av : Addr) (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  if ctop S av V p then
    Vst (Vst (cV1 S V p) (cp1 V p + 8#64) (toBytesLE ((cz1 V p + cns V p) ||| 1#64) 8)) (av + 96#64)
      (toBytesLE (cp1 V p) 8)
  else cV7 S av V p

/-- What the chunk needs when `nextchunk` is not the top. -/
structure CRest (F : Footprint) (Wl : List Rgn) (S av : Addr) (V : Addr → Byte) (p : Addr) : Prop where
  nf : cnf S V p = true → UlkPre F Wl (psh S (cV1 S V p) (cnx V p) (mcn_at.add (298 + 5))) (cnc V p) ∧
    UlkOut S (psh S (cV1 S V p) (cnx V p) (mcn_at.add (298 + 5))) (cnc V p)
  ni : cnf S V p = false → Wr Wl S (cnc V p + 8#64) 8
  f4 : Fd F (av + 112#64) 8
  w1 : Wr Wl S (av + 112#64) 8
  w2 : Wr Wl S (cfu S av V p + 24#64) 8
  w3 : ¬ (cz2 S V p).toNat ≤ 1023 → Wr Wl S (cp1 V p + 32#64) 16
  w4 : Wr Wl S (cp1 V p + 8#64) 8
  w5 : Wr Wl S (cp1 V p + 16#64) 16
  w6 : Wr Wl S (cft S V p) 8

/-- What the chunk `p` in the fastbin `fb` needs: the checks hold, the words read are in the footprint, the words
written in the run's and apart from the frame, `unlink_chunk`'s needs. -/
structure CPre (F : Footprint) (Wl : List Rgn) (S av fb : Addr) (V : Addr → Byte) (p : Addr) : Prop where
  nz : p ≠ 0#64
  fb : fbx av (csz V p) = fb
  f1 : Fd F (p + 8#64) 8
  f2 : Fd F (p + 16#64) 8
  f3 : Fd F (cnc V p + 8#64) 8
  pf : cpf V p = true → Fd F p 8 ∧ Fd F (p - cpv V p + 8#64) 8 ∧
    rdq(V, p - cpv V p + 8#64) &&& 18446744073709551608#64 = cpv V p ∧
    UlkPre F Wl (psh S V (cnx V p) (mcn_at.add (247 + 5))) (p - cpv V p) ∧
    UlkOut S (psh S V (cnx V p) (mcn_at.add (247 + 5))) (p - cpv V p)
  ft : Fd F (av + 96#64) 8
  tp : ctop S av V p → Wr Wl S (cp1 V p + 8#64) 8 ∧ Wr Wl S (av + 96#64) 8
  nt : ¬ ctop S av V p → Fd F (cnc V p + cns V p + 8#64) 1 ∧ CRest F Wl S av V p

/-! ## The loops -/

/-- The bytes after the chunks `ps`. -/
def bfold (S av : Addr) : (Addr → Byte) → List Addr → Addr → Byte
  | V, [] => V
  | V, p :: ps => bfold S av (cstep S av V p) ps

/-- The chunks `ps` of the fastbin `fb`, each the previous one's `fd` (the last one's null), each as `CPre`. -/
def BCh (F : Footprint) (Wl : List Rgn) (S av fb : Addr) : (Addr → Byte) → List Addr → Prop
  | _, [] => True
  | V, p :: ps => CPre F Wl S av fb V p ∧ cnx V p = ps.headD 0#64 ∧ BCh F Wl S av fb (cstep S av V p) ps

/-- The `k`-th fastbin, `&av->fastbinsY[k]`. -/
abbrev fbk (av : Addr) (k : Nat) : Addr := av + BitVec.ofNat 64 (16 + 8 * k)

/-- The bytes after the bins from the `k`-th, `chs` their lists. -/
def mbins (S av : Addr) : Nat → List (List Addr) → (Addr → Byte) → Addr → Byte
  | _, [], V => V
  | k, ch :: chs, V => mbins S av (k + 1) chs (bfold S av (Vst V (fbk av k) (toBytesLE 0#64 8)) ch)

/-- The bins from the `k`-th: each bin's word written (apart from the frame), its list as `BCh`. -/
def MCh (F : Footprint) (Wl : List Rgn) (S av : Addr) : Nat → List (List Addr) → (Addr → Byte) → Prop
  | _, [], _ => True
  | k, ch :: chs, V => Wr Wl S (fbk av k) 8 ∧ rdq(V, fbk av k) = ch.headD 0#64 ∧
      BCh F Wl S av (fbk av k) (Vst V (fbk av k) (toBytesLE 0#64 8)) ch ∧
      MCh F Wl S av (k + 1) chs (bfold S av (Vst V (fbk av k) (toBytesLE 0#64 8)) ch)

/-! ## The frame kept -/

theorem mB_toNat {S : Addr} (hS : 80 ≤ S.toNat) : (mB S).toNat = S.toNat - 72 := by
  obtain ⟨-, -, -, e4⟩ := Cal.fr_e hS
  have e5 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8 - 8) (by rw [e4]; omega)
  have e6 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8 - 8 - 8) (by rw [e5, e4]; omega)
  have hl := S.isLt
  show (S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64).toNat = _
  rw [BitVec.toNat_sub, e6, e5, e4, show (24#64).toNat = 24 from rfl]
  omega

/-- The frame's words at a call keep the frame's upper 64 bytes. -/
theorem kf_psh {S : Addr} (hS : 80 ≤ S.toNat) (V : Addr → Byte) (x ra : Addr) :
    Kf (S.toNat - 64) S.toNat V (psh S V x ra) := by
  have e := mB_toNat hS
  have e8 := Prepare.toNat_sub8 (a := mB S) (by rw [e]; omega)
  have hl := S.isLt
  exact Kf.trans (kf_st (by rw [e]; omega) (.inl (by rw [e]; omega)))
    (kf_st (by rw [e8, e]; omega) (.inl (by rw [e8, e]; omega)))

theorem kf_hi {S : Addr} {V V' : Addr → Byte} (h : Kf (S.toNat - 80) S.toNat V V') : Kf (S.toNat - 64) S.toNat V V' :=
  h.mono (by omega) (Nat.le_refl _)

variable {F : Footprint} {Wl : List Rgn}

theorem kf_cstep {S av fb : Addr} {V : Addr → Byte} {p : Addr} (hS : 80 ≤ S.toNat) (h : CPre F Wl S av fb V p) :
    Kf (S.toNat - 64) S.toNat V (cstep S av V p) := by
  have k1 : Kf (S.toNat - 64) S.toNat V (cV1 S V p) := by
    unfold cV1
    by_cases hp : cpf V p = true
    · rw [if_pos hp]
      obtain ⟨-, -, -, -, uo⟩ := h.pf hp
      exact (kf_psh hS V _ _).trans (kf_hi (kf_ulk uo))
    · rw [if_neg hp]; exact Kf.refl _ _ _
  unfold cstep
  by_cases ht : ctop S av V p
  · rw [if_pos ht]
    obtain ⟨⟨-, a1⟩, ⟨-, a2⟩⟩ := h.tp ht
    exact (k1.trans (kf_hi (kf_ow a1))).trans (kf_hi (kf_ow a2))
  rw [if_neg ht]
  obtain ⟨-, r⟩ := h.nt ht
  have k2 : Kf (S.toNat - 64) S.toNat V (cV2 S V p) := by
    unfold cV2
    by_cases hn : cnf S V p = true
    · rw [if_pos hn]
      obtain ⟨-, uo⟩ := r.nf hn
      exact (k1.trans (kf_psh hS _ _ _)).trans (kf_hi (kf_ulk uo))
    · rw [if_neg hn]; exact k1.trans (kf_hi (kf_ow (r.ni (by simpa using hn)).2))
  have k3 : Kf (S.toNat - 64) S.toNat V (cV3 S av V p) :=
    (k2.trans (kf_hi (kf_ow r.w1.2))).trans (kf_hi (kf_ow r.w2.2))
  have k4 : Kf (S.toNat - 64) S.toNat V (cV4 S av V p) := by
    unfold cV4
    by_cases hz : (cz2 S V p).toNat ≤ 1023
    · rw [if_pos hz]; exact k3
    · rw [if_neg hz]; exact k3.trans (kf_hi (kf_ow (r.w3 hz).2))
  have o5 : Ow S (cp1 V p + 16#64) 8 := ⟨by have := r.w5.2.1; omega, by have := r.w5.2.2; omega⟩
  have o6 : Ow S (cp1 V p + 16#64 + 8#64) 8 := by
    obtain ⟨a1, a2⟩ := r.w5.2
    have e : (cp1 V p + 16#64 + 8#64).toNat = (cp1 V p + 16#64).toNat + 8 := by
      rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega⟩
  exact (((k4.trans (kf_hi (kf_ow r.w4.2))).trans (kf_hi (kf_ow o5))).trans (kf_hi (kf_ow o6))).trans
    (kf_hi (kf_ow r.w6.2))

theorem kf_bfold {S av fb : Addr} (hS : 80 ≤ S.toNat) :
    ∀ (ps : List Addr) (V : Addr → Byte), BCh F Wl S av fb V ps → Kf (S.toNat - 64) S.toNat V (bfold S av V ps)
  | [], _, _ => Kf.refl _ _ _
  | _ :: ps, _, ⟨h, _, hs⟩ => (kf_cstep hS h).trans (kf_bfold hS ps _ hs)

theorem kf_mbins {S av : Addr} (hS : 80 ≤ S.toNat) :
    ∀ (k : Nat) (chs : List (List Addr)) (V : Addr → Byte), MCh F Wl S av k chs V →
      Kf (S.toNat - 64) S.toNat V (mbins S av k chs V)
  | _, [], _, _ => Kf.refl _ _ _
  | k, _ :: chs, _, ⟨hw, _, hb, hs⟩ =>
    ((kf_hi (kf_ow hw.2)).trans (kf_bfold hS _ _ hb)).trans (kf_mbins hS (k + 1) chs _ hs)

end FV7z.Mcn
