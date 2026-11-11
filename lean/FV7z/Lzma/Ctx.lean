import FV7z.Lzma.Arith
import FV7z.Lzma.Norm
/-!
# The call of `LzmaDec_DecodeReal_3`, and what its memory keeps (PLAN.md G2, pilot)

`Ctx`: what stays the same through a call: where the frame, the `CLzmaDec`, the array of probabilities, the
dictionary and the input lie, and the values the prologue stores into the frame. `Mem K V`: the footprint's bytes `V`
hold these values in the frame's slots, probabilities in `[31, 2017]` in every slot of the array, and four `reps` no
larger than the dictionary's buffer. Stores keep it: into the array a probability (`Mem.st_pr`), into a `reps` slot a
value that small (`Mem.st_rep*`), anywhere in the dictionary, the frame's other slots or the `CLzmaDec` (`Mem.st_free`).

`RcU`/`RcN`: the range before and after a normalization, with the count of the bytes read at or after `bufLimit`
(`Crd` of `Arith.lean`). `wnorm_of`: a normalization (`Wnorm` of `Norm.lean`) from `RcU`, its read within 20 bytes of
`bufLimit`.
-/
namespace FV7z.Lzma
open ZellicX86 Decode FV7z FV7z.Leaf

/-- The 8, 4, 2 bytes of `V` at `a`. -/
notation "rdq(" V ", " a ")" => ofBytesLE 64 (List.map V (byteAddrs a 8))
notation "rdd(" V ", " a ")" => ofBytesLE 32 (List.map V (byteAddrs a 4))
notation "rdw(" V ", " a ")" => ofBytesLE 16 (List.map V (byteAddrs a 2))

/-! ## Loads after stores -/

/-- A load apart from a store. -/
theorem rd_Vst (V : Addr → Byte) (a : Addr) (bs : List Byte) (x : Addr) (n : Nat)
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64)
    (h : a.toNat + bs.length ≤ x.toNat ∨ x.toNat + n ≤ a.toNat) :
    List.map (Vst V a bs) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  apply Vst_apart
  intro i hi e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hj hx, toNat_add_of_fits hi ha] at this
  omega

/-- A load of what a store stored. -/
theorem rd_Vst_self (V : Addr → Byte) (a : Addr) (bs : List Byte) {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) : List.map (Vst V a bs) (byteAddrs a n) = bs := by
  subst hn; exact Vst_self bs V a ha

/-! ## The call -/

/-- What stays the same through a call. -/
structure Ctx where
  /-- `rsp` after the prologue: the frame's 128 bytes. -/
  sp : Addr
  /-- `rsp` after the six `push`es. -/
  sq : Addr
  /-- The `CLzmaDec`. -/
  p : Addr
  /-- `probs_1664`, the array of probabilities from 0xd00 bytes below. -/
  P : Addr
  /-- The array's first byte, and its number of 2-byte slots. -/
  pbn : Nat
  np : Nat
  /-- The dictionary: its buffer, the buffer's size, `limit`, `dicPos` at the call. -/
  dic : Addr
  dbs : Nat
  lim : Nat
  dp0 : Nat
  /-- `bufLimit`, and `buf` at the call. -/
  bl : Addr
  b0 : Nat
  lc : Nat
  /-- The masks of the literal's and the position's states, `checkDicSize`. -/
  lpm : BitVec 32
  pbm : BitVec 32
  ckd : BitVec 32
  /-- A bound of `processedPos` at the end of the dictionary's `limit`, while `checkDicSize` is 0. -/
  ppb : Nat
  /-- The registers the prologue saves: `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`. -/
  sv : Fin 6 → BitVec 64

/-- The regions fit, apart from each other. -/
structure Ctx.Ok (K : Ctx) : Prop where
  hP : K.P.toNat = K.pbn + 0xd00
  hnp : K.pbn + 2 * K.np ≤ 2 ^ 64
  hnp0 : 0x7c0 + 0x300 ≤ K.np
  hdic : K.dic.toNat + K.dbs ≤ 2 ^ 64
  hlim : K.lim ≤ K.dbs
  hbl : K.bl.toNat + 21 ≤ 2 ^ 64
  hb0 : K.b0 ≤ K.bl.toNat
  hckd : K.ckd.toNat ≤ K.dbs
  hsq : K.sq.toNat + 56 ≤ 2 ^ 64
  hsp1 : K.sq.toNat ≤ K.sp.toNat + 255
  hsp2 : K.sp.toNat + 0x80 ≤ K.sq.toNat
  hp : K.p.toNat + 0x60 ≤ 2 ^ 64
  aFP : K.sq.toNat + 56 ≤ K.pbn ∨ K.pbn + 2 * K.np ≤ K.sp.toNat
  aFD : K.sq.toNat + 56 ≤ K.dic.toNat ∨ K.dic.toNat + K.dbs ≤ K.sp.toNat
  aFp : K.sq.toNat + 56 ≤ K.p.toNat ∨ K.p.toNat + 0x60 ≤ K.sp.toNat
  aPD : K.pbn + 2 * K.np ≤ K.dic.toNat ∨ K.dic.toNat + K.dbs ≤ K.pbn
  aPp : K.pbn + 2 * K.np ≤ K.p.toNat ∨ K.p.toNat + 0x60 ≤ K.pbn
  aDp : K.dic.toNat + K.dbs ≤ K.p.toNat ∨ K.p.toNat + 0x60 ≤ K.dic.toNat
  hlc : K.lc ≤ 8
  hpbm : K.pbm.toNat ≤ 15
  hppb : K.ppb ≤ K.dbs
  hdp0 : K.dp0 ≤ K.lim
  hnp32 : K.np < 2 ^ 31
  hlit : 0x7c0 + 3 * K.lpm.toNat * 2 ^ K.lc + 0x300 ≤ K.np

/-- A slot of the array of probabilities. -/
def InPr (K : Ctx) (a : Addr) : Prop := ∃ i, i < K.np ∧ a.toNat = K.pbn + 2 * i

/-- A slot of the array with `n` slots from it. -/
def InPrR (K : Ctx) (a : Addr) (n : Nat) : Prop := ∃ i, a.toNat = K.pbn + 2 * i ∧ i + n ≤ K.np

theorem InPrR.at {K : Ctx} {a : Addr} {n : Nat} (h : InPrR K a n) (j : Nat) (hj : j < n) {b : Addr}
    (hb : b.toNat = a.toNat + 2 * j) : InPr K b := by
  obtain ⟨i, hi, hn⟩ := h
  exact ⟨i + j, by omega, by omega⟩

/-- Bytes of the frame that no store after the prologue changes: the slots up to 0x60, and the saved registers. -/
def FrC (K : Ctx) (x : Addr) (n : Nat) : Prop :=
  (K.sp.toNat ≤ x.toNat ∧ x.toNat + n ≤ K.sp.toNat + 0x60) ∨ (K.sq.toNat ≤ x.toNat ∧ x.toNat + n ≤ K.sq.toNat + 48)

/-- Bytes a store may change freely: the dictionary's, the frame's slots from 0x60 to 0x70, the `CLzmaDec`'s. -/
def Free (K : Ctx) (a : Addr) (n : Nat) : Prop :=
  (K.dic.toNat ≤ a.toNat ∧ a.toNat + n ≤ K.dic.toNat + K.dbs) ∨
  (K.sp.toNat + 0x60 ≤ a.toNat ∧ a.toNat + n ≤ K.sp.toNat + 0x70) ∨
  (K.p.toNat ≤ a.toNat ∧ a.toNat + n ≤ K.p.toNat + 0x60)

/-- Bytes a store may change with the frame's values and the probabilities kept: the dictionary's, the frame's
slots from 0x60, the `CLzmaDec`'s. -/
def Free0 (K : Ctx) (a : Addr) (n : Nat) : Prop :=
  (K.dic.toNat ≤ a.toNat ∧ a.toNat + n ≤ K.dic.toNat + K.dbs) ∨
  (K.sp.toNat + 0x60 ≤ a.toNat ∧ a.toNat + n ≤ K.sp.toNat + 0x80) ∨
  (K.p.toNat ≤ a.toNat ∧ a.toNat + n ≤ K.p.toNat + 0x60)

/-- What the footprint's bytes keep through the call, after the prologue: the frame's values, the saved
registers, the probabilities. -/
structure Mem0 (K : Ctx) (V : Addr → Byte) : Prop where
  s0 : rdq(V, K.sp) = K.sq
  s8 : rdq(V, K.sp + 8#64) = K.p
  s28 : rdq(V, K.sp + 40#64) = BitVec.ofNat 64 K.dbs
  s30 : rdq(V, K.sp + 48#64) = K.P
  s38 : rdq(V, K.sp + 56#64) = K.dic
  s40 : rdq(V, K.sp + 64#64) = K.dic + BitVec.ofNat 64 K.lim
  s48 : rdq(V, K.sp + 72#64) = K.bl
  s50 : (rdd(V, K.sp + 80#64)).toNat % 32 = K.lc + 1
  s54 : rdd(V, K.sp + 84#64) = K.lpm
  s58 : rdd(V, K.sp + 88#64) = K.pbm
  s5c : rdd(V, K.sp + 92#64) = K.ckd
  v0 : rdq(V, K.sq) = K.sv 0
  v1 : rdq(V, K.sq + 8#64) = K.sv 1
  v2 : rdq(V, K.sq + 8#64 + 8#64) = K.sv 2
  v3 : rdq(V, K.sq + 8#64 + 8#64 + 8#64) = K.sv 3
  v4 : rdq(V, K.sq + 8#64 + 8#64 + 8#64 + 8#64) = K.sv 4
  v5 : rdq(V, K.sq + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) = K.sv 5
  pr : ∀ a, InPr K a → Pv ((rdw(V, a)).setWidth 32)

/-- And the four `reps` no larger than the dictionary's buffer. -/
structure Mem (K : Ctx) (V : Addr → Byte) : Prop extends Mem0 K V where
  r0 : (rdd(V, K.sp + 112#64)).toNat ≤ K.dbs
  r1 : (rdd(V, K.sp + 116#64)).toNat ≤ K.dbs
  r2 : (rdd(V, K.sp + 120#64)).toNat ≤ K.dbs
  r3 : (rdd(V, K.sp + 124#64)).toNat ≤ K.dbs

variable {K : Ctx} {V V' : Addr → Byte}

/-- The addresses of the frame's slots, as numbers. -/
macro "slot" : tactic => `(tactic| (
  first | (left; constructor <;> bv_omega) | (right; constructor <;> bv_omega)))

theorem Mem0.of_same (hK : K.Ok) (hM : Mem0 K V)
    (hc : ∀ x n, FrC K x n → List.map V' (byteAddrs x n) = List.map V (byteAddrs x n))
    (hpr : ∀ a, InPr K a → Pv ((rdw(V', a)).setWidth 32)) : Mem0 K V' := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  constructor
  · rw [hc _ _ (by slot)]; exact hM.s0
  · rw [hc _ _ (by slot)]; exact hM.s8
  · rw [hc _ _ (by slot)]; exact hM.s28
  · rw [hc _ _ (by slot)]; exact hM.s30
  · rw [hc _ _ (by slot)]; exact hM.s38
  · rw [hc _ _ (by slot)]; exact hM.s40
  · rw [hc _ _ (by slot)]; exact hM.s48
  · rw [hc _ _ (by slot)]; exact hM.s50
  · rw [hc _ _ (by slot)]; exact hM.s54
  · rw [hc _ _ (by slot)]; exact hM.s58
  · rw [hc _ _ (by slot)]; exact hM.s5c
  · rw [hc _ _ (by slot)]; exact hM.v0
  · rw [hc _ _ (by slot)]; exact hM.v1
  · rw [hc _ _ (by slot)]; exact hM.v2
  · rw [hc _ _ (by slot)]; exact hM.v3
  · rw [hc _ _ (by slot)]; exact hM.v4
  · rw [hc _ _ (by slot)]; exact hM.v5
  · exact hpr

/-- A store into the dictionary, the frame's slots from 0x60, or the `CLzmaDec`. -/
theorem Mem0.st_free (hK : K.Ok) (hM : Mem0 K V) {a : Addr} {bs : List Byte} (hf : Free0 K a bs.length) :
    Mem0 K (Vst V a bs) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hdic; have := hK.hp; have := hK.hnp
  have := hK.aFP; have := hK.aFD; have := hK.aFp; have := hK.aPD; have := hK.aPp
  have hfit : a.toNat + bs.length ≤ 2 ^ 64 := by unfold Free0 at hf; omega
  refine hM.of_same hK (fun x n hx => rd_Vst _ _ _ _ _ hfit (by unfold FrC at hx; omega)
    (by unfold FrC Free0 at *; omega)) (fun x hx => ?_)
  obtain ⟨i, hi, hx'⟩ := hx
  rw [rd_Vst _ _ _ _ _ hfit (by omega) (by unfold Free0 at hf; omega)]
  exact hM.pr x ⟨i, hi, hx'⟩

/-- A store into the dictionary, the frame's slots from 0x60 to 0x70, or the `CLzmaDec`. -/
theorem Mem.st_free (hK : K.Ok) (hM : Mem K V) {a : Addr} {bs : List Byte} (hf : Free K a bs.length) :
    Mem K (Vst V a bs) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hdic; have := hK.hp; have := hK.hnp
  have := hK.aFP; have := hK.aFD; have := hK.aFp; have := hK.aPD; have := hK.aPp
  have hfit : a.toNat + bs.length ≤ 2 ^ 64 := by unfold Free at hf; omega
  refine ⟨hM.toMem0.st_free hK (by unfold Free at hf; unfold Free0; omega), ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by unfold Free at hf; bv_omega)]; exact hM.r0
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by unfold Free at hf; bv_omega)]; exact hM.r1
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by unfold Free at hf; bv_omega)]; exact hM.r2
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by unfold Free at hf; bv_omega)]; exact hM.r3

/-- The four `reps` after a store into one of their slots of a value no larger than the buffer. -/
theorem Mem.st_rep (hK : K.Ok) (hM : Mem K V) {a : Addr} {v : BitVec 32} (hv : v.toNat ≤ K.dbs) (c : Nat)
    (hc : c = 112 ∨ c = 116 ∨ c = 120 ∨ c = 124) (ha : a = K.sp + BitVec.ofNat 64 c) :
    Mem K (Vst V a (toBytesLE v 4)) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  have hl : (toBytesLE v 4).length = 4 := toBytesLE_length _ _
  have hfit : a.toNat + (toBytesLE v 4).length ≤ 2 ^ 64 := by rw [hl]; subst ha; bv_omega
  have hs : (ofBytesLE 32 (toBytesLE v 4)).toNat ≤ K.dbs := by rw [ofBytesLE_toBytesLE (by rfl)]; exact hv
  refine ⟨hM.toMem0.st_free hK (by rw [hl]; right; left; subst ha; constructor <;> bv_omega), ?_, ?_, ?_, ?_⟩
  · rcases hc with rfl | rfl | rfl | rfl
    · subst ha; rw [rd_Vst_self _ _ _ hl (by bv_omega)]; exact hs
    all_goals rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r0
  · rcases hc with rfl | rfl | rfl | rfl
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r1
    · subst ha; rw [rd_Vst_self _ _ _ hl (by bv_omega)]; exact hs
    all_goals rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r1
  · rcases hc with rfl | rfl | rfl | rfl
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r2
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r2
    · subst ha; rw [rd_Vst_self _ _ _ hl (by bv_omega)]; exact hs
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r2
  · rcases hc with rfl | rfl | rfl | rfl
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r3
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r3
    · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; subst ha; bv_omega)]; exact hM.r3
    · subst ha; rw [rd_Vst_self _ _ _ hl (by bv_omega)]; exact hs

theorem pv_rt {v : BitVec 32} (hv : Pv v) :
    Pv ((ofBytesLE 16 (toBytesLE (BitVec.setWidth 16 v) 2)).setWidth 32) := by
  rw [ofBytesLE_toBytesLE (by rfl)]
  have e : (BitVec.setWidth 16 v).setWidth 32 = v := by
    apply BitVec.eq_of_toNat_eq
    have := hv.2
    simp only [BitVec.toNat_setWidth]
    omega
  rw [e]; exact hv

/-- A store of a probability into a slot of the array. -/
theorem Mem0.st_pr (hK : K.Ok) (hM : Mem0 K V) {a : Addr} (ha : InPr K a) {v : BitVec 32} (hv : Pv v) :
    Mem0 K (Vst V a (toBytesLE (BitVec.setWidth 16 v) 2)) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hnp; have := hK.aFP
  obtain ⟨i, hi, hai⟩ := ha
  have hfit : a.toNat + (toBytesLE (BitVec.setWidth 16 v) 2).length ≤ 2 ^ 64 := by
    rw [toBytesLE_length]; omega
  have hl : (toBytesLE (BitVec.setWidth 16 v) 2).length = 2 := toBytesLE_length _ _
  refine hM.of_same hK (fun x n hx => rd_Vst _ _ _ _ _ hfit (by unfold FrC at hx; omega)
    (by rw [hl]; unfold FrC at hx; omega)) (fun x hx => ?_)
  obtain ⟨j, hj, hx'⟩ := hx
  by_cases e : j = i
  · have : x = a := BitVec.eq_of_toNat_eq (by omega)
    subst this
    rw [rd_Vst_self _ _ _ hl (by omega)]
    exact pv_rt hv
  · rw [rd_Vst _ _ _ _ _ hfit (by omega) (by rw [hl]; omega)]
    exact hM.pr x ⟨j, hj, hx'⟩

theorem Mem.st_pr (hK : K.Ok) (hM : Mem K V) {a : Addr} (ha : InPr K a) {v : BitVec 32} (hv : Pv v) :
    Mem K (Vst V a (toBytesLE (BitVec.setWidth 16 v) 2)) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hnp; have := hK.aFP
  have hi := ha
  obtain ⟨i, hi, hai⟩ := hi
  have hfit : a.toNat + (toBytesLE (BitVec.setWidth 16 v) 2).length ≤ 2 ^ 64 := by
    rw [toBytesLE_length]; omega
  have hl : (toBytesLE (BitVec.setWidth 16 v) 2).length = 2 := toBytesLE_length _ _
  refine ⟨hM.toMem0.st_pr hK ha hv, ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; bv_omega)]; exact hM.r0
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; bv_omega)]; exact hM.r1
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; bv_omega)]; exact hM.r2
  · rw [rd_Vst _ _ _ _ _ hfit (by bv_omega) (by rw [hl]; bv_omega)]; exact hM.r3

/-- A load from the frame after a store into a slot of the array. -/
theorem rd_fr_pr (hK : K.Ok) {a : Addr} (ha : InPr K a) (v : BitVec 16) {x : Addr} {n : Nat} (c : Nat)
    (hx : x.toNat = K.sp.toNat + c) (hc : c + n ≤ 0x80) :
    List.map (Vst V a (toBytesLE v 2)) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hnp; have := hK.aFP
  obtain ⟨i, hi, hai⟩ := ha
  exact rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega)

/-- A load of a probability. -/
theorem Mem0.rd_pr (hM : Mem0 K V) {a : Addr} (ha : InPr K a) : Pv ((rdw(V, a)).setWidth 32) := hM.pr a ha

/-! ## The footprint -/

/-- Where the call may read and store. -/
structure Env (K : Ctx) (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  fr : ∀ y : Addr, K.sp.toNat ≤ y.toNat → y.toNat < K.sq.toNat + 48 → Foot Wl y
  pr : ∀ y : Addr, K.pbn ≤ y.toNat → y.toNat < K.pbn + 2 * K.np → Foot Wl y
  dw : ∀ y : Addr, K.dic.toNat + K.dp0 ≤ y.toNat → y.toNat < K.dic.toNat + K.lim → Foot Wl y
  dr : ∀ y : Addr, K.dic.toNat ≤ y.toNat → y.toNat < K.dic.toNat + K.dbs → Foot F.data y
  buf : ∀ y : Addr, K.b0 ≤ y.toNat → y.toNat < K.bl.toNat + 20 → Foot F.data y
  pw : ∀ y : Addr, K.p.toNat + 0x28 ≤ y.toNat → y.toNat < K.p.toNat + 0x60 → Foot Wl y
  prd : ∀ y : Addr, K.p.toNat ≤ y.toNat → y.toNat < K.p.toNat + 0x60 → Foot F.data y

variable {F : Footprint} {Wl : List Rgn}

/-- A store into a slot of the array. -/
theorem Env.wr_pr (hE : Env K F Wl) (hK : K.Ok) {a : Addr} (ha : InPr K a) : ∀ i, i < 2 → Foot Wl (a.add i) := by
  intro i hi
  obtain ⟨j, hj, haj⟩ := ha
  have := hK.hnp
  have e := toNat_add_of_fits (a := a) hi (by omega)
  exact hE.pr _ (by omega) (by omega)

/-- A load from a slot of the array. -/
theorem Env.rd_pr (hE : Env K F Wl) (hK : K.Ok) {a : Addr} (ha : InPr K a) :
    ∀ i, i < 2 → Foot F.data (a.add i) := fun i hi => hE.ws _ (hE.wr_pr hK ha i hi)

/-- A store into the frame, `n` bytes from the `c`-th. -/
theorem Env.wr_fr (hE : Env K F Wl) (hK : K.Ok) {a : Addr} {n : Nat} (c : Nat) (ha : a.toNat = K.sp.toNat + c)
    (hc : c + n ≤ 0x80) : ∀ i, i < n → Foot Wl (a.add i) := by
  intro i hi
  have := hK.hsq; have := hK.hsp2
  have e := toNat_add_of_fits (a := a) hi (by omega)
  exact hE.fr _ (by omega) (by omega)

/-- A load from the frame. -/
theorem Env.rd_fr (hE : Env K F Wl) (hK : K.Ok) {a : Addr} {n : Nat} (c : Nat) (ha : a.toNat = K.sp.toNat + c)
    (hc : c + n ≤ 0x80) : ∀ i, i < n → Foot F.data (a.add i) := fun i hi => hE.ws _ (hE.wr_fr hK c ha hc i hi)

/-- A store into the dictionary, from `dicPos` at the call up to `limit`. -/
theorem Env.wr_dic (hE : Env K F Wl) (hK : K.Ok) {a : Addr} {n : Nat} (dq : Nat) (ha : a.toNat = K.dic.toNat + dq)
    (h0 : K.dp0 ≤ dq) (hn : dq + n ≤ K.lim) : ∀ i, i < n → Foot Wl (a.add i) := by
  intro i hi
  have := hK.hdic; have := hK.hlim
  have e := toNat_add_of_fits (a := a) hi (by omega)
  exact hE.dw _ (by omega) (by omega)

/-- A load from the dictionary's buffer. -/
theorem Env.rd_dic (hE : Env K F Wl) (hK : K.Ok) {a : Addr} {n : Nat} (dq : Nat) (ha : a.toNat = K.dic.toNat + dq)
    (hn : dq + n ≤ K.dbs) : ∀ i, i < n → Foot F.data (a.add i) := by
  intro i hi
  have := hK.hdic
  have e := toNat_add_of_fits (a := a) hi (by omega)
  exact hE.dr _ (by omega) (by omega)

/-! ## The range -/

/-- The range `R` with `r15`: after at most `k` bits with probabilities and `d` direct bits since `r15` was last seen
below `bufLimit`, `c` bytes were read at or after `bufLimit`, and the range is as large as `Crd` says. -/
def Cr (K : Ctx) (k d R : Nat) (r15 : Addr) : Prop :=
  ∃ A c, Crd A d c R ∧ A ≤ 256 * 67 ^ k ∧ r15.toNat + 1 ≤ K.bl.toNat + c ∧ K.b0 ≤ r15.toNat ∧ c ≤ 21

/-- The range before a normalization. -/
def RcU (K : Ctx) (k d : Nat) (rax r15 : BitVec 64) : Prop :=
  ∃ R : BitVec 32, rax = R.setWidth 64 ∧ 2 ^ 24 ≤ 67 * R.toNat ∧ Cr K k d R.toNat r15

/-- The range after a normalization. -/
def RcN (K : Ctx) (k d : Nat) (R : BitVec 32) (r15 : BitVec 64) : Prop := 2 ^ 24 ≤ R.toNat ∧ Cr K k d R.toNat r15

/-- The bits a symbol may take: 22 with probabilities and 26 direct ones, or 23 with probabilities. -/
def Bg (k d : Nat) : Prop := (k ≤ 22 ∧ d ≤ 26) ∨ (k ≤ 23 ∧ d = 0)

theorem Cr.mono {k d k' d' R : Nat} {r15 : Addr} (h : Cr K k d R r15) (hk : k ≤ k') (hd : d ≤ d') :
    Cr K k' d' R r15 := by
  obtain ⟨A, c, hc, hA, h1, h2, h3⟩ := h
  exact ⟨A, c, crd_mono_d hc hd,
    Nat.le_trans hA (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)), h1, h2, h3⟩

theorem RcU.mono {k d k' d' : Nat} {rax r15 : BitVec 64} (h : RcU K k d rax r15) (hk : k ≤ k') (hd : d ≤ d') :
    RcU K k' d' rax r15 := by
  obtain ⟨R, e, hR, hc⟩ := h
  exact ⟨R, e, hR, hc.mono hk hd⟩

theorem RcN.mono {k d k' d' : Nat} {R : BitVec 32} {r15 : BitVec 64} (h : RcN K k d R r15) (hk : k ≤ k')
    (hd : d ≤ d') : RcN K k' d' R r15 := ⟨h.1, h.2.mono hk hd⟩

theorem Cr.model {k d R R' : Nat} {r15 : Addr} (h : Cr K k d R r15) (hR : R ≤ 67 * R') : Cr K (k + 1) d R' r15 := by
  obtain ⟨A, c, hc, hA, h1, h2, h3⟩ := h
  refine ⟨67 * A, c, crd_model hc hR, ?_, h1, h2, h3⟩
  rw [Nat.pow_succ]
  calc 67 * A ≤ 67 * (256 * 67 ^ k) := Nat.mul_le_mul_left _ hA
    _ = 256 * (67 ^ k * 67) := by ac_rfl

/-- A bit 0 with a probability: the range is the bound. -/
theorem RcN.bit0 {k d : Nat} {R P : BitVec 32} {r15 : BitVec 64} (h : RcN K k d R r15) (hP : Pv P) :
    RcU K (k + 1) d ((R >>> 11 * P).setWidth 64) r15 := by
  obtain ⟨h1, h2, h3, h4⟩ := bit_bound R P h.1 hP.1 hP.2
  have := h.1
  exact ⟨_, rfl, by omega, h.2.model h2⟩

/-- A bit 1 with a probability: the range less the bound. -/
theorem RcN.bit1 {k d : Nat} {R P : BitVec 32} {r15 : BitVec 64} (h : RcN K k d R r15) (hP : Pv P) :
    RcU K (k + 1) d ((R - R >>> 11 * P).setWidth 64) r15 := by
  obtain ⟨h1, h2, h3, h4⟩ := bit_bound R P h.1 hP.1 hP.2
  have := h.1
  exact ⟨_, rfl, by omega, h.2.model h4⟩

/-- A bit with a probability, without a branch. -/
theorem RcN.bit {k d : Nat} {R P : BitVec 32} {r15 : BitVec 64} (h : RcN K k d R r15) (hP : Pv P) (b : Bool) :
    RcU K (k + 1) d ((if b = true then R - R >>> 11 * P else R >>> 11 * P).setWidth 64) r15 := by
  cases b
  · exact h.bit0 hP
  · exact h.bit1 hP

/-- A direct bit. -/
theorem RcN.dir {k d : Nat} {R : BitVec 32} {r15 : BitVec 64} (h : RcN K k d R r15) :
    RcU K k (d + 1) ((R >>> 1).setWidth 64) r15 := by
  obtain ⟨h1, h2, h3⟩ := dir_bound R h.1
  obtain ⟨A, c, hc, hA, h4, h5, h6⟩ := h.2
  exact ⟨_, rfl, by omega, A, c, crd_direct hc h1 (by omega), hA, h4, h5, h6⟩

/-- With `r15` below `bufLimit`, a new count. -/
theorem RcU.reset {k d : Nat} {rax r15 : BitVec 64} (h : RcU K k d rax r15) (hl : r15.toNat < K.bl.toNat) :
    RcU K 0 0 rax r15 := by
  obtain ⟨R, e, hR, A, c, hc, hA, h1, h2, h3⟩ := h
  refine ⟨R, e, hR, 67, 0, ?_, by decide, by omega, h2, by omega⟩
  unfold Crd; omega

/-- At the call: a range of at least `2^24`, `buf` at most `bufLimit`. -/
theorem RcU.init {R : BitVec 32} {r15 : BitVec 64} (hR : 2 ^ 24 ≤ R.toNat) (h0 : K.b0 ≤ r15.toNat)
    (hl : r15.toNat ≤ K.bl.toNat) : RcU K 0 0 (R.setWidth 64) r15 := by
  refine ⟨R, rfl, by omega, 256, 1, ?_, by decide, by omega, h0, by omega⟩
  unfold Crd; omega

/-- A normalization: from `RcU`, with `RcN` after, the read within 20 bytes of `bufLimit`. -/
theorem wnorm_of (hE : Env K F Wl) (hK : K.Ok) {e k d : Nat} {Q : Post} {f : Rflags}
    {rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64}
    (hb : Bg k d) (hU : RcU K k d rax r15)
    (hq : ∀ (R : BitVec 32) (rbp' r15' : BitVec 64), RcN K k d R r15' → ∀ fl,
      Q e ⟨R.setWidth 64, rcx, rdx, rbx, rsp, rbp', rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15'⟩ fl V) :
    Wnorm e F Wl Q ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ f V := by
  obtain ⟨R, rfl, hR, A, c, hc, hA, h1, h2, h3⟩ := hU
  have hbl := hK.hbl
  simp only [Wnorm, sw_64_32]
  refine ⟨fun h fl => hq R rbp r15 ⟨h, A, c, hc, hA, h1, h2, h3⟩ fl, fun h => ?_⟩
  have hc20 : c ≤ 20 := by
    rcases hb with ⟨hk, hd⟩ | ⟨hk, rfl⟩
    · exact crd_bound hc (Nat.le_trans hA (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk))) hd h
    · exact crd_bound' hc (Nat.le_trans hA (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk))) h
  refine ⟨hE.buf _ h2 (by omega), fun fl rbp' => hq (R <<< 8) rbp' (r15 + 1) ?_ fl⟩
  have e8 : (R <<< 8).toNat = 256 * R.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have e15 : (r15 + 1).toNat = r15.toNat + 1 := by bv_omega
  refine ⟨by omega, A, c + 1, ?_, hA, by omega, by omega, by omega⟩
  rw [e8]; exact crd_read hc

/-- `buf` stays within 20 bytes of `bufLimit`. -/
theorem Cr.r15 {k d R : Nat} {r15 : Addr} (h : Cr K k d R r15) :
    K.b0 ≤ r15.toNat ∧ r15.toNat ≤ K.bl.toNat + 20 := by
  obtain ⟨A, c, _, _, h1, h2, h3⟩ := h
  omega

end FV7z.Lzma
