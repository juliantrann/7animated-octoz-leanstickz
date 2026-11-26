import FV7z.Tdm.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `LzmaDec_TryDummy`: the invariant (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_TryDummy (p, buf, bufOut)` at `0x42af80` in `7zzs` (`C/LzmaDec.c`; `objdump -d`): the range
decoder's dry run over one symbol from `buf` (`rsi`) up to `*bufOut` (`[rdx]`), on the decoder `p` (`rdi`); it reads
the probabilities, the dictionary and `buf[..]`, and stores only `*bufOut = buf'` (at 340), returning the kind of the
symbol (`r12d`: 0 when the input runs out, 1 a literal, 2 a match, 3 a rep).

- `Ctx`: the values the proof names: the registers and the bytes at the entry (`g0`, `V0`), the bytes after the five
  pushes (`V1`), `*bufOut` (`B`), `probs_1664` (`P`, the 8 bytes at `p + 16`), `dic` (`D`), `dicBufSize` (`dbs`),
  `lc`, `lp` (the bytes at `p`, `p + 1`). `Ok`: what the entry gives about them; `Env`: the bytes the code reads and
  writes.
- `Cm`: what holds at every cut point but the entry (the stack, `rdx`, `r9 = B`, `r15`, `buf ≤ rsi ≤ B`).
- `I*`, `M*`: the cut points' conditions and measures; `Inv`, `Fz` (at the `ret`s, 354 and 765), `Nx` (the post of
  `Seg.cfg`); `x*`: the exits into them.
- `fP`, `fIn`, `fD`, `fA`: the reads (probabilities, input, dictionary, the decoder).
- `ctx_ok`, `mask16`, `slot_sa`, `and_cases`, `xor_cases`: the bounds of the computed indices.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tdm
set_option maxRecDepth 100000

/-- The values the proof names. -/
structure Ctx where
  g0 : Gprs
  V0 : Addr → Byte
  V1 : Addr → Byte
  B : Addr
  P : Addr
  D : Addr
  dbs : Nat
  lc : Nat
  lp : Nat

/-- `rsp` after the five pushes. -/
def Ctx.sp (K : Ctx) : Addr := K.g0.rsp - 8 - 8 - 8 - 8 - 8
/-- The number of literal coders, `2 ^ (lc + lp)`. -/
def Ctx.nl (K : Ctx) : Nat := 2 ^ (K.lc + K.lp)

/-- What the entry gives: `V1` the bytes after the pushes, `B` = `*bufOut`, `P`, `D`, `dbs`, `lc`, `lp` the decoder's;
`dicPos < dicBufSize`, `rep0 ≤ dicBufSize`, `state < 12`, `pb ≤ 4`, `lc ≤ 8`, `lp ≤ 4`; the probabilities and the
dictionary inside the address space; `buf ≤ *bufOut`. -/
structure Ok (K : Ctx) : Prop where
  eV1 : K.V1 = Vst (Vst (Vst (Vst (Vst K.V0 (K.g0.rsp - 8) (toBytesLE K.g0.r14 8)) (K.g0.rsp - 8 - 8)
    (toBytesLE K.g0.r13 8)) (K.g0.rsp - 8 - 8 - 8) (toBytesLE K.g0.r12 8)) (K.g0.rsp - 8 - 8 - 8 - 8)
    (toBytesLE K.g0.rbp 8)) (K.g0.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE K.g0.rbx 8)
  eB : ofBytesLE 64 (List.map (Vst K.V0 (K.g0.rsp - 8) (toBytesLE K.g0.r14 8)) (byteAddrs K.g0.rdx 8)) = K.B
  eP : rdq(K.V1, K.g0.rdi + 16#64) = K.P
  eD : rdq(K.V1, K.g0.rdi + 24#64) = K.D
  edbs : rdq(K.V1, K.g0.rdi + 32#64).toNat = K.dbs
  hdp : rdq(K.V1, K.g0.rdi + 40#64).toNat < K.dbs
  hrep : rdd(K.V1, K.g0.rdi + 72#64).toNat ≤ K.dbs
  hst : rdd(K.V1, K.g0.rdi + 88#64).toNat < 12
  hpb : (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.g0.rdi + 2#64) 1))).toNat ≤ 4
  elc : (ofBytesLE 8 (List.map K.V1 (byteAddrs K.g0.rdi 1))).toNat = K.lc
  elp : (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.g0.rdi + 1#64) 1))).toNat = K.lp
  hlc : K.lc ≤ 8
  hlp : K.lp ≤ 4
  hP1 : 3328 ≤ K.P.toNat
  hP2 : K.P.toNat + 640 + 1536 * K.nl ≤ 2 ^ 64
  hD : K.D.toNat + K.dbs ≤ 2 ^ 64
  hB : K.g0.rsi.toNat ≤ K.B.toNat

theorem Ok.hnl {K : Ctx} (hK : Ok K) : K.nl ≤ 4096 := by
  have h1 := hK.hlc
  have h2 := hK.hlp
  unfold Ctx.nl
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : K.lc + K.lp ≤ 12)) (by decide)

theorem Ok.hnl1 {K : Ctx} (_ : Ok K) : 1 ≤ K.nl := Nat.one_le_two_pow

/-- The bytes the code reads and writes: the decoder's first 96, `*bufOut`, the input up to `B`, the probabilities
(`1984 + 768 * nl` of 2 bytes from `P - 3328`), the dictionary, the five stack slots. -/
structure Env (K : Ctx) (F : Footprint) (Wl : List Rgn) : Prop where
  hp : ∀ i < 96, Foot F.data (Addr.add K.g0.rdi i)
  hbo : ∀ i < 8, Foot F.data (Addr.add K.g0.rdx i)
  wbo : ∀ i < 8, Foot Wl (Addr.add K.g0.rdx i)
  hin : ∀ i < K.B.toNat - K.g0.rsi.toNat, Foot F.data (Addr.add K.g0.rsi i)
  hpr : ∀ i < 2 * (1984 + 768 * K.nl), Foot F.data (Addr.add (K.P - 3328#64) i)
  hdic : ∀ i < K.dbs, Foot F.data (Addr.add K.D i)
  w1 : ∀ i < 8, Foot Wl (Addr.add (K.g0.rsp - 8) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (K.g0.rsp - 8 - 8) i)
  w3 : ∀ i < 8, Foot Wl (Addr.add (K.g0.rsp - 8 - 8 - 8) i)
  w4 : ∀ i < 8, Foot Wl (Addr.add (K.g0.rsp - 8 - 8 - 8 - 8) i)
  w5 : ∀ i < 8, Foot Wl (Addr.add (K.g0.rsp - 8 - 8 - 8 - 8 - 8) i)
  f0 : ∀ i < 8, Foot F.data (Addr.add K.sp i)
  f1 : ∀ i < 8, Foot F.data (Addr.add (K.sp + 8) i)
  f2 : ∀ i < 8, Foot F.data (Addr.add (K.sp + 8 + 8) i)
  f3 : ∀ i < 8, Foot F.data (Addr.add (K.sp + 8 + 8 + 8) i)
  f4 : ∀ i < 8, Foot F.data (Addr.add (K.sp + 8 + 8 + 8 + 8) i)

/-- At every cut point but the entry: the stack, `rdx`, `r9 = B`, `r15` as set, `buf ≤ rsi ≤ B`. -/
structure Cm (K : Ctx) (g : Gprs) : Prop where
  sp : g.rsp = K.sp
  dx : g.rdx = K.g0.rdx
  r9 : g.r9 = K.B
  r15 : g.r15 = K.g0.r15
  s1 : K.g0.rsi.toNat ≤ g.rsi.toNat
  s2 : g.rsi.toNat ≤ K.B.toNat

/-- The literal context from `x` (the masked and shifted `processedPos`), `y` (`lc`) and any previous byte is below
`nl`. -/
def CtxOk (K : Ctx) (x y : BitVec 64) : Prop := ∀ b : BitVec 8,
  (BitVec.setWidth 32 x + BitVec.setWidth 32 b >>> ((BitVec.setWidth 8 (8#32 - BitVec.setWidth 32 y)).toNat % 32)).toNat
    < K.nl

/-- `(processedPos & ((1 << lp) - 1)) << lc`, as the code computes it. -/
def cx (r : BitVec 64) (cb pb : BitVec 8) : BitVec 64 :=
  BitVec.setWidth 64 ((BitVec.setWidth 32 r &&& ~~~(4294967295#32 <<< ((BitVec.setWidth 8 (BitVec.setWidth 32 pb)).toNat
    % 32))) <<< ((BitVec.setWidth 8 (BitVec.setWidth 32 cb)).toNat % 32))

/-- `a + 2 * x * 2 ^ c ≤ X` for `c ≤ 5`. -/
def Bnd (a c x X : Nat) : Prop :=
  (c = 0 ∧ a + 2 * x ≤ X) ∨ (c = 1 ∧ a + 4 * x ≤ X) ∨ (c = 2 ∧ a + 8 * x ≤ X) ∨ (c = 3 ∧ a + 16 * x ≤ X) ∨
  (c = 4 ∧ a + 32 * x ≤ X) ∨ (c = 5 ∧ a + 64 * x ≤ X)

/-! ## Tactics -/

/-- The jumps' conditions as facts, then `bv_omega`. -/
scoped macro "tfo" : tactic => `(tactic| ((try simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true,
  Bool.or_eq_false_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq,
  beq_eq_false_iff_ne, Bnd, ne_eq] at *) <;> bv_omega))
/-- A cut point's condition: its conjuncts by `assumption`, `rfl` or `tfo`. -/
scoped macro "tf1" : tactic =>
  `(tactic| first | assumption | exact trivial | (with_reducible rfl) | (with_reducible apply And.intro))
scoped macro "tfs" : tactic => `(tactic| ((repeat' tf1) <;> tfo))
/-- `Cm` after a stretch. -/
scoped macro "tcm" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, by tfo, by tfo⟩)
/-- `I343` after a stretch: no store and `r12d` 0, or the store and the result. -/
scoped macro "t343" : tactic =>
  `(tactic| first | exact Or.inl ⟨by tfo, rfl⟩ | exact Or.inr ⟨⟨by tfo, by tfo⟩, rfl⟩)
/-- `FinR.v` at a `ret`. -/
scoped macro "tfv" : tactic => `(tactic| first | exact Or.inl ⟨by tfo, rfl⟩ | exact Or.inr ⟨by tfo, by tfo, rfl⟩)

/-! ## Bounds -/

theorem andl {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

theorem andr {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ y.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

/-- `processedPos & ((1 << pb) - 1)` is below 16. -/
theorem mask16 (b : BitVec 8) (x : BitVec 32) (h : b.toNat ≤ 4) :
    (~~~(4294967295#32 <<< ((BitVec.setWidth 8 (BitVec.setWidth 32 b)).toNat % 32)) &&& x).toNat < 16 := by
  have e : (BitVec.setWidth 8 (BitVec.setWidth 32 b)).toNat % 32 = b.toNat := by bv_omega
  rw [e]
  have hm := andl (~~~(4294967295#32 <<< b.toNat)) x
  generalize b.toNat = p at *
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl | rfl | rfl <;> bv_omega

theorem ctx_core (r : BitVec 32) (cb pb b : BitVec 8) (hc : cb.toNat ≤ 8) (hp : pb.toNat ≤ 4) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 ((r &&& ~~~(4294967295#32 <<< ((BitVec.setWidth 8
      (BitVec.setWidth 32 pb)).toNat % 32))) <<< ((BitVec.setWidth 8 (BitVec.setWidth 32 cb)).toNat % 32))) +
      BitVec.setWidth 32 b >>> ((BitVec.setWidth 8 (8#32 - BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 cb)))).toNat % 32)).toNat < 2 ^ (cb.toNat + pb.toNat) := by
  have e1 : (BitVec.setWidth 8 (BitVec.setWidth 32 pb)).toNat % 32 = pb.toNat := by bv_omega
  have e2 : (BitVec.setWidth 8 (BitVec.setWidth 32 cb)).toNat % 32 = cb.toNat := by bv_omega
  have e3 : (BitVec.setWidth 8 (8#32 - BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 cb)))).toNat % 32
      = 8 - cb.toNat := by bv_omega
  rw [e1, e2, e3]
  have hm := andr r (~~~(4294967295#32 <<< pb.toNat))
  have hb := b.isLt
  generalize cb.toNat = c at *
  generalize pb.toNat = p at *
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl | rfl | rfl <;>
  (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceSub]) <;> bv_omega

/-- The literal context of any previous byte is below `nl`. -/
theorem ctx_ok {K : Ctx} (hK : Ok K) (r : BitVec 64) :
    CtxOk K (cx r (ofBytesLE 8 (List.map K.V1 (byteAddrs K.g0.rdi 1)))
      (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.g0.rdi + 1#64) 1))))
      (BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 (List.map K.V1 (byteAddrs K.g0.rdi 1))))) := by
  unfold CtxOk cx Ctx.nl
  intro b
  rw [← hK.elc, ← hK.elp]
  exact ctx_core _ _ _ b (by rw [hK.elc]; exact hK.hlc) (by rw [hK.elp]; exact hK.hlp)

/-- The position slot `ps` of a distance: below 4, above 13, or `ps >> 1 - 1` direct bits from `2 * sa` with
`2 * sa + 2 * 2 ^ (ps >> 1 - 1) ≤ 256`. -/
theorem slot_sa (ps : BitVec 32) : ps.toNat < 4 ∨ 13 < ps.toNat ∨ (1 ≤ (ps >>> 1 - 1#32).toNat ∧
    Bnd (2 * ((ps &&& 1#32 ||| 2#32) <<< ((BitVec.setWidth 8 (ps >>> 1 - 1#32)).toNat % 32)).toNat)
      (ps >>> 1 - 1#32).toNat 1 256) := by
  rcases (by omega : ps.toNat < 4 ∨ 13 < ps.toNat ∨ (4 ≤ ps.toNat ∧ ps.toNat ≤ 13)) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    have : ps = 4#32 ∨ ps = 5#32 ∨ ps = 6#32 ∨ ps = 7#32 ∨ ps = 8#32 ∨ ps = 9#32 ∨ ps = 10#32 ∨ ps = 11#32 ∨
        ps = 12#32 ∨ ps = 13#32 := by bv_omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Bnd] <;> decide

/-- `r10 & (2 * matchByte)` with `r10` 0 or 256: 0 or `r10`. -/
theorem and_cases (x y : BitVec 32) (h : x.toNat = 0 ∨ x.toNat = 256) :
    (x &&& y).toNat = 0 ∨ (x &&& y).toNat = x.toNat := by
  rcases h with h | h
  · have : x = 0#32 := by bv_omega
    subst this
    left; simp
  · have : x = BitVec.twoPow 32 8 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_twoPow]; omega
    subst this
    rw [BitVec.twoPow_and]
    split
    · right; rfl
    · left; rfl

/-- `r10 ^ ebp` stays 0 or 256. -/
theorem xor_cases (x y : BitVec 32)
    (h : (x.toNat = 0 ∧ y.toNat = 0) ∨ (x.toNat = 256 ∧ (y.toNat = 0 ∨ y.toNat = 256))) :
    (x ^^^ y).toNat = 0 ∨ (x ^^^ y).toNat = 256 := by
  have : (x = 0#32 ∧ y = 0#32) ∨ (x = 256#32 ∧ (y = 0#32 ∨ y = 256#32)) := by bv_omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide

/-! ## Reads -/

variable {K : Ctx} {F : Footprint} {Wl : List Rgn}

/-- Two bytes of the probabilities. -/
theorem fP (hK : Ok K) (hE : Env K F Wl) {x : Addr} (h1 : K.P.toNat ≤ x.toNat + 3328)
    (h2 : x.toNat + 2 ≤ K.P.toNat + 640 + 1536 * K.nl) : ∀ i < 2, Foot F.data (Addr.add x i) := by
  intro i hi
  have h3 := hK.hP1
  have h := hE.hpr (x.toNat + 3328 - K.P.toNat + i) (by omega)
  have e : Addr.add (K.P - 3328#64) (x.toNat + 3328 - K.P.toNat + i) = Addr.add x i := by
    simp only [Addr.add]; bv_omega
  rwa [e] at h

/-- A byte of the input. -/
theorem fIn (hE : Env K F Wl) {x : Addr} (h1 : K.g0.rsi.toNat ≤ x.toNat) (h2 : x.toNat < K.B.toNat) :
    ∀ i < 1, Foot F.data (Addr.add x i) := by
  intro i hi
  have h := hE.hin (x.toNat - K.g0.rsi.toNat + i) (by omega)
  have e : Addr.add K.g0.rsi (x.toNat - K.g0.rsi.toNat + i) = Addr.add x i := by
    simp only [Addr.add]; bv_omega
  rwa [e] at h

/-- A byte of the dictionary. -/
theorem fD (hE : Env K F Wl) {x : Addr} (h1 : K.D.toNat ≤ x.toNat) (h2 : x.toNat < K.D.toNat + K.dbs) :
    ∀ i < 1, Foot F.data (Addr.add x i) := by
  intro i hi
  have h := hE.hdic (x.toNat - K.D.toNat + i) (by omega)
  have e : Addr.add K.D (x.toNat - K.D.toNat + i) = Addr.add x i := by
    simp only [Addr.add]; bv_omega
  rwa [e] at h

/-- Bytes `k ..< k + m` of a range of `n`. -/
theorem fA {R : List Rgn} {b : Addr} {n : Nat} (h : ∀ i < n, Foot R (Addr.add b i)) {k m : Nat}
    (hk : k + m ≤ n) : ∀ i < m, Foot R (Addr.add (b + BitVec.ofNat 64 k) i) := fun i hi => by
  rw [show Addr.add (b + BitVec.ofNat 64 k) i = Addr.add b (k + i) from addr_add_add' b k i]
  exact h (k + i) (by omega)

theorem fA0 {R : List Rgn} {b : Addr} {n : Nat} (h : ∀ i < n, Foot R (Addr.add b i)) {m : Nat}
    (hk : m ≤ n) : ∀ i < m, Foot R (Addr.add b i) := fun i hi => h i (by omega)

/-! ## The cut points' conditions -/

/-- At the `ret`s: the registers popped, `rax` the result, the bytes `V1` or with `*bufOut = rsi`. -/
structure FinR (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop where
  sp : g.rsp = K.sp + 8 + 8 + 8 + 8 + 8
  dx : g.rdx = K.g0.rdx
  r9 : g.r9 = K.B
  r15 : g.r15 = K.g0.r15
  bx : g.rbx = rdq(V, K.sp)
  bp : g.rbp = rdq(V, K.sp + 8)
  x12 : g.r12 = rdq(V, K.sp + 8 + 8)
  x13 : g.r13 = rdq(V, K.sp + 8 + 8 + 8)
  x14 : g.r14 = rdq(V, K.sp + 8 + 8 + 8 + 8)
  s1 : K.g0.rsi.toNat ≤ g.rsi.toNat
  s2 : g.rsi.toNat ≤ K.B.toNat
  v : (g.rax.toNat = 0 ∧ V = K.V1) ∨ (1 ≤ g.rax.toNat ∧ g.rax.toNat ≤ 3 ∧ V = Vst K.V1 K.g0.rdx (toBytesLE g.rsi 8))

/-- At 343: `r12d` 0 and no store, or the result and `*bufOut = rsi`. -/
def I343 (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop :=
  (g.r12.toNat = 0 ∧ V = K.V1) ∨ ((1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3) ∧ V = Vst K.V1 K.g0.rdx (toBytesLE g.rsi 8))

set_option linter.unusedVariables false

/-- The condition at 103. -/
def I103 (K : Ctx) (g : Gprs) : Prop :=
  g.rdi = K.g0.rdi ∧ g.r11 = K.P ∧ g.r10.toNat < 12 ∧ g.r13.toNat < 512 ∧ g.rcx.toNat ≤ 240
def M103 (g : Gprs) : Nat := 6200

/-- The condition at 180. -/
def I180 (K : Ctx) (g : Gprs) : Prop :=
  g.rdi = K.g0.rdi ∧ g.rcx.toNat < K.dbs ∧ g.r13 = K.D ∧ CtxOk K g.rbx g.r12 ∧ g.r11 = K.P + 640#64
def M180 (g : Gprs) : Nat := 6100

/-- The condition at 210. -/
def I210 (K : Ctx) (g : Gprs) : Prop :=
  g.rdi = K.g0.rdi ∧ K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl
def M210 (g : Gprs) : Nat := 6000

/-- The condition at 248. -/
def I248 (K : Ctx) (g : Gprs) : Prop :=
  K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < 256
def M248 (g : Gprs) : Nat := 4000 + 3 * (512 - g.rdi.toNat)

/-- The condition at 288. -/
def I288 (K : Ctx) (g : Gprs) : Prop :=
  K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < 256
def M288 (g : Gprs) : Nat := 3999 + 3 * (512 - g.rdi.toNat)

/-- The condition at 314. -/
def I314 (K : Ctx) (g : Gprs) : Prop := True
def M314 (g : Gprs) : Nat := 5

/-- The condition at 320. -/
def I320 (K : Ctx) (g : Gprs) : Prop := 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M320 (g : Gprs) : Nat := 4

/-- The condition at 340. -/
def I340 (K : Ctx) (g : Gprs) : Prop := 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M340 (g : Gprs) : Nat := 3

def M343 (g : Gprs) : Nat := 2

/-- The condition at 411. -/
def I411 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rbx.toNat ≤ 54 ∧ g.r13.toNat < 512 ∧ g.rcx.toNat ≤ 240
def M411 (g : Gprs) : Nat := 3100

/-- The condition at 443. -/
def I443 (K : Ctx) (g : Gprs) : Prop :=
  (g.r10.toNat + 2560 = K.P.toNat ∨ g.r10.toNat + 1536 = K.P.toNat) ∧ g.r11 = K.P ∧ g.rcx.toNat ≤ 240 ∧
    1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M443 (g : Gprs) : Nat := 2500

/-- The condition at 481. -/
def I481 (K : Ctx) (g : Gprs) : Prop :=
  (g.r10.toNat + 2560 = K.P.toNat ∨ g.r10.toNat + 1536 = K.P.toNat) ∧ g.r11 = K.P ∧ g.rcx.toNat ≤ 240 ∧
    1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M481 (g : Gprs) : Nat := 2400

/-- The condition at 510. -/
def I510 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 2 ≤ g.rbx.toNat ∧ g.rbx.toNat ≤ 256 ∧
    K.P.toNat ≤ g.r10.toNat + 3328 ∧ g.r10.toNat + 2 * g.rbx.toNat ≤ K.P.toNat + 640
def M510 (g : Gprs) : Nat := 2200

/-- The condition at 532. -/
def I532 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 2 ≤ g.rbx.toNat ∧ g.rbx.toNat ≤ 256 ∧
    K.P.toNat ≤ g.r10.toNat + 3328 ∧ g.r10.toNat + 2 * g.rbx.toNat ≤ K.P.toNat + 640 ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < g.rbx.toNat
def M532 (g : Gprs) : Nat := 600 + 3 * (512 - g.rdi.toNat)

/-- The condition at 572. -/
def I572 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 2 ≤ g.rbx.toNat ∧ g.rbx.toNat ≤ 256 ∧
    K.P.toNat ≤ g.r10.toNat + 3328 ∧ g.r10.toNat + 2 * g.rbx.toNat ≤ K.P.toNat + 640 ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < g.rbx.toNat
def M572 (g : Gprs) : Nat := 599 + 3 * (512 - g.rdi.toNat)

/-- The condition at 594. -/
def I594 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M594 (g : Gprs) : Nat := 500

/-- The condition at 648. -/
def I648 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 2 ≤ g.rbx.toNat ∧ g.rbx.toNat < 128 ∧ 64 ≤ g.rdi.toNat ∧
    g.rdi.toNat ≤ 256
def M648 (g : Gprs) : Nat := 100 + 3 * (128 - g.rbx.toNat)

/-- The condition at 657. -/
def I657 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rbx.toNat ∧ g.rbx.toNat < 64 ∧ 64 ≤ g.rdi.toNat ∧
    g.rdi.toNat ≤ 256
def M657 (g : Gprs) : Nat := 99 + 3 * (128 - g.rbx.toNat)

/-- The condition at 696. -/
def I696 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rbx.toNat ∧ g.rbx.toNat < 64 ∧ 64 ≤ g.rdi.toNat ∧
    g.rdi.toNat ≤ 256
def M696 (g : Gprs) : Nat := 98 + 3 * (128 - g.rbx.toNat)

/-- The condition at 751. -/
def I751 (K : Ctx) (g : Gprs) : Prop := True
def M751 (g : Gprs) : Nat := 1

/-- The condition at 794. -/
def I794 (K : Ctx) (g : Gprs) : Prop :=
  g.rbx.toNat < K.dbs ∧ g.rbp = K.D ∧ K.P.toNat + 640 ≤ g.r11.toNat ∧
    g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl
def M794 (g : Gprs) : Nat := 5600

/-- The condition at 821. -/
def I821 (K : Ctx) (g : Gprs) : Prop :=
  K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl ∧ 2 ≤ g.rdi.toNat ∧
    g.rdi.toNat < 512 ∧ (g.r10.toNat = 0 ∨ g.r10.toNat = 256)
def M821 (g : Gprs) : Nat := 4000 + 3 * (512 - g.rdi.toNat)

/-- The condition at 833. -/
def I833 (K : Ctx) (g : Gprs) : Prop :=
  K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < 256 ∧ (g.r10.toNat = 0 ∨ g.r10.toNat = 256)
def M833 (g : Gprs) : Nat := 3999 + 3 * (512 - g.rdi.toNat)

/-- The condition at 880. -/
def I880 (K : Ctx) (g : Gprs) : Prop :=
  K.P.toNat + 640 ≤ g.r11.toNat ∧ g.r11.toNat + 1536 ≤ K.P.toNat + 640 + 1536 * K.nl ∧ 1 ≤ g.rdi.toNat ∧
    g.rdi.toNat < 256 ∧
    ((g.r10.toNat = 0 ∧ g.rbp.toNat = 0) ∨ (g.r10.toNat = 256 ∧ (g.rbp.toNat = 0 ∨ g.rbp.toNat = 256)))
def M880 (g : Gprs) : Nat := 3998 + 3 * (512 - g.rdi.toNat)

/-- The condition at 960. -/
def I960 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rbx.toNat ≤ 54 ∧ g.r13.toNat < 512 ∧ g.rcx.toNat ≤ 240
def M960 (g : Gprs) : Nat := 3000

/-- The condition at 1024. -/
def I1024 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rcx.toNat ≤ 240
def M1024 (g : Gprs) : Nat := 2900

/-- The condition at 1105. -/
def I1105 (K : Ctx) (g : Gprs) : Prop :=
  (g.r10.toNat + 2560 = K.P.toNat ∨ g.r10.toNat + 1536 = K.P.toNat) ∧ g.r11 = K.P ∧ g.rcx.toNat ≤ 240 ∧
    1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3
def M1105 (g : Gprs) : Nat := 2300

/-- The condition at 1200. -/
def I1200 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rbx.toNat ≤ 54 ∧ g.rcx.toNat ≤ 240
def M1200 (g : Gprs) : Nat := 2800

/-- The condition at 1261. -/
def I1261 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rcx.toNat ≤ 240
def M1261 (g : Gprs) : Nat := 2700

/-- The condition at 1288. -/
def I1288 (K : Ctx) (g : Gprs) : Prop := g.r11 = K.P ∧ g.rcx.toNat ≤ 240
def M1288 (g : Gprs) : Nat := 2600

/-- The condition at 1400. -/
def I1400 (K : Ctx) (g : Gprs) : Prop :=
  1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rcx.toNat ∧ K.P.toNat ≤ g.r11.toNat + 3328 ∧
    Bnd g.r11.toNat g.rcx.toNat 1 (K.P.toNat + 640)
def M1400 (g : Gprs) : Nat := 28

/-- The condition at 1420. -/
def I1420 (K : Ctx) (g : Gprs) : Prop :=
  1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rcx.toNat ∧ K.P.toNat ≤ g.r11.toNat + 3328 ∧
    Bnd g.r11.toNat (g.rcx.toNat - 1) g.r10.toNat (K.P.toNat + 640) ∧ g.r10.toNat ≤ g.rbx.toNat ∧
    g.rbx.toNat < 2 * g.r10.toNat
def M1420 (g : Gprs) : Nat := 10 + 3 * g.rcx.toNat

/-- The condition at 1432. -/
def I1432 (K : Ctx) (g : Gprs) : Prop :=
  1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rcx.toNat ∧ K.P.toNat ≤ g.r11.toNat + 3328 ∧
    Bnd g.r11.toNat g.rcx.toNat g.rbp.toNat (K.P.toNat + 640) ∧ g.rbp.toNat ≤ g.rbx.toNat ∧
    g.rbx.toNat < 2 * g.rbp.toNat
def M1432 (g : Gprs) : Nat := 12 + 3 * g.rcx.toNat

/-- The condition at 1472. -/
def I1472 (K : Ctx) (g : Gprs) : Prop :=
  1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rcx.toNat ∧ K.P.toNat ≤ g.r11.toNat + 3328 ∧
    Bnd g.r11.toNat g.rcx.toNat g.rbp.toNat (K.P.toNat + 640) ∧ g.rbp.toNat ≤ g.rbx.toNat ∧
    g.rbx.toNat < 2 * g.rbp.toNat
def M1472 (g : Gprs) : Nat := 11 + 3 * g.rcx.toNat

/-- The condition at 1504. -/
def I1504 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rdi.toNat ∧ g.rdi.toNat ≤ 26
def M1504 (g : Gprs) : Nat := 31 + 2 * g.rdi.toNat

/-- The condition at 1537. -/
def I1537 (K : Ctx) (g : Gprs) : Prop :=
  g.r11 = K.P ∧ 1 ≤ g.r12.toNat ∧ g.r12.toNat ≤ 3 ∧ 1 ≤ g.rdi.toNat ∧ g.rdi.toNat ≤ 26
def M1537 (g : Gprs) : Nat := 30 + 2 * g.rdi.toNat

/-- The invariant: the entry, or `Cm` and one cut point's condition and measure. -/
def Inv (K : Ctx) (ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = 6300 ∧ g = K.g0 ∧ V = K.V0) ∨ (Cm K g ∧ (
    (ℓ = 103 ∧ V = K.V1 ∧ I103 K g ∧ m = M103 g) ∨
    (ℓ = 180 ∧ V = K.V1 ∧ I180 K g ∧ m = M180 g) ∨
    (ℓ = 210 ∧ V = K.V1 ∧ I210 K g ∧ m = M210 g) ∨
    (ℓ = 248 ∧ V = K.V1 ∧ I248 K g ∧ m = M248 g) ∨
    (ℓ = 288 ∧ V = K.V1 ∧ I288 K g ∧ m = M288 g) ∨
    (ℓ = 314 ∧ V = K.V1 ∧ I314 K g ∧ m = M314 g) ∨
    (ℓ = 320 ∧ V = K.V1 ∧ I320 K g ∧ m = M320 g) ∨
    (ℓ = 340 ∧ V = K.V1 ∧ I340 K g ∧ m = M340 g) ∨
    (ℓ = 343 ∧ I343 K g V ∧ m = M343 g) ∨
    (ℓ = 411 ∧ V = K.V1 ∧ I411 K g ∧ m = M411 g) ∨
    (ℓ = 443 ∧ V = K.V1 ∧ I443 K g ∧ m = M443 g) ∨
    (ℓ = 481 ∧ V = K.V1 ∧ I481 K g ∧ m = M481 g) ∨
    (ℓ = 510 ∧ V = K.V1 ∧ I510 K g ∧ m = M510 g) ∨
    (ℓ = 532 ∧ V = K.V1 ∧ I532 K g ∧ m = M532 g) ∨
    (ℓ = 572 ∧ V = K.V1 ∧ I572 K g ∧ m = M572 g) ∨
    (ℓ = 594 ∧ V = K.V1 ∧ I594 K g ∧ m = M594 g) ∨
    (ℓ = 648 ∧ V = K.V1 ∧ I648 K g ∧ m = M648 g) ∨
    (ℓ = 657 ∧ V = K.V1 ∧ I657 K g ∧ m = M657 g) ∨
    (ℓ = 696 ∧ V = K.V1 ∧ I696 K g ∧ m = M696 g) ∨
    (ℓ = 751 ∧ V = K.V1 ∧ I751 K g ∧ m = M751 g) ∨
    (ℓ = 794 ∧ V = K.V1 ∧ I794 K g ∧ m = M794 g) ∨
    (ℓ = 821 ∧ V = K.V1 ∧ I821 K g ∧ m = M821 g) ∨
    (ℓ = 833 ∧ V = K.V1 ∧ I833 K g ∧ m = M833 g) ∨
    (ℓ = 880 ∧ V = K.V1 ∧ I880 K g ∧ m = M880 g) ∨
    (ℓ = 960 ∧ V = K.V1 ∧ I960 K g ∧ m = M960 g) ∨
    (ℓ = 1024 ∧ V = K.V1 ∧ I1024 K g ∧ m = M1024 g) ∨
    (ℓ = 1105 ∧ V = K.V1 ∧ I1105 K g ∧ m = M1105 g) ∨
    (ℓ = 1200 ∧ V = K.V1 ∧ I1200 K g ∧ m = M1200 g) ∨
    (ℓ = 1261 ∧ V = K.V1 ∧ I1261 K g ∧ m = M1261 g) ∨
    (ℓ = 1288 ∧ V = K.V1 ∧ I1288 K g ∧ m = M1288 g) ∨
    (ℓ = 1400 ∧ V = K.V1 ∧ I1400 K g ∧ m = M1400 g) ∨
    (ℓ = 1420 ∧ V = K.V1 ∧ I1420 K g ∧ m = M1420 g) ∨
    (ℓ = 1432 ∧ V = K.V1 ∧ I1432 K g ∧ m = M1432 g) ∨
    (ℓ = 1472 ∧ V = K.V1 ∧ I1472 K g ∧ m = M1472 g) ∨
    (ℓ = 1504 ∧ V = K.V1 ∧ I1504 K g ∧ m = M1504 g) ∨
    (ℓ = 1537 ∧ V = K.V1 ∧ I1537 K g ∧ m = M1537 g)))

/-- At the `ret`s. -/
def Fz (K : Ctx) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop := (j = 354 ∨ j = 765) ∧ FinR K g V
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (K : Ctx) (m : Nat) : Post := fun j g _ V => (∃ m' < m, Inv K j m' g V) ∨ Fz K j g V

/-! ## The exits -/

variable {m : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}

theorem x103 (hc : Cm K g) (hV : V = K.V1) (hI : I103 K g) (hm : M103 g < m) : Nx K m 103 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x180 (hc : Cm K g) (hV : V = K.V1) (hI : I180 K g) (hm : M180 g < m) : Nx K m 180 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 1 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x210 (hc : Cm K g) (hV : V = K.V1) (hI : I210 K g) (hm : M210 g < m) : Nx K m 210 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 2 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x248 (hc : Cm K g) (hV : V = K.V1) (hI : I248 K g) (hm : M248 g < m) : Nx K m 248 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 3 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x288 (hc : Cm K g) (hV : V = K.V1) (hI : I288 K g) (hm : M288 g < m) : Nx K m 288 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 4 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x314 (hc : Cm K g) (hV : V = K.V1) (hI : I314 K g) (hm : M314 g < m) : Nx K m 314 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 5 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x320 (hc : Cm K g) (hV : V = K.V1) (hI : I320 K g) (hm : M320 g < m) : Nx K m 320 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 6 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x340 (hc : Cm K g) (hV : V = K.V1) (hI : I340 K g) (hm : M340 g < m) : Nx K m 340 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 7 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x343 (hc : Cm K g) (hI : I343 K g V) (hm : M343 g < m) : Nx K m 343 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 8 right
  exact Or.inl ⟨rfl, hI, rfl⟩

theorem x411 (hc : Cm K g) (hV : V = K.V1) (hI : I411 K g) (hm : M411 g < m) : Nx K m 411 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 9 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x443 (hc : Cm K g) (hV : V = K.V1) (hI : I443 K g) (hm : M443 g < m) : Nx K m 443 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 10 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x481 (hc : Cm K g) (hV : V = K.V1) (hI : I481 K g) (hm : M481 g < m) : Nx K m 481 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 11 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x510 (hc : Cm K g) (hV : V = K.V1) (hI : I510 K g) (hm : M510 g < m) : Nx K m 510 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 12 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x532 (hc : Cm K g) (hV : V = K.V1) (hI : I532 K g) (hm : M532 g < m) : Nx K m 532 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 13 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x572 (hc : Cm K g) (hV : V = K.V1) (hI : I572 K g) (hm : M572 g < m) : Nx K m 572 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 14 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x594 (hc : Cm K g) (hV : V = K.V1) (hI : I594 K g) (hm : M594 g < m) : Nx K m 594 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 15 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x648 (hc : Cm K g) (hV : V = K.V1) (hI : I648 K g) (hm : M648 g < m) : Nx K m 648 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 16 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x657 (hc : Cm K g) (hV : V = K.V1) (hI : I657 K g) (hm : M657 g < m) : Nx K m 657 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 17 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x696 (hc : Cm K g) (hV : V = K.V1) (hI : I696 K g) (hm : M696 g < m) : Nx K m 696 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 18 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x751 (hc : Cm K g) (hV : V = K.V1) (hI : I751 K g) (hm : M751 g < m) : Nx K m 751 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 19 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x794 (hc : Cm K g) (hV : V = K.V1) (hI : I794 K g) (hm : M794 g < m) : Nx K m 794 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 20 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x821 (hc : Cm K g) (hV : V = K.V1) (hI : I821 K g) (hm : M821 g < m) : Nx K m 821 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 21 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x833 (hc : Cm K g) (hV : V = K.V1) (hI : I833 K g) (hm : M833 g < m) : Nx K m 833 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 22 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x880 (hc : Cm K g) (hV : V = K.V1) (hI : I880 K g) (hm : M880 g < m) : Nx K m 880 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 23 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x960 (hc : Cm K g) (hV : V = K.V1) (hI : I960 K g) (hm : M960 g < m) : Nx K m 960 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 24 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1024 (hc : Cm K g) (hV : V = K.V1) (hI : I1024 K g) (hm : M1024 g < m) : Nx K m 1024 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 25 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1105 (hc : Cm K g) (hV : V = K.V1) (hI : I1105 K g) (hm : M1105 g < m) : Nx K m 1105 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 26 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1200 (hc : Cm K g) (hV : V = K.V1) (hI : I1200 K g) (hm : M1200 g < m) : Nx K m 1200 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 27 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1261 (hc : Cm K g) (hV : V = K.V1) (hI : I1261 K g) (hm : M1261 g < m) : Nx K m 1261 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 28 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1288 (hc : Cm K g) (hV : V = K.V1) (hI : I1288 K g) (hm : M1288 g < m) : Nx K m 1288 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 29 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1400 (hc : Cm K g) (hV : V = K.V1) (hI : I1400 K g) (hm : M1400 g < m) : Nx K m 1400 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 30 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1420 (hc : Cm K g) (hV : V = K.V1) (hI : I1420 K g) (hm : M1420 g < m) : Nx K m 1420 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 31 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1432 (hc : Cm K g) (hV : V = K.V1) (hI : I1432 K g) (hm : M1432 g < m) : Nx K m 1432 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 32 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1472 (hc : Cm K g) (hV : V = K.V1) (hI : I1472 K g) (hm : M1472 g < m) : Nx K m 1472 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 33 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1504 (hc : Cm K g) (hV : V = K.V1) (hI : I1504 K g) (hm : M1504 g < m) : Nx K m 1504 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 34 right
  exact Or.inl ⟨rfl, hV, hI, rfl⟩

theorem x1537 (hc : Cm K g) (hV : V = K.V1) (hI : I1537 K g) (hm : M1537 g < m) : Nx K m 1537 g f V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩
  iterate 35 right
  exact ⟨rfl, hV, hI, rfl⟩

theorem xFin {j : Nat} (hj : j = 354 ∨ j = 765) (h : FinR K g V) : Nx K m j g f V := Or.inr ⟨hj, h⟩

end FV7z.Tdm
