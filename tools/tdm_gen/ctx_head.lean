import Lean
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

/-- `decide p = true` as `p`, for any instance (the jumps' `decide`s need not carry `instDecidableLtNat`). -/
theorem dec_true {p : Prop} {i : Decidable p} : (@decide p i = true) = p := by cases i <;> simp_all
/-- `decide p = false` as `¬ p`, for any instance. -/
theorem dec_false {p : Prop} {i : Decidable p} : (@decide p i = false) = ¬ p := by cases i <;> simp_all
/-- `(!decide p) = false` as `p`, for any instance. -/
theorem nd_false {p : Prop} {i : Decidable p} : ((!@decide p i) = false) = p := by cases i <;> simp_all
/-- `(!decide p) = true` as `¬ p`, for any instance. -/
theorem nd_true {p : Prop} {i : Decidable p} : ((!@decide p i) = true) = ¬ p := by cases i <;> simp_all

/-! ## Tactics -/

open Lean Elab Tactic Meta in
/-- A jump's condition `h` as a fact: `(!decide p) = false`, `decide p = true` and the like as `p` or `¬ p`, by `cast`
(`simp at *` leaves some of them, kt2301; `simp at h` with its simprocs hits maxRecDepth at 648, kt2303). -/
scoped elab "dcd " h:ident : tactic => withMainContext do
  -- Only on a syntactic match, and by `MVarId.replace` with a built term: no unification, no elaboration
  -- (elaborating `cast nd_false h` against other hypotheses hit maxRecDepth at 648, kt2304).
  let d ← getLocalDeclFromUserName h.getId
  let t ← instantiateMVars d.type
  let some (_, l, r) := t.consumeMData.eq? | return
  let (neg, e) := if l.isAppOfArity `Bool.not 1 then (true, l.appArg!) else (false, l)
  unless e.isAppOfArity `Decidable.decide 2 do return
  let p := e.appFn!.appArg!
  let i := e.appArg!
  let some (lem, ty) := (if r.isConstOf `Bool.true then
      some (if neg then (``nd_true, mkNot p) else (``dec_true, p))
    else if r.isConstOf `Bool.false then
      some (if neg then (``nd_false, p) else (``dec_false, mkNot p))
    else none) | return
  let v := mkApp4 (mkConst ``cast [levelZero]) t ty (mkApp2 (mkConst lem) p i) (mkFVar d.fvarId)
  let res ← (← getMainGoal).replace d.fvarId v (some ty)
  replaceMainGoal [res.mvarId]
open Lean Elab Tactic Meta in
/-- Closed `BitVec.toNat` terms in the goal as numerals, by `whnf` and `change` (for
`(BitVec.setWidth 64 4#32).toNat` from a 32-bit `mov` of an immediate, kt2305). `simp` then leaves `True`s inside
`∨`/`∧` that `omega` does not take (kt2307), hence `true_and` and the like in `tfo`. -/
scoped elab "lits" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    if e.isAppOfArity ``BitVec.toNat 2 && !e.hasFVar && !e.hasMVar then
      let v ← whnf e
      if let some n := v.rawNatLit? <|> v.nat? then return .done (mkNatLit n)
    return .continue)
  if t' == t then throwError "lits: no closed `BitVec.toNat` in the goal"
  replaceMainGoal [← g.change t']
/-- The jumps' conditions as facts, then `bv_omega`. -/
scoped macro "tfo" : tactic => `(tactic| (((try lits) <;>
  (try simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, Bool.and_eq_true,
  decide_eq_true_eq, decide_eq_false_iff_not, dec_true, dec_false, beq_iff_eq, beq_eq_false_iff_ne, Bnd, ne_eq,
    true_and, and_true, true_or, or_true] at *)) <;>
  bv_omega))
/-- Triage only: `tfo` that shows the goal after the jumps' conditions. -/
scoped macro "tfod" : tactic => `(tactic| (((try lits) <;>
  (try simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, Bool.and_eq_true,
  decide_eq_true_eq, decide_eq_false_iff_not, dec_true, dec_false, beq_iff_eq, beq_eq_false_iff_ne, Bnd, ne_eq,
    true_and, and_true, true_or, or_true] at *)) <;>
  (trace_state; bv_omega)))
/-- `tfo` with the wraps that `omega` proves away dropped first (`omega` alone gives up on many of them). -/
scoped macro "tfom" : tactic => `(tactic| (((try lits) <;>
  (try simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, Bool.and_eq_true,
  decide_eq_true_eq, decide_eq_false_iff_not, dec_true, dec_false, beq_iff_eq, beq_eq_false_iff_ne, Bnd, ne_eq,
    true_and, and_true, true_or, or_true] at *)) <;>
  (try simp -implicitDefEqProofs only [bitvec_to_nat] at *) <;>
  (try simp (disch := omega) only [Nat.mod_eq_of_lt] at *) <;> omega))
/-- A cut point's condition: its conjuncts by `assumption`, `rfl` or `tfo`. -/
scoped macro "tf1" : tactic => `(tactic| first | (with_reducible assumption) | exact trivial | (with_reducible rfl) |
  (with_reducible apply And.intro))
scoped macro "tfs" : tactic => `(tactic| ((repeat' tf1) <;> tfo))
scoped macro "tfsm" : tactic => `(tactic| ((repeat' tf1) <;> tfom))
scoped macro "tfsd" : tactic => `(tactic| ((repeat' tf1) <;> (trace_state; tfod)))
/-- `Cm` after a stretch. -/
scoped macro "tcm" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, by tfo, by tfo⟩)
scoped macro "tcmm" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, by tfom, by tfom⟩)
scoped macro "tcmd" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, by tfod, by tfod⟩)
/-- `I343` after a stretch: no store and `r12d` 0 (`t343a`), or the store and the result (`t343b`). -/
scoped macro "t343a" : tactic => `(tactic| exact Or.inl ⟨by tfo, rfl⟩)
scoped macro "t343b" : tactic => `(tactic| exact Or.inr ⟨⟨by tfo, by tfo⟩, rfl⟩)
/-- `FinR.v` at a `ret`, for each case of `I343`. -/
scoped macro "tfva" : tactic => `(tactic| exact Or.inl ⟨by tfo, rfl⟩)
scoped macro "tfvb" : tactic => `(tactic| exact Or.inr ⟨by tfo, by tfo, rfl⟩)

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

/-- `ctx_ok` with `cx` unfolded, as the stretch from 103 leaves `rbx`. -/
theorem ctx_ok' {K : Ctx} (hK : Ok K) (r : BitVec 64) :
    CtxOk K (BitVec.setWidth 64 ((BitVec.setWidth 32 r &&& ~~~(4294967295#32 <<< ((BitVec.setWidth 8
      (BitVec.setWidth 32 (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.g0.rdi + 1#64) 1))))).toNat % 32))) <<<
      ((BitVec.setWidth 8 (BitVec.setWidth 32 (ofBytesLE 8 (List.map K.V1 (byteAddrs K.g0.rdi 1))))).toNat % 32)))
      (BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 (List.map K.V1 (byteAddrs K.g0.rdi 1))))) := by
  have h := ctx_ok hK r
  unfold cx at h
  exact h

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
