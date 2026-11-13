import FV7z.Im2.HeadN
import FV7z.Tun.Inv
/-!
# `_int_malloc`: its frame on the second call (PLAN.md G3, `malloc`)

What the code after offset 2549 needs of the bytes there, whatever way the size took (fastbin, smallbin, largebin):
`Fr S g V W`, `S` the stack pointer after the pushes, `g` the registers at the entry, `V` the bytes at the entry,
`W` the bytes at 2549:

- `Fr.out`: the bytes outside `[S + 8, S + 184)` are those of `V`;
- `Fr.bx` … `Fr.r15`: the six registers pushed at `S + 136` … `S + 176` read back.

- `Vsv`: the six pushes; `Fr.base`: `Fr` of them.
- `Fr.vst`: a store of `k` bytes at `S + d`, `8 ≤ d`, `d + k ≤ 136`, keeps `Fr` (one `refine` per store, the bounds
  by `decide`; `Fr.base` only at the end: an `exact` of it against a longer chain unfolds the stores).
- `Fr.v2n`: `Fr` of `V2n` (the fastbin and smallbin sizes).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (Vst_out)
open FV7z.Imm (rd_off rd_off_self add_n)
namespace FV7z.Im2

/-- The frame of `_int_malloc` at 2549: outside `[S + 8, S + 184)` the bytes `V` of the entry, the six registers of
`g` pushed at `S + 136` … `S + 176`. -/
structure Fr (S : Addr) (g : Gprs) (V W : Addr → Byte) : Prop where
  out : ∀ a : Addr, a.toNat < S.toNat + 8 ∨ S.toNat + 184 ≤ a.toNat → W a = V a
  bx : rdq(W, S + 136#64) = g.rbx
  bp : rdq(W, S + 144#64) = g.rbp
  r12 : rdq(W, S + 152#64) = g.r12
  r13 : rdq(W, S + 160#64) = g.r13
  r14 : rdq(W, S + 168#64) = g.r14
  r15 : rdq(W, S + 176#64) = g.r15

/-- The six pushes of the entry. -/
abbrev Vsv (S : Addr) (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (S + 176#64) (toBytesLE g.r15 8)) (S + 168#64) (toBytesLE g.r14 8))
    (S + 160#64) (toBytesLE g.r13 8)) (S + 152#64) (toBytesLE g.r12 8)) (S + 144#64) (toBytesLE g.rbp 8))
    (S + 136#64) (toBytesLE g.rbx 8)

/-- A store at `S + d` leaves the bytes outside `[S + d, S + d + k)`. -/
theorem vst_off {S : Addr} {m d k : Nat} (x : BitVec m) (W : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (hd : d + k ≤ 256) {a : Addr} (ha : a.toNat < S.toNat + d ∨ S.toNat + d + k ≤ a.toNat) :
    Vst W (S + BitVec.ofNat 64 d) (toBytesLE x k) a = W a :=
  Vst_out _ _ _ _ (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)
    (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)

/-- The eight bytes at `S + d1` after a store at `S + d` below them. -/
theorem rd_vst {S : Addr} {m d k d1 : Nat} (x : BitVec m) (W : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (hd : d + k ≤ d1) (h1 : d1 + 8 ≤ 256) :
    rdq(Vst W (S + BitVec.ofNat 64 d) (toBytesLE x k), S + BitVec.ofNat 64 d1) = rdq(W, S + BitVec.ofNat 64 d1) :=
  congrArg (ofBytesLE 64) (rd_off W hS h1 (by rw [toBytesLE_length]; omega) (.inr (by rw [toBytesLE_length]; omega)))

/-- A store in `[S + 8, S + 136)` keeps the frame. -/
theorem Fr.vst {S : Addr} {g : Gprs} {V W : Addr → Byte} {m d k : Nat} (x : BitVec m) (hS : S.toNat + 256 < 2 ^ 64)
    (h : Fr S g V W) (hd : 8 ≤ d) (hk : d + k ≤ 136) :
    Fr S g V (Vst W (S + BitVec.ofNat 64 d) (toBytesLE x k)) where
  out a ha := (vst_off (a := a) x W hS (by omega) (by omega)).trans (h.out a ha)
  bx := (rd_vst (d1 := 136) x W hS hk (by omega)).trans h.bx
  bp := (rd_vst (d1 := 144) x W hS (by omega) (by omega)).trans h.bp
  r12 := (rd_vst (d1 := 152) x W hS (by omega) (by omega)).trans h.r12
  r13 := (rd_vst (d1 := 160) x W hS (by omega) (by omega)).trans h.r13
  r14 := (rd_vst (d1 := 168) x W hS (by omega) (by omega)).trans h.r14
  r15 := (rd_vst (d1 := 176) x W hS (by omega) (by omega)).trans h.r15

/-- The six pushes: the frame. -/
theorem Fr.base {S : Addr} (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) : Fr S g V (Vsv S g V) where
  out a ha := by
    unfold Vsv
    rw [vst_off (a := a) (d := 136) (k := 8) _ _ hS (by omega) (by omega),
      vst_off (a := a) (d := 144) (k := 8) _ _ hS (by omega) (by omega),
      vst_off (a := a) (d := 152) (k := 8) _ _ hS (by omega) (by omega),
      vst_off (a := a) (d := 160) (k := 8) _ _ hS (by omega) (by omega),
      vst_off (a := a) (d := 168) (k := 8) _ _ hS (by omega) (by omega),
      vst_off (a := a) (d := 176) (k := 8) _ _ hS (by omega) (by omega)]
  bx := by
    simp only [Vsv, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd, Nat.reduceLeDiff]
  bp := by
    simp only [Vsv, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
      Nat.reduceLeDiff]
  r12 := by
    simp only [Vsv, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
      Nat.reduceLeDiff, or_true]
  r13 := by
    simp only [Vsv, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
      Nat.reduceLeDiff, or_true]
  r14 := by
    simp only [Vsv, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
      Nat.reduceLeDiff, or_true]
  r15 := by
    simp only [Vsv, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
      Nat.reduceLeDiff, or_true]

/-- `Fr` of `V2n`: the bytes of the fastbin and smallbin sizes at 2549. -/
theorem Fr.v2n (S : Addr) (g : Gprs) (n nb : Addr) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    Fr S g V (V2n S g n nb V) := by
  have b := Fr.base g V hS
  unfold V2n V1n
  repeat (first
    | refine Fr.vst _ hS ?_ (by decide) (by decide)
    | exact b)

end FV7z.Im2
