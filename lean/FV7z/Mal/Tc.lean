import FV7z.Mal.Heap
/-!
# The heap with chunks in the tcache (PLAN.md G3, `malloc`, `free`)

`Gl` asks for the tcache's 64 counts to be 0: true up to the first `free`, false after it. Here `Gl` is split in two:

- `GlB F Wl fb C V`: all of `Gl` but the counts.
- `TcSt V C bins`: the tcache's bins (`bins i`, the entries' addresses, the `mem` pointers `p + 16` of the chunks):
  the count `i` (`C + 2 i`, 16 bits) is the length of bin `i`, the entry `i` (`C + 128 + 8 i`) its head when it is not
  empty, and the `next` word of each entry (its first word) the one after it. The `next` of the last entry and the
  head of an empty bin are not asked for: glibc 2.31 reads neither (the count first).
- `Gl.split`, `Gl.of_split`: `Gl` is `GlB ∧ TcSt … (fun _ => [])`.
- `bput bins i e`: bin `i` with `e` in front, the others as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mal

/-- `Gl` but the tcache's counts. -/
structure GlB (F : Footprint) (Wl : List Rgn) (fb C : Addr) (V : Addr → Byte) : Prop where
  hk : rdq(V, 7940656#64) = 0#64
  tc : rdq(V, fb + 18446744073709551576#64) = C
  t1 : rdd(V, fb + 24#64) = 0#32
  gm : rdq(V, 8013224#64) = 128#64
  fc : rdd(V, 7940680#64) = 0
  fz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64
  bk : ∀ i, 2 ≤ i → i ≤ 63 →
    rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i)
  lb : ∀ i, 64 ≤ i → i ≤ 126 →
    rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i)
  tb : rdq(V, 7940592#64) = 64#64
  un : rdq(V, 7940792#64) = 7940768#64
  m0 : rdd(V, 7942816#64) = 0
  m1 : rdd(V, 7942820#64) = 0
  m2 : rdd(V, 7942824#64) = 0
  m3 : rdd(V, 7942828#64) = 0
  p0 : rdd(V, 8013220#64) = 0
  fh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)
  fn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)
  f1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)
  W : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a
  gf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i)
  tf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)
  pb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)

/-- The count of bin `i` of the tcache `C`. -/
abbrev tcnt (V : Addr → Byte) (C : Addr) (i : Nat) : BitVec 16 :=
  ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V)

/-- The entry (head) of bin `i` of the tcache `C`. -/
abbrev tent (V : Addr → Byte) (C : Addr) (i : Nat) : Addr :=
  rdq(V, C + BitVec.ofNat 64 (128 + 8 * i))

/-- The tcache's bins: each count the length of its bin, each entry its head, each entry's `next` the one after. -/
def TcSt (V : Addr → Byte) (C : Addr) (bins : Nat → List Addr) : Prop :=
  ∀ i < 64, tcnt V C i = BitVec.ofNat 16 (bins i).length ∧
    (∀ e, (bins i).head? = some e → tent V C i = e) ∧
    ∀ k (h : k + 1 < (bins i).length), rdq(V, (bins i)[k]) = (bins i)[k + 1]

/-- Bin `i` with `e` in front. -/
def bput (bins : Nat → List Addr) (i : Nat) (e : Addr) : Nat → List Addr :=
  fun j => if j = i then e :: bins i else bins j

theorem Gl.split {F : Footprint} {Wl : List Rgn} {fb C : Addr} {V : Addr → Byte} (h : Gl F Wl fb C V) :
    GlB F Wl fb C V ∧ TcSt V C (fun _ => []) :=
  ⟨{ hk := h.hk, tc := h.tc, t1 := h.t1, gm := h.gm, fc := h.fc, fz := h.fz, bk := h.bk, lb := h.lb, tb := h.tb,
     un := h.un, m0 := h.m0, m1 := h.m1, m2 := h.m2, m3 := h.m3, p0 := h.p0, fh := h.fh, fn := h.fn, f1 := h.f1,
     W := h.W, gf := h.gf, tf := h.tf, pb := h.pb },
   fun i hi => ⟨h.cn i hi, fun _ he => by simp at he, fun _ hk => by simp at hk⟩⟩

theorem Gl.of_split {F : Footprint} {Wl : List Rgn} {fb C : Addr} {V : Addr → Byte} (h : GlB F Wl fb C V)
    (ht : TcSt V C (fun _ => [])) : Gl F Wl fb C V :=
  { hk := h.hk, tc := h.tc, cn := fun i hi => (ht i hi).1, t1 := h.t1, gm := h.gm, fc := h.fc, fz := h.fz,
    bk := h.bk, lb := h.lb, tb := h.tb, un := h.un, m0 := h.m0, m1 := h.m1, m2 := h.m2, m3 := h.m3, p0 := h.p0,
    fh := h.fh, fn := h.fn, f1 := h.f1, W := h.W, gf := h.gf, tf := h.tf, pb := h.pb }

theorem gl_iff {F : Footprint} {Wl : List Rgn} {fb C : Addr} {V : Addr → Byte} :
    Gl F Wl fb C V ↔ GlB F Wl fb C V ∧ TcSt V C (fun _ => []) :=
  ⟨Gl.split, fun ⟨h, ht⟩ => Gl.of_split h ht⟩

end FV7z.Mal
