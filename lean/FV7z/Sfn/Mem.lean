import FV7z.Sfn.Cuts
import FV7z.Ocv.Holds
import FV7z.Lemmas.SpCallK
import FV7z.Lemmas.Rmw8
/-!
# `SortFileNames`: the frame, the index buffer and the comparator (PLAN.md §M, M1)

7-Zip 26.06's `SortFileNames (strings, indices)` at `0x5dca70` in `7zzs` (`CPP/7zip/UI/Common/SortUtils.cpp`)
sorts the `n` = `strings.Size ()` entries of `indices` (the buffer at `p`) by heap sort, comparing two entries
through the comparator at `0x5dca50`, which looks up `strings` at the two indices. `R` is the stack pointer after
the prologue (`S - 120`, `S` the one at the entry): spills at `R + 8`, `R + 16`, `R + 24`, `R + 32` (the heap build's
counter `2 i + 1`), `R + 40` (`&temp`), the 4 bytes of `temp` at `R + 52`, the stack guard at `R + 56`, the saved
registers from `R + 72`, the return address at `R + 120`.

- `bq p x`: the address of the `x`-th entry; `Lay`: the frame and the buffer fit and are apart (the buffer also
  apart from the comparator's return address slot, `R - 8`);
- `Pr`: the bytes the function and the comparator keep track of (from `R - 8` to `R + 128`, and the buffer);
  `SameP`: bytes equal there; `Bb`: every entry below `n`; `Tp`: the bytes from `R + 56` (the stack guard, the saved
  registers, the return address) as after the prologue;
- `Ix`: a pointer the comparator is given (`temp` or an entry) and the index there below `n`;
- `Tc`, `Rc`: what the comparator needs and leaves (`Kp`, `rsp`, `SameP`, the caller's `I`);
- `Mk`: what holds of the bytes at the sort's cut points (`I`, `Bb`, `Tp`, `&temp` at `R + 40`), kept by the stores
  into the spills (`Mk.st_S`) and into the buffer (`Mk.st_B`) and by the comparator (`Mk.call`);
- `Env`: the run's hypotheses for the sort's loops; `AtJ`: the run goes on from an offset.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ocv (Kp)
namespace FV7z.Sfn

/-! ## The frame and the buffer -/

/-- The address of the `x`-th entry of the buffer at `p`. -/
abbrev bq (p x : BitVec 64) : Addr := p + x * 4#64

/-- The frame from `R - 8` to `R + 128` and the `4 n` bytes of the buffer fit, and are apart. -/
structure Lay (R p : Addr) (n : Nat) : Prop where
  hn : n < 4294967296
  hR8 : 8 ≤ R.toNat
  hR : R.toNat + 128 < 18446744073709551616
  hp : p.toNat + 4 * n ≤ 18446744073709551616
  hD : p.toNat + 4 * n + 8 ≤ R.toNat ∨ R.toNat + 128 ≤ p.toNat

/-- The bytes kept track of: from `R - 8` to `R + 128`, and the buffer. -/
def Pr (R p : Addr) (n : Nat) (a : Addr) : Prop :=
  (R.toNat ≤ a.toNat + 8 ∧ a.toNat < R.toNat + 128) ∨ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4 * n)

/-- `W'` as `W` on the bytes kept track of. -/
def SameP (R p : Addr) (n : Nat) (W W' : Addr → Byte) : Prop := ∀ a, Pr R p n a → W' a = W a

/-- Every entry below `n`. -/
def Bb (p : Addr) (n : Nat) (W : Addr → Byte) : Prop :=
  ∀ x : BitVec 64, x.toNat < n → (rdd(W, bq p x)).toNat < n

/-- The bytes from `R + 56` to `R + 128` as in `W0`. -/
def Tp (R : Addr) (W0 W : Addr → Byte) : Prop :=
  ∀ a : Addr, R.toNat + 56 ≤ a.toNat → a.toNat < R.toNat + 128 → W a = W0 a

/-- A pointer given to the comparator: `temp` or an entry, the index there below `n`. -/
def Ix (R p : Addr) (n : Nat) (W : Addr → Byte) (a : Addr) : Prop :=
  (rdd(W, a)).toNat < n ∧ (a = R + 52#64 ∨ ∃ x : BitVec 64, x.toNat < n ∧ a = bq p x)

/-- What the comparator needs: the return address at `rsp` = `R - 8`, `rdx` = `strings`, the caller's `I`, two
pointers as `Ix`. -/
def Tc (R p : Addr) (n : Nat) (sv : Addr) (I : (Addr → Byte) → Prop) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = R - 8 ∧ g.rdx = sv ∧ I V ∧ Ix R p n V g.rdi ∧ Ix R p n V g.rsi

/-- What the comparator leaves: the registers a call keeps, `rsp` past the return address, the bytes kept track of,
the caller's `I`. -/
def Rc (R p : Addr) (n : Nat) (I : (Addr → Byte) → Prop) (g : Gprs) (V : Addr → Byte) (g' : Gprs)
    (V' : Addr → Byte) : Prop :=
  Kp g g' ∧ g'.rsp = g.rsp + 8 ∧ SameP R p n V V' ∧ I V'

/-- The bytes at the sort's cut points. -/
structure Mk (R p : Addr) (n : Nat) (I : (Addr → Byte) → Prop) (W0 W : Addr → Byte) : Prop where
  i : I W
  b : Bb p n W
  t : Tp R W0 W
  q40 : rdq(W, R + 40#64) = R + 52#64

/-! ## Addresses -/

theorem tR {R : Addr} {d : Nat} (h : R.toNat + d < 18446744073709551616) :
    (R + BitVec.ofNat 64 d).toNat = R.toNat + d := by
  have hd : d < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (b := 2 ^ 64) hd]
  exact Nat.mod_eq_of_lt h

theorem t4 {x : BitVec 64} (hx : x.toNat < 4294967296) : (x * 4#64).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have e : 4 % 2 ^ 64 = 4 := rfl
  rw [e, Nat.mul_comm]
  exact Nat.mod_eq_of_lt (by omega)

theorem tB {p x : BitVec 64} {n : Nat} (hn : n < 4294967296) (hp : p.toNat + 4 * n ≤ 18446744073709551616)
    (hx : x.toNat < n) : (bq p x).toNat = p.toNat + 4 * x.toNat := by
  show (p + x * 4#64).toNat = _
  rw [BitVec.toNat_add, t4 (x := x) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem tS8 {R : Addr} (h : 8 ≤ R.toNat) : (R - 8).toNat = R.toNat - 8 := by
  have hl : R.toNat < 18446744073709551616 := R.isLt
  rw [BitVec.toNat_sub]
  show (18446744073709551616 - 8 + R.toNat) % 18446744073709551616 = R.toNat - 8
  omega

section
variable {R p : Addr} {n : Nat}

theorem Lay.tR (hL : Lay R p n) {d : Nat} (h : d ≤ 128) : (R + BitVec.ofNat 64 d).toNat = R.toNat + d :=
  FV7z.Sfn.tR (by have := hL.hR; omega)

theorem Lay.tB (hL : Lay R p n) {x : BitVec 64} (hx : x.toNat < n) : (bq p x).toNat = p.toNat + 4 * x.toNat :=
  FV7z.Sfn.tB hL.hn hL.hp hx

theorem pr_R (hL : Lay R p n) {d i : Nat} (h : d + i < 128) : Pr R p n ((R + BitVec.ofNat 64 d).add i) := by
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have hR := hL.hR
  have e2 : ((R + BitVec.ofNat 64 d).add i).toNat = R.toNat + d + i := by
    have h1 : (R + BitVec.ofNat 64 d).toNat + (i + 1) ≤ 2 ^ 64 := by rw [e1]; omega
    rw [toNat_add_of_fits (show i < i + 1 by omega) h1, e1]
  unfold Pr
  left
  rw [e2]
  omega

theorem pr_B (hL : Lay R p n) {x : BitVec 64} (hx : x.toNat < n) {i : Nat} (hi : i < 4) :
    Pr R p n ((bq p x).add i) := by
  have e1 := hL.tB hx
  have hp := hL.hp
  have e2 : ((bq p x).add i).toNat = p.toNat + 4 * x.toNat + i := by
    have h1 : (bq p x).toNat + 4 ≤ 2 ^ 64 := by rw [e1]; omega
    rw [toNat_add_of_fits hi h1, e1]
  unfold Pr
  right
  rw [e2]
  omega

/-! ## Loads and stores -/

theorem SameP.rd {W W' : Addr → Byte} {a : Addr} {k : Nat} (hS : SameP R p n W W')
    (h : ∀ i < k, Pr R p n (a.add i)) : List.map W' (byteAddrs a k) = List.map W (byteAddrs a k) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact hS _ (h j hj)

/-- A load through a call: the return address stored at `R - 8`, then the bytes kept track of as they were. -/
theorem rd_call (hL : Lay R p n) {W W' : Addr → Byte} {bs : List Byte} (hb : bs.length = 8)
    (hS : SameP R p n (Vst W (R - 8) bs) W') {a : Addr} {k : Nat} (hk : a.toNat + k ≤ 18446744073709551616)
    (h1 : ∀ i < k, Pr R p n (a.add i)) (h2 : R.toNat ≤ a.toNat ∨ a.toNat + k + 8 ≤ R.toNat) :
    List.map W' (byteAddrs a k) = List.map W (byteAddrs a k) := by
  rw [hS.rd h1]
  have e := tS8 hL.hR8
  have hR := hL.hR
  have hR8 := hL.hR8
  exact Tun.rd_Vst W (R - 8) bs a k (by rw [hb, e]; omega) hk (by rw [hb, e]; omega)

theorem rdq_callR (hL : Lay R p n) {W W' : Addr → Byte} {bs : List Byte} (hb : bs.length = 8)
    (hS : SameP R p n (Vst W (R - 8) bs) W') {d : Nat} (hd : d + 8 ≤ 128) :
    rdq(W', R + BitVec.ofNat 64 d) = rdq(W, R + BitVec.ofNat 64 d) := by
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have hR := hL.hR
  exact congrArg (ofBytesLE 64) (rd_call hL hb hS (a := R + BitVec.ofNat 64 d) (k := 8) (by rw [e1]; omega)
    (fun i hi => pr_R hL (by omega)) (Or.inl (by rw [e1]; omega)))

theorem rdd_callR (hL : Lay R p n) {W W' : Addr → Byte} {bs : List Byte} (hb : bs.length = 8)
    (hS : SameP R p n (Vst W (R - 8) bs) W') {d : Nat} (hd : d + 4 ≤ 128) :
    rdd(W', R + BitVec.ofNat 64 d) = rdd(W, R + BitVec.ofNat 64 d) := by
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have hR := hL.hR
  exact congrArg (ofBytesLE 32) (rd_call hL hb hS (a := R + BitVec.ofNat 64 d) (k := 4) (by rw [e1]; omega)
    (fun i hi => pr_R hL (by omega))
    (Or.inl (by rw [e1]; omega)))

theorem rdd_callB (hL : Lay R p n) {W W' : Addr → Byte} {bs : List Byte} (hb : bs.length = 8)
    (hS : SameP R p n (Vst W (R - 8) bs) W') {x : BitVec 64} (hx : x.toNat < n) :
    rdd(W', bq p x) = rdd(W, bq p x) := by
  have e1 := hL.tB hx
  have hp := hL.hp
  have hD := hL.hD
  exact congrArg (ofBytesLE 32) (rd_call hL hb hS (a := bq p x) (k := 4) (by rw [e1]; omega)
    (fun i hi => pr_B hL hx hi)
    (by rw [e1]; omega))

/-- A load from the frame apart from a store into it. -/
theorem rd_SS (hL : Lay R p n) {W : Addr → Byte} {d e k : Nat} {bs : List Byte} (hd : d + bs.length ≤ 128)
    (he : e + k ≤ 128) (h : d + bs.length ≤ e ∨ e + k ≤ d) :
    List.map (Vst W (R + BitVec.ofNat 64 d) bs) (byteAddrs (R + BitVec.ofNat 64 e) k) =
      List.map W (byteAddrs (R + BitVec.ofNat 64 e) k) := by
  have hR := hL.hR
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have e2 : (R + BitVec.ofNat 64 e).toNat = R.toNat + e := hL.tR (by omega)
  exact Tun.rd_Vst W _ bs _ k (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1, e2]; omega)

/-- A load from the buffer apart from a store into the frame. -/
theorem rd_SB (hL : Lay R p n) {W : Addr → Byte} {d : Nat} {bs : List Byte} (hd : d + bs.length ≤ 128)
    {x : BitVec 64} (hx : x.toNat < n) :
    List.map (Vst W (R + BitVec.ofNat 64 d) bs) (byteAddrs (bq p x) 4) = List.map W (byteAddrs (bq p x) 4) := by
  have hR := hL.hR
  have hp := hL.hp
  have hD := hL.hD
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have e2 := hL.tB hx
  exact Tun.rd_Vst W _ bs _ 4 (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e1, e2]; omega)

/-- A load from the frame apart from a store into the buffer. -/
theorem rd_BS (hL : Lay R p n) {W : Addr → Byte} {y : BitVec 64} (hy : y.toNat < n) {bs : List Byte}
    (hb : bs.length = 4) {e k : Nat} (he : e + k ≤ 128) :
    List.map (Vst W (bq p y) bs) (byteAddrs (R + BitVec.ofNat 64 e) k) =
      List.map W (byteAddrs (R + BitVec.ofNat 64 e) k) := by
  have hR := hL.hR
  have hp := hL.hp
  have hD := hL.hD
  have e1 := hL.tB hy
  have e2 : (R + BitVec.ofNat 64 e).toNat = R.toNat + e := hL.tR (by omega)
  exact Tun.rd_Vst W _ bs _ k (by rw [e1, hb]; omega) (by rw [e2]; omega) (by rw [e1, e2, hb]; omega)

/-- A load from another entry than the one stored into. -/
theorem rd_BB (hL : Lay R p n) {W : Addr → Byte} {y : BitVec 64} (hy : y.toNat < n) {bs : List Byte}
    (hb : bs.length = 4) {x : BitVec 64} (hx : x.toNat < n) (hne : x ≠ y) :
    List.map (Vst W (bq p y) bs) (byteAddrs (bq p x) 4) = List.map W (byteAddrs (bq p x) 4) := by
  have hp := hL.hp
  have e1 := hL.tB hy
  have e2 := hL.tB hx
  have hne' : x.toNat ≠ y.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  exact Tun.rd_Vst W _ bs _ 4 (by rw [e1, hb]; omega) (by rw [e2]; omega) (by rw [e1, e2, hb]; omega)

theorem rdq_self {W : Addr → Byte} {a : Addr} (v : BitVec 64) (h : a.toNat + 8 ≤ 18446744073709551616) :
    rdq(Vst W a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self (n := 8) W a _ (toBytesLE_length _ _) h]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem rdd_self {W : Addr → Byte} {a : Addr} (v : BitVec 32) (h : a.toNat + 4 ≤ 18446744073709551616) :
    rdd(Vst W a (toBytesLE v 4), a) = v := by
  rw [Tun.rd_Vst_self (n := 4) W a _ (toBytesLE_length _ _) h]
  exact ofBytesLE_toBytesLE (n := 4) rfl _

theorem rdq_selfR (hL : Lay R p n) {W : Addr → Byte} {d : Nat} (hd : d + 8 ≤ 128) (v : BitVec 64) :
    rdq(Vst W (R + BitVec.ofNat 64 d) (toBytesLE v 8), R + BitVec.ofNat 64 d) = v := by
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have hR := hL.hR
  exact rdq_self v (by rw [e1]; omega)

theorem rdd_selfR (hL : Lay R p n) {W : Addr → Byte} {d : Nat} (hd : d + 4 ≤ 128) (v : BitVec 32) :
    rdd(Vst W (R + BitVec.ofNat 64 d) (toBytesLE v 4), R + BitVec.ofNat 64 d) = v := by
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  have hR := hL.hR
  exact rdd_self v (by rw [e1]; omega)

/-! ## `Mk` -/

variable {I : (Addr → Byte) → Prop} {W0 : Addr → Byte}

/-- A store into the spills from `R + 8` to `R + 56`, apart from `&temp` at `R + 40`. -/
theorem Mk.st_S (hL : Lay R p n) (hIw : ∀ W W', I W → (∀ a, ¬ Pr R p n a → W' a = W a) → I W')
    {W : Addr → Byte} (hM : Mk R p n I W0 W) {d : Nat} {bs : List Byte} (h8 : 8 ≤ d)
    (h56 : d + bs.length ≤ 56) (h40 : d + bs.length ≤ 40 ∨ 48 ≤ d) :
    Mk R p n I W0 (Vst W (R + BitVec.ofNat 64 d) bs) := by
  have hR := hL.hR
  have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := hL.tR (by omega)
  refine ⟨hIw _ _ hM.i fun a ha => ?_, fun x hx => ?_, fun a h1 h2 => ?_, ?_⟩
  · unfold Pr at ha
    exact Tun.Vst_out W (R + BitVec.ofNat 64 d) bs a (by rw [e1]; omega) (by rw [e1]; omega)
  · rw [rd_SB hL (d := d) (bs := bs) (by omega) hx]
    exact hM.b x hx
  · rw [Tun.Vst_out W (R + BitVec.ofNat 64 d) bs a (by rw [e1]; omega) (by rw [e1]; omega)]
    exact hM.t a h1 h2
  · rw [rd_SS hL (d := d) (e := 40) (k := 8) (bs := bs) (by omega) (by omega) (by omega)]
    exact hM.q40

/-- A store of an index below `n` into an entry. -/
theorem Mk.st_B (hL : Lay R p n) (hIw : ∀ W W', I W → (∀ a, ¬ Pr R p n a → W' a = W a) → I W')
    {W : Addr → Byte} (hM : Mk R p n I W0 W) {y : BitVec 64} (hy : y.toNat < n) {v : BitVec 32}
    (hv : v.toNat < n) : Mk R p n I W0 (Vst W (bq p y) (toBytesLE v 4)) := by
  have hR := hL.hR
  have hp := hL.hp
  have hD := hL.hD
  have e1 := hL.tB hy
  have hb : (toBytesLE v 4).length = 4 := toBytesLE_length _ _
  refine ⟨hIw _ _ hM.i fun a ha => ?_, fun x hx => ?_, fun a h1 h2 => ?_, ?_⟩
  · unfold Pr at ha
    exact Tun.Vst_out W (bq p y) _ a (by rw [e1, hb]; omega) (by rw [e1, hb]; omega)
  · by_cases hxy : x = y
    · rw [hxy, rdd_self (W := W) (a := bq p y) v (by rw [e1]; omega)]
      exact hv
    · rw [rd_BB hL hy hb hx hxy]
      exact hM.b x hx
  · rw [Tun.Vst_out W (bq p y) (toBytesLE v 4) a (by rw [e1, hb]; omega) (by rw [e1, hb]; omega)]
    exact hM.t a h1 h2
  · rw [rd_BS hL hy hb (e := 40) (k := 8) (by omega)]
    exact hM.q40

/-- Through a call: the return address stored at `R - 8`, then the bytes kept track of as they were, and `I`. -/
theorem Mk.call (hL : Lay R p n) {W W' : Addr → Byte} (hM : Mk R p n I W0 W) {bs : List Byte}
    (hb : bs.length = 8) (hS : SameP R p n (Vst W (R - 8) bs) W') (hI : I W') : Mk R p n I W0 W' := by
  have hR := hL.hR
  have hR8 := hL.hR8
  have e := tS8 hL.hR8
  refine ⟨hI, fun x hx => ?_, fun a h1 h2 => ?_, ?_⟩
  · rw [rdd_callB hL hb hS hx]
    exact hM.b x hx
  · have hP : Pr R p n a := by unfold Pr; exact Or.inl ⟨by omega, h2⟩
    rw [hS a hP, Tun.Vst_out W (R - 8) bs a (by rw [e, hb]; omega) (by rw [e, hb]; omega)]
    exact hM.t a h1 h2
  · rw [rdq_callR hL hb hS (d := 40) (by omega)]
    exact hM.q40

end

/-! ## The run -/

/-- From offset `j` of the function with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (V : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = sfn_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

/-- The run's hypotheses for the sort's loops: the code (the function's, the comparator's), the frame and the
buffer apart and the run's to store into, the caller's `I` kept by stores into the bytes kept track of, the
comparator as `Tc`, `Rc`. -/
structure Env (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (fb R p sv : Addr) (n : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L sfn_at sfn
  lay : Lay R p n
  wS : ∀ i < 128, Foot Wl (Addr.add (R - 8) i)
  wB : ∀ i < 4 * n, Foot Wl (Addr.add p i)
  hIw : ∀ W W', I W → (∀ a, ¬ Pr R p n a → W' a = W a) → I W'
  cc : ∃ codeC : List Byte, CodeIn L 0x5dca50#64 codeC ∧ 0 < codeC.length
  cmp : FnK prof F Wl L s₀ o 0x5dca50#64 (Tc R p n sv I) (Rc R p n I)

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {fb R p sv : Addr} {n : Nat} {I : (Addr → Byte) → Prop}

/-- The frame's bytes from `R + d` are the run's to store into. -/
theorem Env.wR (E : Env prof F Wl L s₀ o fb R p sv n I) {d k : Nat} (h : d + k ≤ 120) :
    ∀ i < k, Foot Wl (Addr.add (R + BitVec.ofNat 64 d) i) := by
  intro i hi
  have e : (R + BitVec.ofNat 64 d).add i = (R - 8).add (8 + d + i) := by
    apply BitVec.eq_of_toNat_eq
    have hR := E.lay.hR
    have hR8 := E.lay.hR8
    have e1 : (R + BitVec.ofNat 64 d).toNat = R.toNat + d := E.lay.tR (by omega)
    have e2 := tS8 E.lay.hR8
    have h1 : (R + BitVec.ofNat 64 d).toNat + (i + 1) ≤ 2 ^ 64 := by rw [e1]; omega
    have h2 : (R - 8).toNat + (8 + d + i + 1) ≤ 2 ^ 64 := by rw [e2]; omega
    rw [toNat_add_of_fits (show i < i + 1 by omega) h1, e1,
      toNat_add_of_fits (show 8 + d + i < 8 + d + i + 1 by omega) h2, e2]
    omega
  rw [e]
  exact E.wS _ (by omega)

/-- The comparator's return address slot is the run's to store into. -/
theorem Env.w8 (E : Env prof F Wl L s₀ o fb R p sv n I) : ∀ i < 8, Foot Wl (Addr.add (R - 8) i) :=
  fun i hi => E.wS i (by omega)

/-- An entry's bytes are the run's to store into. -/
theorem Env.wE (E : Env prof F Wl L s₀ o fb R p sv n I) {x : BitVec 64} (hx : x.toNat < n) :
    ∀ i < 4, Foot Wl (Addr.add (bq p x) i) := by
  intro i hi
  have e : (bq p x).add i = p.add (4 * x.toNat + i) := by
    apply BitVec.eq_of_toNat_eq
    have hp := E.lay.hp
    have e1 := E.lay.tB hx
    have hle : p.toNat + (4 * x.toNat + i + 1) ≤ 2 ^ 64 := by omega
    have h1 : (bq p x).toNat + 4 ≤ 2 ^ 64 := by rw [e1]; omega
    rw [toNat_add_of_fits hi h1, e1, toNat_add_of_fits (Nat.lt_succ_self _) hle]
    omega
  rw [e]
  exact E.wB _ (by omega)

theorem Env.rR (E : Env prof F Wl L s₀ o fb R p sv n I) {d k : Nat} (h : d + k ≤ 120) :
    ∀ i < k, Foot F.data (Addr.add (R + BitVec.ofNat 64 d) i) :=
  fun i hi => E.c.hws _ (E.wR h i hi)

theorem Env.rE (E : Env prof F Wl L s₀ o fb R p sv n I) {x : BitVec 64} (hx : x.toNat < n) :
    ∀ i < 4, Foot F.data (Addr.add (bq p x) i) :=
  fun i hi => E.c.hws _ (E.wE hx i hi)

end

/-! ## Next steps (design notes)

Not yet written: `Sfn/Vc.lean` (the pieces' conditions) and `Sfn/Build.lean`, `Sfn/Sort.lean`, `Sfn/Holds.lean`
(the loops and `sfn_ok`). Plan, as `FV7z.Msi`'s `Holds.lean` (vcs with exact posts `j' = … ∧ g' = {g with …} ∧
V' = …`, the reasoning in the loops through `AtJ`, `(c_J prof fb).run`):

- Instructions outside the blocks: the comparator calls at 320, 356, 553, 589 (`call 0x5dca50`, `Dec` lemmas and
  `tgt_*` as `Msi`'s `qc70`; run with `SpAt.callK … (call_320 _) …` and `Env.cmp`, `Mk.call`, `a1s`); the counter's
  `sub qword [rsp + 32], 2` at 378 (`Seg.s_sub_mi64`, decode `mk .sub 64 [.mem (mbd 4 32 64), .imm 64 2] 6`); the
  `js` at 60 (target outside the code: `Seg.s_jcc_f`, needs the size below `2 ^ 31`).
- Build phase, `Lr R p m sv g := g.rsp = R ∧ g.rbx = p ∧ g.rbp = m ∧ g.r13 = sv` (`m + 1 = n`):
  - `P208 i`: `Lr`, `r15 = i < n`, `Mk W`, the 8 bytes at `R + 32` = `2 i + 1`. `vc_208` (`o10`, `o11`): `temp` :=
    `p[i]`; `m < 2 i + 1` (cond 2) to 378 with `rcx = p[i]`, `rdx = bq p i`; else to 287 with `r14` = `2 i + 1`,
    `[R + 8]` := `i`.
  - Sift-down at 287 (measure `m - c`, `c` = `r14`): `c = m` (cond 6 with `zf`) to 345, `r12 = bq p c`; else 296:
    `r8 = rax + 2`, `[R + 24]` := `r8`, `[R + 16]` := `bq p r8`, comparator (320), 325: `cmovg` twice (`o16`, post
    `g' = G0 ∨ g' = G1`, `split_ifs`, mixed cases by `absurd ((rfz_cond _ _).trans h1) h2`); 345: `rdi = [R + 40]`
    (`&temp`), comparator (356); 361 (`o18`, cond 8 = `(setWidth 32 rax).msb`): taken to 256 (`p[k]` := `p[c]`,
    `rax = 2 c`, `rdx = 2 c + 1`; `m < rdx` to 624 → 378, else 279: `[R + 8]` := `c`, `r14` := `rdx`, to 287); not
    taken to 374 → 378.
  - `P378`: `Lr`, `r15 = i`, `rcx = setWidth 64 temp`, `rdx = bq p y` (`y < n`), `Mk`, `temp < n`, counter `2 i + 1`;
    378 (`sub`), 384: `p[y]` := `ecx` (`Mk.st_B`), `r15 = 0` to 449, else 391: `r15 - 1`, to 208 (counter `2 i - 1`).
- Sort phase from 449 (`rbp = m ≥ 1`, measure `m`): swap `p[m]`, `p[0]`, `temp` := old `p[m]`, `rbp = m - 1`; `zf`
  (`rbp = 1`) to 400, else 469 → sift-down 520 … 606 as above (`r15` the pointer, `[R + 24]` = `&temp`, `test r8d`
  at 594; cases 496, 440, 514, 606).
- `P400`: `rsp = R`, `Mk W`; then the stack guard check (`rdq(W, R + 56) = rdq(W, fb + 40)` from `Tp`), the pops by
  `Tp`, `ret` at 434. The head: 6 pushes, `sub rsp, 72`, the guard, `[rsi + 8]` := 0, the realloc path through
  `operator delete` (0x6014f0) and `new[]` (0x6029b0) as `Arb`'s `kn`, the fill loop (127, 144, 159, 172).
-/

end FV7z.Sfn
