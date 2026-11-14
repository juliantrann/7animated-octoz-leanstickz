import FV7z.Hwc.Strs
import FV7z.Hwc.Post
/-!
# `_dl_important_hwcaps`: from the `malloc` to the `ret`, 1116 → 1681 (PLAN.md G3, startup)

`vc_1116` (the table `P` from `malloc`, nine stores: `M16`), the strings (`loop`, 1248 → 1392), `post` (→ 1681).
`temp` (`cnt` entries `st m`, `ln m`) at `R`, the frame from `Fb = bp - 0xa8` to `bp + 8`, the table and the strings
from `P` below the stack (`sp - 8`, the slot of the return address of the `call`s of `mempcpy`).

- `M16`: the memory after the stores of 1116; `M16.same` (the bytes it keeps), the loads of what it stored.
- `caps_congr`, `pt_congr`: the lengths and the pointers only depend on `temp` and on `str[0]`, `str[1]`.
- `from1116`: the result: the table (`Tab`), `*Q`, the callee-saved registers from the frame, the memory kept
  below `P`, from `sp` to `Fb` and above `Fb + 88`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

set_option maxRecDepth 100000

/-! ## The frame -/

theorem fo68 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551512#64).toNat = (r + 18446744073709551448#64).toNat + 64 := by
  bv_omega

theorem fo70 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551504#64).toNat = (r + 18446744073709551448#64).toNat + 56 := by
  bv_omega

theorem fo78 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551496#64).toNat = (r + 18446744073709551448#64).toNat + 48 := by
  bv_omega

theorem fo88 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551480#64).toNat = (r + 18446744073709551448#64).toNat + 32 := by
  bv_omega

theorem fo8c {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551476#64).toNat = (r + 18446744073709551448#64).toNat + 28 := by
  bv_omega

theorem fo98 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551464#64).toNat = (r + 18446744073709551448#64).toNat + 16 := by
  bv_omega

theorem fo28 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551576#64).toNat = (r + 18446744073709551448#64).toNat + 128 := by
  bv_omega

theorem fo20 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551584#64).toNat = (r + 18446744073709551448#64).toNat + 136 := by
  bv_omega

theorem fo18 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551592#64).toNat = (r + 18446744073709551448#64).toNat + 144 := by
  bv_omega

theorem fo10 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551600#64).toNat = (r + 18446744073709551448#64).toNat + 152 := by
  bv_omega

theorem fo08 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551608#64).toNat = (r + 18446744073709551448#64).toNat + 160 := by
  bv_omega

theorem fobp {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    r.toNat = (r + 18446744073709551448#64).toNat + 168 := by
  bv_omega

set_option hygiene false in
/-- `omega` with the slots of the frame as offsets from `bp - 0xa8` (`hfb` the bound of the frame): the offsets are
rewritten first, so that `omega` sees one atom of the frame (many make it time out, a128). -/
macro "fomega" : tactic => `(tactic| ((try simp only [FV7z.toBytesLE_length, fo48 hfb, fo50 hfb, fo58 hfb, fo60 hfb,
  foa0 hfb, fo80 hfb, fo68 hfb, fo70 hfb, fo78 hfb, fo88 hfb, fo8c hfb, fo98 hfb, fo28 hfb, fo20 hfb, fo18 hfb,
  fo10 hfb, fo08 hfb, fobp hfb]) <;> omega))

/-- A load through the stores apart from it, down to the store it reads (or to the memory under them); the side
conditions as goals, so that a failing one stops the `repeat` (a `by` inside the `rw` only logs its error). -/
macro "vpeel" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.rd_Vst _ _ _ _ _ ?_ ?_ ?_]; rotate_left; iterate 3 fomega)))

/-- `n` bytes from `x` inside a region. -/
theorem rng {p : Addr → Prop} {lo hi : Nat} (hp : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → p a) {x : Addr}
    {n : Nat} (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) (h3 : x.toNat + n ≤ 2 ^ 64) : ∀ i < n, p (x.add i) :=
  fun i hi' => by
    have e := toNat_add_of_fits hi' h3
    exact hp _ (by rw [e]; omega) (by rw [e]; omega)

/-- The first byte of a store. -/
theorem Vst_hd (V : Addr → Byte) (a : Addr) (b : Byte) (bs : List Byte) (h : a.toNat + 1 + bs.length ≤ 2 ^ 64) :
    Vst V a (b :: bs) a = b := by
  show Vst (upd1 V a b) (a.add 1) bs a = b
  rw [Tun.Vst_out _ _ _ _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)]
  simp [upd1]

/-! ## The stores of 1116 -/

/-- The memory after 1116: `m = cnt - 1` (`rbp - 0x78`), `*P = P[2] = P + 16 E` (the first string), `k = H`
(`rbp - 0x68`), `E` (`rbp - 0x80`), `P` (`rbp - 0xa8`), `cnt - 2` (`rbp - 0x60`), `B` (`rbp - 0x58`), `cnt`
(`rbp - 0xa0`). -/
def M16 (V : Addr → Byte) (bp P : Addr) (cnt E H : Nat) (B : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (bp + 18446744073709551496#64)
    (toBytesLE (BitVec.ofNat 32 (cnt - 1)) 4))
    P (toBytesLE (P + BitVec.ofNat 64 (16 * E)) 8)) (P + 16#64) (toBytesLE (P + BitVec.ofNat 64 (16 * E)) 8))
    (bp + 18446744073709551512#64) (toBytesLE (BitVec.ofNat 32 H) 4)) (bp + 18446744073709551488#64)
    (toBytesLE (BitVec.ofNat 64 E) 8))
    (bp + 18446744073709551448#64) (toBytesLE P 8)) (bp + 18446744073709551520#64)
    (toBytesLE (BitVec.ofNat 64 (cnt - 2)) 8))
    (bp + 18446744073709551528#64) (toBytesLE B 8))
    (bp + 18446744073709551456#64) (toBytesLE (BitVec.ofNat 64 cnt) 8)

section
variable (V : Addr → Byte) (bp P : Addr) (cnt E H : Nat) (B : Addr)
  (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
  (hP : P.toNat + 24 ≤ (bp + 18446744073709551448#64).toNat)
include hfb hP

/-- The bytes `M16` keeps: below `P`, from `P + 24` to the frame, the gaps of the frame, above `bp - 0x50`. -/
theorem M16.same {lo hi : Nat} (h : hi ≤ P.toNat ∨ P.toNat + 24 ≤ lo ∧ hi ≤ (bp + 18446744073709551448#64).toNat ∨
      (bp + 18446744073709551448#64).toNat + 16 ≤ lo ∧ hi ≤ (bp + 18446744073709551448#64).toNat + 40 ∨
      (bp + 18446744073709551448#64).toNat + 52 ≤ lo ∧ hi ≤ (bp + 18446744073709551448#64).toNat + 64 ∨
      (bp + 18446744073709551448#64).toNat + 88 ≤ lo) :
    Same V (M16 V bp P cnt E H B) lo hi := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  iterate 9 refine Same.st ?_ (by fomega) (by fomega)
  exact Same.refl _ _ _

theorem M16.rdP : rdq(M16 V bp P cnt E H B, P) = P + BitVec.ofNat 64 (16 * E) ∧
    rdq(M16 V bp P cnt E H B, P + 16#64) = P + BitVec.ofNat 64 (16 * E) := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  constructor
  · vpeel
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]
  · vpeel
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rd60 : rdq(M16 V bp P cnt E H B, bp + 18446744073709551520#64) = BitVec.ofNat 64 (cnt - 2) := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rd58 : rdq(M16 V bp P cnt E H B, bp + 18446744073709551528#64) = B := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rda0 : rdq(M16 V bp P cnt E H B, bp + 18446744073709551456#64) = BitVec.ofNat 64 cnt := by
  unfold M16
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rda8 : rdq(M16 V bp P cnt E H B, bp + 18446744073709551448#64) = P := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rd80 : rdq(M16 V bp P cnt E H B, bp + 18446744073709551488#64) = BitVec.ofNat 64 E := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M16.rd68 : rdd(M16 V bp P cnt E H B, bp + 18446744073709551512#64) = BitVec.ofNat 32 H := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 4) rfl]

theorem M16.rd78 (hc : cnt = 3 ∨ cnt = 4) :
    ofBytesLE 8 (List.map (M16 V bp P cnt E H B) (byteAddrs (bp + 18446744073709551496#64) 1)) =
      BitVec.ofNat 8 (cnt - 1) := by
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  unfold M16
  vpeel
  rw [Tun.rd1, show toBytesLE (BitVec.ofNat 32 (cnt - 1)) 4 =
      BitVec.ofNat 8 (cnt - 1) :: (toBytesLE (BitVec.ofNat 32 (cnt - 1)) 4).tail by
    rcases hc with rfl | rfl <;> decide]
  exact Vst_hd _ _ _ _ (by simp only [List.length_tail, toBytesLE_length]; fomega)

end

/-! ## The lengths and the pointers -/

theorem caps_congr {E : Nat} {Tl Tl' : Nat → Addr} : ∀ (n : Nat) (ℓ : Nat → Addr), (∀ j < n, Tl j = Tl' j) →
    caps E Tl n ℓ = caps E Tl' n ℓ
  | 0, _, _ => rfl
  | n + 1, ℓ, h => by
    rw [caps_succ, caps_succ, h n (by omega)]
    exact caps_congr n _ fun j hj => h j (by omega)

theorem pt1_congr {σ σ' ℓ : Nat → Addr} (h0 : σ 0 = σ' 0) (h1 : σ 1 = σ' 1) : ∀ i, pt1 σ ℓ i = pt1 σ' ℓ i
  | 0 => h0
  | 1 => h1
  | i + 2 => by rw [pt1_ss, pt1_ss, pt1_congr h0 h1 (i + 1), pt1_congr h0 h1 i]

theorem pt_congr {σ σ' ℓ : Nat → Addr} {H : Nat} {T : Addr} (h0 : σ 0 = σ' 0) (h1 : σ 1 = σ' 1) (i : Nat) :
    pt σ ℓ H T i = pt σ' ℓ H T i := by
  unfold pt
  rw [pt1_congr h0 h1 i, pt1_congr h0 h1 (i - H)]

/-! ## 1116 → 1681 -/

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy : List Byte} {Pm : (Addr → Byte) → Prop}

set_option maxHeartbeats 4000000 in
/-- After the `malloc` (1116, `rax = P`): the table of `E = 2^cnt` entries at `P` (the pointers `pt` from the first
string `P + 16 E`, the lengths `caps`), the strings above it, `*Q`, to the `ret` (1681). -/
theorem from1116 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    {V : Addr → Byte} (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    {cnt E H : Nat} {P R bp sp Q : Addr} {ln st : Nat → Addr}
    (hn : cnt = 3 ∧ E = 8 ∧ H = 4 ∨ cnt = 4 ∧ E = 16 ∧ H = 8)
    (hlo : 7940480 ≤ P.toNat) (hbuf : P.toNat + 16 * E + rem cnt ln H ≤ sp.toNat - 8) (hsp8 : 8 ≤ sp.toNat)
    (hRs : sp.toNat ≤ R.toNat) (hRF : R.toNat + 16 * cnt ≤ (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hWP : ∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + 16 * E + rem cnt ln H → Foot Wl a ∧ Foot F.data a)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hFr : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hT : ∀ m < cnt, rdq(V, R + BitVec.ofNat 64 (16 * m)) = st m ∧ rdq(V, R + BitVec.ofNat 64 (16 * m + 8)) = ln m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ P.toNat + 16 * E ∨
      P.toNat + 16 * E + rem cnt ln H ≤ (st m).toNat)
    (hN : rdd(V, bp + 18446744073709551520#64) = BitVec.ofNat 32 cnt)
    (hD : rdq(V, bp + 18446744073709551512#64) = R + BitVec.ofNat 64 (16 * (cnt - 1)))
    (hR8 : rdq(V, bp + 18446744073709551480#64) = BitVec.ofNat 64 E)
    (hD8 : rdq(V, bp + 18446744073709551464#64) = BitVec.ofNat 64 (16 * cnt))
    (hE4 : rdd(V, bp + 18446744073709551476#64) = BitVec.ofNat 32 E)
    (hL : rdq(V, bp + 18446744073709551536#64) = ln (cnt - 1))
    (hl : rdq(V, bp + 18446744073709551544#64) = ln 0)
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : ∀ Y t' (W : Addr → Byte), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (tlen V R) cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → Y.cpu.gpr.rsp = bp + 8#64 →
      Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
      Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
      Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
      Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (tlen V R) cnt (fun _ => 0#64)) H (ln (cnt - 1)))
        (caps E (tlen V R) cnt (fun _ => 0#64)) →
      Same V W 0 P.toNat → Same V W sp.toNat (bp + 18446744073709551448#64).toNat →
      Same V W ((bp + 18446744073709551448#64).toNat + 88) (2 ^ 64) → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1116 →
      X.cpu.gpr.rax = P → X.cpu.gpr.r12 = BitVec.ofNat 64 cnt → X.cpu.gpr.r13 = BitVec.ofNat 64 (16 * E) →
      X.cpu.gpr.rbx = R → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = sp → GoG prof L o gev gP gE X t := by
  intro X t hK hA hrip hax h12 h13 hbx hbp hsp
  have hsl := sp.isLt
  have hRl := R.isLt
  have hE8 : 8 ≤ E := by fomega
  have hcn : cnt = 3 ∨ cnt = 4 := by fomega
  have h2c : 2 ^ (cnt - 1) = H := by rcases hn with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ <;> rfl
  have hP24 : P.toNat + 24 ≤ (bp + 18446744073709551448#64).toNat := by fomega
  have mrd60 := M16.rd60 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrd58 := M16.rd58 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrda0 := M16.rda0 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrda8 := M16.rda8 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrd80 := M16.rd80 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrd68 := M16.rd68 V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrdP := M16.rdP V bp P cnt E H (st (cnt - 1)) hfb hP24
  have mrd78 := M16.rd78 V bp P cnt E H (st (cnt - 1)) hfb hP24 hcn
  have msame := @M16.same V bp P cnt E H (st (cnt - 1)) hfb hP24
  have e16 : (P + 16#64).toNat = P.toNat + 16 := addO (by fomega)
  have eD : (R + BitVec.ofNat 64 (16 * (cnt - 1))).toNat = R.toNat + 16 * (cnt - 1) := addO (by fomega)
  have hFrW : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a := fun a h1 h2 => (hFr a h1 h2).1
  have hFrD : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot F.data a := fun a h1 h2 => (hFr a h1 h2).2
  have hWPW : ∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + 16 * E + rem cnt ln H → Foot Wl a :=
    fun a h1 h2 => (hWP a h1 h2).1
  have hT0 : rdq(V, R) = st 0 := by
    have := (hT 0 (by fomega)).1
    rwa [Nat.mul_zero, BitVec.add_zero] at this
  -- 1116: the nine stores
  refine (c_1116 prof fb).run c hfs hin _ hK hA hrip
    (vc_1116 (n := cnt) (m := cnt - 1) (q := cnt - 2) (k := H) (e := E) (r := 16 * E)
      (D := R + BitVec.ofNat 64 (16 * (cnt - 1))) (B := st (cnt - 1)) (A := st 0) (by fomega)
      (by rw [hax]; rintro rfl; simp at hlo) h12 h13 (by rw [hbp]; exact hN) (by rw [hbp]; exact hD)
      (by
        rw [hbp, hax]
        vpeel
        rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 4) rfl])
      (by
        rw [hbp, hax]
        vpeel
        exact (hT _ (by fomega)).1)
      (by
        rw [hbp, hax, hbx]
        vpeel
        exact hT0)
      (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))
      (rng hFT (by fomega) (by fomega) (by fomega))
      (by rw [hbx]; exact rng hFT (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hax]; exact rng hWPW (by fomega) (by fomega) (by fomega))
      (by rw [hax]; exact rng hWPW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hAY' : Agree F Y.proc.mm.mem (M16 V bp P cnt E H (st (cnt - 1))) := by
    rw [hbp, hax, h12] at hAY
    exact hAY
  have hdiY : Y.cpu.gpr.rdi.toNat = P.toNat + 16 * E := by
    rw [hgY]
    show (X.cpu.gpr.rax + BitVec.ofNat 64 (16 * E)).toNat = _
    rw [hax]
    exact addO (by fomega)
  -- the bytes of `M16`
  have rdM : ∀ {x : Addr} {n : Nat}, x.toNat + n ≤ 2 ^ 64 →
      (P.toNat + 24 ≤ x.toNat ∧ x.toNat + n ≤ (bp + 18446744073709551448#64).toNat ∨
        (bp + 18446744073709551448#64).toNat + 16 ≤ x.toNat ∧
          x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 40 ∨
        (bp + 18446744073709551448#64).toNat + 52 ≤ x.toNat ∧
          x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 64 ∨
        (bp + 18446744073709551448#64).toNat + 88 ≤ x.toNat) →
      List.map (M16 V bp P cnt E H (st (cnt - 1))) (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun {x n} hx h => (msame (lo := x.toNat) (hi := x.toNat + n)
      (by fomega)).rd (Nat.le_refl _) (Nat.le_refl _) hx
  have rdW : ∀ {W : Addr → Byte} {A p : Nat} {x : Addr} {n : Nat},
      Outs (M16 V bp P cnt E H (st (cnt - 1))) W A p sp.toNat → sp.toNat ≤ x.toNat → x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ (bp + 18446744073709551448#64).toNat ∨
        (bp + 18446744073709551448#64).toNat + 16 ≤ x.toNat ∧
          x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 40 ∨
        (bp + 18446744073709551448#64).toNat + 52 ≤ x.toNat ∧
          x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 64 ∨
        (bp + 18446744073709551448#64).toNat + 88 ≤ x.toNat) →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun hO hs hx h => (hO.2.2.rd hs hx hx).trans (rdM hx (by fomega))
  have hPm' : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = M16 V bp P cnt E H (st (cnt - 1)) a) →
      Pm W := fun W hW => hPm W fun a ha => (hW a ha).trans
    (msame (lo := 0) (hi := P.toNat) (by fomega) a (Nat.zero_le _)
      (by fomega))
  -- 1248 → 1392: the strings
  refine loop c hfs hin hinc hc0 hcpy (V₀ := M16 V bp P cnt E H (st (cnt - 1))) hPm' (A := P.toNat + 16 * E)
    (B := P.toNat + 16 * E + rem cnt ln H) (pe := P.toNat + 16 * E + rem cnt ln H) (sp := sp) (R := R) (bp := bp)
    (Ev := BitVec.ofNat 64 E) (Cv := BitVec.ofNat 64 cnt) (Pv := P) (ln := ln) (st := st) hcn (by fomega) hbuf
    hsp8 (Nat.le_refl _) (fun a h1 h2 => hWPW a (by fomega) h2) hst hRs (by fomega) hFT
    (fun m h1 h2 => by
      have e1 : (R + BitVec.ofNat 64 (16 * m + 8)).toNat = R.toNat + (16 * m + 8) := addO (by fomega)
      have e2 : (R + BitVec.ofNat 64 (16 * m)).toNat = R.toNat + 16 * m := addO (by fomega)
      rw [rdM (by fomega) (by fomega), rdM (by fomega) (by fomega)]
      exact ⟨(hT m (by fomega)).2, (hT m (by fomega)).1⟩)
    hsrc hs64 hsd (by fomega) hfb (mrd60) (mrd58)
    (by rw [rdM (by fomega) (by fomega)]; exact hL) (by rw [rdM (by fomega) (by fomega)]; exact hl)
    (mrda0) (mrda8) (mrd80)
    (rng hFrD (by fomega) (by fomega) (by fomega)) (rng hFrD (by fomega) (by fomega) (by fomega))
    (rng hFrD (by fomega) (by fomega) (by fomega)) (rng hFrD (by fomega) (by fomega) (by fomega))
    (rng hFrD (by fomega) (by fomega) (by fomega)) (rng hFrD (by fomega) (by fomega) (by fomega))
    (rng hFrD (by fomega) (by fomega) (by fomega)) ?_ (H / 2 - 1) (by rw [h2c]; fomega) Y t' _ hKY hAY' hrY
    (by rw [hgY]; exact hsp) (by rw [hgY]; exact hbx) (by rw [hgY]; exact hbp)
    (by rw [hgY, show 2 * (H / 2 - 1) + 2 = H by fomega]) (by rw [hgY]) (by rw [hgY]) (by fomega)
    (by rw [hdiY, show 2 * (H / 2 - 1) + 2 = H by fomega])
    ⟨Same.refl _ _ _, Same.refl _ _ _, Same.refl _ _ _⟩
  intro Z t₂ W hKZ hAZ hrZ hax0 hcx hr12 hr14 hspZ hbxZ hbpZ hdiZ hOZ
  have hgx : Z.cpu.gpr = { Z.cpu.gpr with rax := 0#64 } := by
    rw [← hax0]
    try rfl
  have hcapsEq : caps E (tlen W Z.cpu.gpr.rbx) cnt (fun _ => 0#64) = caps E (tlen V R) cnt (fun _ => 0#64) := by
    rw [hbxZ]
    refine caps_congr cnt _ fun j hj => ?_
    have e : (R + BitVec.ofNat 64 (16 * j + 8)).toNat = R.toNat + (16 * j + 8) := addO (by fomega)
    unfold tlen
    rw [rdW hOZ (by fomega) (by fomega) (by fomega)]
  -- 1392 → 1681
  refine post c hfs hin (g₀ := Z.cpu.gpr) (cnt := cnt) (E := E) (D := 16 * cnt) (H := H) (T := ln (cnt - 1))
    (Q := Q) (V₀ := W) (by fomega) hcx hr12 (by rw [hr14, hbxZ]; fomega) (by rw [hbxZ]; fomega)
    (by rw [hr14, hbpZ]; fomega) (by rw [hbpZ]; fomega)
    (by rw [hbpZ, rdW hOZ (by fomega) (by fomega) (by fomega)]; exact hR8)
    (by rw [hbpZ, rdW hOZ (by fomega) (by fomega) (by fomega)]; exact hD8)
    (by rw [hbpZ, rdW hOZ (by fomega) (by fomega) (by fomega)]; exact hE4)
    (by rw [hbpZ, hOZ.2.2.rd (by fomega) (by fomega) (by fomega)]; exact mrd78)
    (by rw [hbpZ, hOZ.2.2.rd (by fomega) (by fomega) (by fomega)]; exact mrd68)
    (by rw [hbpZ, rdW hOZ (by fomega) (by fomega) (by fomega)]; exact hL)
    (by rw [hbpZ, rdW hOZ (by fomega) (by fomega) (by fomega)]; exact hQ) hsQ
    (by rw [hr14]; exact fun a h1 h2 => hWP a h1 (by fomega)) (by rw [hbxZ]; exact hFT)
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega))
    (by rw [hbpZ]; exact rng hFrD (by fomega) (by fomega) (by fomega)) ?_ Z t₂ hKZ hAZ hrZ hgx
  intro Y4 t4 W4 σF a9 hK4 hA4 hr4 hg4 hT4 hσ hS4 hS4'
  rw [hcapsEq] at hA4 hT4 hσ
  rw [hr14] at hT4 hσ hS4 hS4'
  have rdS : ∀ (bs : List Byte) (x : Addr), bs.length = 8 → (bp + 18446744073709551448#64).toNat + 128 ≤ x.toNat →
      x.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 176 → rdq(Vst W4 Q bs, x) = rdq(V, x) :=
    fun bs x hl h1 h2 => by
      rw [Tun.rd_Vst _ _ _ _ _ (by rw [hl]; fomega) (by fomega) (by rw [hl]; fomega),
        hS4.rd (by fomega) (by fomega) (by fomega), rdW hOZ (by fomega) (by fomega) (by fomega)]
  have h0 : rdq(W, P + BitVec.ofNat 64 (16 * 0)) = P + BitVec.ofNat 64 (16 * E) := by
    rw [Nat.mul_zero, BitVec.add_zero, hOZ.1.rdq (by fomega) (by fomega) (by fomega)]
    exact (mrdP).1
  have h1 : rdq(W, P + BitVec.ofNat 64 (16 * 1)) = P + BitVec.ofNat 64 (16 * E) := by
    rw [Nat.mul_one, hOZ.1.rdq (by fomega) (by fomega) (by fomega)]
    exact (mrdP).2
  refine k Y4 t4 W4 hK4 hA4 hr4 (by rw [hg4]; exact hr14) (by rw [hg4]; dsimp only; rw [hbpZ])
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (by rw [hg4]; dsimp only; rw [hbpZ]; exact rdS _ _ (toBytesLE_length _ _) (by fomega) (by fomega))
    (hT4.congr (fun i hi => (hσ i hi).trans (pt_congr (σ := fun i => rdq(W, P + BitVec.ofNat 64 (16 * i)))
      (σ' := fun _ => P + BitVec.ofNat 64 (16 * E)) h0 h1 i)) (fun _ _ => rfl)) ?_ ?_ ?_
  · exact (msame (lo := 0) (hi := P.toNat) (by fomega)).trans
      ((hOZ.1.mono (Nat.le_refl _) (by fomega)).trans hS4')
  · exact (msame (lo := sp.toNat) (hi := (bp + 18446744073709551448#64).toNat)
      (by fomega)).trans ((hOZ.2.2.mono (Nat.le_refl _) (by fomega)).trans (hS4.mono (by fomega) (by fomega)))
  · exact (msame (lo := (bp + 18446744073709551448#64).toNat + 88) (hi := 2 ^ 64)
      (by fomega)).trans ((hOZ.2.2.mono (by fomega) (Nat.le_refl _)).trans (hS4.mono (by fomega) (Nat.le_refl _)))

end FV7z.Hwc
