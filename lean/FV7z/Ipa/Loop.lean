import FV7z.Ipa.Vc
import FV7z.Ipa.Set
/-!
# `_dl_init_paths`: the loop over the 4 system directories (PLAN.md G3, startup)

From the `memset` of element `i` (267, `r15 = b` the element, `r14 = a` the next slot of `A`) to the `ret` (450):
`memset (b + 0x28, 0, 4 n)` (`SetAt`), then element `i + 1` (`vc_293`) back to 267, or after the last (`i = 3`) the
ends of the lists and the epilogue (`vc_384`).

- `step`: one element, to 267 with `i + 1` (`i < 3`) or to 450 (`i = 3`).
- `loop`: from element `i ≤ 3` to 450, by `step` and induction on `3 - i`.

What the loop keeps (`Kp`): the bytes below the heap (`0x792980`) and the frame from `llp` (`r - 0x50`) up; the
loads of the pieces are made of the bytes at 267 for element 0 (`V₁`) through it.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The bytes the loop keeps. -/
abbrev Kp (r x : Addr) : Prop := x.toNat < 7940480 ∨ Mal.Kn x ∨ r.toNat - 80 ≤ x.toNat

/-- A load of bytes two maps agree on. -/
theorem kr {V V₁ : Addr → Byte} {P : Addr → Prop} (h : ∀ a, P a → V a = V₁ a) {x : Addr} {n : Nat}
    (hx : ∀ i < n, P (x.add i)) : List.map V (byteAddrs x n) = List.map V₁ (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h _ (hx j hj)

/-- A load of 8 bytes the loop kept, in the frame. -/
theorem kfr {V V₁ : Addr → Byte} {r x : Addr} (h : ∀ a, Kp r a → V a = V₁ a) (h1 : r.toNat - 80 ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ 2 ^ 64) : rdq(V, x) = rdq(V₁, x) := by
  rw [kr h (rgn (p := Kp r) (lo := r.toNat - 80) (hi := 2 ^ 64) (fun a h1 _ => Or.inr (Or.inr h1)) h1 h2 h2)]

/-- A load the loop kept, below the heap. -/
theorem klo {V V₁ : Addr → Byte} {r x : Addr} {n : Nat} (h : ∀ a, Kp r a → V a = V₁ a)
    (h1 : x.toNat + n ≤ 7940480) : List.map V (byteAddrs x n) = List.map V₁ (byteAddrs x n) :=
  kr h (rgn (p := Kp r) (lo := 0) (hi := 7940480) (fun a _ h2 => Or.inl h2) (Nat.zero_le _) h1 (by omega))

theorem m88 (r : Addr) : r + 18446744073709551536#64 - 8 = r + 18446744073709551528#64 := by bv_omega
theorem p88 (r : Addr) : r + 18446744073709551528#64 + 8 = r + 18446744073709551536#64 := by bv_omega

/-- The registers other than `rsp` after a `call` (`set 4`). -/
theorem set4_rsp (g : Gprs) (v : Addr) : (g.set 4 v).rsp = v := rfl
theorem set4_rdi (g : Gprs) (v : Addr) : (g.set 4 v).rdi = g.rdi := rfl
theorem set4_rdx (g : Gprs) (v : Addr) : (g.set 4 v).rdx = g.rdx := rfl
theorem set4_rbx (g : Gprs) (v : Addr) : (g.set 4 v).rbx = g.rbx := rfl
theorem set4_rbp (g : Gprs) (v : Addr) : (g.set 4 v).rbp = g.rbp := rfl
theorem set4_r12 (g : Gprs) (v : Addr) : (g.set 4 v).r12 = g.r12 := rfl
theorem set4_r13 (g : Gprs) (v : Addr) : (g.set 4 v).r13 = g.r13 := rfl
theorem set4_r14 (g : Gprs) (v : Addr) : (g.set 4 v).r14 = g.r14 := rfl
theorem set4_r15 (g : Gprs) (v : Addr) : (g.set 4 v).r15 = g.r15 := rfl

/-- What the run at the `ret` (450) has: `rsp` past the saved `rbp`, the registers the prologue pushed (of `V₁`),
the bytes kept. -/
def Fin450 (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (r : Addr) (V₁ : Addr → Byte) : Prop :=
  ∀ Y t' V', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = ipa_at.add 450 → Y.cpu.gpr.rsp = r + 8#64 →
    Y.cpu.gpr.rbx = rdq(V₁, r + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V₁, r + 18446744073709551584#64) →
    Y.cpu.gpr.r13 = rdq(V₁, r + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V₁, r + 18446744073709551600#64) →
    Y.cpu.gpr.r15 = rdq(V₁, r + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V₁, r) →
    (∀ x : Addr, (x.toNat < 7937712 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ r.toNat - 80 ≤ x.toNat ∨
      Mal.Kn x) → V' x = V₁ x) → GoG prof L o gev gP gE Y t'

set_option maxHeartbeats 4000000 in
/-- After the last element (`i = 3`, at 384): the ends of the lists, then the epilogue (425) to the `ret`. -/
theorem fin3 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa) {V₁ V₂ : Addr → Byte} {r b a : Addr}
    (hr : 8029560 + 88 ≤ r.toNat) (hr2 : r.toNat + 16 ≤ 2 ^ 64)
    (hFD : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot F.data x)
    (hWb : ∀ x : Addr, 7937712 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (h80 : rdq(V₁, r + 18446744073709551536#64) = 0#64)
    (hb1 : 7940480 ≤ b.toNat) (hbk : 8032256 ≤ b.toNat) (hb2 : b.toNat + 8 ≤ r.toNat - 88)
    (hWB : ∀ x : Addr, b.toNat ≤ x.toNat → x.toNat < b.toNat + 8 → Foot Wl x)
    (ha1 : 7940480 ≤ a.toNat) (hak : 8032256 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ r.toNat - 88)
    (hWA : ∀ x : Addr, a.toNat ≤ x.toNat → x.toNat < a.toNat + 8 → Foot Wl x)
    (hk₂ : ∀ x, Kp r x → V₂ x = V₁ x) (kfin : Fin450 prof L o gev gP gE F Wl s₀ r V₁)
    (Y₄ : State) (t₄ : Nat) (hK₄ : KeptW Wl s₀ Y₄) (hA₄ : Agree F Y₄.proc.mm.mem V₂)
    (hr₄ : Y₄.cpu.rip = ipa_at.add 384) (bp₄ : Y₄.cpu.gpr.rbp = r) (r14₄ : Y₄.cpu.gpr.r14 = a)
    (r15₄ : Y₄.cpu.gpr.r15 = b) (hW7a : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x) :
    GoG prof L o gev gP gE Y₄ t₄ := by
  have hr0 : 96 ≤ r.toNat := by omega
  refine (c_384 prof).run c hin _ hK₄ hA₄ hr₄
    (vc_384 (by rw [bp₄, kfr hk₂ (by ifd) (by ifd)]; exact h80) (by rw [bp₄]; omega) (by rw [bp₄]; omega)
      (by rw [r15₄]; exact hb1) (by rw [r15₄]; exact hbk) (by rw [r15₄, bp₄]; omega) (by rw [r14₄]; exact ha1)
      (by rw [r14₄]; exact hak) (by rw [r14₄, bp₄]; omega) (by rw [bp₄]; omega) (by rw [r14₄]; exact hWA)
      (by rw [r15₄]; exact hWB) hW7a
      (by rw [bp₄]; exact fun x h1 h2 => hFD x (by omega) (by omega))) ?_
  rintro j' g' fl V' ⟨rfl, rfl, hkeep, hkn⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hk₅ : ∀ x, Kp r x → V' x = V₁ x := fun x hx => by
    refine Eq.trans ?_ (hk₂ x hx)
    rcases hx with hx | hx | hx
    · exact hkeep x (by rw [bp₄]; omega)
    · exact hkn x hx
    · exact hkeep x (by rw [bp₄]; omega)
  have bp₅ : Y₅.cpu.gpr.rbp = r := by rw [hg₅]; exact bp₄
  refine (c_425 prof).run c hin _ hK₅ hA₅ hr₅
    (vc_425 (by rw [bp₅]; omega) (by rw [bp₅]; omega) hWb
      (by rw [bp₅]; exact fun x h1 h2 => hFD x (by omega) h2)) ?_
  rintro j' g' fl V'' ⟨rfl, hsp', hbx', h12', h13', h14', h15', hbp', hkeep'⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  refine kfin Y₆ t₆ V'' hK₆ hA₆ hr₆ (by rw [hg₆, hsp', bp₅])
    (by rw [hg₆, hbx', bp₅, kfr hk₅ (by ifd) (by ifd)]) (by rw [hg₆, h12', bp₅, kfr hk₅ (by ifd) (by ifd)])
    (by rw [hg₆, h13', bp₅, kfr hk₅ (by ifd) (by ifd)]) (by rw [hg₆, h14', bp₅, kfr hk₅ (by ifd) (by ifd)])
    (by rw [hg₆, h15', bp₅, kfr hk₅ (by ifd) (by ifd)]) (by rw [hg₆, hbp', bp₅, kfr hk₅ (by omega) (by omega)])
    fun x hx => ?_
  rcases hx with h | h | h | h
  · rw [hkeep' x (by omega)]; exact hk₅ x (Or.inl (by omega))
  · rw [hkeep' x (by omega)]; exact hk₅ x (Or.inl (by omega))
  · rw [hkeep' x (by omega)]; exact hk₅ x (Or.inr (Or.inr h))
  · have := Mal.Kn.lt h
    rw [hkeep' x (by omega)]; exact hk₅ x (Or.inr (Or.inl h))

set_option maxHeartbeats 4000000 in
/-- Not the last element (`i < 3`, at 293): element `i + 1`, back to 267. -/
theorem nxt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa) {V₁ V₂ : Addr → Byte} {n q i : Nat}
    {r b a : Addr} (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3) (hi3 : i < 3)
    (hr : 8029560 + 88 ≤ r.toNat) (hr2 : r.toNat + 16 ≤ 2 ^ 64)
    (hFD : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot F.data x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (h72 : rdq(V₁, r + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q))
    (h64 : rdq(V₁, r + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q))
    (h56 : rdq(V₁, r + 18446744073709551560#64) = BitVec.ofNat 64 n)
    (hlen : ∀ k < 3, rdq(V₁, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (lA k))
    (hsl : ∀ k < 3, ofBytesLE 8 (List.map V₁ (byteAddrs (BitVec.ofNat 64 (sA k)) 1)) = 47#8)
    (hb1 : 7940480 ≤ b.toNat) (hbk : 8032256 ≤ b.toNat) (hbn : b.toNat + 80 * q ≤ r.toNat - 88)
    (hWB : ∀ x : Addr, b.toNat ≤ x.toNat → x.toNat < b.toNat + 80 * q → Foot Wl x)
    (ha1 : 7940480 ≤ a.toNat) (hak : 8032256 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ r.toNat - 88)
    (hWA : ∀ x : Addr, a.toNat ≤ x.toNat → x.toNat < a.toNat + 8 → Foot Wl x)
    (hk₂ : ∀ x, Kp r x → V₂ x = V₁ x)
    (knext : ∀ Y t' V', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = ipa_at.add 267 →
      Y.cpu.gpr.rsp = r + 18446744073709551536#64 → Y.cpu.gpr.rbp = r →
      Y.cpu.gpr.r15 = b + BitVec.ofNat 64 (40 * q) → Y.cpu.gpr.r14 = a + 8#64 →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * (i + 1)) → Y.cpu.gpr.rbx = BitVec.ofNat 64 (sA (i + 1)) →
      Y.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) → (∀ x, Kp r x → V' x = V₁ x) → GoG prof L o gev gP gE Y t')
    (Y₄ : State) (t₄ : Nat) (hK₄ : KeptW Wl s₀ Y₄) (hA₄ : Agree F Y₄.proc.mm.mem V₂)
    (hr₄ : Y₄.cpu.rip = ipa_at.add 293) (s₄ : Y₄.cpu.gpr.rsp = r + 18446744073709551536#64)
    (bp₄ : Y₄.cpu.gpr.rbp = r) (r12₄ : Y₄.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i))
    (r13₄ : Y₄.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n)) (r14₄ : Y₄.cpu.gpr.r14 = a) (r15₄ : Y₄.cpu.gpr.r15 = b)
    (rbx₄ : Y₄.cpu.gpr.rbx = BitVec.ofNat 64 (sA i)) : GoG prof L o gev gP gE Y₄ t₄ := by
  have hr0 : 96 ≤ r.toNat := by omega
  refine (c_293 prof).run c hin _ hK₄ hA₄ hr₄
    (vc_293 hq hi3 r12₄ rbx₄ (by rw [bp₄, kfr hk₂ (by ifd) (by ifd)]; exact h72)
      (by rw [bp₄, kfr hk₂ (by ifd) (by ifd)]; exact h64) (by rw [bp₄, kfr hk₂ (by ifd) (by ifd)]; exact h56)
      (by rw [klo (x := BitVec.ofNat 64 (7364040 + 8 * i)) (n := 8) hk₂ (by ifd)]; exact hlen i hi3)
      (by rw [klo (x := BitVec.ofNat 64 (sA i)) (n := 1) hk₂ (by have := sA_le i; ifd)]; exact hsl i hi3)
      (by rw [bp₄]; omega) (by rw [bp₄]; omega) (by rw [r15₄]; exact hb1) (by rw [r15₄]; exact hbk)
      (by rw [r15₄, bp₄]; omega) (by rw [r14₄]; exact ha1) (by rw [r14₄]; exact hak) (by rw [r14₄, bp₄]; omega)
      (by rw [r14₄]; exact hWA)
      (by rw [r15₄]; exact fun x h1 h2 => hWB x h1 (by omega))
      (by rw [bp₄]; exact fun x h1 h2 => hFD x (by omega) (by omega)) hFR) ?_
  rintro j' g' fl V' ⟨rfl, h15', h14', h12', hbx', h13', hbp', hsp', hkeep, hkn⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  refine knext Y₅ t₅ V' hK₅ hA₅ hr₅ (by rw [hg₅, hsp', s₄]) (by rw [hg₅, hbp', bp₄])
    (by rw [hg₅, h15', r15₄]) (by rw [hg₅, h14', r14₄]) (by rw [hg₅, h12']; congr 1; omega) (by rw [hg₅, hbx'])
    (by rw [hg₅, h13', r13₄]) fun x hx => ?_
  refine Eq.trans ?_ (hk₂ x hx)
  rcases hx with hx | hx | hx
  · exact hkeep x (by rw [bp₄]; omega)
  · exact hkn x hx
  · exact hkeep x (by rw [bp₄]; omega)

set_option maxHeartbeats 4000000 in
/-- One element: from 267 (element `i` at `b`, the next slot of `A` at `a`) to 267 with element `i + 1` at
`b + 40 q` (`i < 3`), or to the `ret` (`i = 3`). -/
theorem step (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa)
    {ms : List Byte} (hins : CodeIn L 4198528#64 ms) (hms0 : 0 < ms.length) {Ps : (Addr → Byte) → Prop}
    (hset : SetAt prof L o 4198528#64 Ps) {V₁ : Addr → Byte} {n q i bh : Nat} {r b a : Addr}
    (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3) (hi : i ≤ 3)
    (hPs : ∀ W : Addr → Byte, (∀ x : Addr, x.toNat < 7940480 → W x = V₁ x) → Ps W)
    (hr : 8029560 + 88 ≤ r.toNat) (hr2 : r.toNat + 16 ≤ 2 ^ 64)
    (hFs : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot Wl x ∧ Foot F.data x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hW7a : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hWb : ∀ x : Addr, 7937712 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (h72 : rdq(V₁, r + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q))
    (h64 : rdq(V₁, r + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q))
    (h56 : rdq(V₁, r + 18446744073709551560#64) = BitVec.ofNat 64 n)
    (h80 : rdq(V₁, r + 18446744073709551536#64) = 0#64)
    (hlen : ∀ k < 3, rdq(V₁, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (lA k))
    (hsl : ∀ k < 3, ofBytesLE 8 (List.map V₁ (byteAddrs (BitVec.ofNat 64 (sA k)) 1)) = 47#8)
    (hb1 : 7940480 ≤ b.toNat) (hbk : 8032256 ≤ b.toNat) (hb2 : b.toNat + 40 * q ≤ bh)
    (hbn : i < 3 → b.toNat + 80 * q ≤ bh)
    (hbh : bh ≤ r.toNat - 88) (hWB : ∀ x : Addr, b.toNat ≤ x.toNat → x.toNat < bh → Foot Wl x)
    (ha1 : 7940480 ≤ a.toNat) (hak : 8032256 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ r.toNat - 88)
    (hWA : ∀ x : Addr, a.toNat ≤ x.toNat → x.toNat < a.toNat + 8 → Foot Wl x)
    (X : State) (t : Nat) (V : Addr → Byte) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = ipa_at.add 267) (hsp : X.cpu.gpr.rsp = r + 18446744073709551536#64)
    (hbp : X.cpu.gpr.rbp = r) (h15 : X.cpu.gpr.r15 = b) (h14 : X.cpu.gpr.r14 = a)
    (h12 : X.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i)) (hbx : X.cpu.gpr.rbx = BitVec.ofNat 64 (sA i))
    (h13 : X.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n)) (hkp : ∀ x, Kp r x → V x = V₁ x)
    (knext : i < 3 → ∀ Y t' V', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = ipa_at.add 267 →
      Y.cpu.gpr.rsp = r + 18446744073709551536#64 → Y.cpu.gpr.rbp = r →
      Y.cpu.gpr.r15 = b + BitVec.ofNat 64 (40 * q) → Y.cpu.gpr.r14 = a + 8#64 →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * (i + 1)) → Y.cpu.gpr.rbx = BitVec.ofNat 64 (sA (i + 1)) →
      Y.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) → (∀ x, Kp r x → V' x = V₁ x) → GoG prof L o gev gP gE Y t')
    (kfin : i = 3 → Fin450 prof L o gev gP gE F Wl s₀ r V₁) : GoG prof L o gev gP gE X t := by
  have hFW : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot Wl x :=
    fun x h1 h2 => (hFs x h1 h2).1
  have hFD : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot F.data x :=
    fun x h1 h2 => (hFs x h1 h2).2
  have hr0 : 96 ≤ r.toNat := by omega
  have hnq : 40 + 4 * n ≤ 40 * q := by omega
  have hn16 : n ≤ 16 := by omega
  -- 267: the arguments of `memset`
  refine (c_267 prof).run c hin _ hK hA hrip vc_267 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have s₁ : Y₁.cpu.gpr.rsp = r + 18446744073709551536#64 := by rw [hg₁]; exact hsp
  -- 276: `call memset`
  refine c.s_call hK₁ hA₁ hin (lt_len (by omega)) hr₁ (call_276 _) hins hms0 tgt_276
    (by rw [s₁, m88]; ireg hFW) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [s₁, m88] at hA₂
  have s₂ : Y₂.cpu.gpr.rsp = r + 18446744073709551528#64 := by
    rw [hg₂, set4_rsp, s₁, m88]
  have di₂ : Y₂.cpu.gpr.rdi = b + 40#64 := by
    rw [hg₂, set4_rdi, hg₁]; show X.cpu.gpr.r15 + 40#64 = _; rw [h15]
  have dx₂ : Y₂.cpu.gpr.rdx = BitVec.ofNat 64 (4 * n) := by rw [hg₂, set4_rdx, hg₁]; exact h13
  refine hset c hK₂ hA₂ hr₂ (hPs _ fun x hx => ?_) hin (lt_len (j := 281) (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Tun.Vst_out _ _ _ _ (by ifd) (by ifd)]; exact hkp x (Or.inl hx)
  · rw [s₂, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by ifd), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [s₂]; ireg hFD
  · rw [di₂, dx₂]; ireg hWB
  · rw [di₂, dx₂]; ipd
  · rw [di₂, dx₂, s₂]; ifd
  intro Z t₃ V₂ hK₃ hA₃ hr₃ hs₃ _ hbx₃ hbp₃ h12₃ h13₃ h14₃ h15₃ _ hout₃
  have sZ : Z.cpu.gpr.rsp = r + 18446744073709551536#64 := by rw [hs₃, s₂, p88]
  have bpZ : Z.cpu.gpr.rbp = r := by rw [hbp₃, hg₂, set4_rbp, hg₁]; exact hbp
  have r12Z : Z.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i) := by rw [h12₃, hg₂, set4_r12, hg₁]; exact h12
  have r13Z : Z.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) := by rw [h13₃, hg₂, set4_r13, hg₁]; exact h13
  have r14Z : Z.cpu.gpr.r14 = a := by rw [h14₃, hg₂, set4_r14, hg₁]; exact h14
  have r15Z : Z.cpu.gpr.r15 = b := by rw [h15₃, hg₂, set4_r15, hg₁]; exact h15
  have rbxZ : Z.cpu.gpr.rbx = BitVec.ofNat 64 (sA i) := by rw [hbx₃, hg₂, set4_rbx, hg₁]; exact hbx
  have hk₂ : ∀ x, Kp r x → V₂ x = V₁ x := fun x hx => by
    have hx' : x.toNat < 7940480 ∨ 7943128 ≤ x.toNat ∧ x.toNat < 8032256 ∨ r.toNat - 80 ≤ x.toNat := by
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Mal.Kn.lt h))
      · exact Or.inr (Or.inr h)
    rw [hout₃ x (by rw [di₂, dx₂]; ifd), Tun.Vst_out _ _ _ _ (by ifd) (by ifd)]
    exact hkp x hx
  -- 281: the last directory or not
  refine (c_281 prof).run c hin _ hK₃ hA₃ hr₃ (vc_281 hi r12Z) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have s₄ : Y₄.cpu.gpr.rsp = r + 18446744073709551536#64 := by rw [hg₄]; exact sZ
  have bp₄ : Y₄.cpu.gpr.rbp = r := by rw [hg₄]; exact bpZ
  have r12₄ : Y₄.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i) := by rw [hg₄]; exact r12Z
  have r13₄ : Y₄.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) := by rw [hg₄]; exact r13Z
  have r14₄ : Y₄.cpu.gpr.r14 = a := by rw [hg₄]; exact r14Z
  have r15₄ : Y₄.cpu.gpr.r15 = b := by rw [hg₄]; exact r15Z
  have rbx₄ : Y₄.cpu.gpr.rbx = BitVec.ofNat 64 (sA i) := by rw [hg₄]; exact rbxZ
  by_cases h3 : i = 3
  · rw [if_pos h3] at hr₄
    exact fin3 c hin hr hr2 hFD hWb h80 hb1 hbk (by omega) (fun x h1 h2 => hWB x h1 (by omega)) ha1 hak ha2 hWA
      hk₂
      (kfin h3) Y₄ t₄ hK₄ hA₄ hr₄ bp₄ r14₄ r15₄ hW7a
  · rw [if_neg h3] at hr₄
    have hi3 : i < 3 := by omega
    exact nxt c hin hq hi3 hr hr2 hFD hFR h72 h64 h56 hlen hsl hb1 hbk (by have := hbn hi3; omega)
      (fun x h1 h2 => hWB x h1 (by have := hbn hi3; omega)) ha1 hak ha2 hWA hk₂ (knext hi3)
      Y₄ t₄ hK₄ hA₄ hr₄ s₄ bp₄ r12₄ r13₄ r14₄ r15₄ rbx₄

set_option maxHeartbeats 4000000 in
/-- From the `memset` of element `i ≤ 3` (at `b = B + 40 q i`, the next slot of `A` at `a = A + 8 (i + 1)`) to
the `ret`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa)
    {ms : List Byte} (hins : CodeIn L 4198528#64 ms) (hms0 : 0 < ms.length) {Ps : (Addr → Byte) → Prop}
    (hset : SetAt prof L o 4198528#64 Ps) {V₁ : Addr → Byte} {n q : Nat} {r A B : Addr}
    (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3)
    (hPs : ∀ W : Addr → Byte, (∀ x : Addr, x.toNat < 7940480 → W x = V₁ x) → Ps W)
    (hr : 8029560 + 88 ≤ r.toNat) (hr2 : r.toNat + 16 ≤ 2 ^ 64)
    (hFs : ∀ x : Addr, r.toNat - 88 ≤ x.toNat → x.toNat < r.toNat + 8 → Foot Wl x ∧ Foot F.data x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hW7a : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hWb : ∀ x : Addr, 7937712 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (h72 : rdq(V₁, r + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q))
    (h64 : rdq(V₁, r + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q))
    (h56 : rdq(V₁, r + 18446744073709551560#64) = BitVec.ofNat 64 n)
    (h80 : rdq(V₁, r + 18446744073709551536#64) = 0#64)
    (hlen : ∀ k < 3, rdq(V₁, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (lA k))
    (hsl : ∀ k < 3, ofBytesLE 8 (List.map V₁ (byteAddrs (BitVec.ofNat 64 (sA k)) 1)) = 47#8)
    (hB1 : 7940480 ≤ B.toNat) (hBk : 8032256 ≤ B.toNat) (hB2 : B.toNat + 160 * q ≤ r.toNat - 88)
    (hWB : ∀ x : Addr, B.toNat ≤ x.toNat → x.toNat < B.toNat + 160 * q → Foot Wl x)
    (hA1 : 7940480 ≤ A.toNat) (hAk : 8032256 ≤ A.toNat) (hA2 : A.toNat + 40 ≤ r.toNat - 88)
    (hWA : ∀ x : Addr, A.toNat ≤ x.toNat → x.toNat < A.toNat + 40 → Foot Wl x)
    (kfin : Fin450 prof L o gev gP gE F Wl s₀ r V₁) :
    ∀ i ≤ 3, ∀ (X : State) (t : Nat) (V : Addr → Byte) (b a : Addr), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = ipa_at.add 267 → X.cpu.gpr.rsp = r + 18446744073709551536#64 → X.cpu.gpr.rbp = r →
      X.cpu.gpr.r15 = b → b.toNat = B.toNat + 40 * q * i → X.cpu.gpr.r14 = a → a.toNat = A.toNat + 8 * (i + 1) →
      X.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i) → X.cpu.gpr.rbx = BitVec.ofNat 64 (sA i) →
      X.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) → (∀ x, Kp r x → V x = V₁ x) → GoG prof L o gev gP gE X t := by
  have hq0 := hq
  have hr0 : 96 ≤ r.toNat := by omega
  suffices H : ∀ d i, i + d = 3 → ∀ (X : State) (t : Nat) (V : Addr → Byte) (b a : Addr), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = ipa_at.add 267 → X.cpu.gpr.rsp = r + 18446744073709551536#64 →
      X.cpu.gpr.rbp = r → X.cpu.gpr.r15 = b → b.toNat = B.toNat + 40 * q * i → X.cpu.gpr.r14 = a →
      a.toNat = A.toNat + 8 * (i + 1) → X.cpu.gpr.r12 = BitVec.ofNat 64 (7364032 + 8 * i) →
      X.cpu.gpr.rbx = BitVec.ofNat 64 (sA i) → X.cpu.gpr.r13 = BitVec.ofNat 64 (4 * n) →
      (∀ x, Kp r x → V x = V₁ x) → GoG prof L o gev gP gE X t from
    fun i hi => H (3 - i) i (by omega)
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    intro d
    induction d with
    | zero =>
      intro i hd X t V b a hK hA hrip hsp hbp h15 hb h14 ha h12 hbx h13 hkp
      exact step c hin hins hms0 hset (bh := B.toNat + 160 * _) hq0 (by omega) hPs hr hr2 hFs hFR hW7a hWb
        h72 h64 h56 h80 hlen hsl (by omega) (by omega) (by omega) (fun h => absurd h (by omega)) hB2
        (fun x h1 h2 => hWB x (by omega) h2) (by omega) (by omega) (by omega)
        (fun x h1 h2 => hWA x (by omega) (by omega))
        X t V hK hA hrip hsp hbp h15 h14 h12 hbx h13 hkp (fun h => absurd h (by omega)) (fun _ => kfin)
    | succ d ih =>
      intro i hd X t V b a hK hA hrip hsp hbp h15 hb h14 ha h12 hbx h13 hkp
      exact step c hin hins hms0 hset (bh := B.toNat + 160 * _) hq0 (by omega) hPs hr hr2 hFs hFR hW7a hWb
        h72 h64 h56 h80 hlen hsl (by omega) (by omega) (by omega) (fun _ => by omega) hB2
        (fun x h1 h2 => hWB x (by omega) h2) (by omega) (by omega) (by omega)
        (fun x h1 h2 => hWA x (by omega) (by omega))
        X t V hK hA hrip hsp hbp h15 h14 h12 hbx h13 hkp
        (fun _ Y t' V' hK' hA' hr' hs' hb' h15' h14' h12' hbx' h13' hk' =>
          ih (i + 1) (by omega) Y t' V' _ _ hK' hA' hr' hs' hb' h15' (by ifd) h14' (by ifd) h12' hbx' h13' hk')
        (fun h => absurd h (by omega))

end FV7z.Ipa
