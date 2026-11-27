import FV7z.U16.Vc
/-!
# `Utf8_To_Utf16`: the invariant (PLAN.md §M, M1)

The definitions behind `u16_ok` (design in `U16.Holds`): the flag bits `Fl`, `Uf`, `Z2`, `Z4`; the count `Ct`, `NN`,
`Rm`, `Ib` over `Cnt`'s `cnt`/`rem`/`inn`; the frame `FR`; the loop's registers `Gu`; the caller's facts `Pr`, `Bud`;
the invariant `Inv` (11 disjuncts), the exit `Fx` and `Nx`. Then the count's steps (`ct_*`, `rm_*`, `ib_*`) and the
intro lemmas `i2`–`i11` (an exit's `Nx` from the target's facts).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

/-! ## Definitions -/

/-- `flags`. -/
abbrev Fl (g₀ : Gprs) : BitVec 32 := w32(g₀.r8)
/-- Bit 0 of `flags` set (no surrogates). -/
abbrev Uf (g₀ : Gprs) : Bool := !zr (Fl g₀ &&& 1#32)
/-- Bit 1 of `flags` clear (an error skips the bytes read). -/
abbrev Z2 (g₀ : Gprs) : Bool := zr (Fl g₀ &&& 2#32)
/-- Bit 2 of `flags` clear (no escapes). -/
abbrev Z4 (g₀ : Gprs) : Bool := zr (Fl g₀ &&& 4#32)

/-- The characters from the `k`-th byte on. -/
def Ct (g₀ : Gprs) (V₀ : Addr → Byte) (n k : Nat) : Nat := cnt V₀ g₀.rdx n (Uf g₀) (Z2 g₀) (Z4 g₀) k
/-- All the characters. -/
def NN (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Nat := Ct g₀ V₀ n 0
/-- The characters from a lead byte's form on. -/
def Rm (g₀ : Gprs) (V₀ : Addr → Byte) (n k : Nat) (r : Res) : Nat := rem V₀ g₀.rdx n (Uf g₀) (Z2 g₀) (Z4 g₀) k r
/-- The inner loop of the `k`-th byte's form, `j` its continuation bytes. -/
abbrev Ib (g₀ : Gprs) (V₀ : Addr → Byte) (n k j m e : Nat) (d : BitVec 32) : Res :=
  inn V₀ g₀.rdx n k (Uf g₀) (128#32 >>> j) m e d
/-- The frame: the memory after the entry's stores, but for `dest`. -/
abbrev FR (g₀ : Gprs) (V₀ : Addr → Byte) (W : Nat) (V : Addr → Byte) : Prop := Fr (Vs1 g₀ V₀) g₀.rdi W V
/-- The registers in the loop. -/
abbrev Gu (g₀ : Gprs) (a c d bp s i x y r11 : BitVec 64) : Gprs :=
  ⟨a, c, d, g₀.rdi, S6 g₀.rsp, bp, s, i, x, y, g₀.rcx, r11, w64(Fl g₀ &&& 2#32), w64(128#32), w64(65533#32),
    w64(Fl g₀ &&& 1#32)⟩

/-- What the caller gives: `srcLim = src + n` (no wrap), the stack, `dest` (`W` bytes) and `destLen` apart, and the
footprints. -/
structure Pr (F : Footprint) (Wl : List Rgn) (g₀ : Gprs) (n W : Nat) : Prop where
  lim : g₀.rcx = g₀.rdx + BitVec.ofNat 64 n
  pn : g₀.rdx.toNat + n < 2 ^ 64
  sp : 64 ≤ g₀.rsp.toNat
  spT : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  dT : g₀.rdi.toNat + W ≤ 2 ^ 64
  pT : g₀.rsi.toNat + 8 ≤ 2 ^ 64
  sDS : g₀.rdi.toNat + W + 60 ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat
  sDp : g₀.rdi.toNat + W ≤ g₀.rdx.toNat ∨ g₀.rdx.toNat + n ≤ g₀.rdi.toNat
  spS : g₀.rdx.toNat + n + 60 ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ g₀.rdx.toNat
  sPS : g₀.rsi.toNat + 56 ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rsi.toNat
  fa : ∀ k < n, ∀ i < 1, Foot F.data (Addr.add (g₀.rdx + BitVec.ofNat 64 k) i)
  fw : ∀ j < W, ∀ i < 1, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 j) i)
  fst : ∀ x : Addr, g₀.rsp.toNat ≤ x.toNat + 60 → x.toNat < g₀.rsp.toNat → Foot Wl x
  fsr : ∀ x : Addr, g₀.rsp.toNat ≤ x.toNat + 60 → x.toNat < g₀.rsp.toNat → Foot F.data x
  fra : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i)
  fP : ∀ i < 8, Foot Wl (Addr.add g₀.rsi i)

/-- The characters fit in `dest` (when there is one). -/
def Bud (g₀ : Gprs) (V₀ : Addr → Byte) (n W : Nat) : Prop := g₀.rdi ≠ 0 → 4 * NN g₀ V₀ n ≤ W

/-- The invariant at the cut points, `c` the characters so far (`r11`), `k` the byte (`rdx` or `r9 - 1`): the entry;
116, 125 at the `k`-th byte; 109, 141 with one character for it; 174 with a lead byte's form set up; 209, 192, 201 in
its inner loop (`e` read, `ms` left); 272 with a form that fails; 295, 299 with its character; 392 with a whole form;
492, 409, 413 with its characters stored; 312 at the end. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (n W ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = 30 * n + 40 ∧ g = g₀ ∧ V = V₀) ∨
  (∃ o, ((ℓ = 116 ∧ o = 30) ∨ (ℓ = 125 ∧ o = 29)) ∧ ∃ k ≤ n, (ℓ = 125 → k < n) ∧ m = 30 * (n - k) + o ∧
    ∃ c, c + Ct g₀ V₀ n k = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx bp s i x y, g = Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) ∨
  (∃ o, ((ℓ = 109 ∧ o = 2) ∨ (ℓ = 141 ∧ o = 3 ∧ g₀.rdi ≠ 0)) ∧ ∃ k < n, m = 30 * (n - k) + o ∧
    ∃ c, c + 1 + Ct g₀ V₀ n (k + 1) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx d bp s i x, g = Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) ∨
  (ℓ = 174 ∧ ∃ k < n, ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ m = 30 * (n - k) + 28 ∧
    ∃ c, c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j (j - 1) 0 (d0 (by8 V₀ g₀.rdx k) j)) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a bp s i x, g = Gu g₀ a (w64(BitVec.ofNat 32 j)) (w64(d0 (by8 V₀ g₀.rdx k) j)) bp s i x
      (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) ∨
  (ℓ = 209 ∧ ∃ k j ms e, ms + e + 1 = j ∧ j ≤ 3 ∧ k + 1 + e ≤ n ∧ m = 30 * (n - k) + 24 - 5 * e ∧
    ∃ c dd, c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j ms e dd) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a bp, g = Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 e))
      (g₀.rdx + BitVec.ofNat 64 (k + 1 + e)) (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) ∨
  (∃ o, ((ℓ = 192 ∧ o = 22) ∨ (ℓ = 201 ∧ o = 21)) ∧ ∃ k j ms e, ms + e + 1 = j ∧ j ≤ 3 ∧ k + 1 + e < n ∧
    (ℓ = 201 → ms ≠ 0) ∧ m = 30 * (n - k) + o - 5 * e ∧
    ∃ c dd, c + Rm g₀ V₀ n k (if ms = 0 then .ok dd (e + 1) else Ib g₀ V₀ n k j (ms - 1) (e + 1) dd) = NN g₀ V₀ n ∧
    FR g₀ V₀ W V ∧
    ∃ a bp, g = Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 (e + 1)))
      (g₀.rdx + BitVec.ofNat 64 (k + 1 + e)) (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) ∨
  (ℓ = 272 ∧ ∃ k e, e ≤ 3 ∧ k + 1 + e ≤ n ∧ m = 30 * (n - k) + 8 ∧
    ∃ c, c + Rm g₀ V₀ n k (.err e) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx d bp s i x, w32(s) = BitVec.ofNat 32 e ∧
      g = Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) ∨
  (∃ o, ((ℓ = 295 ∧ o = 33 ∧ g₀.rdi ≠ 0) ∨ (ℓ = 299 ∧ o = 32)) ∧ ∃ k ≤ n, m = 30 * (n - k) + o ∧
    ∃ c, c + 1 + Ct g₀ V₀ n k = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx bp s i x y, g = Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) ∨
  (ℓ = 392 ∧ ∃ k e q dd, ((big dd = true ∧ q = 2) ∨ (big dd = false ∧ q = 1)) ∧ 1 ≤ e ∧ e ≤ 3 ∧ k + 1 + e ≤ n ∧
    m = 30 * (n - k) + 8 ∧ ∃ c, c + q + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx bp i x, g = Gu g₀ a cx (w64(dd)) bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) ∨
  (∃ o q, ((ℓ = 492 ∧ o = 7 ∧ q = 2) ∨ (ℓ = 409 ∧ o = 7 ∧ q = 1) ∨ (ℓ = 413 ∧ o = 6 ∧ q = 0)) ∧
    ∃ k e, 1 ≤ e ∧ e ≤ 3 ∧ k + 1 + e ≤ n ∧ m = 30 * (n - k) + o ∧
    ∃ c, c + q + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n ∧ FR g₀ V₀ W V ∧
    ∃ a cx d bp i x, g = Gu g₀ a cx d bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) ∨
  (ℓ = 312 ∧ m = 0 ∧ g.rsp = S6 g₀.rsp ∧ g.r11 = BitVec.ofNat 64 (NN g₀ V₀ n) ∧
    (Fr (Vs0 g₀ V₀) g₀.rdi W V ∨ FR g₀ V₀ W V))

/-- The memory at the end: as at the entry outside the 60 bytes below `rsp`, the `W` bytes from `dest` and the 8 bytes
of `destLen`. -/
def FinM (g₀ : Gprs) (V₀ : Addr → Byte) (W : Nat) (V : Addr → Byte) : Prop :=
  ∀ x : Addr, (x.toNat + 60 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ x.toNat) →
    (x.toNat < g₀.rdi.toNat ∨ g₀.rdi.toNat + W ≤ x.toNat) → (x.toNat < g₀.rsi.toNat ∨ g₀.rsi.toNat + 8 ≤ x.toNat) →
    V x = V₀ x
/-- At the `ret`: `*destLen` the count, `eax = 1`, the callee-saved registers back. -/
def Fx (g₀ : Gprs) (V₀ : Addr → Byte) (n W j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 335 ∧ FinM g₀ V₀ W V ∧ rdq(V, g₀.rsi) = BitVec.ofNat 64 (NN g₀ V₀ n) ∧ ∃ c d s i x y u v,
    g = { g₀ with rax := w64(1#32), rcx := c, rdx := d, rsi := s, rdi := i, r8 := x, r9 := y, r10 := u, r11 := v }
/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n W m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ n W j m' g V) ∨ Fx g₀ V₀ n W j g V

/-! ## The count's steps -/

section count
variable {g₀ : Gprs} {V₀ : Addr → Byte} {n k : Nat}

theorem ct_ge (hk : n ≤ k) : Ct g₀ V₀ n k = 0 := by
  unfold Ct; exact cnt_ge hk
theorem ct_a (hk : k < n) (h : na (by8 V₀ g₀.rdx k) = false) : Ct g₀ V₀ n k = 1 + Ct g₀ V₀ n (k + 1) := by
  unfold Ct; rw [cnt_lt hk, step_a h]
  try rfl
theorem ct_b (hk : k < n) (h : lv (by8 V₀ g₀.rdx k) = false) : Ct g₀ V₀ n k = 1 + Ct g₀ V₀ n (k + 1) := by
  unfold Ct; rw [cnt_lt hk, step_b h]
  try rfl
theorem ct_c {j : Nat} (hk : k < n) (h1 : na (by8 V₀ g₀.rdx k) = true) (h2 : lv (by8 V₀ g₀.rdx k) = true)
    (hj : nc (by8 V₀ g₀.rdx k) = j) :
    Ct g₀ V₀ n k = Rm g₀ V₀ n k (Ib g₀ V₀ n k j (j - 1) 0 (d0 (by8 V₀ g₀.rdx k) j)) := by
  unfold Ct Rm rem; rw [cnt_lt hk, step_c h1 h2, hj]
  try rfl

theorem rm_fin {r : Res} {a b : Nat} (h : fin k (Z2 g₀) (Z4 g₀) r = (a, b)) : Rm g₀ V₀ n k r = a + Ct g₀ V₀ n b := by
  unfold Rm rem Ct; rw [h]
  try rfl

theorem rm_e1 {e : Nat} (h : Z2 g₀ = true) : Rm g₀ V₀ n k (.err e) = 1 + Ct g₀ V₀ n (k + 1 + e) :=
  rm_fin (by show (1, bif Z2 g₀ then k + 1 + e else k + 1) = _; rw [h, Bool.cond_true])
theorem rm_e2 {e : Nat} (h : Z2 g₀ = false) : Rm g₀ V₀ n k (.err e) = 1 + Ct g₀ V₀ n (k + 1) :=
  rm_fin (by show (1, bif Z2 g₀ then k + 1 + e else k + 1) = _; rw [h, Bool.cond_false])
theorem rm_esc {d : BitVec 32} {e : Nat} (h : (!Z4 g₀ && esc d) = true) :
    Rm g₀ V₀ n k (.ok d e) = 1 + Ct g₀ V₀ n (k + 1) :=
  rm_fin (by
    show (bif !Z4 g₀ && esc d then (1, k + 1) else bif big d then (2, k + 1 + e) else (1, k + 1 + e)) = _
    rw [h, Bool.cond_true])
theorem rm_ok2 {d : BitVec 32} {e : Nat} (h : (!Z4 g₀ && esc d) = false) (hb : big d = true) :
    Rm g₀ V₀ n k (.ok d e) = 2 + Ct g₀ V₀ n (k + 1 + e) :=
  rm_fin (by
    show (bif !Z4 g₀ && esc d then (1, k + 1) else bif big d then (2, k + 1 + e) else (1, k + 1 + e)) = _
    rw [h, Bool.cond_false, hb, Bool.cond_true])
theorem rm_ok1 {d : BitVec 32} {e : Nat} (h : (!Z4 g₀ && esc d) = false) (hb : big d = false) :
    Rm g₀ V₀ n k (.ok d e) = 1 + Ct g₀ V₀ n (k + 1 + e) :=
  rm_fin (by
    show (bif !Z4 g₀ && esc d then (1, k + 1) else bif big d then (2, k + 1 + e) else (1, k + 1 + e)) = _
    rw [h, Bool.cond_false, hb, Bool.cond_false])

/-! The inner loop's steps in `Ib`'s form. -/
variable {j m e : Nat} {d : BitVec 32}

theorem ib_end (h : k + 1 + e = n) : Ib g₀ V₀ n k j m e d = .err e := inn_end h
theorem ib_bad (h : ¬ k + 1 + e = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + e)) = true) :
    Ib g₀ V₀ n k j m e d = .err e := inn_bad h hb
theorem ib_ovl (h : ¬ k + 1 + 0 = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + 0)) = false)
    (ho : ovl (128#32 >>> j) (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = true) : Ib g₀ V₀ n k j m 0 d = .err 1 :=
  inn_ovl h hb ho
theorem ib_sur (h : ¬ k + 1 + 0 = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + 0)) = false)
    (ho : ovl (128#32 >>> j) (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false) (hu : Uf g₀ = true)
    (hs : nsg (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false) : Ib g₀ V₀ n k j 1 0 d = .err 1 :=
  inn_sur h hb ho hu hs
theorem ib_hi (h : ¬ k + 1 + 0 = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + 0)) = false)
    (ho : ovl (128#32 >>> j) (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false)
    (hl : l271 (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false) : Ib g₀ V₀ n k j 2 0 d = .err 1 :=
  inn_hi h hb ho hl
/-- A continuation byte past the first. -/
theorem ib_go (h : ¬ k + 1 + e = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + e)) = false) (he : e ≠ 0) :
    Ib g₀ V₀ n k j m e d = if m = 0 then .ok (acc d (by8 V₀ g₀.rdx (k + 1 + e))) (e + 1)
      else Ib g₀ V₀ n k j (m - 1) (e + 1) (acc d (by8 V₀ g₀.rdx (k + 1 + e))) :=
  inn_go h hb (fun h' => he h'.1) (fun h' => he h'.1) (fun h' => he h'.1)
/-- The first continuation byte, the checks passed. -/
theorem ib_g0 (h : ¬ k + 1 + 0 = n) (hb : bad (by8 V₀ g₀.rdx (k + 1 + 0)) = false)
    (ho : ovl (128#32 >>> j) (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false)
    (hs : ¬ (m = 1 ∧ Uf g₀ = true ∧ nsg (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false))
    (hl : ¬ (m = 2 ∧ l271 (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) = false)) :
    Ib g₀ V₀ n k j m 0 d = if m = 0 then .ok (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) (0 + 1)
      else Ib g₀ V₀ n k j (m - 1) (0 + 1) (acc d (by8 V₀ g₀.rdx (k + 1 + 0))) :=
  inn_go h hb (fun h' => nt ho h'.2) (fun h' => hs h'.2) (fun h' => hl h'.2)

end count

/-! ## Intro lemmas: an exit's `Nx` from the target's facts (registers by unification) -/

section intro
variable {g₀ : Gprs} {V₀ : Addr → Byte} {n W μ : Nat} {fl : Rflags} {V : Addr → Byte}

theorem i2 {ℓ o k c : Nat} (hl : (ℓ = 116 ∧ o = 30) ∨ (ℓ = 125 ∧ o = 29)) (hk : k ≤ n) (h5 : ℓ = 125 → k < n)
    (hμ : 30 * (n - k) + o < μ) (hc : c + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V)
    {a cx bp s i x y : BitVec 64} :
    Nx g₀ V₀ n W μ ℓ (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inl ⟨o, hl, k, hk, h5, rfl, c, hc, hF, a, cx, bp, s, i, x, y, rfl⟩)⟩
theorem i3 {ℓ o k c : Nat} (hl : (ℓ = 109 ∧ o = 2) ∨ (ℓ = 141 ∧ o = 3 ∧ g₀.rdi ≠ 0)) (hk : k < n)
    (hμ : 30 * (n - k) + o < μ) (hc : c + 1 + Ct g₀ V₀ n (k + 1) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V)
    {a cx d bp s i x : BitVec 64} :
    Nx g₀ V₀ n W μ ℓ (Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inl ⟨o, hl, k, hk, rfl, c, hc, hF, a, cx, d, bp, s, i, x, rfl⟩))⟩
theorem i4 {k j c : Nat} (hk : k < n) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (hμ : 30 * (n - k) + 28 < μ)
    (hc : c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j (j - 1) 0 (d0 (by8 V₀ g₀.rdx k) j)) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V)
    {a bp s i x : BitVec 64} :
    Nx g₀ V₀ n W μ 174 (Gu g₀ a (w64(BitVec.ofNat 32 j)) (w64(d0 (by8 V₀ g₀.rdx k) j)) bp s i x
      (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, j, hj1, hj3, rfl, c, hc, hF, a, bp, s, i, x, rfl⟩)))⟩
theorem i5 {k j ms e c : Nat} {dd : BitVec 32} (hj : ms + e + 1 = j) (hj3 : j ≤ 3) (hk : k + 1 + e ≤ n)
    (hμ : 30 * (n - k) + 24 - 5 * e < μ) (hc : c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j ms e dd) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) {a bp : BitVec 64} :
    Nx g₀ V₀ n W μ 209 (Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 e))
      (g₀.rdx + BitVec.ofNat 64 (k + 1 + e)) (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, k, j, ms, e, hj, hj3, hk, rfl, c, dd, hc, hF, a, bp, rfl⟩))))⟩
theorem i6 {ℓ o k j ms e c : Nat} {dd : BitVec 32} (hl : (ℓ = 192 ∧ o = 22) ∨ (ℓ = 201 ∧ o = 21))
    (hj : ms + e + 1 = j) (hj3 : j ≤ 3) (hk : k + 1 + e < n) (h5 : ℓ = 201 → ms ≠ 0)
    (hμ : 30 * (n - k) + o - 5 * e < μ)
    (hc : c + Rm g₀ V₀ n k (if ms = 0 then .ok dd (e + 1) else Ib g₀ V₀ n k j (ms - 1) (e + 1) dd) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) {a bp : BitVec 64} :
    Nx g₀ V₀ n W μ ℓ (Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 (e + 1)))
      (g₀.rdx + BitVec.ofNat 64 (k + 1 + e)) (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨o, hl, k, j, ms, e, hj, hj3, hk, h5, rfl, c, dd, hc, hF, a, bp, rfl⟩)))))⟩
theorem i7 {k e c : Nat} (he : e ≤ 3) (hk : k + 1 + e ≤ n) (hμ : 30 * (n - k) + 8 < μ)
    (hc : c + Rm g₀ V₀ n k (.err e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) {a cx d bp s i x : BitVec 64}
    (hs : w32(s) = BitVec.ofNat 32 e) :
    Nx g₀ V₀ n W μ 272 (Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, k, e, he, hk, rfl, c, hc, hF, a, cx, d, bp, s, i, x, hs, rfl⟩))))))⟩
theorem i8 {ℓ o k c : Nat} (hl : (ℓ = 295 ∧ o = 33 ∧ g₀.rdi ≠ 0) ∨ (ℓ = 299 ∧ o = 32)) (hk : k ≤ n)
    (hμ : 30 * (n - k) + o < μ) (hc : c + 1 + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V)
    {a cx bp s i x y : BitVec 64} :
    Nx g₀ V₀ n W μ ℓ (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨o, hl, k, hk, rfl, c, hc, hF, a, cx, bp, s, i, x, y, rfl⟩)))))))⟩
theorem i9 {k e q c : Nat} {dd : BitVec 32} (hq : (big dd = true ∧ q = 2) ∨ (big dd = false ∧ q = 1)) (he1 : 1 ≤ e)
    (he3 : e ≤ 3) (hk : k + 1 + e ≤ n) (hμ : 30 * (n - k) + 8 < μ)
    (hc : c + q + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) {a cx bp i x : BitVec 64} :
    Nx g₀ V₀ n W μ 392 (Gu g₀ a cx (w64(dd)) bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, k, e, q, dd, hq, he1, he3, hk, rfl, c, hc, hF, a, cx, bp, i, x, rfl⟩))))))))⟩
theorem i10 {ℓ o q k e c : Nat}
    (hl : (ℓ = 492 ∧ o = 7 ∧ q = 2) ∨ (ℓ = 409 ∧ o = 7 ∧ q = 1) ∨ (ℓ = 413 ∧ o = 6 ∧ q = 0)) (he1 : 1 ≤ e)
    (he3 : e ≤ 3) (hk : k + 1 + e ≤ n) (hμ : 30 * (n - k) + o < μ)
    (hc : c + q + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) {a cx d bp i x : BitVec 64} :
    Nx g₀ V₀ n W μ ℓ (Gu g₀ a cx d bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) fl V :=
  Or.inl ⟨_, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨o, q, hl, k, e, he1, he3, hk, rfl, c, hc, hF, a, cx, d, bp, i, x, rfl⟩)))))))))⟩
theorem i11 {g : Gprs} (hμ : 0 < μ) (hs : g.rsp = S6 g₀.rsp) (hr : g.r11 = BitVec.ofNat 64 (NN g₀ V₀ n))
    (hF : Fr (Vs0 g₀ V₀) g₀.rdi W V ∨ FR g₀ V₀ W V) : Nx g₀ V₀ n W μ 312 g fl V :=
  Or.inl ⟨0, hμ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨rfl, rfl, hs, hr, hF⟩)))))))))⟩

end intro

end FV7z.U16
