import FV7z.Memcpy.Small2
/-!
# The bytes stored by the forward loop of a copy (PLAN.md M, `__memmove_sse2_unaligned`)

Above 128 bytes with `rdi < rsi`, the copy stores 64 bytes per iteration at increasing offsets, from an offset `a₀`
on. The bytes it loads from `rsi` lie at or past the next offset to be stored, so they are still the source's.
`FwdP V V₂ d s a₀ a`: `V₂` is `V` outside the bytes from `d + a₀` to `d + a`, and inside them the bytes of `V` from `s`.

- `FwdP.start`, `FwdP.st`: a store at the next offset; `FwdP.rd`: a byte of the source past the stored ones;
  `FwdP.copyP`: as `CopyP` (`Lemmas/CopyP.lean`), for the copy's last stores.
- `TailX`: the `xmm` registers loaded before the loop for the last stores (the first 16, the last 64 bytes).
- `add_back`, `wr_add_rsi`, `wr_add_rdi`, `wr_sub_rdx`: addresses and the loop's register updates.
-/
namespace FV7z.Memcpy
open ZellicX86

/-- `V₂`: `V` outside the bytes from `d + a₀` to `d + a`, those of `V` from `s` within. -/
def FwdP (V V₂ : Addr → Byte) (d s : Addr) (a₀ a : Nat) : Prop :=
  (∀ i, a₀ ≤ i → i < a → V₂ (Addr.add d i) = V (Addr.add s i)) ∧
    ∀ x : Addr, ¬ (d.toNat + a₀ ≤ x.toNat ∧ x.toNat < d.toNat + a) → V₂ x = V x

theorem FwdP.start (V : Addr → Byte) (d s : Addr) (a : Nat) : FwdP V V d s a a :=
  ⟨fun _ h1 h2 => absurd h2 (by omega), fun _ _ => rfl⟩

/-- A store of `k` bytes at the next offset `a`, those of `V` from `s + a`. -/
theorem FwdP.st0 {V V₂ : Addr → Byte} {d s : Addr} {a₀ a k : Nat} (h : FwdP V V₂ d s a₀ a) (ha : a₀ ≤ a)
    (hn : d.toNat + a + k ≤ 2 ^ 64) {bs : List Byte} (hl : bs.length = k)
    (hb : ∀ j (hj : j < bs.length), bs[j] = V (Addr.add s (a + j))) :
    FwdP V (Vst V₂ (Addr.add d a) bs) d s a₀ (a + k) := by
  subst hl
  refine ⟨fun i h1 h2 => ?_, fun x hx => ?_⟩
  · by_cases hi : a ≤ i
    · have e : Addr.add d i = Addr.add (Addr.add d a) (i - a) := by
        rw [addr_add_add]
        congr 1
        omega
      have hf : (Addr.add d a).toNat + bs.length ≤ 2 ^ 64 := by
        rw [toNat_add_of_fits (n := a + bs.length) (i := a) (by omega) (by omega)]
        omega
      rw [e, Vst_get bs V₂ (Addr.add d a) hf (by omega), hb _ (by omega), show a + (i - a) = i by omega]
    · rw [Vst_apart bs _ _ _ fun j hj e => ?_]
      · exact h.1 i h1 (by omega)
      · have h3 := congrArg BitVec.toNat e
        rw [toNat_add_of_fits (n := a + bs.length) (i := i) (by omega) (by omega), addr_add_add,
          toNat_add_of_fits (n := a + bs.length) (i := a + j) (by omega) (by omega)] at h3
        omega
  · rw [Vst_apart bs _ _ _ fun j hj e => hx ?_]
    · exact h.2 x fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩
    · rw [e, addr_add_add, toNat_add_of_fits (n := a + bs.length) (i := a + j) (by omega) (by omega)]
      omega

/-- `FwdP.st0` with the offset stored at written `o`. -/
theorem FwdP.st {V V₂ : Addr → Byte} {d s : Addr} {a₀ a : Nat} (h : FwdP V V₂ d s a₀ a) (ha : a₀ ≤ a)
    {o k : Nat} (ho : o = a) (hn : d.toNat + a + k ≤ 2 ^ 64) {bs : List Byte} (hl : bs.length = k)
    (hb : ∀ j (hj : j < bs.length), bs[j] = V (Addr.add s (o + j))) :
    FwdP V (Vst V₂ (Addr.add d o) bs) d s a₀ (a + k) := by
  subst ho
  exact FwdP.st0 h ha hn hl hb

/-- A byte of the source at or past the next offset: not yet stored over. -/
theorem FwdP.rd {V V₂ : Addr → Byte} {d s : Addr} {a₀ a : Nat} (h : FwdP V V₂ d s a₀ a)
    (hds : d.toNat ≤ s.toNat) {i : Nat} (hi : a ≤ i) (hs : s.toNat + i < 2 ^ 64) :
    V₂ (Addr.add s i) = V (Addr.add s i) :=
  h.2 _ fun ⟨_, h2⟩ => by
    rw [toNat_add_of_fits (n := i + 1) (i := i) (by omega) (by omega)] at h2
    omega

/-- As `CopyP`, the bytes from offset `a₀` to `a` copied. -/
theorem FwdP.copyP {V V₂ : Addr → Byte} {d s : Addr} {a₀ a n : Nat} (h : FwdP V V₂ d s a₀ a) (ha : a ≤ n) :
    CopyP V V₂ d s n fun i => a₀ ≤ i ∧ i < a :=
  ⟨fun i _ hP => h.1 i hP.1 hP.2, fun x hx => h.2 x fun ⟨h1, h2⟩ => hx ⟨by omega, by omega⟩⟩

/-- The registers `xmm4` to `xmm8` the copy loads before its loop: the first 16 and the last 64 bytes of `V` from
`s`, `n` bytes. -/
structure TailX (V : Addr → Byte) (s : Addr) (n : Nat) (x : XRegs) : Prop where
  x4 : x (xmmOf 4) = ofBytesLE 128 ((byteAddrs (Addr.add s 0) 16).map V)
  x5 : x (xmmOf 5) = ofBytesLE 128 ((byteAddrs (Addr.add s (n - 16)) 16).map V)
  x6 : x (xmmOf 6) = ofBytesLE 128 ((byteAddrs (Addr.add s (n - 32)) 16).map V)
  x7 : x (xmmOf 7) = ofBytesLE 128 ((byteAddrs (Addr.add s (n - 48)) 16).map V)
  x8 : x (xmmOf 8) = ofBytesLE 128 ((byteAddrs (Addr.add s (n - 64)) 16).map V)

theorem TailX.set {V : Addr → Byte} {s : Addr} {n : Nat} {x : XRegs} (h : TailX V s n x) (k : Fin 32)
    (v : BitVec 128) (h4 : xmmOf 4 ≠ k) (h5 : xmmOf 5 ≠ k) (h6 : xmmOf 6 ≠ k) (h7 : xmmOf 7 ≠ k)
    (h8 : xmmOf 8 ≠ k) : TailX V s n (xset x k v) :=
  ⟨by rw [xset_ne _ _ h4]; exact h.x4, by rw [xset_ne _ _ h5]; exact h.x5, by rw [xset_ne _ _ h6]; exact h.x6,
    by rw [xset_ne _ _ h7]; exact h.x7, by rw [xset_ne _ _ h8]; exact h.x8⟩

/-- `a + m` and a negative displacement `D = 2 ^ 64 - k`. -/
theorem add_back (a : Addr) (m : Nat) {k D : Nat} (hD : D + k = 2 ^ 64) (hk : k ≤ m) :
    Addr.add a m + BitVec.ofNat 64 D = Addr.add a (m - k) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem wr_add_rsi (g : Gprs) (m : Nat) :
    (wr g 6 (addR (gv g 64 6) (BitVec.ofNat 64 m))).rsi = Addr.add g.rsi m := by
  show (addR (g.rsi.setWidth 64) (BitVec.ofNat 64 m)).setWidth 64 = _
  rw [sw_64_64, addR_eq, sw_64_64, Addr.add]

theorem wr_add_rdi (g : Gprs) (m : Nat) :
    (wr g 7 (addR (gv g 64 7) (BitVec.ofNat 64 m))).rdi = Addr.add g.rdi m := by
  show (addR (g.rdi.setWidth 64) (BitVec.ofNat 64 m)).setWidth 64 = _
  rw [sw_64_64, addR_eq, sw_64_64, Addr.add]

theorem wr_sub_rdx (g : Gprs) (m : Nat) :
    (wr g 2 (subR (gv g 64 2) (BitVec.ofNat 64 m))).rdx = g.rdx - BitVec.ofNat 64 m := by
  show (subR (g.rdx.setWidth 64) (BitVec.ofNat 64 m)).setWidth 64 = _
  rw [sw_64_64, subR_eq, sw_64_64]

/-- `x - m`, `m ≤ x`. -/
theorem toNat_sub_le {x : Addr} {m : Nat} (h : m ≤ x.toNat) :
    (x - BitVec.ofNat 64 m).toNat = x.toNat - m := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end FV7z.Memcpy
