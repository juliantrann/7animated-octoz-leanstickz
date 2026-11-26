import FV7z.Memcpy.FwdP
/-!
# The bytes stored by the backward loop of a copy (PLAN.md M, `__memmove_sse2_unaligned`)

Above 128 bytes with `rsi < rdi`, the copy stores 64 bytes per iteration at decreasing offsets, from an offset `b₀`
down. The stored bytes are still described by `FwdP V V₂ d s b b₀` (`Memcpy/FwdP.lean`), now with its lower end `b`
moving: a store just below `b` (`FwdP.stB`), and the bytes of the source below `b` not yet stored over, the source
lying below the destination (`FwdP.rdB`).

- `HeadX`: the `xmm` registers loaded before the loop for the last stores (the first 64, the last 16 bytes).
- `LoopB`: the registers at the top of the loop; `wr_sub_rcx`, `wr_sub_r9`, `sub_back`: their updates.
-/
namespace FV7z.Memcpy
open ZellicX86 FV7z.Memset

/-- A store of `k` bytes just below the lowest stored offset `b`, those of `V` from `s + o`. -/
theorem FwdP.stB {V V₂ : Addr → Byte} {d s : Addr} {b c : Nat} (h : FwdP V V₂ d s b c) (hbc : b ≤ c)
    {o k : Nat} (ho : o + k = b) (hn : d.toNat + c ≤ 2 ^ 64) {bs : List Byte} (hl : bs.length = k)
    (hb : ∀ j (hj : j < bs.length), bs[j] = V (Addr.add s (o + j))) :
    FwdP V (Vst V₂ (Addr.add d o) bs) d s o c := by
  subst hl
  refine ⟨fun i h1 h2 => ?_, fun x hx => ?_⟩
  · by_cases hi : i < b
    · have e : Addr.add d i = Addr.add (Addr.add d o) (i - o) := by
        rw [addr_add_add]
        congr 1
        omega
      have hf : (Addr.add d o).toNat + bs.length ≤ 2 ^ 64 := by
        rw [toNat_add_of_fits (n := c) (i := o) (by omega) hn]
        omega
      rw [e, Vst_get bs V₂ (Addr.add d o) hf (by omega), hb _ (by omega), show o + (i - o) = i by omega]
    · rw [Vst_apart bs _ _ _ fun j hj e => ?_]
      · exact h.1 i (by omega) h2
      · have h3 := congrArg BitVec.toNat e
        rw [toNat_add_of_fits (n := c) (i := i) (by omega) hn, addr_add_add,
          toNat_add_of_fits (n := c) (i := o + j) (by omega) hn] at h3
        omega
  · rw [Vst_apart bs _ _ _ fun j hj e => hx ?_]
    · exact h.2 x fun ⟨h1, h2⟩ => hx ⟨by omega, h2⟩
    · rw [e, addr_add_add, toNat_add_of_fits (n := c) (i := o + j) (by omega) hn]
      omega

/-- A byte of the source below the lowest stored offset, the source below the destination: not yet stored over. -/
theorem FwdP.rdB {V V₂ : Addr → Byte} {d s : Addr} {b c : Nat} (h : FwdP V V₂ d s b c)
    (hsd : s.toNat ≤ d.toNat) {i : Nat} (hi : i < b) (hs : s.toNat + i < 2 ^ 64) :
    V₂ (Addr.add s i) = V (Addr.add s i) :=
  h.2 _ fun ⟨h1, _⟩ => by
    rw [toNat_add_of_fits (n := i + 1) (i := i) (by omega) (by omega)] at h1
    omega

/-- The registers `xmm4` to `xmm8` the backward copy loads before its loop: the first 64 and the last 16 bytes of
`V` from `s`, `n` bytes. -/
structure HeadX (V : Addr → Byte) (s : Addr) (n : Nat) (x : XRegs) : Prop where
  x4 : x (xmmOf 4) = ofBytesLE 128 ((byteAddrs (Addr.add s 0) 16).map V)
  x5 : x (xmmOf 5) = ofBytesLE 128 ((byteAddrs (Addr.add s 16) 16).map V)
  x6 : x (xmmOf 6) = ofBytesLE 128 ((byteAddrs (Addr.add s 32) 16).map V)
  x7 : x (xmmOf 7) = ofBytesLE 128 ((byteAddrs (Addr.add s 48) 16).map V)
  x8 : x (xmmOf 8) = ofBytesLE 128 ((byteAddrs (Addr.add s (n - 16)) 16).map V)

theorem HeadX.set {V : Addr → Byte} {s : Addr} {n : Nat} {x : XRegs} (h : HeadX V s n x) (k : Fin 32)
    (v : BitVec 128) (h4 : xmmOf 4 ≠ k) (h5 : xmmOf 5 ≠ k) (h6 : xmmOf 6 ≠ k) (h7 : xmmOf 7 ≠ k)
    (h8 : xmmOf 8 ≠ k) : HeadX V s n (xset x k v) :=
  ⟨by rw [xset_ne _ _ h4]; exact h.x4, by rw [xset_ne _ _ h5]; exact h.x5, by rw [xset_ne _ _ h6]; exact h.x6,
    by rw [xset_ne _ _ h7]; exact h.x7, by rw [xset_ne _ _ h8]; exact h.x8⟩

/-- The registers at the top of the backward loop, the bytes from offset `b` on stored, of a copy from `g₀`
returning `r`: `rcx` and `r9` at the last 16 bytes below `b` of the source and the destination. -/
structure LoopB (g₀ : Gprs) (r : Addr) (b : Nat) (g : Gprs) : Prop where
  di : g.rdi = g₀.rdi
  si : g.rsi = g₀.rsi
  dx : g.rdx.toNat = b
  cx : g.rcx = Addr.add g₀.rsi (b - 16)
  r9 : g.r9 = Addr.add g₀.rdi (b - 16)
  r11 : g.r11 = Addr.add g₀.rdi (g₀.rdx.toNat - 16)
  kp : KpS g₀ g
  ax : g.rax = r

theorem wr_sub_rcx (g : Gprs) (m : Nat) :
    (wr g 1 (subR (gv g 64 1) (BitVec.ofNat 64 m))).rcx = g.rcx - BitVec.ofNat 64 m := by
  show (subR (g.rcx.setWidth 64) (BitVec.ofNat 64 m)).setWidth 64 = _
  rw [sw_64_64, subR_eq, sw_64_64]

theorem wr_sub_r9 (g : Gprs) (m : Nat) :
    (wr g 9 (subR (gv g 64 9) (BitVec.ofNat 64 m))).r9 = g.r9 - BitVec.ofNat 64 m := by
  show (subR (g.r9.setWidth 64) (BitVec.ofNat 64 m)).setWidth 64 = _
  rw [sw_64_64, subR_eq, sw_64_64]

/-- `a + m - k`, `k ≤ m`. -/
theorem sub_back (a : Addr) {m k : Nat} (hk : k ≤ m) :
    Addr.add a m - BitVec.ofNat 64 k = Addr.add a (m - k) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end FV7z.Memcpy
