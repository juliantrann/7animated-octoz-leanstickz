import FV7z.Start.Keep
/-!
# The names `_dl_non_dynamic_init` calls `getenv` with (PLAN.md G3, startup)

`Ndi.Cx` asks for `NmOk` of the seven names (`LD_WARN`, `LD_LIBRARY_PATH`, `LD_BIND_NOW`, `LD_BIND_NOT`,
`LD_DYNAMIC_WEAK`, `LD_PROFILE_OUTPUT`, `LD_ASSUME_KERNEL`), one after the other in `.rodata` at `0x6f3930`. Each
begins with `LD_`, so an environment with no string beginning with `LD_` has none beginning with the name and `=`.

- `nms`, `nms_pin`, `nmL`, `nms_ok`: the 99 bytes in the file, and where each name lies in them.
- `ent_nms`: the bytes in `lif_ok`'s bytes.
- `nm_ok`: `NmOk` of a name, for bytes that are the file's there and an environment with no string beginning
  with `LD_`.
- `no_ld`: that hypothesis, from the launch's environment.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- The seven names, each with its 0. -/
def nms : List Byte := [
  0x4c, 0x44, 0x5f, 0x57, 0x41, 0x52, 0x4e, 0x00, 0x4c, 0x44, 0x5f, 0x4c, 0x49, 0x42, 0x52, 0x41, 0x52, 0x59,
  0x5f, 0x50, 0x41, 0x54, 0x48, 0x00, 0x4c, 0x44, 0x5f, 0x42, 0x49, 0x4e, 0x44, 0x5f, 0x4e, 0x4f, 0x57, 0x00,
  0x4c, 0x44, 0x5f, 0x42, 0x49, 0x4e, 0x44, 0x5f, 0x4e, 0x4f, 0x54, 0x00, 0x4c, 0x44, 0x5f, 0x44, 0x59, 0x4e,
  0x41, 0x4d, 0x49, 0x43, 0x5f, 0x57, 0x45, 0x41, 0x4b, 0x00, 0x4c, 0x44, 0x5f, 0x50, 0x52, 0x4f, 0x46, 0x49,
  0x4c, 0x45, 0x5f, 0x4f, 0x55, 0x54, 0x50, 0x55, 0x54, 0x00, 0x4c, 0x44, 0x5f, 0x41, 0x53, 0x53, 0x55, 0x4d,
  0x45, 0x5f, 0x4b, 0x45, 0x52, 0x4e, 0x45, 0x4c, 0x00]

theorem nms_pin : Exe.bytesAt V2606.zzs.blob 0x6f3930 99 = some nms := by decide +kernel

/-- Each name's offset in `nms` and its length. -/
def nmL : List (Nat × Nat) := [(0, 7), (8, 15), (24, 11), (36, 11), (48, 15), (64, 17), (82, 16)]

theorem nms_ok : ∀ p ∈ nmL, 3 ≤ p.2 ∧ p.1 + p.2 < 99 ∧ (∀ k < p.2, nms.getD (p.1 + k) 0 ≠ 0) ∧
    nms.getD (p.1 + p.2) 0 = 0 ∧ nms.getD p.1 0 = 0x4c ∧ nms.getD (p.1 + 1) 0 = 0x44 ∧
    nms.getD (p.1 + 2) 0 = 0x5f := by decide

theorem nms_add (j : Nat) : Addr.add 7289136#64 j = BitVec.ofNat 64 (0x6f3930 + j) := by
  simp only [Addr.add]
  bv_omega

/-- The names in `lif_ok`'s bytes. -/
theorem ent_nms {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    ∀ j < 99, Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
      (Addr.add 7289136#64 j) = nms.getD j 0 := by
  intro j hj
  have t := tg (b := 7289136) hj (by omega)
  rw [ent_ro hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega) (hD _ (by omega) (by omega)), nms_add]
  exact hI _ _ _ nms_pin (by decide) (by decide) j hj

/-- `NmOk` of the name at offset `o`, for bytes `M` that have the names and an environment with no string
beginning with `LD_`. -/
theorem nm_ok {E : Ndi.Ev} {M : Addr → Byte} {F : Footprint} {o n : Nat} (hon : (o, n) ∈ nmL)
    (hM : ∀ j < 99, M (Addr.add 7289136#64 j) = nms.getD j 0)
    (hpg : ∀ x : Addr, 0x6f3000 ≤ x.toNat → x.toNat < 0x6f4000 → Foot F.data x)
    (hLD : ∀ i < E.N, ¬ (M (Addr.add (E.ptr i) 0) = 0x4c ∧ M (Addr.add (E.ptr i) 1) = 0x44 ∧
      M (Addr.add (E.ptr i) 2) = 0x5f)) :
    Ndi.NmOk E M F (BitVec.ofNat 64 (7289136 + o)) n := by
  obtain ⟨h3, hlt, hnz, hz, hL, hD, hU⟩ := nms_ok (o, n) hon
  have t0 : (BitVec.ofNat 64 (7289136 + o)).toNat = 7289136 + o := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have aa : ∀ k ≤ n, Addr.add (BitVec.ofNat 64 (7289136 + o)) k = Addr.add 7289136#64 (o + k) := by
    intro k hk
    apply BitVec.eq_of_toNat_eq
    rw [tg (b := 7289136 + o) (n := n + 1) (by omega) (by omega),
      tg (b := 7289136) (n := 99) (by omega) (by omega)]
    omega
  refine ⟨by omega, by rw [t0]; omega, fun k hk => ?_, ?_, fun x h1 h2 => ?_, fun i hi he => ?_⟩
  · rw [aa k (by omega), hM (o + k) (by omega)]
    exact hnz k hk
  · rw [aa n (Nat.le_refl _), hM (o + n) (by omega)]
    exact hz
  · rw [t0] at h1 h2
    exact hpg x (by omega) (by omega)
  · refine absurd ⟨?_, ?_, ?_⟩ (hLD i hi)
    · rw [he 0 (by omega), aa 0 (by omega), hM (o + 0) (by omega)]
      exact hL
    · rw [he 1 (by omega), aa 1 (by omega), hM (o + 1) (by omega)]
      exact hD
    · rw [he 2 (by omega), aa 2 (by omega), hM (o + 2) (by omega)]
      exact hU

/-- An environment of the launch with no string beginning with `LD_`, in bytes `M` that have its strings: `hLD` of
`nm_ok`. A string shorter than 3 has its 0 among the first three bytes. -/
theorem no_ld {K : Ctx} {E : Ndi.Ev} {M : Addr → Byte} (hK : K.Ok) (hN : E.N = K.N)
    (hp : ∀ i < K.N, E.ptr i = K.ptr i)
    (hS : ∀ i < K.N, ∀ k ≤ K.len i, M ((K.ptr i).add k) = K.V0 ((K.ptr i).add k))
    (noLD : ∀ i < K.N, ¬ (K.ez i 0 = 0x4c ∧ K.ez i 1 = 0x44 ∧ K.ez i 2 = 0x5f)) :
    ∀ i < E.N, ¬ (M (Addr.add (E.ptr i) 0) = 0x4c ∧ M (Addr.add (E.ptr i) 1) = 0x44 ∧
      M (Addr.add (E.ptr i) 2) = 0x5f) := by
  intro i hi ⟨h0, h1, h2⟩
  rw [hN] at hi
  rw [hp i hi] at h0 h1 h2
  have e : ∀ k ≤ K.len i, M (Addr.add (K.ptr i) k) = K.ez i k := fun k hk =>
    (hS i hi k hk).trans (hK.hstr i hi k hk)
  by_cases hl : 2 ≤ K.len i
  · exact noLD i hi ⟨(e 0 (by omega)).symm.trans h0, (e 1 (by omega)).symm.trans h1, (e 2 hl).symm.trans h2⟩
  · have hz := hK.hz i hi
    rcases (by omega : K.len i = 0 ∨ K.len i = 1) with h | h
    · rw [h] at hz
      rw [e 0 (by omega), hz] at h0
      exact absurd h0 (by decide)
    · rw [h] at hz
      rw [e 1 (by omega), hz] at h1
      exact absurd h1 (by decide)

end FV7z.Start
