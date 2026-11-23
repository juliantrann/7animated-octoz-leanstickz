import FV7z.Start.Ro
import FV7z.Start.Plat
/-!
# `"xeon_phi"` and `"haswell"` at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`init_cpu_features` may set `_dl_platform` to `"xeon_phi"` (`0x6ee608`) or `"haswell"` (`0x6ee611`), strings in
`.rodata`; `Ndi.lif_ok`'s `Pl` then asks that they end where they do (`nnz`, `nz`). Below `0x791ca0` the bytes in
`lif_ok`'s memory are the file's (`Start.ent_ro`).

- `xp_pin`, `hs_pin`: the two strings in the file.
- `v0_pls`: so in the launch bytes; `ent_pls`: in `lif_ok`'s bytes.
- `pl_ro`: `Pl` for either string, the pages of the string in the data footprint given.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tls (TlsMem)
open FV7z.StartB (GuardMem PtrMem)

/-- `"xeon_phi"` in the file. -/
theorem xp_pin : Exe.bytesAt V2606.zzs.blob 0x6ee608 9 = some [120, 101, 111, 110, 95, 112, 104, 105, 0] := by
  decide +kernel

/-- `"haswell"` in the file. -/
theorem hs_pin : Exe.bytesAt V2606.zzs.blob 0x6ee611 8 = some [104, 97, 115, 119, 101, 108, 108, 0] := by
  decide +kernel

theorem xp_add (k : Nat) : Addr.add 0x6ee608#64 k = BitVec.ofNat 64 (0x6ee608 + k) := by
  simp only [Addr.add]
  bv_omega

theorem hs_add (k : Nat) : Addr.add 0x6ee611#64 k = BitVec.ofNat 64 (0x6ee611 + k) := by
  simp only [Addr.add]
  bv_omega

/-- The two strings in the launch bytes. -/
theorem v0_pls {V : Addr → Byte} (hI : Img V) :
    (∀ k < 8, V (Addr.add 0x6ee608#64 k) ≠ 0) ∧ V (Addr.add 0x6ee608#64 8) = 0 ∧
      (∀ k < 7, V (Addr.add 0x6ee611#64 k) ≠ 0) ∧ V (Addr.add 0x6ee611#64 7) = 0 := by
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [xp_add, hI _ _ _ xp_pin (by decide) (by decide) k (by omega)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [xp_add, hI _ _ _ xp_pin (by decide) (by decide) 8 (by omega)]
    decide
  · rw [hs_add, hI _ _ _ hs_pin (by decide) (by decide) k (by omega)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hs_add, hI _ _ _ hs_pin (by decide) (by decide) 7 (by omega)]
    decide

/-- The two strings in the bytes at the `call` of `_dl_non_dynamic_init` after its pushes. -/
theorem ent_pls {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    let M := Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
    (∀ k < 8, M (Addr.add 0x6ee608#64 k) ≠ 0) ∧ M (Addr.add 0x6ee608#64 8) = 0 ∧
      (∀ k < 7, M (Addr.add 0x6ee611#64 k) ≠ 0) ∧ M (Addr.add 0x6ee611#64 7) = 0 := by
  intro M
  have t1 : (0x6ee608#64 : Addr).toNat = 0x6ee608 := rfl
  have t2 : (0x6ee611#64 : Addr).toNat = 0x6ee611 := rfl
  have e : ∀ {y : Addr} {k : Nat}, (y.toNat = 0x6ee608 ∨ y.toNat = 0x6ee611) → k < 9 →
      M (Addr.add y k) = K.V0 (Addr.add y k) := by
    intro y k hy hk
    have t : (Addr.add y k).toNat = y.toNat + k := toNat_add_of_fits (n := 9) hk (by omega)
    exact ent_ro hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega) (hD _ (by omega) (by omega))
  have c := v0_pls hI
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [e (k := k) (.inl t1) (by omega)]
    exact c.1 k hk
  · rw [e (k := 8) (.inl t1) (by omega)]
    exact c.2.1
  · rw [e (k := k) (.inr t2) (by omega)]
    exact c.2.2.1 k hk
  · rw [e (k := 7) (.inr t2) (by omega)]
    exact c.2.2.2

/-- `Pl` for `"xeon_phi"` or `"haswell"`: `_dl_platform` points to it, it ends where it does, and its pages are in
the data footprint. -/
theorem pl_ro {M : Addr → Byte} {F : Footprint} {sp p : Addr} {n : Nat}
    (hpn : p = 0x6ee608#64 ∧ n = 8 ∨ p = 0x6ee611#64 ∧ n = 7) (hp : rdq(M, 8029512#64) = p)
    (hs : (∀ k < 8, M (Addr.add 0x6ee608#64 k) ≠ 0) ∧ M (Addr.add 0x6ee608#64 8) = 0 ∧
      (∀ k < 7, M (Addr.add 0x6ee611#64 k) ≠ 0) ∧ M (Addr.add 0x6ee611#64 7) = 0)
    (hpg : ∀ x : Addr, 0x6ee000 ≤ x.toNat → x.toNat < 0x6ef000 → Foot F.data x) : Ndi.Pl M F sp p n := by
  have t1 : (0x6ee608#64 : Addr).toNat = 0x6ee608 := rfl
  have t2 : (0x6ee611#64 : Addr).toNat = 0x6ee611 := rfl
  obtain ⟨s1, s2, s3, s4⟩ := hs
  rcases hpn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hp, .inr (by rw [t1]; omega), by rw [t1]; omega, by omega, s1, s2,
      fun x h1 h2 => hpg x (by rw [t1] at h1; omega) (by rw [t1] at h2; omega)⟩
  · exact ⟨hp, .inr (by rw [t2]; omega), by rw [t2]; omega, by omega, s3, s4,
      fun x h1 h2 => hpg x (by rw [t2] at h1; omega) (by rw [t2] at h2; omega)⟩

end FV7z.Start
