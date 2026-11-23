import FV7z.Start.La
import FV7z.Start.Ent
import FV7z.Ndi.Head
/-!
# Read-only image bytes at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` reads bytes of the image below `0x791ca0` (`.rodata`, `.data.rel.ro`): the strings `"x86_64"`
(`0x6f3879`, `hx1`, `hx1z`) and `"avx512_1"` (`0x6f3882`, `hx2`, `hx2z`) of `_dl_important_hwcaps`, and more. No
variable the start code stores to lies there (`globals`, `d3`, `TlsVar`, `PimVar`, `CpuVar` are all above), and
`__libc_init_first` and the prologue of `_dl_non_dynamic_init` store only to the stack and to globals above.

- `ptr_ro`: a byte in `[0x400000, 0x791ca0)` is, at `0x613434`, the launch byte (`K.V0`).
- `ent_ro`: the same byte under `fV` (the five pushes of `_dl_non_dynamic_init`) of the bytes at the `call` of
  `_dl_non_dynamic_init` (`Lif.LifMem`, the return addresses).
- `x1_pin`, `x2_pin`, `v0_x`, `ent_x`: `hx1`, `hx1z`, `hx2`, `hx2z` of `lif_ok`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar)
open FV7z.StartB (GuardMem PtrMem)

/-- A byte of the image below `0x791ca0` is, at the call of `__libc_init_first`, the byte of the launch. -/
theorem ptr_ro {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a) {a : Addr}
    (h1 : 0x400000 ≤ a.toNat) (h2 : a.toNat < 0x791ca0) (hDa : D a) : W a = K.V0 a := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hi0 := hK.himg
  have hd : ¬ Foot (d3 ++ AuxInit.globals) a :=
    not_dg (lo := 0x400000) (hi := 0x791ca0) (by decide) h1 h2
  rw [hW a (.inl hDa) ?_ ?_]
  · unfold PtrMem
    rw [Vst_out]
    · exact ver_img ver hK hM.same hb hb' h1 (by omega) (by unfold TlsVar; omega) (by omega) hd
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 Junk2 Junk at hj
    rcases hj with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · unfold CpuVar at h
      omega
  · unfold Pim.PimVar
    omega

/-- The same byte in `lif_ok`'s bytes: under the pushes of `_dl_non_dynamic_init` (`fV`), the return addresses and
`Lif.LifMem`. -/
theorem ent_ro {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) {a : Addr} (h1 : 0x400000 ≤ a.toNat) (h2 : a.toNat < 0x791ca0) (hDa : D a) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a =
      K.V0 a := by
  unfold Ndi.fV Lif.LifMem Lif.LifStk
  repeat rw [Vst_out]
  · exact ptr_ro hK hM hb hb' hW h1 h2 hDa
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- `"x86_64"` in the file. -/
theorem x1_pin : Exe.bytesAt V2606.zzs.blob 0x6f3879 7 = some [0x78, 0x38, 0x36, 0x5f, 0x36, 0x34, 0] := by
  decide +kernel

/-- `"avx512_1"` in the file. -/
theorem x2_pin : Exe.bytesAt V2606.zzs.blob 0x6f3882 9 =
    some [0x61, 0x76, 0x78, 0x35, 0x31, 0x32, 0x5f, 0x31, 0] := by
  decide +kernel

theorem x1_add (k : Nat) : Addr.add 7288953#64 k = BitVec.ofNat 64 (0x6f3879 + k) := by
  simp only [Addr.add]
  bv_omega

theorem x2_add (k : Nat) : Addr.add 7288962#64 k = BitVec.ofNat 64 (0x6f3882 + k) := by
  simp only [Addr.add]
  bv_omega

/-- The two strings in the launch bytes. -/
theorem v0_x {V : Addr → Byte} (hI : Img V) :
    (∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) ∧ V (Addr.add 7288953#64 6) = 0 ∧
      (∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) ∧ V (Addr.add 7288962#64 8) = 0 := by
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [x1_add, hI _ _ _ x1_pin (by decide) (by decide) k (by omega)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [x1_add, hI _ _ _ x1_pin (by decide) (by decide) 6 (by omega)]
    decide
  · rw [x2_add, hI _ _ _ x2_pin (by decide) (by decide) k (by omega)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [x2_add, hI _ _ _ x2_pin (by decide) (by decide) 8 (by omega)]
    decide

/-- `hx1`, `hx1z`, `hx2`, `hx2z` of `lif_ok`, in the bytes at the `call` of `_dl_non_dynamic_init` after its
pushes. -/
theorem ent_x {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    let M := Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
    (∀ k < 6, M (Addr.add 7288953#64 k) ≠ 0) ∧ M (Addr.add 7288953#64 6) = 0 ∧
      (∀ k < 8, M (Addr.add 7288962#64 k) ≠ 0) ∧ M (Addr.add 7288962#64 8) = 0 := by
  intro M
  have t1 : (7288953#64 : Addr).toNat = 7288953 := rfl
  have t2 : (7288962#64 : Addr).toNat = 7288962 := rfl
  have e : ∀ {y : Addr} {k : Nat}, (y.toNat = 7288953 ∨ y.toNat = 7288962) → k < 9 →
      M (Addr.add y k) = K.V0 (Addr.add y k) := by
    intro y k hy hk
    have t : (Addr.add y k).toNat = y.toNat + k := toNat_add_of_fits (n := 9) hk (by omega)
    exact ent_ro hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega) (hD _ (by omega) (by omega))
  have c := v0_x hI
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [e (k := k) (.inl t1) (by omega)]
    exact c.1 k hk
  · rw [e (k := 6) (.inl t1) (by omega)]
    exact c.2.1
  · rw [e (k := k) (.inr t2) (by omega)]
    exact c.2.2.1 k hk
  · rw [e (k := 8) (.inr t2) (by omega)]
    exact c.2.2.2

end FV7z.Start
