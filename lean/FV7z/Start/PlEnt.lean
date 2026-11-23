import FV7z.Start.Keep
import FV7z.Start.PlStr
import FV7z.Start.PlAt
import FV7z.Start.LoadedAt
/-!
# The `AT_PLATFORM` string at `_dl_non_dynamic_init` (PLAN.md G3, startup)

The platform string `execve` puts on the stack lies above `__libc_start_main`'s frame and above the TLS block, so no
store of the start code lands on it: in `lif_ok`'s bytes it is the launch's (`ent_keep_hi`, `ptr_hi`).

- `ent_hi`: a byte of the stack above the frame, the TLS block and `lif_ok`'s stack is there the launch byte.
- `ent_pstr`: each byte of the string in `lif_ok`'s bytes, from the launch bytes.
- `pl_at`: `Pl` for it, when `_dl_platform` points to it.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem pstr_nz : ∀ k < 6, platformString.getD k 0 ≠ 0 := by decide
theorem pstr_z : platformString.getD 6 0 = 0 := rfl
theorem pstr_len : platformString.length = 7 := rfl

/-- A byte of the stack above `__libc_start_main`'s frame, the TLS block and `lif_ok`'s stack is, in `lif_ok`'s
bytes, the launch byte: the strings `execve` puts there. -/
theorem ent_hi {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {a : Addr} (hbp : K.bp.toNat + 376 ≤ a.toNat) (htl : b.toNat + 8192 ≤ a.toNat)
    (hr : g.rsp.toNat + 8 ≤ a.toNat) (hr0 : 32 ≤ g.rsp.toNat) (hsp : sp.toNat + 120 ≤ a.toNat) (hDa : D a) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a =
      K.V0 a :=
  (ent_keep_hi hr hr0 hsp (by omega)).trans (ptr_hi hM hb hb' hW hbp htl hDa)

/-- The platform string in `lif_ok`'s bytes. -/
theorem ent_pstr {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {P : Nat} (hP : P + 7 ≤ 2 ^ 64) (hbp : K.bp.toNat + 376 ≤ P)
    (htl : b.toNat + 8192 ≤ P) (hr : g.rsp.toNat + 8 ≤ P) (hr0 : 32 ≤ g.rsp.toNat) (hsp : sp.toNat + 120 ≤ P)
    (hD : ∀ k < 7, D (BitVec.ofNat 64 (P + k)))
    (hV0 : ∀ k < platformString.length, K.V0 (BitVec.ofNat 64 (P + k)) = platformString.getD k 0)
    {k : Nat} (hk : k < 7) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
        (BitVec.ofNat 64 (P + k)) = platformString.getD k 0 := by
  have ht : (BitVec.ofNat 64 (P + k)).toNat = P + k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have e := ent_hi (g := g) (gY := gY) (ra := ra) (ra₀ := ra₀) (sp := sp) hM hb hb' hW
    (a := BitVec.ofNat 64 (P + k)) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) hr0
    (by rw [ht]; omega) (hD k hk)
  rw [e, hV0 k (by rw [pstr_len]; exact hk)]

/-- `Pl` for the platform string: `_dl_platform` points to it, it is above `sp`, and its pages are in the data
footprint. -/
theorem pl_at {M : Addr → Byte} {F : Footprint} {sp : Addr} {P : Nat} (hP : P + 7 ≤ 2 ^ 64)
    (hp : rdq(M, 8029512#64) = BitVec.ofNat 64 P) (hsp : sp.toNat ≤ P)
    (hs : ∀ k < 7, M (BitVec.ofNat 64 (P + k)) = platformString.getD k 0)
    (hpg : ∀ x : Addr, P / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (P + 6) / 4096 → Foot F.data x) :
    Ndi.Pl M F sp (BitVec.ofNat 64 P) 6 := by
  have ht : (BitVec.ofNat 64 P).toNat = P := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hp, .inl (by rw [ht]; exact hsp), by rw [ht]; omega, by omega, fun k hk => ?_, ?_,
    fun x h1 h2 => hpg x (by rw [ht] at h1; exact h1) (by rw [ht] at h2; exact h2)⟩
  · rw [add_ofNat, hs k (by omega)]
    exact pstr_nz k hk
  · rw [add_ofNat, hs 6 (by omega)]
    exact pstr_z

end FV7z.Start
