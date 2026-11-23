import FV7z.Start.Ro
import FV7z.Ndi.Loop
import FV7z.Ndi.Mv
import FV7z.Ipa.Vc
/-!
# Program headers and the search path table at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` reads the 8 program headers at `0x400040` (`hph : Ph …`, the loop of `_dl_non_dynamic_init`) and the
table of `_dl_init_paths`' system directories at `0x705dc8` (`hlenV`: lengths 26, 5, 9; `hslV`: each starts with
`/`). Both lie in the image below `0x791ca0`, so `Start.ent_ro` gives them from the file.

- `img_rd`: `n` bytes of the file in the launch bytes.
- `ph_ro`: `Ph` of bytes that agree on `[0x400000, 0x791ca0)`.
- `v0_ph`, `v0_len`, `v0_sl`: the three facts in the launch bytes (pins of the file).
- `ent_rdn`, `ent_ph`, `ent_len`, `ent_sl`: `hph`, `hlenV`, `hslV` in `lif_ok`'s bytes.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tls (TlsMem)
open FV7z.StartB (GuardMem PtrMem)

/-- `n` bytes of the file, read in the launch bytes. -/
theorem img_rd {V : Addr → Byte} (hI : Img V) {a n : Nat} {bs : List Byte}
    (hp : Exe.bytesAt V2606.zzs.blob a n = some bs) (hl : bs.length = n) (hlo : 0x400000 ≤ a)
    (hhi : a + n ≤ 0x7a9000) : List.map V (byteAddrs (BitVec.ofNat 64 a) n) = bs := by
  have h := hI.map hp hl hlo hhi (off := 0) (m := n) (by omega)
  rw [Nat.add_zero, List.drop_zero, List.take_of_length_le (by omega)] at h
  exact h

/-- `Ph` on bytes that agree on the image below `0x791ca0`. -/
theorem ph_ro {V V' : Addr → Byte} (h : Ndi.Ph V)
    (hs : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → V' a = V a) : Ndi.Ph V' := by
  have R : ∀ x n : Nat, 0x400000 ≤ x → x + n ≤ 0x791ca0 →
      List.map V' (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h1 h2 => Ndi.rd_of (by omega) fun a a1 a2 => hs a (by omega) (by omega)
  exact
    { t0 := by rw [R 4194368 4 (by omega) (by omega)]; exact h.t0
      t1 := by rw [R 4194424 4 (by omega) (by omega)]; exact h.t1
      t2 := by rw [R 4194480 4 (by omega) (by omega)]; exact h.t2
      t3 := by rw [R 4194536 4 (by omega) (by omega)]; exact h.t3
      t4 := by rw [R 4194592 4 (by omega) (by omega)]; exact h.t4
      t5 := by rw [R 4194648 4 (by omega) (by omega)]; exact h.t5
      t6 := by rw [R 4194704 4 (by omega) (by omega)]; exact h.t6
      f6 := by rw [R 4194708 4 (by omega) (by omega)]; exact h.f6
      t7 := by rw [R 4194760 4 (by omega) (by omega)]; exact h.t7
      a7 := by rw [R 4194776 8 (by omega) (by omega)]; exact h.a7
      m7 := by rw [R 4194800 8 (by omega) (by omega)]; exact h.m7 }

theorem p_t0 : Exe.bytesAt V2606.zzs.blob 4194368 4 = some [1, 0, 0, 0] := by decide +kernel
theorem p_t1 : Exe.bytesAt V2606.zzs.blob 4194424 4 = some [1, 0, 0, 0] := by decide +kernel
theorem p_t2 : Exe.bytesAt V2606.zzs.blob 4194480 4 = some [1, 0, 0, 0] := by decide +kernel
theorem p_t3 : Exe.bytesAt V2606.zzs.blob 4194536 4 = some [1, 0, 0, 0] := by decide +kernel
theorem p_t4 : Exe.bytesAt V2606.zzs.blob 4194592 4 = some [4, 0, 0, 0] := by decide +kernel
theorem p_t5 : Exe.bytesAt V2606.zzs.blob 4194648 4 = some [7, 0, 0, 0] := by decide +kernel
theorem p_t6 : Exe.bytesAt V2606.zzs.blob 4194704 4 = some [0x51, 0xe5, 0x74, 0x64] := by decide +kernel
theorem p_f6 : Exe.bytesAt V2606.zzs.blob 4194708 4 = some [6, 0, 0, 0] := by decide +kernel
theorem p_t7 : Exe.bytesAt V2606.zzs.blob 4194760 4 = some [0x52, 0xe5, 0x74, 0x64] := by decide +kernel
theorem p_a7 : Exe.bytesAt V2606.zzs.blob 4194776 8 = some [0x70, 0x77, 0x77, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_m7 : Exe.bytesAt V2606.zzs.blob 4194800 8 = some [0x90, 0xa8, 1, 0, 0, 0, 0, 0] := by decide +kernel

/-- The program headers in the launch bytes. -/
theorem v0_ph {V : Addr → Byte} (hI : Img V) : Ndi.Ph V where
  t0 := by rw [img_rd hI p_t0 rfl (by omega) (by omega)]; rfl
  t1 := by rw [img_rd hI p_t1 rfl (by omega) (by omega)]; rfl
  t2 := by rw [img_rd hI p_t2 rfl (by omega) (by omega)]; rfl
  t3 := by rw [img_rd hI p_t3 rfl (by omega) (by omega)]; rfl
  t4 := by rw [img_rd hI p_t4 rfl (by omega) (by omega)]; rfl
  t5 := by rw [img_rd hI p_t5 rfl (by omega) (by omega)]; rfl
  t6 := by rw [img_rd hI p_t6 rfl (by omega) (by omega)]; rfl
  f6 := by rw [img_rd hI p_f6 rfl (by omega) (by omega)]; rfl
  t7 := by rw [img_rd hI p_t7 rfl (by omega) (by omega)]; rfl
  a7 := by rw [img_rd hI p_a7 rfl (by omega) (by omega)]; rfl
  m7 := by rw [img_rd hI p_m7 rfl (by omega) (by omega)]; rfl

theorem p_l0 : Exe.bytesAt V2606.zzs.blob 7364040 8 = some [26, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_l1 : Exe.bytesAt V2606.zzs.blob 7364048 8 = some [5, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_l2 : Exe.bytesAt V2606.zzs.blob 7364056 8 = some [9, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_s0 : Exe.bytesAt V2606.zzs.blob 7364087 1 = some [0x2f] := by decide +kernel
theorem p_s1 : Exe.bytesAt V2606.zzs.blob 7364114 1 = some [0x2f] := by decide +kernel
theorem p_s2 : Exe.bytesAt V2606.zzs.blob 7364120 1 = some [0x2f] := by decide +kernel

/-- The lengths of the three system directories in the launch bytes. -/
theorem v0_len {V : Addr → Byte} (hI : Img V) :
    ∀ k < 3, rdq(V, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k) := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 7364040) 8)) = _
    rw [img_rd hI p_l0 rfl (by omega) (by omega)]; rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 7364048) 8)) = _
    rw [img_rd hI p_l1 rfl (by omega) (by omega)]; rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 7364056) 8)) = _
    rw [img_rd hI p_l2 rfl (by omega) (by omega)]; rfl

/-- Each system directory starts with `/` in the launch bytes. -/
theorem v0_sl {V : Addr → Byte} (hI : Img V) :
    ∀ k < 3, ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8 := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [show Ipa.sA 0 = 7364087 from rfl, img_rd hI p_s0 rfl (by omega) (by omega)]; rfl
  · rw [show Ipa.sA 1 = 7364114 from rfl, img_rd hI p_s1 rfl (by omega) (by omega)]; rfl
  · rw [show Ipa.sA 2 = 7364120 from rfl, img_rd hI p_s2 rfl (by omega) (by omega)]; rfl

section E
variable {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
  {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
  (hb' : b.toNat + 8192 ≤ 2 ^ 63)
  (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
    ¬ Pim.PimVar (b + 2176#64) a →
    W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
  (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
  (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
  (hsn : sp.toNat + 120 ≤ 2 ^ 64)
include hK hM hb hb' hW hD hr hr' hsp hsn

/-- A byte of the image below `0x791ca0` in `lif_ok`'s bytes. -/
theorem ent_b (a : Addr) (h1 : 0x400000 ≤ a.toNat) (h2 : a.toNat < 0x791ca0) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a =
      K.V0 a :=
  ent_ro hK hM hb hb' hW hr hr' hsp hsn h1 h2 (hD a h1 h2)

/-- `n` bytes of the image below `0x791ca0` in `lif_ok`'s bytes. -/
theorem ent_rdn {x n : Nat} (h1 : 0x400000 ≤ x) (h2 : x + n ≤ 0x791ca0) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (byteAddrs (BitVec.ofNat 64 x) n) = List.map K.V0 (byteAddrs (BitVec.ofNat 64 x) n) :=
  Ndi.rd_of (by omega) fun a a1 a2 => ent_b hK hM hb hb' hW hD hr hr' hsp hsn a (by omega) (by omega)

include hI in
/-- `hph` of `lif_ok`. -/
theorem ent_ph :
    Ndi.Ph (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY) :=
  ph_ro (v0_ph hI) fun a h1 h2 => ent_b hK hM hb hb' hW hD hr hr' hsp hsn a h1 h2

include hI in
/-- `hlenV` of `lif_ok`. -/
theorem ent_len : ∀ k < 3,
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k) := by
  intro k hk
  rw [ent_rdn hK hM hb hb' hW hD hr hr' hsp hsn (x := 7364040 + 8 * k) (n := 8) (by omega) (by omega)]
  exact v0_len hI k hk

include hI in
/-- `hslV` of `lif_ok`. -/
theorem ent_sl : ∀ k < 3,
    ofBytesLE 8 (List.map
      (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8 := by
  intro k hk
  have hs : 7364087 ≤ Ipa.sA k ∧ Ipa.sA k ≤ 7364120 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  rw [ent_rdn hK hM hb hb' hW hD hr hr' hsp hsn (x := Ipa.sA k) (n := 1) (by omega) (by omega)]
  exact v0_sl hI k hk

end E

end FV7z.Start
