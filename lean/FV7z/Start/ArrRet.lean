import FV7z.Start.SecRet
import FV7z.Csu.Holds
/-!
# `.preinit_array` and `.init_array` after the return of `__libc_init_first` (PLAN.md G3, startup)

`__libc_csu_init` calls the function of `.preinit_array` (`0x777798`), `_init` and the 102 of `.init_array`
(`0x7777a0`); `Csu.csu_ok` asks for the words of the two arrays (`hpre`, `harr`). They are in the RELRO pages, so no
layer before stores to them: at `0x613439` they are the file's.

- `arrB`, `arr_pin`: the 824 bytes of the two arrays in the file.
- `csuTg`: the 104 functions: the one of `.preinit_array`, `_init` (`0x401000`), the 102 of `.init_array`.
- `arr_tg`: bytes that are the file's there give `hpre` and `harr` for `csuTg`.
- `low_ret`: a byte of the image below `0x791cb8` at `0x613439` is the byte `W` at `0x613434`.
- `RetAt.arr`: a byte of the arrays at `0x613439` is the launch image's.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tls (TlsVar)

/-- The 824 bytes of `.preinit_array` (one word) and `.init_array` (102 words) at `0x777798` in the file. -/
def arrB : List Byte :=
  [80, 252, 95, 0, 0, 0, 0, 0, 64, 212, 65, 0, 0, 0, 0, 0, 64, 193, 65, 0, 0, 0, 0, 0, 80, 193, 65, 0, 0, 0, 0, 0, 96,
    193, 65, 0, 0, 0, 0, 0, 112, 193, 65, 0, 0, 0, 0, 0, 128, 193, 65, 0, 0, 0, 0, 0, 144, 193, 65, 0, 0, 0, 0, 0,
    160, 193, 65, 0, 0, 0, 0, 0, 176, 193, 65, 0, 0, 0, 0, 0, 192, 193, 65, 0, 0, 0, 0, 0, 208, 193, 65, 0, 0, 0, 0,
    0, 224, 193, 65, 0, 0, 0, 0, 0, 16, 194, 65, 0, 0, 0, 0, 0, 32, 194, 65, 0, 0, 0, 0, 0, 48, 194, 65, 0, 0, 0, 0,
    0, 64, 194, 65, 0, 0, 0, 0, 0, 80, 194, 65, 0, 0, 0, 0, 0, 96, 194, 65, 0, 0, 0, 0, 0, 112, 194, 65, 0, 0, 0, 0,
    0, 128, 194, 65, 0, 0, 0, 0, 0, 144, 194, 65, 0, 0, 0, 0, 0, 160, 194, 65, 0, 0, 0, 0, 0, 176, 194, 65, 0, 0, 0,
    0, 0, 192, 194, 65, 0, 0, 0, 0, 0, 208, 194, 65, 0, 0, 0, 0, 0, 224, 194, 65, 0, 0, 0, 0, 0, 240, 194, 65, 0, 0,
    0, 0, 0, 0, 195, 65, 0, 0, 0, 0, 0, 16, 195, 65, 0, 0, 0, 0, 0, 32, 195, 65, 0, 0, 0, 0, 0, 48, 195, 65, 0, 0, 0,
    0, 0, 64, 195, 65, 0, 0, 0, 0, 0, 80, 195, 65, 0, 0, 0, 0, 0, 96, 195, 65, 0, 0, 0, 0, 0, 112, 195, 65, 0, 0, 0,
    0, 0, 128, 195, 65, 0, 0, 0, 0, 0, 208, 195, 65, 0, 0, 0, 0, 0, 0, 196, 65, 0, 0, 0, 0, 0, 16, 196, 65, 0, 0, 0,
    0, 0, 32, 196, 65, 0, 0, 0, 0, 0, 48, 196, 65, 0, 0, 0, 0, 0, 64, 196, 65, 0, 0, 0, 0, 0, 80, 196, 65, 0, 0, 0, 0,
    0, 128, 196, 65, 0, 0, 0, 0, 0, 144, 196, 65, 0, 0, 0, 0, 0, 160, 196, 65, 0, 0, 0, 0, 0, 176, 196, 65, 0, 0, 0,
    0, 0, 192, 196, 65, 0, 0, 0, 0, 0, 208, 196, 65, 0, 0, 0, 0, 0, 224, 196, 65, 0, 0, 0, 0, 0, 16, 197, 65, 0, 0, 0,
    0, 0, 64, 197, 65, 0, 0, 0, 0, 0, 80, 197, 65, 0, 0, 0, 0, 0, 96, 197, 65, 0, 0, 0, 0, 0, 176, 197, 65, 0, 0, 0,
    0, 0, 192, 197, 65, 0, 0, 0, 0, 0, 208, 197, 65, 0, 0, 0, 0, 0, 224, 197, 65, 0, 0, 0, 0, 0, 240, 197, 65, 0, 0,
    0, 0, 0, 0, 198, 65, 0, 0, 0, 0, 0, 32, 198, 65, 0, 0, 0, 0, 0, 48, 198, 65, 0, 0, 0, 0, 0, 96, 198, 65, 0, 0, 0,
    0, 0, 112, 198, 65, 0, 0, 0, 0, 0, 128, 198, 65, 0, 0, 0, 0, 0, 144, 198, 65, 0, 0, 0, 0, 0, 192, 198, 65, 0, 0,
    0, 0, 0, 208, 198, 65, 0, 0, 0, 0, 0, 224, 198, 65, 0, 0, 0, 0, 0, 48, 199, 65, 0, 0, 0, 0, 0, 64, 199, 65, 0, 0,
    0, 0, 0, 80, 199, 65, 0, 0, 0, 0, 0, 96, 199, 65, 0, 0, 0, 0, 0, 112, 199, 65, 0, 0, 0, 0, 0, 208, 199, 65, 0, 0,
    0, 0, 0, 48, 200, 65, 0, 0, 0, 0, 0, 96, 200, 65, 0, 0, 0, 0, 0, 112, 200, 65, 0, 0, 0, 0, 0, 128, 200, 65, 0, 0,
    0, 0, 0, 144, 200, 65, 0, 0, 0, 0, 0, 160, 200, 65, 0, 0, 0, 0, 0, 112, 201, 65, 0, 0, 0, 0, 0, 128, 201, 65, 0,
    0, 0, 0, 0, 144, 201, 65, 0, 0, 0, 0, 0, 160, 201, 65, 0, 0, 0, 0, 0, 176, 201, 65, 0, 0, 0, 0, 0, 160, 202, 65,
    0, 0, 0, 0, 0, 176, 202, 65, 0, 0, 0, 0, 0, 240, 202, 65, 0, 0, 0, 0, 0, 96, 203, 65, 0, 0, 0, 0, 0, 112, 203, 65,
    0, 0, 0, 0, 0, 128, 203, 65, 0, 0, 0, 0, 0, 144, 203, 65, 0, 0, 0, 0, 0, 208, 203, 65, 0, 0, 0, 0, 0, 48, 204, 65,
    0, 0, 0, 0, 0, 80, 204, 65, 0, 0, 0, 0, 0, 176, 204, 65, 0, 0, 0, 0, 0, 240, 204, 65, 0, 0, 0, 0, 0, 80, 205, 65,
    0, 0, 0, 0, 0, 48, 206, 65, 0, 0, 0, 0, 0, 112, 206, 65, 0, 0, 0, 0, 0, 240, 206, 65, 0, 0, 0, 0, 0]

theorem arr_pin : Exe.bytesAt V2606.zzs.blob 0x777798 824 = some arrB := by
  decide +kernel

theorem arrB_length : arrB.length = 824 := rfl

/-- The functions `__libc_csu_init` calls, in order: the word of `.preinit_array`, `_init`, the 102 words of
`.init_array`. -/
def csuTg (m : Nat) : Addr :=
  if m = 1 then 0x401000#64 else ofBytesLE 64 ((arrB.drop (8 * (m - 1))).take 8)

theorem csuTg_one : csuTg 1 = 0x401000#64 := rfl

/-- Bytes that are the file's at the two arrays give `Csu.csu_ok`'s `hpre` and `harr` for `csuTg`. -/
theorem arr_tg {V V0 : Addr → Byte} (hI : Img V0)
    (hV : ∀ a : Addr, 0x777798 ≤ a.toNat ∧ a.toNat < 0x777ad0 → V a = V0 a) :
    rdq(V, 7829400#64) = csuTg 0 ∧ ∀ k < 102, rdq(V, BitVec.ofNat 64 (7829408 + 8 * k)) = csuTg (k + 2) := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Csu.rd_in hV (by decide) (by decide) (by decide)]
    show ofBytesLE 64 (List.map V0 (byteAddrs (BitVec.ofNat 64 (0x777798 + 0)) 8)) = _
    rw [hI.map arr_pin arrB_length (by decide) (by decide) (off := 0) (m := 8) (by decide)]
    rfl
  · have t : (BitVec.ofNat 64 (7829408 + 8 * k) : Addr).toNat = 7829408 + 8 * k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [Csu.rd_in hV (by rw [t]; omega) (by rw [t]; omega) (by rw [t]; omega)]
    have e : 7829408 + 8 * k = 0x777798 + 8 * (k + 1) := by omega
    rw [e, hI.map arr_pin arrB_length (by decide) (by decide) (off := 8 * (k + 1)) (m := 8) (by omega)]
    unfold csuTg
    rw [if_neg (show ¬ (k + 2 = 1) by omega), show k + 2 - 1 = k + 1 by omega]

/-- At the return of `__libc_init_first` to `0x613439`, a byte of the image below `0x791cb8` is the byte `W` at
`0x613434`. -/
theorem low_ret {W W₂ : Addr → Byte} {Z : State} {b fsb fb a0 s x : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
    (h1 : x.toNat < 7937208) (hN : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) b fsb W₂)
    (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat) (hsp : 8032256 + 72 ≤ (lifSp Z).toNat)
    (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64) (he : 0x7a9000 + 32 ≤ (entG Z).rsp.toNat)
    (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64) (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat)
    (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  have ha : Away x := by unfold Away; omega
  rw [ct_away ha hg hfb hfb', Ndi.ndi_glob_w hE hU hL (by omega) (by omega) (by omega) hs (.inl h1)]
  exact lifW_away ha he he'

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- A byte of `.preinit_array` or `.init_array` at `0x613439` is the launch image's. -/
theorem RetAt.arr {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} {D : Addr → Prop} (h : RetAt W W₂ Z B g)
    (hK : K.Ok) (hM : MB K V) (hW : PtrW K W V B ver D) {x : Addr} (hx : 0x777798 ≤ x.toNat ∧ x.toNat < 0x777ad0)
    (hD : D x) : Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x = K.V0 x := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  rw [low_ret (by omega) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega) (by omega)
    (by omega)]
  exact ptr_keep hK hM h.hb h.hb' hW (by omega) (by omega) hD (by unfold TlsVar; omega) (by omega)
    (not_dg (lo := 0x777798) (hi := 0x777ad0) (by decide) hx.1 hx.2) (by unfold CpuVar; omega)
    (by unfold Pim.PimVar; omega)

end FV7z.Start
