import FV7z.Start.Lw
import FV7z.Start.Tg
import FV7z.Lif.Ok
/-!
# `malloc`'s state at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `Mal.MPre` of the bytes at the entry of `_dl_get_origin` (`hpre`): `malloc`'s state in
`.data` as in the file (`main_arena`, `mp_`, the hook), the twelve `glibc.malloc.*` tunables unset, the thread's
`tcache` and `multiple_threads` 0, `__curbrk` the break and the rest of the break's page 0.

- `MAt`, `ent_m`: bytes of `malloc`'s state in `.data` and of `.bss` below `__environ` are, in `lif_ok`'s bytes,
  those of the launch.
- `p_*`, `tu*`: the words and the tunables' entries in the file; `ent_tun`: the tunables in `lif_ok`'s bytes.
- `TZ`, `ent_tz`, `ent_tzr`: the bytes of the TLS block that no store of the start code reaches are 0.
- `ent_cb`: `__curbrk` is `b + 4544`; `ent_ml`: the word at `0x7939c0` is 0 (`Lif.LifMem`).
- `ent_mpre`: `MPre` of `lif_ok`'s bytes; `ent_mpreN`: of those at the entry of `_dl_get_origin` (`Ndi.nV_fV`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out rd_Vst rd_Vst_self)
open FV7z.Tls (TlsMem TlsVar WD WC T4 T3 T2 rd_ext)
open FV7z.StartB (GuardMem PtrMem)
open FV7z.Brk (curbrk)
open FV7z.Mal (MPre)

/-- Bytes `[x, x + n)` of `malloc`'s state in `.data` (below `_dl_pagesize`'s neighbours), or of `.bss` between the
`pthread` variables and `__environ`: no store of the start code reaches them. -/
def MAt (x n : Nat) : Prop := 0x7922b8 ≤ x ∧ x + n ≤ 0x7933cc ∨ 0x7a3f78 ≤ x ∧ x + n ≤ 0x7a4798

/-- Such bytes in `lif_ok`'s bytes are those of the launch. -/
theorem ent_m {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {x n : Nat} (hK : K.Ok) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) (hx : MAt x n)
    (hD : ∀ i < n, D (Addr.add (BitVec.ofNat 64 x) i)) (hr : x + n + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + n ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (byteAddrs (BitVec.ofNat 64 x) n) = List.map K.V0 (byteAddrs (BitVec.ofNat 64 x) n) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hd : ∀ a : Addr, x ≤ a.toNat → a.toNat < x + n → ¬ Foot (d3 ++ AuxInit.globals) a := fun a h1 h2 => by
    unfold MAt at hx
    rcases hx with h | h
    · exact not_dg (lo := 0x7922b8) (hi := 0x7933cc) (by decide) (by omega) (by omega)
    · exact not_dg (lo := 0x7a3f78) (hi := 0x7a4798) (by decide) (by omega) (by omega)
  have hx' := hx
  unfold MAt at hx'
  refine rd_ext _ n fun i hi => ?_
  have t : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := tg hi (by omega)
  rw [ent_keep (a := Addr.add (BitVec.ofNat 64 x) i) (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩]
  exact ptr_keep hK hM hb hb' hW (by omega) (by omega) (hD i hi) (by unfold TlsVar; omega) (by omega)
    (hd _ (by omega) (by omega)) (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)

/-! The words of `malloc`'s state in the file. -/
theorem p_hook : Exe.bytesAt V2606.zzs.blob 7940656 8 = some [0xa0, 0x2b, 0x63, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_mi : Exe.bytesAt V2606.zzs.blob 7940484 4 = some [0xff, 0xff, 0xff, 0xff] := by decide +kernel
theorem p_lk : Exe.bytesAt V2606.zzs.blob 7940672 4 = some [0, 0, 0, 0] := by decide +kernel
theorem p_fl : Exe.bytesAt V2606.zzs.blob 7940676 1 = some [0] := by decide +kernel
theorem p_fz : Exe.bytesAt V2606.zzs.blob 7940688 56 = some (List.replicate 56 0) := by decide +kernel
theorem p_tb : Exe.bytesAt V2606.zzs.blob 7940592 8 = some [64, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_m0 : Exe.bytesAt V2606.zzs.blob 7942816 4 = some [0, 0, 0, 0] := by decide +kernel
theorem p_m1 : Exe.bytesAt V2606.zzs.blob 7942820 4 = some [0, 0, 0, 0] := by decide +kernel
theorem p_m2 : Exe.bytesAt V2606.zzs.blob 7942824 4 = some [0, 0, 0, 0] := by decide +kernel
theorem p_m3 : Exe.bytesAt V2606.zzs.blob 7942828 4 = some [0, 0, 0, 0] := by decide +kernel
theorem p_thr : Exe.bytesAt V2606.zzs.blob 7940528 8 = some [0, 0, 2, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_sz : Exe.bytesAt V2606.zzs.blob 7940776 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_pad : Exe.bytesAt V2606.zzs.blob 7940520 8 = some [0, 0, 2, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_mc : Exe.bytesAt V2606.zzs.blob 7942872 8 = some [0xb0, 0x5a, 0x63, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_sm : Exe.bytesAt V2606.zzs.blob 7942856 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_sb : Exe.bytesAt V2606.zzs.blob 7940584 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem p_mx : Exe.bytesAt V2606.zzs.blob 7942864 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

/-! The tunables' entries in the file: the type at `+8` (0 for the 32-bit ones, 2 for `SIZE_T`) and the
`initialized` byte at `+40`. -/
theorem tu8_25 : Tgv.ent 25 + 8#64 = BitVec.ofNat 64 7936992 := by decide
theorem tu40_25 : Tgv.ent 25 + 40#64 = BitVec.ofNat 64 7937024 := by decide
theorem tuT_25 : Exe.bytesAt V2606.zzs.blob 7936992 4 = some [0, 0, 0, 0] := by decide +kernel
theorem tuI_25 : Exe.bytesAt V2606.zzs.blob 7937024 1 = some [0] := by decide +kernel
theorem tu8_2 : Tgv.ent 2 + 8#64 = BitVec.ofNat 64 7935704 := by decide
theorem tu40_2 : Tgv.ent 2 + 40#64 = BitVec.ofNat 64 7935736 := by decide
theorem tuT_2 : Exe.bytesAt V2606.zzs.blob 7935704 4 = some [0, 0, 0, 0] := by decide +kernel
theorem tuI_2 : Exe.bytesAt V2606.zzs.blob 7935736 1 = some [0] := by decide +kernel
theorem tu8_12 : Tgv.ent 12 + 8#64 = BitVec.ofNat 64 7936264 := by decide
theorem tu40_12 : Tgv.ent 12 + 40#64 = BitVec.ofNat 64 7936296 := by decide
theorem tuT_12 : Exe.bytesAt V2606.zzs.blob 7936264 4 = some [0, 0, 0, 0] := by decide +kernel
theorem tuI_12 : Exe.bytesAt V2606.zzs.blob 7936296 1 = some [0] := by decide +kernel
theorem tu8_8 : Tgv.ent 8 + 8#64 = BitVec.ofNat 64 7936040 := by decide
theorem tu40_8 : Tgv.ent 8 + 40#64 = BitVec.ofNat 64 7936072 := by decide
theorem tuT_8 : Exe.bytesAt V2606.zzs.blob 7936040 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_8 : Exe.bytesAt V2606.zzs.blob 7936072 1 = some [0] := by decide +kernel
theorem tu8_19 : Tgv.ent 19 + 8#64 = BitVec.ofNat 64 7936656 := by decide
theorem tu40_19 : Tgv.ent 19 + 40#64 = BitVec.ofNat 64 7936688 := by decide
theorem tuT_19 : Exe.bytesAt V2606.zzs.blob 7936656 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_19 : Exe.bytesAt V2606.zzs.blob 7936688 1 = some [0] := by decide +kernel
theorem tu8_1 : Tgv.ent 1 + 8#64 = BitVec.ofNat 64 7935648 := by decide
theorem tu40_1 : Tgv.ent 1 + 40#64 = BitVec.ofNat 64 7935680 := by decide
theorem tuT_1 : Exe.bytesAt V2606.zzs.blob 7935648 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_1 : Exe.bytesAt V2606.zzs.blob 7935680 1 = some [0] := by decide +kernel
theorem tu8_18 : Tgv.ent 18 + 8#64 = BitVec.ofNat 64 7936600 := by decide
theorem tu40_18 : Tgv.ent 18 + 40#64 = BitVec.ofNat 64 7936632 := by decide
theorem tuT_18 : Exe.bytesAt V2606.zzs.blob 7936600 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_18 : Exe.bytesAt V2606.zzs.blob 7936632 1 = some [0] := by decide +kernel
theorem tu8_22 : Tgv.ent 22 + 8#64 = BitVec.ofNat 64 7936824 := by decide
theorem tu40_22 : Tgv.ent 22 + 40#64 = BitVec.ofNat 64 7936856 := by decide
theorem tuT_22 : Exe.bytesAt V2606.zzs.blob 7936824 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_22 : Exe.bytesAt V2606.zzs.blob 7936856 1 = some [0] := by decide +kernel
theorem tu8_24 : Tgv.ent 24 + 8#64 = BitVec.ofNat 64 7936936 := by decide
theorem tu40_24 : Tgv.ent 24 + 40#64 = BitVec.ofNat 64 7936968 := by decide
theorem tuT_24 : Exe.bytesAt V2606.zzs.blob 7936936 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_24 : Exe.bytesAt V2606.zzs.blob 7936968 1 = some [0] := by decide +kernel
theorem tu8_21 : Tgv.ent 21 + 8#64 = BitVec.ofNat 64 7936768 := by decide
theorem tu40_21 : Tgv.ent 21 + 40#64 = BitVec.ofNat 64 7936800 := by decide
theorem tuT_21 : Exe.bytesAt V2606.zzs.blob 7936768 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_21 : Exe.bytesAt V2606.zzs.blob 7936800 1 = some [0] := by decide +kernel
theorem tu8_14 : Tgv.ent 14 + 8#64 = BitVec.ofNat 64 7936376 := by decide
theorem tu40_14 : Tgv.ent 14 + 40#64 = BitVec.ofNat 64 7936408 := by decide
theorem tuT_14 : Exe.bytesAt V2606.zzs.blob 7936376 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_14 : Exe.bytesAt V2606.zzs.blob 7936408 1 = some [0] := by decide +kernel
theorem tu8_6 : Tgv.ent 6 + 8#64 = BitVec.ofNat 64 7935928 := by decide
theorem tu40_6 : Tgv.ent 6 + 40#64 = BitVec.ofNat 64 7935960 := by decide
theorem tuT_6 : Exe.bytesAt V2606.zzs.blob 7935928 4 = some [2, 0, 0, 0] := by decide +kernel
theorem tuI_6 : Exe.bytesAt V2606.zzs.blob 7935960 1 = some [0] := by decide +kernel

/-- The twelve tunables in `lif_ok`'s bytes: their entries are below `0x791ca0`, as in the file. -/
theorem ent_tun {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    (∀ d ∈ Pmi.t32, rdd(
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        Tgv.ent d + 8#64) = 0 ∧
      rdb(
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        Tgv.ent d + 40#64) = 0) ∧
    (∀ d ∈ Pmi.t64, rdd(
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        Tgv.ent d + 8#64) = 2#32 ∧
      rdb(
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        Tgv.ent d + 40#64) = 0) := by
  have R : ∀ x n : Nat, 0x777000 ≤ x → x + n ≤ 0x791ca0 →
      List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
        (byteAddrs (BitVec.ofNat 64 x) n) = List.map K.V0 (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h1 h2 => rd_ext _ n fun i hi => by
      have t := tg (b := x) hi (by omega)
      exact ent_ro hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega) (hD _ (by omega) (by omega))
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  · simp only [Pmi.t32, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [tu8_25, tu40_25, R 7936992 4 (by omega) (by omega), R 7937024 1 (by omega) (by omega),
        img_rd hI tuT_25 rfl (by omega) (by omega), img_rd hI tuI_25 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_2, tu40_2, R 7935704 4 (by omega) (by omega), R 7935736 1 (by omega) (by omega),
        img_rd hI tuT_2 rfl (by omega) (by omega), img_rd hI tuI_2 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_12, tu40_12, R 7936264 4 (by omega) (by omega), R 7936296 1 (by omega) (by omega),
        img_rd hI tuT_12 rfl (by omega) (by omega), img_rd hI tuI_12 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
  · simp only [Pmi.t64, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tu8_8, tu40_8, R 7936040 4 (by omega) (by omega), R 7936072 1 (by omega) (by omega),
        img_rd hI tuT_8 rfl (by omega) (by omega), img_rd hI tuI_8 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_19, tu40_19, R 7936656 4 (by omega) (by omega), R 7936688 1 (by omega) (by omega),
        img_rd hI tuT_19 rfl (by omega) (by omega), img_rd hI tuI_19 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_1, tu40_1, R 7935648 4 (by omega) (by omega), R 7935680 1 (by omega) (by omega),
        img_rd hI tuT_1 rfl (by omega) (by omega), img_rd hI tuI_1 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_18, tu40_18, R 7936600 4 (by omega) (by omega), R 7936632 1 (by omega) (by omega),
        img_rd hI tuT_18 rfl (by omega) (by omega), img_rd hI tuI_18 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_22, tu40_22, R 7936824 4 (by omega) (by omega), R 7936856 1 (by omega) (by omega),
        img_rd hI tuT_22 rfl (by omega) (by omega), img_rd hI tuI_22 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_24, tu40_24, R 7936936 4 (by omega) (by omega), R 7936968 1 (by omega) (by omega),
        img_rd hI tuT_24 rfl (by omega) (by omega), img_rd hI tuI_24 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_21, tu40_21, R 7936768 4 (by omega) (by omega), R 7936800 1 (by omega) (by omega),
        img_rd hI tuT_21 rfl (by omega) (by omega), img_rd hI tuI_21 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_14, tu40_14, R 7936376 4 (by omega) (by omega), R 7936408 1 (by omega) (by omega),
        img_rd hI tuT_14 rfl (by omega) (by omega), img_rd hI tuI_14 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [tu8_6, tu40_6, R 7935928 4 (by omega) (by omega), R 7935960 1 (by omega) (by omega),
        img_rd hI tuT_6 rfl (by omega) (by omega), img_rd hI tuI_6 rfl (by omega) (by omega)]
      exact ⟨rfl, rfl⟩

/-- `n` bytes from `x` in the variables (`0x777000`–`0x7a9000`) are in `D`. -/
theorem dv_n {D : Addr → Prop} (hD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → D a) {x n : Nat}
    (h1 : 0x777000 ≤ x) (h2 : x + n ≤ 0x7a9000) : ∀ i < n, D (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have t := tg (b := x) hi (by omega)
  exact hD _ (by omega) (by omega)

/-- Bytes of `.bss` are 0 in the launch bytes. -/
theorem bss_map {V : Addr → Byte} (hB : Bss V) {x n : Nat} (h1 : 0x7945d0 ≤ x) (h2 : x + n ≤ 0x7a86c0) :
    List.map V (byteAddrs (BitVec.ofNat 64 x) n) = List.map (fun _ => (0 : Byte)) (byteAddrs (BitVec.ofNat 64 x) n) :=
  rd_ext _ n fun i hi => by
    have t := tg (b := x) hi (by omega)
    exact hB _ (by omega) (by omega)

/-- Bytes of `malloc`'s state in `lif_ok`'s bytes are the file's. -/
theorem ent_mv {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {x n : Nat} {bs : List Byte} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V)
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → D a) (hr : 0x7a4798 + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x7a4798 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64)
    (hx : MAt x n) (hp : Exe.bytesAt V2606.zzs.blob x n = some bs) (hl : bs.length = n) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (byteAddrs (BitVec.ofNat 64 x) n) = bs := by
  have hx' := hx
  unfold MAt at hx'
  exact (ent_m hK hM hb hb' hW hx (dv_n hD (by omega) (by omega)) (by omega) hr' (by omega) hsn).trans
    (img_rd hI hp hl (by omega) (by omega))

/-- Bytes of the TLS block `[b, b + 8192)` that no store of the start code reaches: between the copied
initialisation image and the TCB, the TCB's words after `header.self` and before the stack guard, and the break's
page above `b + 4544`. -/
def TZ (b j : Nat) : Prop :=
  b + 2088 ≤ j ∧ j < b + 2176 ∨ b + 2200 ≤ j ∧ j < b + 2216 ∨ b + 4544 ≤ j ∧ j < b + 8192

/-- Such a byte is 0 in `lif_ok`'s bytes: `__sbrk` zeroed the two pages. -/
theorem ent_tz {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D) {a : Addr} (ha : TZ b.toNat a.toNat)
    (hr : b.toNat + 8192 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsp : b.toNat + 8192 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a = 0 := by
  unfold TZ at ha
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  have h1 : b.toNat ≤ a.toNat := by omega
  have h2 : a.toNat < b.toNat + 8192 := by omega
  rw [ent_keep (a := a) (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩,
    hW a (.inr ⟨h1, h2⟩) ?_ ?_]
  · unfold PtrMem VerMem GuardMem TlsMem WD WC T4 T3 T2
    rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
      Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
      Vst_out, Vz_in h1 h2]
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 at hj
    rcases hj with ⟨h3, -⟩ | hj
    · omega
    · exact not_junk2 (by omega) (by unfold CpuVar; omega) hj
  · unfold Pim.PimVar
    omega

/-- `n` such bytes from `x`, `x.toNat = c`. -/
theorem ent_tzr {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {x : Addr} {n c : Nat} (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hxt : x.toNat = c) (hcn : c + n ≤ b.toNat + 8192) (hz : ∀ j, c ≤ j → j < c + n → TZ b.toNat j)
    (hr : b.toNat + 8192 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsp : b.toNat + 8192 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (byteAddrs x n) = List.map (fun _ => (0 : Byte)) (byteAddrs x n) :=
  rd_ext _ n fun i hi => by
    have t : (x.add i).toNat = c + i := by rw [toNat_add_of_fits hi (by omega), hxt]
    exact ent_tz hb hb' hbp hW (by rw [t]; exact hz _ (by omega) (by omega)) hr hr' hsp hsn

/-- `cb` of `MPre`: `__curbrk` is `b + 4544`, as `__sbrk` left it. -/
theorem ent_cb {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add curbrk i))
    (hr : 0x7a4c40 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x7a4c40 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      curbrk) = b + 4544#64 := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  have h8 : ∀ i < 8,
      Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
        (Addr.add curbrk i) = T2 V b (Addr.add curbrk i) := by
    intro i hi
    have t : (Addr.add curbrk i).toNat = 0x7a4c38 + i := tg (b := 0x7a4c38) hi (by omega)
    rw [ent_keep (a := Addr.add curbrk i) (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩,
      hW _ (.inl (hD i hi)) ?_ ?_]
    · unfold PtrMem VerMem GuardMem TlsMem WD WC T4 T3
      rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
        Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
      all_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega
    · intro hj
      unfold Junk3 at hj
      rcases hj with ⟨h3, -⟩ | hj
      · omega
      · exact not_junk2 (by omega) (by unfold CpuVar; omega) hj
    · unfold Pim.PimVar
      omega
  rw [rd_ext _ 8 h8]
  unfold T2
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) ?_]
  · exact ofBytesLE_toBytesLE (n := 8) rfl _
  · first | decide | (simp only [curbrk]; bv_omega) | bv_omega

/-- `ml0` of `MPre`: `__libc_init_first` stored 0 to the word at `0x7939c0`. -/
theorem ent_ml {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr}
    (hr : 7944644 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 7944644 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdd(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      7944640#64) = 0 := by
  unfold Ndi.fV
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  unfold Lif.LifMem
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _) ?_]
  · exact ofBytesLE_toBytesLE (n := 4) rfl _
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- A byte of a tunable's entry is in the variables. -/
macro "tun_omega" : tactic =>
  `(tactic| (unfold Tgv.ent; first | (simp only [Addr.add]; bv_omega) | bv_omega |
    (simp only [BitVec.add_eq]; bv_omega)))

set_option maxHeartbeats 1600000 in
/-- `MPre` of `lif_ok`'s bytes, the break `b + 4544` and `fs` at `b + 2176`; `M_PAD` `0x20000`, no `sbrk` or
`mmap` so far. -/
theorem ent_mpre {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {F : Footprint}
    {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V)
    (hps : (K.vs K.M).pagesize = 4096#64) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hal : b.toNat % 4096 = 0) (hbp : b.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → D a)
    (hFv : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a)
    (hr : b.toNat + 8192 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : b.toNat + 8192 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    MPre F (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (b + 4544#64) (b + 2176#64) 0x20000#64 0#64 0#64 := by
  have e45 : (b + 4544#64).toNat = b.toNat + 4544 := by bv_omega
  have hr1 : 0x7a4798 + 32 ≤ g.rsp.toNat := by omega
  have hs1 : 0x7a4798 ≤ sp.toNat + 80 := by omega
  have hsp' : b.toNat + 8192 ≤ sp.toNat + 80 := by omega
  obtain ⟨T32, T64⟩ := ent_tun (ra := ra) (ra₀ := ra₀) (gY := gY) hK hI hM hb hb' hW
    (fun a h1 h2 => hD a h1 (by omega)) (by omega) hr' (by omega) hsn
  have m32 : ∀ d ∈ Pmi.t32, d.toNat < 64 := by decide
  have m64 : ∀ d ∈ Pmi.t64, d.toNat < 64 := by decide
  refine
    { hook := ?_, mi := ?_, u32 := fun d hd => ?_, u64 := fun d hd => ?_, sd := ?_, mt := ?_, lk := ?_,
      tc := ?_, fz := fun k hk => ?_, tb := ?_, m0 := ?_, m1 := ?_, m2 := ?_, m3 := ?_, ps := ?_, thr := ?_,
      sz := ?_, hpad := ?_, fl := ?_, mc := ?_, cb := ?_, ml0 := ?_, k0 := ?_, hsm := ?_, sb := ?_, hmx := ?_,
      p0 := ?_, z := fun a h1 h2 => ?_ }
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940656) (n := 8) (by unfold MAt; omega) p_hook rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940484) (n := 4) (by unfold MAt; omega) p_mi rfl]
    first | rfl | decide
  · have h64 := m32 d hd
    exact ⟨fun i hi => hFv _ (by tun_omega) (by tun_omega), fun i hi => hFv _ (by tun_omega) (by tun_omega),
      fun i hi => hFv _ (by tun_omega) (by tun_omega), (T32 d hd).1, (T32 d hd).2⟩
  · have h64 := m64 d hd
    exact ⟨fun i hi => hFv _ (by tun_omega) (by tun_omega), fun i hi => hFv _ (by tun_omega) (by tun_omega),
      fun i hi => hFv _ (by tun_omega) (by tun_omega), fun h => absurd ((T64 d hd).1.symm.trans h) (by decide),
      (T64 d hd).2⟩
  · rw [ent_tzr (x := b + 2176#64 + 18446744073709551584#64) (n := 1) (c := b.toNat + 2144) hb hb' hbp hW
      (by bv_omega) (by omega) (fun j h1 h2 => by unfold TZ; omega) hr hr' hsp' hsn]
    simp only [byteAddrs, List.map_map, Function.comp_def]
    first | rfl | decide
  · rw [ent_tzr (x := b + 2176#64 + 24#64) (n := 4) (c := b.toNat + 2200) hb hb' hbp hW
      (by bv_omega) (by omega) (fun j h1 h2 => by unfold TZ; omega) hr hr' hsp' hsn]
    simp only [byteAddrs, List.map_map, Function.comp_def]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940672) (n := 4) (by unfold MAt; omega) p_lk rfl]
    first | rfl | decide
  · rw [ent_tzr (x := b + 2176#64 + 18446744073709551576#64) (n := 8) (c := b.toNat + 2136) hb hb' hbp hW
      (by bv_omega) (by omega) (fun j h1 h2 => by unfold TZ; omega) hr hr' hsp' hsn]
    simp only [byteAddrs, List.map_map, Function.comp_def]
    first | rfl | decide
  · rw [ent_m hK hM hb hb' hW (x := 7940688 + 8 * k) (n := 8) (by unfold MAt; omega)
      (dv_n hD (by omega) (by omega)) (by omega) hr' (by omega) hsn,
      hI.map p_fz (by simp) (by omega) (by omega) (off := 8 * k) (m := 8) (by omega)]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940592) (n := 8) (by unfold MAt; omega) p_tb rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942816) (n := 4) (by unfold MAt; omega) p_m0 rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942820) (n := 4) (by unfold MAt; omega) p_m1 rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942824) (n := 4) (by unfold MAt; omega) p_m2 rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942828) (n := 4) (by unfold MAt; omega) p_m3 rfl]
    first | rfl | decide
  · exact ent_pgs hM hps hb hb' (by omega) hW (dv_n hD (by omega) (by omega)) (by omega) hr' (by omega) hsn
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940528) (n := 8) (by unfold MAt; omega) p_thr rfl]
    decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940776) (n := 8) (by unfold MAt; omega) p_sz rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940520) (n := 8) (by unfold MAt; omega) p_pad rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940676) (n := 1) (by unfold MAt; omega) p_fl rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942872) (n := 8) (by unfold MAt; omega) p_mc rfl]
    first | rfl | decide
  · exact ent_cb hb hb' hbp hW (fun i hi => by
      have t : (Addr.add curbrk i).toNat = 0x7a4c38 + i := tg (b := 0x7a4c38) hi (by omega)
      exact hD _ (by omega) (by omega)) (by omega) hr' (by omega) hsn
  · exact ent_ml (by omega) hr' (by omega) hsn
  · rw [ent_m hK hM hb hb' hW (x := 8013152) (n := 8) (by unfold MAt; omega) (dv_n hD (by omega) (by omega))
      (by omega) hr' (by omega) hsn, bss_map hB (x := 8013152) (n := 8) (by omega) (by omega)]
    simp only [byteAddrs, List.map_map, Function.comp_def]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942856) (n := 8) (by unfold MAt; omega) p_sm rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7940584) (n := 8) (by unfold MAt; omega) p_sb rfl]
    first | rfl | decide
  · rw [ent_mv hK hI hM hb hb' hW hD hr1 hr' hs1 hsn (x := 7942864) (n := 8) (by unfold MAt; omega) p_mx rfl]
    first | rfl | decide
  · rw [ent_m hK hM hb hb' hW (x := 8013220) (n := 4) (by unfold MAt; omega) (dv_n hD (by omega) (by omega))
      (by omega) hr' (by omega) hsn, bss_map hB (x := 8013220) (n := 4) (by omega) (by omega)]
    simp only [byteAddrs, List.map_map, Function.comp_def]
    first | rfl | decide
  · rw [e45] at h1 h2
    unfold pageUp at h2
    exact ent_tz hb hb' hbp hW (by unfold TZ; omega) hr hr' hsp' hsn

/-- `hpre` of `lif_ok`: `MPre` of the bytes at the entry of `_dl_get_origin`, which below the return address of its
call are `lif_ok`'s bytes. -/
theorem ent_mpreN {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {F : Footprint}
    {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V)
    (hps : (K.vs K.M).pagesize = 4096#64) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hal : b.toNat % 4096 = 0) (hbp : b.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → D a)
    (hFv : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a)
    (hr : b.toNat + 8192 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsp : b.toNat + 8648 ≤ sp.toNat) (hsn : sp.toNat + 128 ≤ 2 ^ 64) :
    MPre F (Ndi.nV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      (b + 4544#64) (b + 2176#64) 0x20000#64 0#64 0#64 := by
  have e45 : (b + 4544#64).toNat = b.toNat + 4544 := by bv_omega
  have e21 : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  refine (ent_mpre hK hI hB hM hps hb hb' hal hbp hW hD hFv hr hr' (by omega) (by omega)).lo
    (by rw [e21]; omega) (by rw [e21, e45]; omega) fun a ha => ?_
  rw [e45] at ha
  exact Ndi.nV_fV (by omega) hsn (.inl (by omega))

end FV7z.Start
