import FV7z.Start.Phd
/-!
# `_dl_sysinfo_dso`, `_dl_sysinfo_map` and `__libc_enable_secure` at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7a8508) = 0` (`h1`, `_dl_sysinfo_dso`), `rdq(·, 0x7a84f0) = 0` (`h4`,
`_dl_sysinfo_map`) and `rdd(·, 0x791ce0) = 0` (`h5`, `__libc_enable_secure`). The first two are in `.bss`;
`_dl_aux_init` stores `_dl_sysinfo_dso` for an `AT_SYSINFO_EHDR` (33) only, which `execve` puts in the vector only
with a vDSO (`prof.linux.vdso`). The third is the `AT_SECURE` value, 0 (`vs_secure`).

- `auxv_n33`, `auxv_no33`, `step_sdso`, `vsOf_sdso`, `ctxOf_sdso`: without a vDSO, `_dl_sysinfo_dso` after
  `_dl_aux_init` is as before it.
- `ent_bss`: a word of `.bss` away from `_dl_aux_init`'s variables is 0 in `lif_ok`'s bytes.
- `ent_sdso`, `ent_sm`, `ent_sec`: `h1`, `h4`, `h5` of `lif_ok`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Tls (rd_ext)

theorem auxv_n33 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout)
    (hv : prof.linux.vdso = false) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ ∀ e ∈ pre, e.1 ≠ 33 ∧ e.1 < 64 := by
  refine ⟨[(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_⟩ <;>
    simp [auxv, hv]

/-- The vector by index: without a vDSO, no entry is an `AT_SYSINFO_EHDR`. -/
theorem auxv_no33 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout)
    (hv : prof.linux.vdso = false) :
    ∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 ≠ 33 := by
  obtain ⟨pre, hA, h33⟩ := auxv_n33 prof hdr pa a c l hv
  have hlen : pre.length = auxCount prof.linux - 1 := by
    have := auxv_length prof hdr pa a c l
    rw [hA] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  rw [hA, ← hlen]
  intro n hn h
  have hin : (pre ++ [(0, 0)]).getD n (0, 0) ∈ pre := by
    rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  have h' : BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 33 := h
  have := congrArg BitVec.toNat h'
  have b := h33 _ hin
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem step_sdso (v : Vars) (e : BitVec 64 × BitVec 64) (h : e.1 ≠ 33) :
    (AuxInit.step v e).sysinfoDso = v.sysinfoDso := by
  simp only [AuxInit.step, apply_ite Vars.sysinfoDso, h, ↓reduceIte]
  repeat' split
  all_goals rfl

/-- `_dl_sysinfo_dso` after a vector with no `AT_SYSINFO_EHDR`. -/
theorem vsOf_sdso {ty val : Nat → BitVec 64} {w : Vars} :
    ∀ M, (∀ n < M, ty n ≠ 33) → (vsOf ty val w M).sysinfoDso = w.sysinfoDso
  | 0, _ => rfl
  | M + 1, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).sysinfoDso = _
    rw [step_sdso _ _ (hall M (Nat.lt_succ_self _))]
    exact vsOf_sdso M fun k hk => hall k (Nat.lt_succ_of_lt hk)

/-- Without a vDSO, `_dl_sysinfo_dso` after `_dl_aux_init` is as before it. -/
theorem ctxOf_sdso (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) (hv : prof.linux.vdso = false) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).sysinfoDso = (ctxOf prof s a c).w0.sysinfoDso :=
  vsOf_sdso _ (auxv_no33 prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c) hv)

/-- `h1` of `lif_ok`: `_dl_sysinfo_dso` is 0. -/
theorem ent_sdso {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hB : Bss K.V0) (hM : MB K V)
    (hsd : (K.vs K.M).sysinfoDso = K.w0.sysinfoDso) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 8029448#64 i))
    (hr : 8029456 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 8029456 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      8029448#64) = 0#64 := by
  have e := ent_v (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 8029448) (n := 8) hb hb' hbp hW hD
    (by unfold GlAt; omega) hr hr' hsp hsn
  have z := bss_rdq hB (x := 8029448) ⟨by omega, by omega⟩
  rw [e]
  exact hM.gl.sysinfoDso.trans (hsd.trans (hK.hgl.sysinfoDso.symm.trans z))

/-- A word of `.bss` that `GlAt` covers and `_dl_aux_init` does not store to is 0 in `lif_ok`'s bytes. -/
theorem ent_bss {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {x : Nat} (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ i < 8, D (Addr.add (BitVec.ofNat 64 x) i)) (hx : GlAt x 8) (hz : 0x7945d0 ≤ x ∧ x + 8 ≤ 0x7a86c0)
    (hd : ∀ r ∈ d3 ++ globals, r.base.toNat + r.len ≤ x ∨ x + 8 ≤ r.base.toNat)
    (hr : x + 8 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + 8 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      BitVec.ofNat 64 x) = 0#64 := by
  have e := ent_v (ra := ra) (ra₀ := ra₀) (gY := gY) hb hb' hbp hW hD hx hr hr' hsp hsn
  have e' := rd_ext (W' := V) (W := K.V0) (BitVec.ofNat 64 x) 8 fun i hi => by
    have t := tg (b := x) hi (by omega)
    exact hM.same _ (by simp only [InStk]; omega) (not_dg hd (by omega) (by omega))
  rw [e, e']
  exact bss_rdq hB hz

/-- `h4` of `lif_ok`: `_dl_sysinfo_map` is 0. -/
theorem ent_sm {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ i < 8, D (Addr.add 8029424#64 i)) (hr : 8029432 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsp : 8029432 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      8029424#64) = 0#64 :=
  ent_bss (x := 8029424) hB hM hb hb' hbp hW hD (by unfold GlAt; omega) ⟨by omega, by omega⟩ (by decide) hr hr'
    hsp hsn

/-- `h5` of `lif_ok`: `__libc_enable_secure` is 0. -/
theorem ent_sec {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ i < 4, D (Addr.add 7937248#64 i)) (hr : 7937252 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsp : 7937252 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdd(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      7937248#64) = 0#32 := by
  have e := ent_v (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 7937248) (n := 4) hb hb' hbp hW hD
    (by unfold GlAt; omega) hr hr' hsp hsn
  rw [e]
  exact hM.gl.secure.trans (vs_secure hK K.M (Nat.le_refl _) ⟨K.sn, hK.hsn, hK.hsec⟩).1

end FV7z.Start
