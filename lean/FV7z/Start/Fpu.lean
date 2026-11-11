import FV7z.Start.ToPtr
/-!
# The two x87 control words at `__libc_init_first` (PLAN.md G3, startup)

`__libc_init_first` compares `__fpu_control` (`0x793c80`) with `_dl_fpu_control` (`0x7933cc`) and calls
`__setfpucw` if they differ. `_dl_aux_init` stores `_dl_fpu_control` for an `AT_FPUCW` (18) only, and the vector
`execve` makes has none; so both are the file's `0x037f`.

- `auxv_fp`, `auxv_no18`: no entry of the vector has the type 18.
- `step_fpu`, `vsOf_fpu`, `ctxOf_fpu`: `_dl_fpu_control` after `_dl_aux_init` is as before it.
- `fpu_pin`, `fpc_pin`: the two words in the file.
- `mb_fpu`: after `_dl_aux_init` (`MB`), the two words are `0x037f`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit

theorem auxv_fp (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ ∀ e ∈ pre, e.1 ≠ 18 ∧ e.1 < 64 := by
  refine ⟨(if prof.linux.vdso then [(33, c.vdsoText)] else []) ++
    [(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_⟩ <;>
    cases hv : prof.linux.vdso <;> simp [auxv, hv]

/-- The vector by index: no entry is an `AT_FPUCW`. -/
theorem auxv_no18 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    ∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 ≠ 18 := by
  obtain ⟨pre, hA, h18⟩ := auxv_fp prof hdr pa a c l
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
  have h' : BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 18 := h
  have := congrArg BitVec.toNat h'
  have b := h18 _ hin
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem step_fpu (v : Vars) (e : BitVec 64 × BitVec 64) (h : e.1 ≠ 18) :
    (AuxInit.step v e).fpuControl = v.fpuControl := by
  simp only [AuxInit.step, apply_ite Vars.fpuControl, h, ↓reduceIte]
  repeat' split
  all_goals rfl

/-- `_dl_fpu_control` after a vector with no `AT_FPUCW`. -/
theorem vsOf_fpu {ty val : Nat → BitVec 64} {w : Vars} :
    ∀ M, (∀ n < M, ty n ≠ 18) → (vsOf ty val w M).fpuControl = w.fpuControl
  | 0, _ => rfl
  | M + 1, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).fpuControl = _
    rw [step_fpu _ _ (hall M (Nat.lt_succ_self _))]
    exact vsOf_fpu M fun k hk => hall k (Nat.lt_succ_of_lt hk)

/-- `_dl_fpu_control` after `_dl_aux_init` is as before it. -/
theorem ctxOf_fpu (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).fpuControl = (ctxOf prof s a c).w0.fpuControl :=
  vsOf_fpu _ (auxv_no18 prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c))

/-- `_dl_fpu_control` in the file. -/
theorem fpu_pin : Exe.bytesAt V2606.zzs.blob 0x7933cc 2 = some [0x7f, 0x03] := by decide +kernel
/-- `__fpu_control` in the file. -/
theorem fpc_pin : Exe.bytesAt V2606.zzs.blob 0x793c80 2 = some [0x7f, 0x03] := by decide +kernel

/-- After `_dl_aux_init`, `_dl_fpu_control` and `__fpu_control` are the file's `0x037f`. -/
theorem mb_fpu {K : Ctx} {V : Addr → Byte} (hK : K.Ok) (hI : Img K.V0) (hMB : MB K V)
    (hfp : (K.vs K.M).fpuControl = K.w0.fpuControl) :
    rdw(V, 7943116#64) = 0x37f#16 ∧ rdw(V, 7945344#64) = 0x37f#16 := by
  have him := hK.himg
  refine ⟨?_, ?_⟩
  · have e1 : rdw(V, 7943116#64) = (K.vs K.M).fpuControl := hMB.gl.fpuControl
    have e2 : rdw(K.V0, 7943116#64) = K.w0.fpuControl := hK.hgl.fpuControl
    rw [e1, hfp, ← e2]
    exact (congrArg (ofBytesLE 16) (hI.map fpu_pin rfl (by decide) (by decide) (off := 0) (m := 2)
      (by decide))).trans (by decide)
  · have e : List.map V (byteAddrs 7945344#64 2) = List.map K.V0 (byteAddrs 7945344#64 2) :=
      rd_congr fun i hi => by
        have e := tg hi (b := 7945344) (by decide)
        exact hMB.same _ (by simp only [InStk]; omega)
          (not_dg (lo := 0x793c80) (hi := 0x793c82) (by decide) (by omega) (by omega))
    rw [e]
    exact (congrArg (ofBytesLE 16) (hI.map fpc_pin rfl (by decide) (by decide) (off := 0) (m := 2)
      (by decide))).trans (by decide)

end FV7z.Start
