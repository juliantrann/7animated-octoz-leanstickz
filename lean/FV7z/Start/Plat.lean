import FV7z.Start.ToOsv
/-!
# `_dl_platform` after `_dl_aux_init` and at the call of `__libc_init_first` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `Pl`: `_dl_platform` (`0x7a8548`) points to a string. `_dl_aux_init` stores `AT_PLATFORM`,
the address of the platform string `execve` puts on the new stack; `init_cpu_features` may replace it with
`"xeon_phi"` (`0x6ee608`) or `"haswell"` (`0x6ee611`) (`CpuFeat.PlW`, carried to `0x613434` by `launch_to_ptr`).

- `auxv_plat`, `auxv_idx15`, `ctxOf_platform`: the vector has an `AT_PLATFORM`, with the address of the string; so
  `_dl_platform` after `_dl_aux_init` is that address.
- `mb_plat`: from `PlW` on the bytes `MB` describes, `_dl_platform` is one of the three.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit

theorem auxv_plat (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ (∀ e ∈ pre, e.1 ≠ 0 ∧ e.1 < 64) ∧
      (∀ e ∈ pre, e.1 = 15 → e.2 = l.platform - platformString.length) ∧
      (15, l.platform - platformString.length) ∈ pre := by
  refine ⟨(if prof.linux.vdso then [(33, c.vdsoText)] else []) ++
    [(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_, ?_, ?_⟩ <;>
    cases hv : prof.linux.vdso <;> simp [auxv, hv]

/-- The vector by index: there is an `AT_PLATFORM`, and each has the address of the string. -/
theorem auxv_idx15 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    (∃ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 15) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 15 →
      ((auxv prof hdr pa a c l).getD n (0, 0)).2 = l.platform - platformString.length) := by
  obtain ⟨pre, hA, hnz, h5, m5⟩ := auxv_plat prof hdr pa a c l
  have hlen : pre.length = auxCount prof.linux - 1 := by
    have := auxv_length prof hdr pa a c l
    rw [hA] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  rw [hA, ← hlen]
  have hin : ∀ n, n < pre.length → (pre ++ [(0, 0)]).getD n (0, 0) ∈ pre := by
    intro n hn
    rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn, e⟩ := List.mem_iff_getElem.1 m5
    exact ⟨n, hn, by
      rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, e]; rfl⟩
  · intro n hn h
    refine h5 _ (hin n hn) ?_
    have h' : BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 15 := h
    have := congrArg BitVec.toNat h'
    have b := (hnz _ (hin n hn)).2
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem step_platform (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).platform = if e.1 = 15 then e.2 else v.platform := by
  by_cases h : e.1 = 15
  · simp [AuxInit.step, h]
  · simp only [AuxInit.step, apply_ite Vars.platform, h, ↓reduceIte]
    repeat' split
    all_goals rfl

/-- `_dl_platform` after a vector with an `AT_PLATFORM`, each with the value `x`. -/
theorem vsOf_platform {ty val : Nat → BitVec 64} {w : Vars} {x : BitVec 64} :
    ∀ M, (∃ n < M, ty n = 15) → (∀ n < M, ty n = 15 → val n = x) → (vsOf ty val w M).platform = x
  | 0, ⟨_, hn, _⟩, _ => absurd hn (Nat.not_lt_zero _)
  | M + 1, ⟨n, hn, h3⟩, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).platform = x
    rw [step_platform]
    split
    · next hM => exact hall M (Nat.lt_succ_self _) hM
    · next hM =>
      have hlt : n < M := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
        · exact h
        · exact absurd (h ▸ h3) hM
      exact vsOf_platform M ⟨n, hlt, h3⟩ fun k hk => hall k (Nat.lt_succ_of_lt hk)

/-- After `_dl_aux_init`, in a run of `7zzs`: `_dl_platform` is the address of the platform string. -/
theorem ctxOf_platform (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).platform =
      BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length) := by
  obtain ⟨e5, h5⟩ := auxv_idx15 prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  refine vsOf_platform _ e5 fun n hn h => ?_
  show BitVec.ofNat 64 _ = _
  rw [h5 n hn h]

/-- `_dl_platform` in bytes `PlW`-related to those `MB` describes: `AT_PLATFORM`, `"xeon_phi"` or `"haswell"`. -/
theorem mb_plat {K : Ctx} {V W : Addr → Byte} (hM : MB K V) (h : CpuFeat.PlW V W) :
    rdq(W, 0x7a8548#64) = (K.vs K.M).platform ∨ rdq(W, 0x7a8548#64) = 0x6ee608#64 ∨
      rdq(W, 0x7a8548#64) = 0x6ee611#64 := by
  have hg := hM.gl.platform
  unfold CpuFeat.PlW at h
  rcases h with h | h | h
  · exact .inl (h.trans hg)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

end FV7z.Start
