import FV7z.Start.LchOf
/-!
# `_dl_pagesize` after `_dl_aux_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7933d8) = 4096` (`hpgs`). Zellic's `execve` writes one `AT_PAGESZ` entry, value
4096, before `AT_NULL`, so after `_dl_aux_init` the variable holds 4096.

- `step_ps_ne`, `step_ps6`: an entry of another type leaves `pagesize`; an `AT_PAGESZ` entry of 4096 sets it.
- `vsOf_ps`: if one of the first `n` entries has type 6 and each such entry has value 4096, the variables after them
  have `pagesize = 4096`.
- `auxv_ps`: the vector of `execve` has an `AT_PAGESZ` entry before `AT_NULL`, and each holds 4096.
- `ctxOf_ps`: so `(K.vs K.M).pagesize = 4096` for the context of a state `execve` starts 7zzs in; `mb_ps`: in the
  bytes `MB` describes, `rdq(0x7933d8) = 4096` when that holds.
-/
namespace FV7z.Start
open ZellicX86
open FV7z.AuxInit (Vars)

theorem step_ps_ne (v : Vars) (e : BitVec 64 × BitVec 64) (h : e.1 ≠ 6) :
    (AuxInit.step v e).pagesize = v.pagesize := by
  simp only [AuxInit.step, apply_ite Vars.pagesize, h, ↓reduceIte, ite_self]

theorem step_ps6 (v : Vars) (e : BitVec 64 × BitVec 64) (h1 : e.1 = 6) (h2 : e.2 = 4096#64) :
    (AuxInit.step v e).pagesize = 4096#64 := by
  obtain ⟨t, x⟩ := e
  simp only at h1 h2
  subst h1 h2
  first | rfl | decide | simp [AuxInit.step]

theorem vsOf_ps (ty val : Nat → BitVec 64) (w : Vars) :
    ∀ n, (∀ k < n, ty k = 6 → val k = 4096#64) → (∃ k, k < n ∧ ty k = 6) → (vsOf ty val w n).pagesize = 4096#64 := by
  intro n
  induction n with
  | zero => rintro - ⟨k, hk, -⟩; omega
  | succ n ih =>
    rintro h4 ⟨k, hk, hk6⟩
    show (AuxInit.step (vsOf ty val w n) (ty n, val n)).pagesize = 4096#64
    by_cases h : ty n = 6
    · exact step_ps6 _ (ty n, val n) h (h4 n (by omega) h)
    · rw [step_ps_ne _ (ty n, val n) h]
      exact ih (fun j hj => h4 j (by omega)) ⟨k, by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h' | h'
        · exact h'
        · subst h'; exact absurd hk6 h, hk6⟩

theorem auxv_ps (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    (∃ n, n < auxCount prof.linux - 1 ∧ BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 6) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 6 →
      BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).2 = 4096#64) := by
  obtain ⟨pre, hA, hnz, -⟩ := auxv_facts prof hdr pa a c l
  have h6a : ∀ e ∈ auxv prof hdr pa a c l, e.1 = 6 → e.2 = 4096 := by
    cases hv : prof.linux.vdso <;> simp [auxv, hv]
  have m6a : ((6 : Nat), (4096 : Nat)) ∈ auxv prof hdr pa a c l := by
    cases hv : prof.linux.vdso <;> simp [auxv, hv]
  have h6 : ∀ e ∈ pre, e.1 = 6 → e.2 = 4096 := fun e he => h6a e (by rw [hA]; exact List.mem_append_left _ he)
  have m6 : ((6 : Nat), (4096 : Nat)) ∈ pre := by
    rw [hA] at m6a
    rcases List.mem_append.1 m6a with h | h
    · exact h
    · simp at h
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
  have hof : ∀ t k : Nat, t < 64 → k < 64 → BitVec.ofNat 64 t = BitVec.ofNat 64 k → t = k := by
    intro t k ht hk h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn, e⟩ := List.mem_iff_getElem.1 m6
    exact ⟨n, hn, by
      rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, e]
      rfl⟩
  · intro n hn h
    rw [h6 _ (hin n hn) (hof _ 6 (hnz _ (hin n hn)).2 (by omega) h)]

/-- After `_dl_aux_init`, in the context of a state `execve` starts 7zzs in, `_dl_pagesize` is 4096. -/
theorem ctxOf_ps (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).pagesize = 4096#64 := by
  obtain ⟨⟨j, hj, h6⟩, h4⟩ := auxv_ps prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  exact vsOf_ps (ctxOf prof s a c).ty (ctxOf prof s a c).val (ctxOf prof s a c).w0 _ h4 ⟨j, hj, h6⟩

/-- The bytes `MB` describes hold the pagesize of the context at `0x7933d8`. -/
theorem mb_ps {K : Ctx} {V : Addr → Byte} (hM : MB K V) (hps : (K.vs K.M).pagesize = 4096#64) :
    rdq(V, 0x7933d8#64) = 4096#64 :=
  hM.gl.pagesize.trans hps

end FV7z.Start
