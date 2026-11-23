import FV7z.Start.Plat
import FV7z.Start.Pgs
import FV7z.Start.Keep
/-!
# `_dl_phdr` and `_dl_phnum` at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7a8580) = 0x400040` (`h2`, `_dl_phdr`) and `rdq(·, 0x7a8598) = 8` (`h3`,
`_dl_phnum`). `_dl_aux_init` sets them from `AT_PHDR` and `AT_PHNUM`; no later store of the start code touches them.

- `idx_pre`: a vector `pre ++ [(0, 0)]` in which every entry of type `T` has the value `v`, and one has type `T`.
- `vsOf_fld`: a variable `_dl_aux_init` sets from one type only, after a vector as `idx_pre` gives.
- `ctxOf_phdr`, `ctxOf_phnum`: so after `_dl_aux_init` in a run of 7zzs, `0x400040` and 8.
- `ptr_gl`, `ent_gl`: a word of the variables above `0x7a8418` (but `_dl_osversion` and the CPU variables) is, in the
  bytes at `0x613434` and in `lif_ok`'s, that of `MB`.
- `ent_phd`: `h2` and `h3` of `lif_ok`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

theorem idx_pre {pre : List (Nat × Nat)} {T v : Nat} (hnz : ∀ e ∈ pre, e.1 ≠ 0 ∧ e.1 < 64)
    (hT : ∀ e ∈ pre, e.1 = T → e.2 = v) (mT : (T, v) ∈ pre) :
    (∃ n < pre.length, BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 T) ∧
    (∀ n < pre.length, BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 T →
      ((pre ++ [(0, 0)]).getD n (0, 0)).2 = v) := by
  have hin : ∀ n, n < pre.length → (pre ++ [(0, 0)]).getD n (0, 0) ∈ pre := by
    intro n hn
    rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  have hT64 := (hnz _ mT).2
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn, e⟩ := List.mem_iff_getElem.1 mT
    exact ⟨n, hn, by
      rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, e]
      try rfl⟩
  · intro n hn h
    refine hT _ (hin n hn) ?_
    have := congrArg BitVec.toNat h
    have b := (hnz _ (hin n hn)).2
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- A variable that `_dl_aux_init` sets from the entries of one type `T` only: after a vector with such an entry,
each with the value `x`, it is `x`. -/
theorem vsOf_fld (f : Vars → BitVec 64) (T : BitVec 64)
    (hs : ∀ v e, f (AuxInit.step v e) = if e.1 = T then e.2 else f v) {ty val : Nat → BitVec 64} {w : Vars}
    {x : BitVec 64} : ∀ M, (∃ n < M, ty n = T) → (∀ n < M, ty n = T → val n = x) → f (vsOf ty val w M) = x
  | 0, ⟨_, hn, _⟩, _ => absurd hn (Nat.not_lt_zero _)
  | M + 1, ⟨n, hn, h3⟩, hall => by
    show f (AuxInit.step (vsOf ty val w M) (ty M, val M)) = x
    rw [hs]
    split
    · next hM => exact hall M (Nat.lt_succ_self _) hM
    · next hM =>
      have hlt : n < M := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
        · exact h
        · exact absurd (h ▸ h3) hM
      exact vsOf_fld f T hs M ⟨n, hlt, h3⟩ fun k hk => hall k (Nat.lt_succ_of_lt hk)

theorem step_phdr (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).phdr = if e.1 = 3 then e.2 else v.phdr := by
  by_cases h : e.1 = 3
  · simp [AuxInit.step, h]
  · simp only [AuxInit.step, apply_ite Vars.phdr, h, ↓reduceIte]
    repeat' split
    all_goals rfl

theorem step_phnum (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).phnum = if e.1 = 5 then e.2 else v.phnum := by
  by_cases h : e.1 = 5
  · simp [AuxInit.step, h]
  · simp only [AuxInit.step, apply_ite Vars.phnum, h, ↓reduceIte]
    repeat' split
    all_goals rfl

theorem auxv_pn (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ (∀ e ∈ pre, e.1 ≠ 0 ∧ e.1 < 64) ∧
      (∀ e ∈ pre, e.1 = 5 → e.2 = hdr.phnum) ∧ (5, hdr.phnum) ∈ pre := by
  refine ⟨(if prof.linux.vdso then [(33, c.vdsoText)] else []) ++
    [(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_, ?_, ?_⟩ <;>
    cases hv : prof.linux.vdso <;> simp [auxv, hv]

theorem zzs_phnum : (ElfHeader.read V2606.zzs.blob.bytes).phnum = 8 := by decide +kernel

/-- After `_dl_aux_init`, in a run of `7zzs`: `_dl_phdr` is `0x400040`. -/
theorem ctxOf_phdr (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).phdr = 0x400040#64 := by
  obtain ⟨-, -, -, -, e3, h3⟩ := auxv_idx prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  refine vsOf_fld AuxInit.Vars.phdr 3 step_phdr _ e3 fun n hn h => ?_
  show BitVec.ofNat 64 _ = _
  rw [h3 n hn h, zzs_phdrAddr]
  try rfl

/-- After `_dl_aux_init`, in a run of `7zzs`: `_dl_phnum` is 8. -/
theorem ctxOf_phnum (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).phnum = 8#64 := by
  obtain ⟨pre, hA, hnz, h5, m5⟩ := auxv_pn prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  have hlen : pre.length = auxCount prof.linux - 1 := by
    have := auxv_length prof (ElfHeader.read V2606.zzs.blob.bytes)
      (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
    rw [hA] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  obtain ⟨e5, f5⟩ := idx_pre hnz h5 m5
  rw [hlen, ← hA] at e5 f5
  refine vsOf_fld AuxInit.Vars.phnum 5 step_phnum _ e5 fun n hn h => ?_
  show BitVec.ofNat 64 _ = _
  rw [f5 n hn h, zzs_phnum]
  try rfl

/-- A word of the variables above `0x7a8418`, away from `_dl_osversion` (`0x7a8520`) and `_dl_platform`, is at the
call of `__libc_init_first` that of the bytes `MB` describes. -/
theorem ptr_gl {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {x : Nat}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add (BitVec.ofNat 64 x) i))
    (hx : 0x7a8418 ≤ x ∧ x + 8 ≤ 0x7a8520 ∨ 0x7a8580 ≤ x ∧ x + 8 ≤ 0x7a9000) :
    rdq(W, BitVec.ofNat 64 x) = rdq(V, BitVec.ofNat 64 x) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have t0 : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h : ∀ i < 8, W (Addr.add (BitVec.ofNat 64 x) i) = V (Addr.add (BitVec.ofNat 64 x) i) := by
    intro i hi
    have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := by
      rw [toNat_add_of_fits (a := BitVec.ofNat 64 x) (n := 8) hi (by omega), t0]
    have hDa := hD i hi
    generalize Addr.add (BitVec.ofNat 64 x) i = a at hx' hDa ⊢
    rw [hW a (.inl hDa) ?_ ?_]
    · unfold PtrMem
      rw [Vst_out, ver_tls V ver hb' (by omega) (by omega) (by omega),
        TlsMem_out _ hb hb' (by unfold TlsVar; omega) (by omega)]
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
  rw [rd_ext (W' := W) (W := V) (BitVec.ofNat 64 x) 8 h]

/-- The same word in `lif_ok`'s bytes, below `0x7a85c8` (`Lif.LifMem`'s globals). -/
theorem ent_gl {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} {x : Nat}
    (hx : 0x7a8418 ≤ x ∧ x + 8 ≤ 0x7a8520 ∨ 0x7a8580 ≤ x ∧ x + 8 ≤ 8029640)
    (hr : x + 8 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + 8 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      BitVec.ofNat 64 x) = rdq(W, BitVec.ofNat 64 x) := by
  have t0 : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h : ∀ i < 8, Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64)
      (toBytesLE ra 8)) sp gY (Addr.add (BitVec.ofNat 64 x) i) = W (Addr.add (BitVec.ofNat 64 x) i) := by
    intro i hi
    have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := by
      rw [toNat_add_of_fits (a := BitVec.ofNat 64 x) (n := 8) hi (by omega), t0]
    exact ent_keep (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩
  rw [rd_ext (BitVec.ofNat 64 x) 8 h]

/-- `h2` and `h3` of `lif_ok`: `_dl_phdr` is `0x400040` and `_dl_phnum` 8. -/
theorem ent_phd {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hM : MB K V) (hph : (K.vs K.M).phdr = 0x400040#64)
    (hpn : (K.vs K.M).phnum = 8#64) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD1 : ∀ i < 8, D (Addr.add 8029568#64 i)) (hD2 : ∀ i < 8, D (Addr.add 8029592#64 i))
    (hr : 8029600 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 8029600 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8029568#64) = 4194368#64 ∧
      rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8029592#64) = 8#64 :=
  ⟨((ent_gl (x := 8029568) (.inr ⟨by omega, by omega⟩) (by omega) hr' (by omega) hsn).trans
      (ptr_gl (x := 8029568) hb hb' hbp hW hD1 (.inr ⟨by omega, by omega⟩))).trans (hM.gl.phdr.trans hph),
    ((ent_gl (x := 8029592) (.inr ⟨by omega, by omega⟩) (by omega) hr' (by omega) hsn).trans
      (ptr_gl (x := 8029592) hb hb' hbp hW hD2 (.inr ⟨by omega, by omega⟩))).trans (hM.gl.phnum.trans hpn)⟩

end FV7z.Start
