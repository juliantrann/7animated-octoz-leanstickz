import FV7z.Start.ToCpu
import FV7z.Tls.Holds
/-!
# What `__libc_setup_tls` reads, at `0x6133bb` of a run of `7zzs` (PLAN.md G3, startup)

`Tls.In` asks for the bytes `__libc_setup_tls` reads at its entry. Here they are had from the launch: the auxiliary
vector's `AT_PHDR` and `AT_PHNUM`, which `_dl_aux_init` stored, and the file's bytes, which the startup up to
`0x6133bb` has not stored to.

- `auxv_ph`, `auxv_idx5`, `zzs_phnum`: every `AT_PHNUM` (5) of the vector `execve` writes has the header's number of
  program headers, 8 for `7zzs`.
- `vsOf_phdr`, `vsOf_phnum`, `ctxOf_ph`: `_dl_phdr` is `0x400040` and `_dl_phnum` 8 after `_dl_aux_init`.
- `phb`: the first six program headers in the file; `dm_map`, `dm_laddr`, `dm_ssize`: the words of `.data` at
  `0x793440` (the main map's address), `0x7934e0` (its `l_addr`) and `0x7922b0` (`_dl_tls_static_size`).
- `cpuW_fine`: where `init_cpu_features` and `apply_irel` store.
- `tls_in`: `Tls.In V` for bytes `V` that are those of `FinP` (`MB`) outside what those two store to.
-/
namespace FV7z.Start
open ZellicX86 FV7z FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (cpuW icfW irelW)
open FV7z.Auxv (Gl)

/-! ## `AT_PHNUM` -/

theorem auxv_ph (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
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

/-- The vector by index: there is an `AT_PHNUM`, and each has the header's number of program headers. -/
theorem auxv_idx5 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    (∃ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 5) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 5 →
      ((auxv prof hdr pa a c l).getD n (0, 0)).2 = hdr.phnum) := by
  obtain ⟨pre, hA, hnz, h5, m5⟩ := auxv_ph prof hdr pa a c l
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
    have h' : BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 5 := h
    have := congrArg BitVec.toNat h'
    have b := (hnz _ (hin n hn)).2
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- `7zzs` has 8 program headers. -/
theorem zzs_phnum : (ElfHeader.read V2606.zzs.blob.bytes).phnum = 8 := by decide +kernel

/-! ## `_dl_phdr` and `_dl_phnum` after `_dl_aux_init` -/

theorem step_phdr (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).phdr = if e.1 = 3 then e.2 else v.phdr := by
  simp only [AuxInit.step, apply_ite Vars.phdr]
  repeat' split
  all_goals rfl

theorem step_phnum (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).phnum = if e.1 = 3 then v.phnum else if e.1 = 5 then e.2 else v.phnum := by
  simp only [AuxInit.step, apply_ite Vars.phnum]
  repeat' split
  all_goals rfl

/-- `_dl_phdr` after a vector with an `AT_PHDR`, each with the value `x`. -/
theorem vsOf_phdr {ty val : Nat → BitVec 64} {w : Vars} {x : BitVec 64} :
    ∀ M, (∃ n < M, ty n = 3) → (∀ n < M, ty n = 3 → val n = x) → (vsOf ty val w M).phdr = x
  | 0, ⟨_, hn, _⟩, _ => absurd hn (Nat.not_lt_zero _)
  | M + 1, ⟨n, hn, h3⟩, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).phdr = x
    rw [step_phdr]
    split
    · next hM => exact hall M (Nat.lt_succ_self _) hM
    · next hM =>
      have hlt : n < M := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
        · exact h
        · exact absurd (h ▸ h3) hM
      exact vsOf_phdr M ⟨n, hlt, h3⟩ fun k hk => hall k (Nat.lt_succ_of_lt hk)

/-- `_dl_phnum` after a vector with an `AT_PHNUM`, each with the value `x`. -/
theorem vsOf_phnum {ty val : Nat → BitVec 64} {w : Vars} {x : BitVec 64} :
    ∀ M, (∃ n < M, ty n = 5) → (∀ n < M, ty n = 5 → val n = x) → (vsOf ty val w M).phnum = x
  | 0, ⟨_, hn, _⟩, _ => absurd hn (Nat.not_lt_zero _)
  | M + 1, ⟨n, hn, h5⟩, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).phnum = x
    rw [step_phnum]
    have ih : ty M ≠ 5 → (vsOf ty val w M).phnum = x := fun hM => by
      have hlt : n < M := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
        · exact h
        · exact absurd (h ▸ h5) hM
      exact vsOf_phnum M ⟨n, hlt, h5⟩ fun k hk => hall k (Nat.lt_succ_of_lt hk)
    split
    · next h3 =>
      have h3' : ty M = 3 := h3
      exact ih (by rw [h3']; decide)
    · split
      · next hM => exact hall M (Nat.lt_succ_self _) hM
      · next hM => exact ih hM

/-- After `_dl_aux_init`, in a run of `7zzs`: `_dl_phdr` is `0x400040`, `_dl_phnum` is 8. -/
theorem ctxOf_ph (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).phdr = 0x400040#64 ∧
      ((ctxOf prof s a c).vs (ctxOf prof s a c).M).phnum = 8#64 := by
  obtain ⟨-, -, -, -, e3, h3⟩ := auxv_idx prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  obtain ⟨e5, h5⟩ := auxv_idx5 prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  constructor
  · refine vsOf_phdr _ e3 fun n hn h => ?_
    show BitVec.ofNat 64 _ = _
    rw [h3 n hn h, zzs_phdrAddr]
  · refine vsOf_phnum _ e5 fun n hn h => ?_
    show BitVec.ofNat 64 _ = _
    rw [h5 n hn h, zzs_phnum]

/-! ## The file's bytes -/

/-- The first six program headers of `7zzs` (`0x400040`, 56 bytes each); the sixth is `PT_TLS`. -/
def phb : List Byte := [
  0x01, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x30, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x30, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00,
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x10, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7d, 0x66, 0x2d, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x7d, 0x66, 0x2d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x01, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x80, 0x2d, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x80, 0x6d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x6d, 0x00, 0x00, 0x00, 0x00, 0x00,
  0xe9, 0xdb, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe9, 0xdb, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00,
  0x70, 0x67, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x77, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x70, 0x77, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0xce, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x50, 0x0f, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x04, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x02, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x44, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x44, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
  0x70, 0x67, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x77, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x70, 0x77, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem phb_pin : Exe.bytesAt V2606.zzs.blob 0x400040 336 = some phb := by decide +kernel
theorem phb_length : phb.length = 336 := by decide +kernel

/-- None of the first five is `PT_TLS`. -/
theorem phb_nt : ∀ i < 5, ofBytesLE 32 ((phb.drop (56 * i)).take 4) ≠ 7#32 := by decide +kernel

/-- The sixth: `PT_TLS`, at `0x777770`, 40 bytes in the file, 128 in memory, aligned to 8. -/
theorem phb_tls : ofBytesLE 32 ((phb.drop 280).take 4) = 7#32 ∧ ofBytesLE 64 ((phb.drop 296).take 8) = 7829360#64 ∧
    ofBytesLE 64 ((phb.drop 312).take 8) = 40#64 ∧ ofBytesLE 64 ((phb.drop 320).take 8) = 128#64 ∧
    ofBytesLE 64 ((phb.drop 328).take 8) = 8#64 := by decide +kernel

/-- `_dl_ns[0]._ns_loaded` (`0x793440`): the main map, at `0x7934e0`. -/
theorem dm_map : Exe.bytesAt V2606.zzs.blob 0x793440 8 = some [0xe0, 0x34, 0x79, 0, 0, 0, 0, 0] := by decide +kernel

/-- The main map's `l_addr` (`0x7934e0`): 0. -/
theorem dm_laddr : Exe.bytesAt V2606.zzs.blob 0x7934e0 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

/-- `_dl_tls_static_size` (`0x7922b0`): 2048. -/
theorem dm_ssize : Exe.bytesAt V2606.zzs.blob 0x7922b0 8 = some [0, 8, 0, 0, 0, 0, 0, 0] := by decide +kernel

/-! ## The bytes at `0x6133bb` -/

/-- Where `init_cpu_features` and `apply_irel` store, their frame at `q` above the image. -/
theorem cpuW_fine {q a : Addr} (hq : 0x7a9000 + 256 ≤ q.toNat) (hq' : q.toNat + 128 ≤ 2 ^ 64)
    (h : Foot (cpuW q) a) : 0x7a9000 ≤ a.toNat ∨ (0x792018 ≤ a.toNat ∧ a.toNat < 0x792110) ∨
      (0x7a4ac8 ≤ a.toNat ∧ a.toNat < 0x7a4b88) ∨ (0x7a8548 ≤ a.toNat ∧ a.toNat < 0x7a8550) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  simp only [cpuW, icfW, irelW, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Addr.add, BitVec.reduceToNat] at h1 h2 <;> bv_omega

/-- The bytes of the image `init_cpu_features` and `apply_irel` store to: the GOT's slots, `_dl_hwcap` and
`_dl_x86_cpu_features`, `_dl_platform`. -/
def CpuVar (a : Addr) : Prop :=
  (0x792018 ≤ a.toNat ∧ a.toNat < 0x792110) ∨ (0x7a4ac8 ≤ a.toNat ∧ a.toNat < 0x7a4b88) ∨
    (0x7a8548 ≤ a.toNat ∧ a.toNat < 0x7a8550)

theorem not_dg {lo hi : Nat} (h : ∀ r ∈ d3 ++ globals, r.base.toNat + r.len ≤ lo ∨ hi ≤ r.base.toNat) {a : Addr}
    (h1 : lo ≤ a.toNat) (h2 : a.toNat < hi) : ¬ Foot (d3 ++ globals) a := by
  rintro ⟨r, hr, m1, m2⟩
  rcases h r hr with h | h <;> omega

theorem dg_lo : ∀ r ∈ d3 ++ globals, 0x791ca0 ≤ r.base.toNat := by decide

/-- A read of the image at `0x6133bb`, of bytes not stored to since the entry. -/
theorem rd_fin {K : Ctx} {V V' : Addr → Byte} (hK : K.Ok) (hS : Same K (d3 ++ globals) V')
    (hV : ∀ a : Addr, (0x400000 ≤ a.toNat ∧ a.toNat < 0x401000) ∨ (0x777000 ≤ a.toNat ∧ a.toNat < 0x7a9000) →
      ¬ CpuVar a → V a = V' a) (b n : Nat)
    (hb : (0x400000 ≤ b ∧ b + n ≤ 0x401000) ∨ (0x777000 ≤ b ∧ b + n ≤ 0x7a9000))
    (hd : ∀ r ∈ d3 ++ globals, r.base.toNat + r.len ≤ b ∨ b + n ≤ r.base.toNat)
    (hc : b + n ≤ 0x792018 ∨ (0x792110 ≤ b ∧ b + n ≤ 0x7a4ac8) ∨ (0x7a4b88 ≤ b ∧ b + n ≤ 0x7a8548) ∨ 0x7a8550 ≤ b) :
    List.map V (byteAddrs (BitVec.ofNat 64 b) n) = List.map K.V0 (byteAddrs (BitVec.ofNat 64 b) n) := by
  have := hK.himg
  refine rd_congr fun i hi => ?_
  have e := tg hi (b := b) (by omega)
  rw [hV _ (by omega) (by unfold CpuVar; omega)]
  exact hS _ (by simp only [InStk]; omega) (not_dg hd (by omega) (by omega))

/-- A read of the file's bytes, whole. -/
theorem Img.rd {V : Addr → Byte} (h : Img V) {a n : Nat} {bs : List Byte}
    (hp : Exe.bytesAt V2606.zzs.blob a n = some bs) (hl : bs.length = n) (hlo : 0x400000 ≤ a)
    (hhi : a + n ≤ 0x7a9000) : List.map V (byteAddrs (BitVec.ofNat 64 a) n) = bs := by
  subst hl
  have := h.map hp rfl hlo hhi (off := 0) (m := bs.length) (Nat.le_of_eq (Nat.zero_add _))
  rw [List.drop_zero, List.take_length] at this
  exact this

/-- What `__libc_setup_tls` reads at its entry, in a run of `7zzs`: `V` the bytes at `0x6133bb`, those of `FinP`
(`V'`) outside what `init_cpu_features` and `apply_irel` store to. -/
theorem tls_in {K : Ctx} {V V' : Addr → Byte} (hK : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V')
    (hph : (K.vs K.M).phdr = 0x400040#64) (hpn : (K.vs K.M).phnum = 8#64)
    (hV : ∀ a : Addr, (0x400000 ≤ a.toNat ∧ a.toNat < 0x401000) ∨ (0x777000 ≤ a.toNat ∧ a.toNat < 0x7a9000) →
      ¬ CpuVar a → V a = V' a) : Tls.In V := by
  have rv : ∀ b n : Nat, 0x7a8550 ≤ b → b + n ≤ 0x7a9000 →
      List.map V (byteAddrs (BitVec.ofNat 64 b) n) = List.map V' (byteAddrs (BitVec.ofNat 64 b) n) := by
    intro b n h1 h2
    refine rd_congr fun i hi => ?_
    have e := tg hi (b := b) (by omega)
    exact hV _ (by omega) (by unfold CpuVar; omega)
  have hdr : ∀ off m, off + m ≤ 336 →
      List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + off)) m) = (phb.drop off).take m := by
    intro off m h
    rw [rd_fin hK hM.same hV (0x400040 + off) m (.inl ⟨by omega, by omega⟩)
      (fun r hr => .inr (by have := dg_lo r hr; omega)) (.inl (by omega))]
    exact hI.map phb_pin phb_length (by decide) (by decide) h
  obtain ⟨t1, t2, t3, t4, t5⟩ := phb_tls
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x7a8580) 8)) = _
    rw [rv 0x7a8580 8 (by decide) (by decide)]
    exact hM.gl.phdr.trans hph
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x7a8598) 8)) = _
    rw [rv 0x7a8598 8 (by decide) (by decide)]
    exact hM.gl.phnum.trans hpn
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x793440) 8)) = _
    rw [rd_fin hK hM.same hV 0x793440 8 (by decide) (by decide) (by decide),
      hI.rd dm_map rfl (by decide) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x7934e0) 8)) = _
    rw [rd_fin hK hM.same hV 0x7934e0 8 (by decide) (by decide) (by decide),
      hI.rd dm_laddr rfl (by decide) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x7922b0) 8)) = _
    rw [rd_fin hK hM.same hV 0x7922b0 8 (by decide) (by decide) (by decide),
      hI.rd dm_ssize rfl (by decide) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 0x7a4c38) 8)) = _
    rw [rd_fin hK hM.same hV 0x7a4c38 8 (by decide) (by decide) (by decide),
      rd_congr (V := fun _ => (0 : Byte)) fun i hi => hB _
        (by have e := tg hi (b := 0x7a4c38) (by decide); omega)
        (by have e := tg hi (b := 0x7a4c38) (by decide); omega)]
    rfl
  · intro i hi
    have := hdr (56 * i) 4 (by omega)
    show ofBytesLE 32 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 56 * i)) 4)) ≠ _
    rw [this]
    exact phb_nt i hi
  · have := hdr 280 4 (by decide)
    show ofBytesLE 32 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 280)) 4)) = _
    rw [this]
    exact t1
  · have := hdr 296 8 (by decide)
    show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 296)) 8)) = _
    rw [this]
    exact t2
  · have := hdr 312 8 (by decide)
    show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 312)) 8)) = _
    rw [this]
    exact t3
  · have := hdr 320 8 (by decide)
    show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 320)) 8)) = _
    rw [this]
    exact t4
  · have := hdr 328 8 (by decide)
    show ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 (0x400040 + 328)) 8)) = _
    rw [this]
    exact t5

end FV7z.Start
