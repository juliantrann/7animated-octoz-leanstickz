import FV7z.Start.Reach
/-!
# A code list for `7zzs`: its executable segment (PLAN.md §M, the theorem against vacuity)

`launch_to_main` names a list `L` of code segments, each the file's bytes at its address in the executable segment
(`hL`), and asks for the code of each function the run reaches in it (`StartCode`, `TlsCode`, `OsvCode`, `PimCode`,
`LifCode`, `MalCode`, `CxaCode`, `MainCode`, `Ctor.CtorCode`). The list of one segment, the whole file part of the
executable `PT_LOAD` segment (`0x401000` to `0x6d767d`, `0x2d667d` bytes), has them all: each function's bytes
(`*_pin`) are a stretch of it, since no other loadable segment's file part meets `0x401000` to `0x6d767d`
(`text_only`). The segment's bytes stay a variable `T` with `Exe.bytesAt … = some T` (`text_some`), so that no
elaboration or kernel check ever evaluates the 3 MB list.

- `segL T`: the list; `seg_at`: bytes `Exe.bytesAt` reads at an address of the segment are a stretch of `T`.
- `seg_hL`: `segL T` is the file's bytes (`hL`).
- `codeIn_text`, `text_any`: `CodeIn (segL T)` of each function's pinned bytes, and of some byte at each address of
  the segment.
- `start_text` … `ctor_text`: the bundles; `text_code`: a list with `hL` and all of them.
-/
namespace FV7z.Start
open ZellicX86 FV7z
set_option maxRecDepth 100000

/-- The code list of one segment: the bytes `T` at `0x401000`. -/
def segL (T : List Byte) : List (Addr × List Byte) := [(0x401000#64, T)]

theorem mem_segL (T : List Byte) : (0x401000#64, T) ∈ segL T := List.mem_singleton_self _

/-- The loadable segments: the executable one, or one whose file part ends before `0x401000` or starts at
`0x6d767d` or later (by the kernel's evaluation of the ELF reader on the file). -/
theorem text_only : zzsPhdrs.all (fun p => p.type != PT_LOAD ||
    (p.vaddr == 0x401000 && p.offset == 0x1000 && p.filesz == 0x2d667d) ||
    decide (p.vaddr + p.filesz ≤ 0x401000) || decide (0x6d767d ≤ p.vaddr)) = true := by decide +kernel

/-- A loadable segment whose file part holds a byte at `0x401000` to `0x6d767d` is the executable one. -/
theorem text_phdr {p : Phdr} (hp : p ∈ zzsPhdrs) (hty : p.type = PT_LOAD) {x : Nat} (hlo : p.vaddr ≤ x)
    (hhi : x < p.vaddr + p.filesz) (ha : 0x401000 ≤ x) (ha' : x < 0x6d767d) :
    p.vaddr = 0x401000 ∧ p.offset = 0x1000 ∧ p.filesz = 0x2d667d := by
  have hq := List.all_eq_true.1 text_only p hp
  simp only [hty, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hq
  rcases hq with (⟨⟨hv, ho⟩, hf⟩ | h1) | h2
  · exact ⟨hv, ho, hf⟩
  · omega
  · omega

theorem seg_len {a N : Nat} {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob a N = some T) : T.length = N := by
  obtain ⟨q, -, -, -, -, hb⟩ := bytesAt_some hT
  rw [hb, List.length_map, List.length_range]

/-- What `Exe.bytesAt` reads at an address of the executable segment is a stretch of what it reads from the
segment's start `0x401000`: the bytes from the address's distance from `0x401000` on. -/
theorem seg_at {a n N : Nat} {bs T : List Byte} (h : Exe.bytesAt V2606.zzs.blob a n = some bs)
    (hT : Exe.bytesAt V2606.zzs.blob 0x401000 N = some T) (hN : 0x2d667d ≤ N) (ha : 0x401000 ≤ a) (ha' : a < 0x6d767d) :
    bs = (T.drop (a - 0x401000)).take n := by
  obtain ⟨p, hp, hty, hlo, hhi, rfl⟩ := bytesAt_some h
  obtain ⟨q, hq, hqt, hqlo, hqhi, rfl⟩ := bytesAt_some hT
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [List.range_zero, List.map_nil, List.take_zero]
  obtain ⟨hv, ho, hf⟩ := text_phdr hp hty hlo (by omega) ha ha'
  obtain ⟨hv', ho', hf'⟩ := text_phdr hq hqt hqlo (by omega) (Nat.le_refl _) (by decide)
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_take, List.length_drop, List.length_map,
      List.length_range]
    omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, hv, ho, hv', ho',
      Nat.add_assoc, Nat.sub_self, Nat.add_zero, Nat.zero_add]

/-- The executable segment's file part, `0x2d667d` bytes (by the kernel's evaluation of the ELF reader). -/
theorem text_some : (Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d).isSome = true := by decide +kernel

theorem seg_hL {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    ∀ p ∈ segL T, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2 := by
  intro p hp
  simp only [segL, List.mem_singleton] at hp
  subst hp
  have hl := seg_len hT
  refine ⟨0x401000, rfl, Nat.le_refl _, ?_, ?_⟩
  · show 0x401000 + T.length ≤ 0x6d8000
    rw [hl]
    decide
  · show Exe.bytesAt V2606.zzs.blob 0x401000 T.length = some T
    rw [hl]
    exact hT

theorem addr_off {x b : Addr} (h : b.toNat ≤ x.toNat) : x = Addr.add b (x.toNat - b.toNat) := by
  have := x.isLt
  have := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem text_addr {x : Addr} (ha : 0x401000 ≤ x.toNat) : x = Addr.add 0x401000#64 (x.toNat - 0x401000) := by
  have t : (0x401000#64 : Addr).toNat = 0x401000 := by decide
  have e := addr_off (b := 0x401000#64) (x := x) (by rw [t]; exact ha)
  rwa [t] at e

theorem nat_text {a : Nat} (h : 0x401000 ≤ a ∧ a < 0x6d767d) :
    0x401000 ≤ (BitVec.ofNat 64 a).toNat ∧ (BitVec.ofNat 64 a).toNat < 0x6d767d := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.2 (by decide))]
  exact h

section
variable {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T)
include hT

/-- The bytes `Exe.bytesAt` reads at an address of the executable segment are code of `segL T`. -/
theorem codeIn_text {a n : Nat} {bs : List Byte} (h : Exe.bytesAt V2606.zzs.blob a n = some bs)
    (ha : 0x401000 ≤ a) (ha' : a < 0x6d767d) : CodeIn (segL T) (BitVec.ofNat 64 a) bs := by
  have e := seg_at h hT (Nat.le_refl _) ha ha'
  have t : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans ha' (by decide))]
  have ea : BitVec.ofNat 64 a = Addr.add 0x401000#64 (a - 0x401000) := by
    have := text_addr (x := BitVec.ofNat 64 a) (by rw [t]; exact ha)
    rwa [t] at this
  rw [e]
  exact ⟨(0x401000#64, T), mem_segL T, a - 0x401000, ea, List.take_prefix _ _⟩

/-- Some byte at each address of the executable segment is code of `segL T`. -/
theorem text_any {x : Addr} (ha : 0x401000 ≤ x.toNat) (ha' : x.toNat < 0x6d767d) :
    ∃ c, CodeIn (segL T) x c ∧ 0 < c.length := by
  have hl := seg_len hT
  refine ⟨(T.drop (x.toNat - 0x401000)).take 1, ⟨(0x401000#64, T), mem_segL T, x.toNat - 0x401000,
    text_addr ha, List.take_prefix _ _⟩, ?_⟩
  rw [List.length_take, List.length_drop, hl]
  omega

end

/-! ## The bundles -/

theorem res_text : ∀ r ∈ Glibc.V2606.resolvers, 0x401000 ≤ r.1 ∧ r.1 < 0x6d767d := by decide +kernel

theorem plt_text : ∀ a ∈ lifPlt, 0x401000 ≤ a ∧ a < 0x6d767d := by decide +kernel

theorem tg_text : ∀ i < 104, 0x401000 ≤ (csuTg i).toNat ∧ (csuTg i).toNat < 0x6d767d := by decide +kernel

theorem start_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    StartCode (segL T) where
  ent := codeIn_text hT Entry.ent_pin (by decide) (by decide)
  lsm := codeIn_text hT lsm_pin (by decide) (by decide)
  pie := codeIn_text hT Pie.pie_pin (by decide) (by decide)
  aux := codeIn_text hT Auxv.aux_pin (by decide) (by decide)
  sec := codeIn_text hT Sec.sec_pin (by decide) (by decide)
  tin := codeIn_text hT Tun.tin_pin (by decide) (by decide)
  icf := codeIn_text hT CpuFeat.icf_pin (by decide) (by decide)
  icfk := codeIn_text hT CpuFeat.icfk_pin (by decide) (by decide)
  tgv := codeIn_text hT CpuFeat.tgv_pin (by decide) (by decide)
  gci := codeIn_text hT CpuFeat.gci_pin (by decide) (by decide)
  icfa := codeIn_text hT CpuFeat.icfa_pin (by decide) (by decide)
  icfh := codeIn_text hT CpuFeat.icfh_pin (by decide) (by decide)
  icfi := codeIn_text hT CpuFeat.icfi_pin (by decide) (by decide)
  irl := codeIn_text hT CpuFeat.irl_pin (by decide) (by decide)
  next := text_any hT (by decide) (by decide)
  res := fun r hr _ h => codeIn_text hT h (res_text r hr).1 (res_text r hr).2

theorem tls_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    TlsCode (segL T) where
  tls := codeIn_text hT Tls.tls_pin (by decide) (by decide)
  sbk := codeIn_text hT Sbrk.sbk_pin (by decide) (by decide)
  brk := codeIn_text hT Brk.brk_pin (by decide) (by decide)
  cpy := text_any hT (by decide) (by decide)

theorem osv_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    OsvCode (segL T) where
  osv := codeIn_text hT Osv.osv_pin (by decide) (by decide)
  unm := codeIn_text hT Uname.unm_pin (by decide) (by decide)

theorem pim_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    StartB.PimCode (segL T) where
  pim := codeIn_text hT Pim.pim_pin (by decide) (by decide)
  sga := codeIn_text hT Sga.sga_pin (by decide) (by decide)
  gts := codeIn_text hT Gts.gts_pin (by decide) (by decide)
  grl := codeIn_text hT Grl.grl_pin (by decide) (by decide)
  lpi := codeIn_text hT Lpi.lpi_pin (by decide) (by decide)
  raf := codeIn_text hT Raf.raf_pin (by decide) (by decide)
  pti := codeIn_text hT Pti.pti_pin (by decide) (by decide)
  tgv := codeIn_text hT Tgv.tgv_pin (by decide) (by decide)

theorem lif_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    LifCode (segL T) where
  lif := codeIn_text hT Lif.lif_pin (by decide) (by decide)
  ndi := codeIn_text hT Ndi.ndi_pin (by decide) (by decide)
  gev := codeIn_text hT Genv.gev_pin (by decide) (by decide)
  gor := codeIn_text hT Gor.gor_pin (by decide) (by decide)
  ipa := codeIn_text hT Ipa.ipa_pin (by decide) (by decide)
  hwc := codeIn_text hT Hwc.hwc_pin (by decide) (by decide)
  mnx := codeIn_text hT Mnx.mnx_pin (by decide) (by decide)
  imm := codeIn_text hT Imm.imm_pin (by decide) (by decide)
  tgv := codeIn_text hT Tgv.tgv_pin (by decide) (by decide)
  dpr := codeIn_text hT Dpr.dpr_pin (by decide) (by decide)
  mpr := codeIn_text hT Mpr.mpr_pin (by decide) (by decide)
  ims := codeIn_text hT Ims.ims_pin (by decide) (by decide)
  cti := codeIn_text hT Cti.cti_pin (by decide) (by decide)
  plt := fun a ha => text_any hT (nat_text (plt_text a ha)).1 (nat_text (plt_text a ha)).2

theorem mal_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    MalCode (segL T) where
  mal := codeIn_text hT Mal.mal_pin (by decide) (by decide)
  mhi := codeIn_text hT Mhi.mhi_pin (by decide) (by decide)
  pmi := codeIn_text hT Pmi.pmi_pin (by decide) (by decide)
  tgv := codeIn_text hT Tgv.tgv_pin (by decide) (by decide)
  tci := codeIn_text hT Tci.tci_pin (by decide) (by decide)
  imm := codeIn_text hT Imm.imm_pin (by decide) (by decide)
  smm := codeIn_text hT Smm.smm_pin (by decide) (by decide)
  dmc := codeIn_text hT Dmc.dmc_pin (by decide) (by decide)
  sbk := codeIn_text hT Sbrk.sbk_pin (by decide) (by decide)
  brk := codeIn_text hT Brk.brk_pin (by decide) (by decide)

theorem cxa_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    CxaCode (segL T) where
  cxa := codeIn_text hT Cxa.cxa_pin (by decide) (by decide)
  nef := codeIn_text hT Nef.nef_pin (by decide) (by decide)

theorem main_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    MainCode (segL T) where
  dbg := codeIn_text hT Dbg.dbg_pin (by decide) (by decide)
  sjp := codeIn_text hT Sjp.sjp_pin (by decide) (by decide)
  ssj := codeIn_text hT Ssj.ssj_pin (by decide) (by decide)
  csu := codeIn_text hT Csu.csu_pin (by decide) (by decide)
  main := text_any hT (by decide) (by decide)
  tcode := fun i hi => text_any hT (tg_text i hi).1 (tg_text i hi).2
  eli := codeIn_text hT Eli.eli_pin (by decide) (by decide)
  tgv := codeIn_text hT Tgv.tgv_pin (by decide) (by decide)
  ini := codeIn_text hT Ini.ini_pin (by decide) (by decide)
  fdm := codeIn_text hT Fdm.fdm_pin (by decide) (by decide)
  rtc := codeIn_text hT Rtc.rtc_pin (by decide) (by decide)
  rfi := codeIn_text hT Rfi.rfi_pin (by decide) (by decide)
  pml := codeIn_text hT Pml.pml_pin (by decide) (by decide)
  pmu := codeIn_text hT Pmu.pmu_pin (by decide) (by decide)

/-- `endbr64; ret` at `0x43cd90`, the file's. -/
theorem nret_pin : Exe.bytesAt V2606.zzs.blob 0x43cd90 5 = some Ctor.nret := by decide +kernel

theorem reg_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    ∀ r, CodeIn (segL T) (Ctor.regAt r) (Ctor.regCode r)
  | 0 => codeIn_text hT Rga.rga_pin (by decide) (by decide)
  | 1 => codeIn_text hT Rgc.rgc_pin (by decide) (by decide)
  | _ + 2 => show CodeIn (segL T) 0x458e90 Rgh.rgh from codeIn_text hT Rgh.rgh_pin (by decide) (by decide)

theorem ctor_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    Ctor.CtorCode (segL T) where
  hin := codeIn_text hT Ctor.sti_pin (by decide) (by decide)
  hinN := codeIn_text hT nret_pin (by decide) (by decide)
  hinR := reg_text hT
  i3 := codeIn_text hT C3.c3_pin (by decide) (by decide)
  i15 := codeIn_text hT C15.c15_pin (by decide) (by decide)
  i78 := codeIn_text hT C78.c78_pin (by decide) (by decide)
  iF17 := codeIn_text hT Ctor.cf17_pin (by decide) (by decide)
  iU17 := codeIn_text hT Ctor.umk_pin (by decide) (by decide)
  iLz := codeIn_text hT Prepare.lz_pin (by decide) (by decide)
  iSse41 := codeIn_text hT Prepare.sse41_pin (by decide) (by decide)
  iAvx2 := codeIn_text hT Prepare.avx2_pin (by decide) (by decide)
  iAvx := codeIn_text hT Prepare.avx_pin (by decide) (by decide)
  iMaxf := codeIn_text hT Prepare.maxf_pin (by decide) (by decide)
  iCpuid := codeIn_text hT Prepare.cpuid_pin (by decide) (by decide)
  iSha1p := codeIn_text hT Prepare.sha1p_pin (by decide) (by decide)
  iSha := codeIn_text hT Prepare.sha_pin (by decide) (by decide)
  iSsse3 := codeIn_text hT Prepare.ssse3_pin (by decide) (by decide)
  iSha256p := codeIn_text hT Prepare.sha256p_pin (by decide) (by decide)
  iAesg := codeIn_text hT Prepare.aesg_pin (by decide) (by decide)
  iAes := codeIn_text hT Prepare.aes_pin (by decide) (by decide)
  iVaes := codeIn_text hT Prepare.vaes_pin (by decide) (by decide)
  iB2s := codeIn_text hT Prepare.b2s_pin (by decide) (by decide)
  iSwap := codeIn_text hT Prepare.swap_pin (by decide) (by decide)
  iMxs := codeIn_text hT Mxs.mxs_pin (by decide) (by decide)
  iMxi := codeIn_text hT Mxi.mxi_pin (by decide) (by decide)
  iCxa := codeIn_text hT Cxa.cxa_pin (by decide) (by decide)
  iNef := codeIn_text hT Nef.nef_pin (by decide) (by decide)
  iOin := codeIn_text hT Oin.oin_pin (by decide) (by decide)
  iNst := codeIn_text hT Nst.nst_pin (by decide) (by decide)
  iOnw := codeIn_text hT Onw.onw_pin (by decide) (by decide)
  iMnx := codeIn_text hT Mnx.mnx_pin (by decide) (by decide)
  iImm := codeIn_text hT Imm.imm_pin (by decide) (by decide)
  iHca := codeIn_text hT Hca.hca_pin (by decide) (by decide)

/-- A code list with all `launch_to_main` asks of it: the executable segment of `7zzs`. -/
theorem text_code : ∃ L : List (Addr × List Byte),
    (∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) ∧
    StartCode L ∧ TlsCode L ∧ OsvCode L ∧ StartB.PimCode L ∧ LifCode L ∧ MalCode L ∧ CxaCode L ∧ MainCode L ∧
    Ctor.CtorCode L := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 text_some
  exact ⟨segL T, seg_hL hT, start_text hT, tls_text hT, osv_text hT, pim_text hT, lif_text hT, mal_text hT,
    cxa_text hT, main_text hT, ctor_text hT⟩

end FV7z.Start
