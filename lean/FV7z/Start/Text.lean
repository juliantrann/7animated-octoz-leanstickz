import FV7z.Start.Reach
/-!
# A code list for `7zzs`: its executable segment (PLAN.md §M, the theorem against vacuity)

`launch_to_main` names a list `L` of code segments, each the file's bytes at its address in the executable segment
(`hL`), and asks for the code of each function the run reaches in it (`StartCode`, `TlsCode`, `OsvCode`, `PimCode`,
`LifCode`, `MalCode`, `CxaCode`, `MainCode`, `Ctor.CtorCode`). The list of one segment, the whole file part of the
executable `PT_LOAD` segment (`0x401000` to `0x6d767d`, `0x2d667d` bytes from the file's offset `0x1000`), has them
all: each function's bytes (`*_pin`) are a stretch of it, since no other loadable segment's file part meets
`0x401000` to `0x6d767d` (`text_only`).

- `textB`, `textL`: the segment's bytes and the list.
- `text_at`: bytes `Exe.bytesAt` reads at an address of the segment are its bytes from there.
- `text_pin`: `textL`'s segment is the file's (`hL`).
- `codeIn_text`, `text_any`: so `CodeIn textL` holds of each function's pinned bytes, and of some byte at each
  address of the segment.
- `start_text` … `ctor_text`: the bundles `launch_to_main` asks for.
-/
namespace FV7z.Start
open ZellicX86 FV7z

/-- The file part of the executable segment of `7zzs`: `0x2d667d` bytes from the file's offset `0x1000`. -/
noncomputable def textB : List Byte := (List.range 0x2d667d).map fun i => V2606.zzs.blob.bytes (0x1000 + i)

/-- The code list of one segment, `textB` at `0x401000`. -/
noncomputable def textL : List (Addr × List Byte) := [(0x401000#64, textB)]

theorem textB_length : textB.length = 0x2d667d := by
  simp only [textB, List.length_map, List.length_range]

/-- The loadable segments: the executable one, or one whose file part ends before `0x401000` or starts at
`0x6d767d` or later (by the kernel's evaluation of the ELF reader on the file). -/
theorem text_only : zzsPhdrs.all (fun p => p.type != PT_LOAD ||
    (p.vaddr == 0x401000 && p.offset == 0x1000 && p.filesz == 0x2d667d) ||
    decide (p.vaddr + p.filesz ≤ 0x401000) || decide (0x6d767d ≤ p.vaddr)) = true := by decide +kernel

/-- What `Exe.bytesAt` reads at an address of the executable segment is the file's bytes at the segment's offset
plus the address's distance from `0x401000`, and ends in the segment. -/
theorem text_at {a n : Nat} {bs : List Byte} (h : Exe.bytesAt V2606.zzs.blob a n = some bs)
    (ha : 0x401000 ≤ a) (ha' : a < 0x6d767d) :
    a + n ≤ 0x6d767d ∧ bs = (List.range n).map fun i => V2606.zzs.blob.bytes (0x1000 + (a - 0x401000) + i) := by
  obtain ⟨p, hp, hty, hlo, hhi, rfl⟩ := bytesAt_some h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨by omega, by simp only [List.range_zero, List.map_nil]⟩
  have hq := List.all_eq_true.1 text_only p hp
  simp only [hty, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hq
  rcases hq with (⟨⟨hv, ho⟩, hf⟩ | h1) | h2
  · rw [hv, ho]
    exact ⟨by omega, rfl⟩
  · omega
  · omega

/-- `textL`'s segment is the file's bytes there (`launch_to_main`'s `hL`). -/
theorem text_some : (Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d).isSome = true := by decide +kernel

theorem text_pin : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some textB := by
  obtain ⟨bs, hb⟩ := Option.isSome_iff_exists.1 text_some
  obtain ⟨-, rfl⟩ := text_at hb (by decide) (by decide)
  exact hb

theorem text_hL : ∀ p ∈ textL, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
    Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2 := by
  intro p hp
  simp only [textL, List.mem_singleton] at hp
  subst hp
  exact ⟨0x401000, rfl, by decide, by rw [textB_length]; decide, by rw [textB_length]; exact text_pin⟩

theorem text_addr {x : Addr} (ha : 0x401000 ≤ x.toNat) : x = (0x401000#64 : Addr).add (x.toNat - 0x401000) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The bytes `Exe.bytesAt` reads at an address of the executable segment are code of `textL`. -/
theorem codeIn_text {a n : Nat} {bs : List Byte} (h : Exe.bytesAt V2606.zzs.blob a n = some bs)
    (ha : 0x401000 ≤ a) (ha' : a < 0x6d767d) : CodeIn textL (BitVec.ofNat 64 a) bs := by
  obtain ⟨hn, rfl⟩ := text_at h ha ha'
  have t : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat]
    omega
  have ea : BitVec.ofNat 64 a = (0x401000#64 : Addr).add (a - 0x401000) := by
    have := text_addr (x := BitVec.ofNat 64 a) (by omega)
    rwa [t] at this
  refine ⟨_, List.mem_singleton_self _, a - 0x401000, ea, ?_⟩
  have e : (List.range n).map (fun i => V2606.zzs.blob.bytes (0x1000 + (a - 0x401000) + i)) =
      (textB.drop (a - 0x401000)).take n := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_take, List.length_drop, textB_length]
      omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, textB] <;>
        congr 1 <;> omega
  rw [e]
  exact List.take_prefix _ _

/-- Some byte at each address of the executable segment is code of `textL`. -/
theorem text_any {x : Addr} (ha : 0x401000 ≤ x.toNat) (ha' : x.toNat < 0x6d767d) :
    ∃ c, CodeIn textL x c ∧ 0 < c.length := by
  refine ⟨(textB.drop (x.toNat - 0x401000)).take 1, ⟨_, List.mem_singleton_self _, x.toNat - 0x401000,
    text_addr ha, List.take_prefix _ _⟩, ?_⟩
  simp only [List.length_take, List.length_drop, textB_length]
  omega

/-! ## The bundles -/

theorem res_text : ∀ r ∈ V2606.resolvers, 0x401000 ≤ r.1 ∧ r.1 < 0x6d767d := by decide +kernel

theorem plt_text : ∀ a ∈ lifPlt, 0x401000 ≤ a ∧ a < 0x6d767d := by decide +kernel

theorem tg_text : ∀ i < 104, 0x401000 ≤ (csuTg i).toNat ∧ (csuTg i).toNat < 0x6d767d := by decide +kernel

theorem start_text : StartCode textL where
  ent := codeIn_text Entry.ent_pin (by decide) (by decide)
  lsm := codeIn_text lsm_pin (by decide) (by decide)
  pie := codeIn_text Pie.pie_pin (by decide) (by decide)
  aux := codeIn_text Auxv.aux_pin (by decide) (by decide)
  sec := codeIn_text Sec.sec_pin (by decide) (by decide)
  tin := codeIn_text Tun.tin_pin (by decide) (by decide)
  icf := codeIn_text CpuFeat.icf_pin (by decide) (by decide)
  icfk := codeIn_text CpuFeat.icfk_pin (by decide) (by decide)
  tgv := codeIn_text CpuFeat.tgv_pin (by decide) (by decide)
  gci := codeIn_text CpuFeat.gci_pin (by decide) (by decide)
  icfa := codeIn_text CpuFeat.icfa_pin (by decide) (by decide)
  icfh := codeIn_text CpuFeat.icfh_pin (by decide) (by decide)
  icfi := codeIn_text CpuFeat.icfi_pin (by decide) (by decide)
  irl := codeIn_text CpuFeat.irl_pin (by decide) (by decide)
  next := text_any (by decide) (by decide)
  res := fun r hr _ h => codeIn_text h (res_text r hr).1 (res_text r hr).2

theorem tls_text : TlsCode textL where
  tls := codeIn_text Tls.tls_pin (by decide) (by decide)
  sbk := codeIn_text Sbrk.sbk_pin (by decide) (by decide)
  brk := codeIn_text Brk.brk_pin (by decide) (by decide)
  cpy := text_any (by decide) (by decide)

theorem osv_text : OsvCode textL where
  osv := codeIn_text Osv.osv_pin (by decide) (by decide)
  unm := codeIn_text Uname.unm_pin (by decide) (by decide)

theorem pim_text : StartB.PimCode textL where
  pim := codeIn_text Pim.pim_pin (by decide) (by decide)
  sga := codeIn_text Sga.sga_pin (by decide) (by decide)
  gts := codeIn_text Gts.gts_pin (by decide) (by decide)
  grl := codeIn_text Grl.grl_pin (by decide) (by decide)
  lpi := codeIn_text Lpi.lpi_pin (by decide) (by decide)
  raf := codeIn_text Raf.raf_pin (by decide) (by decide)
  pti := codeIn_text Pti.pti_pin (by decide) (by decide)
  tgv := codeIn_text Tgv.tgv_pin (by decide) (by decide)

theorem lif_text : LifCode textL where
  lif := codeIn_text Lif.lif_pin (by decide) (by decide)
  ndi := codeIn_text Ndi.ndi_pin (by decide) (by decide)
  gev := codeIn_text Genv.gev_pin (by decide) (by decide)
  gor := codeIn_text Gor.gor_pin (by decide) (by decide)
  ipa := codeIn_text Ipa.ipa_pin (by decide) (by decide)
  hwc := codeIn_text Hwc.hwc_pin (by decide) (by decide)
  mnx := codeIn_text Mnx.mnx_pin (by decide) (by decide)
  imm := codeIn_text Imm.imm_pin (by decide) (by decide)
  tgv := codeIn_text Tgv.tgv_pin (by decide) (by decide)
  dpr := codeIn_text Dpr.dpr_pin (by decide) (by decide)
  mpr := codeIn_text Mpr.mpr_pin (by decide) (by decide)
  ims := codeIn_text Ims.ims_pin (by decide) (by decide)
  cti := codeIn_text Cti.cti_pin (by decide) (by decide)
  plt := fun a ha => text_any (by simp only [BitVec.toNat_ofNat]; have := (plt_text a ha).1; omega)
    (by simp only [BitVec.toNat_ofNat]; have := (plt_text a ha).2; omega)

theorem mal_text : MalCode textL where
  mal := codeIn_text Mal.mal_pin (by decide) (by decide)
  mhi := codeIn_text Mhi.mhi_pin (by decide) (by decide)
  pmi := codeIn_text Pmi.pmi_pin (by decide) (by decide)
  tgv := codeIn_text Tgv.tgv_pin (by decide) (by decide)
  tci := codeIn_text Tci.tci_pin (by decide) (by decide)
  imm := codeIn_text Imm.imm_pin (by decide) (by decide)
  smm := codeIn_text Smm.smm_pin (by decide) (by decide)
  dmc := codeIn_text Dmc.dmc_pin (by decide) (by decide)
  sbk := codeIn_text Sbrk.sbk_pin (by decide) (by decide)
  brk := codeIn_text Brk.brk_pin (by decide) (by decide)

theorem cxa_text : CxaCode textL where
  cxa := codeIn_text Cxa.cxa_pin (by decide) (by decide)
  nef := codeIn_text Nef.nef_pin (by decide) (by decide)

theorem main_text : MainCode textL where
  dbg := codeIn_text Dbg.dbg_pin (by decide) (by decide)
  sjp := codeIn_text Sjp.sjp_pin (by decide) (by decide)
  ssj := codeIn_text Ssj.ssj_pin (by decide) (by decide)
  csu := codeIn_text Csu.csu_pin (by decide) (by decide)
  main := text_any (by decide) (by decide)
  tcode := fun i hi => text_any (tg_text i hi).1 (tg_text i hi).2
  eli := codeIn_text Eli.eli_pin (by decide) (by decide)
  tgv := codeIn_text Tgv.tgv_pin (by decide) (by decide)
  ini := codeIn_text Ini.ini_pin (by decide) (by decide)
  fdm := codeIn_text Fdm.fdm_pin (by decide) (by decide)
  rtc := codeIn_text Rtc.rtc_pin (by decide) (by decide)
  rfi := codeIn_text Rfi.rfi_pin (by decide) (by decide)
  pml := codeIn_text Pml.pml_pin (by decide) (by decide)
  pmu := codeIn_text Pmu.pmu_pin (by decide) (by decide)

/-- `endbr64; ret` at `0x43cd90`, the file's. -/
theorem nret_pin : Exe.bytesAt V2606.zzs.blob 0x43cd90 5 = some Ctor.nret := by decide +kernel

theorem reg_text : ∀ r, CodeIn textL (Ctor.regAt r) (Ctor.regCode r)
  | 0 => codeIn_text Rga.rga_pin (by decide) (by decide)
  | 1 => codeIn_text Rgc.rgc_pin (by decide) (by decide)
  | _ + 2 => show CodeIn textL 0x458e90 Rgh.rgh from codeIn_text Rgh.rgh_pin (by decide) (by decide)

theorem ctor_text : Ctor.CtorCode textL where
  hin := codeIn_text Ctor.sti_pin (by decide) (by decide)
  hinN := codeIn_text nret_pin (by decide) (by decide)
  hinR := reg_text
  i3 := codeIn_text C3.c3_pin (by decide) (by decide)
  i15 := codeIn_text C15.c15_pin (by decide) (by decide)
  i78 := codeIn_text C78.c78_pin (by decide) (by decide)
  iF17 := codeIn_text Ctor.cf17_pin (by decide) (by decide)
  iU17 := codeIn_text Ctor.umk_pin (by decide) (by decide)
  iLz := codeIn_text Prepare.lz_pin (by decide) (by decide)
  iSse41 := codeIn_text Prepare.sse41_pin (by decide) (by decide)
  iAvx2 := codeIn_text Prepare.avx2_pin (by decide) (by decide)
  iAvx := codeIn_text Prepare.avx_pin (by decide) (by decide)
  iMaxf := codeIn_text Prepare.maxf_pin (by decide) (by decide)
  iCpuid := codeIn_text Prepare.cpuid_pin (by decide) (by decide)
  iSha1p := codeIn_text Prepare.sha1p_pin (by decide) (by decide)
  iSha := codeIn_text Prepare.sha_pin (by decide) (by decide)
  iSsse3 := codeIn_text Prepare.ssse3_pin (by decide) (by decide)
  iSha256p := codeIn_text Prepare.sha256p_pin (by decide) (by decide)
  iAesg := codeIn_text Prepare.aesg_pin (by decide) (by decide)
  iAes := codeIn_text Prepare.aes_pin (by decide) (by decide)
  iVaes := codeIn_text Prepare.vaes_pin (by decide) (by decide)
  iB2s := codeIn_text Prepare.b2s_pin (by decide) (by decide)
  iSwap := codeIn_text Prepare.swap_pin (by decide) (by decide)
  iMxs := codeIn_text Mxs.mxs_pin (by decide) (by decide)
  iMxi := codeIn_text Mxi.mxi_pin (by decide) (by decide)
  iCxa := codeIn_text Cxa.cxa_pin (by decide) (by decide)
  iNef := codeIn_text Nef.nef_pin (by decide) (by decide)
  iOin := codeIn_text Oin.oin_pin (by decide) (by decide)
  iNst := codeIn_text Nst.nst_pin (by decide) (by decide)
  iOnw := codeIn_text Onw.onw_pin (by decide) (by decide)
  iMnx := codeIn_text Mnx.mnx_pin (by decide) (by decide)
  iImm := codeIn_text Imm.imm_pin (by decide) (by decide)
  iHca := codeIn_text Hca.hca_pin (by decide) (by decide)

end FV7z.Start
