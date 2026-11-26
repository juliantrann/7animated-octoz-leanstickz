import FV7z.Start.Text
import FV7z.Start.ReachP
/-!
# The PLT's code in the executable segment (PLAN.md §M, the theorem against vacuity)

`launch_main_plt` asks for the six PLT stubs the startup calls and the SSE2 functions they jump to (`PltCode`). The
executable segment `segL T` has them: the stubs' bytes are pinned with their contracts, the functions' here
(`sl2_pin` … `scm_pin`), and each is a stretch of `T` (`codeIn_text`).

- `pltc_text`: `PltCode (segL T)`.
- `text_code_plt`: `text_code` with `PltCode`.
-/
namespace FV7z.Start
open ZellicX86 FV7z
set_option maxRecDepth 100000

theorem sl2_pin : Exe.bytesAt V2606.zzs.blob 0x6546d0 412 = some Strlen.sl2 := by decide +kernel
theorem sr2_pin : Exe.bytesAt V2606.zzs.blob 0x654200 754 = some Strrchr.sr2 := by decide +kernel
theorem mc2_pin : Exe.bytesAt V2606.zzs.blob 0x65b8d0 992 = some Memcpy.mc2 := by decide +kernel
theorem ms2_pin : Exe.bytesAt V2606.zzs.blob 0x65c650 343 = some Memset.ms2 := by decide +kernel
theorem scm_pin : Exe.bytesAt V2606.zzs.blob 0x63a420 6233 = some Strncmp.scm := by decide +kernel

theorem pltc_text {T : List Byte} (hT : Exe.bytesAt V2606.zzs.blob 0x401000 0x2d667d = some T) :
    PltCode (segL T) where
  cpyP := codeIn_text hT Memcpy.plt_pin_cpy (by decide) (by decide)
  lenP := codeIn_text hT Strlen.pltLen_pin (by decide) (by decide)
  cmpP := codeIn_text hT Strncmp.plt_pin_ncmp (by decide) (by decide)
  pcpyP := codeIn_text hT Memcpy.plt_pin_pcpy (by decide) (by decide)
  setP := codeIn_text hT Memset.plt_pin (by decide) (by decide)
  rchrP := codeIn_text hT Strrchr.plt_pin (by decide) (by decide)
  cpy := codeIn_text hT mc2_pin (by decide) (by decide)
  len := codeIn_text hT sl2_pin (by decide) (by decide)
  cmp := codeIn_text hT scm_pin (by decide) (by decide)
  set := codeIn_text hT ms2_pin (by decide) (by decide)
  rchr := codeIn_text hT sr2_pin (by decide) (by decide)

/-- A code list with all `launch_main_plt` asks of it: the executable segment of `7zzs`. -/
theorem text_code_plt : ∃ L : List (Addr × List Byte),
    (∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) ∧
    StartCode L ∧ TlsCode L ∧ OsvCode L ∧ StartB.PimCode L ∧ LifCode L ∧ MalCode L ∧ CxaCode L ∧ MainCode L ∧
    Ctor.CtorCode L ∧ PltCode L := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 text_some
  exact ⟨segL T, seg_hL hT, start_text hT, tls_text hT, osv_text hT, pim_text hT, lif_text hT, mal_text hT,
    cxa_text hT, main_text hT, ctor_text hT, pltc_text hT⟩

end FV7z.Start
