import FV7z.Lif.Ok
/-!
# The code `__libc_init_first` runs (PLAN.md G3, startup)

`Ndi.lif_ok` asks for the code of each function it runs through in `L`, and for some code at the PLT entries it
calls through (`strlen`, `strncmp`, `mempcpy`, `malloc`, `memset`, `strrchr`). `LifCode L` gathers these, as
`StartCode` and `TlsCode` do for `launch_to_ptr`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (gor_at gor)

/-- The PLT entries `__libc_init_first` calls through: `strlen`, `strncmp`, `mempcpy`, `malloc`, `memset`,
`strrchr`. -/
def lifPlt : List Nat := [4198664, 4198472, 4198592, 6500704, 4198528, 4198480]

/-- The code `__libc_init_first` runs through is in `L`. -/
structure LifCode (L : List (Addr × List Byte)) : Prop where
  lif : CodeIn L Lif.lif_at Lif.lif
  ndi : CodeIn L Ndi.ndi_at Ndi.ndi
  gev : CodeIn L Genv.gev_at Genv.gev
  gor : CodeIn L gor_at gor
  ipa : CodeIn L Ipa.ipa_at Ipa.ipa
  hwc : CodeIn L Hwc.hwc_at Hwc.hwc
  mnx : CodeIn L Mnx.mnx_at Mnx.mnx
  imm : CodeIn L Imm.imm_at Imm.imm
  tgv : CodeIn L Tgv.tgv_at Tgv.tgv
  dpr : CodeIn L Dpr.dpr_at Dpr.dpr
  mpr : CodeIn L Mpr.mpr_at Mpr.mpr
  ims : CodeIn L Ims.ims_at Ims.ims
  cti : CodeIn L Cti.cti_at Cti.cti
  plt : ∀ a ∈ lifPlt, ∃ c, CodeIn L (BitVec.ofNat 64 a) c ∧ 0 < c.length

end FV7z.Start
