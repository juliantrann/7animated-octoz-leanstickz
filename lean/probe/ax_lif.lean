import FV7z.Lif.Bc
import FV7z.Ndi.Far
import FV7z.Ndi.Hpa
import FV7z.Lif.Nb
import FV7z.Lif.Ok
import FV7z.Lif.Ent
/-! Probe: the axioms of the `__libc_init_first` and `_dl_non_dynamic_init` pieces (expected: `propext`,
`Classical.choice`, `Quot.sound`). -/
#print axioms FV7z.Lif.lif_bc
#print axioms FV7z.Ndi.ndi_tls
#print axioms FV7z.Ndi.ndi_stk
#print axioms FV7z.Ndi.ndi_ok
#print axioms FV7z.Ndi.hpa
#print axioms FV7z.Mal.at_ok
#print axioms FV7z.Ndi.ndi_glob
#print axioms FV7z.Lif.lif_nb
#print axioms FV7z.Ndi.lif_ok
#print axioms FV7z.Lif.ptr_call
