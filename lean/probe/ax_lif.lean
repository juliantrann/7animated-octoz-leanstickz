import FV7z.Lif.Bc
import FV7z.Ndi.Far
import FV7z.Ndi.Hpa
import FV7z.Lif.Nb
import FV7z.Lif.Ok
import FV7z.Lif.Ent
import FV7z.Tls.Lp
import FV7z.Start.Lp
import FV7z.Start.Ctp
import FV7z.Start.Ent
import FV7z.Start.Psz
import FV7z.Start.Pgs
import FV7z.Start.La
import FV7z.Start.Ro
import FV7z.Start.Ro2
import FV7z.Start.Keep
import FV7z.Start.Tg
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
#print axioms FV7z.Tls.TlsMem_lp
#print axioms FV7z.Tls.lp_pin
#print axioms FV7z.Start.ptr_lp
#print axioms FV7z.Lif.ent_rd
#print axioms FV7z.Start.ptr_lpv
#print axioms FV7z.Start.ptr_img
#print axioms FV7z.Start.v0_ct
#print axioms FV7z.Start.ent_ct
#print axioms FV7z.Start.vsOf_ps
#print axioms FV7z.Start.auxv_ps
#print axioms FV7z.Start.ctxOf_ps
#print axioms FV7z.Start.mb_ps
#print axioms FV7z.Start.ptr_ps
#print axioms FV7z.Start.ptr_img_mid
#print axioms FV7z.Start.ptr_la
#print axioms FV7z.Start.ptr_ro
#print axioms FV7z.Start.ent_ro
#print axioms FV7z.Start.ent_x
#print axioms FV7z.Start.ent_ph
#print axioms FV7z.Start.ent_len
#print axioms FV7z.Start.ent_sl
#print axioms FV7z.Start.ptr_keep
#print axioms FV7z.Start.ent_keep
#print axioms FV7z.Start.ent_pl
#print axioms FV7z.Start.v0_t11
#print axioms FV7z.Start.ent_t11
#print axioms FV7z.Start.ent_unset
