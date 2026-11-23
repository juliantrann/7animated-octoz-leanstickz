import FV7z.Start.ToLifL
import FV7z.Ndi.Exit
/-!
# `__cxa_atexit`'s variables at the return of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_lif` gives the bytes at `0x613439` as `Cti.CtMem (Lif.bcV W₂ …)`, `W₂` those at the return of
`_dl_non_dynamic_init` (`Ndi.NdiRet` of `lif_ok`'s bytes `lifW W Z`). On `__cxa_atexit`'s variables (`Ndi.ExitB`:
`__exit_funcs_done`, `initial`, `__exit_funcs_lock`) none of the layers stores, so they are the bytes `W` at
`0x613434`.

- `ct_exit`: `__init_misc` and `__ctype_init` store on the stack, to `__init_misc`'s two variables and below `fb`.
- `lifW_exit`: `lif_a` stores on the stack and to four variables, none of them `ExitB`.
- `exit_ret`: the three joined with `Ndi.ndi_exit`.
- `ptr_exit`: at `0x613434` they are 0, as in the image (the bss).
- `ct_tcb`, `lifW_tcb`, `tcb_ret`: the same for the first 56 bytes of the TCB (`multiple_threads` at `fs + 24`,
  `pointer_guard` at `fs + 48`), with `Ndi.ndi_tcb`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Ndi (ExitB)

/-- After `_dl_non_dynamic_init` returns, the stores of `__init_misc` and `__ctype_init` miss `ExitB`. -/
theorem ct_exit {W₂ : Addr → Byte} {g : Gprs} {a0 s fb x : Addr} {a1 a2 a3 : BitVec 64} (hx : ExitB x)
    (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hf : 0x7a9000 + 64 ≤ fb.toNat) (hf' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W₂ x := by
  unfold ExitB at hx
  unfold Cti.CtMem
  rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]
  exact Lif.bcV_out (by omega) (by omega) (by omega)

/-- `lif_ok`'s bytes on `ExitB` are those at `0x613434` (`g`: the registers at the entry of
`__libc_init_first`). -/
theorem lifW_exit {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} {x : Addr} (hx : ExitB x)
    (hr : 7944640 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) x = W x := by
  unfold ExitB at hx
  unfold Lif.LifMem Lif.LifStk
  rw [Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_]
  all_goals bv_omega

/-- At the return of `__libc_init_first` to `0x613439`, a byte of `ExitB` is the byte `W` at `0x613434`. -/
theorem exit_ret {W W₂ : Addr → Byte} {Z : State} {b fsb fb a0 s x : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
    (hx : ExitB x) (hN : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) b fsb W₂)
    (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat) (hsp : 8032256 + 72 ≤ (lifSp Z).toNat)
    (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64) (he : 7944640 + 32 ≤ (entG Z).rsp.toNat)
    (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64) (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat)
    (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  rw [ct_exit hx hg hfb hfb', Ndi.ndi_exit hE hU hL hb hf hsp hs hx]
  exact lifW_exit hx he he'

/-- At `0x613434` (`ptr_keep`'s bytes), a byte of `ExitB` is 0: none of the layers before stores to it. -/
theorem ptr_exit {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {a : Addr} (hx : ExitB a) (hDa : D a) : W a = 0 := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  unfold ExitB at hx
  have hd : ¬ Foot (d3 ++ AuxInit.globals) a := by
    rcases hx with h | h
    · exact not_dg (lo := 8010388) (hi := 8011440) (by decide) h.1 h.2
    · exact not_dg (lo := 8029184) (hi := 8029200) (by decide) h.1 h.2
  rw [ptr_keep hK hM hb hb' hW (by omega) (by omega) hDa (by unfold TlsVar; omega) (by omega) hd
    (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)]
  exact hB a (by omega) (by omega)

/-- After `_dl_non_dynamic_init` returns, the stores of `__init_misc` and `__ctype_init` miss the first 56 bytes of
the TCB. -/
theorem ct_tcb {W₂ : Addr → Byte} {g : Gprs} {a0 s fb x : Addr} {a1 a2 a3 : BitVec 64} (h1 : fb.toNat ≤ x.toNat)
    (h2 : x.toNat < fb.toNat + 56) (hg : fb.toNat + 96 ≤ g.rsp.toNat) (hf : 0x7a9000 + 64 ≤ fb.toNat)
    (hf' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W₂ x := by
  unfold Cti.CtMem
  rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]
  exact Lif.bcV_out (by omega) (by omega) (by omega)

/-- `lif_ok`'s bytes on the first 56 bytes of the TCB are those at `0x613434`. -/
theorem lifW_tcb {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} {fb x : Addr} (h1 : fb.toNat ≤ x.toNat)
    (h2 : x.toNat < fb.toNat + 56) (hf : 0x7a9000 ≤ fb.toNat) (hr : fb.toNat + 56 + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) x = W x := by
  unfold Lif.LifMem Lif.LifStk
  rw [Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_]
  all_goals bv_omega

/-- At the return of `__libc_init_first` to `0x613439`, a byte of the first 56 of the TCB at `fb` is the byte `W` at
`0x613434`. -/
theorem tcb_ret {W W₂ : Addr → Byte} {Z : State} {b fb a0 s x : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
    (h1 : fb.toNat ≤ x.toNat) (h2 : x.toNat < fb.toNat + 56)
    (hN : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) b fb W₂) (hb : fb.toNat + 56 ≤ b.toNat)
    (hsp : fb.toNat + 56 + 72 ≤ (lifSp Z).toNat) (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64)
    (he : fb.toNat + 56 + 32 ≤ (entG Z).rsp.toNat) (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64)
    (hg : fb.toNat + 96 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat) (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  rw [ct_tcb h1 h2 hg hfb hfb', Ndi.ndi_tcb hE hU hL (by omega) hb hsp hs h1 h2]
  exact lifW_tcb h1 h2 (by omega) he he'

end FV7z.Start
