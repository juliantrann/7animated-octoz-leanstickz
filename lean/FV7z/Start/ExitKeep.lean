import FV7z.Start.ToLifL
import FV7z.Ndi.Exit
/-!
# `__cxa_atexit`'s variables at the return of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_lif` gives the bytes at `0x613439` as `Cti.CtMem (Lif.bcV W₂ …)`, `W₂` those at the return of
`_dl_non_dynamic_init` (`Ndi.NdiRet` of `lif_ok`'s bytes `lifW W Z`). On `__cxa_atexit`'s variables (`Ndi.ExitB`:
`__exit_funcs_done`, `initial`, `__exit_funcs_lock`) none of the layers stores, so they are the bytes `W` at
`0x613434`.

- `Away`: the bytes of the image (below `0x7a9000`) apart from the variables `__init_misc` and `lif_a` store to.
- `ct_away`: `__init_misc` and `__ctype_init` store on the stack, to `__init_misc`'s two variables and below `fb`.
- `lifW_away`: `lif_a` stores on the stack and to four variables.
- `exit_ret`: the three joined with `Ndi.ndi_exit`; `glob_ret`: with `Ndi.ndi_glob`, for `[0x791eb8, 0x792980)`
  (`__exit_funcs` at `0x7923b0`).
- `ptr_exit`: at `0x613434` they are 0, as in the image (the bss); `ptr_ef`: `__exit_funcs` is `&initial`.
- `ct_tcb`, `lifW_tcb`, `tcb_ret`: the same for the first 56 bytes of the TCB (`multiple_threads` at `fs + 24`,
  `pointer_guard` at `fs + 48`), with `Ndi.ndi_tcb`.
- `lif_r12`: `r12` at `0x613439` (`fini`) is the one at `0x613434`, through the slot `__libc_init_first` saves it
  to.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out rd_Vst rd_Vst_self)
open FV7z.Ndi (ExitB)

/-- A byte of the image apart from `__init_misc`'s two variables (`[0x793338, 0x793348)`) and the four `lif_a` stores
to (`__libc_multiple_libcs`, `__environ`, `__libc_argc`, `__libc_argv`). -/
def Away (x : Addr) : Prop :=
  x.toNat < 7942968 ∨ 7942984 ≤ x.toNat ∧ x.toNat < 7944640 ∨ 7944644 ≤ x.toNat ∧ x.toNat < 8013720 ∨
    8013728 ≤ x.toNat ∧ x.toNat < 8029640 ∨ 8029656 ≤ x.toNat ∧ x.toNat < 0x7a9000

theorem exit_away {x : Addr} (hx : ExitB x) : Away x := by
  unfold ExitB at hx; unfold Away; omega

/-- After `_dl_non_dynamic_init` returns, the stores of `__init_misc` and `__ctype_init` miss `Away`. -/
theorem ct_away {W₂ : Addr → Byte} {g : Gprs} {a0 s fb x : Addr} {a1 a2 a3 : BitVec 64} (hx : Away x)
    (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hf : 0x7a9000 + 64 ≤ fb.toNat) (hf' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W₂ x := by
  unfold Away at hx
  unfold Cti.CtMem
  rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]
  exact Lif.bcV_out (by omega) (by omega) (by omega)

/-- `lif_ok`'s bytes on `Away` are those at `0x613434` (`g`: the registers at the entry of `__libc_init_first`). -/
theorem lifW_away {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} {x : Addr} (hx : Away x)
    (hr : 0x7a9000 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) x = W x := by
  unfold Away at hx
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
    (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64) (he : 0x7a9000 + 32 ≤ (entG Z).rsp.toNat)
    (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64) (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat)
    (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  rw [ct_away (exit_away hx) hg hfb hfb', Ndi.ndi_exit hE hU hL hb hf hsp hs hx]
  exact lifW_away (exit_away hx) he he'

/-- At the return of `__libc_init_first` to `0x613439`, a byte of `[0x791eb8, 0x792980)` (with `__exit_funcs` at
`0x7923b0`) is the byte `W` at `0x613434`. -/
theorem glob_ret {W W₂ : Addr → Byte} {Z : State} {b fsb fb a0 s x : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
    (h1 : 7937720 ≤ x.toNat) (h2 : x.toNat < 7940480) (hN : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) b fsb W₂)
    (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat) (hsp : 8032256 + 72 ≤ (lifSp Z).toNat)
    (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64) (he : 0x7a9000 + 32 ≤ (entG Z).rsp.toNat)
    (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64) (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat)
    (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  have ha : Away x := by unfold Away; omega
  rw [ct_away ha hg hfb hfb', Ndi.ndi_glob hE hU hL (by omega) (by omega) (by omega) hs (.inr ⟨h1, h2⟩)]
  exact lifW_away ha he he'

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
  rw [ptr_keep hK hM hb hb' hW (by omega) (by omega) hDa (by unfold Tls.TlsVar; omega) (by omega) hd
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

/-- `r12` at the return of `__libc_init_first` (`rdq(lifW W Z, lifSp Z + 136)`, `launch_to_lif`) is `r12` at
`0x613434`: `lif_a` pushes it to `rsp - 16` and pops it back. -/
theorem lif_r12 {W : Addr → Byte} {Z : State} (h : 8029656 + 16 ≤ (entG Z).rsp.toNat) :
    rdq(lifW W Z, lifSp Z + 136#64) = Z.cpu.gpr.r12 := by
  have e : lifSp Z + 136#64 = (entG Z).rsp - 16#64 := by simp only [lifSp]; bv_omega
  have := (entG Z).rsp.isLt
  have hr : (entG Z).r12 = Z.cpu.gpr.r12 := rfl
  rw [e]
  unfold lifW Lif.LifMem Lif.LifStk
  rw [rd_Vst _ _ _ _ _ ?_ ?_ ?_, rd_Vst _ _ _ _ _ ?_ ?_ ?_, rd_Vst _ _ _ _ _ ?_ ?_ ?_, rd_Vst _ _ _ _ _ ?_ ?_ ?_,
    rd_Vst _ _ _ _ _ ?_ ?_ ?_, rd_Vst _ _ _ _ _ ?_ ?_ ?_, rd_Vst_self _ _ _ (toBytesLE_length _ _) ?_,
    ofBytesLE_toBytesLE (n := 8) rfl, hr]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- `__exit_funcs` (`0x7923b0`) in the file: `&initial` (`0x7a3aa0`). -/
theorem ef_pin : Exe.bytesAt V2606.zzs.blob 0x7923b0 8 = some [160, 58, 122, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- At `0x613434`, `__exit_funcs` points to `initial` (`0x7a3aa0`): none of the layers before stores to it. -/
theorem ptr_ef {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 7938992#64 i)) : rdq(W, 7938992#64) = 8010400#64 := by
  have t0 : (7938992#64 : Addr).toNat = 7938992 := rfl
  rw [ptr_img hK hM hb hb' hW (.inr ⟨by rw [t0]; omega, by rw [t0]; omega⟩) hD]
  show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 (0x7923b0 + 0)) 8)) = _
  rw [hI.map ef_pin rfl (by decide) (by decide) (off := 0) (m := 8) (by decide)]
  rfl

end FV7z.Start
