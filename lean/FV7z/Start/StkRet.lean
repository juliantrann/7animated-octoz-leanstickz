import FV7z.Start.ArrRet
/-!
# `__libc_start_main`'s frame after the return of `__cxa_atexit` (PLAN.md G3, startup)

`StartB.lsb_tail` reads `main` (`q + 24`), `argc` (`q + 12`) and `argv` (`q + 16`) from `__libc_start_main`'s frame,
`q` the stack pointer at `0x61344a` (`K.bp + 112`). None of the layers since `0x613434` stores there (they all store
below `q`, or to the image and the brk), so these are the slots of `Fr`.

- `lifW_hi`: `lif_a`'s stores miss the stack from `g.rsp + 8` up.
- `ct_hi`: `__init_misc`'s and `__ctype_init`'s stores miss the stack from `g.rsp` up, above the TLS block.
- `RetAt.stk`: a byte from `(entG Z).rsp + 8` up at `0x613439` is the byte `W` at `0x613434`.
- `ptr_fr`: a byte of the frame's slots (`[bp + 112, bp + 156)`) at `0x613434` is the one of `MB`.
- `reg_out`: `__cxa_atexit` (`Cxa.Reg`) and its return address miss a byte apart from its frame and `initial`.
- `RetAt.cxa_lo`, `RetAt.cxa_fr`, `RetAt.cxa_rd`: the bytes at `0x61344a`, below `initial` and in the frame's slots.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- `lif_a`'s stores miss the stack from `g.rsp + 8` up (`g`: the registers at the entry of `__libc_init_first`). -/
theorem lifW_hi {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} {x : Addr} (hx : g.rsp.toNat + 8 ≤ x.toNat)
    (hr : 8029656 + 32 ≤ g.rsp.toNat) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) x = W x := by
  have := x.isLt
  unfold Lif.LifMem Lif.LifStk
  rw [Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_]
  all_goals bv_omega

/-- `__init_misc`'s and `__ctype_init`'s stores miss the stack from `g.rsp` up, above the TLS block at `fb`. -/
theorem ct_hi {W₂ : Addr → Byte} {g : Gprs} {a0 s fb x : Addr} {a1 a2 a3 : BitVec 64}
    (hx : g.rsp.toNat ≤ x.toNat) (hfx : fb.toNat ≤ x.toNat) (hg : 7942984 + 40 ≤ g.rsp.toNat) (hf : 64 ≤ fb.toNat) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W₂ x := by
  have := x.isLt
  unfold Cti.CtMem
  rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]
  exact Lif.bcV_out (by omega) (.inr hx) (.inr (by omega))

/-- `lifSp`'s offset back to the entry's stack pointer. -/
theorem lifSp_152 (Z : State) : lifSp Z + 152#64 = (entG Z).rsp := BitVec.sub_add_cancel _ _

theorem lifSp_toNat {Z : State} (h : 152 ≤ (entG Z).rsp.toNat) : (lifSp Z).toNat + 152 = (entG Z).rsp.toNat := by
  have e := lifSp_152 Z
  have := (entG Z).rsp.isLt
  have t : (lifSp Z + 152#64).toNat = (entG Z).rsp.toNat := by rw [e]
  bv_omega

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- At the return of `__libc_init_first` to `0x613439`, a byte from `(entG Z).rsp + 8` up (and from `g.rsp` up) is
the byte `W` at `0x613434`. -/
theorem RetAt.stk (h : RetAt W W₂ Z B g) {x : Addr} (hx : (entG Z).rsp.toNat + 8 ≤ x.toNat)
    (hgx : g.rsp.toNat ≤ x.toNat) : Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x = W x := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have e := lifSp_toNat (Z := Z) (by omega)
  obtain ⟨W', U, m, r, hE, hU, -, hS⟩ := h.nd
  rw [ct_hi hgx (by omega) (by omega) (by omega), Ndi.ndi_stk hE hU hS (by omega) (by omega) (by omega)]
  exact lifW_hi hx (by omega)

/-- At `0x613434` (`PtrW`'s bytes), a byte of `__libc_start_main`'s frame slots (`[bp + 112, bp + 156)`) above the
break's TLS block is the one of `MB`. -/
theorem ptr_fr {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) {a : Addr}
    (h1 : K.bp.toNat + 112 ≤ a.toNat) (h2 : a.toNat < K.bp.toNat + 156) (h3 : b.toNat + 8192 ≤ a.toNat)
    (hDa : D a) : W a = V a := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have ha := a.isLt
  rw [hW a (.inl hDa) ?_ (by unfold Pim.PimVar; omega)]
  · unfold PtrMem
    rw [Vst_out, ver_tls V ver hb' (by omega) (by omega) (by omega),
      TlsMem_out _ hb hb' (by unfold TlsVar; omega) (by omega)]
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 Junk2 Junk CpuVar at hj
    omega

/-- `__cxa_atexit`'s stores (`Cxa.Reg`, the list `initial` at `0x7a3aa0`) and its return address at `sp` miss a byte
apart from its frame `[sp - 56, sp + 8)`, `initial`'s count and first place and the lock. -/
theorem reg_out {V₀ V : Addr → Byte} {sp : Addr} {ra f0 : BitVec 64}
    (hR : Cxa.Reg (Vst V₀ sp (toBytesLE ra 8)) V sp 8010400#64 8010416#64 0 f0 0 0) (hs : sp.toNat + 8 ≤ 2 ^ 64)
    {x : Addr} (h1 : x.toNat + 56 ≤ sp.toNat ∨ sp.toNat + 8 ≤ x.toNat)
    (h2 : x.toNat < 8010408 ∨ 8010448 ≤ x.toNat ∧ x.toNat < 8029184 ∨ 8029200 ≤ x.toNat) : V x = V₀ x := by
  have tl : (8010400#64 : Addr).toNat = 8010400 := rfl
  have tp : (8010416#64 : Addr).toNat = 8010416 := rfl
  rw [hR.out x (by omega) (by omega) (by omega) (by omega)]
  exact Ndi.vap (toBytesLE_length _ _) hs (by omega)

/-- At the return of `__cxa_atexit` to `0x61344a`, a byte of the image below `initial` is the one at `0x613439`. -/
theorem RetAt.cxa_lo {V : Addr → Byte} {ra f0 : BitVec 64} (h : RetAt W W₂ Z B g)
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64) (toBytesLE ra 8)) V
      (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0) {x : Addr} (hx : x.toNat < 8010408) :
    V x = Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x := by
  have := h.hb; have := h.he; have := h.he'
  have e := lifSp_152 Z
  exact reg_out hR (by rw [e]; omega) (.inl (by rw [e]; omega)) (.inl hx)

/-- At the return of `__cxa_atexit` to `0x61344a`, a byte of `__libc_start_main`'s frame slots above `(entG Z).rsp`
is the one of `MB` (`g.rsp`: `__init_misc`'s frame, below). -/
theorem RetAt.cxa_fr {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {D : Addr → Prop} {ra f0 : BitVec 64}
    (h : RetAt W W₂ Z B g) (hW : PtrW K W V₀ B ver D)
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64) (toBytesLE ra 8)) V
      (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0)
    (hbp : K.bp.toNat + 112 = (entG Z).rsp.toNat + 8) (hg : g.rsp.toNat ≤ (entG Z).rsp.toNat + 8) {x : Addr}
    (h1 : K.bp.toNat + 112 ≤ x.toNat) (h2 : x.toNat < K.bp.toNat + 156) (hD : D x) : V x = V₀ x := by
  have := h.hb; have := h.he; have := h.he'
  have e := lifSp_152 Z
  rw [reg_out hR (by rw [e]; omega) (.inr (by rw [e]; omega)) (.inr (.inr (by omega))), h.stk (by omega) (by omega)]
  exact ptr_fr h.hb h.hb' hW h1 h2 (by omega) hD

/-- `n` bytes of the frame's slots from `bp + c` at `0x61344a` are those of `MB`. -/
theorem RetAt.cxa_rd {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {ra f0 : BitVec 64}
    (h : RetAt W W₂ Z B g) (hW : PtrW K W V₀ B ver (fun _ => True))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64) (toBytesLE ra 8)) V
      (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0)
    (hbp : K.bp.toNat + 112 = (entG Z).rsp.toNat + 8) (hg : g.rsp.toNat ≤ (entG Z).rsp.toNat + 8)
    (hbn : K.bp.toNat + 328 ≤ 2 ^ 64) {c n : Nat} (h1 : 112 ≤ c) (h2 : c + n ≤ 156) :
    List.map V (byteAddrs (K.bp + BitVec.ofNat 64 c) n) = List.map V₀ (byteAddrs (K.bp + BitVec.ofNat 64 c) n) :=
  rd_ext _ n fun i hi => by
    have tc : (K.bp + BitVec.ofNat 64 c).toNat = K.bp.toNat + c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have t : ((K.bp + BitVec.ofNat 64 c).add i).toNat = K.bp.toNat + c + i := by
      rw [toNat_add_of_fits hi (by omega), tc]
    exact h.cxa_fr hW hR hbp hg (by omega) (by omega) trivial

end FV7z.Start
