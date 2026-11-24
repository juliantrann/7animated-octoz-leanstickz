import FV7z.Start.DbgCall
import FV7z.Ssj.Holds
/-!
# `__libc_start_main` calls `_setjmp` (PLAN.md G3, startup)

After `_dl_debug_initialize` returns to `0x613477` (`lsm` 1079), glibc 2.31's `__libc_start_main` sets up the
cancellation buffer of the thread, `struct pthread_unwind_buf unwind_buf` at `rsp + 0x70`, by
`_setjmp (unwind_buf.cancel_jmp_buf)` at `0x61347c` (`lsm` 1084), which returns 0 to `0x613481` (`lsm` 1089).

- `vc_1079`: `lea rdi, [rsp + 0x70]`.
- `call_1084`: the `call`.
- `lsb_sjp`: the run from `0x613477` to the return of `_setjmp`, by `Ssj.setjmp_ok`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst_self)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- The argument of `_setjmp`: the buffer at `rsp + 0x70`. -/
theorem vc_1079 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1079 fb F Wl (fun j' g' _ V' => j' = 1084 ∧ g' = { g with rdi := g.rsp + 112#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1079, o11, Op.lea]
  try simp only [BitVec.zero_mul, BitVec.add_zero, BitVec.setWidth_eq]
  first | trivial | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩

/-- The `call` of `_setjmp` in `__libc_start_main`. -/
def pc1084 : List Byte := [0xe8, 0xbf, 0xee, 0x00, 0x00]
theorem pc1084_0 : ∀ feat, Dec feat pc1084 0 (FV7z.mk .call 64 [.rel 61119] 5) := by dec_rfl
theorem wc1084 : pc1084 <+: lsm.drop 1084 := by decide +kernel
theorem call_1084 (feat : Features) : Dec feat lsm 1084 (FV7z.mk .call 64 [.rel 61119] 5) :=
  Dec.shift (j := 1084) (k := 0) (pc1084_0 feat) wc1084 (Nat.zero_le _)

theorem add_m8 {sp : Addr} {i : Nat} : Addr.add (sp - 8#64) (8 + i) = Addr.add sp i := by
  simp only [Addr.add]
  bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- From `0x613477` to the return of `_setjmp (rsp + 0x70)` at `0x613481`, the return address's slot at `sp`: at the
return the buffer at `sp + 0x78` is filled (`Ssj.Jb`, of the bytes before the call with the return address stored),
`rax` is 0, and the registers a call keeps are as at the call. -/
theorem lsb_sjp {fb sp : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hl : CodeIn L lsm_at lsm) (hinp : CodeIn L Sjp.sjp_at Sjp.sjp) (hin : CodeIn L Ssj.ssj_at Ssj.ssj)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1079)
    (hsp : X.cpu.gpr.rsp = sp + 8#64) (hs : 16 ≤ sp.toNat) (hs8 : sp.toNat + 216 ≤ 2 ^ 64)
    (hst : ∀ i < 16, Foot Wl (Addr.add (sp - 8#64) i)) (hbw : ∀ i < 96, Foot Wl (Addr.add (sp + 120#64) i))
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 56 ≤ sp.toNat ∨ sp.toNat + 8 ≤ fb.toNat)
    (hfd : fb.toNat + 56 ≤ sp.toNat + 120 ∨ sp.toNat + 216 ≤ fb.toNat)
    (k : ∀ (V' : Addr → Byte) (g' : Gprs) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Ssj.Jb (Vst V sp (toBytesLE (lsm_at.add 1089) 8)) V' sp (sp + 120#64) X.cpu.gpr.rbx
        ((X.cpu.gpr.rbp ^^^ rdq(V, fb + 48#64)).rotateLeft 17) X.cpu.gpr.r12 X.cpu.gpr.r13 X.cpu.gpr.r14
        X.cpu.gpr.r15 ((sp + 8#64 ^^^ rdq(V, fb + 48#64)).rotateLeft 17)
        ((lsm_at.add 1089 ^^^ rdq(V, fb + 48#64)).rotateLeft 17) →
      Z.cpu.rip = lsm_at.add 1089 → Z.cpu.gpr = g' → g'.rax = 0 →
      Osv.Back ({ X.cpu.gpr with rdi := sp + 120#64 }.set 4 sp) g' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have t120 : (sp + 120#64).toNat = sp.toNat + 120 := by bv_omega
  have tm8 : (sp - 8#64).toNat = sp.toNat - 8 := by bv_omega
  have f48 : (fb + 48#64).toNat = fb.toNat + 48 := by bv_omega
  have e120 : X.cpu.gpr.rsp + 112#64 = sp + 120#64 := by
    rw [hsp, BitVec.add_assoc]
    rfl
  have hss : ∀ i < 8, Foot Wl (Addr.add sp i) := fun i hi => by
    have h := hst (8 + i) (by omega)
    rwa [add_m8] at h
  have hb8 : (toBytesLE (lsm_at.add (1084 + 5)) 8).length = 8 := toBytesLE_length _ _
  refine (c_1079 prof fb).run c hfs hl _ hK hA hrip vc_1079 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYs : Y.cpu.gpr.rsp - 8 = sp := by
    rw [hgY]
    show X.cpu.gpr.rsp - 8 = sp
    rw [hsp]
    exact BitVec.add_sub_cancel sp 8#64
  refine c.s_call hKY hAY hl (by rw [lsm_length]; decide) hrY (call_1084 _) hinp
    (by rw [Sjp.sjp_length]; decide) (by decide) (fun i hi => by rw [hYs]; exact hss i hi) ?_
  rintro Z₁ u₁ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hYs] at hAZ hgZ
  have hzs : Z₁.cpu.gpr.rsp = sp := by
    rw [hgZ]
    rfl
  have hzr : Z₁.cpu.gpr.rdi = sp + 120#64 := by
    rw [hgZ, hgY]
    exact e120
  refine Ssj.setjmp_ok (e₂ := lsm_at) (j₂ := 1089) c hfs hinp hin hKZ hAZ hrZ
    (fun i hi => by rw [hzr]; exact hbw i hi) (by rw [hzr, t120]; omega)
    (fun i hi => by
      rw [hzs]
      have h := hst i (by omega)
      exact h)
    (by rw [hzs]; omega) (fun i hi => by rw [hzs]; exact c.hws _ (hss i hi)) hl (by rw [lsm_length]; decide)
    (by rw [hzs, rd_Vst_self _ _ _ hb8 (by omega), ofBytesLE_toBytesLE (n := 8) rfl]) (by rw [hzs]; omega)
    (by rw [hzr, hzs, t120]; omega) hft hfn (by rw [hzr, t120]; omega) ?_
  intro V₂ g' Z t' hKZ' hAZ' hJ hrZ' hgZ' hax hBk
  rw [rd_ra (fb + 48#64) 8 hb8 (by omega) (by rw [f48]; omega) (by rw [f48]; omega)] at hJ
  rw [hzr, hzs] at hJ
  rw [hgZ, hgY] at hJ hBk
  rw [e120] at hBk
  exact k V₂ g' Z t' hKZ' hAZ' hJ hrZ' hgZ' hax hBk

end FV7z.StartB
