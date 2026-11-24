import FV7z.Start.CsuCall
import FV7z.Start.StackMap
import FV7z.Dbg.Holds
/-!
# `__libc_start_main` calls `_dl_debug_initialize (0, LM_ID_BASE)` (PLAN.md G3, startup)

After `init` returns to `0x61346e` (`lsm` 1070), glibc 2.31's `__libc_start_main` (static: `SHARED` is not defined)
calls `_dl_debug_initialize (0, LM_ID_BASE)` at `0x613472` (`lsm` 1074), which returns to `0x613477` (`lsm` 1079).
The call goes by the function's own proof (`Dbg.dbg_holdsK`): it stores only into `_r_debug`.

- `vc_1070`: `xor edi, edi; xor esi, esi`.
- `call_1074`: the `call`.
- `back_ret`: the registers a System V callee keeps, from `Returns`.
- `lsb_dbg`: the run from `0x61346e` to the return of `_dl_debug_initialize`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.DebugInit (rDebug rLoaded)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- The arguments of `_dl_debug_initialize`: `ldbase` and `ns` 0. -/
theorem vc_1070 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1070 fb F Wl (fun j' g' _ V' => j' = 1074 ∧ g' = { g with rsi := 0#64, rdi := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1070, o10, Op.xor]
  try simp only [BitVec.xor_self]
  first | trivial | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩

/-- The `call` of `_dl_debug_initialize` in `__libc_start_main`. -/
def pc1074 : List Byte := [0xe8, 0x29, 0xb0, 0x05, 0x00]
theorem pc1074_0 : ∀ feat, Dec feat pc1074 0 (FV7z.mk .call 64 [.rel 372777] 5) := by dec_rfl
theorem wc1074 : pc1074 <+: lsm.drop 1074 := by decide +kernel
theorem call_1074 (feat : Features) : Dec feat lsm 1074 (FV7z.mk .call 64 [.rel 372777] 5) :=
  Dec.shift (j := 1074) (k := 0) (pc1074_0 feat) wc1074 (Nat.zero_le _)

/-- After a System V callee's return, `rsp` is past the return address and the callee-saved registers are kept. -/
theorem back_ret {Y Z : State} {ra : Addr} (h : Returns sysv Y ra Z) : Osv.Back Y.cpu.gpr Z.cpu.gpr := by
  obtain ⟨-, hp, hsp, -⟩ := h
  have e : ∀ r : Reg, RegName.gpr r ∈ sysv.preserved → Z.cpu.gpr.get r = Y.cpu.gpr.get r := fun r hr => hp _ hr
  exact ⟨hsp, e 3 (by simp [sysv]), e 5 (by simp [sysv]), e 12 (by simp [sysv]), e 13 (by simp [sysv]),
    e 14 (by simp [sysv]), e 15 (by simp [sysv])⟩

theorem rDebug_mem {a : Addr} (h : rDebug.Mem a) : 0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84c0 + 40 := h
theorem rLoaded_mem {a : Addr} (h : rLoaded.Mem a) : 0x793440 ≤ a.toNat ∧ a.toNat < 0x793440 + 8 := h

/-- The return address's slot of a call with no stack frame, at `sp`. -/
theorem frame0 {E : State} {sp : Addr} (h : E.cpu.gpr.rsp = sp) {a : Addr} (ha : (frame E 0).Mem a) :
    sp.toNat ≤ a.toNat ∧ a.toNat < sp.toNat + 8 := by
  have e : (frame E 0).base = sp := by
    show E.cpu.gpr.rsp - BitVec.ofNat 64 0 = sp
    rw [h]
    exact BitVec.sub_zero sp
  have el : (frame E 0).len = 8 := rfl
  obtain ⟨h1, h2⟩ := ha
  rw [e] at h1
  rw [e, el] at h2
  exact ⟨h1, h2⟩

theorem below0 {E : State} {a : Addr} (ha : (below E 0).Mem a) : False := by
  have el : (below E 0).len = 0 := rfl
  obtain ⟨h1, h2⟩ := ha
  rw [el] at h2
  omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- From `0x61346e` to the return of `_dl_debug_initialize (0, LM_ID_BASE)` at `0x613477`, the return address's slot
at `sp` above `_r_debug`: at the return the bytes outside `_r_debug` are as before the call with the return address
stored, `rax` is `&_r_debug`, and the registers a call keeps are as at the call. -/
theorem lsb_dbg {fb sp : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hl : CodeIn L lsm_at lsm) (hin : CodeIn L Dbg.dbg_at Dbg.dbg) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1070) (hsp : X.cpu.gpr.rsp = sp + 8#64)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) (hal : (sp + 8#64).toNat % 16 = 0)
    (hs : 0x7a84e8 ≤ sp.toNat) (hs8 : sp.toNat + 16 ≤ 2 ^ 64) (hst : ∀ i < 8, Foot Wl (Addr.add sp i))
    (hsw : ∀ y : Addr, sp.toNat ≤ y.toNat → y.toNat < sp.toNat + 8 → Foot F.writes y)
    (hdw : ∀ y, rDebug.Mem y → Foot F.writes y) (hdW : ∀ y, rDebug.Mem y → Foot Wl y)
    (hlr : ∀ y, rLoaded.Mem y → Foot F.writes y ∨ Foot F.reads y)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ y, ¬ rDebug.Mem y → V' y = Vst V sp (toBytesLE (lsm_at.add 1079) 8) y) →
      Z.cpu.rip = lsm_at.add 1079 → Osv.Back ({ X.cpu.gpr with rsi := 0#64, rdi := 0#64 }.set 4 sp) Z.cpu.gpr →
      Z.cpu.gpr.rax = 0x7a84c0 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_1070 prof fb).run c hfs hl _ hK hA hrip vc_1070 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYs : Y.cpu.gpr.rsp - 8 = sp := by
    rw [hgY]
    show X.cpu.gpr.rsp - 8 = sp
    rw [hsp]
    bv_omega
  have hY8 : Y.cpu.gpr.rsp = sp + 8#64 := by
    rw [hgY]
    exact hsp
  refine c.s_callK hKY hAY hl (by rw [lsm_length]; decide) hrY (call_1074 _) hin (by rw [Dbg.dbg_length]; decide)
    (by decide) (fun i hi => by rw [hYs]; exact hst i hi) (by rw [hYs]; omega) (Dbg.dbg_holdsK L prof hin) hdf hx87
    (canonical_low (by decide) _) (by rw [hY8]; exact hal) ?_ ?_
  · intro E _ _ _ hgE
    have hEs : E.cpu.gpr.rsp = sp := by
      rw [hgE]
      exact hYs
    refine ⟨⟨?_, ?_, ?_, c.code.symm ▸ rfl, rfl, c.own⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro r hr
      simp only [Contract.footprint, fnK, fn, DebugInit.reads, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · show (frame E 0).base.toNat + (frame E 0).len ≤ 2 ^ 64
        have e : (frame E 0).base = sp := by
          show E.cpu.gpr.rsp - BitVec.ofNat 64 0 = sp
          rw [hEs]
          exact BitVec.sub_zero sp
        have el : (frame E 0).len = 8 := rfl
        rw [e, el]
        omega
      · exact (by decide : rDebug.base.toNat + rDebug.len ≤ 2 ^ 64)
      · exact (by decide : rLoaded.base.toNat + rLoaded.len ≤ 2 ^ 64)
    · rintro y ⟨r, hr, hm⟩
      simp only [Contract.footprint, fnK, fn, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := frame0 hEs hm
        exact hsw y this.1 this.2
      · exact hdw y hm
    · rintro y ⟨r, hr, hm⟩
      simp only [Contract.footprint, fnK, fn, DebugInit.reads, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact hlr y hm
    · rintro y ⟨r, hr, hm⟩
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (below0 hm).elim
      · exact hdW y hm
    · rw [hgE, hgY]
      rfl
    · intro r hr q hq a ha hb
      simp only [List.mem_singleton] at hr hq
      subst hr hq
      have h1 := frame0 hEs ha
      have h2 := rDebug_mem hb
      omega
    · rintro i hi ⟨r, hr, hm⟩
      simp only [List.mem_singleton] at hr
      subst hr
      have h2 := rDebug_mem hm
      rw [hEs, toNat_add_of_fits (a := sp) hi (by omega)] at h2
      omega
    · intro r hr q hq a ha hb
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [DebugInit.reads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      have h1 := frame0 hEs ha
      rcases hq with rfl | rfl
      · have h2 := rDebug_mem hb
        omega
      · have h2 := rLoaded_mem hb
        omega
  · intro E Z t' _ hgE hKZ hmem hret hpost
    rw [hYs] at hmem
    have hb := back_ret hret
    rw [hgE, hYs, hgY] at hb
    refine k (fun y => if Foot (ws 0 (fun _ => [rDebug]) E) y then Z.proc.mm.mem.readByte y
      else Vst V₁ sp (toBytesLE (lsm_at.add 1079) 8) y) Z t' hKZ ?_ ?_ hret.1 hb hpost.ret
    · intro y hy
      by_cases h : Foot (ws 0 (fun _ => [rDebug]) E) y
      · show _ = ite _ _ _
        rw [if_pos h]
      · show _ = ite _ _ _
        rw [if_neg h]
        exact hmem y hy h
    · intro y hy
      show ite _ _ _ = _
      rw [if_neg]
      rintro ⟨r, hr, hm⟩
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact below0 hm
      · exact hy hm

end FV7z.StartB
