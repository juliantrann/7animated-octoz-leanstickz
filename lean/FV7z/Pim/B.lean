import FV7z.Pim.A
import FV7z.Sga.Holds
/-!
# `__pthread_initialize_minimal_internal`: the two handlers and the signals' mask (PLAN.md G3, startup)

The second stretch of the function at `0x6000b0`, offsets 251 to 352: `__libc_sigaction (32, &sa, 0)` with the
handler `0x5ffec0` (`sigcancel_handler`), `__libc_sigaction (33, &sa, 0)` with the handler `0x5fff60`
(`sighandler_setxid`) and the flag `SA_RESTART`, the two signals in the action's set, `rt_sigprocmask (SIG_UNBLOCK)`.

- `sgEv`, `mskEv`: the system calls' events.
- `sga_call`: a call of `__libc_sigaction` from the function's body, the frame's description kept.
- `vc_251` … `vc_345`: the verification conditions; `pim_b`: the stretch.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- `rt_sigaction (n, act, 0, 8)` of `__libc_sigaction`, called in the function entered with the stack pointer `sp`. -/
abbrev sgEv (n r9 : BitVec 64) (sp : Addr) : Event := ⟨13, [n, sp - 552#64, 0, 8, 0, r9], 0, [], []⟩

/-- `rt_sigprocmask (SIG_UNBLOCK, set, 0, 8)`. -/
abbrev mskEv (sp : Addr) : Event :=
  ⟨BitVec.setWidth 64 14#32, [BitVec.setWidth 64 1#32, sp - 176#64, BitVec.setWidth 64 0#32, BitVec.setWidth 64 8#32,
    0, 0], 0, [], []⟩

/-- The first handler, to the call. -/
theorem vc_251 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 32#64) i)) :
    W_251 fb F Wl (fun j' g' _ V' => j' = 271 ∧
      g' = { g with rax := 6291136#64, rsi := g.r12, rdi := BitVec.setWidth 64 32#32 } ∧
      V' = Vst V (g.rsp + 32#64) (toBytesLE (6291136#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_251, o6]
  exact h

/-- The second handler and its flags, to the call. -/
theorem vc_276 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 168#64) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 32#64) i)) :
    W_276 fb F Wl (fun j' g' _ V' => j' = 309 ∧
      g' = { g with rax := 6291296#64, rdx := BitVec.setWidth 64 0#32, rsi := g.r12,
                    rdi := BitVec.setWidth 64 33#32 } ∧
      V' = Vst (Vst V (g.rsp + 168#64) (toBytesLE (268435460#32) 4)) (g.rsp + 32#64) (toBytesLE (6291296#64) 8))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_276, o7, BitVec.xor_self]
  exact ⟨h1, h2⟩

/-- The arguments of `rt_sigprocmask`. -/
theorem vc_314 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_314 fb F Wl (fun j' g' _ V' => j' = 340 ∧
      g' = { g with rax := 6442450944#64, rdx := BitVec.setWidth 64 0#32, rsi := g.rbp,
                    rdi := BitVec.setWidth 64 1#32, r10 := BitVec.setWidth 64 8#32 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_314, o8, BitVec.xor_self]

/-- The system call's number. -/
theorem vc_345 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_345 fb F Wl (fun j' g' _ V' => j' = 350 ∧ g' = { g with rax := BitVec.setWidth 64 14#32 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_345, o9]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- A call of `__libc_sigaction (n, sp - 184, 0)` at offset `j` of the function, the handler `h` in the action: the
run reaches offset `j + 5` with `rax`, `r8`, `r9` 0, from a new start; the bytes are as before but in the callee's
frame. -/
theorem sga_call {lim n j rel : Nat} {b fb sp : Addr} {kst : Kst} {h r12 rbp cn : BitVec 64} {G : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fb kst) (hin : CodeIn L pim_at pim)
    (hinS : CodeIn L Sga.sga_at Sga.sga) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hL : Lay F Wl sp fb) (htop : sp.toNat ≤ userPtrMax prof.feat) (hF : Fr G V sp r12 rbp cn)
    (hj : j + 5 < 753) (hrip : X.cpu.rip = pim_at.add j)
    (hd : Dec prof.feat pim j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : pim_at.add (j + 5) + BitVec.ofNat 64 rel = Sga.sga_at)
    (hsp : X.cpu.gpr.rsp = sp - 216#64) (hsi : X.cpu.gpr.rsi = sp - 184#64) (hdx : X.cpu.gpr.rdx = 0)
    (hsig : argInt X.cpu.gpr.rdi = (n : Int)) (h1 : 1 ≤ n) (h64 : n ≤ 64) (h9 : n ≠ 9) (h19 : n ≠ 19)
    (hh : rdq(V, sp - 184#64) = h) (hh0 : h ≠ 0) (hh1 : h ≠ 1)
    (k : ∀ s₁ V' g' Z t', Seg prof F Wl L s₁ o → Base s₁ lim b fb kst → KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V' →
      Fr G V' sp r12 rbp cn → Z.cpu.rip = pim_at.add (j + 5) → Z.cpu.gpr = g' → g'.rax = 0 → g'.r8 = 0 → g'.r9 = 0 →
      g'.rsp = sp - 216#64 → g'.rbx = X.cpu.gpr.rbx → g'.rbp = X.cpu.gpr.rbp → g'.r12 = X.cpu.gpr.r12 →
      g'.r13 = X.cpu.gpr.r13 → g'.r14 = X.cpu.gpr.r14 → g'.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [sgEv X.cpu.gpr.rdi X.cpu.gpr.r9 sp]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp' := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := sp.isLt
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd hinS (Sga.lt_len (by decide)) htgt (fun i hi => ?_) ?_
  · rw [hsp]
    exact off_ft hL.hst 328 (by bv_omega) (by decide) i hi
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hsp, show sp - 216#64 - 8 = sp - 224#64 from by bv_omega] at hA₁ hg₁
  have hF₁ : Fr G (Vst V (sp - 224#64) (toBytesLE (pim_at.add (j + 5)) 8)) sp r12 rbp cn :=
    hF.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
  have hsp₁ : Y.cpu.gpr.rsp = sp - 224#64 := by rw [hg₁]; rfl
  have hsi₁ : Y.cpu.gpr.rsi = sp - 184#64 := by rw [hg₁]; exact hsi
  have e224 : (sp - 224#64).toNat = sp.toNat - 224 := by bv_omega
  refine Sga.sga_ok (n := n) (h := h) c hB hinS hK₁ hA₁ hr₁ (by rw [hsp₁]; omega)
    (by rw [hsp₁]; exact Nat.le_trans (by omega) htop)
    (by rw [hsp₁]; exact off_ft hL.hst 0 (by bv_omega) (by decide))
    (by rw [hsp₁]; exact fun i hi => hL.hws _ (off_ft hL.hst 328 (by bv_omega) (by decide) i hi))
    hin (j₂ := j + 5) (lt_len hj) ?_ (by rw [hg₁]; exact hsig) h1 h64 h9 h19 (by rw [hsi₁]; bv_omega)
    (by rw [hg₁]; exact hdx) (by rw [hsi₁]; bv_omega)
    (by rw [hsi₁]; exact fun i hi => hL.hws _ (off_ft hL.hst 368 (by bv_omega) (by decide) i hi))
    (by rw [hsi₁, hsp₁]; bv_omega) ?_ hh0 hh1 (fun i hi => hL.hws _ (off_ft hL.htcb 40 rfl (by decide) i hi))
    (by bv_omega) (by rw [hsp₁]; bv_omega) ?_
  · rw [hsp₁, vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [hsi₁, vr (by ln) (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hh
  intro s₁ V₂ g₂ Z t₂ c₁ hB₁ hK₂ hA₂ ho₂ hr₂ hg₂ hax h8 h9' hbk
  rw [hsp₁, e224] at ho₂
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hbk
  have hev : Sga.sgaEv Y.cpu.gpr = sgEv X.cpu.gpr.rdi X.cpu.gpr.r9 sp := by
    rw [hg₁]
    show (⟨13, [X.cpu.gpr.rdi, sp - 224#64 - 328#64, 0, 8, 0, X.cpu.gpr.r9], 0, [], []⟩ : Event) = _
    rw [show sp - 224#64 - 328#64 = sp - 552#64 from by bv_omega]
  rw [hev]
  have kp : Y.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine k s₁ V₂ g₂ Z t₂ c₁ hB₁ hK₂ hA₂ (hF₁.of_out hL.hsp ho₂ (by omega) (by omega)) hr₂ hg₂ hax h8 h9' ?_
    (hb2.trans kp.1) (hb3.trans kp.2.1) (hb4.trans kp.2.2.1) (hb5.trans kp.2.2.2.1) (hb6.trans kp.2.2.2.2.1)
    (hb7.trans kp.2.2.2.2.2)
  rw [hb1, hsp₁]
  bv_omega

/-- From offset 251 to offset 352: the two handlers set, the two signals unblocked. -/
theorem pim_b {lim : Nat} {b fb : Addr} {kst : Kst} {g₀ : Gprs} {G : Addr → Byte} {r12 rbp cn : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fb kst) (hin : CodeIn L pim_at pim)
    (hinS : CodeIn L Sga.sga_at Sga.sga) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pim_at.add 251) (hL : Lay F Wl g₀.rsp fb) (htop : g₀.rsp.toNat ≤ userPtrMax prof.feat)
    (hF : Fr G V g₀.rsp r12 rbp cn) (hR : Rg g₀ X.cpu.gpr) (hdx : X.cpu.gpr.rdx = 0)
    (k : ∀ s₁ V' g' Z t', Seg prof F Wl L s₁ o → Base s₁ lim b fb kst → KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V' →
      Fr G V' g₀.rsp r12 rbp cn → Z.cpu.rip = pim_at.add 352 → Z.cpu.gpr = g' → Rg g₀ g' → g'.r8 = 0 → g'.r9 = 0 →
      GoG prof L o (gev ++ [sgEv (BitVec.setWidth 64 32#32) X.cpu.gpr.r9 g₀.rsp] ++
        [sgEv (BitVec.setWidth 64 33#32) 0 g₀.rsp] ++ [mskEv g₀.rsp]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hbp, h12, hbx, h13, h14, h15⟩ := hR
  have hsp' := hL.hsp
  have hlt := g₀.rsp.isLt
  -- the first handler
  refine (c_251 prof fb).run c hB.fsb hin _ hK hA hrip
    (vc_251 (by rw [hsp]; exact off_ft hL.hst 368 (by bv_omega) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hsp, show g₀.rsp - 216#64 + 32#64 = g₀.rsp - 184#64 from by bv_omega] at hA₁
  have hF₁ : Fr G (Vst V (g₀.rsp - 184#64) (toBytesLE (6291136#64) 8)) g₀.rsp r12 rbp cn :=
    hF.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
  have k1 : Y₁.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₁.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₁.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₁.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₁.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine sga_call (n := 32) (h := 6291136#64) c hB hin hinS hK₁ hA₁ hL htop hF₁ (by decide) hr₁ (call_271 _)
    (by decide) (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h12) (by rw [hg₁]; exact hdx) (by rw [hg₁]; rfl)
    (by decide) (by decide) (by decide) (by decide) ?_ (by decide) (by decide) ?_
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro s₁ V₂ g₂ Y₂ t₂ c₁ hB₁ hK₂ hA₂ hF₂ hr₂ hg₂ hax₂ h8₂ h9₂ hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  subst hg₂
  have hev₁ : sgEv Y₁.cpu.gpr.rdi Y₁.cpu.gpr.r9 g₀.rsp = sgEv (BitVec.setWidth 64 32#32) X.cpu.gpr.r9 g₀.rsp := by
    rw [hg₁]
  rw [hev₁]
  -- the second handler
  refine (c_276 prof fb).run c₁ hB₁.fsb hin _ hK₂ hA₂ hr₂
    (vc_276 (by rw [hsp₂]; exact off_ft hL.hst 504 (by bv_omega) (by decide))
      (by rw [hsp₂]; exact off_ft hL.hst 368 (by bv_omega) (by decide))) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hsp₂, show g₀.rsp - 216#64 + 168#64 = g₀.rsp - 48#64 from by bv_omega,
    show g₀.rsp - 216#64 + 32#64 = g₀.rsp - 184#64 from by bv_omega] at hA₃
  have hF₃ : Fr G (Vst (Vst V₂ (g₀.rsp - 48#64) (toBytesLE (268435460#32) 4)) (g₀.rsp - 184#64)
      (toBytesLE (6291296#64) 8)) g₀.rsp r12 rbp cn :=
    (hF₂.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)).lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
  have k3 : Y₃.cpu.gpr.rbx = Y₂.cpu.gpr.rbx ∧ Y₃.cpu.gpr.rbp = Y₂.cpu.gpr.rbp ∧ Y₃.cpu.gpr.r12 = Y₂.cpu.gpr.r12 ∧
      Y₃.cpu.gpr.r13 = Y₂.cpu.gpr.r13 ∧ Y₃.cpu.gpr.r14 = Y₂.cpu.gpr.r14 ∧ Y₃.cpu.gpr.r15 = Y₂.cpu.gpr.r15 := by
    rw [hg₃]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine sga_call (n := 33) (h := 6291296#64) c₁ hB₁ hin hinS hK₃ hA₃ hL htop hF₃ (by decide) hr₃ (call_309 _)
    (by decide) (by rw [hg₃]; exact hsp₂) (by rw [hg₃]; exact (h12₂.trans k1.2.2.1).trans h12) (by rw [hg₃]; rfl)
    (by rw [hg₃]; rfl) (by decide) (by decide) (by decide) (by decide) ?_ (by decide) (by decide) ?_
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro s₂ V₄ g₄ Y₄ t₄ c₂ hB₂ hK₄ hA₄ hF₄ hr₄ hg₄ hax₄ h8₄ h9₄ hsp₄ hbx₄ hbp₄ h12₄ h13₄ h14₄ h15₄
  subst hg₄
  have hev₂ : sgEv Y₃.cpu.gpr.rdi Y₃.cpu.gpr.r9 g₀.rsp = sgEv (BitVec.setWidth 64 33#32) 0 g₀.rsp := by
    rw [hg₃]
    show sgEv _ Y₂.cpu.gpr.r9 _ = _
    rw [h9₂]
  rw [hev₂]
  have ebx : Y₄.cpu.gpr.rbx = g₀.rbx := (((hbx₄.trans k3.1).trans hbx₂).trans k1.1).trans hbx
  have ebp : Y₄.cpu.gpr.rbp = g₀.rsp - 176#64 := (((hbp₄.trans k3.2.1).trans hbp₂).trans k1.2.1).trans hbp
  have e12 : Y₄.cpu.gpr.r12 = g₀.rsp - 184#64 := (((h12₄.trans k3.2.2.1).trans h12₂).trans k1.2.2.1).trans h12
  have e13 : Y₄.cpu.gpr.r13 = g₀.r13 := (((h13₄.trans k3.2.2.2.1).trans h13₂).trans k1.2.2.2.1).trans h13
  have e14 : Y₄.cpu.gpr.r14 = g₀.r14 := (((h14₄.trans k3.2.2.2.2.1).trans h14₂).trans k1.2.2.2.2.1).trans h14
  have e15 : Y₄.cpu.gpr.r15 = g₀.r15 := (((h15₄.trans k3.2.2.2.2.2).trans h15₂).trans k1.2.2.2.2.2).trans h15
  -- the two signals in the set
  refine (c_314 prof fb).run c₂ hB₂.fsb hin _ hK₄ hA₄ hr₄ vc_314 ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have e40 : eaD Y₅ 4 40 = g₀.rsp - 176#64 := by
    show Y₅.cpu.gpr.rsp + 40#64 = _
    rw [hg₅]
    show Y₄.cpu.gpr.rsp + 40#64 = _
    rw [hsp₄]
    bv_omega
  refine c₂.s_or_mr64 hK₅ hA₅ hin (lt_len (by decide)) hr₅ (or_340 _)
    (by rw [e40]; exact off_ft hL.hst 376 (by bv_omega) (by decide)) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  rw [e40] at hA₆
  obtain ⟨V₆, hA₆, hF₆⟩ : ∃ V₆, Agree F Y₆.proc.mm.mem V₆ ∧ Fr G V₆ g₀.rsp r12 rbp cn :=
    ⟨_, hA₆, hF₄.lo hL.hsp (toBytesLE_length _ _) (by bv_omega) (by bv_omega)⟩
  refine (c_345 prof fb).run c₂ hB₂.fsb hin _ hK₆ hA₆ hr₆ vc_345 ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have hg₇' : Y₇.cpu.gpr =
      { Y₄.cpu.gpr with rax := BitVec.setWidth 64 14#32, rdx := BitVec.setWidth 64 0#32, rsi := Y₄.cpu.gpr.rbp,
                        rdi := BitVec.setWidth 64 1#32, r10 := BitVec.setWidth 64 8#32 } := by
    rw [hg₇, hg₆, hg₅]
  -- `rt_sigprocmask`
  refine c₂.b_sigunblock hB₂ hK₇ hA₇ hin (lt_len (by decide)) hr₇ (sys_350 _) (by rw [hg₇']; rfl)
    (by rw [hg₇']; rfl) ?_ (by rw [hg₇']; rfl) (by rw [hg₇']; rfl) ?_ ?_ ?_
  · rw [hg₇']
    show Y₄.cpu.gpr.rbp ≠ 0
    rw [ebp]
    bv_omega
  · rw [hg₇']
    show Y₄.cpu.gpr.rbp.toNat + 8 ≤ _
    rw [ebp]
    exact Nat.le_trans (by bv_omega) htop
  · rw [hg₇']
    show ∀ i < 8, Foot F.data (Addr.add Y₄.cpu.gpr.rbp i)
    rw [ebp]
    exact fun i hi => hL.hws _ (off_ft hL.hst 376 (by bv_omega) (by decide) i hi)
  intro s₃ t₈ c₃ hB₃ hA₈ hr₈ hg₈ _
  have hev₃ : sysEv Y₇ 0 = mskEv g₀.rsp := by simp only [sysEv, hg₇', ebp, h8₄, h9₄]
  rw [hev₃]
  refine k s₃ _ _ s₃ t₈ c₃ hB₃ (KeptW.refl _ _) hA₈ hF₆ hr₈ rfl ?_ ?_ ?_
  · rw [hg₈]
    unfold sysGpr
    rw [hg₇']
    exact ⟨hsp₄, ebp, e12, ebx, e13, e14, e15⟩
  · rw [hg₈]
    unfold sysGpr
    rw [hg₇']
    exact h8₄
  · rw [hg₈]
    unfold sysGpr
    rw [hg₇']
    exact h9₄

end FV7z.Pim
