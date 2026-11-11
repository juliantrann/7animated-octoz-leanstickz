import FV7z.Tls.PartB
/-!
# `__libc_setup_tls`: from the return of `memcpy` to the `ret` (PLAN.md G3, startup)

- `tls_c`: the three words of the thread control block at `c + 2176` (the bytes `WC`) and
  `arch_prctl (ARCH_SET_FS, c + 2176)`: the run goes on from the state after the `syscall`, a new start with the
  `fs` base there (`Seg.b_set_fs`).
- `tls_d`: the stores of the end (the bytes `WD`), with the three SSE moves that copy the two sizes, to the `ret`
  with the saved registers back.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)

namespace FV7z.Tls
variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- The bytes at the `syscall`, from those after `memcpy`: the thread control block's three words. -/
abbrev WC (W : Addr → Byte) (c : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (c + 2176#64 + 8#64) (toBytesLE 8027920#64 8)) (c + 2176#64) (toBytesLE (c + 2176#64) 8))
    (c + 2176#64 + 16#64) (toBytesLE (c + 2176#64) 8)

set_option maxHeartbeats 1600000 in
/-- From the return of `memcpy` through `arch_prctl (ARCH_SET_FS, c + 2176)`, `c` the block's address: the run goes
on from the state after the `syscall`, its own start, with the `fs` base at the thread control block. -/
theorem tls_c {G : Footprint} {Wn : List Rgn} {s₁ Y : State} {W : Addr → Byte} {q c : Addr} {lim : Nat}
    {bb fsb : Addr} {ks : Kst} (cs : Seg prof G Wn L s₁ o) (hB : Base s₁ lim bb fsb ks) (hin : CodeIn L tls_at tls)
    (hK : KeptW Wn s₁ Y) (hA : Agree G Y.proc.mm.mem W) (hr : Y.cpu.rip = tls_at.add 304)
    (hsp : Y.cpu.gpr.rsp = q) (hbx : Y.cpu.gpr.rbx = 2176#64) (h24 : rdq(W, q + 24#64) = c)
    (hl : ∀ i < 8, Foot G.data (Addr.add (q + 24#64) i)) (hst : ∀ i < 24, Foot Wn (Addr.add (c + 2176#64) i))
    (hc : (c + 2176#64).toNat < 2 ^ 47 - 4096)
    (k : ∀ s₂ t', Seg prof G Wn L s₂ o → Base s₂ lim bb (c + 2176#64) ks → Agree G s₂.proc.mm.mem (WC W c) →
      s₂.cpu.rip = tls_at.add 343 →
      (s₂.cpu.gpr.rax = 0#64 ∧ s₂.cpu.gpr.rsp = q ∧ s₂.cpu.gpr.rbp = Y.cpu.gpr.rbp ∧
        s₂.cpu.gpr.r12 = Y.cpu.gpr.r12 ∧ s₂.cpu.gpr.r13 = Y.cpu.gpr.r13 ∧ s₂.cpu.gpr.r14 = Y.cpu.gpr.r14 ∧
        s₂.cpu.gpr.r15 = Y.cpu.gpr.r15) →
      GoG prof L o (gev ++ [⟨158#64, [4098#64, c + 2176#64, Y.cpu.gpr.rdx, Y.cpu.gpr.r10, Y.cpu.gpr.r8,
        Y.cpu.gpr.r9], 0, [], []⟩]) gP gE s₂ t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_304 prof).run cs hin _ hK hA hr (vc_304 hbx (by rw [hsp]; exact hl) hst (by rw [hsp]; exact h24)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsi : Y₁.cpu.gpr.rsi = c + 2176#64 := by rw [hg₁]; rfl
  refine cs.b_set_fs hB hK₁ hA₁ hin (lt_len (by decide)) hr₁ (sys_341 _) (by rw [hg₁]; rfl) (by rw [hg₁]; rfl)
    (by rw [hsi]; exact hc) ?_
  have ev : sysEv Y₁ 0 = ⟨158#64, [4098#64, c + 2176#64, Y.cpu.gpr.rdx, Y.cpu.gpr.r10, Y.cpu.gpr.r8,
      Y.cpu.gpr.r9], 0, [], []⟩ := by
    simp only [sysEv, hg₁]
    rfl
  rw [ev, hsi]
  intro s₂ t₂ c₂ hB₂ hA₂ hr₂ hg₂
  refine k s₂ t₂ c₂ hB₂ hA₂ hr₂ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg₂]; rfl
  · rw [hg₂]; show Y₁.cpu.gpr.rsp = q; rw [hg₁]; exact hsp
  · rw [hg₂]; show Y₁.cpu.gpr.rbp = _; rw [hg₁]; rfl
  · rw [hg₂]; show Y₁.cpu.gpr.r12 = _; rw [hg₁]; rfl
  · rw [hg₂]; show Y₁.cpu.gpr.r13 = _; rw [hg₁]; rfl
  · rw [hg₂]; show Y₁.cpu.gpr.r14 = _; rw [hg₁]; rfl
  · rw [hg₂]; show Y₁.cpu.gpr.r15 = _; rw [hg₁]; rfl

/-- The bytes at the `ret`, from those after `arch_prctl`; `x13` is the address of the initialisation image. -/
abbrev WD (W : Addr → Byte) (x13 : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst W 7944480#64 (toBytesLE 8#64 8)) 8027888#64
    (toBytesLE 8008672#64 8)) 7944456#64 (toBytesLE x13 8)) 7944464#64
    (toBytesLE 2361183241434822606888#128 16)) 8008712#64 (toBytesLE 7943392#64 8)) 8027880#64 (toBytesLE 128#64 8))
    7944504#64 (toBytesLE 1#64 8)) 8027856#64 (toBytesLE 64#64 8)) 8008672#64 (toBytesLE 64#64 8)) 8027864#64
    (toBytesLE 1#64 8)) 7938736#64 (toBytesLE 4480#64 8)) 8027872#64 (toBytesLE 1#64 8)

set_option maxHeartbeats 1600000 in
/-- From after `arch_prctl`, which has returned 0, to the `ret`. -/
theorem tls_d {G : Footprint} {Wn : List Rgn} {s₂ Y : State} {W : Addr → Byte} {q : Addr} {g₀ : Gprs}
    {x13 : BitVec 64} (cs : Seg prof G Wn L s₂ o) (hin : CodeIn L tls_at tls)
    (hK : KeptW Wn s₂ Y) (hA : Agree G Y.proc.mm.mem W) (hr : Y.cpu.rip = tls_at.add 343)
    (hax : Y.cpu.gpr.rax = 0#64) (hsp : Y.cpu.gpr.rsp = q) (hbp : Y.cpu.gpr.rbp = 64#64)
    (h12 : Y.cpu.gpr.r12 = 8#64) (h13 : Y.cpu.gpr.r13 = x13) (h14 : Y.cpu.gpr.r14 = 7943392#64)
    (h15 : Y.cpu.gpr.r15 = 128#64) (hfr : Fr q g₀ W) (hs : rdq(W, 7938736#64) = 2048#64)
    (hq : 0x7a9000 ≤ q.toNat) (hq' : q.toNat + 88 ≤ 2 ^ 64)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wn a)
    (hst : ∀ i < 88, Foot G.data (Addr.add q i))
    (k : ∀ Z t', KeptW Wn s₂ Z → Agree G Z.proc.mm.mem (WD W x13) → Z.cpu.rip = tls_at.add 523 →
      (Z.cpu.gpr.rsp = q + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧ Z.cpu.gpr.rax = 4480#64 ∧ Z.cpu.gpr.rbx = g₀.rbx ∧
        Z.cpu.gpr.rbp = g₀.rbp ∧ Z.cpu.gpr.r12 = g₀.r12 ∧ Z.cpu.gpr.r13 = g₀.r13 ∧ Z.cpu.gpr.r14 = g₀.r14 ∧
        Z.cpu.gpr.r15 = g₀.r15) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have slot : ∀ a : Addr, ∀ k < 88, a = Addr.add q k → Foot G.data a := fun a k hk ha => ha ▸ hst k hk
  refine (c_343 prof).run cs hin _ hK hA hr (vc_343 hax) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  obtain rfl : W = V₁ := hV.symm
  have hsp₁ : Y₁.cpu.gpr.rsp = q := by rw [hg₁]; exact hsp
  -- `movq xmm0, [rsp + 8]`
  have e8 : eaD Y₁ 4 8 = q + 8#64 := by
    show Y₁.cpu.gpr.rsp + 8#64 = _
    rw [hsp₁]
  refine cs.s_movq_ld hK₁ hA₁ hin (lt_len (by decide)) hr₁ (movq_375 _) (fun i hi => ?_) ?_
  · rw [e8]
    exact slot _ (8 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂⟩
  rw [e8, hfr.fs] at hx₂
  have e12 : Y₂.cpu.gpr.r12 = 8#64 := by rw [hg₂, hg₁]; exact h12
  have eax : Y₂.cpu.gpr.rax = 8008672#64 := by rw [hg₂, hg₁]; rfl
  refine cs.s_blkA_v hin (blk_381 prof) Y₂.cpu.vec hK₂ hA₂ hr₂ rfl rfl
    (vc_381 (by rw [hg₂, hg₁]; exact h14) hgl cs.hws hs ?_)
  intro fl Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  rw [e12, eax] at hA₃
  -- `movhps xmm0, [rsp + 16]`
  have e16 : eaD Y₃ 4 16 = q + 16#64 := by
    show Y₃.cpu.gpr.rsp + 16#64 = _
    rw [hg₃, hg₂]
    show Y₁.cpu.gpr.rsp + 16#64 = _
    rw [hsp₁]
  refine cs.s_movhps_ld hK₃ hA₃ hin (lt_len (by decide)) hr₃ (movhps_402 _) (fun i hi => ?_) ?_
  · rw [e16]
    exact slot _ (16 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hx₄⟩
  have hx₃ : xlo Y₃ 0 = (40#64).setWidth 128 := by
    show (Y₃.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₃]
    exact hx₂
  have hms : rdq(Vst (Vst W 7944480#64 (toBytesLE 8#64 8)) 8027888#64 (toBytesLE 8008672#64 8), q + 16#64) =
      128#64 := by
    rw [rd_Vst, rd_Vst]
    · exact hfr.ms
    all_goals sd
  have ex : (128#64 ++ lane 64 ((40#64).setWidth 128) 0).setWidth 128 = 2361183241434822606888#128 := by decide
  rw [e16, hms, hx₃, ex] at hx₄
  have e13 : Y₄.cpu.gpr.r13 = x13 := by rw [hg₄, hg₃, hg₂, hg₁]; exact h13
  refine cs.s_blkA_v hin ((blk_407 prof).at tls_at) Y₄.cpu.vec hK₄ hA₄ hr₄ rfl rfl
    (vc_407 (by rw [hg₄, hg₃, hg₂, hg₁]; exact h14) hgl ?_)
  intro fl Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ hv₅
  have e15₄ : Y₄.cpu.gpr.r15 = 128#64 := by rw [hg₄, hg₃, hg₂, hg₁]; exact h15
  have eax₄ : Y₄.cpu.gpr.rax = 2048#64 := by rw [hg₄, hg₃]; rfl
  have esum : 128#64 + 2048#64 + 63#64 = 2239#64 := by decide
  rw [e13] at hA₅
  rw [e15₄, eax₄, esum] at hg₅
  -- `movups [r14 + 0x430], xmm0`
  have e14 : eaD Y₅ 14 1072 = 7944464#64 := by
    show Y₅.cpu.gpr.r14 + 1072#64 = _
    rw [hg₅, hg₄, hg₃, hg₂, hg₁]
    show Y.cpu.gpr.r14 + 1072#64 = _
    rw [h14]
    decide
  refine cs.s_movups_st hK₅ hA₅ hin (lt_len (by decide)) hr₅ (movups_419 _) (fun i hi => ?_) ?_
  · rw [e14]
    exact hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  have hx₅ : xlo Y₅ 0 = 2361183241434822606888#128 := by
    show (Y₅.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₅]
    exact hx₄
  rw [e14, hx₅] at hA₆
  have hsp₆ : Y₆.cpu.gpr.rsp = q := by rw [hg₆, hg₅, hg₄, hg₃, hg₂]; exact hsp₁
  have hax₆ : Y₆.cpu.gpr.rax = 2239#64 := by rw [hg₆, hg₅]; rfl
  have e15 : Y₆.cpu.gpr.r15 = 128#64 := by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; exact h15
  have ebp : Y₆.cpu.gpr.rbp = 64#64 := by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; exact hbp
  refine (c_427 prof).run cs hin _ hK₆ hA₆ hr₆ (vc_427 hax₆ (by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; exact h14)
    hgl (fun i hi => ?_) (by rw [hsp₆]; exact hq) (by rw [hsp₆]; exact hq')) ?_
  · rw [hsp₆]
    exact slot _ (40 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [e15, ebp] at hA₇
  have hfr₆ : Fr q g₀ (Vst (Vst (Vst (Vst W 7944480#64 (toBytesLE 8#64 8)) 8027888#64 (toBytesLE 8008672#64 8))
      7944456#64 (toBytesLE x13 8)) 7944464#64 (toBytesLE 2361183241434822606888#128 16)) := by
    refine hfr.keep hq' fun a h1 h2 h3 => ?_
    rw [Vst_out, Vst_out, Vst_out, Vst_out]
    all_goals simp only [toBytesLE_length]
    all_goals bv_omega
  rw [hsp₆, hfr₆.bx, hfr₆.bp, hfr₆.r12, hfr₆.r13, hfr₆.r14, hfr₆.r15] at hg₇
  refine k Y₇ t₇ hK₇ hA₇ hr₇ ?_
  rw [hg₇]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.Tls
