import FV7z.Pim.Frame
/-!
# `__pthread_initialize_minimal_internal`, from its entry to the two handlers' set (PLAN.md G3, startup)

The first stretch of the function at `0x6000b0`, to offset 251: the prologue, `set_tid_address`, the thread
descriptor's fields (`tid`, `specific[0]`, `user_stack`, the robust list's head and its offset), `set_robust_list`,
`stackblock_size`, the descriptor on the list `__stack_user`, `report_events`, the action's flags and its empty set of
signals (`rep stos`).

- `Lay`: what the function needs of the footprint and of where the stack, the thread's block and the image are.
- `MemA`: the bytes outside the frame after the stretch, stores from those of the entry.
- `Rg`: the registers in the function's body.
- `tidEv`, `robEv`: the two system calls' events.
- `vc_0` … `vc_193`: the verification conditions; `pim_a`: the stretch.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- What the function, entered with the stack pointer `sp` in a run with the `fs` base `fb`, needs of the footprint:
the 552 bytes below `sp`, the thread's block and the image's data in what the run may store into; the image, the
block and the stack in this order. -/
structure Lay (F : Footprint) (Wl : List Rgn) (sp fb : Addr) : Prop where
  hsp : 552 < sp.toNat
  hst : ∀ i < 552, Foot Wl (Addr.add (sp - 552#64) i)
  htcb : ∀ i < 1704, Foot Wl (Addr.add fb i)
  hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a
  hws : ∀ y, Foot Wl y → Foot F.data y
  hfb : 0x7a9000 ≤ fb.toNat
  hlo : fb.toNat + 1704 ≤ sp.toNat - 552

/-- Bytes of the image's data. -/
theorem Lay.gl {sp fb : Addr} (h : Lay F Wl sp fb) {x : Addr} {n : Nat} (h1 : 0x777000 ≤ x.toNat)
    (h2 : x.toNat + n ≤ 0x7a9000) : ∀ i < n, Foot Wl (Addr.add x i) := fun i hi =>
  h.hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)

/-- The bytes outside the frame at offset 251, from the bytes `V` at the entry: the thread's id, `specific[0]`,
`user_stack`, the robust list's offset and head, `stackblock_size`, the list `__stack_user` with the descriptor on
it, `report_events`. -/
def MemA (V : Addr → Byte) (fb : Addr) (tid : Nat) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (fb + 720#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 tid)) 4))
    (fb + 1296#64) (toBytesLE (fb + 784#64) 8))
    (fb + 1554#64) (toBytesLE (1#8) 1))
    (fb + 744#64) (toBytesLE (18446744073709551584#64) 8))
    (fb + 728#64) (toBytesLE ((fb + 736#64) ++ (fb + 736#64)) 16))
    (fb + 1688#64) (toBytesLE rdq(V, 7937200#64) 8))
    (7991568#64) (toBytesLE (7991568#64) 8))
    (7991576#64) (toBytesLE (fb + 704#64) 8))
    (fb + 704#64) (toBytesLE (7991568#64 ++ 7991568#64) 16))
    (7991568#64) (toBytesLE (fb + 704#64) 8))
    (fb + 1553#64) (toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 32 rdb(V, 7991632#64))) 1)

/-- The registers `g'` in the function's body, entered with `g`: the frame, the action's address in `r12`, its set
of signals' in `rbp`. -/
structure Rg (g g' : Gprs) : Prop where
  rsp : g'.rsp = g.rsp - 216#64
  rbp : g'.rbp = g.rsp - 176#64
  r12 : g'.r12 = g.rsp - 184#64
  rbx : g'.rbx = g.rbx
  r13 : g'.r13 = g.r13
  r14 : g'.r14 = g.r14
  r15 : g'.r15 = g.r15

/-- The event of `set_tid_address`, the function entered with registers `g`. -/
abbrev tidEv (g : Gprs) (fb : Addr) (tid : Nat) : Event :=
  ⟨BitVec.setWidth 64 218#32, [fb + 720#64, g.rsi, fb, g.r10, 7991568#64, g.r9], BitVec.ofNat 64 tid, [], []⟩

/-- The event of `set_robust_list`. -/
abbrev robEv (g : Gprs) (fb : Addr) : Event :=
  ⟨BitVec.setWidth 64 273#32, [fb + 736#64, BitVec.setWidth 64 24#32, fb, g.r10, 7991568#64, g.r9], 0, [], []⟩

theorem lane_sw (x : BitVec 64) : lane 64 (x.setWidth 128) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lane, hi]
  intro _
  omega

/-! ## The verification conditions -/

/-- The two pushes. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 14 ∧ g' = { g with rsp := g.rsp - 8 - 8, r8 := 7991568#64 } ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  exact ⟨h1, h2⟩

/-- The thread's descriptor. -/
theorem vc_19 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot F.data ((fb + 16#64).add i)) :
    wp F Wl (o1 fb) (fun g' _ V' => g' = { g with rdx := rdq(V, fb + 16#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o1, Op.ldf]
  exact h1

/-- The frame and the stack guard's copy, to `set_tid_address`. -/
theorem vc_32 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot F.data ((fb + 40#64).add i))
    (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 200#64 + 184#64) i)) :
    wp F Wl (o2 fb) (fun g' _ V' =>
      g' = { g with rax := BitVec.setWidth 64 218#32, rsp := g.rsp - 200#64, rdi := g.rdx + 720#64 } ∧
      V' = Vst V (g.rsp - 200#64 + 184#64) (toBytesLE rdq(V, fb + 40#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o2, Op.ldf]
  exact ⟨h1, h2⟩

/-- The descriptor's fields, to `set_robust_list`. -/
theorem vc_72 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdx : g.rdx = fb)
    (h : ∀ i < 1704, Foot Wl (Addr.add fb i)) :
    wp F Wl (o3 fb) (fun g' _ V' =>
      g' = { g with rax := BitVec.setWidth 64 273#32, rsi := BitVec.setWidth 64 24#32, rdi := fb + 736#64 } ∧
      V' = Vst (Vst (Vst (Vst V (fb + 720#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4)) (fb + 1296#64)
        (toBytesLE (fb + 784#64) 8)) (fb + 1554#64) (toBytesLE (1#8) 1)) (fb + 744#64)
        (toBytesLE (18446744073709551584#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdx
  subst hdx
  wpx [o3, Op.ldf, Op.stf, Op.stfi]
  exact ⟨off_ft h 720 rfl (by decide), off_ft h 1296 rfl (by decide), off_ft h 1554 rfl (by decide),
    off_ft h 744 rfl (by decide)⟩

/-- `stackblock_size` and the list's two pointers. -/
theorem vc_149 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdx : g.rdx = fb) (h8 : g.r8 = 7991568#64)
    (h : ∀ i < 1704, Foot Wl (Addr.add fb i)) (h1 : ∀ i < 8, Foot F.data (Addr.add 7937200#64 i))
    (h2 : ∀ i < 8, Foot Wl (Addr.add 7991568#64 i)) (h3 : ∀ i < 8, Foot Wl (Addr.add 7991576#64 i)) :
    wp F Wl (o4 fb) (fun g' _ V' => g' = { g with rax := fb + 704#64 } ∧
      V' = Vst (Vst (Vst V (fb + 1688#64) (toBytesLE rdq(V, 7937200#64) 8)) (7991568#64)
        (toBytesLE (7991568#64) 8)) (7991576#64) (toBytesLE (fb + 704#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdx h8
  subst hdx h8
  wpx [o4, Op.ldf, Op.stf, Op.lda, Op.sta]
  exact ⟨h1, off_ft h 1688 rfl (by decide), h2, h3⟩

/-- The list's first pointer, `report_events`, the action's flags; the registers of `rep stos`. -/
theorem vc_193 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ∀ i < 1704, Foot Wl (Addr.add fb i)) (h1 : ∀ i < 8, Foot Wl (Addr.add 7991568#64 i))
    (h2 : ∀ i < 1, Foot F.data (Addr.add 7991632#64 i)) (h3 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 168#64) i)) :
    W_193 fb F Wl (fun j' g' _ V' => j' = 248 ∧
      g' = { g with rax := BitVec.setWidth 64 0#32, rcx := BitVec.setWidth 64 16#32, rdx := BitVec.setWidth 64 0#32,
                    rbp := g.rsp + 40#64, rdi := g.rsp + 40#64, r12 := g.rsp + 32#64 } ∧
      V' = Vst (Vst (Vst V (7991568#64) (toBytesLE g.rax 8)) (fb + 1553#64) (toBytesLE (BitVec.setWidth 8
        (BitVec.setWidth 32 rdb(V, 7991632#64))) 1)) (g.rsp + 168#64) (toBytesLE (4#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e : rdb(Vst V (7991568#64) (toBytesLE rax 8), 7991632#64) = rdb(V, 7991632#64) :=
    congrArg (ofBytesLE 8) (vr (by ln) (by decide) (by decide) (by decide))
  wpx [W_193, o5, Op.ldf, Op.stf, Op.stfi, Op.stf8, Op.sta, Op.ldzxa, BitVec.xor_self, e]
  exact ⟨h1, h2, off_ft h 1553 rfl (by decide), h3⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 1600000 in
/-- From the entry to offset 251. The run goes on from a new start, after the two system calls that change the
kernel's record of the thread. -/
theorem pim_a {lim : Nat} {b fb : Addr} {kst : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fb kst)
    (hin : CodeIn L pim_at pim) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pim_at)
    (hL : Lay F Wl X.cpu.gpr.rsp fb) (hself : rdq(V, fb + 16#64) = fb)
    (k : ∀ s₁ V' g' Z t', Seg prof F Wl L s₁ o → Base s₁ lim b fb kst → KeptW Wl s₁ Z →
      Agree F Z.proc.mm.mem V' →
      Fr (MemA V fb kst.tid) V' X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp rdq(V, fb + 40#64) →
      Z.cpu.rip = pim_at.add 251 → Z.cpu.gpr = g' → Rg X.cpu.gpr g' → g'.rdx = 0 → g'.r9 = X.cpu.gpr.r9 →
      GoG prof L o (gev ++ [tidEv X.cpu.gpr fb kst.tid] ++ [robEv X.cpu.gpr fb]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := X.cpu.gpr.rsp.isLt
  have tcbd : ∀ (d n : Nat), d + n ≤ 1704 → ∀ i < n, Foot F.data ((fb + BitVec.ofNat 64 d).add i) :=
    fun d n h i hi => hL.hws _ (off_ft hL.htcb d rfl h i hi)
  -- the pushes
  refine (c_0 prof fb).run c hB.fsb hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (off_ft hL.hst 544 (by bv_omega) (by decide)) (off_ft hL.hst 536 (by bv_omega) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  -- `movq xmm0, r8`
  refine c.s_movq_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (movq_14 _) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
  have hx₂' : xlo Y₂ 0 = (7991568#64).setWidth 128 := by
    rw [hx₂]
    show ((Y₁.cpu.gpr.get (regOf 8)).setWidth 64).setWidth 128 = _
    rw [hg₁]
    rfl
  -- the descriptor's address
  refine c.runV hB.fsb hin (blk_19 prof fb) rfl _ hK₂ hA₂ hr₂ (vc_19 (tcbd 16 8 (by decide))) ?_
  rintro g fl V₃ ⟨rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hv₃
  -- `punpcklqdq xmm0, xmm0`
  refine c.s_punpcklqdq hK₃ hA₃ hin (lt_len (by decide)) hr₃ (punp_28 _) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hx₄, -⟩
  have hx₄' : xlo Y₄ 0 = 7991568#64 ++ 7991568#64 := by
    have h3 : xlo Y₃ 0 = (7991568#64).setWidth 128 := by
      show (Y₃.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
      rw [hv₃]
      exact hx₂'
    rw [hx₄, h3, lane_sw]
  have hself' : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8), fb + 16#64) = fb := by
    refine Eq.trans (congrArg (ofBytesLE 64) ?_) hself
    repeat pv
  have hg₄' : Y₄.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8 - 8, r8 := 7991568#64, rdx := fb } := by
    rw [hg₄, hg₃, hg₂, hg₁, hself']
  -- the frame, to `set_tid_address`
  refine c.runV hB.fsb hin (blk_32 prof fb) rfl _ hK₄ hA₄ hr₄ (vc_32 (tcbd 40 8 (by decide))
    (by rw [hg₄']; exact off_ft hL.hst 520 (by bv_omega) (by decide))) ?_
  rintro g fl V₅ ⟨rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hv₅
  rw [hg₄'] at hg₅ hA₅
  obtain ⟨V₅, hA₅, hF₅⟩ : ∃ V₅, Agree F Y₅.proc.mm.mem V₅ ∧
      Fr V V₅ X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp rdq(V, fb + 40#64) := by
    refine ⟨_, hA₅, fun a ha => ?_, ?_, ?_, ?_⟩
    · repeat pv
    · repeat pv
      rw [show X.cpu.gpr.rsp - 8#64 = X.cpu.gpr.rsp - 8 from rfl, vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · pv
      rw [show X.cpu.gpr.rsp - 16#64 = X.cpu.gpr.rsp - 8 - 8 from by bv_omega, vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [show X.cpu.gpr.rsp - 32#64 = X.cpu.gpr.rsp - 8 - 8 - 200#64 + 184#64 from by bv_omega,
        vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]
      repeat pv
  -- `set_tid_address`
  refine c.b_set_tid hB hK₅ hA₅ hin (lt_len (by decide)) hr₅ (sys_70 _) (by rw [hg₅]; rfl) ?_
  intro s₁ t₆ c₁ hB₁ hA₆ hr₆ hg₆ hv₆
  have hev : sysEv Y₅ (BitVec.ofNat 64 kst.tid) = tidEv X.cpu.gpr fb kst.tid := by simp only [sysEv, hg₅]
  rw [hev]
  have hx₆ : xlo s₁ 0 = 7991568#64 ++ 7991568#64 := by
    show (s₁.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₆, hv₅]
    exact hx₄'
  -- the descriptor's fields
  refine c₁.runV hB₁.fsb hin (blk_72 prof fb) rfl _ (KeptW.refl _ _) hA₆ hr₆
    (vc_72 (by rw [hg₆]; unfold sysGpr; rw [hg₅]; rfl) hL.htcb) ?_
  rintro g fl V₇ ⟨rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ hv₇
  have hax₆ : s₁.cpu.gpr.rax = BitVec.ofNat 64 kst.tid := by rw [hg₆]; rfl
  rw [hax₆] at hA₇
  -- `movq xmm1, rdi`, `punpcklqdq xmm1, xmm1`
  refine c₁.s_movq_rx hK₇ hA₇ hin (lt_len (by decide)) hr₇ (movq_131 _) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈, hx₈, hk₈⟩
  refine c₁.s_punpcklqdq hK₈ hA₈ hin (lt_len (by decide)) hr₈ (punp_136 _) ?_
  rintro Y₉ t₉ hK₉ hA₉ ⟨hr₉, hg₉, hx₉, hk₉⟩
  have hx₉' : xlo Y₉ 1 = (fb + 736#64) ++ (fb + 736#64) := by
    have h7 : rv Y₇ 64 7 = fb + 736#64 := by
      show (Y₇.cpu.gpr.get (regOf 7)).setWidth 64 = _
      rw [hg₇]
      rfl
    rw [hx₉, hx₈, h7, lane_sw]
  have hx₉₀ : xlo Y₉ 0 = 7991568#64 ++ 7991568#64 := by
    rw [hk₉ 0 (by decide), hk₈ 0 (by decide)]
    show (Y₇.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₇]
    exact hx₆
  have hg₉' : Y₉.cpu.gpr =
      { s₁.cpu.gpr with rax := BitVec.setWidth 64 273#32, rsi := BitVec.setWidth 64 24#32, rdi := fb + 736#64 } := by
    rw [hg₉, hg₈, hg₇]
  have hdx₉ : Y₉.cpu.gpr.rdx = fb := by rw [hg₉', hg₆]; unfold sysGpr; rw [hg₅]; rfl
  -- `movups [rdx + 728], xmm1`
  have e728 : eaD Y₉ 2 728 = fb + 728#64 := by
    show Y₉.cpu.gpr.rdx + 728#64 = _
    rw [hdx₉]
  refine c₁.s_movups_stv hK₉ hA₉ hin (lt_len (by decide)) hr₉ (movups_140 _)
    (by rw [e728]; exact off_ft hL.htcb 728 rfl (by decide)) ?_
  rintro Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀, hv₁₀⟩
  rw [e728, hx₉'] at hA₁₀
  obtain ⟨V₁₀, hA₁₀, hF₁₀⟩ : ∃ V₁₀, Agree F Y₁₀.proc.mm.mem V₁₀ ∧
      Fr (Vst (Vst (Vst (Vst (Vst V
        (fb + 720#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 kst.tid)) 4))
        (fb + 1296#64) (toBytesLE (fb + 784#64) 8))
        (fb + 1554#64) (toBytesLE (1#8) 1))
        (fb + 744#64) (toBytesLE (18446744073709551584#64) 8))
        (fb + 728#64) (toBytesLE ((fb + 736#64) ++ (fb + 736#64)) 16))
        V₁₀ X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp rdq(V, fb + 40#64) := by
    refine ⟨_, hA₁₀, ?_⟩
    repeat (refine Fr.gl ?_ hsp (by ln) (by bv_omega) (by bv_omega))
    exact hF₅
  -- `set_robust_list`
  refine c₁.b_set_robust hB₁ hK₁₀ hA₁₀ hin (lt_len (by decide)) hr₁₀ (sys_147 _) (by rw [hg₁₀, hg₉']; rfl)
    (by rw [hg₁₀, hg₉']; rfl) ?_
  intro s₂ t₁₁ c₂ hB₂ hA₁₁ hr₁₁ hg₁₁ hv₁₁
  have hg₁₀' : Y₁₀.cpu.gpr =
      { X.cpu.gpr with rax := BitVec.setWidth 64 273#32, rcx := Y₅.cpu.rip.add 2, rdx := fb,
                       rsp := X.cpu.gpr.rsp - 8 - 8 - 200#64, rsi := BitVec.setWidth 64 24#32,
                       rdi := fb + 736#64, r8 := 7991568#64, r11 := (rf0 Y₅).toBits } := by
    rw [hg₁₀, hg₉', hg₆]
    unfold sysGpr
    rw [hg₅]
    rfl
  have hev₂ : sysEv Y₁₀ 0 = robEv X.cpu.gpr fb := by simp only [sysEv, hg₁₀']
  rw [hev₂]
  have hx₁₁ : xlo s₂ 0 = 7991568#64 ++ 7991568#64 := by
    show (s₂.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₁₁, hv₁₀]
    exact hx₉₀
  have hg₁₁' : s₂.cpu.gpr =
      { X.cpu.gpr with rax := 0, rcx := Y₁₀.cpu.rip.add 2, rdx := fb, rsp := X.cpu.gpr.rsp - 8 - 8 - 200#64,
                       rsi := BitVec.setWidth 64 24#32, rdi := fb + 736#64, r8 := 7991568#64,
                       r11 := (rf0 Y₁₀).toBits } := by
    rw [hg₁₁]
    unfold sysGpr
    rw [hg₁₀']
    rfl
  -- `stackblock_size`, the list's pointers
  refine c₂.runV hB₂.fsb hin (blk_149 prof fb) rfl _ (KeptW.refl _ _) hA₁₁ hr₁₁
    (vc_149 (by rw [hg₁₁']) (by rw [hg₁₁']) hL.htcb (fun i hi => hL.hws _ (hL.gl (by decide) (by decide) i hi))
      (hL.gl (by decide) (by decide)) (hL.gl (by decide) (by decide))) ?_
  rintro g fl V₁₂ ⟨rfl, rfl⟩ Y₁₂ t₁₂ hK₁₂ hA₁₂ hr₁₂ hg₁₂ hv₁₂
  -- `movups [rdx + 704], xmm0`
  have e704 : eaD Y₁₂ 2 704 = fb + 704#64 := by
    show Y₁₂.cpu.gpr.rdx + 704#64 = _
    rw [hg₁₂, hg₁₁']
  refine c₂.s_movups_stv hK₁₂ hA₁₂ hin (lt_len (by decide)) hr₁₂ (movups_186 _)
    (by rw [e704]; exact off_ft hL.htcb 704 rfl (by decide)) ?_
  rintro Y₁₃ t₁₃ hK₁₃ hA₁₃ ⟨hr₁₃, hg₁₃, -⟩
  have hx₁₂ : xlo Y₁₂ 0 = 7991568#64 ++ 7991568#64 := by
    show (Y₁₂.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₁₂]
    exact hx₁₁
  have e1 : rdq(V₁₀, 7937200#64) = rdq(V, 7937200#64) := by
    refine congrArg (ofBytesLE 64) ((hF₁₀.rd (by decide) (by bv_omega)).trans ?_)
    repeat pv
  rw [e704, hx₁₂, e1] at hA₁₃
  obtain ⟨V₁₃, hA₁₃, hF₁₃⟩ : ∃ V₁₃, Agree F Y₁₃.proc.mm.mem V₁₃ ∧
      Fr (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
        (fb + 720#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 kst.tid)) 4))
        (fb + 1296#64) (toBytesLE (fb + 784#64) 8))
        (fb + 1554#64) (toBytesLE (1#8) 1))
        (fb + 744#64) (toBytesLE (18446744073709551584#64) 8))
        (fb + 728#64) (toBytesLE ((fb + 736#64) ++ (fb + 736#64)) 16))
        (fb + 1688#64) (toBytesLE rdq(V, 7937200#64) 8))
        (7991568#64) (toBytesLE (7991568#64) 8))
        (7991576#64) (toBytesLE (fb + 704#64) 8))
        (fb + 704#64) (toBytesLE (7991568#64 ++ 7991568#64) 16))
        V₁₃ X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp rdq(V, fb + 40#64) := by
    refine ⟨_, hA₁₃, ?_⟩
    repeat (refine Fr.gl ?_ hsp (by ln) (by bv_omega) (by bv_omega))
    exact hF₁₀
  have e2 : rdb(V₁₃, 7991632#64) = rdb(V, 7991632#64) := by
    refine congrArg (ofBytesLE 8) ((hF₁₃.rd (by decide) (by bv_omega)).trans ?_)
    repeat pv
  have hg₁₃' : Y₁₃.cpu.gpr = { s₂.cpu.gpr with rax := fb + 704#64 } := by rw [hg₁₃, hg₁₂]
  -- the list's first pointer, `report_events`, the action's flags
  refine (c_193 prof fb).run c₂ hB₂.fsb hin _ hK₁₃ hA₁₃ hr₁₃
    (vc_193 hL.htcb (hL.gl (by decide) (by decide)) (fun i hi => hL.hws _ (hL.gl (by decide) (by decide) i hi))
      (by rw [hg₁₃', hg₁₁']; exact off_ft hL.hst 504 (by bv_omega) (by decide))) ?_
  rintro j' g fl V₁₄ ⟨rfl, rfl, rfl⟩ Y₁₄ t₁₄ hK₁₄ hA₁₄ hr₁₄ hg₁₄ -
  rw [hg₁₃', hg₁₁'] at hg₁₄ hA₁₄
  dsimp only at hg₁₄ hA₁₄
  rw [e2] at hA₁₄
  -- `rep stos`
  refine c₂.s_rep_stosq hB₂.df hin (lt_len (j := 250) (by decide)) (lt_len (by decide)) (stos_248 _) 15 hK₁₄ hA₁₄
    hr₁₄ (by rw [hg₁₄]; rfl) (by rw [hg₁₄]; exact off_ft hL.hst 376 (by bv_omega) (by decide)) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hg₁₄] at hgZ hAZ
  dsimp only at hgZ hAZ
  refine k s₂ _ _ Z t' c₂ hB₂ hKZ hAZ ?_ hrZ hgZ ?_ rfl rfl
  · refine Fr.fill hsp _ 16 ?_ (by bv_omega) (by bv_omega)
    refine Fr.lo ?_ hsp (by ln) (by bv_omega) (by bv_omega)
    unfold MemA
    repeat (refine Fr.gl ?_ hsp (by ln) (by bv_omega) (by bv_omega))
    exact hF₁₃
  · refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · show X.cpu.gpr.rsp - 8 - 8 - 200#64 = X.cpu.gpr.rsp - 216#64
      bv_omega
    · show X.cpu.gpr.rsp - 8 - 8 - 200#64 + 40#64 = X.cpu.gpr.rsp - 176#64
      bv_omega
    · show X.cpu.gpr.rsp - 8 - 8 - 200#64 + 32#64 = X.cpu.gpr.rsp - 184#64
      bv_omega

end FV7z.Pim
