import FV7z.Lif.Cuts
import FV7z.Cti.Holds
import FV7z.Lemmas.FnFar
/-!
# `__libc_init_first` (PLAN.md G3, startup)

glibc 2.31's `__libc_init_first (argc, argv, envp)` at `0x672160` in `7zzs` (static): the weak `_dl_starting_up` is
0, so `__libc_multiple_libcs` is set to 0; `__fpu_control` (`0x793c80`) is compared with `_dl_fpu_control`
(`0x7933cc`), and `__setfpucw` called if they differ; `__libc_argc`, `__libc_argv`, `__environ` are stored; then
`_dl_non_dynamic_init ()`, `__init_misc (argc, argv, envp)`, and a `jmp` to `__ctype_init`. Here the function's own
code, in three pieces between its calls:

- `lif_a`: from the entry to the first instruction of `_dl_non_dynamic_init`, the two control words equal (`LifMem`,
  `lifG`: the bytes and the registers there).
- `lif_b`: from the return of that call (70) to the first instruction of `__init_misc`.
- `lif_c`: from the return of that call (83), by `__ctype_init` (`Cti.cti_ok`), to the return address of
  `__libc_init_first`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Lif

/-- The `call` of `_dl_non_dynamic_init`. -/
def pc65 : List Byte := [0xe8, 0x8a, 0xd6, 0xff, 0xff]
theorem pc65_0 : ∀ feat, Dec feat pc65 0 (FV7z.mk .call 64 [.rel 18446744073709541002] 5) := by dec_rfl
theorem wc65 : pc65 <+: lif.drop 65 := by decide +kernel
theorem call_65 (feat : Features) : Dec feat lif 65 (FV7z.mk .call 64 [.rel 18446744073709541002] 5) :=
  Dec.shift (j := 65) (k := 0) (pc65_0 feat) wc65 (Nat.zero_le _)

/-- The `call` of `__init_misc`. -/
def pc78 : List Byte := [0xe8, 0xed, 0x6b, 0xff, 0xff]
theorem pc78_0 : ∀ feat, Dec feat pc78 0 (FV7z.mk .call 64 [.rel 18446744073709513709] 5) := by dec_rfl
theorem wc78 : pc78 <+: lif.drop 78 := by decide +kernel
theorem call_78 (feat : Features) : Dec feat lif 78 (FV7z.mk .call 64 [.rel 18446744073709513709] 5) :=
  Dec.shift (j := 78) (k := 0) (pc78_0 feat) wc78 (Nat.zero_le _)

/-- The `jmp` to `__ctype_init`. -/
def pj88 : List Byte := [0xe9, 0x23, 0x3f, 0xfa, 0xff]
theorem pj88_0 : ∀ feat, Dec feat pj88 0 (FV7z.mk .jmp 64 [.rel 18446744073709174563] 5) := by dec_rfl
theorem wj88 : pj88 <+: lif.drop 88 := by decide +kernel
theorem jmp_88 (feat : Features) : Dec feat lif 88 (FV7z.mk .jmp 64 [.rel 18446744073709174563] 5) :=
  Dec.shift (j := 88) (k := 0) (pj88_0 feat) wj88 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the three `push`es: `r13`, `r12`, `rbp` below the stack pointer. -/
def LifStk (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8#64) (toBytesLE g.r13 8)) (g.rsp - 16#64) (toBytesLE g.r12 8)) (g.rsp - 24#64)
    (toBytesLE g.rbp 8)

/-- The bytes at the `call` of `_dl_non_dynamic_init`: `__libc_multiple_libcs` 0, `__libc_argc`, `__libc_argv`,
`__environ` the three arguments. -/
def LifMem (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (LifStk V g) 7944640#64 (toBytesLE 0#32 4)) 8029640#64 (toBytesLE (g.rdi.setWidth 32) 4))
    8029648#64 (toBytesLE g.rsi 8)) 8013720#64 (toBytesLE g.rdx 8)

/-- The registers at the `call` of `_dl_non_dynamic_init`, `fp` the control word. -/
def lifG (g : Gprs) (fp : BitVec 16) : Gprs :=
  { g with rax := 0#64, rsp := g.rsp - 24#64, rbp := (g.rdi.setWidth 32).setWidth 64,
           rdi := (fp.setWidth 32).setWidth 64, r12 := g.rsi, r13 := g.rdx }

theorem sw16 (x : BitVec 16) : BitVec.setWidth 16 (BitVec.setWidth 32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem sw32 (x : BitVec 64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = BitVec.setWidth 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24#64) i))
    (hsp : 0x7a9000 + 24 ≤ g.rsp.toNat) (f1 : ∀ i < 2, Foot F.data (Addr.add 7945344#64 i))
    (f2 : ∀ i < 2, Foot F.data (Addr.add 7943116#64 i)) (fw : ∀ i < 4, Foot Wl (Addr.add 7944640#64 i))
    (hfp : rdw(V, 7945344#64) = rdw(V, 7943116#64)) :
    W_0 F Wl (fun j' g' _ V' => j' = 45 ∧ g' = lifG g rdw(V, 7945344#64) ∧
      V' = Vst (LifStk V g) 7944640#64 (toBytesLE 0#32 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hlt := rsp.isLt
  dsimp only at hst hsp
  have w1 : ∀ i < 8, Foot Wl (Addr.add (rsp - 8) i) := fun i hi => by
    have := hst (16 + i) (by omega)
    rwa [show Addr.add (rsp - 24#64) (16 + i) = Addr.add (rsp - 8) i by simp only [Addr.add]; bv_omega] at this
  have w2 : ∀ i < 8, Foot Wl (Addr.add (rsp - 16#64) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (rsp - 24#64) (8 + i) = Addr.add (rsp - 16#64) i by simp only [Addr.add]; bv_omega] at this
  have w3 : ∀ i < 8, Foot Wl (Addr.add (rsp - 24#64) i) := fun i hi => hst i (by omega)
  have r1 : rdw(Vst (Vst (Vst V (rsp - 8) (toBytesLE r13 8)) (rsp - 16#64) (toBytesLE r12 8)) (rsp - 24#64)
      (toBytesLE rbp 8), 7945344#64) = rdw(V, 7945344#64) := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega)]
  have r2 : rdw(Vst (Vst (Vst V (rsp - 8) (toBytesLE r13 8)) (rsp - 16#64) (toBytesLE r12 8)) (rsp - 24#64)
      (toBytesLE rbp 8), 7943116#64) = rdw(V, 7943116#64) := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega)]
  have e2 : rsp - 8 - 8 = rsp - 16#64 := by bv_omega
  have e3 : rsp - 8 - 8 - 8 = rsp - 24#64 := by
    clear e2
    bv_omega
  wpx [W_0, W_96, o0, o4, Op.push, Op.ldzxa, Op.cmpma, Op.stia]
  rw [e3, e2, r1, r2, sw16, hfp]
  refine ⟨w1, w2, w3, fun _ => ⟨f1, f2, fw, fun _ => ⟨?_, rfl⟩, fun h => ?_⟩, fun h => absurd h (by decide)⟩
  · rfl
  · exact absurd h (by simp)

theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot Wl (Addr.add 8029640#64 i))
    (fb : ∀ i < 8, Foot Wl (Addr.add 8029648#64 i)) (fe : ∀ i < 8, Foot Wl (Addr.add 8013720#64 i)) :
    W_45 F Wl (fun j' g' _ V' => j' = 65 ∧ g' = g ∧
      V' = Vst (Vst (Vst V 8029640#64 (toBytesLE (g.rbp.setWidth 32) 4)) 8029648#64 (toBytesLE g.r12 8)) 8013720#64
        (toBytesLE g.r13 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_45, o1, Op.sta]
  exact ⟨fa, fb, fe⟩

/-- The registers at the `call` of `__init_misc`: the three arguments again. -/
def lifB (g : Gprs) : Gprs :=
  { g with rdx := g.r13, rsi := g.r12, rdi := (g.rbp.setWidth 32).setWidth 64 }

theorem vc_70 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_70 F Wl (fun j' g' _ V' => j' = 78 ∧ g' = lifB g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_70, o2]
  rfl

/-- The registers at the `jmp` to `__ctype_init`: the three saved ones popped. -/
def lifC (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rsp := g.rsp + 24#64, rbp := rdq(V, g.rsp), r12 := rdq(V, g.rsp + 8#64), r13 := rdq(V, g.rsp + 16#64) }

theorem vc_83 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 24, Foot F.data (Addr.add g.rsp i)) :
    W_83 F Wl (fun j' g' _ V' => j' = 88 ∧ g' = lifC g V ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl
  have l1 : ∀ i < 8, Foot F.data (Addr.add rsp i) := fun i hi => hl i (by omega)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (rsp + 8#64) i) := fun i hi => by
    have := hl (8 + i) (by omega)
    rwa [show Addr.add rsp (8 + i) = Addr.add (rsp + 8#64) i by simp only [Addr.add]; bv_omega] at this
  have l3 : ∀ i < 8, Foot F.data (Addr.add (rsp + 16#64) i) := fun i hi => by
    have := hl (16 + i) (by omega)
    rwa [show Addr.add rsp (16 + i) = Addr.add (rsp + 16#64) i by simp only [Addr.add]; bv_omega] at this
  have e3 : rsp + 8 + 8 + 8 = rsp + 24#64 := by bv_omega
  have e2 : rsp + 8 + 8 = rsp + 16#64 := by
    clear e3
    bv_omega
  wpx [W_83, o3, Op.pop]
  rw [e3, e2]
  exact ⟨l1, l2, l3, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__libc_init_first (argc, argv, envp)` from its entry to the first instruction of `_dl_non_dynamic_init`
(`0x66f830`), the two control words equal: the bytes are `LifMem` with the return address (70) below the three
saved registers. -/
theorem lif_a {e₂ : Addr} {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lif_at lif)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length) (he : e₂ = 6748208#64) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lif_at)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i)) (hsp : 0x7a9000 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (f1 : ∀ i < 2, Foot F.data (Addr.add 7945344#64 i)) (f2 : ∀ i < 2, Foot F.data (Addr.add 7943116#64 i))
    (fw : ∀ i < 4, Foot Wl (Addr.add 7944640#64 i)) (fa : ∀ i < 4, Foot Wl (Addr.add 8029640#64 i))
    (fb : ∀ i < 8, Foot Wl (Addr.add 8029648#64 i)) (fe : ∀ i < 8, Foot Wl (Addr.add 8013720#64 i))
    (hfp : rdw(V, 7945344#64) = rdw(V, 7943116#64))
    (k : ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (LifMem V X.cpu.gpr) (X.cpu.gpr.rsp - 32#64) (toBytesLE (lif_at.add 70) 8)) →
      Y.cpu.rip = e₂ → Y.cpu.gpr = (lifG X.cpu.gpr rdw(V, 7945344#64)).set 4 (X.cpu.gpr.rsp - 32#64) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have s24 : ∀ i < 24, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24#64) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 32#64) (8 + i) = Addr.add (X.cpu.gpr.rsp - 24#64) i by
      simp only [Addr.add]; bv_omega] at this
  have e1 : (lifG X.cpu.gpr rdw(V, 7945344#64)).rsp - 8 = X.cpu.gpr.rsp - 32#64 := by
    show X.cpu.gpr.rsp - 24#64 - 8 = _
    bv_omega
  have e2 : (lifG X.cpu.gpr rdw(V, 7945344#64)).rbp.setWidth 32 = X.cpu.gpr.rdi.setWidth 32 := sw32 _
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 s24 (by omega) f1 f2 fw hfp) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine (c_45 prof).run c hin _ hK₁ hA₁ hr₁ (vc_45 fa fb fe) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine c.s_call hK₂ hA₂ hin (lt_len (by omega)) hr₂ (call_65 _) hin₂ h₂ (by rw [he]; decide) (fun i hi => ?_) ?_
  · rw [hg₂, hg₁, e1]
    exact hst i (by omega)
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hg₂, hg₁, e1] at hA₃ hg₃
  rw [e2] at hA₃
  exact k Y₃ t₃ hK₃ hA₃ hr₃ hg₃

/-- From the return of `_dl_non_dynamic_init` (70) to the first instruction of `__init_misc` (`0x668da0`), called
with the three arguments. -/
theorem lif_b {e₂ : Addr} {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lif_at lif)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length) (he : e₂ = 6720928#64) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lif_at.add 70)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lif_at.add 83) 8)) →
      Y.cpu.rip = e₂ → Y.cpu.gpr = (lifB X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_70 prof).run c hin _ hK hA hrip vc_70 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e1 : (lifB X.cpu.gpr).rsp = X.cpu.gpr.rsp := rfl
  refine c.s_call hK₁ hA₁ hin (lt_len (by omega)) hr₁ (call_78 _) hin₂ h₂ (by rw [he]; decide) (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ hg₂

/-- From the return of `__init_misc` (83), by `__ctype_init`, to the return address of `__libc_init_first`: the
three saved registers are those on the stack, the thread's three `ctype` pointers stored (`Cti.CtMem`). -/
theorem lif_c {fb lp ct : Addr} {a b cc : BitVec 64} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L lif_at lif) (hci : CodeIn L Cti.cti_at Cti.cti) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lif_at.add 83)
    (hlp : rdq(V, fb - 112#64) = lp) (hct : rdq(V, lp) = ct) (ha : rdq(V, ct + 64#64) = a)
    (hb : rdq(V, ct + 72#64) = b) (hc : rdq(V, ct + 88#64) = cc)
    (f1 : ∀ i < 8, Foot F.data ((fb - 112#64).add i)) (f2 : ∀ i < 8, Foot F.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot F.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl ((fb - 64#64).add i))
    (hfb : 64 ≤ fb.toNat) (hcn : ct.toNat + 96 ≤ 2 ^ 64)
    (hap : ct.toNat + 96 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ ct.toNat + 64)
    (hl : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 32 ≤ 2 ^ 64)
    (hsa : X.cpu.gpr.rsp.toNat + 32 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ X.cpu.gpr.rsp.toNat + 24)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 24#64) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cti.CtMem V fb a b cc) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (Cti.ctG (lifC X.cpu.gpr V) a b cc).set 4 (X.cpu.gpr.rsp + 32#64) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have e1 : (lifC X.cpu.gpr V).rsp = X.cpu.gpr.rsp + 24#64 := rfl
  have e2 : X.cpu.gpr.rsp + 24#64 + 8 = X.cpu.gpr.rsp + 32#64 := by bv_omega
  have n1 : (X.cpu.gpr.rsp + 24#64).toNat = X.cpu.gpr.rsp.toNat + 24 := by bv_omega
  refine (c_83 prof).run c hin _ hK hA hrip (vc_83 fun i hi => hl i (by omega)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_jmp_x hK₁ hA₁ hin (lt_len (by omega)) hr₁ (jmp_88 _) hci (tgt := 0) (by rw [Cti.cti_length]; omega)
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp + 24#64 := by rw [hg₂, hg₁, e1]
  refine Cti.cti_ok c hfs hci hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hlp hct ha hb hc f1 f2 f3 fw hfb hcn hap
    (fun i hi => ?_) (by rw [hsp₂, n1]; omega) (by rw [hsp₂, n1]; omega) hin₂ h₂ (by rw [hsp₂]; exact hra) ?_
  · rw [hsp₂]
    have := hl (24 + i) (by omega)
    rwa [show Addr.add X.cpu.gpr.rsp (24 + i) = Addr.add (X.cpu.gpr.rsp + 24#64) i by
      simp only [Addr.add]; bv_omega] at this
  rintro Z t' hKZ hAZ hrZ hgZ
  rw [hsp₂, e2, hg₂, hg₁] at hgZ
  exact k Z t' hKZ hAZ hrZ hgZ

end FV7z.Lif
