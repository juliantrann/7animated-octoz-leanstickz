import FV7z.Fdm.Cuts
import FV7z.Rfi.Holds
import FV7z.Rtc.Holds
/-!
# `frame_dummy` (PLAN.md G3, startup)

libgcc's `frame_dummy` at `0x41d440` in `7zzs` (`libgcc/crtstuff.c`, in `crtbegin.o`), the first entry of
`.init_array`: `__register_frame_info` is there (`0x6127e0`, not null), so
`__register_frame_info (__EH_FRAME_BEGIN__, &object)` (`0x70bb60`, `0x794620`) is called, and the function ends in
`register_tm_clones ()` (`0x41d3c0`), a tail call, which returns at once, its table being empty.

- `call_28`, `jmp_34`: the instructions outside the blocks; `vc_0`, `vc_33`, `vc_r`: the verification conditions
  (`vc_r`: `register_tm_clones`' own, with the memory as it was).
- `Env`: what the four codes, the 72 bytes of stack, the object, the mutex and the words need.
- `fdm_ok`: with the first word at `__EH_FRAME_BEGIN__` not 0, nothing registered yet, the mutex free and of the
  plain kind, no elision: the run reaches the return address, the registers a call keeps as at the entry, the object
  at the head of `unseen_objects` (`Rfi.Dat`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Fdm

/-! ## The instructions outside the blocks -/

def pc0 : List Byte := [0xe8, 0x7f, 0x53, 0x1f, 0x00]
theorem pc0_0 : ∀ feat, Dec feat pc0 0 (FV7z.mk .call 64 [.rel 2052991] 5) := by dec_rfl
theorem w_28 : pc0 <+: fdm.drop 28 := by decide +kernel
/-- `call __register_frame_info`. -/
theorem call_28 (feat : Features) : Dec feat fdm 28 (FV7z.mk .call 64 [.rel 2052991] 5) :=
  Dec.shift (j := 28) (k := 0) (pc0_0 feat) w_28 (Nat.zero_le _)

def pj0 : List Byte := [0xe9, 0x59, 0xff, 0xff, 0xff]
theorem pj0_0 : ∀ feat, Dec feat pj0 0 (FV7z.mk .jmp 64 [.rel 18446744073709551449] 5) := by dec_rfl
theorem w_34 : pj0 <+: fdm.drop 34 := by decide +kernel
/-- `jmp register_tm_clones`. -/
theorem jmp_34 (feat : Features) : Dec feat fdm 34 (FV7z.mk .jmp 64 [.rel 18446744073709551449] 5) :=
  Dec.shift (j := 34) (k := 0) (pj0_0 feat) w_34 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the call: `rbp` pushed, the two arguments. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 28 ∧
      g' = { g with rax := 6367200#64, rsp := g.rsp - 8, rbp := g.rsp - 8, rsi := 7947808#64, rdi := 7388000#64 } ∧
      V' = Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1
  wpx [W_0, W_14, o0, o1, BitVec.and_self]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨h1, rfl⟩⟩

/-- `pop rbp`. -/
theorem vc_33 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_33 F Wl (fun j' g' _ V' => j' = 34 ∧ g' = { g with rsp := g.rsp + 8, rbp := rdq(V, g.rsp) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1
  wpx [W_33, o2]
  exact h1

/-- `register_tm_clones` up to its `ret`: the table is empty, so the first `je` is taken. -/
theorem vc_r {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    Rtc.W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Rtc.W_0, Rtc.W_31, Rtc.W_41, Rtc.o0, Rtc.o1, Rtc.o2, Op.shr64, Op.sar64]
  intro _ _ _ _ fl hz
  have hz' : fl.zf = true := by rw [hz (by decide)]; decide
  exact ⟨fun _ => trivial, fun h => absurd hz' (by rw [h]; decide)⟩

/-! ## The whole -/

/-- What the run needs: the four codes at their places, the stack's 72 bytes below `S` (the saved `rbp`, the return
address of the call, `__register_frame_info`'s 56) above the data and apart from the thread's block, the return
address at `S`, the object (`0x794620`), the first word at `__EH_FRAME_BEGIN__` (`0x70bb60`), `object_mutex`,
`any_objects_registered`, `unseen_objects`, the thread's `tid`, `__pthread_force_elision`. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb S : Addr) : Prop where
  code : CodeIn L fdm_at fdm
  tcode : CodeIn L Rtc.rtc_at Rtc.rtc
  rcode : CodeIn L Rfi.rfi_at Rfi.rfi
  lcode : CodeIn L Pml.pml_at Pml.pml
  ucode : CodeIn L Pmu.pmu_at Pmu.pmu
  s0 : 8008672 + 72 ≤ S.toNat
  s8 : S.toNat + 8 ≤ 2 ^ 64
  f0 : 8008672 ≤ fb.toNat
  f1 : fb.toNat + 724 ≤ S.toNat - 72
  st : ∀ i < 72, Foot Wl (Addr.add (S - 72#64) i)
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  ob : ∀ i < 48, Foot Wl (Addr.add (7947808#64) i)
  bg : ∀ i < 4, Foot F.data (Addr.add (7388000#64) i)
  mu : ∀ i < 20, Foot Wl (Addr.add (8008608#64) i)
  any : ∀ i < 4, Foot Wl (Addr.add (8008648#64) i)
  uns : ∀ i < 8, Foot Wl (Addr.add (8008664#64) i)
  tid : ∀ i < 4, Foot F.data (Addr.add (fb + 720#64) i)
  fe : ∀ i < 4, Foot F.data (Addr.add (7991628#64) i)

variable {V : Addr → Byte} {S x : Addr} {n : Nat} {rp ra : BitVec 64}

/-- Bytes of the data, at the call: apart from the two words pushed. -/
theorem c_rd (hx : x.toNat + n ≤ 8008672) (hs0 : 8008672 + 72 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) :
    List.map (Vst (Vst V (S - 8#64) (toBytesLE rp 8)) (S - 16#64) (toBytesLE ra 8)) (byteAddrs x n) =
      List.map V (byteAddrs x n) := by
  repeat pv

/-- After `__register_frame_info`: the saved `rbp` and the return address are where they were, and what the
function did, said of the memory at the entry of `frame_dummy`. -/
theorem post {ob bg : Addr} {Vr : Addr → Byte}
    (hD : Rfi.Dat ((S - 16#64).toNat - 56) (S - 16#64).toNat ob bg
      (Vst (Vst V (S - 8#64) (toBytesLE rp 8)) (S - 16#64) (toBytesLE ra 8)) Vr)
    (hs0 : 8008672 + 72 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) (ho : ob.toNat + 48 ≤ 7991628) :
    rdq(Vr, S - 8#64) = rp ∧ rdq(Vr, S) = rdq(V, S) ∧ Rfi.Dat (S.toNat - 72) S.toNat ob bg V Vr := by
  have hw : Rfi.Dat (S.toNat - 72) S.toNat ob bg V Vr := hD.wide (fun a ha => by
    rw [vo (by ln) (by bv_omega) (by bv_omega), vo (by ln) (by bv_omega) (by bv_omega)]) (by bv_omega)
    (by bv_omega) (by omega)
  refine ⟨?_, ?_, hw⟩
  · refine (congrArg (ofBytesLE 64) (Rfi.rd_of (by bv_omega) fun a h1 h2 =>
      hD.out a (by bv_omega) (by unfold Rfi.Wr; bv_omega))).trans ?_
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · exact congrArg (ofBytesLE 64) (Rfi.rd_of hs8 fun a h1 h2 => hw.out a (by omega) (by unfold Rfi.Wr; omega))

theorem b8 (S : Addr) : S - 8 = S - 72#64 + BitVec.ofNat 64 64 := by bv_omega
theorem b8' (S : Addr) : S - 8#64 = S - 72#64 + BitVec.ofNat 64 64 := by bv_omega
theorem b16 (S : Addr) : S - 8#64 - 8 = S - 16#64 := by bv_omega
theorem b16' (S : Addr) : S - 16#64 = S - 72#64 + BitVec.ofNat 64 56 := by bv_omega
theorem b72 (S : Addr) : S - 16#64 - 56#64 = S - 72#64 + BitVec.ofNat 64 0 := by bv_omega
theorem u8 (S : Addr) : S - 16#64 + 8#64 = S - 8#64 := by bv_omega
theorem u0 (S : Addr) : S - 8#64 + 8 = S := by bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `frame_dummy ()`, the first registration, the mutex free and of the plain kind, no elision: the run reaches the
return address, the registers a call keeps as at the entry, the object at the head of `unseen_objects`
(`Rfi.Dat`, with `frame_dummy`'s 72 bytes of stack). -/
theorem fdm_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hE : Env F Wl L fb X.cpu.gpr.rsp) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = fdm_at) (hb : rdd(V, 7388000#64) ≠ 0)
    (hkd : rdd(V, 8008608#64 + 16#64) = 0) (hfe : rdd(V, 7991628#64) = 0) (hlk : rdd(V, 8008608#64) = 0)
    (how : rdd(V, 8008608#64 + 8#64) = 0) (hany : rdd(V, 8008648#64) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Rfi.Dat (X.cpu.gpr.rsp.toNat - 72) X.cpu.gpr.rsp.toNat (7947808#64) (7388000#64) V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hf0 := hE.f0
  have hf1 := hE.f1
  -- `rbp` pushed, the arguments
  refine (c_0 prof).run c hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (off_ft hE.st 64 (b8 _) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [show X.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 from rfl] at hA₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hg₁]; rfl
  -- `__register_frame_info (__EH_FRAME_BEGIN__, &object)`
  refine c.s_call_x hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (call_28 _) hE.rcode (tgt := 176)
    (Rfi.lt_len (by decide)) (by decide) (fun i hi => ?_) ?_
  · rw [hsp₁, b16]
    exact off_ft hE.st 56 (b16' _) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, b16] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hg₂]; rfl
  have hsi₂ : Y₂.cpu.gpr.rsi = 7947808#64 := by rw [hg₂, hg₁]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = 7388000#64 := by rw [hg₂, hg₁]; rfl
  have hRE : Rfi.Env F Wl L fb (X.cpu.gpr.rsp - 16#64) (7947808#64) :=
    { code := hE.rcode, lcode := hE.lcode, ucode := hE.ucode, s0 := by bv_omega, s8 := by bv_omega,
      o0 := by decide, f0 := hf0, f1 := by bv_omega,
      st := off_ft hE.st 0 (b72 _) (by decide),
      lr := fun i hi => c.hws _ (off_ft hE.st 56 (b16' _) (by decide) i hi),
      ob := hE.ob, mu := hE.mu, any := hE.any, uns := hE.uns, tid := hE.tid, fe := hE.fe }
  refine Rfi.rfi_ok c hfs (by rw [hsp₂, hsi₂]; exact hRE) hK₂ hA₂ hr₂ (by rw [hdi₂]; decide)
    (by rw [hdi₂]; exact hE.bg) ?_ ?_ ?_ ?_ ?_ ?_ hE.code (j₂ := 33) (lt_len (by decide)) ?_ ?_
  · rw [hdi₂]
    exact fun h => hb ((congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).symm.trans h)
  · exact (congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).trans hkd
  · exact (congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).trans hfe
  · exact (congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).trans hlk
  · exact (congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).trans how
  · exact (congrArg (ofBytesLE 32) (c_rd (by decide) hs0 hs8)).trans hany
  · rw [hsp₂, vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro Vr Y₃ t₃ hK₃ hA₃ hD hr₃ hbk₃
  rw [hsp₂, hsi₂, hdi₂] at hD
  obtain ⟨hsp₃, hbx₃, hbp₃, h12₃, h13₃, h14₃, h15₃⟩ := hbk₃
  rw [hsp₂, u8] at hsp₃
  obtain ⟨p8, pS, hDw⟩ := post hD hs0 hs8 (by decide)
  -- `pop rbp`
  refine (c_33 prof).run c hE.code _ hK₃ hA₃ hr₃ (vc_33 (fun i hi => ?_)) ?_
  · rw [hsp₃]
    exact c.hws _ (off_ft hE.st 64 (b8' _) (by decide) i hi)
  rintro j' g fl V₄ ⟨rfl, rfl, hV⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst V₄
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₄]
    show Y₃.cpu.gpr.rsp + 8 = _
    rw [hsp₃]
    exact u0 _
  have hbp₄ : Y₄.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hg₄]
    show rdq(_, Y₃.cpu.gpr.rsp) = _
    rw [hsp₃]
    exact p8
  have sv₄ : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₄.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y₄.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₄.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₄]
    show Y₃.cpu.gpr.rbx = _ ∧ Y₃.cpu.gpr.r12 = _ ∧ Y₃.cpu.gpr.r13 = _ ∧ Y₃.cpu.gpr.r14 = _ ∧ Y₃.cpu.gpr.r15 = _
    rw [hbx₃, h12₃, h13₃, h14₃, h15₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- `register_tm_clones ()`, a tail call
  refine c.s_jmp_x hK₄ hA₄ hE.code (lt_len (by decide)) hr₄ (jmp_34 _) hE.tcode (tgt := 0)
    (Rtc.lt_len (by decide)) (by decide) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  refine (Rtc.c_0 prof).run c hE.tcode _ hK₅ hA₅ hr₅ vc_r ?_
  rintro j' g fl V₆ ⟨rfl, q1, q2, q3, q4, q5, q6, q7, hV⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  subst V₆
  rw [← hg₆, hg₅] at q1 q2 q3 q4 q5 q6 q7
  refine c.s_ret hK₆ hA₆ hE.tcode (Rtc.lt_len (by decide)) hr₆ (Rtc.ret_48 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [q1, hsp₄]
    exact hE.lr i hi
  · rw [q1, hsp₄]
    exact pS.trans hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hDw hrZ ?_
  rw [hgZ]
  refine ⟨?_, q2.trans sv₄.1, q3.trans hbp₄, q4.trans sv₄.2.1, q5.trans sv₄.2.2.1, q6.trans sv₄.2.2.2.1,
    q7.trans sv₄.2.2.2.2⟩
  show Y₆.cpu.gpr.rsp + 8 = _
  rw [q1, hsp₄]
  rfl

end FV7z.Fdm
