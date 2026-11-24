import FV7z.Mxi.Cuts
import FV7z.Mxs.Cuts
import FV7z.Ssj.Holds
/-!
# `CriticalSection_Init` and `pthread_mutex_init (m, NULL)` (PLAN.md G3, constructors)

7-Zip's `CriticalSection_Init` at `0x448b40` (`C/Threads.c`) with its mutex `m` not null: `rsi := 0`, then a jump to
glibc 2.31's `__pthread_mutex_init` at `0x5fbb20` (`nptl/pthread_mutex_init.c`) with no attributes. That one pushes
`r13`, `r12`, `rbp`, `rbx`, keeps the stack guard's copy, clears the 40 bytes of the mutex (two `movups` of `xmm0`,
whatever bytes the model gives them, then the word at 32 and the kind at 16 stored 0), checks the copy and returns 0.

- `jmp_11`, `ret_170`: the instructions outside the blocks; `vc_s`, `vc_0`: the verification conditions.
- `mxV`: the bytes at the `ret`; `MxF`, `mx_rd`: what they keep.
- `mx_ok`: called with `m` not null, the run reaches the return address, the registers a call keeps as at the entry
  (`Osv.Back`), the bytes outside the 56 below the stack pointer and the 40 of the mutex as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Mxi

/-! ## The instructions outside the blocks -/

/-- `CriticalSection_Init`'s jump to `__pthread_mutex_init`. -/
def qjm : List Byte := [0xe9, 0xd0, 0x2f, 0x1b, 0x00]
theorem qjm_0 : ∀ feat, Dec feat qjm 0 (FV7z.mk .jmp 64 [.rel 1781712] 5) := by dec_rfl
theorem wx_11 : qjm <+: Mxs.mxs.drop 11 := by decide +kernel
theorem jmp_11 (feat : Features) : Dec feat Mxs.mxs 11 (FV7z.mk .jmp 64 [.rel 1781712] 5) :=
  Dec.shift (j := 11) (k := 0) (qjm_0 feat) wx_11 (Nat.zero_le _)

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wx_170 : qret <+: mxi.drop 170 := by decide +kernel
theorem ret_170 (feat : Features) : Dec feat mxi 170 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 170) (k := 0) (qret_0 feat) wx_170 (Nat.zero_le _)

/-! ## The bytes -/

/-- The stack pointer after the prologue, from `S` at the entry. -/
abbrev sp1 (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 24#64

/-- The bytes after the four pushes under `S`. -/
abbrev mx4 (V : Addr → Byte) (S : Addr) (r13 r12 rbp rbx : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (S - 8) (toBytesLE r13 8)) (S - 8 - 8) (toBytesLE r12 8)) (S - 8 - 8 - 8) (toBytesLE rbp 8))
    (S - 8 - 8 - 8 - 8) (toBytesLE rbx 8)

/-- The bytes at the `ret`: the pushes, the stack guard's copy, the mutex `m` cleared (`b1`, `b2`: the bytes of
`xmm0` as the model stores them). -/
abbrev mxV (V : Addr → Byte) (S m fb : Addr) (r13 r12 rbp rbx : BitVec 64) (b1 b2 : List Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (mx4 V S r13 r12 rbp rbx) (sp1 S + 8#64)
    (toBytesLE rdq(mx4 V S r13 r12 rbp rbx, fb + 40#64) 8)) (m + 32#64) (toBytesLE (0#64) 8)) m b1) (m + 16#64) b2)
    (m + 16#64) (toBytesLE (0#32) 4)

/-- The registers at the `ret`. -/
abbrev g170 (g : Gprs) (S : Addr) (V' : Addr → Byte) (c : BitVec 64) : Gprs :=
  { g with rax := 0, rcx := c, rsi := 0, rsp := sp1 S + 24#64 + 8 + 8 + 8 + 8, rbx := rdq(V', sp1 S + 24#64),
           rbp := rdq(V', sp1 S + 24#64 + 8), r12 := rdq(V', sp1 S + 24#64 + 8 + 8),
           r13 := rdq(V', sp1 S + 24#64 + 8 + 8 + 8) }

/-- A `jne` after `xor` taken: the two words differ. -/
theorem xne {x y : BitVec 64} (h : (!(x ^^^ y == 0)) = true) : x ≠ y := by
  intro hxy
  subst hxy
  simp at h

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- `CriticalSection_Init` with `m` not null: to its jump, `rsi := 0`. -/
theorem vc_s {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi ≠ 0) (Q : Post)
    (hQ : ∀ f', Q 11 { g with rsi := 0 } f' V) : Mxs.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi
  wpx [Mxs.W_0, Mxs.W_9, Mxs.o0, Mxs.o1, BitVec.and_self, BitVec.xor_self]
  intro _
  refine ⟨fun h => absurd ?_ hdi, fun _ _ => hQ _⟩
  simpa using h

/-- `__pthread_mutex_init (m, NULL)` from its entry, the stack pointer `S`: to the `ret` with the bytes `mxV`, or to
the stack guard's failure with the copy not the guard. -/
theorem vc_0 {fb S m : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hS : g.rsp = S) (hM : g.rdi = m)
    (hsi : g.rsi = 0)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (h4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcw : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 8#64) i))
    (hcr : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 8#64) i))
    (hm32 : ∀ i < 8, Foot Wl (Addr.add (m + 32#64) i)) (hm0 : ∀ i < 16, Foot Wl (Addr.add m i))
    (hm16 : ∀ i < 16, Foot Wl (Addr.add (m + 16#64) i))
    (hp0 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 24#64) i))
    (hp1 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8) i))
    (hp2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8) i))
    (hp3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8) i)) (Q : Post)
    (hQ : ∀ (b1 b2 : List Byte) (c : BitVec 64) (f' : Rflags), b1.length = 16 → b2.length = 16 →
      Q 170 (g170 g S (mxV V S m fb g.r13 g.r12 g.rbp g.rbx b1 b2) c) f' (mxV V S m fb g.r13 g.r12 g.rbp g.rbx b1 b2))
    (hX : ∀ (b1 b2 : List Byte) (g' : Gprs) (f' : Rflags), b1.length = 16 → b2.length = 16 →
      (!(rdq(mxV V S m fb g.r13 g.r12 g.rbp g.rbx b1 b2, sp1 S + 8#64) ^^^
        rdq(mxV V S m fb g.r13 g.r12 g.rbp g.rbx b1 b2, fb + 40#64) == 0)) = true →
      Q 472 g' f' (mxV V S m fb g.r13 g.r12 g.rbp g.rbx b1 b2)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hS hM hsi
  subst hS hM hsi
  wpx [W_0, W_240, W_134, W_140, W_160, o0, o1, o2, o3, o4, Op.ldf, Op.xormf, Op.vs, BitVec.xor_self]
  refine ⟨h1, h2, h3, h4, hfl, hcw, fun _ _ => ⟨fun _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), hm32, fun _ =>
    ⟨hm0, fun b1 hb1 => ⟨hm16, fun b2 hb2 => ⟨fun i hi => hm16 i (by omega), fun _ => ⟨hcr, hfl, fun _ =>
      ⟨fun h => hX _ _ _ _ hb1 hb2 h, fun _ => ⟨hp0, hp1, hp2, hp3, hQ _ _ _ _ hb1 hb2⟩⟩⟩⟩⟩⟩⟩,
    fun h => absurd h (by decide)⟩⟩

/-! ## The frame -/

theorem k24 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 = S - 8 - 8 - 8 - 8 := by bv_omega
theorem k32 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 = S - 8 - 8 - 8 := by bv_omega
theorem k40 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 = S - 8 - 8 := by bv_omega
theorem k48 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 = S - 8 := by bv_omega
theorem k56 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 + 8 = S := by bv_omega

theorem f8 (S : Addr) : S - 8 = S - 56#64 + BitVec.ofNat 64 48 := by bv_omega
theorem f16 (S : Addr) : S - 8 - 8 = S - 56#64 + BitVec.ofNat 64 40 := by bv_omega
theorem f24 (S : Addr) : S - 8 - 8 - 8 = S - 56#64 + BitVec.ofNat 64 32 := by bv_omega
theorem f32 (S : Addr) : S - 8 - 8 - 8 - 8 = S - 56#64 + BitVec.ofNat 64 24 := by bv_omega
theorem fc (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 8#64 = S - 56#64 + BitVec.ofNat 64 8 := by bv_omega
theorem fp0 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 = S - 56#64 + BitVec.ofNat 64 24 := by bv_omega
theorem fp1 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 = S - 56#64 + BitVec.ofNat 64 32 := by bv_omega
theorem fp2 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 = S - 56#64 + BitVec.ofNat 64 40 := by
  bv_omega
theorem fp3 (S : Addr) : S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 = S - 56#64 + BitVec.ofNat 64 48 := by
  bv_omega

/-- What the bytes `V'` at the `ret` keep of the bytes `V` at the entry: all outside the 56 under `S` and the 40 of
the mutex `m`; the stack guard's copy, the four saved registers, the return address. -/
structure MxF (V V' : Addr → Byte) (S m fb : Addr) (r13 r12 rbp rbx : BitVec 64) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 56 ≤ a.toNat ∧ a.toNat < S.toNat) →
    ¬ (m.toNat ≤ a.toNat ∧ a.toNat < m.toNat + 40) → V' a = V a
  can : rdq(V', sp1 S + 8#64) = rdq(V', fb + 40#64)
  bx : rdq(V', sp1 S + 24#64) = rbx
  bp : rdq(V', sp1 S + 24#64 + 8) = rbp
  x12 : rdq(V', sp1 S + 24#64 + 8 + 8) = r12
  x13 : rdq(V', sp1 S + 24#64 + 8 + 8 + 8) = r13
  ra : rdq(V', S) = rdq(V, S)

/-- The bytes at the `ret` are as `MxF` says: the mutex apart from the frame and the return address, the stack
guard apart from both. -/
theorem mx_rd (V : Addr → Byte) (S m fb : Addr) (r13 r12 rbp rbx : BitVec 64) {b1 b2 : List Byte}
    (hb1 : b1.length = 16) (hb2 : b2.length = 16) (hs : 56 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hm : m.toNat + 40 ≤ 2 ^ 64) (hmd : m.toNat + 40 ≤ S.toNat - 56 ∨ S.toNat + 8 ≤ m.toNat)
    (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ S.toNat - 56 ∨ S.toNat ≤ (fb + 40#64).toNat)
    (hfm : (fb + 40#64).toNat + 8 ≤ m.toNat ∨ m.toNat + 40 ≤ (fb + 40#64).toNat) :
    MxF V (mxV V S m fb r13 r12 rbp rbx b1 b2) S m fb r13 r12 rbp rbx := by
  have e1 : rdq(mxV V S m fb r13 r12 rbp rbx b1 b2, sp1 S + 8#64) = rdq(V, fb + 40#64) := by
    unfold mxV mx4 sp1
    repeat pv
    rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]
    repeat pv
  have e2 : rdq(mxV V S m fb r13 r12 rbp rbx b1 b2, fb + 40#64) = rdq(V, fb + 40#64) := by
    unfold mxV mx4 sp1
    repeat pv
  refine ⟨fun a ha hb => ?_, e1.trans e2.symm, ?_, ?_, ?_, ?_, ?_⟩
  · unfold mxV mx4 sp1
    repeat pv
  · unfold mxV mx4 sp1
    rw [k24]
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · unfold mxV mx4 sp1
    rw [k32]
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · unfold mxV mx4 sp1
    rw [k40]
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · unfold mxV mx4 sp1
    rw [k48]
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · unfold mxV mx4 sp1
    repeat pv

/-! ## The call -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}


/-- `Osv.Back` from the registers with `rsi := 0`. -/
theorem back_rsi {g g' : Gprs} (h : Osv.Back { g with rsi := 0 } g') : Osv.Back g g' := h

/-- `__pthread_mutex_init (m, NULL)` from its entry with the stack pointer `S` at the return address: the run reaches
the return address, the registers a call keeps as at the entry, the bytes outside the 56 under `S` and the 40 of the
mutex as they were. -/
theorem mxi_ok {fb S m : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hini : CodeIn L mxi_at mxi) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mxi_at.add 0) (hS : X.cpu.gpr.rsp = S) (hM : X.cpu.gpr.rdi = m) (hsi : X.cpu.gpr.rsi = 0)
    (hs : 56 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 56, Foot Wl (Addr.add (S - 56#64) i)) (hlr : ∀ i < 8, Foot F.data (Addr.add S i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ S.toNat - 56 ∨ S.toNat ≤ (fb + 40#64).toNat)
    (hfm : (fb + 40#64).toNat + 8 ≤ m.toNat ∨ m.toNat + 40 ≤ (fb + 40#64).toNat)
    (hmw : ∀ i < 40, Foot Wl (Addr.add m i)) (hm : m.toNat + 40 ≤ 2 ^ 64)
    (hmd : m.toNat + 40 ≤ S.toNat - 56 ∨ S.toNat + 8 ≤ m.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (S.toNat - 56 ≤ a.toNat ∧ a.toNat < S.toNat) → ¬ (m.toNat ≤ a.toNat ∧ a.toNat < m.toNat + 40) →
        V' a = V a) →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hini _ hK hA hrip
    (vc_0 (S := S) (m := m) hS hM hsi
      (off_ft hst 48 (f8 _) (by decide)) (off_ft hst 40 (f16 _) (by decide)) (off_ft hst 32 (f24 _) (by decide))
      (off_ft hst 24 (f32 _) (by decide)) hfl (off_ft hst 8 (fc _) (by decide))
      (fun i hi => c.hws _ (off_ft hst 8 (fc _) (by decide) i hi)) (off_ft hmw 32 rfl (by decide))
      (fun i hi => hmw i (by omega)) (off_ft hmw 16 rfl (by decide))
      (fun i hi => c.hws _ (off_ft hst 24 (fp0 _) (by decide) i hi))
      (fun i hi => c.hws _ (off_ft hst 32 (fp1 _) (by decide) i hi))
      (fun i hi => c.hws _ (off_ft hst 40 (fp2 _) (by decide) i hi))
      (fun i hi => c.hws _ (off_ft hst 48 (fp3 _) (by decide) i hi))
      (fun j' g' _ V' => ∃ b1 b2 : List Byte, b1.length = 16 ∧ b2.length = 16 ∧
        V' = mxV V S m fb X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx b1 b2 ∧
        ((j' = 170 ∧ ∃ c, g' = g170 X.cpu.gpr S V' c) ∨
          (j' = 472 ∧ (!(rdq(V', sp1 S + 8#64) ^^^ rdq(V', fb + 40#64) == 0)) = true)))
      (fun b1 b2 c _ h1 h2 => ⟨b1, b2, h1, h2, rfl, .inl ⟨rfl, c, rfl⟩⟩)
      (fun b1 b2 _ _ h1 h2 h => ⟨b1, b2, h1, h2, rfl, .inr ⟨rfl, h⟩⟩)) ?_
  rintro j' g' fl V₃ ⟨b1, b2, hb1, hb2, rfl, h⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hF := mx_rd V S m fb X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx hb1 hb2 hs hs8 hm hmd hfb hfd hfm
  rcases h with ⟨rfl, cc, rfl⟩ | ⟨rfl, hc⟩
  rotate_left
  · exact absurd hF.can (xne hc)
  -- the `ret`
  have hsp₃ : Y₃.cpu.gpr.rsp = S := (congrArg Gprs.rsp hg₃).trans (k56 _)
  refine c.s_ret hK₃ hA₃ hini (lt_len (by decide)) hr₃ (ret_170 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₃]
    exact hlr i hi
  · rw [hsp₃, hF.ra]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hF.out hrZ ?_
  rw [hgZ]
  refine ⟨?_, (congrArg Gprs.rbx hg₃).trans hF.bx, (congrArg Gprs.rbp hg₃).trans hF.bp,
    (congrArg Gprs.r12 hg₃).trans hF.x12, (congrArg Gprs.r13 hg₃).trans hF.x13, (congrArg Gprs.r14 hg₃).trans rfl,
    (congrArg Gprs.r15 hg₃).trans rfl⟩
  show Y₃.cpu.gpr.rsp + 8 = _
  rw [hsp₃, hS]
  rfl

/-- `CriticalSection_Init (m)` with `m` not null, from its entry with the stack pointer `S` at the return address:
as `mxi_ok`. -/
theorem mx_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L Mxs.mxs_at Mxs.mxs) (hini : CodeIn L mxi_at mxi) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = Mxs.mxs_at) (hm0 : X.cpu.gpr.rdi ≠ 0)
    (hs : 56 ≤ X.cpu.gpr.rsp.toNat) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 56, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56#64) i))
    (hlr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 56 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (hfm : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 40 ≤ (fb + 40#64).toNat)
    (hmw : ∀ i < 40, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hm : X.cpu.gpr.rdi.toNat + 40 ≤ 2 ^ 64)
    (hmd : X.cpu.gpr.rdi.toNat + 40 ≤ X.cpu.gpr.rsp.toNat - 56 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + 40) → V' a = V a) →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- `CriticalSection_Init`: `rsi := 0`, the jump
  refine (Mxs.c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_s hm0 (fun j' g' _ V' => j' = 11 ∧ g' = { X.cpu.gpr with rsi := 0 } ∧ V' = V) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hV] at hA₁
  refine c.s_jmp_x hK₁ hA₁ hin (Mxs.lt_len (by decide)) hr₁ (jmp_11 _) hini (lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hg : Y₂.cpu.gpr = { X.cpu.gpr with rsi := 0 } := hg₂.trans hg₁
  -- `__pthread_mutex_init`
  refine mxi_ok c hfs hini hK₂ hA₂ hr₂ (congrArg Gprs.rsp hg) (congrArg Gprs.rdi hg) (congrArg Gprs.rsi hg) hs hs8
    hst hlr hfl hfb hfd hfm hmw hm hmd hin₂ h₂ hra ?_
  intro V' Z t' hKZ hAZ hout hrZ hB
  rw [hg] at hB
  exact k V' Z t' hKZ hAZ hout hrZ (back_rsi hB)
