import FV7z.Pti.Cuts
import FV7z.Tgv.Holds
/-!
# `__pthread_tunables_init` (PLAN.md G3, startup)

glibc 2.31's `__pthread_tunables_init` at `0x5ffbc0` in `7zzs` (`nptl/pthread_mutex_conf.c`), called by
`__pthread_initialize_minimal_internal`: `__tunable_get_val (23, &v, callback)` for `glibc.pthread.mutex_spin_count`
(the 24th entry of `tunable_list`, at `0x791b68`), with `v` 4 bytes of the frame, between the stack guard's copy and
its check. With the tunable not set (`Tgv.tgv32_ok`), the callback (`0x5ffbb0`) does not run.

- `call_41`, `ret_66`: the instructions outside the blocks; `vc_0`, `vc_46`: the verification conditions.
- `pti_ok`: called with the tunable's type code 0 and its `initialized` byte 0, 32 bytes below the stack pointer in
  what the run may store into and above the tunables, the stack guard at `fs:0x28` apart from them, the run reaches
  the return address, the registers a call keeps as at the entry (`Osv.Back`), the bytes outside the 32 as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Pti

/-- The call of `__tunable_get_val`. -/
def pcall : List Byte := [0xe8, 0xb2, 0xf7, 0x06, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 456626] 5) := by dec_rfl
theorem w_41 : pcall <+: pti.drop 41 := by decide +kernel
theorem call_41 (feat : Features) : Dec feat pti 41 (FV7z.mk .call 64 [.rel 456626] 5) :=
  Dec.shift (j := 41) (k := 0) (pcall_0 feat) w_41 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_66 : pret <+: pti.drop 66 := by decide +kernel
theorem ret_66 (feat : Features) : Dec feat pti 66 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 66) (k := 0) (pret_0 feat) w_66 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the call: the stack guard's copy, the arguments `(23, &v, callback)`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 24#64 + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 41 ∧
      g' = { g with rsp := g.rsp - 24#64, rdx := 6290352#64, rdi := 23, rax := 0, rsi := g.rsp - 24#64 + 4#64 } ∧
      V' = Vst V (g.rsp - 24#64 + 8#64) (toBytesLE rdq(V, fb + 40#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst
  wpx [W_0, o0, Op.ldf, BitVec.xor_self]
  exact ⟨hfl, hst, rfl⟩

/-- The check of the stack guard, to the `ret`. -/
theorem vc_46 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) :
    W_46 fb F Wl (fun j' g' _ V' => j' = 66 ∧ g' = { g with rax := 0, rsp := g.rsp + 24#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc
  wpx [W_46, W_62, o1, o2, Op.xormf, hc, BitVec.xor_self]
  exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

theorem e8 : Tgv.ent 23 + 8#64 = 7936880#64 := by decide
theorem e32 : Tgv.ent 23 + 32#64 = 7936904#64 := by decide
theorem e40 : Tgv.ent 23 + 40#64 = 7936912#64 := by decide

/-- `__pthread_tunables_init ()` with `glibc.pthread.mutex_spin_count` not set: the run reaches the return address,
the bytes outside its 32 as they were. -/
theorem pti_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pti_at pti)
    (hinT : CodeIn L Tgv.tgv_at Tgv.tgv) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pti_at) (hsp : 32 < X.cpu.gpr.rsp.toNat)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hhi : 7936928 ≤ X.cpu.gpr.rsp.toNat - 32)
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (hty : ∀ i < 4, Foot F.data (Addr.add 7936880#64 i)) (hva : ∀ i < 8, Foot F.data (Addr.add 7936904#64 i))
    (hin0 : ∀ i < 1, Foot F.data (Addr.add 7936912#64 i))
    (ht0 : rdd(V, 7936880#64) = 0) (hz : rdb(V, 7936912#64) = 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → Osv.Back X.cpu.gpr g' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to the call
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hfl (off_ft hst 16 (by bv_omega) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₁]
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_41 _) hinT (Tgv.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact off_ft hst 0 (by bv_omega) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, show X.cpu.gpr.rsp - 24#64 - 8 = X.cpu.gpr.rsp - 32#64 from by bv_omega] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by rw [hg₂]; rfl
  have hsi₂ : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 + 4#64 := by rw [hg₂, hg₁]; rfl
  obtain ⟨V₂, hA₂, h2o, h2c, h2r⟩ : ∃ V₂, Agree F Y₂.proc.mm.mem V₂ ∧
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₂ a = V a) ∧
      rdq(V₂, X.cpu.gpr.rsp - 24#64 + 8#64) = rdq(V, fb + 40#64) ∧
      rdq(V₂, X.cpu.gpr.rsp - 32#64) = pti_at.add 46 := by
    refine ⟨_, hA₂, fun a ha => ?_, ?_, ?_⟩
    · repeat pv
    · pv
      rw [vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  -- `__tunable_get_val (23, &v, callback)`
  refine Tgv.tgv32_ok (d := 23) c hinT hK₂ hA₂ hr₂ (by rw [hg₂, hg₁]; rfl) (by rw [e8]; exact hty)
    (by rw [e32]; exact hva) (by rw [e40]; exact hin0) ?_ ?_ (fun i hi => ?_) (by rw [hsi₂]; bv_omega)
    (by rw [e40, hsi₂]; bv_omega) (fun i hi => ?_) hin (j₂ := 46) (lt_len (by decide)) (by rw [hsp₂]; exact h2r)
    (by rw [hsp₂]; bv_omega) (by rw [hsp₂, hsi₂]; bv_omega) ?_
  · rw [e8, ← ht0]
    exact congrArg (ofBytesLE 32) (rd_out h2o (by decide) (by bv_omega))
  · rw [e40, ← hz]
    exact congrArg (ofBytesLE 8) (rd_out h2o (by decide) (by bv_omega))
  · rw [hsi₂]
    exact off_ft hst 12 (by bv_omega) (by decide) i hi
  · rw [hsp₂]
    exact c.hws _ (off_ft hst 0 (by bv_omega) (by decide) i hi)
  intro g₃ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hbk₃
  rw [hsi₂] at hA₃
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by
    rw [hg₃, hbk₃.1, hsp₂]
    bv_omega
  obtain ⟨V₃, hA₃, h3o, h3c⟩ : ∃ V₃, Agree F Y₃.proc.mm.mem V₃ ∧
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₃ a = V a) ∧
      rdq(V₃, X.cpu.gpr.rsp - 24#64 + 8#64) = rdq(V, fb + 40#64) := by
    refine ⟨_, hA₃, fun a ha => ?_, ?_⟩
    · pv
      exact h2o a ha
    · pv
      exact h2c
  -- the stack guard's check, the `ret`
  refine (c_46 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ (vc_46 (fun i hi => ?_) hfl ?_) ?_
  · rw [hsp₃]
    exact c.hws _ (off_ft hst 16 (by bv_omega) (by decide) i hi)
  · rw [hsp₃, h3c]
    exact (congrArg (ofBytesLE 64) (rd_out h3o hfb hfd)).symm
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₄]
    show Y₃.cpu.gpr.rsp + 24#64 = _
    rw [hsp₃]
    bv_omega
  refine c.s_ret hK₄ hA₄ hin (lt_len (by decide)) hr₄ (ret_66 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₄]
    exact hl i hi
  · rw [hsp₄, ← hra]
    exact congrArg (ofBytesLE 64) (rd_out h3o hs8 (by omega))
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have b2 : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have b4 : Y₄.cpu.gpr.rbx = g₃.rbx ∧ Y₄.cpu.gpr.rbp = g₃.rbp ∧ Y₄.cpu.gpr.r12 = g₃.r12 ∧
      Y₄.cpu.gpr.r13 = g₃.r13 ∧ Y₄.cpu.gpr.r14 = g₃.r14 ∧ Y₄.cpu.gpr.r15 = g₃.r15 := by
    rw [hg₄, hg₃]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, k1, k2, k3, k4, k5, k6⟩ := hbk₃
  refine k V₄ _ Z t' hKZ hAZ h3o hrZ hgZ
    ⟨?_, b4.1.trans (k1.trans b2.1), b4.2.1.trans (k2.trans b2.2.1), b4.2.2.1.trans (k3.trans b2.2.2.1),
      b4.2.2.2.1.trans (k4.trans b2.2.2.2.1), b4.2.2.2.2.1.trans (k5.trans b2.2.2.2.2.1),
      b4.2.2.2.2.2.trans (k6.trans b2.2.2.2.2.2)⟩
  show Y₄.cpu.gpr.rsp + 8 = _
  rw [hsp₄]
  rfl

end FV7z.Pti
