import FV7z.Lpi.Cuts
import FV7z.Raf.Holds
/-!
# `__libc_pthread_init` (PLAN.md G3, startup)

glibc 2.31's `__libc_pthread_init (ptr, reclaim)` at `0x62da30` in `7zzs`, as `__pthread_initialize_minimal_internal`
calls it: `ptr` goes to `__fork_generation_pointer` (`0x7a8410`), `__register_atfork (0, 0, reclaim, 0)` adds the
first fork handler (`Raf.raf_ok`), and the answer is the address of `__libc_multiple_threads` (`0x7a8418`).

- `call_24`, `ret_40`: the instructions outside the blocks; `vc_0`, `vc_29`: the verification conditions.
- `lpi_ok`: called with one thread (`fs:0x18` 0), the fork handlers' lock free and their list not set up, 56 bytes
  below the stack pointer, the 88 bytes of the lock and the list and the pointer's 8 bytes in what the run may store
  into, the stack and the thread's block above them, the run reaches the return address with `rax` `0x7a8418`, the
  pointer's bytes `rdi`, the registers a call keeps as at the entry (`Osv.Back`), the other bytes outside the 56 and
  the 88 as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft rd_out2)
namespace FV7z.Lpi

/-- The call of `__register_atfork`. -/
def pcall : List Byte := [0xe8, 0x13, 0x00, 0x00, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 19] 5) := by dec_rfl
theorem w_24 : pcall <+: lpi.drop 24 := by decide +kernel
theorem call_24 (feat : Features) : Dec feat lpi 24 (FV7z.mk .call 64 [.rel 19] 5) :=
  Dec.shift (j := 24) (k := 0) (pcall_0 feat) w_24 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_40 : pret <+: lpi.drop 40 := by decide +kernel
theorem ret_40 (feat : Features) : Dec feat lpi 40 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 40) (k := 0) (pret_0 feat) w_40 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the call: the pointer stored, the arguments `(0, 0, reclaim, 0)`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hpw : ∀ i < 8, Foot Wl (Addr.add 8029200#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧
      g' = { g with rsp := g.rsp - 8#64, rdx := g.rsi, rcx := 0, rsi := 0, rdi := 0 } ∧
      V' = Vst V 8029200#64 (toBytesLE g.rdi 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.sta, BitVec.xor_self]
  exact ⟨hpw, rfl⟩

/-- After the call: the answer, the frame given back. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_29 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = { g with rax := 8029208#64, rsp := g.rsp + 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_29, o1]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__libc_pthread_init (ptr, reclaim)` with one thread, the fork handlers' lock free and their list not set up:
the run reaches the return address with `rax` the address of `__libc_multiple_threads`, `ptr` stored. -/
theorem lpi_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lpi_at lpi)
    (hinr : CodeIn L Raf.raf_at Raf.raf) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lpi_at) (hsp : 56 < X.cpu.gpr.rsp.toNat)
    (hst : ∀ i < 56, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hpw : ∀ i < 8, Foot Wl (Addr.add 8029200#64 i)) (hbw : ∀ i < 88, Foot Wl (Addr.add 8011552#64 i))
    (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i))
    (hhi : 8029208 ≤ X.cpu.gpr.rsp.toNat - 56) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) (hfb : (fb + 24#64).toNat + 4 ≤ 2 ^ 64)
    (hfd : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 56 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 24#64).toNat)
    (hfh : 8029208 ≤ (fb + 24#64).toNat)
    (hmt : rdd(V, fb + 24#64) = 0) (hlock : rdd(V, 8011552#64) = 0) (hflag : rdb(V, 8011556#64) = 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) → V' a = V a) →
      rdq(V', 8029200#64) = X.cpu.gpr.rdi →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = 8029208#64 → Osv.Back X.cpu.gpr g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to the call
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hpw) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hg₁]
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_24 _) hinr (Raf.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact off_ft hst 40 (by bv_omega) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, show X.cpu.gpr.rsp - 8#64 - 8 = X.cpu.gpr.rsp - 16#64 from by bv_omega] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hg₂]; rfl
  obtain ⟨V₂, hA₂, h2o, h2r, h2s⟩ : ∃ V₂, Agree F Y₂.proc.mm.mem V₂ ∧
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 8) →
        ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) → V₂ a = V a) ∧
      rdq(V₂, X.cpu.gpr.rsp - 16#64) = lpi_at.add 29 ∧ rdq(V₂, 8029200#64) = X.cpu.gpr.rdi := by
    refine ⟨_, hA₂, fun a h1 h2 => ?_, ?_, ?_⟩
    · repeat pv
    · rw [vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · pv
      rw [vs (by ln) (by decide)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  -- `__register_atfork (0, 0, reclaim, 0)`
  refine Raf.raf_ok c hfs hinr hK₂ hA₂ hr₂ (by rw [hsp₂]; bv_omega) (fun i hi => ?_) (fun i hi => ?_) hin (j₂ := 29)
    (lt_len (by decide)) (by rw [hsp₂]; exact h2r) hbw hro (by rw [hsp₂]; bv_omega) (by rw [hsp₂]; bv_omega) hfl hfb
    (by rw [hsp₂]; bv_omega) (Or.inr (by omega)) ?_ ?_ ?_ ?_
  · rw [hsp₂]
    exact off_ft hst 0 (by bv_omega) (by decide) i hi
  · rw [hsp₂]
    exact c.hws _ (off_ft hst 40 (by bv_omega) (by decide) i hi)
  · rw [← hmt]
    exact congrArg (ofBytesLE 32) (rd_out2 h2o hfb (by omega) (Or.inr hfh))
  · rw [← hlock]
    exact congrArg (ofBytesLE 32) (rd_out2 h2o (by decide) (by bv_omega) (by decide))
  · rw [← hflag]
    exact congrArg (ofBytesLE 8) (rd_out2 h2o (by decide) (by bv_omega) (by decide))
  intro V₃ g₃ Y₃ t₃ hK₃ hA₃ h3o hr₃ hg₃ hax₃ hbk₃
  rw [hsp₂] at h3o
  -- to the `ret`
  refine (c_29 prof).run c hin _ hK₃ hA₃ hr₃ vc_29 ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₄]
    show Y₃.cpu.gpr.rsp + 8#64 = _
    rw [hg₃, hbk₃.1, hsp₂]
    bv_omega
  refine c.s_ret hK₄ hA₄ hin (lt_len (by decide)) hr₄ (ret_40 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₄]
    exact hl i hi
  · rw [hsp₄, ← hra]
    exact congrArg (ofBytesLE 64) ((rd_out2 h3o hs8 (by bv_omega) (by bv_omega)).trans
      (rd_out2 h2o hs8 (by bv_omega) (by bv_omega)))
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
  refine k V₄ _ Z t' hKZ hAZ (fun a h1 h2 h3 => (h3o a (by bv_omega) h2).trans (h2o a (by bv_omega) h3)) ?_ hrZ hgZ ?_
    ⟨?_, b4.1.trans (k1.trans b2.1), b4.2.1.trans (k2.trans b2.2.1), b4.2.2.1.trans (k3.trans b2.2.2.1),
      b4.2.2.2.1.trans (k4.trans b2.2.2.2.1), b4.2.2.2.2.1.trans (k5.trans b2.2.2.2.2.1),
      b4.2.2.2.2.2.trans (k6.trans b2.2.2.2.2.2)⟩
  · rw [← h2s]
    exact congrArg (ofBytesLE 64) (rd_out2 h3o (by decide) (by bv_omega) (by decide))
  · rw [hg₄]
    rfl
  · show Y₄.cpu.gpr.rsp + 8 = _
    rw [hsp₄]
    rfl

end FV7z.Lpi
