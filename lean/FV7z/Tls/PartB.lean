import FV7z.Tls.PartA
/-!
# `__libc_setup_tls`: from the `ret` of `__sbrk` to the `call` of `memcpy` (PLAN.md G3, startup)

- `and_m64`: the block's address rounded to a multiple of 64 is the break, which is one.
- `tls_b`: `__sbrk` having returned the break `b`, the stores of `_dl_static_dtv`'s first entries and of the main
  map's TLS fields (the bytes `WB`), to the `call` of `memcpy (b + 2048, 0x777770, 40)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Tls
variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- The block's address, made a multiple of 64: the break's, which is one. -/
theorem and_m64 (b : BitVec 64) (h : b.toNat % 64 = 0) :
    (64#64 + b + 18446744073709551615#64) &&& 18446744073709551552#64 = b := by
  have e : 64#64 + b + 18446744073709551615#64 = b + 63#64 := by bv_omega
  have hm : 18446744073709551552#64 = ~~~ 63#64 := by decide
  have hb : b.toNat + 63 < 2 ^ 64 := by have := b.isLt; omega
  rw [e, hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h63 : (63#64).getLsbD i = decide (i < 6) := by
    rw [BitVec.getLsbD_ofNat, show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, h63]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h6 : i < 6
  · have h0 : b.getLsbD i = false := by
      have h1 := Nat.testBit_mod_two_pow b.toNat 6 i
      rw [show (2 : Nat) ^ 6 = 64 from rfl, h, Nat.zero_testBit] at h1
      simpa [h6, BitVec.getLsbD] using h1.symm
    simp [h6, h0]
  · simp only [h6, decide_false, Bool.not_false, Bool.and_true]
    have e1 : (b + 63#64).toNat = b.toNat + 63 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [BitVec.getLsbD, BitVec.getLsbD, e1]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 6 := ⟨i - 6, by omega⟩
    rw [← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow]
    congr 1
    omega

/-- The bytes at the `call` of `memcpy`, from those at the `ret` of `__sbrk`. -/
abbrev WB (W : Addr → Byte) (q b : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst W 8027904#64 (toBytesLE 62#64 8)) (q + 24#64) (toBytesLE b 8)) 7944496#64
    (toBytesLE 128#64 8)) 8027936#64 (toBytesLE (2048#64 + b) 8)) 8027944#64 (toBytesLE 0#64 8)

set_option maxHeartbeats 1600000 in
/-- From the `ret` of `__sbrk`, which has returned `b`, to the `call` of `memcpy`. `q` is the stack pointer after
the prologue. -/
theorem tls_b {G : Footprint} {Wn : List Rgn} {s₁ Y : State} {W : Addr → Byte} {q b : Addr} {g₀ : Gprs}
    (c : Seg prof G Wn L s₁ o) (hin : CodeIn L tls_at tls) (hins : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wn s₁ Y) (hA : Agree G Y.proc.mm.mem W) (hr : Y.cpu.rip = Sbrk.sbk_at.add 159)
    (hsp : Y.cpu.gpr.rsp = q - 8) (hra : rdq(W, q - 8) = tls_at.add 189) (hax : Y.cpu.gpr.rax = b)
    (hb : b.toNat % 64 = 0) (hbx : Y.cpu.gpr.rbx = 2176#64) (hbp : Y.cpu.gpr.rbp = 64#64)
    (h12 : Y.cpu.gpr.r12 = 8#64) (h14 : Y.cpu.gpr.r14 = 7943392#64) (h15 : Y.cpu.gpr.r15 = 1#64) (hfr : Fr q g₀ W)
    (hq : 0x7a9000 + 8 ≤ q.toNat) (hq' : q.toNat + 88 ≤ 2 ^ 64)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wn a)
    (hst : ∀ i < 96, Foot Wn (Addr.add (q - 8) i))
    (k : ∀ Z t', KeptW Wn s₁ Z → Agree G Z.proc.mm.mem (WB W q b) → Z.cpu.rip = tls_at.add 299 →
      (Z.cpu.gpr.rsp = q ∧ Z.cpu.gpr.rdi = 2048#64 + b ∧ Z.cpu.gpr.rsi = Y.cpu.gpr.r13 ∧ Z.cpu.gpr.rdx = 40#64 ∧
        Z.cpu.gpr.rbx = 2176#64 ∧ Z.cpu.gpr.rbp = 64#64 ∧ Z.cpu.gpr.r12 = 8#64 ∧ Z.cpu.gpr.r13 = Y.cpu.gpr.r13 ∧
        Z.cpu.gpr.r14 = 7943392#64 ∧ Z.cpu.gpr.r15 = 128#64) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have slot : ∀ a : Addr, ∀ k < 96, a = Addr.add (q - 8) k → Foot Wn a := fun a k hk ha => ha ▸ hst k hk
  refine c.s_ret hK hA hins (Sbrk.lt_len (by decide)) hr (Sbrk.ret_159 _) (fun i hi => ?_) hin (j₂ := 189)
    (lt_len (by decide)) (by rw [hsp]; exact hra) ?_
  · rw [hsp]
    exact c.hws _ (hst i (by omega))
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  have hsp₁ : Y₁.cpu.gpr.rsp = q := by
    rw [hg₁, hsp]
    show q - 8 + 8 = q
    bv_omega
  refine (c_189 prof).run c hin _ hK₁ hA₁ hr₁ (vc_189 (by rw [hg₁]; exact hbp) (by rw [hg₁]; exact h12)
    (by rw [hg₁]; exact h15) hgl (fun i hi => ?_) ?_) ?_
  · rw [hsp₁]
    exact c.hws _ (slot _ (24 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · rw [hsp₁, rd_Vst]
    · exact hfr.ms
    all_goals sd
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hax₁ : Y₁.cpu.gpr.rax = b := by rw [hg₁]; exact hax
  rw [hax₁, and_m64 b hb] at hg₂
  have hrv : rv Y₂ 64 6 = 8#64 := by
    show (Y₂.cpu.gpr.get (regOf 6)).setWidth 64 = _
    rw [hg₂]
    rfl
  refine c.s_div64 hK₂ hA₂ hin (lt_len (by decide)) hr₂ (div_245 _) (by rw [hg₂]; rfl) (by rw [hrv]; decide) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  have hax₂ : Y₂.cpu.gpr.rax = 135#64 := by rw [hg₂]; rfl
  have ed : 135#64 / 8#64 = 16#64 := by decide
  have em : 135#64 % 8#64 = 7#64 := by decide
  rw [hrv, hax₂, ed, em] at hg₃
  have hsp₃ : Y₃.cpu.gpr.rsp = q := by rw [hg₃, hg₂]; exact hsp₁
  have hcx₃ : Y₃.cpu.gpr.rcx = b := by rw [hg₃, hg₂]; rfl
  refine (c_248 prof).run c hin _ hK₃ hA₃ hr₃ (vc_248 (by rw [hg₃]; rfl) (by rw [hg₃, hg₂]; rfl)
    (by rw [hg₃, hg₂, hg₁]; exact hbx) (by rw [hg₃, hg₂, hg₁]; exact h14) hgl (fun i hi => ?_) (fun i hi => ?_) ?_) ?_
  · rw [hsp₃]
    exact c.hws _ (slot _ (16 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · rw [hsp₃]
    exact slot _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  · rw [hsp₃, rd_Vst]
    · exact hfr.fs
    all_goals sd
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hsp₃, hcx₃] at hA₄
  rw [hcx₃] at hg₄
  refine k Y₄ t₄ hK₄ hA₄ hr₄ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg₄]; exact hsp₃
  · rw [hg₄]; rfl
  · rw [hg₄, hg₃, hg₂, hg₁]; rfl
  · rw [hg₄]; rfl
  · rw [hg₄, hg₃, hg₂, hg₁]; exact hbx
  · rw [hg₄, hg₃, hg₂, hg₁]; exact hbp
  · rw [hg₄, hg₃, hg₂, hg₁]; exact h12
  · rw [hg₄, hg₃, hg₂, hg₁]; rfl
  · rw [hg₄, hg₃, hg₂, hg₁]; exact h14
  · rw [hg₄]; rfl

end FV7z.Tls
