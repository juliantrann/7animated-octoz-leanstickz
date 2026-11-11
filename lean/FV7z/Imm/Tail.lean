import FV7z.Imm.Hand
import FV7z.Raf.Holds
/-!
# `_int_malloc`: from the return of `sysmalloc` to the `ret` (PLAN.md G3, `malloc`)

- `pops`: the addresses of the six `pop`s.
- `vc_3285`: what the pieces from offset 3285 need: a chunk in `rax`, `perturb_byte` 0, the frame readable.
- `im_c`: the run from offset 3285 to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
namespace FV7z.Imm
variable {F : Footprint} {Wl : List Rgn}

/-- The addresses of the six `pop`s and the stack pointer after them. -/
theorem pops (S : Addr) : S + 136#64 + 8 = S + 144#64 ∧ S + 144#64 + 8 = S + 152#64 ∧
    S + 152#64 + 8 = S + 160#64 ∧ S + 160#64 + 8 = S + 168#64 ∧ S + 168#64 + 8 = S + 176#64 ∧
    S + 176#64 + 8 = S + 184#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- From the return of `sysmalloc` with a chunk (`rax` not 0) and no `perturb_byte`: to the `ret`, the frame given
back, `rax` kept and the registers a call keeps read from the frame. -/
theorem vc_3285 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax ≠ 0#64)
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (hst : ∀ i < 184, Foot F.data (Addr.add g.rsp i)) :
    W_3285 fb F Wl (fun j' g' _ V' => j' = 950 ∧ V' = V ∧ g'.rax = g.rax ∧ g'.rsp = g.rsp + 184#64 ∧
      g'.rbx = rdq(V, g.rsp + 136#64) ∧ g'.rbp = rdq(V, g.rsp + 144#64) ∧ g'.r12 = rdq(V, g.rsp + 152#64) ∧
      g'.r13 = rdq(V, g.rsp + 160#64) ∧ g'.r14 = rdq(V, g.rsp + 168#64) ∧ g'.r15 = rdq(V, g.rsp + 176#64))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hst ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := pops rsp
  wpx [W_3285, W_3297, W_930, o23, o24, o7, Op.lda, hp0, a1, a2, a3, a4, a5, a6]
  refine ⟨fun h => absurd (by simpa using h) hax, fun _ => ⟨hpb, fun _ => ⟨off_ft hst 136 rfl (by decide),
    off_ft hst 144 rfl (by decide), off_ft hst 152 rfl (by decide), off_ft hst 160 rfl (by decide),
    off_ft hst 168 rfl (by decide), off_ft hst 176 rfl (by decide)⟩, fun h => absurd h (by decide)⟩⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- From offset 3285, the return of `sysmalloc` with a chunk in `rax` (not 0), no `perturb_byte`: the run reaches
the return address with `rax` kept, the frame given back and the registers a call keeps read from the frame; no
byte is written. -/
theorem im_c {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at.add 3285)
    (hax : X.cpu.gpr.rax ≠ 0#64) (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i))
    (hp0 : rdd(V, 8013220#64) = 0) (hst : ∀ i < 192, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 184#64) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = X.cpu.gpr.rax →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 192#64 ∧ Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp + 136#64) ∧
        Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 144#64) ∧ Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 152#64) ∧
        Z.cpu.gpr.r13 = rdq(V, X.cpu.gpr.rsp + 160#64) ∧ Z.cpu.gpr.r14 = rdq(V, X.cpu.gpr.rsp + 168#64) ∧
        Z.cpu.gpr.r15 = rdq(V, X.cpu.gpr.rsp + 176#64)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_3285 prof fb).run c hfs hin _ hK hA hrip
    (vc_3285 hax hpb hp0 (fun i hi => hst i (by omega))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hax₁, hsp₁, hbx, hbp, h12, h13, h14, h15⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_950 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₁]
    exact off_ft hst 184 rfl (by decide) i hi
  · rw [hsp₁]
    exact hra
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg']; exact hax₁) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg']
    show Y.cpu.gpr.rsp + 8 = _
    rw [hsp₁]
    bv_omega
  all_goals
    rw [hg']
    assumption
end FV7z.Imm
