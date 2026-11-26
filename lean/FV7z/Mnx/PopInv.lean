import FV7z.Mnx.Get
import FV7z.Mnx.PopRun
/-!
# The `malloc` contract on the tcache path (PLAN.md G3, `malloc`)

- `mal_pop_inv`: from 52 (the pushes done, `rbx` the bin `ix`) with `GlB` and `TcSt V C bins`, bin `ix` with head
  `e`: `malloc` returns `e` with `GlB` and `TcSt W C (bpop bins ix)`, from `mal_pop_tail` and `pop_inv`. The frame
  `[S, S + 32)` (the three pushes and the return address) apart from the tcache and from `e`'s `key`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Mal (GlB TcSt tcnt tent)
open FV7z.Ifr (a2 a8)
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `malloc` from 52 with a chunk in bin `ix`: the entry `e` back, `GlB` kept, bin `ix` without `e`. -/
theorem mal_pop_inv {fb C ix e : Addr} {bins : Nat → List Addr} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mnx_at mnx) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mnx_at.add 52) (hbx : X.cpu.gpr.rbx = ix)
    (hk : ix.toNat < 64) (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (hb : (bins ix.toNat).head? = some e)
    (hlen : (bins ix.toNat).length < 65536) (hC : C ≠ 0#64) (hc : C.toNat + 640 ≤ 2 ^ 64)
    (he : e.toNat + 16 ≤ 2 ^ 64) (eC : e.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat + 8)
    (dis : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 8 ≤ 2 ^ 64 ∧ (x.toNat + 8 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) ∧
      (x.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat))
    (f0 : 40 ≤ fb.toNat) (f1 : fb.toNat + 28 ≤ 2 ^ 64)
    (hG : ∀ a : Addr, Ifr.Gr fb a → (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) ∧
      (a.toNat < e.toNat + 8 ∨ e.toNat + 16 ≤ a.toNat))
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add e i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (e + 8#64) i))
    (hsd : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hS : X.cpu.gpr.rsp.toNat + 32 ≤ 2 ^ 64)
    (sC : X.cpu.gpr.rsp.toNat + 32 ≤ C.toNat ∨ C.toNat + 640 ≤ X.cpu.gpr.rsp.toNat)
    (se : X.cpu.gpr.rsp.toNat + 32 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      GlB F Wl fb C W → TcSt W C (bpop bins ix.toNat) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = e → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 →
      Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp) → Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 8) →
      Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8 + 8) →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨h1, h2, -⟩ := ht _ hk
  have hE : rdq(V, C + ix * 8#64 + 128#64) = e := by
    rw [← a8 hc hk]
    exact h2 e hb
  have hl : 0 < (bins ix.toNat).length := by
    cases hb' : bins ix.toNat with
    | nil => rw [hb'] at hb; simp at hb
    | cons _ _ => simp only [List.length_cons]; omega
  have hcn : cntM V C ix ≠ 0 := by
    intro h0
    have h0' : tcnt V C ix.toNat = 0 := by
      show ofBytesLE 16 (List.map V (byteAddrs (C + BitVec.ofNat 64 (2 * ix.toNat)) 2)) = 0
      rw [a2 hc hk]
      exact h0
    rw [h1] at h0'
    have := congrArg BitVec.toNat h0'
    simp [BitVec.toNat_ofNat] at this <;> omega
  have f1' : ∀ i < 2, Foot F.data (Addr.add (C + ix * 2#64) i) := by
    rw [← a2 hc hk]
    exact hg.fn _ hk
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have q8 : (X.cpu.gpr.rsp + 8).toNat = X.cpu.gpr.rsp.toNat + 8 := by rw [BitVec.toNat_add, h8]; omega
  have q16 : (X.cpu.gpr.rsp + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 16 := by
    rw [BitVec.toNat_add, q8, h8]; omega
  have q24 : (X.cpu.gpr.rsp + 8 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 24 := by
    rw [BitVec.toNat_add, q16, h8]; omega
  have rf : ∀ x : Addr, X.cpu.gpr.rsp.toNat ≤ x.toNat → x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat + 32 →
      rdq(Vget V C ix e (cntM V C ix), x) = rdq(V, x) := fun x b1 b2 =>
    congrArg (ofBytesLE 64) (rd3 V C ix e _ he hc hk (by omega) (by omega) (by omega) (by omega))
  obtain ⟨g1, g2⟩ := pop_inv hg ht hc hk hb he eC dis f0 f1 hG
  refine mal_pop_tail c hfs hin hK hA hrip hbx hk hg.tb hg.tc hC hcn hE hfb hg.tf f1' f2 f3 w1 w2 w3 hsd hin₂ h₂
    (by rw [rf (X.cpu.gpr.rsp + 8 + 8 + 8) (by omega) (by omega)]; exact hra) ?_
  intro Z t' hK' hA' hr' hax hsp hbx' hbp' h12' h13 h14 h15
  exact k Z t' _ hK' hA' g1 g2 hr' hax hsp (hbx'.trans (rf X.cpu.gpr.rsp (by omega) (by omega)))
    (hbp'.trans (rf (X.cpu.gpr.rsp + 8) (by omega) (by omega)))
    (h12'.trans (rf (X.cpu.gpr.rsp + 8 + 8) (by omega) (by omega)))
    h13 h14 h15

end FV7z.Mnx
