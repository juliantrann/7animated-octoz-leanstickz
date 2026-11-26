import FV7z.Mnx.PopInv
/-!
# `malloc` from its entry on the tcache path (PLAN.md G3, `malloc`)

- `mal_pop_next`: `malloc (n)` after the first call from its entry (`rsp = S + 216`) with `GlB` and `TcSt V C bins`,
  the bin `ix` of `n` (below `mp_.tcache_bins` = 64) with head `e`: `vc_0n` or `vc_0s` (the pushes, `Mal.Vm`),
  `GlB` and `TcSt` carried over the pushes (`Ifr.GlB.congr`, `Ifr.TcSt.congr`), then `mal_pop_inv`; the pops read
  back what the pushes left (`Mal.regs3`).

Open gap: the tcache null at 52 (`0xc8`, `tcache_init`), a stop of the blocks; excluded here by `C ≠ 0` (the first
call's `malloc_hook_ini` made it).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Mal (GlB TcSt)
open FV7z.Imm (add_n)
open FV7z.Im5 (ClsN)
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `malloc (n)` after the first call from its entry with a chunk in the bin `ix` of `n`: the entry `e` back, `GlB`
kept, bin `ix` without `e`, the registers a call keeps as at the entry. -/
theorem mal_pop_next {fb S C n nb ix e : Addr} {bins : Nat → List Addr} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mnx_at mnx) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hcls : ClsN n nb) (hix : (nb + 18446744073709551599#64) >>> 4 = ix)
    (hk : ix.toNat < 64) (hrip : X.cpu.rip = mnx_at) (hdi : X.cpu.gpr.rdi = n)
    (hrsp : X.cpu.gpr.rsp = S + 216#64) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (f0 : 40 ≤ fb.toNat) (hf24 : fb.toNat + 28 ≤ S.toNat)
    (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (hb : (bins ix.toNat).head? = some e)
    (hlen : (bins ix.toNat).length < 65536) (hC : C ≠ 0#64) (hCS : C.toNat + 640 ≤ S.toNat)
    (he : e.toNat + 16 ≤ S.toNat) (eC : e.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat + 8)
    (dis : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 8 ≤ 2 ^ 64 ∧ (x.toNat + 8 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) ∧
      (x.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat))
    (hD : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 8 ≤ S.toNat)
    (hG : ∀ a : Addr, Ifr.Gr fb a → (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) ∧
      (a.toNat < e.toNat + 8 ∨ e.toNat + 16 ≤ a.toNat))
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add e i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (e + 8#64) i))
    (hsw : ∀ i < 24, Foot Wl (Addr.add (S + 192#64) i))
    (hsd : ∀ i < 32, Foot F.data (Addr.add (S + 192#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 216#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      GlB F Wl fb C W → TcSt W C (bpop bins ix.toNat) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = e → Z.cpu.gpr.rsp = S + 224#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hR := X.cpu.gpr.rsp.isLt
  have hspn : X.cpu.gpr.rsp.toNat = S.toNat + 216 := by rw [hrsp, add_n _ _ (by omega)]
  have s24 : X.cpu.gpr.rsp - 24 = S + 192#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hspn, add_n S 192 (by omega)]
    show (2 ^ 64 - 24 + (S.toNat + 216)) % 2 ^ 64 = S.toNat + 192
    omega
  have hst : ∀ i < 24, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => by
    rw [s24]
    exact hsw i hi
  have hsp' : 7940664 + 8 ≤ X.cpu.gpr.rsp.toNat := by omega
  have e192 : X.cpu.gpr.rsp - 8 - 8 - 8 = S + 192#64 := by rw [hrsp]; exact s192 S
  -- 52 on, the pushes done
  suffices K : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Mal.Vm X.cpu.gpr V) →
      Y.cpu.rip = mnx_at.add 52 → Y.cpu.gpr.rsp = S + 192#64 →
      Y.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4 → Y.cpu.gpr.rbp = n →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Y t₁ by
    rcases hcls with ((⟨h9, h10, h11⟩ | ⟨h8, h32⟩) | ⟨h9, h10, h11⟩) | ⟨rfl, rfl⟩
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0n hdi h9 (by omega) hg.hk hg.fh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁]
      show ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4 = _
      rw [h11]
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0s hdi h8 hg.hk hg.fh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁, h32] <;> rfl
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0n hdi (by omega) (by omega) hg.hk hg.fh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁]
      show ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4 = _
      rw [h11]
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0n hdi (by decide) (by decide) hg.hk hg.fh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁] <;> first | rfl | decide
  intro Y t₁ hKY hAY hrY hspY hbxY _ h13 h14 h15
  have hc : C.toNat + 640 ≤ 2 ^ 64 := by omega
  have f1 : fb.toNat + 28 ≤ 2 ^ 64 := by omega
  have hY : Y.cpu.gpr.rsp.toNat = S.toNat + 192 := by rw [hspY, add_n S 192 (by omega)]
  -- `GlB` and `TcSt` over the pushes
  have hg' : GlB F Wl fb C (Mal.Vm X.cpu.gpr V) := Ifr.GlB.congr hg f0 f1 fun a ha =>
    Vm_out V hrsp hS (.inl (by rcases ha with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega))
  have ht' : TcSt (Mal.Vm X.cpu.gpr V) C bins := Ifr.TcSt.congr ht hc
    (fun i hi x hx => ⟨(dis i hi x hx).1, fun a _ h2 => Vm_out V hrsp hS (.inl (by have := hD i hi x hx; omega))⟩)
    (fun a _ h2 => Vm_out V hrsp hS (.inl (by omega)))
  -- the pops read back what the pushes left
  obtain ⟨r1, r2, r3, r4, -⟩ := Mal.regs3 X.cpu.gpr V (by omega) (by omega)
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 + 8 + 8 + 8 = X.cpu.gpr.rsp - 8 - 8 - 8 + 24#64 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  refine mal_pop_inv c hfs hin hKY hAY hrY (hbxY.trans hix) hk hg' ht' hb hlen hC hc (by omega) eC dis f0 f1 hG
    hfb f2 f3 w1 w2 w3 (by rw [hspY]; exact hsd) (by omega) (.inr (by omega)) (.inr (by omega)) hin₂ h₂
    (by rw [hspY, ← e192, e24, r4, hrsp]; exact hra) ?_
  intro Z t' W hK' hA' g1 g2 hr' hax hsp hbx hbp h12 h13' h14' h15'
  refine k Z t' W hK' hA' g1 g2 hr' hax ?_ (by rw [hbx, hspY, ← e192]; exact r1) (by rw [hbp, hspY, ← e192]; exact r2)
    (by rw [h12, hspY, ← e192]; exact r3) (h13'.trans h13) (h14'.trans h14) (h15'.trans h15)
  rw [hsp, hspY]
  simp only [BitVec.add_assoc] <;> rfl

end FV7z.Mnx
