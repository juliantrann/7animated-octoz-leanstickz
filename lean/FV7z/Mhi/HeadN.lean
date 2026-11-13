import FV7z.Mhi.HoldsN
import FV7z.Mhi.Head
/-!
# `malloc_hook_ini`: from the entry to the call of `tcache_init`, `n ≤ 1032` (PLAN.md G3, `malloc`)

- `mhi_headn`: `mhi_head` with `vc_341n` (`vc_341s` for `n ≤ 8`): `tcache_init` is reached with the tcache index
  of `nb` (`n + 23 &&& -16`, 32 for `n ≤ 8`) in `rbx` and `n` in `rbp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `mhi_head` for every request `n ≤ 1032`: `tcache_init` is reached with the tcache index of `nb`
(`n + 23 &&& -16`, 32 for `n ≤ 8`) in `rbx` and `n` in `rbp`. -/
theorem mhi_headn {fb n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mhi_at mhi) (hinP : CodeIn L Pmi.pmi_at Pmi.pmi) (hinG : CodeIn L Tgv.tgv_at Tgv.tgv)
    (hinT : CodeIn L Tci.tci_at Tci.tci)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mhi_at)
    (hdi : X.cpu.gpr.rdi = n)
    (hcls : (9 ≤ n.toNat ∧ n.toNat ≤ 1032 ∧ n + 23#64 &&& 18446744073709551600#64 = nb) ∨ (n.toNat ≤ 8 ∧ nb = 32#64))
    (hlo : 8029888 + 64 ≤ X.cpu.gpr.rsp.toNat)
    (hf0 : 8013232 + 40 ≤ fb.toNat) (hf1 : fb.toNat + 48 ≤ X.cpu.gpr.rsp.toNat - 64)
    (hst : ∀ i < 64, Foot Wl (Addr.add (X.cpu.gpr.rsp - 64#64) i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (htl : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551592#64) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgmf : ∀ i < 8, Foot Wl (Addr.add (8013224#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfs1 : ∀ i < 1, Foot F.data (Addr.add (fb + 18446744073709551584#64) i))
    (hmi : (rdd(V, 7940484#64)).msb = true)
    (h32 : ∀ d ∈ Pmi.t32, Tgv.Unset F V d) (h64 : ∀ d ∈ Pmi.t64, Tgv.UnsetW F V d)
    (htc : rdq(V, fb + 18446744073709551576#64) = 0#64)
    (hsd : ofBytesLE 8 ((byteAddrs (fb + 18446744073709551584#64) 1).map V) = 0#8)
    (k : ∀ (Vd : Addr → Byte) Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst Vd (X.cpu.gpr.rsp - 32#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) →
      Pmi.Dat fb (X.cpu.gpr.rsp - 32#64) 1 (Vh X.cpu.gpr.rsp X.cpu.gpr V) Vd →
      Z.cpu.rip = Tci.tci_at → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 →
      Z.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4 →
      Z.cpu.gpr.rbp = n →
      (Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hR := X.cpu.gpr.rsp.isLt
  obtain ⟨e32, r32, e3, e4, e24, -, o40, o32, o0, sp8⟩ := ofs X.cpu.gpr.rsp (by omega)
  have D := win hW
  have e0 : (7940656#64 : Addr).toNat = 7940656 := rfl
  -- the entry → 336
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
    (vc_0 hmi (fun i hi => c.hws _ (D (7940484#64) 4 (by decide) (by decide) i hi))
      (D (7940656#64) 8 (by decide) (by decide)) (off_ft hst 40 o40 (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e1 : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hg₁]
  -- the call of `ptmalloc_init`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_336 _) hinP (Pmi.lt_len (j := 0) (by decide)) tgt_336
    (by rw [e1, e32]; exact off_ft hst 32 o32 (by decide)) ?_
  rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
  rw [e1] at hA₀
  have sp₀ : Z₀.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by
    rw [hg₀]; show Y₁.cpu.gpr.rsp - 8 = _; rw [e1]; exact e32
  have ho : ∀ a : Addr, ¬ (7940484 ≤ a.toNat ∧ a.toNat < 2 ^ 64) → Vh X.cpu.gpr.rsp X.cpu.gpr V a = V a :=
    fun a ha => Vh_out _ _ _ (by omega) (by omega) (by omega)
  have g32 : ∀ d ∈ Pmi.t32, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
    simp only [Pmi.t32, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  have g64 : ∀ d ∈ Pmi.t64, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
    simp only [Pmi.t64, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have l8 : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  refine Pmi.pmi_ok (V := Vh X.cpu.gpr.rsp X.cpu.gpr V) c hfs
    (by
      rw [sp₀]
      exact ⟨hinP, hinG, by omega, by omega, by omega, by omega, off_ft hst 0 o0 (by decide),
        fun i hi => c.hws _ (off_ft hst 32 o32 (by decide) i hi), hfl, htl,
        D _ 4 (by decide) (by decide), D _ 4 (by decide) (by decide), D _ 8 (by decide) (by decide),
        D _ 2032 (by decide) (by decide), hgmf⟩)
    hK₀ hA₀ hr₀ (fun d hd => (h32 d hd).out (g32 d hd) (by decide) ho)
    (fun d hd => (h64 d hd).out (g64 d hd) (by decide) ho) hin (lt_len (j := 336 + 5) (by decide))
    (by
      rw [sp₀, ← e32, rd_Vst_self _ _ _ (l8 _) (by rw [e32, r32]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro Vd Z₁ t₂ hK₂ hA₂ hD hr₂ hB
  rw [sp₀] at hD
  obtain ⟨sp₂, bx₂, bp₂, r12₂, r13₂, r14₂, r15₂⟩ := hB
  -- the bytes after `ptmalloc_init`, below the frame and outside `Wr`, those at the entry
  have RD : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 64 →
      (x.toNat + n ≤ 7940484 ∨ 8013232 ≤ x.toNat) → (x.toNat + n ≤ fb.toNat - 24 ∨ fb.toNat - 16 ≤ x.toNat) →
      (x.toNat + n ≤ 7940656 ∨ 7940664 ≤ x.toNat) →
      List.map Vd (byteAddrs x n) = List.map V (byteAddrs x n) := fun x n h1 h2 h3 h4 =>
    rd_eq (by omega) fun a a1 a2 => (hD.out a (by rw [r32]; omega) (by unfold Pmi.Wr; omega)).trans
      (Vh_out _ _ _ (by omega) (by omega) (by omega))
  have f40 : (fb + 18446744073709551576#64).toNat = fb.toNat - 40 := f40 fb (by omega)
  have f32' : (fb + 18446744073709551584#64).toNat = fb.toNat - 32 := f32 fb (by omega)
  -- 341 → 68
  have hhk : rdq(Vd, 7940656#64) = 0#64 := by
    have e : List.map Vd (byteAddrs (7940656#64) 8) = List.map (Vh X.cpu.gpr.rsp X.cpu.gpr V)
        (byteAddrs (7940656#64) 8) :=
      rd_eq (by decide) fun a a1 a2 => hD.out a (by rw [r32]; rw [e0] at a1 a2; omega)
        (by unfold Pmi.Wr; rw [e0] at a1 a2; omega)
    rw [congrArg (ofBytesLE 64) e]
    unfold Vh
    rw [rd_Vst _ _ _ _ _ (by rw [l8, e32, r32]; omega) (by decide) (.inr (by rw [e32, r32, e0]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l8, e4]; omega) (by decide) (.inr (by rw [e4, e0]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l8, e3]; omega) (by decide) (.inr (by rw [e3, e0]; omega)),
      rd_Vst_self _ _ _ (l8 _) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have bp₁ : Z₁.cpu.gpr.rbp = n := by rw [bp₂, hg₀]; show Y₁.cpu.gpr.rbp = _; rw [hg₁]; exact hdi
  have hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i) :=
    fun i hi => c.hws _ (D (7940656#64) 8 (by decide) (by decide) i hi)
  -- from 68 on, both ways
  have K : ∀ j' g fl V₃,
      (j' = 68 ∧ (∃ a, g = { Z₁.cpu.gpr with rax := a, rbx := (nb + 18446744073709551599#64) >>> 4 }) ∧ V₃ = Vd) →
      ∀ Y₃ t₃, KeptW Wl s₀ Y₃ → Agree F Y₃.proc.mm.mem V₃ → Y₃.cpu.rip = mhi_at.add j' → Y₃.cpu.gpr = g →
        Y₃.cpu.rflags = fl → GoG prof L o gev gP gE Y₃ t₃ := by
    rintro j' g fl V₃ ⟨rfl, ⟨a, rfl⟩, hV₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₃
    -- 68 → 231
    refine (c_68 prof fb).run c hfs hin _ hK₃ hA₃ hr₃
      (vc_68 (by rw [congrArg (ofBytesLE 64) (RD _ 8 (by omega) (.inr (by omega)) (.inl (by omega))
          (.inr (by omega)))]; exact htc)
        (by rw [RD _ 1 (by omega) (.inr (by omega)) (.inl (by omega)) (.inr (by omega))]; exact hsd) hft hfs1) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hv₄⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
    rw [hv₄] at hA₄
    have sp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by
      rw [hg₄, hg₃]; show Z₁.cpu.gpr.rsp = _; rw [sp₂, sp₀]; exact sp8
    -- the call of `tcache_init`
    refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_231 _) hinT (Tci.lt_len (j := 0) (by decide)) tgt_231
      (by rw [sp₄, e24]; exact off_ft hst 32 o32 (by decide)) ?_
    rintro Z t' hK' hA' ⟨hr', hg'⟩
    rw [sp₄, e24] at hA'
    refine k Vd Z t' hK' hA' hD hr' (by rw [hg']; show Y₄.cpu.gpr.rsp - 8 = _; rw [sp₄, e24])
      (by rw [hg', hg₄, hg₃]; rfl)
      (by rw [hg', hg₄, hg₃]; exact bp₁)
      ⟨?_, ?_, ?_, ?_⟩
    · rw [hg', hg₄, hg₃]; show Z₁.cpu.gpr.r12 = _; rw [r12₂, hg₀]; show Y₁.cpu.gpr.r12 = _; rw [hg₁]
    · rw [hg', hg₄, hg₃]; show Z₁.cpu.gpr.r13 = _; rw [r13₂, hg₀]; show Y₁.cpu.gpr.r13 = _; rw [hg₁]
    · rw [hg', hg₄, hg₃]; show Z₁.cpu.gpr.r14 = _; rw [r14₂, hg₀]; show Y₁.cpu.gpr.r14 = _; rw [hg₁]
    · rw [hg', hg₄, hg₃]; show Z₁.cpu.gpr.r15 = _; rw [r15₂, hg₀]; show Y₁.cpu.gpr.r15 = _; rw [hg₁]
  rcases hcls with ⟨hn, hn', rfl⟩ | ⟨hn, rfl⟩
  · exact (c_341 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_341n bp₁ hn (by omega) hhk hfh)
      fun j' g fl V₃ ⟨h1, h2, h3⟩ => K j' g fl V₃ ⟨h1, ⟨_, h2⟩, h3⟩
  · have ei : ((32#64 : Addr) + 18446744073709551599#64) >>> 4 = 0#64 := by decide
    exact (c_341 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_341s bp₁ hn hhk hfh)
      fun j' g fl V₃ ⟨h1, h2, h3⟩ => K j' g fl V₃ ⟨h1, ⟨n + 23#64, by rw [h2, ei]⟩, h3⟩

end FV7z.Mhi
