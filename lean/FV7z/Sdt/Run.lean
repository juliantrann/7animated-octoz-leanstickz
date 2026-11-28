import FV7z.Sdt.Heap
/-!
# `CArchiveExtractCallback::SetDirsTimes` (PLAN.md §M, M1): the run

`sdt_ok`: from the entry to the return address. The fill (96–141, `fill_ok`) by induction on what is left of
the count `n`, `SetDirTime` of each folder (373–432, `set_ok`) likewise, the items freed from the last
(432–508, `free_ok`) by induction on the index. The heap sort's loops (219–355, 528–696) are the hypothesis `kH`;
the callees (`new`, `0x5ad550`, `SetDirTime`, `delete[]`, `delete`) are `KC` hypotheses. `I P` is the memory
invariant once `new` gave the pairs `P`; `E P` the one after `_size = 0`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sdt
set_option linter.unusedVariables false

open FV7z.Rst (aR e24 V1)
open FV7z.Fr40 (Fr KS)

/-! ## Numbers -/

theorem sw_ix {i : Nat} (h : i < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 64 i := by
  first
  | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  | bv_omega

theorem tn1 {i : Nat} (h : i + 1 < 4294967296) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32).toNat = i + 1 := by
  first
  | (simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  | bv_omega

theorem sw1 {i : Nat} (h : i + 1 < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32) = BitVec.ofNat 64 (i + 1) := by
  first
  | (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
     omega)
  | bv_omega

theorem tn2 {k : Nat} (h : k + 1 < 4294967296) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 k + 1#64)).toNat = k + 1 := by
  first
  | (simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  | bv_omega

theorem ad1 (k : Nat) : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  first
  | (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
     omega)
  | bv_omega

theorem swn (d : BitVec 32) : BitVec.setWidth 64 d = BitVec.ofNat 64 d.toNat := by
  rw [BitVec.ofNat_toNat]

theorem a1 {d : BitVec 32} (h : 1 ≤ d.toNat) :
    BitVec.setWidth 64 d + 18446744073709551615#64 = BitVec.ofNat 64 (d.toNat - 1) := by
  have hd := d.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hd ⊢
  omega

theorem sh3 (x : BitVec 64) : x <<< (3 : Nat) = x * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow,
    Nat.reduceMod]
  all_goals omega

theorem r12n {d : BitVec 32} (h : 1 ≤ d.toNat) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 d + 18446744073709551615#64)) <<< (3 : Nat) =
      BitVec.ofNat 64 (d.toNat - 1) * 8#64 := by
  have hd := d.isLt
  simp only [Nat.reducePow] at hd
  rw [a1 h, sw_ix (i := d.toNat - 1) (by omega), sh3]

theorem zs (k : Nat) : BitVec.ofNat 64 (k + 1) * 8#64 - 8#64 = BitVec.ofNat 64 k * 8#64 := by
  first
  | (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
     omega)
  | bv_omega

theorem zk {k : Nat} (h : k + 1 < 2147483648) :
    ¬ BitVec.ofNat 64 (k + 1) * 8#64 - 8#64 = 18446744073709551608#64 := by
  rw [zs]
  intro e
  have := congrArg BitVec.toNat e
  first
  | (simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this; omega)
  | bv_omega

theorem p04 (P : Addr) : P + BitVec.ofNat 64 0 * 8#64 + 4#64 = P + 4#64 := by
  first
  | rw [show BitVec.ofNat 64 0 * 8#64 = 0#64 by decide, BitVec.add_zero]
  | bv_omega

/-- The count's value as `new`'s argument (`r13`). -/
abbrev nq (V : Addr → Byte) (g0 : Gprs) : BitVec 64 := BitVec.setWidth 64 rdd(V2 V g0, aR g0.rsp + 12#64)

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-! ## The fill -/

set_option maxHeartbeats 4000000 in
/-- The fill from 96 (`r12` = `i` below the count `n32`, `rbp` = the pairs `P`, `r13` = `N`) to 141: the
pair `i`'s index stored, `0x5ad550` (`ka`) at 123, `i + 1` below `n32` back to 96, else to 141 (`k141`). -/
theorem fill_ok {g0 : Gprs} {P : Addr} {N : BitVec 64} {I : (Addr → Byte) → Prop} {n32 : BitVec 32}
    {cA : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdt_at sdt)
    (hinA : CodeIn L 0x5ad550#64 cA) (hA0 : 0 < cA.length) (hlb : n32.toNat < 2147483648)
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 536#64) i))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 544#64) i))
    (e544 : ∀ W, I W → rdd(W, g0.rdi + 544#64) = n32)
    (fit : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) k))
    (f56 : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) + 56#64) k))
    (w4 : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 4, Foot Wl (Addr.add (P + BitVec.ofNat 64 i * 8#64 + 4#64) k))
    (ka : ∀ (i r : Nat) (G : Gprs) (W : Addr → Byte), i < n32.toNat → G.rsp = aR g0.rsp →
      G.rdi = P + BitVec.ofNat 64 i * 8#64 → I W →
      KC prof F Wl L s₀ o gev gP gE 0x5ad550#64 r G
        (Vst W (P + BitVec.ofNat 64 i * 8#64 + 4#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 i)) 4))
        fun _ W' => I W')
    (k141 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 141 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r13 = N → I W → GoG prof L o gev gP gE Y t') :
    ∀ (m i : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), n32.toNat - i < m → i < n32.toNat → I W →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = sdt_at.add 96 →
      Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 i → Y.cpu.gpr.r13 = N → GoG prof L o gev gP gE Y t' := by
  intro m
  induction m with
  | zero => intro i Y W t' hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
    intro i Y W t' hm hi hIW hKY hAY hrY gs gb gp g12 g13
    have hsw : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) = BitVec.ofNat 64 i := by
      rw [g12]; exact sw_ix (by omega)
    refine (c_96 prof).run c hin (fun j' g' _ V' => j' = 123 ∧
        V' = Vst W (P + BitVec.ofNat 64 i * 8#64 + 4#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 i)) 4) ∧
        g'.rsp = aR g0.rsp ∧ g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 i ∧ g'.r13 = N ∧
        g'.rdi = P + BitVec.ofNat 64 i * 8#64) hKY hAY hrY
      (vc_96 (by rw [gb]; exact f536) (by rw [gb, hsw]; exact fit W hIW i hi)
        (by rw [gp, hsw]; exact w4 W hIW i hi) (by rw [gb, hsw]; exact f56 W hIW i hi)
        fun _ a b d e r x _ _ => ⟨rfl, by rw [gp, hsw, g12], a.trans gs, b.trans gb, d.trans gp, e.trans g12,
          r.trans g13, by rw [x, gp, hsw]⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs₁, gb₁, gp₁, g12₁, g13₁, gdi₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_123 _) hinA hA0 tgt_123
      (by rw [gs₁]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine ka i (123 + 5) U.cpu.gpr W hi gs₁ gdi₁ hIW Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
    rintro Z W' t₃ hKZ hAZ hrZ hfr hIW'
    have hIW'' : I W' := hIW'
    have zs : Z.cpu.gpr.rsp = aR g0.rsp := hfr.1.trans gs₁
    have zb : Z.cpu.gpr.rbx = g0.rdi := hfr.2.1.trans gb₁
    have zp : Z.cpu.gpr.rbp = P := hfr.2.2.1.trans gp₁
    have z12 : Z.cpu.gpr.r12 = BitVec.ofNat 64 i := hfr.2.2.2.1.trans g12₁
    have z13 : Z.cpu.gpr.r13 = N := hfr.2.2.2.2.1.trans g13₁
    have e4 := e544 W' hIW''
    rcases Nat.lt_or_ge (i + 1) n32.toNat with h1 | h1
    · refine (c_128 prof).run c hin (fun j' g' _ V' => j' = 96 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 (i + 1) ∧ g'.r13 = N) hKZ hAZ hrZ
        (vc_128c (by rw [zb]; exact f544) (by rw [zb, e4, z12, tn1 (i := i) (by omega)]; exact h1)
          fun _ a b d e r _ => ⟨rfl, rfl, a.trans zs, b.trans zb, d.trans zp,
            by rw [r, z12, sw1 (i := i) (by omega)], e.trans z13⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e, r⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact ih (i + 1) U₂ W' t₄ (by omega) h1 hIW'' hKU₂ hAU₂ hrU₂ a b d e r
    · refine (c_128 prof).run c hin (fun j' g' _ V' => j' = 141 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r13 = N) hKZ hAZ hrZ
        (vc_128e (by rw [zb]; exact f544)
          (by rw [zb, e4, z12]; exact BitVec.eq_of_toNat_eq (by rw [tn1 (i := i) (by omega)]; omega))
          fun _ a b d e _ => ⟨rfl, rfl, a.trans zs, b.trans zb, d.trans zp, e.trans z13⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact k141 U₂ W' t₄ hKU₂ hAU₂ hrU₂ a b d e hIW''

/-! ## `SetDirTime` of each folder -/

set_option maxHeartbeats 4000000 in
/-- From 373 (`r12` = `k` below `n32`, `rcx` = the pair `k`'s index) to 432: `SetDirTime` (`kt`) of the item at
that index (388), `k + 1` below `n32` back to 373, else `r12` = `8 (n32 - 1)` to 432 (`k432`). -/
theorem set_ok {g0 : Gprs} {P : Addr} {I : (Addr → Byte) → Prop} {n32 : BitVec 32} {cT : List Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdt_at sdt)
    (hinT : CodeIn L 0x5ad590#64 cT) (hT0 : 0 < cT.length) (hlb : n32.toNat < 2147483648) (hn0 : ¬ n32 = 0)
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 536#64) i))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 544#64) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR g0.rsp + 12#64) i))
    (e12 : ∀ W, I W → rdd(W, aR g0.rsp + 12#64) = n32)
    (e544 : ∀ W, I W → rdd(W, g0.rdi + 544#64) = n32)
    (fit : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) k))
    (f56 : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) + 56#64) k))
    (w4 : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 4, Foot Wl (Addr.add (P + BitVec.ofNat 64 i * 8#64 + 4#64) k))
    (ix : ∀ W, I W → ∀ i < n32.toNat, (rdd(W, P + BitVec.ofNat 64 i * 8#64 + 4#64)).toNat < n32.toNat)
    (kt : ∀ (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I W →
      KC prof F Wl L s₀ o gev gP gE 0x5ad590#64 r G W fun _ W' => I W')
    (k432 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 432 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 (n32.toNat - 1) * 8#64 → I W → GoG prof L o gev gP gE Y t') :
    ∀ (m k : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), n32.toNat - k < m → k < n32.toNat → I W →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = sdt_at.add 373 →
      Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 k →
      Y.cpu.gpr.rcx = BitVec.setWidth 64 rdd(W, P + BitVec.ofNat 64 k * 8#64 + 4#64) →
      GoG prof L o gev gP gE Y t' := by
  have f12 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 12#64) i) := fun i hi => c.hws _ (w12 i hi)
  intro m
  induction m with
  | zero => intro k Y W t' hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
    intro k Y W t' hm hk hIW hKY hAY hrY gs gb gp g12 gcx
    have hx := ix W hIW k hk
    have hc : Y.cpu.gpr.rcx = BitVec.ofNat 64 (rdd(W, P + BitVec.ofNat 64 k * 8#64 + 4#64)).toNat := by
      rw [gcx, swn]
    refine (c_373 prof).run c hin (fun j' g' _ V' => j' = 388 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
        g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k) hKY hAY hrY
      (vc_373 (by rw [gb]; exact f536) (by rw [gb, hc]; exact fit W hIW _ hx)
        (by rw [gb, hc]; exact f56 W hIW _ hx)
        fun _ a b d e _ _ _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, e.trans g12⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs₁, gb₁, gp₁, g12₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_388 _) hinT hT0 tgt_388
      (by rw [gs₁]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine kt (388 + 5) U.cpu.gpr W gs₁ hIW Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
    rintro Z W' t₃ hKZ hAZ hrZ hfr hIW'
    have hIW'' : I W' := hIW'
    have zs : Z.cpu.gpr.rsp = aR g0.rsp := hfr.1.trans gs₁
    have zb : Z.cpu.gpr.rbx = g0.rdi := hfr.2.1.trans gb₁
    have zp : Z.cpu.gpr.rbp = P := hfr.2.2.1.trans gp₁
    have z12 : Z.cpu.gpr.r12 = BitVec.ofNat 64 k := hfr.2.2.2.1.trans g12₁
    have e2 := e12 W' hIW''
    rcases Nat.lt_or_ge (k + 1) n32.toNat with h1 | h1
    · refine (c_393 prof).run c hin (fun j' g' _ V' => j' = 373 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 (k + 1) ∧
          g'.rcx = BitVec.setWidth 64 rdd(W', P + BitVec.ofNat 64 (k + 1) * 8#64 + 4#64)) hKZ hAZ hrZ
        (vc_393c (by rw [zs]; exact f12)
          (by rw [zp, z12, ad1]; exact fun i hi => c.hws _ (w4 W' hIW'' (k + 1) h1 i hi))
          (by rw [zs, e2, z12, tn2 (k := k) (by omega)]; exact h1)
          fun _ a b d e r _ => ⟨rfl, rfl, a.trans zs, b.trans zb, d.trans zp, by rw [e, z12, ad1],
            by rw [r, zp, z12, ad1]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e, r⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact ih (k + 1) U₂ W' t₄ (by omega) h1 hIW'' hKU₂ hAU₂ hrU₂ a b d e r
    · have hk1 : k + 1 = n32.toNat := by omega
      have e4 := e544 W' hIW''
      refine (c_393 prof).run c hin (fun j' g' _ V' => j' = 432 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 (n32.toNat - 1) * 8#64) hKZ hAZ hrZ
        (vc_393n (by rw [zs]; exact f12)
          (by rw [zs, e2, z12]; exact BitVec.eq_of_toNat_eq (by rw [tn2 (k := k) (by omega)]; omega))
          (by rw [zb]; exact f544) (by rw [zb, e4]; exact hn0)
          fun _ a b d e _ => ⟨rfl, rfl, a.trans zs, b.trans zb, d.trans zp,
            by rw [e, zb, e4, r12n (d := n32) (by omega)]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact k432 U₂ W' t₄ hKU₂ hAU₂ hrU₂ a b d e hIW''

/-! ## The items freed -/

set_option maxHeartbeats 4000000 in
/-- From 432 (`r12` = `8 k`, `k` below `n32`) to 508: the item at `k` (if any) freed, its path by `delete[]`
(`kd`, 457), the item by `operator delete` (`ke`, 470); `k` = 0: `_size = 0` (`E` after it, `hIE`) and, the pairs
`P` not null, `delete[] P` (`kp`, 503); then to 508 (`k508`). -/
theorem free_ok {g0 : Gprs} {P : Addr} {I E : (Addr → Byte) → Prop} {n32 : BitVec 32} {cD cE : List Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdt_at sdt)
    (hinD : CodeIn L 0x6014f0#64 cD) (hD0 : 0 < cD.length) (hinE : CodeIn L 0x6014e0#64 cE) (hE0 : 0 < cE.length)
    (hlb : n32.toNat < 2147483648) (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 536#64) i))
    (w544 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 544#64) i))
    (fit : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) k))
    (f56 : ∀ W, I W → ∀ i < n32.toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) + 56#64) k))
    (hIE : ∀ W, I W → E (Vst W (g0.rdi + 544#64) (toBytesLE 0#32 4)))
    (kd : ∀ (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I W →
      KC prof F Wl L s₀ o gev gP gE 0x6014f0#64 r G W fun _ W' => I W')
    (ke : ∀ (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I W →
      KC prof F Wl L s₀ o gev gP gE 0x6014e0#64 r G W fun _ W' => I W')
    (kp : ∀ (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → G.rdi = P → E W →
      KC prof F Wl L s₀ o gev gP gE 0x6014f0#64 r G W fun _ W' => E W')
    (k508 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 508 → Y.cpu.gpr.rsp = aR g0.rsp → E W → GoG prof L o gev gP gE Y t') :
    ∀ (k : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), k < n32.toNat → I W →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = sdt_at.add 432 →
      Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 k * 8#64 → GoG prof L o gev gP gE Y t' := by
  -- from 500: `delete[] P` at 503
  have T500 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 500 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbp = P → E W →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY gs gp hEW
    refine (c_500 prof).run c hin (fun j' g' _ V' => j' = 503 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧ g'.rdi = P)
      hKY hAY hrY (vc_500 fun _ a b _ => ⟨rfl, rfl, a.trans gs, b.trans gp⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs₁, gdi₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_503 _) hinD hD0 tgt_503
      (by rw [gs₁]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine kp (503 + 5) U.cpu.gpr W gs₁ gdi₁ hEW Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
    rintro Z W' t₃ hKZ hAZ hrZ hfr hEW'
    exact k508 Z W' t₃ hKZ hAZ hrZ (hfr.1.trans gs₁) hEW'
  -- from 432 to 475
  have L432 : ∀ (k : Nat), k < n32.toNat →
      (∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
        Y.cpu.rip = sdt_at.add 475 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
        Y.cpu.gpr.r12 = BitVec.ofNat 64 k * 8#64 → I W → GoG prof L o gev gP gE Y t') →
      ∀ (Y : State) (W : Addr → Byte) (t' : Nat), I W → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
        Y.cpu.rip = sdt_at.add 432 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi →
        Y.cpu.gpr.rbp = P → Y.cpu.gpr.r12 = BitVec.ofNat 64 k * 8#64 → GoG prof L o gev gP gE Y t' := by
    intro k hk hC Y W t' hIW hKY hAY hrY gs gb gp g12
    have hf := fit W hIW k hk
    by_cases hz : rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 k * 8#64) = 0
    · refine (c_432 prof).run c hin (fun j' g' _ V' => j' = 475 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k * 8#64) hKY hAY hrY
        (vc_432z (by rw [gb]; exact f536) (by rw [gb, g12]; exact hf) (by rw [gb, g12]; exact hz)
          fun _ a b d e _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, e.trans g12⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
      subst V₁ hgU
      exact hC U W t₁ hKU hAU hrU a b d e hIW
    · have hp := f56 W hIW k hk
      -- from 462: `operator delete` of the item at 470
      have T462 : ∀ (Y' : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W' →
          Y'.cpu.rip = sdt_at.add 462 → Y'.cpu.gpr.rsp = aR g0.rsp → Y'.cpu.gpr.rbx = g0.rdi →
          Y'.cpu.gpr.rbp = P → Y'.cpu.gpr.r12 = BitVec.ofNat 64 k * 8#64 → I W' →
          GoG prof L o gev gP gE Y' t'' := by
        intro Y' W' t'' hKY' hAY' hrY' gs' gb' gp' g12' hIW'
        refine (c_462 prof).run c hin (fun j' g' _ V' => j' = 470 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
            g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k * 8#64) hKY' hAY' hrY'
          (vc_462 fun _ a b d e _ _ _ => ⟨rfl, rfl, a.trans gs', b.trans gb', d.trans gp', e.trans g12'⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_470 _) hinE hE0 tgt_470
          (by rw [a]; exact hr8) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        refine ke (470 + 5) U.cpu.gpr W' a hIW' Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
        rintro Z W'' t₃ hKZ hAZ hrZ hfr hIW''
        exact hC Z W'' t₃ hKZ hAZ hrZ (hfr.1.trans a) (hfr.2.1.trans b) (hfr.2.2.1.trans d)
          (hfr.2.2.2.1.trans e) hIW''
      by_cases hq : rdq(W, rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 k * 8#64) + 56#64) = 0
      · refine (c_432 prof).run c hin (fun j' g' _ V' => j' = 462 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
            g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k * 8#64) hKY hAY hrY
          (vc_432a (by rw [gb]; exact f536) (by rw [gb, g12]; exact hf) (by rw [gb, g12]; exact hz)
            (by rw [gb, g12]; exact hp) (by rw [gb, g12]; exact hq)
            fun _ a b d e _ _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, e.trans g12⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        exact T462 U W t₁ hKU hAU hrU a b d e hIW
      · refine (c_432 prof).run c hin (fun j' g' _ V' => j' = 457 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
            g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k * 8#64) hKY hAY hrY
          (vc_432b (by rw [gb]; exact f536) (by rw [gb, g12]; exact hf) (by rw [gb, g12]; exact hz)
            (by rw [gb, g12]; exact hp) (by rw [gb, g12]; exact hq)
            fun _ a b d e _ _ _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, e.trans g12⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_457 _) hinD hD0 tgt_457
          (by rw [a]; exact hr8) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        refine kd (457 + 5) U.cpu.gpr W a hIW Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
        rintro Z W' t₃ hKZ hAZ hrZ hfr hIW'
        exact T462 Z W' t₃ hKZ hAZ hrZ (hfr.1.trans a) (hfr.2.1.trans b) (hfr.2.2.1.trans d)
          (hfr.2.2.2.1.trans e) hIW'
  -- from 475, by induction on the index
  have T475 : ∀ (k : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), k < n32.toNat → I W →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = sdt_at.add 475 →
      Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r12 = BitVec.ofNat 64 k * 8#64 → GoG prof L o gev gP gE Y t' := by
    intro k
    induction k with
    | zero =>
      intro Y W t' hk hIW hKY hAY hrY gs gb gp g12
      have he : Y.cpu.gpr.r12 - 8#64 = 18446744073709551608#64 := by rw [g12]; decide
      by_cases h0 : Y.cpu.gpr.rbp = 0
      · refine (c_475 prof).run c hin (fun j' g' _ V' => j' = 508 ∧
            V' = Vst W (g0.rdi + 544#64) (toBytesLE 0#32 4) ∧ g'.rsp = aR g0.rsp) hKY hAY hrY
          (vc_475z he (by rw [gb]; exact w544) h0 fun _ a _ => ⟨rfl, by rw [gb], a.trans gs⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, a⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        exact k508 U _ t₁ hKU hAU hrU a (hIE W hIW)
      · refine (c_475 prof).run c hin (fun j' g' _ V' => j' = 500 ∧
            V' = Vst W (g0.rdi + 544#64) (toBytesLE 0#32 4) ∧ g'.rsp = aR g0.rsp ∧ g'.rbp = P) hKY hAY hrY
          (vc_475p he (by rw [gb]; exact w544) h0 fun _ a b _ => ⟨rfl, by rw [gb], a.trans gs, b.trans gp⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, a, b⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        exact T500 U _ t₁ hKU hAU hrU a b (hIE W hIW)
    | succ k ih =>
      intro Y W t' hk hIW hKY hAY hrY gs gb gp g12
      refine (c_475 prof).run c hin (fun j' g' _ V' => j' = 432 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = BitVec.ofNat 64 k * 8#64) hKY hAY hrY
        (vc_475c (by rw [g12]; exact zk (by omega))
          fun _ a b d e _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, by rw [e, g12, zs]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
      subst V₁ hgU
      exact L432 k (by omega) (fun Y₁ W₁ t₁' a₁ b₁ d₁ e₁ f₁ r₁ x₁ hI₁ =>
        ih Y₁ W₁ t₁' (by omega) hI₁ a₁ b₁ d₁ e₁ f₁ r₁ x₁) U W t₁ hIW hKU hAU hrU a b d e
  intro k Y W t' hk hIW hKY hAY hrY gs gb gp g12
  exact L432 k hk (fun Y₁ W₁ t₁' a₁ b₁ d₁ e₁ f₁ r₁ x₁ hI₁ => T475 k Y₁ W₁ t₁' hk hI₁ a₁ b₁ d₁ e₁ f₁ r₁ x₁)
    Y W t' hIW hKY hAY hrY gs gb gp g12

/-! ## The run -/

set_option maxHeartbeats 4000000 in
/-- `SetDirsTimes ()` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`, `this` = `g0.rdi`, the count
`n32` = `cnt V g0` below `2^31`): the pushes' slots, the count's slot `aR S + 12`, `_size` and the `call`s' return
address slot in what the run may store into; `_arc`, `_extractedFolders`' items and the return address readable;
`hS2`, the stack as the prologue leaves it. `new` (`kn`, `8 n32` bytes) gives the pairs `P` and the invariant
`I P`, which gives the stack slot's and `_size`'s count (`e12`, `e544`), the items' and their paths' slots
(`fit`, `f56`), the pairs' slots in what the run may store into (`w4`), the pairs' indices below `n32` (`ix`),
and `E P` after `_size = 0` (`hIE`), which gives the stack (`hEs`). The heap sort (`kH`, from 219 to 355:
`rcx` = the first pair's index) and the callees keep them. At the return address (`kr`): `rsp` 8 above the
entry's, the callee-saved registers as they were. -/
theorem sdt_ok {g0 : Gprs} {I E : Addr → (Addr → Byte) → Prop} {cN cA cT cD cE : List Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdt_at sdt)
    (hinN : CodeIn L 0x6029b0#64 cN) (hN0 : 0 < cN.length) (hinA : CodeIn L 0x5ad550#64 cA) (hA0 : 0 < cA.length)
    (hinT : CodeIn L 0x5ad590#64 cT) (hT0 : 0 < cT.length) (hinD : CodeIn L 0x6014f0#64 cD) (hD0 : 0 < cD.length)
    (hinE : CodeIn L 0x6014e0#64 cE) (hE0 : 0 < cE.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sdt_at) (hg0 : X.cpu.gpr = g0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR g0.rsp + 12#64) i))
    (w544 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 544#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 64#64) i))
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 536#64) i))
    (hra : rdq(V, g0.rsp) = e₂.add j₂) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hS2 : Stk (V2 V g0) g0.rsp g0 (e₂.add j₂)) (hlb : (cnt V g0).toNat < 2147483648)
    (e12 : ∀ P W, I P W → rdd(W, aR g0.rsp + 12#64) = cnt V g0)
    (e544 : ∀ P W, I P W → rdd(W, g0.rdi + 544#64) = cnt V g0)
    (fit : ∀ P W, I P W → ∀ i < (cnt V g0).toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) k))
    (f56 : ∀ P W, I P W → ∀ i < (cnt V g0).toNat, ∀ k < 8,
      Foot F.data (Addr.add (rdq(W, rdq(W, g0.rdi + 536#64) + BitVec.ofNat 64 i * 8#64) + 56#64) k))
    (w4 : ∀ P W, I P W → ∀ i < (cnt V g0).toNat, ∀ k < 4,
      Foot Wl (Addr.add (P + BitVec.ofNat 64 i * 8#64 + 4#64) k))
    (ix : ∀ P W, I P W → ∀ i < (cnt V g0).toNat,
      (rdd(W, P + BitVec.ofNat 64 i * 8#64 + 4#64)).toNat < (cnt V g0).toNat)
    (hIE : ∀ P W, I P W → E P (Vst W (g0.rdi + 544#64) (toBytesLE 0#32 4)))
    (hEs : ∀ P W, E P W → Stk W g0.rsp g0 (e₂.add j₂))
    (kn : ∀ (r : Nat) (G : Gprs), G.rsp = aR g0.rsp → G.rdi = nq V g0 * 8#64 →
      KC prof F Wl L s₀ o gev gP gE 0x6029b0#64 r G (V2 V g0) fun Z W' => I Z.rax W')
    (ka : ∀ (P : Addr) (i r : Nat) (G : Gprs) (W : Addr → Byte), i < (cnt V g0).toNat → G.rsp = aR g0.rsp →
      G.rdi = P + BitVec.ofNat 64 i * 8#64 → I P W →
      KC prof F Wl L s₀ o gev gP gE 0x5ad550#64 r G
        (Vst W (P + BitVec.ofNat 64 i * 8#64 + 4#64) (toBytesLE (BitVec.setWidth 32 (BitVec.ofNat 64 i)) 4))
        fun _ W' => I P W')
    (kH : ∀ (P : Addr) (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 219 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      ¬ nq V g0 = 1#64 → Y.cpu.gpr.rax = nq V g0 + 18446744073709551615#64 →
      Y.cpu.gpr.rdi = (nq V g0 >>> 1) + 18446744073709551615#64 →
      Y.cpu.gpr.r9 = P + ((nq V g0 >>> 1) + 18446744073709551615#64) * 8#64 →
      Y.cpu.gpr.r11 = (nq V g0 >>> 1) + 18446744073709551615#64 + ((nq V g0 >>> 1) + 18446744073709551615#64) +
        1#64 → I P W →
      (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
        Z.cpu.rip = sdt_at.add 355 → Z.cpu.gpr.rsp = aR g0.rsp → Z.cpu.gpr.rbx = g0.rdi → Z.cpu.gpr.rbp = P →
        Z.cpu.gpr.rcx = BitVec.setWidth 64 rdd(W', P + 4#64) → I P W' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kt : ∀ (P : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I P W →
      KC prof F Wl L s₀ o gev gP gE 0x5ad590#64 r G W fun _ W' => I P W')
    (kd : ∀ (P : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I P W →
      KC prof F Wl L s₀ o gev gP gE 0x6014f0#64 r G W fun _ W' => I P W')
    (ke : ∀ (P : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → I P W →
      KC prof F Wl L s₀ o gev gP gE 0x6014e0#64 r G W fun _ W' => I P W')
    (kp : ∀ (P : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → G.rdi = P → E P W →
      KC prof F Wl L s₀ o gev gP gE 0x6014f0#64 r G W fun _ W' => E P W')
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have g1 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have g4 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  have g5 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs5 i hi)
  have g6 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) i) :=
    fun i hi => c.hws _ (hs6 i hi)
  have f544 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 544#64) i) := fun i hi => c.hws _ (w544 i hi)
  have f12 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 12#64) i) := fun i hi => c.hws _ (w12 i hi)
  have hrip' : X.cpu.rip = sdt_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hz0 : rdq(V, g0.rdi + 64#64) = 0#64
  · -- `_arc` null: the `ret` at 690
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 690 ∧ V' = V ∧ Fr g0 g') hK hA hrip'
      (by rw [hg0]; exact vc_0z f64 hz0 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gF⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_690 _) (by rw [gF.1]; exact hl) hin₂ h₂
      (by rw [gF.1]; exact hra) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr V Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [gF.1]
    · rw [hgZ']
      exact (show KS g0 U.cpu.gpr from ⟨gF.2.1, gF.2.2.1, gF.2.2.2.1, gF.2.2.2.2.1, gF.2.2.2.2.2.1,
        gF.2.2.2.2.2.2⟩)
  by_cases hc0 : cnt V g0 = 0
  · -- no folders: to 508
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 508 ∧ V' = V2 V g0 ∧ g'.rsp = aR g0.rsp) hK hA hrip'
      (by rw [hg0]; exact vc_0e f64 hz0 hs1 hs2 hs3 hs4 hs5 hs6 f544 w12 hc0 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact tail508 c hin hKU hAU hrU gs hS2 g1 g2 g3 g4 g5 g6 hl hin₂ h₂
      fun Z' t'' a b d e f => kr _ Z' t'' a b d e f
  have hpos : 0 < (cnt V g0).toNat :=
    Nat.pos_of_ne_zero fun h => hc0 (BitVec.eq_of_toNat_eq (h.trans (by decide)))
  have hmsb : (cnt V g0).msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 31 ≤ (cnt V g0).toNat); omega)
  refine (c_0 prof).run c hin (fun j' g' fl V' => j' = 50 ∧ V' = V2 V g0 ∧ g'.rsp = aR g0.rsp ∧
      g'.rbx = g0.rdi ∧ fl.sf = (cnt V g0).msb) hK hA hrip'
    (by rw [hg0]; exact vc_0n f64 hz0 hs1 hs2 hs3 hs4 hs5 hs6 f544 w12 hc0 fun _ a b _ d => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gsf⟩ U t₁ hKU hAU hrU hgU hfU
  subst V₁ hgU hfU
  -- the `js` at 50, not taken
  have hcc : U.cpu.rflags.cond 8 = false := by rw [cond_8, gsf, hmsb]
  refine c.s_jcc_f hKU hAU hin (lt_len (by decide)) hrU (js_50 _) hcc ?_
  rintro Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
  have y1s : Y₁.cpu.gpr.rsp = aR g0.rsp := by rw [hg₁]; exact gs
  have y1b : Y₁.cpu.gpr.rbx = g0.rdi := by rw [hg₁]; exact gb
  refine (c_56 prof).run c hin (fun j' g' _ V' => j' = 69 ∧ V' = V2 V g0 ∧ g'.rsp = aR g0.rsp ∧
      g'.rbx = g0.rdi ∧ g'.r13 = nq V g0 ∧ g'.rdi = nq V g0 * 8#64) hK₁ hA₁ hr₁
    (vc_56 (by rw [y1s]; exact f12) fun _ a b d e _ => ⟨rfl, rfl, a.trans y1s, b.trans y1b, by rw [d, y1s],
      by rw [e, y1s]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs', gb', g13', gdi'⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₁ hgU₂
  -- `new` at 69
  refine c.s_call hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (call_69 _) hinN hN0 tgt_69
    (by rw [gs']; exact hr8) ?_
  rintro Y₂ t₄ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine kn (69 + 5) U₂.cpu.gpr gs' gdi' Y₂ t₄ hK₂ hA₂ hr₂ hg₂ ?_
  rintro Z W' t₅ hKZ hAZ hrZ hfr hIP0
  have hIP : I Z.cpu.gpr.rax W' := hIP0
  have zs : Z.cpu.gpr.rsp = aR g0.rsp := hfr.1.trans gs'
  have zb : Z.cpu.gpr.rbx = g0.rdi := hfr.2.1.trans gb'
  have z13 : Z.cpu.gpr.r13 = nq V g0 := hfr.2.2.2.2.1.trans g13'
  generalize hP : Z.cpu.gpr.rax = P at hIP
  -- from 508
  have T508 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 508 → Y.cpu.gpr.rsp = aR g0.rsp → E P W → GoG prof L o gev gP gE Y t' :=
    fun Y W t' a b d e hE => tail508 c hin a b d e (hEs P W hE) g1 g2 g3 g4 g5 g6 hl hin₂ h₂
      fun Z' t'' x y z u v => kr W Z' t'' x y z u v
  have T432 := free_ok (P := P) (I := I P) (E := E P) (n32 := cnt V g0) c hin hinD hD0 hinE hE0 hlb hr8 f536
    w544 (fit P) (f56 P) (hIE P) (kd P) (ke P) (kp P) T508
  have T373 := set_ok (P := P) (I := I P) c hin hinT hT0 hlb hc0 hr8 f536 f544 w12 (e12 P) (e544 P) (fit P)
    (f56 P) (w4 P) (ix P) (kt P) (fun Y W t' a b d e f r x hI =>
      T432 ((cnt V g0).toNat - 1) Y W t' (by omega) hI a b d e f r x)
  -- from 355
  have T355 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 355 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.rcx = BitVec.setWidth 64 rdd(W, P + 4#64) → I P W → GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY gs gb gp gc hIW
    refine (c_355 prof).run c hin (fun j' g' _ V' => j' = 373 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
        g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = 0#64 ∧
        g'.rcx = BitVec.setWidth 64 rdd(W, P + BitVec.ofNat 64 0 * 8#64 + 4#64)) hKY hAY hrY
      (vc_355 fun _ a b d e r _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, r, by rw [e, gc, p04]⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e, r⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact T373 ((cnt V g0).toNat + 1) 0 U W t₁ (by omega) hpos hIW hKU hAU hrU a b d e r
  -- from 141: one pair, or the heap sort from 219
  have f4 : ∀ W, I P W → ∀ i < 4, Foot F.data (Addr.add (P + 4#64) i) := fun W hIW i hi => by
    have := c.hws _ (w4 P W hIW 0 hpos i hi)
    rwa [p04] at this
  have T141 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = sdt_at.add 141 → Y.cpu.gpr.rsp = aR g0.rsp → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.rbp = P →
      Y.cpu.gpr.r13 = nq V g0 → I P W → GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY gs gb gp g13 hIW
    by_cases h1 : Y.cpu.gpr.r13 = 1#64
    · refine (c_141 prof).run c hin (fun j' g' _ V' => j' = 355 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.rcx = BitVec.setWidth 64 rdd(W, P + 4#64)) hKY hAY hrY
        (vc_141e (by rw [gp]; exact f4 W hIW) h1
          fun _ a b d e _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, by rw [e, gp]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e⟩ U t₁ hKU hAU hrU hgU -
      subst V₁ hgU
      exact T355 U W t₁ hKU hAU hrU a b d e hIW
    · refine (c_141 prof).run c hin (fun j' g' _ V' => j' = 219 ∧ V' = W ∧ g'.rsp = aR g0.rsp ∧
          g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.rax = nq V g0 + 18446744073709551615#64 ∧
          g'.rdi = (nq V g0 >>> 1) + 18446744073709551615#64 ∧
          g'.r9 = P + ((nq V g0 >>> 1) + 18446744073709551615#64) * 8#64 ∧
          g'.r11 = (nq V g0 >>> 1) + 18446744073709551615#64 + ((nq V g0 >>> 1) + 18446744073709551615#64) +
            1#64) hKY hAY hrY
        (vc_141n h1 fun _ a b d e r x y _ => ⟨rfl, rfl, a.trans gs, b.trans gb, d.trans gp, by rw [e, g13],
          by rw [r, g13], by rw [x, gp, g13], by rw [y, g13]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, e, r, x, y⟩ U t₁ hKU hAU hrU hgU -
      subst V₁ hgU
      exact kH P U W t₁ hKU hAU hrU a b d (fun h => h1 (g13.trans h)) e r x y hIW T355
  -- from 74: the pairs `P`, the fill from 96
  refine (c_74 prof).run c hin (fun j' g' _ V' => j' = 96 ∧ V' = W' ∧ g'.rsp = aR g0.rsp ∧
      g'.rbx = g0.rdi ∧ g'.rbp = P ∧ g'.r12 = 0#64 ∧ g'.r13 = nq V g0) hKZ hAZ hrZ
    (vc_74n (by rw [zb]; exact f544) (by rw [zb, e544 P W' hIP]; exact hc0)
      fun _ a b d e r _ => ⟨rfl, rfl, a.trans zs, b.trans zb, d.trans hP, r, e.trans z13⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, a, b, d, r, e⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst V₁ hgU₃
  exact fill_ok (P := P) (N := nq V g0) (I := I P) c hin hinA hA0 hlb hr8 f536 f544 (e544 P) (fit P) (f56 P)
    (w4 P) (ka P) T141 ((cnt V g0).toNat + 1) 0 U₃ W' t₆ (by omega) hpos hIP hKU₃ hAU₃ hrU₃ a b d r e

end FV7z.Sdt
