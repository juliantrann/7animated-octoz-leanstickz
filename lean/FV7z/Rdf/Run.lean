import FV7z.Rdf.Holds
/-!
# `NWindows::NFile::NName::ResolveDotsFolders` (PLAN.md §M, M1): the run

`rdf_ok`: from the entry to the return address, the loop at 32 by induction on `2 ln W - i` (`ln W` the string's
length in the bytes `W`, `i` the index; a `Delete` of `n` chars from `x` with `j + 1 ≤ x + n` lowers it), the
backward scans at 184 and 253 by induction on the index.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rdf
set_option linter.unusedVariables false

open FV7z.Fr40 (Fr KS)

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

set_option maxHeartbeats 4000000 in
/-- `ResolveDotsFolders (s)` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`, `s` = `g0.rdi`): the pushes'
slots and the `call`s' return address slot in what the run may store into; `s`, the first char and the return
address readable. The memory invariant `I` with the length `ln`: of the bytes after the pushes (`hI0`, the chars'
pointer and the first char as before, `e0`, `e1`), giving the stack (`hIs`), the chars up to `ln W` readable (`fc`),
the char at `ln W` 0 (`hz`), `ln W < 2 ^ 30` (`hlb`). The callee `kd` (`UString::Delete (s, x, n)`, `x + n ≤ ln W`):
`I` again with the length `ln W - n`. At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved
registers as they were. -/
theorem rdf_ok {g0 : Gprs} {I : (Addr → Byte) → Prop} {ln : (Addr → Byte) → Nat} {cD : List Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rdf_at rdf)
    (hinD : CodeIn L 0x44e0b0#64 cD) (hD : 0 < cD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rdf_at) (hg0 : X.cpu.gpr = g0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add g0.rdi i))
    (fc0 : ∀ i < 4, Foot F.data (Addr.add rdq(V, g0.rdi) i))
    (hra : rdq(V, g0.rsp) = e₂.add j₂) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hI0 : I (V1 V g0)) (e0 : rdq(V1 V g0, g0.rdi) = rdq(V, g0.rdi))
    (e1 : cr (V1 V g0) g0.rdi 0 = rdd(V, rdq(V, g0.rdi)))
    (hIs : ∀ W, I W → Stk W g0.rsp g0 (e₂.add j₂))
    (fc : ∀ W, I W → ∀ k ≤ ln W, ∀ i < 4, Foot F.data (Addr.add (rdq(W, g0.rdi) + BitVec.ofNat 64 (4 * k)) i))
    (hz : ∀ W, I W → cr W g0.rdi (ln W) = 0)
    (hlb : ∀ W, I W → ln W < 1073741824)
    (kd : ∀ (r : Nat) (G : Gprs) (W : Addr → Byte) (x n : Nat), G.rsp = aR g0.rsp → G.rdi = g0.rdi →
      G.rsi = BitVec.ofNat 64 x → G.rdx = BitVec.ofNat 64 n → I W → x + n ≤ ln W →
      KC prof F Wl L s₀ o gev gP gE 0x44e0b0#64 r G W (fun W' => I W' ∧ ln W' + n = ln W))
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have g1 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  -- from 65
  have T65 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = rdf_at.add 65 → Fm (aR g0.rsp) g0 Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t' :=
    fun Y W t' hKY hAY hrY hm hIW => tail65 c hin hKY hAY hrY hm (hIs W hIW) g1 g2 g3 hl hin₂ h₂
      fun Z' t'' a b d e f => kr W Z' t'' a b d e f
  -- from 200
  have T200 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = rdf_at.add 200 → Fm (aR g0.rsp) g0 Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hm hIW
    refine (c_200 prof).run c hin (fun j' g' _ V' => j' = 65 ∧ V' = W ∧ Fm (aR g0.rsp) g0 g') hKY hAY hrY
      (vc_200 fun _ a _ => ⟨rfl, rfl, fmF hm a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gm⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact T65 U W t₁ hKU hAU hrU gm hIW
  -- the loop at 32, by induction on a bound of `2 ln W - j`
  have LP : ∀ (m j : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), 2 * ln W - j < m → j < ln W → I W →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = rdf_at.add 32 →
      Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 Y.cpu.gpr →
      Y.cpu.gpr.rax = BitVec.setWidth 64 (cr W g0.rdi j) → GoG prof L o gev gP gE Y t' := by
    intro m
    induction m with
    | zero => intro j Y W t' hm; exact absurd hm (Nat.not_lt_zero _)
    | succ m ih =>
      -- from 53
      have T53 : ∀ (x : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), 2 * ln W - x < m → x ≤ ln W → I W →
          KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = rdf_at.add 53 →
          L53 (aR g0.rsp) g0.rdi rdq(W, g0.rdi) x g0 Y.cpu.gpr → GoG prof L o gev gP gE Y t' := by
        intro x Y W t' hm hx hIW hKY hAY hrY hL
        by_cases h0 : cr W g0.rdi x = 0
        · refine (c_53 prof).run c hin (fun j' g' _ V' => j' = 65 ∧ V' = W ∧ Fm (aR g0.rsp) g0 g') hKY hAY hrY
            (vc_53 hL (fc W hIW x hx) (fun _ _ a _ => ⟨rfl, rfl, a⟩) (fun h => absurd h0 h)) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gm⟩ U t₁ hKU hAU hrU hgU -
          subst V₁ hgU
          exact T65 U W t₁ hKU hAU hrU gm hIW
        · refine (c_53 prof).run c hin (fun j' g' _ V' => j' = 32 ∧ V' = W ∧
              Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) x g0 g' ∧ g'.rax = BitVec.setWidth 64 (cr W g0.rdi x))
            hKY hAY hrY (vc_53 hL (fc W hIW x hx) (fun h => absurd h h0) (fun _ _ a b _ => ⟨rfl, rfl, a, b⟩)) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gL, gax⟩ U t₁ hKU hAU hrU hgU -
          subst V₁ hgU
          exact ih x U W t₁ hm (ltc hx (hz W hIW) h0) hIW hKU hAU hrU gL gax
      intro j Y W t' hm hj hIW hKY hAY hrY hL hax
      have hzW := hz W hIW
      have hlW := hlb W hIW
      -- from 51
      have T51 : ∀ (Y' : State) (t'' : Nat), KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W →
          Y'.cpu.rip = rdf_at.add 51 → Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 Y'.cpu.gpr →
          Y'.cpu.gpr.rdx = BitVec.ofNat 64 (j + 1) → Y'.cpu.gpr.rbx = BitVec.ofNat 64 (4 * (j + 1)) →
          GoG prof L o gev gP gE Y' t'' := by
        intro Y' t'' hKY' hAY' hrY' hL' hd hb
        refine (c_51 prof).run c hin (fun j' g' _ V' => j' = 53 ∧ V' = W ∧
            L53 (aR g0.rsp) g0.rdi rdq(W, g0.rdi) (j + 1) g0 g') hKY' hAY' hrY'
          (vc_51 hL' hd hb (by omega) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gL'⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        exact T53 (j + 1) U₂ W t₂ (by omega) (by omega) hIW hKU₂ hAU₂ hrU₂ gL'
      -- from 129: `Delete (s, x, n)` at 134, back at 139
      have T129 : ∀ (x n : Nat) (Y' : State) (t'' : Nat), 1 ≤ n → j + 1 ≤ x + n → x + n ≤ ln W →
          KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W → Y'.cpu.rip = rdf_at.add 129 →
          Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) x g0 Y'.cpu.gpr → Y'.cpu.gpr.rbx = BitVec.ofNat 64 (4 * x) →
          Y'.cpu.gpr.rdx = BitVec.ofNat 64 n → GoG prof L o gev gP gE Y' t'' := by
        intro x n Y' t'' hn1 hn2 hn3 hKY' hAY' hrY' hL' hb hd
        refine (c_129 prof).run c hin (fun j' g' _ V' => j' = 134 ∧ V' = W ∧ Fr Y'.cpu.gpr g' ∧
            g'.rsi = BitVec.ofNat 64 x ∧ g'.rdx = Y'.cpu.gpr.rdx ∧ g'.rdi = Y'.cpu.gpr.r12) hKY' hAY' hrY'
          (vc_129 hL'.2.2.2 (by omega) fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gF, gsi, gdx, gdi⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        have gs : U.cpu.gpr.rsp = aR g0.rsp := gF.1.trans hL'.1.1
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_134 _) hinD hD (by decide)
          (by rw [gs]; exact hr8) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        refine kd (134 + 5) U.cpu.gpr W x n gs (gdi.trans hL'.2.1) gsi (gdx.trans hd) hIW hn3
          Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
        rintro Z W' t₃ hKZ hAZ hrZ hfr ⟨hIW', hln⟩
        have zF := frT gF hfr
        refine (c_139 prof).run c hin (fun j' g' _ V' => j' = 53 ∧ V' = W' ∧ Fr Z.cpu.gpr g' ∧
            g'.rsi = rdq(W', Z.cpu.gpr.r12)) hKZ hAZ hrZ
          (vc_139 (by rw [zF.2.2.2.1, hL'.2.1]; exact fp) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gF', gsi'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        have wF := frT zF gF'
        have hlW' := hlb W' hIW'
        exact T53 x U₂ W' t₄ (by omega) (by omega) hIW' hKU₂ hAU₂ hrU₂
          ⟨⟨fmF hL'.1 wF, wF.2.2.2.1.trans hL'.2.1, gsi'.trans (by rw [zF.2.2.2.1, hL'.2.1]),
            wF.2.2.1.trans hL'.2.2.2⟩, wF.2.1.trans hb⟩
      -- from 287: `Delete (s, x, n)` at 295, back at 300
      have T287 : ∀ (x n : Nat) (Y' : State) (t'' : Nat), 1 ≤ n → j + 1 ≤ x + n → x + n ≤ ln W →
          KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W → Y'.cpu.rip = rdf_at.add 287 →
          Fm (aR g0.rsp) g0 Y'.cpu.gpr → Y'.cpu.gpr.r12 = g0.rdi → Y'.cpu.gpr.rbp = BitVec.ofNat 64 x →
          Y'.cpu.gpr.rbx = BitVec.ofNat 64 (4 * x) → Y'.cpu.gpr.r8 = BitVec.ofNat 64 n →
          GoG prof L o gev gP gE Y' t'' := by
        intro x n Y' t'' hn1 hn2 hn3 hKY' hAY' hrY' hm' h12 hbp hb h8
        refine (c_287 prof).run c hin (fun j' g' _ V' => j' = 295 ∧ V' = W ∧ Fr Y'.cpu.gpr g' ∧
            g'.rsi = BitVec.ofNat 64 x ∧ g'.rdx = BitVec.ofNat 64 n ∧ g'.rdi = Y'.cpu.gpr.r12) hKY' hAY' hrY'
          (vc_287 hbp h8 (by omega) (by omega) fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gF, gsi, gdx, gdi⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        have gs : U.cpu.gpr.rsp = aR g0.rsp := gF.1.trans hm'.1
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_295 _) hinD hD (by decide)
          (by rw [gs]; exact hr8) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        refine kd (295 + 5) U.cpu.gpr W x n gs (gdi.trans h12) gsi gdx hIW hn3 Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
        rintro Z W' t₃ hKZ hAZ hrZ hfr ⟨hIW', hln⟩
        have zF := frT gF hfr
        refine (c_300 prof).run c hin (fun j' g' _ V' => j' = 53 ∧ V' = W' ∧ Fr Z.cpu.gpr g' ∧
            g'.rsi = rdq(W', Z.cpu.gpr.r12)) hKZ hAZ hrZ
          (vc_300 (by rw [zF.2.2.2.1, h12]; exact fp) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gF', gsi'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        have wF := frT zF gF'
        have hlW' := hlb W' hIW'
        exact T53 x U₂ W' t₄ (by omega) (by omega) hIW' hKU₂ hAU₂ hrU₂
          ⟨⟨fmF hm' wF, wF.2.2.2.1.trans h12, gsi'.trans (by rw [zF.2.2.2.1, h12]), wF.2.2.1.trans hbp⟩,
            wF.2.1.trans hb⟩
      -- the scan back to the previous `/` at 253, by induction on the index
      have LM : ∀ (N m : Nat) (Y' : State) (t'' : Nat), m < N → m ≤ j → j + 2 ≤ ln W →
          KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W → Y'.cpu.rip = rdf_at.add 253 →
          Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 Y'.cpu.gpr → Y'.cpu.gpr.r8 = BitVec.ofNat 64 (j + 2) →
          Y'.cpu.gpr.rcx = BitVec.setWidth 64 (cr W g0.rdi (j + 2)) →
          Y'.cpu.gpr.rax = BitVec.ofNat 64 m + 18446744073709551615#64 → GoG prof L o gev gP gE Y' t'' := by
        intro N
        induction N with
        | zero => intro m Y' t'' hN; exact absurd hN (Nat.not_lt_zero _)
        | succ N ihM =>
          intro m Y' t'' hN hmj hj2 hKY' hAY' hrY' hL' h8 hcx hax'
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · refine (c_253 prof).run c hin (fun j' g' _ V' => j' = 266 ∧ V' = W ∧ Fr Y'.cpu.gpr g' ∧
                ∃ n, j + 2 ≤ n ∧ n ≤ j + 3 ∧ (n = j + 2 ∨ cr W g0.rdi (j + 2) ≠ 0) ∧ g'.r8 = BitVec.ofNat 64 n)
              hKY' hAY' hrY'
              (vc_253 hax' h8 hcx hL'.2.2.2 hmj (by omega) (fun h => absurd h (by omega))
                (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
                fun _ n a b d _ e f _ => ⟨rfl, rfl, e, n, a, b, d, f⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gF, n, hn1, hn2, hn3, g8⟩ U t₁ hKU hAU hrU hgU -
            subst V₁ hgU
            refine (c_266 prof).run c hin (fun j' g' _ V' => j' = 287 ∧ V' = W ∧ Fm (aR g0.rsp) g0 g' ∧
                g'.r12 = g0.rdi ∧ g'.rbp = BitVec.ofNat 64 0 ∧ g'.rbx = BitVec.ofNat 64 (4 * 0) ∧
                g'.r8 = BitVec.ofNat 64 n) hKU hAU hrU
              (vc_266 fun _ a b d e f r x y _ => ⟨rfl, rfl, fmE (fmF hL'.1 gF) a d e f,
                b.trans (gF.2.2.2.1.trans hL'.2.1), y.trans z4, x.trans z4, r.trans g8⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gm, g12, gbp, gbx, g8'⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
            subst V₁ hgU₂
            exact T287 0 n U₂ t₂ (by omega) (by omega)
              (hn3.elim (fun e => by omega) (fun e => by have := ltc (k := j + 2) (by omega) hzW e; omega))
              hKU₂ hAU₂ hrU₂ gm g12 gbp gbx g8'
          · refine (c_253 prof).run c hin (fun j' g' _ V' => V' = W ∧
                ((j' = 253 ∧ Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 g' ∧ g'.r8 = BitVec.ofNat 64 (j + 2) ∧
                  g'.rcx = BitVec.setWidth 64 (cr W g0.rdi (j + 2)) ∧
                  g'.rax = BitVec.ofNat 64 (m - 1) + 18446744073709551615#64) ∨
                 (j' = 287 ∧ Fm (aR g0.rsp) g0 g' ∧ g'.r12 = g0.rdi ∧ g'.rbp = BitVec.ofNat 64 (m - 1) ∧
                  g'.rbx = BitVec.ofNat 64 (4 * (m - 1)) ∧ g'.r8 = BitVec.ofNat 64 (j + 2 - (m - 1)))))
              hKY' hAY' hrY'
              (vc_253 hax' h8 hcx hL'.2.2.2 hmj (by omega)
                (fun _ => by rw [hL'.2.2.1]; exact fc W hIW (m - 1) (by omega))
                (fun _ _ a b d e f _ => ⟨rfl, Or.inl ⟨rfl, lbF hL' a (b.trans hL'.2.2.1), e.trans h8,
                  d.trans hcx, f⟩⟩)
                (fun _ _ a b d e f r x y _ => ⟨rfl, Or.inr ⟨rfl, fmE hL'.1 a d e f, b.trans hL'.2.1, r, x, y⟩⟩)
                (fun h => absurd h (by omega))) ?_
            rintro j' g fl V₁ ⟨hV₁, ⟨rfl, gL, g8, gcx, gax⟩ | ⟨rfl, gm, g12, gbp, gbx, g8⟩⟩ U t₁ hKU hAU hrU hgU -
            · subst V₁ hgU
              exact ihM (m - 1) U t₁ (by omega) (by omega) hj2 hKU hAU hrU gL g8 gcx gax
            · subst V₁ hgU
              exact T287 (m - 1) (j + 2 - (m - 1)) U t₁ (by omega) (by omega) (by omega) hKU hAU hrU gm g12 gbp
                gbx g8
      -- the scan back over `/` at 184, by induction on the index
      have LK : ∀ (N k : Nat) (Y' : State) (t'' : Nat), k < N → k + 2 ≤ j → j + 2 ≤ ln W →
          KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W → Y'.cpu.rip = rdf_at.add 184 →
          Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 Y'.cpu.gpr → Y'.cpu.gpr.r8 = BitVec.ofNat 64 (j + 2) →
          Y'.cpu.gpr.rcx = BitVec.setWidth 64 (cr W g0.rdi (j + 2)) → Y'.cpu.gpr.rdx = BitVec.ofNat 64 k →
          GoG prof L o gev gP gE Y' t'' := by
        intro N
        induction N with
        | zero => intro k Y' t'' hN; exact absurd hN (Nat.not_lt_zero _)
        | succ N ihK =>
          intro k Y' t'' hN hkj hj2 hKY' hAY' hrY' hL' h8 hcx hdx
          refine (c_184 prof).run c hin (fun j' g' _ V' => V' = W ∧ Fr Y'.cpu.gpr g' ∧
              ((j' = 253 ∧ g'.rsi = Y'.cpu.gpr.rsi ∧ g'.rcx = Y'.cpu.gpr.rcx ∧ g'.r8 = Y'.cpu.gpr.r8 ∧
                g'.rax = BitVec.ofNat 64 k + 18446744073709551615#64) ∨
               (j' = 184 ∧ 1 ≤ k ∧ g'.rsi = Y'.cpu.gpr.rsi ∧ g'.rcx = Y'.cpu.gpr.rcx ∧ g'.r8 = Y'.cpu.gpr.r8 ∧
                g'.rdx = BitVec.ofNat 64 (k - 1)) ∨ j' = 200)) hKY' hAY' hrY'
            (vc_184 hdx (by omega) (by rw [hL'.2.2.1]; exact fc W hIW k (by omega))
              (fun _ a b d e f _ => ⟨rfl, a, Or.inl ⟨rfl, b, d, e, f⟩⟩)
              (fun h _ a b d e f _ => ⟨rfl, a, Or.inr (Or.inl ⟨rfl, h, b, d, e, f⟩)⟩)
              (fun _ _ a _ => ⟨rfl, a, Or.inr (Or.inr rfl)⟩)) ?_
          rintro j' g fl V₁ ⟨hV₁, gF, ⟨rfl, gsi, gcx, g8, gax⟩ | ⟨rfl, hk1, gsi, gcx, g8, gdx⟩ | rfl⟩
            U t₁ hKU hAU hrU hgU -
          · subst V₁ hgU
            exact LM (k + 1) k U t₁ (Nat.lt_succ_self _) (by omega) hj2 hKU hAU hrU
              (lbF hL' gF (gsi.trans hL'.2.2.1)) (g8.trans h8) (gcx.trans hcx) gax
          · subst V₁ hgU
            exact ihK (k - 1) U t₁ (by omega) (by omega) hj2 hKU hAU hrU
              (lbF hL' gF (gsi.trans hL'.2.2.1)) (g8.trans h8) (gcx.trans hcx) gdx
          · subst V₁ hgU
            exact T200 U W t₁ hKU hAU hrU (fmF hL'.1 gF) hIW
      -- the head at 32
      refine (c_32 prof).run c hin (fun j' g' _ V' => V' = W ∧ Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 g' ∧
          g'.rdx = BitVec.ofNat 64 (j + 1) ∧ g'.rbx = BitVec.ofNat 64 (4 * (j + 1)) ∧
          (j' = 51 ∨ (j' = 93 ∧ g'.rcx = BitVec.ofNat 64 (j + 1)))) hKY hAY hrY
        (vc_32 hL hax (by omega) (fun h1 => fc W hIW (j - 1) (by omega))
          (fun _ a b d _ => ⟨rfl, a, b, d, Or.inl rfl⟩) (fun _ a b d e _ => ⟨rfl, a, d, e, Or.inr ⟨rfl, b⟩⟩)) ?_
      rintro j' g fl V₁ ⟨hV₁, gL, gdx, gbx, rfl | ⟨rfl, gcx⟩⟩ U t₁ hKU hAU hrU hgU -
      · subst V₁ hgU
        exact T51 U t₁ hKU hAU hrU gL gdx gbx
      · subst V₁ hgU
        refine (c_93 prof).run c hin (fun j' g' _ V' => V' = W ∧ Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) j g0 g' ∧
            ((j' = 51 ∧ g'.rdx = BitVec.ofNat 64 (j + 1) ∧ g'.rbx = BitVec.ofNat 64 (4 * (j + 1))) ∨
             (j' = 110 ∧ g'.rax = BitVec.setWidth 64 (cr W g0.rdi (j + 1))) ∨
             (j' = 170 ∧ cr W g0.rdi (j + 1) = 46#32 ∧ g'.r8 = BitVec.ofNat 64 (j + 2) ∧
              g'.rcx = BitVec.setWidth 64 (cr W g0.rdi (j + 2))))) hKU hAU hrU
          (vc_93 gL gcx gdx gbx (by omega) (fc W hIW (j + 1) (by omega))
            (fun h => fc W hIW (j + 2) (by have := ltc (k := j + 1) (by omega) hzW (n46 h); omega))
            (fun _ a b d _ => ⟨rfl, a, Or.inl ⟨rfl, b, d⟩⟩)
            (fun _ a b _ => ⟨rfl, a, Or.inr (Or.inl ⟨rfl, b⟩)⟩)
            (fun h _ a b d _ => ⟨rfl, a, Or.inr (Or.inr ⟨rfl, h, b, d⟩)⟩)) ?_
        rintro j' g fl V₁ ⟨hV₁, gL', ⟨rfl, gdx', gbx'⟩ | ⟨rfl, gax'⟩ | ⟨rfl, h46, g8, gcx'⟩⟩
          U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
        · subst V₁ hgU₂
          exact T51 U₂ t₂ hKU₂ hAU₂ hrU₂ gL' gdx' gbx'
        · subst V₁ hgU₂
          refine (c_110 prof).run c hin (fun j' g' _ V' => j' = 129 ∧ V' = W ∧ ∃ x n, 1 ≤ n ∧ j + 1 ≤ x + n ∧
              x + n ≤ ln W ∧ Lb (aR g0.rsp) g0.rdi rdq(W, g0.rdi) x g0 g' ∧ g'.rbx = BitVec.ofNat 64 (4 * x) ∧
              g'.rdx = BitVec.ofNat 64 n) hKU₂ hAU₂ hrU₂
            (vc_110 gL' gax' (by omega) fun x n a b d e _ f r s _ => ⟨rfl, rfl, x, n, a, b,
              e.elim (fun e => by omega) (fun e => by have := ltc (k := j + 1) (by omega) hzW e; omega), f, r, s⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, x, n, a, b, d, e, f, r⟩ U₃ t₃ hKU₃ hAU₃ hrU₃ hgU₃ -
          subst V₁ hgU₃
          exact T129 x n U₃ t₃ a b d hKU₃ hAU₃ hrU₃ e f r
        · subst V₁ hgU₂
          have hj2 : j + 2 ≤ ln W := by have := ltc (k := j + 1) (by omega) hzW (n46 h46); omega
          by_cases h2 : j < 2
          · refine (c_170 prof).run c hin (fun j' g' _ V' => j' = 200 ∧ V' = W ∧ Fr U₂.cpu.gpr g') hKU₂ hAU₂ hrU₂
              (vc_170 gL'.2.2.2 (by omega) (fun _ _ a _ => ⟨rfl, rfl, a⟩) (fun h => absurd h (by omega))) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gF⟩ U₃ t₃ hKU₃ hAU₃ hrU₃ hgU₃ -
            subst V₁ hgU₃
            exact T200 U₃ W t₃ hKU₃ hAU₃ hrU₃ (fmF gL'.1 gF) hIW
          · refine (c_170 prof).run c hin (fun j' g' _ V' => j' = 184 ∧ V' = W ∧ Fr U₂.cpu.gpr g' ∧
                g'.rdx = BitVec.ofNat 64 (j - 2) ∧ g'.rsi = U₂.cpu.gpr.rsi ∧ g'.rcx = U₂.cpu.gpr.rcx ∧
                g'.r8 = U₂.cpu.gpr.r8) hKU₂ hAU₂ hrU₂
              (vc_170 gL'.2.2.2 (by omega) (fun h => absurd h (by omega))
                (fun _ _ a b d e f _ => ⟨rfl, rfl, a, b, d, e, f⟩)) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gF, gdx'', gsi'', gcx'', g8''⟩ U₃ t₃ hKU₃ hAU₃ hrU₃ hgU₃ -
            subst V₁ hgU₃
            exact LK (j - 2 + 1) (j - 2) U₃ t₃ (Nat.lt_succ_self _) (by omega) hj2 hKU₃ hAU₃ hrU₃
              (lbF gL' gF (gsi''.trans gL'.2.2.1)) (g8''.trans g8) (gcx''.trans gcx') gdx''
  -- the entry
  have hrip' : X.cpu.rip = rdf_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hz0 : rdd(V, rdq(V, g0.rdi)) = 0
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 314 ∧ V' = V ∧ g'.rsp = g0.rsp ∧ KS g0 g') hK hA hrip'
      (by rw [hg0]; exact vc_0 fp fc0 hs1 hs2 hs3 (fun _ _ a b _ => ⟨rfl, rfl, a, b⟩) (fun h => absurd hz0 h)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gK⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_314 _) (by rw [gs]; exact hl) hin₂ h₂
      (by rw [gs]; exact hra) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr V Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [gs]
    · rw [hgZ']
      exact gK
  · have h0 : cr (V1 V g0) g0.rdi 0 ≠ 0 := fun e => hz0 (e1.symm.trans e)
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 32 ∧ V' = V1 V g0 ∧
        Lb (aR g0.rsp) g0.rdi rdq(V, g0.rdi) 0 g0 g' ∧ g'.rax = BitVec.setWidth 64 rdd(V, rdq(V, g0.rdi)))
      hK hA hrip'
      (by rw [hg0]; exact vc_0 fp fc0 hs1 hs2 hs3 (fun h => absurd h hz0) (fun _ _ a b _ => ⟨rfl, rfl, a, b⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gL, gax⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact LP (2 * ln (V1 V g0) + 1) 0 U (V1 V g0) t₁ (by omega) (ltc (Nat.zero_le _) (hz _ hI0) h0) hI0
      hKU hAU hrU (by rw [e0]; exact gL) (by rw [gax, e1])

end FV7z.Rdf
