import FV7z.Rdd.Scan
/-!
# `__readdir`: the loop over the buffer (PLAN.md §M, M1)

From 109 with the offset `k` in `rdx` and the size `n` in `rax`.

- `step109`: `k < n`: `vc_109l` to 80 (`r8 = k + 48`), then `z80` (`d_ino` 0, back to 109 past the entry) or `n80`.
- `scan`: by induction on `n - k` (each entry is at least 18 bytes), down to the state at 109 with `k = n`, which is
  given as `Hgd` (there the buffer is used up: `vc_109g` and `__getdents`, `rdd_gd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- At 109 with an entry left: to 80, then `z80` (back to 109, `ih`) or `n80` (the result). -/
theorem step109 {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {tr : List Event} {n k : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = rdd_at.add 109) (R : LR S p g0 n Y.cpu.gpr) (M : LM S p fb A g0 V₀ W n k)
    (hdx : Y.cpu.gpr.rdx.toNat = k) (hk : k < n) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev)
    (ih : ∀ (Y' : State) (W' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W' →
      Y'.cpu.rip = rdd_at.add 109 → LR S p g0 n Y'.cpu.gpr → LM S p fb A g0 V₀ W' n (k + rl W p k) →
      Dir W' p A 1#32 n (k + rl W p k) → Y'.cpu.gpr.rdx.toNat = k + rl W p k → GoG prof L o tr gP gE Y' t') :
    GoG prof L o tr gP gE Y t := by
  have hpA := C.hpA
  obtain ⟨_, hD⟩ := M.dir
  have hnA := hD.nA
  have hl : Y.cpu.gpr.rdx.toNat < Y.cpu.gpr.rax.toNat := by rw [hdx, R.ax]; exact hk
  refine (c_109 prof fb).run c hfs hin _ hK hA hrip (vc_109l (g := Y.cpu.gpr) hl) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have R₁ : LR S p g0 n Y₁.cpu.gpr := by
    rw [hg₁]
    exact ⟨R.sp, R.bx, R.bp, R.di, R.r15, R.ax⟩
  have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
  have hx : (Y.cpu.gpr.rdx + 48#64 + p).toNat = p.toNat + (48 + k) := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hdx, h48]
    omega
  have he : Y₁.cpu.gpr.r8 + Y₁.cpu.gpr.r14 = Addr.add p (48 + k) := by
    rw [hg₁]
    show Y.cpu.gpr.rdx + 48#64 + Y.cpu.gpr.r14 = _
    rw [R.di]
    exact Opd.fa (by omega) hx
  have hdx₁ : Y₁.cpu.gpr.rdx.toNat = k := by rw [hg₁]; exact hdx
  by_cases hz : rdq(W, Addr.add p (48 + k)) = 0#64
  · exact z80 c hfs hin C hK₁ hA₁ hr₁ R₁ M hk he hdx₁ hz ih
  · exact n80 c hfs hrs hin C hK₁ hA₁ hr₁ R₁ M hk he hdx₁ hz hT hmt0 hin₂ h₂ hra K

/-- The loop: from 109 at any offset `k ≤ n` of the chain, given the state at 109 with the buffer used up. -/
theorem scan {g0 : Gprs} {V₀ : Addr → Byte} {tr : List Event} {n : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev)
    (Hgd : ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = rdd_at.add 109 → LR S p g0 n Y.cpu.gpr → LM S p fb A g0 V₀ W n n →
      Dir W p A 1#32 n n → Y.cpu.gpr.rdx.toNat = n → GoG prof L o tr gP gE Y t) :
    ∀ (m k : Nat) (Y : State) (W : Addr → Byte) (t : Nat), n - k ≤ m → k ≤ n → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = rdd_at.add 109 → LR S p g0 n Y.cpu.gpr →
      LM S p fb A g0 V₀ W n k → Dir W p A 1#32 n k → Y.cpu.gpr.rdx.toNat = k → GoG prof L o tr gP gE Y t := by
  intro m
  induction m with
  | zero =>
    intro k Y W t hm hkn hK hA hr R M hD hdx
    obtain rfl : k = n := by omega
    exact Hgd Y W t hK hA hr R M hD hdx
  | succ m ih =>
    intro k Y W t hm hkn hK hA hr R M hD hdx
    by_cases hk : k < n
    · obtain ⟨⟨h18, -⟩, hrl, -⟩ := M.ch.inv hk
      exact step109 c hfs hrs hin C hK hA hr R M hdx hk hT hmt0 hin₂ h₂ hra K
        fun Y' W' t' hK' hA' hr' R' M' hD' hdx' =>
          ih (k + rl W p k) Y' W' t' (by omega) hrl hK' hA' hr' R' M' hD' hdx'
    · obtain rfl : k = n := by omega
      exact Hgd Y W t hK hA hr R M hD hdx

end FV7z.Rdd
