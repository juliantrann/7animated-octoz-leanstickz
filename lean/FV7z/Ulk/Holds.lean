import FV7z.Ulk.Vc
import FV7z.Cxa.Holds
/-!
# `unlink_chunk` takes a chunk out of its bin (PLAN.md §M, M1)

glibc 2.31's `unlink_chunk (av, p)` at `0x62ea20` in `7zzs` (`av` dropped by IPA-SRA: `rdi = p`): the chunk's size
`sz` (at `p + 8`) checked against the next chunk's `prev_size`, `fd->bk == p` and `bk->fd == p` checked, then
`fd->bk = bk`, `bk->fd = fd`; for a large chunk (`sz` over 0x3ff) with `fd_nextsize` set, `p` also out of the
`nextsize` list after its checks (`p->fd_nextsize->bk_nextsize == p`, `p->bk_nextsize->fd_nextsize == p`). A failed
check calls `malloc_printerr` (it does not return): here the checks are hypotheses (`UlkPre`), so the run does not
go there.

- `usz`, `ufd`, `ubk`, `uV1`, `ufdn`, `ubkn`, …: the words the code reads, each in the bytes as they are then;
  `ulkV`: the bytes when it returns, as glibc's C says (`unlink_chunk`), the stores in their order.
- `UlkPre`: the checks hold, the words read are in the footprint, the words written in the run's.
- `ulk_ok`: from the entry to the return address, the bytes `ulkV`, `rdi` and the registers a call keeps as at the
  entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ulk

/-! ## What the code reads and writes -/

/-- The size word. -/
def usz (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 8#64)
/-- `fd`. -/
def ufd (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 16#64)
/-- `bk`. -/
def ubk (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 24#64)
/-- The bytes after `fd->bk = bk`, `bk->fd = fd`. -/
def uV1 (V : Addr → Byte) (p : Addr) : Addr → Byte := ulk1 V (ufd V p) (ubk V p)
/-- `fd_nextsize`, then. -/
def ufdn (V : Addr → Byte) (p : Addr) : Addr := rdq(uV1 V p, p + 32#64)
/-- `bk_nextsize`, then. -/
def ubkn (V : Addr → Byte) (p : Addr) : Addr := rdq(uV1 V p, p + 40#64)
/-- `fd->fd_nextsize`, then. -/
def uff (V : Addr → Byte) (p : Addr) : Addr := rdq(uV1 V p, ufd V p + 32#64)
/-- `fd->fd_nextsize` set: after `p->fd_nextsize->bk_nextsize = p->bk_nextsize`. -/
def uVa (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (uV1 V p) (ufdn V p + 40#64) (toBytesLE (ubkn V p) 8)
/-- `p->bk_nextsize`, then. -/
def uqa (V : Addr → Byte) (p : Addr) : Addr := rdq(uVa V p, p + 40#64)
/-- `fd->fd_nextsize` null: after `fd->fd_nextsize = p->fd_nextsize`, `fd->bk_nextsize = p->bk_nextsize`. -/
def uVc (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (uV1 V p) (ufd V p + 32#64) (toBytesLE (ubkn V p ++ ufdn V p) 16)
/-- `p->fd_nextsize`, then. -/
def uac (V : Addr → Byte) (p : Addr) : Addr := rdq(uVc V p, p + 32#64)
/-- After `p->fd_nextsize->bk_nextsize = fd`. -/
def uVc2 (V : Addr → Byte) (p : Addr) : Addr → Byte := Vst (uVc V p) (uac V p + 40#64) (toBytesLE (ufd V p) 8)
/-- `p->bk_nextsize`, then. -/
def ubc (V : Addr → Byte) (p : Addr) : Addr := rdq(uVc2 V p, p + 40#64)

/-- The bytes when `unlink_chunk (av, p)` returns. -/
def ulkV (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  if (usz V p).toNat ≤ 1023 ∨ ufdn V p = 0#64 then uV1 V p
  else if uff V p ≠ 0#64 then Vst (uVa V p) (uqa V p + 32#64) (toBytesLE (ufdn V p) 8)
  else if p = ufdn V p then Vst (uV1 V p) (ufd V p + 32#64) (toBytesLE (ufd V p ++ ufd V p) 16)
  else Vst (uVc2 V p) (ubc V p + 32#64) (toBytesLE (ufd V p) 8)

/-- What a large chunk in the `nextsize` list needs: the checks, the words read, the words written. -/
structure UlkLg (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (p : Addr) : Prop where
  c4 : rdq(uV1 V p, ufdn V p + 40#64) = p
  c5 : rdq(uV1 V p, ubkn V p + 32#64) = p
  g2 : ∀ i < 8, Foot F.data (Addr.add (ufdn V p + 40#64) i)
  g3 : ∀ i < 8, Foot F.data (Addr.add (p + 40#64) i)
  g4 : ∀ i < 8, Foot F.data (Addr.add (ubkn V p + 32#64) i)
  g5 : ∀ i < 8, Foot F.data (Addr.add (ufd V p + 32#64) i)
  wa : uff V p ≠ 0#64 → (∀ i < 8, Foot Wl (Addr.add (ufdn V p + 40#64) i)) ∧
    ∀ i < 8, Foot Wl (Addr.add (uqa V p + 32#64) i)
  wb : uff V p = 0#64 → ∀ i < 16, Foot Wl ((ufd V p + 32#64).add i)
  wc : uff V p = 0#64 → p ≠ ufdn V p → (∀ i < 8, Foot Wl (Addr.add (uac V p + 40#64) i)) ∧
    ∀ i < 8, Foot Wl (Addr.add (ubc V p + 32#64) i)

/-- What `unlink_chunk (av, p)` needs: the checks hold, the words read are in the footprint, the words written in
the run's. -/
structure UlkPre (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (p : Addr) : Prop where
  c1 : rdq(V, p + (usz V p &&& 18446744073709551608#64)) = usz V p &&& 18446744073709551608#64
  c2 : rdq(V, ufd V p + 24#64) = p
  c3 : rdq(V, ubk V p + 16#64) = p
  f1 : ∀ i < 8, Foot F.data (Addr.add (p + 8#64) i)
  f2 : ∀ i < 8, Foot F.data (Addr.add (p + (usz V p &&& 18446744073709551608#64)) i)
  f3 : ∀ i < 8, Foot F.data (Addr.add (p + 16#64) i)
  f4 : ∀ i < 8, Foot F.data (Addr.add (p + 24#64) i)
  f5 : ∀ i < 8, Foot F.data (Addr.add (ufd V p + 24#64) i)
  f6 : ∀ i < 8, Foot F.data (Addr.add (ubk V p + 16#64) i)
  w1 : ∀ i < 8, Foot Wl (Addr.add (ufd V p + 24#64) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (ubk V p + 16#64) i)
  f7 : 1023 < (usz V p).toNat → ∀ i < 8, Foot F.data (Addr.add (p + 32#64) i)
  lg : 1023 < (usz V p).toNat → ufdn V p ≠ 0#64 → UlkLg F Wl V p

/-! ## The run -/

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- `unlink_chunk (av, p)` (`rdi = p`) when the checks hold (`UlkPre`): the run reaches the return address at
`rsp` (`hra`, read in the bytes at the end) with the bytes `ulkV`, `rsp` past it, `rdi` and the registers a call
keeps as at the entry. -/
theorem ulk_ok {fb : Addr} {X : State} {t : Nat} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L ulk_at ulk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ulk_at)
    (hP : UlkPre F Wl V X.cpu.gpr.rdi) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(ulkV V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (ulkV V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Kp X.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨c1, c2, c3, f1, f2, f3, f4, f5, f6, w1, w2, f7, hlg⟩ := hP
  -- from 106: the frame given back, the `ret`
  have k106 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (ulkV V X.cpu.gpr.rdi) →
      Y.cpu.rip = ulk_at.add 106 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 → Kp X.cpu.gpr Y.cpu.gpr →
      GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hspY hkY
    refine (c_106 prof fb).run c hfs hin _ hKY hAY hrY vc_106 ?_
    rintro j' g₉ fl V' ⟨rfl, hVV, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
    subst V'
    have hsp₉ : Y₉.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      rw [hg₉]; show Y.cpu.gpr.rsp + 8#64 = _; rw [hspY]; exact BitVec.sub_add_cancel _ _
    refine c.s_ret hK₉ hA₉ hin (lt_len (by decide)) hr₉ (ret_110 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
    · rw [hsp₉]; exact hl i hi
    · rw [hsp₉]; exact hra
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hkY
    refine k Z t' hKZ hAZ hrZ (by rw [hgZ]; show Y₉.cpu.gpr.rsp + 8 = _; rw [hsp₉]) ?_
    rw [hgZ, hg₉]
    exact ⟨k1, k2, k3, k4, k5, k6, k7⟩
  have hsz : rdq(V, X.cpu.gpr.rdi + 8#64) = usz V X.cpu.gpr.rdi := rfl
  have hfd : rdq(V, X.cpu.gpr.rdi + 16#64) = ufd V X.cpu.gpr.rdi := rfl
  have hbk : rdq(V, X.cpu.gpr.rdi + 24#64) = ubk V X.cpu.gpr.rdi := rfl
  have hrp : X.cpu.rip = ulk_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hsm : (usz V X.cpu.gpr.rdi).toNat ≤ 1023 ∨ ufdn V X.cpu.gpr.rdi = 0#64
  · -- small, or no `fd_nextsize`
    have hV : ulkV V X.cpu.gpr.rdi = uV1 V X.cpu.gpr.rdi := by unfold ulkV; rw [if_pos hsm]
    refine (c_0 prof fb).run c hfs hin _ hK hA hrp
      (vc_0s hsz c1 hfd hbk c2 c3 hsm f1 f2 f3 f4 f5 f6 w1 w2 f7) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hsp, hkp⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    exact k106 Y₁ t₁ hK₁ (by rw [hV]; exact hA₁) hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact hkp)
  have hlg' : 1023 < (usz V X.cpu.gpr.rdi).toNat := by omega
  have hn0 : ufdn V X.cpu.gpr.rdi ≠ 0#64 := fun h => hsm (.inr h)
  obtain ⟨c4, c5, g2, g3, g4, g5, wa, wb, wc⟩ := hlg hlg' hn0
  have hL : Lg F V X.cpu.gpr.rdi (ufd V X.cpu.gpr.rdi) (ubk V X.cpu.gpr.rdi) (ufdn V X.cpu.gpr.rdi)
      (ubkn V X.cpu.gpr.rdi) :=
    ⟨rfl, by simp only [beq_eq_false_iff_ne]; exact hn0, c4, rfl, c5, f7 hlg', g2, g3, g4, g5⟩
  by_cases hff : uff V X.cpu.gpr.rdi ≠ 0#64
  · -- `fd->fd_nextsize` set
    have hV : ulkV V X.cpu.gpr.rdi = Vst (uVa V X.cpu.gpr.rdi) (uqa V X.cpu.gpr.rdi + 32#64)
        (toBytesLE (ufdn V X.cpu.gpr.rdi) 8) := by unfold ulkV; rw [if_neg hsm, if_pos hff]
    obtain ⟨w3, w4⟩ := wa hff
    refine (c_0 prof fb).run c hfs hin _ hK hA hrp
      (vc_0a (q := uqa V X.cpu.gpr.rdi) hsz c1 hfd hbk c2 c3 hlg' hL hff rfl f1 f2 f3 f4 f5 f6 w1 w2 w3 w4) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hsp, hkp⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    exact k106 Y₁ t₁ hK₁ (by rw [hV]; exact hA₁) hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact hkp)
  have hff0 : uff V X.cpu.gpr.rdi = 0#64 := Classical.not_not.1 hff
  have w5 := wb hff0
  by_cases hpe : X.cpu.gpr.rdi = ufdn V X.cpu.gpr.rdi
  · -- `p` alone in the `nextsize` list: `fd`'s links to `fd`
    have hV : ulkV V X.cpu.gpr.rdi = Vst (uV1 V X.cpu.gpr.rdi) (ufd V X.cpu.gpr.rdi + 32#64)
        (toBytesLE (ufd V X.cpu.gpr.rdi ++ ufd V X.cpu.gpr.rdi) 16) := by
      unfold ulkV; rw [if_neg hsm, if_neg hff, if_pos hpe]
    refine (c_0 prof fb).run c hfs hin _ hK hA hrp
      (vc_0b hsz c1 hfd hbk c2 c3 hlg' hL hff0 hpe f1 f2 f3 f4 f5 f6 w1 w2) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hax, hsp, hkp⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    refine c.s_movq_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (mq_176 _) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
    refine c.s_punpcklqdq hK₂ hA₂ hin (lt_len (by decide)) hr₂ (pu_181 _) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hx₃, -⟩
    have hg₃' : Y₃.cpu.gpr = g₁ := hg₃.trans (hg₂.trans hg₁)
    have hea : eaD Y₃ 0 32 = ufd V X.cpu.gpr.rdi + 32#64 := by
      show Y₃.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 32 = _
      rw [hg₃']; show g₁.rax + _ = _; rw [hax] <;> rfl
    have hxv : xlo Y₃ 0 = ufd V X.cpu.gpr.rdi ++ ufd V X.cpu.gpr.rdi := by
      have h1 : Y₁.cpu.gpr.get (regOf 0) = ufd V X.cpu.gpr.rdi := by rw [hg₁]; exact hax
      rw [hx₃, hx₂]
      show lane 64 ((Y₁.cpu.gpr.get (regOf 0)).setWidth 64 |>.setWidth 128) 0 ++
        lane 64 ((Y₁.cpu.gpr.get (regOf 0)).setWidth 64 |>.setWidth 128) 0 =
        ufd V X.cpu.gpr.rdi ++ ufd V X.cpu.gpr.rdi
      rw [h1, BitVec.setWidth_eq, Cxa.lane_lo]
    refine c.s_movups_stv hK₃ hA₃ hin (lt_len (by decide)) hr₃ (mv_185 _) (by rw [hea]; exact w5) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, -⟩
    rw [hea, hxv] at hA₄
    refine (c_189 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ vc_189 ?_
    rintro j' g₅ fl V' ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    have hg₅' : Y₅.cpu.gpr = g₁ := hg₅.trans (hg₄.trans hg₃')
    exact k106 Y₅ t₅ hK₅ (by rw [hV]; exact hA₅) hr₅ (by rw [hg₅']; exact hsp) (by rw [hg₅']; exact hkp)
  · -- `fd` takes `p`'s place in the `nextsize` list
    obtain ⟨w6, w7⟩ := wc hff0 hpe
    have hV : ulkV V X.cpu.gpr.rdi = Vst (uVc2 V X.cpu.gpr.rdi) (ubc V X.cpu.gpr.rdi + 32#64)
        (toBytesLE (ufd V X.cpu.gpr.rdi) 8) := by
      unfold ulkV; rw [if_neg hsm, if_neg hff, if_neg hpe]
    refine (c_0 prof fb).run c hfs hin _ hK hA hrp
      (vc_0c hsz c1 hfd hbk c2 c3 hlg' hL hff0 hpe f1 f2 f3 f4 f5 f6 w1 w2) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hax, hdx, hcx, hsp, hkp⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    refine c.s_movq_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (mq_117 _) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
    refine c.s_movq_rx hK₂ hA₂ hin (lt_len (by decide)) hr₂ (mq_122 _) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hx₃, hk₃⟩
    refine c.s_punpcklqdq hK₃ hA₃ hin (lt_len (by decide)) hr₃ (pu_127 _) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hx₄, -⟩
    have hg₄' : Y₄.cpu.gpr = g₁ := hg₄.trans (hg₃.trans (hg₂.trans hg₁))
    have hea : eaD Y₄ 0 32 = ufd V X.cpu.gpr.rdi + 32#64 := by
      show Y₄.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 32 = _
      rw [hg₄']; show g₁.rax + _ = _; rw [hax] <;> rfl
    have hxv : xlo Y₄ 0 = ubkn V X.cpu.gpr.rdi ++ ufdn V X.cpu.gpr.rdi := by
      have h1 : Y₂.cpu.gpr.get (regOf 1) = ubkn V X.cpu.gpr.rdi := by rw [hg₂, hg₁]; exact hcx
      have h2 : Y₁.cpu.gpr.get (regOf 2) = ufdn V X.cpu.gpr.rdi := by rw [hg₁]; exact hdx
      rw [hx₄, hx₃, hk₃ 0 (by decide), hx₂]
      show lane 64 ((Y₂.cpu.gpr.get (regOf 1)).setWidth 64 |>.setWidth 128) 0 ++
        lane 64 ((Y₁.cpu.gpr.get (regOf 2)).setWidth 64 |>.setWidth 128) 0 =
        ubkn V X.cpu.gpr.rdi ++ ufdn V X.cpu.gpr.rdi
      rw [h1, h2, BitVec.setWidth_eq, BitVec.setWidth_eq, Cxa.lane_lo, Cxa.lane_lo]
    refine c.s_movups_stv hK₄ hA₄ hin (lt_len (by decide)) hr₄ (mv_131 _) (by rw [hea]; exact w5) ?_
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, -⟩
    rw [hea, hxv] at hA₅
    have hg₅' : Y₅.cpu.gpr = g₁ := hg₅.trans hg₄'
    have hdi : Y₅.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₅']; exact hkp.1
    have hra5 : Y₅.cpu.gpr.rax = ufd V X.cpu.gpr.rdi := by rw [hg₅']; exact hax
    refine (c_135 prof fb).run c hfs hin _ hK₅ hA₅ hr₅
      (vc_135 (a := uac V X.cpu.gpr.rdi) (b := ubc V X.cpu.gpr.rdi) (by rw [hdi]; rfl)
        (by rw [hdi, hra5]; rfl) (by rw [hdi]; exact f7 hlg') (by rw [hdi]; exact g3) w6 w7)
      ?_
    rintro j' g₆ fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
    rw [hra5] at hA₆
    exact k106 Y₆ t₆ hK₆ (by rw [hV]; exact hA₆) hr₆
      (by rw [hg₆]; show Y₅.cpu.gpr.rsp = _; rw [hg₅']; exact hsp)
      (by rw [hg₆]; show Kp X.cpu.gpr Y₅.cpu.gpr; rw [hg₅']; exact hkp)

end

end FV7z.Ulk
