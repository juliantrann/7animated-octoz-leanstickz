import FV7z.Rdd.Gd
import FV7z.Rdd.Scan
/-!
# `__readdir`: after `__getdents` returns (PLAN.md §M, M1)

The ways from 133 (the return address of the `call __getdents`), the registers of the loop kept by the call.

- `at162`: `errno` stored back (`vc_162`), then `fin176` with `RS` left (`NULL`).
- `gd_err`: `rax` -1: `vc_133e` (`errno` `ENOENT`) then `at162`, or `vc_133o` then `fin176`.
- `gd_zero`: `rax` 0 (the end of the directory): `vc_133z` then `at162`.
- `gd_pos`: `rax` the size of the entries: `vc_133p` (the size stored, the offset 0), then `n80` at `k = 0`
  (`ch_dn`, the first entry's `d_ino` by `ino_dn`, not 0 by `NzIno`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- At 162: `errno` stored back, then the end with `NULL`. -/
theorem at162 {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {tr : List Event} {n : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = rdd_at.add 162) (hsp : Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8) (h14 : Y.cpu.gpr.r14 = p)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hbp : Y.cpu.gpr.rbp = 18446744073709551544#64) (hsv : RSv S g0 W)
    (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n n) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Y t := by
  refine (c_162 prof fb).run c hfs hin _ hK hA hrip (vc_162 (g := Y.cpu.gpr) hbp C.fe) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have eS := C.eS
  have eD := C.eD
  have hfe := C.hfe
  obtain ⟨s1, r1, d1⟩ := gst (g0 := g0) (V₀ := V₀) (errnoAt fb) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.r13) 4)
    C (by rw [toBytesLE_length]; exact hfe) (by rw [toBytesLE_length]; omega)
    (fun x x1 x2 => Or.inr (Or.inr ⟨x1, by rw [toBytesLE_length] at x2; exact x2⟩))
    (by rw [toBytesLE_length]; omega) hsv hfr hD
  exact fin176 c hfs hrs hin C hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h14)
    (by rw [hg₁]; exact h15) s1 r1 d1 (Or.inl ⟨by rw [hg₁]; try rfl, rfl⟩) hT hmt0 hin₂ h₂ hra K

/-- At 133, `rax` -1 (an error): `errno` `ENOENT` goes back to its value before, then the end with `NULL`. -/
theorem gd_err {g0 : Gprs} {V₀ W : Addr → Byte} {Z : State} {t : Nat} {tr : List Event} {n : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem W)
    (hrip : Z.cpu.rip = rdd_at.add 133) (hsp : Z.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8) (h14 : Z.cpu.gpr.r14 = p)
    (h15 : Z.cpu.gpr.r15 = g0.r15) (hbp : Z.cpu.gpr.rbp = 18446744073709551544#64)
    (hax : Z.cpu.gpr.rax = 18446744073709551615#64) (hsv : RSv S g0 W)
    (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n n) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Z t := by
  have hs : Z.cpu.gpr.rax.msb = true := by rw [hax]; decide
  have fe' : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i) := fun i hi => c.hws _ (C.fe i hi)
  by_cases he : rdd(W, errnoAt fb) = 2#32
  · refine (c_133 prof fb).run c hfs hin _ hK hA hrip (vc_133e (g := Z.cpu.gpr) hs hbp he fe') ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact at162 c hfs hrs hin C hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h14)
      (by rw [hg₁]; exact h15) (by rw [hg₁]; exact hbp) hsv hfr hD hT hmt0 hin₂ h₂ hra K
  · refine (c_133 prof fb).run c hfs hin _ hK hA hrip (vc_133o (g := Z.cpu.gpr) hs hbp he fe') ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact fin176 c hfs hrs hin C hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h14)
      (by rw [hg₁]; exact h15) hsv hfr hD (Or.inl ⟨by rw [hg₁]; try rfl, rfl⟩) hT hmt0 hin₂ h₂ hra K

/-- At 133, `rax` 0 (no entries left): to 162. -/
theorem gd_zero {g0 : Gprs} {V₀ W : Addr → Byte} {Z : State} {t : Nat} {tr : List Event} {n : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem W)
    (hrip : Z.cpu.rip = rdd_at.add 133) (hsp : Z.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8) (h14 : Z.cpu.gpr.r14 = p)
    (h15 : Z.cpu.gpr.r15 = g0.r15) (hbp : Z.cpu.gpr.rbp = 18446744073709551544#64)
    (hax : Z.cpu.gpr.rax = 0#64) (hsv : RSv S g0 W)
    (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n n) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Z t := by
  refine (c_133 prof fb).run c hfs hin _ hK hA hrip (vc_133z (g := Z.cpu.gpr) hax) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  exact at162 c hfs hrs hin C hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h14)
    (by rw [hg₁]; exact h15) (by rw [hg₁]; exact hbp) hsv hfr hD hT hmt0 hin₂ h₂ hra K

/-- At 133, `rax` the size of the entries `getdents64` wrote at `p + 48`: the size stored, then the first entry. -/
theorem gd_pos {g0 : Gprs} {V₀ W W₁ : Addr → Byte} {Z : State} {t : Nat} {tr : List Event} {n' k' : Nat}
    {r : DnOut} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem W)
    (hrip : Z.cpu.rip = rdd_at.add 133) (hsp : Z.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8) (h14 : Z.cpu.gpr.r14 = p)
    (h15 : Z.cpu.gpr.r15 = g0.r15) (hbp : Z.cpu.gpr.rbp = 18446744073709551544#64) (hbx : Z.cpu.gpr.rbx = p + 48#64)
    (hW : W = Vst W₁ (p.add 48) (dnBuf W₁ (p.add 48) A r)) (hs : (r.es.map Dirent.reclen).sum ≤ A)
    (hpos : 0 < (r.es.map Dirent.reclen).sum) (hni : ∀ e ∈ r.es, e.ino ≠ 0#64)
    (hax : Z.cpu.gpr.rax = BitVec.ofNat 64 (r.es.map Dirent.reclen).sum) (hsv : RSv S g0 W)
    (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n' k') (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Z t := by
  have hpA := C.hpA
  have hA31 := C.hA
  have hsN : (BitVec.ofNat 64 (r.es.map Dirent.reclen).sum).toNat = (r.es.map Dirent.reclen).sum := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hz : Z.cpu.gpr.rax ≠ 0#64 := fun h => by
    have h2 := congrArg BitVec.toNat (hax.symm.trans h)
    have h3 : (0#64 : BitVec 64).toNat = 0 := rfl
    rw [hsN] at h2
    omega
  have hsm : Z.cpu.gpr.rax.msb = false := by
    rw [BitVec.msb_eq_decide, hax, hsN]
    exact decide_eq_false (by omega)
  have t4 : (p + 4#64).toNat = p.toNat + 4 := Opd.tAdd p 4 (by omega)
  have t8 : (p + 8#64).toNat = p.toNat + 8 := Opd.tAdd p 8 (by omega)
  have t16 : (p + 16#64).toNat = p.toNat + 16 := Opd.tAdd p 16 (by omega)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  have t48 : (p.add 48).toNat = p.toNat + 48 := tna p 48 (by omega)
  have w16 : ∀ i < 8, Foot Wl (Addr.add (Z.cpu.gpr.r14 + 16#64) i) := by
    rw [h14]; exact Opd.frw C.pw (Opd.fa (B := p) (d := 16) (by omega) t16) (by omega)
  refine (c_133 prof fb).run c hfs hin _ hK hA hrip (vc_133p (g := Z.cpu.gpr) hz hsm w16) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  rw [h14] at hA₁
  have hl8 : (toBytesLE Z.cpu.gpr.rax 8).length = 8 := toBytesLE_length _ _
  obtain ⟨s1, r1, b1⟩ := dst (g0 := g0) (V₀ := V₀) (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8) C (by omega)
    (by rw [hl8]; omega) hsv hfr
  have hal : (p + 16#64).toNat + (toBytesLE Z.cpu.gpr.rax 8).length ≤ 2 ^ 64 := by rw [hl8]; omega
  have d1 : Dir (Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8)) p A 1#32 (r.es.map Dirent.reclen).sum
      (rdq(Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8), p + 24#64)).toNat := by
    refine ⟨?_, ?_, ?_, hs, rfl⟩
    · rw [rd_Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8) (p + 4#64) 4 hal (by omega) (by omega)]; exact hD.lk
    · rw [rd_Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8) (p + 8#64) 8 hal (by omega) (by omega)]; exact hD.al
    · rw [rd_Vst_self W (p + 16#64) _ hl8 (by omega), ofBytesLE_toBytesLE (by decide), hax, hsN]
  have hch : Ch W p (r.es.map Dirent.reclen).sum 0 := by
    rw [hW]; exact ch_dn W₁ (by omega) hs
  have R₁ : LR S p g0 (r.es.map Dirent.reclen).sum Y₁.cpu.gpr := by
    rw [hg₁]
    exact ⟨hsp, hbx, hbp, h14, h15, by show Z.cpu.gpr.rax.toNat = _; rw [hax, hsN]⟩
  have he : Y₁.cpu.gpr.r8 + Y₁.cpu.gpr.r14 = Addr.add p (48 + 0) := by
    rw [hg₁]
    show 48#64 + Z.cpu.gpr.r14 = _
    rw [h14, BitVec.add_comm]
    exact Opd.fa (by omega) (by rw [Opd.tAdd p 48 (by omega)])
  have hdx : Y₁.cpu.gpr.rdx.toNat = 0 := by rw [hg₁]; try rfl
  -- the first entry is at least 24 bytes, so its `d_ino` lies in the buffer
  have h8 : 8 ≤ (r.es.map Dirent.reclen).sum := by
    cases hr : r.es with
    | nil => rw [hr] at hpos; simp at hpos
    | cons e es =>
      have := reclen_ge e
      simp only [List.map_cons, List.sum_cons]
      omega
  have hnz : rdq(Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8), Addr.add p (48 + 0)) ≠ 0#64 := by
    show rdq(Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8), p.add 48) ≠ 0#64
    rw [rd_Vst W (p + 16#64) (toBytesLE Z.cpu.gpr.rax 8) (p.add 48) 8 hal (by omega) (by omega), hW,
      ← dn_one (V := W₁) (a := p.add 48) hs (by omega)]
    show rdq(vRuns W₁ (p.add 48) (direntRuns r.es 0), p.add 48) ≠ 0#64
    cases hr : r.es with
    | nil => rw [hr] at hpos; simp at hpos
    | cons e es =>
      rw [hr] at hs
      rw [ino_dn (p := p) (N := A) (by omega) W₁ e es hs]
      exact hni e (by rw [hr]; exact List.mem_cons_self ..)
  exact n80 c hfs hrs hin C hK₁ hA₁ hr₁ R₁ ⟨s1, r1, ⟨_, d1⟩, Ch.congr (fun i hi => b1 i (by omega)) hch⟩
    hpos he hdx hnz hT hmt0 hin₂ h₂ hra K

end FV7z.Rdd
