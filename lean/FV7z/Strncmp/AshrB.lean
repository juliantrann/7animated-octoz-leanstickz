import FV7z.Strncmp.AshrI
/-!
# The shifted loops of `__strncmp_sse2`: a round's 16 bytes (PLAN.md G3, `strncmp`)

In the loop shifting by `k`, at `rcx = K`, `rsi + K` holds the 16 bytes at byte `u` of `y` (`rsi`'s string) and
`rdi + K` those at byte `u + 16 - k` of `x`; `xmm3` holds, from its byte `k` on, the bytes of `x` from `u` on (the
16 before `rdi + K`). A round (`bodyS`, at `138` and at `218`) loads both, lines `x`'s up with `y`'s
(`psrldq xmm3, k; pslldq xmm2, 16 - k; por xmm2, xmm3`, `lane_align`), keeps `rdi`'s in `xmm4`, and compares as
`ashr_0` does: a stop leaves by `6160`, `sub r11, 16; jbe` returns 0 when no more are to be compared. `AtB` is what
holds at a round: with `r10` the place in their page of `rdi + K`, and that page to read.

- `same_lanes`: the bytes the same up to a stop in 16 bytes.
- `same_ab`, `foot_of`: the strings in order; a byte with none 0 before it, to read.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem same_ab {V : Addr → Byte} {a b x y : Addr} {sw : Bool} {m : Nat}
    (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a) (h : Same V x y m) : Same V a b m := by
  rcases hxy with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · exact h
  · exact h.comm

theorem foot_of {F : Footprint} {V : Addr → Byte} {a : Addr} {n u : Nat} (hp : Str.StrPg F V a n) (hu : u < n)
    (hnz : ∀ i < u, V (a.add i) ≠ 0) : Foot F.data (a.add u) :=
  pg_of hp hu hnz _ rfl

/-- 16 bytes `Yb` of `y` and `Xc` of `x` from `u`, the same and not 0 below `p`: the strings the same to `u + p`. -/
theorem same_lanes {V : Addr → Byte} {x y : Addr} {u p : Nat} {Yb Xc : BitVec 128} (hs : Same V x y u)
    (hY : ∀ j < 16, lane 8 Yb j = V (y.add (u + j))) (hX : ∀ j < 16, lane 8 Xc j = V (x.add (u + j)))
    (ht : ∀ i < p, lane 8 Yb i = lane 8 Xc i ∧ lane 8 Yb i ≠ 0) (hp : p ≤ 16) : Same V x y (u + p) := by
  intro i hi
  by_cases hiu : i < u
  · exact hs i hiu
  · have h := ht (i - u) (by omega)
    rw [hY _ (by omega), hX _ (by omega), show u + (i - u) = i by omega] at h
    exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩

/-- At a round of the loop shifting by `k`, at `rcx = K`: see the module doc. -/
structure AtB (g₀ : Gprs) (Y : State) (F : Footprint) (V : Addr → Byte) (x y : Addr) (sw : Bool)
    (n k u K : Nat) : Prop where
  kp : KpN g₀ Y.cpu.gpr
  di : Addr.add Y.cpu.gpr.rdi K = x.add (u + 16 - k)
  si : Addr.add Y.cpu.gpr.rsi K = y.add u
  cx : Y.cpu.gpr.rcx = BitVec.ofNat 64 K
  r9 : Y.cpu.gpr.r9 = BitVec.ofNat 64 k
  r8 : Y.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0
  r11 : Y.cpu.gpr.r11 = BitVec.ofNat 64 (n - u)
  r10 : Y.cpu.gpr.r10 = BitVec.ofNat 64 (2 ^ 64 - 4096 + (Addr.add Y.cpu.gpr.rdi K).toNat % 4096 + k)
  K16 : 16 ≤ K
  di16 : (Addr.add Y.cpu.gpr.rdi K).toNat % 16 = 0
  si16 : (Addr.add Y.cpu.gpr.rsi K).toNat % 16 = 0
  pg : ∀ z : Addr, z.toNat / 4096 = (Addr.add Y.cpu.gpr.rdi K).toNat / 4096 → Foot F.data z
  x0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = 0
  x3 : ∀ i, k ≤ i → i < 16 → lane 8 (xsOf Y.cpu.vec.zmm (xmmOf 3)) i = V (x.add (u + (i - k)))
  hu : u < n
  same : Same V x y u

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A round, from `j₀` (`138` or `218`): `movdqa xmm1, [rsi + rcx]; movdqa xmm2, [rdi + rcx]; movdqa xmm4, xmm2;
psrldq xmm3, k; pslldq xmm2, 16 - k; por xmm2, xmm3; pcmpeqb xmm0, xmm1; pcmpeqb xmm1, xmm2; psubb xmm1, xmm0;
pmovmskb edx, xmm1; sub edx, 0xffff; jne 6160; sub r11, 16; jbe 6212`. -/
theorem bodyS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k j₀ j₁ j₂ l₂ j₄ : Nat}
    (hb₀ : BlkV prof scm j₀ j₁ (A138 k)) (hb₁ : BlkV prof scm j₁ j₂ A166) (hj₂ : JccAt prof 5 j₂ l₂ 6160)
    (hl₂ : j₂ < scm.length) (hb₃ : BlkV prof scm (j₂ + l₂) j₄ A194) (hj₄ : JccAt prof 6 j₄ 6 6212)
    (hl₄ : j₄ < scm.length)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j₀)
    (hB : AtB g₀ Y F V x y sw n k u K) (hk : k < 16) (hn64 : n < 2 ^ 64)
    (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (H : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (j₄ + 6) →
      KpN g₀ Z.cpu.gpr → Z.cpu.gpr.rdi = Y.cpu.gpr.rdi → Z.cpu.gpr.rsi = Y.cpu.gpr.rsi →
      Z.cpu.gpr.rcx = Y.cpu.gpr.rcx → Z.cpu.gpr.r9 = Y.cpu.gpr.r9 → Z.cpu.gpr.r8 = Y.cpu.gpr.r8 →
      Z.cpu.gpr.r10 = Y.cpu.gpr.r10 → Z.cpu.gpr.r11 = BitVec.ofNat 64 (n - (u + 16)) →
      xsOf Z.cpu.vec.zmm (xmmOf 0) = 0 →
      (∀ i, k ≤ i → i < 16 → lane 8 (xsOf Z.cpu.vec.zmm (xmmOf 4)) i = V (x.add (u + 16 + (i - k)))) →
      u + 16 < n → Same V x y (u + 16) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hu := hB.hu
  have hsame := hB.same
  have hK16 := hB.K16
  have hfa : ∀ i < 16, Foot F.data ((Addr.add Y.cpu.gpr.rdi K).add i) :=
    foot_chunk (d := 0) hB.di16 (by decide) (by rw [addr_add_zero]; exact hB.pg)
  have hfb : ∀ i < 16, Foot F.data ((y.add u).add i) :=
    foot_chunk (d := 0) (by rw [← hB.si]; exact hB.si16) (by decide) (by
      rw [addr_add_zero]
      exact pg_of hpy hu fun i hi h0 => (hsame i hi).2 ((hsame i hi).1.trans h0))
  have hea : VOp.eaBI Y.cpu.gpr 7 1 0 = Addr.add Y.cpu.gpr.rdi K := by
    show Y.cpu.gpr.rdi + Y.cpu.gpr.rcx + BitVec.ofNat 64 0 = Addr.add Y.cpu.gpr.rdi K
    rw [hB.cx, BitVec.add_zero]
    try rfl
  have heb : VOp.eaBI Y.cpu.gpr 6 1 0 = y.add u := by
    show Y.cpu.gpr.rsi + Y.cpu.gpr.rcx + BitVec.ofNat 64 0 = y.add u
    rw [hB.cx, BitVec.add_zero]
    exact hB.si
  have hfa' : ∀ i < 16, Foot F.data ((VOp.eaBI Y.cpu.gpr 7 1 0).add i) := by rw [hea]; exact hfa
  have hfb' : ∀ i < 16, Foot F.data ((VOp.eaBI Y.cpu.gpr 6 1 0).add i) := by rw [heb]; exact hfb
  have hal' : (VOp.eaBI Y.cpu.gpr 7 1 0).toNat % 16 = 0 := by rw [hea]; exact hB.di16
  have hbl' : (VOp.eaBI Y.cpu.gpr 6 1 0).toNat % 16 = 0 := by rw [heb, ← hB.si]; exact hB.si16
  -- `movdqa xmm1, [rsi + rcx]; movdqa xmm2, [rdi + rcx]; movdqa xmm4, xmm2; psrldq xmm3, k;
  -- pslldq xmm2, 16 - k; por xmm2, xmm3`
  refine c.s_blkV hin hb₀ hK hA hrip ?_
  refine wpV_v hfb' (fun _ => hbl') <| wpV_v hfa' (fun _ => hal') <| wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_v0 <|
    wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  have hg₁' : Y₁.cpu.gpr = Y.cpu.gpr := by rw [hg₁]
  have hx1 : xsOf Y₁.cpu.vec.zmm (xmmOf 1) = rd16 V (y.add u) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, heb, rd16]
  have hx2 : xsOf Y₁.cpu.vec.zmm (xmmOf 2) = (rd16 V (Addr.add Y.cpu.gpr.rdi K) <<< (8 * (16 - k))) |||
      (xsOf Y.cpu.vec.zmm (xmmOf 3) >>> (8 * k)) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, hea, rd16]
  have hx4 : xsOf Y₁.cpu.vec.zmm (xmmOf 4) = rd16 V (Addr.add Y.cpu.gpr.rdi K) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, hea, rd16]
  have hx0 : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = 0 := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, hB.x0]
  have hYl : ∀ j < 16, lane 8 (rd16 V (y.add u)) j = V (y.add (u + j)) := fun j hj => lane_at V y u hj
  have hX2 : ∀ i, k ≤ i → i < 16 → lane 8 (rd16 V (Addr.add Y.cpu.gpr.rdi K)) i = V (x.add (u + 16 + (i - k))) :=
    fun i hki hi => by
      rw [lane_rd16 V _ hi, hB.di, addr_add_add, show u + 16 - k + i = u + 16 + (i - k) by omega]
  have hXl : ∀ j < 16, lane 8 ((rd16 V (Addr.add Y.cpu.gpr.rdi K) <<< (8 * (16 - k))) |||
      (xsOf Y.cpu.vec.zmm (xmmOf 3) >>> (8 * k))) j = V (x.add (u + j)) := fun j hj => by
    rw [lane_align _ _ (by omega) hj]
    split
    · rw [hB.x3 _ (by omega) (by omega), show u + (j + k - k) = u + j by omega]
    · rw [lane_rd16 V _ (by omega), hB.di, addr_add_add, show u + 16 - k + (j + k - 16) = u + j by omega]
  generalize rd16 V (y.add u) = Yb at hx1 hYl
  generalize (rd16 V (Addr.add Y.cpu.gpr.rdi K) <<< (8 * (16 - k))) |||
    (xsOf Y.cpu.vec.zmm (xmmOf 3) >>> (8 * k)) = Xc at hx2 hXl
  generalize rd16 V (Addr.add Y.cpu.gpr.rdi K) = X2 at hx4 hX2
  -- `pcmpeqb xmm0, xmm1; pcmpeqb xmm1, xmm2; psubb xmm1, xmm0; pmovmskb edx, xmm1; sub edx, 0xffff`
  refine c.s_blkV hin hb₁ hK₁ hA₁ hr₁ ?_
  refine wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  have hz : Y₂.cpu.rflags.zf = decide (cmask Yb Xc - BitVec.ofNat 32 65535 = 0) := by
    rw [hf₂, hfl, subF_zf]
    simp (disch := decide) only [gv, Src.val, get2, set_rdx, sw_64_32, sub_eq_zero_iff, xset_same, xset_ne, hx0,
      hx1, hx2, cmask]
  have hdx₂ : Y₂.cpu.gpr.rdx = (cmask Yb Xc - BitVec.ofNat 32 65535).setWidth 64 := by
    rw [hg₂]
    simp (disch := decide) only [wr, gv, Src.val, set_rdx, get2, sw_64_32, subR_eq, xset_same, xset_ne, hx0,
      hx1, hx2, cmask]
  have hxm0 : xsOf Y₂.cpu.vec.zmm (xmmOf 0) = peqb 0 Yb := by
    rw [hv₂]
    simp (disch := decide) only [xset_same, xset_ne, hx0, hx1]
  have hxm4 : xsOf Y₂.cpu.vec.zmm (xmmOf 4) = X2 := by
    rw [hv₂]
    simp (disch := decide) only [xset_same, xset_ne, hx4]
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂, hg₁', wr, set_rdx]; exact hB.kp
  have hdi₂ : Y₂.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₂, hg₁', wr, set_rdx]
  have hsi₂ : Y₂.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₂, hg₁', wr, set_rdx]
  have hcx₂ : Y₂.cpu.gpr.rcx = Y.cpu.gpr.rcx := by simp only [hg₂, hg₁', wr, set_rdx]
  have h9₂ : Y₂.cpu.gpr.r9 = Y.cpu.gpr.r9 := by simp only [hg₂, hg₁', wr, set_rdx]
  have h8₂ : Y₂.cpu.gpr.r8 = Y.cpu.gpr.r8 := by simp only [hg₂, hg₁', wr, set_rdx]
  have h10₂ : Y₂.cpu.gpr.r10 = Y.cpu.gpr.r10 := by simp only [hg₂, hg₁', wr, set_rdx]
  have h11₂ : Y₂.cpu.gpr.r11 = Y.cpu.gpr.r11 := by simp only [hg₂, hg₁', wr, set_rdx]
  -- `jne 6160`
  obtain ⟨r₁, hd₂, ht₂⟩ := hj₂
  refine c.s_jccV hK₂ hA₂ hin hl₂ hr₂ hd₂ ht₂ (lt_scm (by decide)) ?_ ?_
  · -- a stop in the 16 bytes
    intro hcc
    rw [cond_5, hz] at hcc
    have hne : cmask Yb Xc - BitVec.ofNat 32 65535 ≠ 0 := fun h => by simp [h] at hcc
    have hex : ∃ j < 16, decide (lane 8 Yb j = lane 8 Xc j ∧ lane 8 Yb j ≠ 0) = false := by
      refine Classical.byContradiction fun hn => hne ((cmask_sub_zero Yb Xc).2 fun j hj => ?_)
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 Yb j = lane 8 Xc j ∧ lane 8 Yb j ≠ 0)
      · exact absurd ⟨j, hj, h⟩ hn
      · rfl
    obtain ⟨p, hp, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 Yb p = lane 8 Xc p ∧ lane 8 Yb p ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i < p, lane 8 Yb i = lane 8 Xc i ∧ lane 8 Yb i ≠ 0 := fun i hi => of_decide_eq_true (hpt i hi)
    obtain ⟨hnz, hlow⟩ := cmask_sub_low Yb Xc hp hpf' hpt'
    have hsp : Same V x y (u + p) := same_lanes hsame hYl hXl hpt' (by omega)
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, -⟩
    refine exit6160 (k₉ := k) (kc := K) (q := u) (R := n - u) (p := p) (sw := sw) (x := x) (y := y) c hin
      hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃, h9₂]; exact hB.r9) (by rw [hg₃, hcx₂]; exact hB.cx)
      (by omega) (by rw [hg₃, hdi₂]; exact addr_shift hB.di (by omega)) (by rw [hg₃, hsi₂]; exact hB.si)
      (by rw [hg₃, h8₂]; exact hB.r8) hxy (by rw [hg₃, h11₂]; exact hB.r11) (by omega) (by omega)
      (by rw [hg₃, hdx₂]; exact hnz) (by rw [hg₃, hdx₂]; exact hlow) (by omega)
      (hsp.mono (by omega)) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · refine stop_comm ?_
      rw [← hYl p hp, ← hXl p hp]
      exact hpf'
    · exact foot_of hpx (by omega) fun i hi => (hsp i hi).2
    · exact foot_of hpy (by omega) fun i hi h0 => (hsp i hi).2 ((hsp i hi).1.trans h0)
  · -- the 16 bytes the same and not 0
    intro hcc
    rw [cond_5, hz] at hcc
    have h0 : cmask Yb Xc - BitVec.ofNat 32 65535 = 0 := by simpa using hcc
    have hall := (cmask_sub_zero Yb Xc).1 h0
    have hs16 : Same V x y (u + 16) := same_lanes hsame hYl hXl hall (Nat.le_refl _)
    have hz0 : peqb 0 Yb = 0 := peqb0_nz fun j hj => (hall j hj).2
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    -- `sub r11, 16`
    refine c.s_blkV hin hb₃ hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ hv₄
    have h11₃ : Y₃.cpu.gpr.r11 = BitVec.ofNat 64 (n - u) := by rw [hg₃, h11₂]; exact hB.r11
    have hc : Y₄.cpu.rflags.cond 6 = decide (n - u ≤ 16) := by
      rw [hf₄, hfl, cond_6, subF_cf, subF_zf]
      simp only [Src.val, gv, get11, BitVec.setWidth_eq, h11₃]
      exact be_ofNat (by omega) (by decide)
    simp only [wr, gv, Src.val, get11, BitVec.setWidth_eq, set11, subR_eq, hg₃, h11₂] at hg₄
    -- `jbe 6212`
    obtain ⟨r₂, hd₄, ht₄⟩ := hj₄
    refine c.s_jccV hK₄ hA₄ hin hl₄ hr₄ hd₄ ht₄ (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have hle : n - u ≤ 16 := by
        rw [hc] at hcc
        exact of_decide_eq_true hcc
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, -⟩
      exact ret0 c hin hK₅ hA₅ hr₅ (by rw [hg₅]; simp only [KpN, hg₄]; exact hkp₂)
        (hP 0 (nres_zero (same_ab hxy hs16) (by omega))) hR
    · intro hcc
      have hlt : 16 < n - u := by
        rw [hc] at hcc
        exact Nat.lt_of_not_le (of_decide_eq_false hcc)
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
      refine H Y₅ t₅ hK₅ hA₅ hr₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) hs16
      · rw [hg₅]; simp only [KpN, hg₄]; exact hkp₂
      · rw [hg₅, hg₄]; exact hdi₂
      · rw [hg₅, hg₄]; exact hsi₂
      · rw [hg₅, hg₄]; exact hcx₂
      · rw [hg₅, hg₄]; exact h9₂
      · rw [hg₅, hg₄]; exact h8₂
      · rw [hg₅, hg₄]; exact h10₂
      · rw [hg₅, hg₄]
        show Y.cpu.gpr.r11 - BitVec.ofNat 64 16 = _
        rw [hB.r11, ← Nat.sub_sub]
        exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
      · rw [hv₅, hv₄, hv₃, hxm0]
        exact hz0
      · intro i hki hi
        rw [hv₅, hv₄, hv₃, hxm4]
        exact hX2 i hki hi

end FV7z.Strncmp
