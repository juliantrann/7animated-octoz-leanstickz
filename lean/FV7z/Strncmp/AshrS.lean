import FV7z.Strncmp.AshrE
/-!
# The shifted loops of `__strncmp_sse2`: the way in (PLAN.md G3, `strncmp`)

From the loop's start `cL` (`align`'s `AtL`, `x`'s offset `d` in its 16 bytes less than `y`'s `c`, `k = 16 + d - c`),
the 16 aligned bytes of `y` at `rsi` are compared from `c` on with those of `x` at `rdi` moved up by `c - d`
(`pslldq xmm2, 16 - k`): a stop leaves by `6165`; otherwise when no more than those `16 - c` were to be compared
it returns 0 (`jb`, `je 6212`), and else it sets up the loop (`r11` the bytes left after them, `rcx = 16`,
`r9 = k`, `r10` the place of `rdi` in its page, `xmm3` the 16 bytes at `rdi`) and goes on at `128` (`entryS`).
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem sw32_ofNat {k : Nat} (hk : k < 16) : (BitVec.ofNat 32 k).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Aligned `r` and `r + d`, `d < 16`, in the same page. -/
theorem pg_off {r : Addr} {d : Nat} (hr : r.toNat % 16 = 0) (hd : d < 16) :
    (Addr.add r d).toNat / 4096 = r.toNat / 4096 := by
  have := r.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From the start `cL` of the loop shifting by `k = 16 + d - c`: see the module doc. -/
theorem entryS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (he : e ≤ 4)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n q : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add cL)
    (hL : AtL g₀ Y.cpu.gpr x y n q sw) (hlt : x.toNat % 16 < y.toNat % 16)
    (hkd : k + y.toNat % 16 = 16 + x.toNat % 16)
    (hn64 : n < 2 ^ 64) (hq : q < n) (hsame : Same V x y q)
    (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hkp, hdi0, hdi, hsi0, hsi, h11, hcx, hax, hdx, h8⟩ := hL
  generalize hd : x.toNat % 16 = d at hdi hax hlt hkd
  generalize hc : y.toNat % 16 = cy at hsi hcx hlt hkd
  have hc16 : cy < 16 := hc ▸ Nat.mod_lt _ (by decide)
  have hk1 : 1 ≤ k := by omega
  have hk : k < 16 := by omega
  have hnzx : ∀ i < q, V (x.add i) ≠ 0 := fun i hi => (hsame i hi).2
  have hnzy : ∀ i < q, V (y.add i) ≠ 0 := fun i hi h0 => (hsame i hi).2 ((hsame i hi).1.trans h0)
  have hfa : ∀ i < 16, Foot F.data (Addr.add Y.cpu.gpr.rdi i) :=
    foot_chunk hdi0 (by omega : d < 16) (by rw [hdi]; exact pg_of hpx hq hnzx)
  have hfb : ∀ i < 16, Foot F.data (Addr.add Y.cpu.gpr.rsi i) :=
    foot_chunk hsi0 hc16 (by rw [hsi]; exact pg_of hpy hq hnzy)
  have heA : eaB Y.cpu.gpr 7 0 = Y.cpu.gpr.rdi := by
    show Y.cpu.gpr.rdi + BitVec.ofNat 64 0 = _
    rw [BitVec.add_zero]
  have heB : eaB Y.cpu.gpr 6 0 = Y.cpu.gpr.rsi := by
    show Y.cpu.gpr.rsi + BitVec.ofNat 64 0 = _
    rw [BitVec.add_zero]
  have hfa' : ∀ i < 16, Foot F.data ((eaB Y.cpu.gpr 7 0).add i) := by rw [heA]; exact hfa
  have hfb' : ∀ i < 16, Foot F.data ((eaB Y.cpu.gpr 6 0).add i) := by rw [heB]; exact hfb
  have hal' : (eaB Y.cpu.gpr 7 0).toNat % 16 = 0 := by rw [heA]; exact hdi0
  have hbl' : (eaB Y.cpu.gpr 6 0).toNat % 16 = 0 := by rw [heB]; exact hsi0
  -- `pxor xmm0, xmm0; movdqa xmm2, [rdi]; movdqa xmm1, [rsi]; pcmpeqb xmm0, xmm1; pslldq xmm2, 16 - k;
  -- pcmpeqb xmm2, xmm1`
  refine c.s_blkV hin A.p0 hK hA hrip ?_
  refine wpV_v0 <| wpV_v hfa' (fun _ => hal') <| wpV_v hfb' (fun _ => hbl') <| wpV_v0 <| wpV_v0 <| wpV_v0 <|
    wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  have hx2₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 2) =
      peqb (rd16 V Y.cpu.gpr.rdi <<< (8 * (16 - k))) (rd16 V Y.cpu.gpr.rsi) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, heA, heB, rd16]
  have hx0₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = peqb 0 (rd16 V Y.cpu.gpr.rsi) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, xor_z, heB, rd16]
  have hg₁' : Y₁.cpu.gpr = Y.cpu.gpr := by rw [hg₁]
  generalize hYb : rd16 V Y.cpu.gpr.rsi = Yb at hx2₁ hx0₁
  generalize hXs : rd16 V Y.cpu.gpr.rdi <<< (8 * (16 - k)) = Xs at hx2₁
  have hYl : ∀ j, cy ≤ j → j < 16 → lane 8 Yb j = V (y.add (q + (j - cy))) := fun j hcj hj => by
    rw [← hYb, lane_rd16 V _ hj, add_shift hsi hcj]
  have hXl : ∀ j, cy ≤ j → j < 16 → lane 8 Xs j = V (x.add (q + (j - cy))) := fun j hcj hj => by
    rw [← hXs, lane_shl _ _ hj, if_pos (show 16 - k ≤ j by omega), lane_rd16 V _ (by omega), add_shift hdi (by omega),
      show q + (j - (16 - k) - d) = q + (j - cy) by omega]
  -- `psubb xmm2, xmm0; pmovmskb r9d, xmm2; shr edx, cl; shr r9d, cl; sub edx, r9d`
  refine c.s_blkV hin A.p25 hK₁ hA₁ hr₁ ?_
  refine wpV_v0 <| wpV_v0 <| wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  have hdx₂ : Y₂.cpu.gpr.rdx = ((BitVec.ofNat 32 65535 >>> cy) - (cmask Yb Xs >>> cy)).setWidth 64 := by
    rw [hg₂]
    simp (disch := decide) only [wr, gv, Src.val, set_rdx, set_r9n, get2, get_r9n, get1, hg₁', hcx, hdx,
      sw_64_32, shr_cnt hc16, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), subR_eq, xset_same, hx2₁, hx0₁,
      cmask, peqb_comm Yb Xs]
  have hz₂ : Y₂.cpu.rflags.zf = decide ((BitVec.ofNat 32 65535 >>> cy) - (cmask Yb Xs >>> cy) = 0) := by
    rw [hf₂, hfl, subF_zf]
    simp (disch := decide) only [wr, gv, Src.val, set_rdx, set_r9n, get2, get_r9n, get1, hg₁', hcx, hdx,
      sw_64_32, shr_cnt hc16, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), sub_eq_zero_iff, xset_same, hx2₁,
      hx0₁, cmask, peqb_comm Yb Xs]
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂, hg₁', wr, set_rdx, set_r9n]; exact hkp
  have hdi₂ : Y₂.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₂, hg₁', wr, set_rdx, set_r9n]
  have hsi₂ : Y₂.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₂, hg₁', wr, set_rdx, set_r9n]
  have hcx₂ : Y₂.cpu.gpr.rcx = BitVec.ofNat 64 cy := by simp only [hg₂, hg₁', wr, set_rdx, set_r9n]; exact hcx
  have hax₂ : Y₂.cpu.gpr.rax = BitVec.ofNat 64 d := by simp only [hg₂, hg₁', wr, set_rdx, set_r9n]; exact hax
  have h11₂ : Y₂.cpu.gpr.r11 = BitVec.ofNat 64 (n - q) := by
    simp only [hg₂, hg₁', wr, set_rdx, set_r9n]; exact h11
  have h8₂ : Y₂.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0 := by
    simp only [hg₂, hg₁', wr, set_rdx, set_r9n]; exact h8
  -- `jne 6165`
  obtain ⟨r₁, hd₁, ht₁⟩ := A.j42
  refine c.s_jccV hK₂ hA₂ hin (lt_scm (by omega)) hr₂ hd₁ ht₁ (lt_scm (by decide)) ?_ ?_
  · -- a stop in the bytes from `cy` on
    intro hcc
    rw [cond_5, hz₂] at hcc
    have hne : (BitVec.ofNat 32 65535 >>> cy) - (cmask Yb Xs >>> cy) ≠ 0 := fun h => by
      rw [h] at hcc
      exact absurd hcc (by decide)
    have hex : ∃ j < 16 - cy,
        decide (lane 8 Yb (cy + j) = lane 8 Xs (cy + j) ∧ lane 8 Yb (cy + j) ≠ 0) = false := by
      refine Classical.byContradiction fun hn => hne ((shr_sub_zero Yb Xs cy).2 fun j hcj hj => ?_)
      have e : cy + (j - cy) = j := by omega
      rw [← e]
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 Yb (cy + (j - cy)) = lane 8 Xs (cy + (j - cy)) ∧ lane 8 Yb (cy + (j - cy)) ≠ 0)
      · exact absurd ⟨j - cy, by omega, h⟩ hn
      · rfl
    obtain ⟨j₀, hj₀, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 Yb (cy + j₀) = lane 8 Xs (cy + j₀) ∧ lane 8 Yb (cy + j₀) ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i, cy ≤ i → i < cy + j₀ → lane 8 Yb i = lane 8 Xs i ∧ lane 8 Yb i ≠ 0 := fun i h1 h2 => by
      have h := of_decide_eq_true (hpt (i - cy) (by omega))
      rwa [show cy + (i - cy) = i by omega] at h
    obtain ⟨hnz, hlow⟩ := shr_sub_low Yb Xs (c := cy) (p := cy + j₀) (by omega) (by omega) hpf' hpt'
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, -⟩
    refine exit6165 (ka := d) (kc := cy) (q := q) (R := n - q) (p := j₀) (sw := sw) (x := x) (y := y) c hin
      hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hax₂) (by rw [hg₃]; exact hcx₂)
      (by rw [hg₃, hdi₂]; exact hdi) (by rw [hg₃, hsi₂]; exact hsi) (by rw [hg₃]; exact h8₂)
      hxy (by rw [hg₃]; exact h11₂) (by omega) (by omega) (by rw [hg₃, hdx₂]; exact hnz)
      (by rw [hg₃, hdx₂, hlow]; omega) (by omega) ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · intro i hi
      by_cases hiq : i < q
      · exact hsame i hiq
      · have h := hpt' (i - q + cy) (by omega) (by omega)
        rw [hYl _ (by omega) (by omega), hXl _ (by omega) (by omega), show q + (i - q + cy - cy) = i by omega] at h
        exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩
    · refine stop_comm ?_
      rw [show q + j₀ = q + (cy + j₀ - cy) by omega, ← hYl (cy + j₀) (by omega) (by omega),
        ← hXl (cy + j₀) (by omega) (by omega)]
      exact hpf'
    · rw [show q + j₀ = q + (d + j₀ - d) by omega, ← add_shift hdi (by omega : d ≤ d + j₀)]
      exact hfa _ (by omega)
    · rw [show q + j₀ = q + (cy + j₀ - cy) by omega, ← add_shift hsi (by omega : cy ≤ cy + j₀)]
      exact hfb _ (by omega)
  · -- the bytes from `cy` on the same and not 0
    intro hcc
    rw [cond_5, hz₂] at hcc
    have h0 : (BitVec.ofNat 32 65535 >>> cy) - (cmask Yb Xs >>> cy) = 0 := by simpa using hcc
    have hall := (shr_sub_zero Yb Xs cy).1 h0
    have hs : Same V x y (q + (16 - cy)) := by
      intro i hi
      by_cases hiq : i < q
      · exact hsame i hiq
      · have h := hall (i - q + cy) (by omega) (by omega)
        rw [hYl _ (by omega) (by omega), hXl _ (by omega) (by omega), show q + (i - q + cy - cy) = i by omega] at h
        exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, -⟩
    have heA₃ : eaB Y₃.cpu.gpr 7 0 = Y.cpu.gpr.rdi := by
      show Y₃.cpu.gpr.rdi + BitVec.ofNat 64 0 = _
      rw [BitVec.add_zero, hg₃, hdi₂]
    have hfa₃ : ∀ i < 16, Foot F.data ((eaB Y₃.cpu.gpr 7 0).add i) := by rw [heA₃]; exact hfa
    have hal₃ : (eaB Y₃.cpu.gpr 7 0).toNat % 16 = 0 := by rw [heA₃]; exact hdi0
    -- `movdqa xmm3, [rdi]; lea r9, [rcx + r11 - 16]; cmp r11, r9`
    refine c.s_blkV hin A.p48 hK₃ hA₃ (rip_at hr₃ (by omega)) ?_
    refine wpV_v hfa₃ (fun _ => hal₃) <| wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ hv₄
    have h3₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 3) = rd16 V Y.cpu.gpr.rdi := by
      rw [hv₄]
      simp only [xset_same, heA₃, rd16]
    have h9₄ : Y₄.cpu.gpr.r9 = BitVec.ofNat 64 cy + BitVec.ofNat 64 (n - q) * BitVec.ofNat 64 1 +
        BitVec.ofNat 64 18446744073709551600 := by
      rw [hg₄]
      simp only [wr, eaG, optV, set_r9n, get1, get11, BitVec.setWidth_eq, hg₃, hcx₂, h11₂]
    have hc2 : Y₄.cpu.rflags.cond 2 = decide (n - q < (BitVec.ofNat 64 cy + BitVec.ofNat 64 (n - q) *
        BitVec.ofNat 64 1 + BitVec.ofNat 64 18446744073709551600).toNat) := by
      rw [hf₄, hfl, cond_2, subF_cf]
      simp only [wr, gv, Src.val, eaG, optV, set_r9n, get1, get11, get_r9n, BitVec.setWidth_eq, hg₃, hcx₂, h11₂]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n - q < 2 ^ 64 by omega)]
    have hkp₄ : KpN g₀ Y₄.cpu.gpr := by simp only [KpN, hg₄, hg₃, wr, set_r9n]; exact hkp₂
    have hdi₄ : Y₄.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₄, hg₃, wr, set_r9n]; exact hdi₂
    have hsi₄ : Y₄.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₄, hg₃, wr, set_r9n]; exact hsi₂
    have h8₄ : Y₄.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0 := by
      simp only [hg₄, hg₃, wr, set_r9n]; exact h8₂
    -- `jb 6212`
    obtain ⟨r₂, hd₂, ht₂⟩ := A.j60
    refine c.s_jccV hK₄ hA₄ hin (lt_scm (by omega)) hr₄ hd₂ ht₂ (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have hle : n ≤ q + (16 - cy) := by
        refine Nat.le_of_not_lt fun hgt => ?_
        rw [hc2, lea_m16 (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show cy + (n - q) - 16 < 2 ^ 64 by omega)] at hcc
        exact absurd (of_decide_eq_true hcc) (by omega)
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, -⟩
      exact ret0 c hin hK₅ hA₅ hr₅ (by rw [hg₅]; exact hkp₄) (hP 0 (nres_zero (same_ab hxy hs) hle)) hR
    intro hcc
    have hge : 16 ≤ cy + (n - q) := by
      refine Nat.le_of_not_lt fun hw => ?_
      rw [hc2, decide_eq_true (lea_wrap (by omega))] at hcc
      exact absurd hcc (by decide)
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
    have h9₅ : Y₅.cpu.gpr.r9 = BitVec.ofNat 64 (cy + (n - q) - 16) := by rw [hg₅, h9₄]; exact lea_m16 hge
    -- `test r9, r9`
    refine c.s_blkV hin A.p66 hK₅ hA₅ (rip_at hr₅ (by omega)) ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ hf₆ hv₆
    have hz₆ : Y₆.cpu.rflags.cond 4 = decide (cy + (n - q) - 16 = 0) := by
      rw [hf₆, cond4_log hfl]
      simp only [gv, Src.val, get_r9n, BitVec.setWidth_eq, BitVec.and_self, h9₅]
      exact ofNat_beq_zero (by omega)
    have hg₆' : Y₆.cpu.gpr = Y₄.cpu.gpr := by rw [hg₆, hg₅]
    -- `je 6212`
    obtain ⟨r₃, hd₃, ht₃⟩ := A.j69
    refine c.s_jccV hK₆ hA₆ hin (lt_scm (by omega)) hr₆ hd₃ ht₃ (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have h16 : cy + (n - q) - 16 = 0 := by
        rw [hz₆] at hcc
        exact of_decide_eq_true hcc
      rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, -⟩
      exact ret0 c hin hK₇ hA₇ hr₇ (by rw [hg₇, hg₆']; exact hkp₄)
        (hP 0 (nres_zero (same_ab hxy hs) (by omega))) hR
    intro hcc
    have hgt : 16 < cy + (n - q) := by
      rw [hz₆] at hcc
      have := of_decide_eq_false hcc
      omega
    rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, hv₇⟩
    -- `mov r11, r9; pxor xmm0, xmm0; mov rcx, 16; mov r9d, k; lea r10, [rdi + k]; and r10, 4095`
    refine c.s_blkV hin A.p75 hK₇ hA₇ (rip_at hr₇ (by omega)) ?_
    refine wpV_reg fun _ _ => wpV_v0 <| wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_nil ?_
    intro Y₈ t₈ hK₈ hA₈ hr₈ hg₈ _ hv₈
    -- `sub r10, 4096; nop; nop`
    refine c.s_blkV hin A.p106 hK₈ hA₈ hr₈ ?_
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
    intro Y₉ t₉ hK₉ hA₉ hr₉ hg₉ _ hv₉
    simp only [wr, gv, Src.val, eaG, optV, set11, set_rcx, set_r9n, set_r10n, get_r9n, get_r10n, get7,
      BitVec.setWidth_eq, BitVec.zero_mul, BitVec.add_zero, subR_eq, hg₇, hg₆'] at hg₈ hg₉
    have hkp₉ : KpN g₀ Y₉.cpu.gpr := by simp only [KpN, hg₉, hg₈]; exact hkp₄
    have hdi₉ : Y₉.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₉, hg₈]; exact hdi₄
    have hsi₉ : Y₉.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₉, hg₈]; exact hsi₄
    have hcx₉ : Y₉.cpu.gpr.rcx = BitVec.ofNat 64 16 := by simp only [hg₉, hg₈]
    have h9₉ : Y₉.cpu.gpr.r9 = BitVec.ofNat 64 k := by simp only [hg₉, hg₈]; exact sw32_ofNat hk
    have h8₉ : Y₉.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0 := by simp only [hg₉, hg₈]; exact h8₄
    have h9₄' : Y₄.cpu.gpr.r9 = BitVec.ofNat 64 (n - (q + (16 - cy))) := by
      rw [← hg₅, h9₅, show cy + (n - q) - 16 = n - (q + (16 - cy)) by omega]
    have h11₉ : Y₉.cpu.gpr.r11 = BitVec.ofNat 64 (n - (q + (16 - cy))) := by simp only [hg₉, hg₈, h9₄']
    have h10₉ : Y₉.cpu.gpr.r10 =
        ((Y.cpu.gpr.rdi + BitVec.ofNat 64 k) &&& BitVec.ofNat 64 4095) - BitVec.ofNat 64 4096 := by
      simp only [hg₉, hg₈, hdi₄]
    have hx0₉ : xsOf Y₉.cpu.vec.zmm (xmmOf 0) = 0 := by
      rw [hv₉, hv₈]
      simp only [xset_same, xor_z]
    have hx3₉ : xsOf Y₉.cpu.vec.zmm (xmmOf 3) = rd16 V Y.cpu.gpr.rdi := by
      rw [hv₉, hv₈]
      simp (disch := decide) only [xset_ne, hv₇, hv₆, hv₅, h3₄]
    have hpg : ∀ z : Addr, z.toNat / 4096 = Y.cpu.gpr.rdi.toNat / 4096 → Foot F.data z := by
      rw [← pg_off hdi0 (by omega : d < 16), hdi]
      exact pg_of hpx hq hnzx
    -- the loop, at `128`
    have hu : q + (16 - cy) < n := by omega
    refine at128 c hin A hcl hk1 hk hK₉ hA₉ hr₉ ?_ hn64 hxy hpx hpy hP hR
      fun Z t' => (loopS c hin A hcl he hk1 hk hn64 hxy hpx hpy hP hR (n - (q + (16 - cy))) (q + (16 - cy))
        le_rfl).1 Z t' 16
    exact
      { reg :=
          { kp := hkp₉
            di := by rw [hdi₉]; exact addr_shift hdi (by omega)
            si := by rw [hsi₉]; exact addr_shift hsi (by omega)
            cx := hcx₉
            r9 := h9₉
            r8 := h8₉
            r11 := h11₉ }
        K16 := Nat.le_refl 16
        r10 := by rw [h10₉, hdi₉, Nat.sub_self, addr_add_zero]; exact r10_init hdi0 hk
        di0 := by rw [hdi₉, Nat.sub_self, addr_add_zero]; exact hdi0
        si16 := by rw [hsi₉]; exact al_add hsi0 (by decide)
        pg := by rw [hdi₉, Nat.sub_self, addr_add_zero]; exact hpg
        x0 := hx0₉
        x3 := fun i hki hi => by
          rw [hx3₉, lane_rd16 V _ hi, add_shift hdi (by omega)]
          congr 2
          omega
        hu := hu
        same := hs }

end FV7z.Strncmp
