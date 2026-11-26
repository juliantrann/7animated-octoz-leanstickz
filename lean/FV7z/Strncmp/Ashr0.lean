import FV7z.Strncmp.ExitS
import FV7z.Strncmp.Shr
/-!
# `__strncmp_sse2`: the loop of `ashr_0` (PLAN.md G3, `strncmp`)

When the two strings' offsets `d` in their 16 bytes are the same, `align` goes on to `192` with `rdi` and `rsi` the
aligned 16 bytes holding the next bytes of each. The first compare (`192`–`225`) is of those 16 bytes from `d` on
(`Shr.lean`); a stop there leaves by `6165`. Otherwise `lea r9, [rcx + r11 - 16]` is what is left of `n` after them:
`jb` (it wrapped) and `je` (it is 0) return 0, else from `254` `r11 = r9`, `rcx = r9 = 16`, `xmm0 = 0`, and the loop at
`288` compares the 16 aligned bytes at `rsi + rcx` and `rdi + rcx`, the bytes at `u = q + rcx - d` of each string,
twice per round (`half`, at `288` and at `340`): a stop leaves by `6160`, `sub r11, 16; jbe` returns 0 when no more
are to be compared, and `add rcx, 16` goes on, `xmm0` 0 again since no byte of `rsi`'s 16 was 0. `InvL` is what holds at
the loop's halves; `loop288` is the loop, by induction on the bytes left, and `ashr0` the run from `192`.

- `peqb0_nz`: `pcmpeqb` of 0 with 16 bytes none 0 is 0.
- `foot_chunk`, `pg_of`: the aligned 16 bytes holding a byte of a string in its page, to read.
- `add_shift`, `al_add`: addresses `d` bytes before a string's byte; alignment.
- `lea_wrap`: `rcx + r11 - 16` wraps when fewer than `16 - rcx` bytes are left.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

/-! ## Numbers and addresses -/

/-- `pcmpeqb` of 0 with 16 bytes none 0. -/
theorem peqb0_nz {Y : BitVec 128} (h : ∀ j < 16, lane 8 Y j ≠ 0) : peqb 0 Y = 0 := by
  have e : ∀ j < 16, (if lane 8 (0 : BitVec 128) j = lane 8 Y j then BitVec.allOnes 8 else 0) = (0 : BitVec 8) :=
    fun j hj => by rw [lane_zero, if_neg (fun e => h j hj e.symm)]
  simp only [peqb, ofBytes, e 15 (by decide), e 14 (by decide), e 13 (by decide), e 12 (by decide),
    e 11 (by decide), e 10 (by decide), e 9 (by decide), e 8 (by decide), e 7 (by decide), e 6 (by decide),
    e 5 (by decide), e 4 (by decide), e 3 (by decide), e 2 (by decide), e 1 (by decide), e 0 (by decide)]
  all_goals decide

/-- The 16 bytes from an aligned `z` are in the page of `z + d`, `d < 16`. -/
theorem foot_chunk {F : Footprint} {z : Addr} {d : Nat} (hz : z.toNat % 16 = 0) (hd : d < 16)
    (hpg : ∀ x : Addr, x.toNat / 4096 = (Addr.add z d).toNat / 4096 → Foot F.data x) :
    ∀ i < 16, Foot F.data (z.add i) := by
  intro i hi
  apply hpg
  have hz' := z.isLt
  have e1 : (z.add i).toNat = z.toNat + i := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e2 : (Addr.add z d).toNat = z.toNat + d := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, e2]
  omega

/-- Byte `u` of a string with all before it not 0, `u < n`: its page is to read. -/
theorem pg_of {F : Footprint} {V : Addr → Byte} {a : Addr} {n u : Nat} (hp : Str.StrPg F V a n) (hu : u < n)
    (hnz : ∀ i < u, V (a.add i) ≠ 0) : ∀ x : Addr, x.toNat / 4096 = (a.add u).toNat / 4096 → Foot F.data x := by
  obtain ⟨h64, hpg⟩ := hp u hu hnz
  have e : (a.add u).toNat = a.toNat + u := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact hpg

/-- `r` is `d` bytes before byte `q` of `z`: `r + j` is byte `q + (j - d)`. -/
theorem add_shift {r z : Addr} {d q j : Nat} (h : Addr.add r d = z.add q) (hj : d ≤ j) :
    r.add j = z.add (q + (j - d)) := by
  rw [← addr_add_add, ← h, addr_add_add, Nat.add_sub_cancel' hj]

/-- Aligned, plus a multiple of 16. -/
theorem al_add {z : Addr} {k : Nat} (hz : z.toNat % 16 = 0) (hk : k % 16 = 0) : (z.add k).toNat % 16 = 0 := by
  have := z.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `rcx + r11 - 16`, `rcx + r11 < 16`: wrapped, above `r11`. -/
theorem lea_wrap {d R : Nat} (h : d + R < 16) :
    R < (BitVec.ofNat 64 d + BitVec.ofNat 64 R * BitVec.ofNat 64 1 + BitVec.ofNat 64 18446744073709551600).toNat := by
  have e : BitVec.ofNat 64 18446744073709551600 = -BitVec.ofNat 64 16 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, BitVec.mul_one, BitVec.ofNat_add_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show d + R < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 ^ 64 - 16 + (d + R) < 2 ^ 64 by omega)]
  omega

/-- `shr r32, cl` with `rcx = d < 16`: the count `d`. -/
theorem shr_cnt {d : Nat} (hd : d < 16) : ((BitVec.ofNat 64 d).setWidth 8).toNat % 32 = d := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The bytes `j` of 16 at byte `u` of a string. -/
theorem lane_at (V : Addr → Byte) (z : Addr) (u : Nat) {j : Nat} (hj : j < 16) :
    lane 8 (rd16 V (z.add u)) j = V (z.add (u + j)) := by
  rw [lane_rd16 V _ hj, addr_add_add]

/-- A stop of `b` and `a` at their 16 bytes from `u`: what is the same up to it. -/
theorem same_chunk {V : Addr → Byte} {a b : Addr} {u p : Nat} (hs : Same V a b u)
    (ht : ∀ i < p, lane 8 (rd16 V (b.add u)) i = lane 8 (rd16 V (a.add u)) i ∧ lane 8 (rd16 V (b.add u)) i ≠ 0)
    (hp : p ≤ 16) : Same V a b (u + p) := by
  intro i hi
  by_cases hiu : i < u
  · exact hs i hiu
  · have h := ht (i - u) (by omega)
    rw [lane_at V b u (by omega), lane_at V a u (by omega), show u + (i - u) = i by omega] at h
    exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩

/-! ## The loop -/

/-- At the loop's halves: `rdi + k` and `rsi + k` the bytes at `u` of `a` and `b`, `rcx = k`, `r9 = 16`, `r8 = 0`
(not swapped), `r11` the bytes left of `n`. -/
def InvL (g₀ g : Gprs) (a b : Addr) (n u k : Nat) : Prop :=
  KpN g₀ g ∧ Addr.add g.rdi k = a.add u ∧ Addr.add g.rsi k = b.add u ∧ g.rcx = BitVec.ofNat 64 k ∧
    g.r9 = BitVec.ofNat 64 16 ∧ g.r8 = 0 ∧ g.r11 = BitVec.ofNat 64 (n - u)

theorem InvL.rdx {g₀ g : Gprs} {a b : Addr} {n u k : Nat} (h : InvL g₀ g a b n u k) (v : BitVec 64) :
    InvL g₀ (g.set (regOf 2) v) a b n u k := h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A half of the loop, from `j₀` (`288` or `340`): `movdqa xmm1, [rsi + rcx]; movdqa xmm2, [rdi + rcx]; pcmpeqb
xmm0, xmm1; pcmpeqb xmm1, xmm2; psubb xmm1, xmm0; pmovmskb edx, xmm1; sub edx, 0xffff; jne 6160; sub r11, 16;
jbe 6212; add rcx, 16`. -/
theorem half (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {j₀ j₁ j₂ j₄ j₆ r₁ r₂ : Nat}
    (hb₀ : BlkV prof scm j₀ j₁ o288) (hb₁ : BlkV prof scm j₁ j₂ o314)
    (hd₂ : Dec prof.feat scm j₂ (FV7z.mk (.jcc 5) 64 [.rel r₁] 6)) (hl₂ : j₂ < scm.length)
    (ht₂ : (j₂ + 6 + r₁) % 2 ^ 64 = 6160 % 2 ^ 64) (hb₃ : BlkV prof scm (j₂ + 6) j₄ o326)
    (hd₄ : Dec prof.feat scm j₄ (FV7z.mk (.jcc 6) 64 [.rel r₂] 6)) (hl₄ : j₄ < scm.length)
    (ht₄ : (j₄ + 6 + r₂) % 2 ^ 64 = 6212 % 2 ^ 64) (hb₅ : BlkV prof scm (j₄ + 6) j₆ o336)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b : Addr} {n u k : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j₀)
    (hI : InvL g₀ Y.cpu.gpr a b n u k) (hx0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = 0)
    (hn64 : n < 2 ^ 64) (hu : u < n) (hsame : Same V a b u) (hpa : Str.StrPg F V a n) (hpb : Str.StrPg F V b n)
    (hal : (a.add u).toNat % 16 = 0) (hbl : (b.add u).toNat % 16 = 0)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (K : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j₆ →
      InvL g₀ Z.cpu.gpr a b n (u + 16) (k + 16) → xsOf Z.cpu.vec.zmm (xmmOf 0) = 0 → u + 16 < n →
      Same V a b (u + 16) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hfa : ∀ i < 16, Foot F.data ((a.add u).add i) :=
    foot_chunk (d := 0) hal (by decide) (by rw [addr_add_zero]; exact pg_of hpa hu fun i hi => (hsame i hi).2)
  have hfb : ∀ i < 16, Foot F.data ((b.add u).add i) :=
    foot_chunk (d := 0) hbl (by decide) (by
      rw [addr_add_zero]
      exact pg_of hpb hu fun i hi h0 => (hsame i hi).2 ((hsame i hi).1.trans h0))
  have hea : VOp.eaBI Y.cpu.gpr 7 1 0 = a.add u := by
    show Y.cpu.gpr.rdi + Y.cpu.gpr.rcx + BitVec.ofNat 64 0 = a.add u
    rw [hI.2.2.2.1, BitVec.add_zero]
    exact hI.2.1
  have heb : VOp.eaBI Y.cpu.gpr 6 1 0 = b.add u := by
    show Y.cpu.gpr.rsi + Y.cpu.gpr.rcx + BitVec.ofNat 64 0 = b.add u
    rw [hI.2.2.2.1, BitVec.add_zero]
    exact hI.2.2.1
  have hfa' : ∀ i < 16, Foot F.data ((VOp.eaBI Y.cpu.gpr 7 1 0).add i) := by rw [hea]; exact hfa
  have hfb' : ∀ i < 16, Foot F.data ((VOp.eaBI Y.cpu.gpr 6 1 0).add i) := by rw [heb]; exact hfb
  have hal' : (VOp.eaBI Y.cpu.gpr 7 1 0).toNat % 16 = 0 := by rw [hea]; exact hal
  have hbl' : (VOp.eaBI Y.cpu.gpr 6 1 0).toNat % 16 = 0 := by rw [heb]; exact hbl
  -- `movdqa xmm1, [rsi + rcx]; movdqa xmm2, [rdi + rcx]; pcmpeqb xmm0, xmm1; pcmpeqb xmm1, xmm2; psubb xmm1, xmm0;
  -- pmovmskb edx, xmm1`
  refine c.s_blkV hin hb₀ hK hA hrip ?_
  refine wpV_v hfb' (fun _ => hbl') <| wpV_v hfa' (fun _ => hal') <| wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_v0 <|
    wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  have hdx₁ : Y₁.cpu.gpr.rdx = (cmask (rd16 V (b.add u)) (rd16 V (a.add u))).setWidth 64 := by
    rw [hg₁]
    simp (disch := decide) only [set_rdx, xset_same, xset_ne, hx0, heb, hea, cmask, rd16]
  have hxm0 : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = peqb 0 (rd16 V (b.add u)) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, hx0, heb, rd16]
  have hI₁ : InvL g₀ Y₁.cpu.gpr a b n u k := by rw [hg₁]; exact hI.rdx _
  -- `sub edx, 0xffff`
  refine c.s_blkV hin hb₁ hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  have hz : Y₂.cpu.rflags.zf = decide (cmask (rd16 V (b.add u)) (rd16 V (a.add u)) - BitVec.ofNat 32 65535 = 0) := by
    rw [hf₂, hfl, subF_zf]
    simp only [gv, Src.val, get2, hdx₁, sw_64_32, sub_eq_zero_iff]
  have hdx₂ : Y₂.cpu.gpr.rdx = (cmask (rd16 V (b.add u)) (rd16 V (a.add u)) - BitVec.ofNat 32 65535).setWidth 64 := by
    rw [hg₂]
    simp only [wr, gv, Src.val, set_rdx, get2, hdx₁, sw_64_32, subR_eq]
  have hI₂ : InvL g₀ Y₂.cpu.gpr a b n u k := by rw [hg₂]; exact hI₁.rdx _
  obtain ⟨hkp₂, hdi₂, hsi₂, hcx₂, h9₂, h8₂, h11₂⟩ := hI₂
  generalize hYb : rd16 V (b.add u) = Yb at hdx₂ hz hxm0
  generalize hXa : rd16 V (a.add u) = Xa at hdx₂ hz
  have hYl : ∀ j < 16, lane 8 Yb j = V (b.add (u + j)) := fun j hj => by rw [← hYb]; exact lane_at V b u hj
  have hXl : ∀ j < 16, lane 8 Xa j = V (a.add (u + j)) := fun j hj => by rw [← hXa]; exact lane_at V a u hj
  -- `jne 6160`
  refine c.s_jccV hK₂ hA₂ hin hl₂ hr₂ hd₂ ht₂ (lt_scm (by decide)) ?_ ?_
  · -- a stop in the 16 bytes
    intro hcc
    rw [cond_5, hz] at hcc
    have hne : cmask Yb Xa - BitVec.ofNat 32 65535 ≠ 0 := fun h => by simp [h] at hcc
    have hex : ∃ j < 16, decide (lane 8 Yb j = lane 8 Xa j ∧ lane 8 Yb j ≠ 0) = false := by
      refine Classical.byContradiction fun hn => hne ((cmask_sub_zero Yb Xa).2 fun j hj => ?_)
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 Yb j = lane 8 Xa j ∧ lane 8 Yb j ≠ 0)
      · exact absurd ⟨j, hj, h⟩ hn
      · rfl
    obtain ⟨p, hp, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 Yb p = lane 8 Xa p ∧ lane 8 Yb p ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i < p, lane 8 Yb i = lane 8 Xa i ∧ lane 8 Yb i ≠ 0 := fun i hi => of_decide_eq_true (hpt i hi)
    obtain ⟨hnz, hlow⟩ := cmask_sub_low Yb Xa hp hpf' hpt'
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, -⟩
    refine exit6160 (k₉ := 16) (kc := k) (q := u) (R := n - u) (p := p) (sw := false) (x := a) (y := b) c hin
      hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact h9₂) (by rw [hg₃]; exact hcx₂) (by omega)
      (by rw [hg₃, Nat.add_sub_cancel_left]; exact hdi₂) (by rw [hg₃]; exact hsi₂) (by rw [hg₃]; exact h8₂)
      (Or.inl ⟨rfl, rfl, rfl⟩) (by rw [hg₃]; exact h11₂) (by omega) (by omega) (by rw [hg₃, hdx₂]; exact hnz)
      (by rw [hg₃, hdx₂]; exact hlow) (by omega) ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · refine same_chunk hsame (fun i hi => ?_) (by omega)
      rw [hYb, hXa]
      exact hpt' i hi
    · refine stop_comm ?_
      rw [← hYl p hp, ← hXl p hp]
      exact hpf'
    · rw [← addr_add_add]
      exact hfa p hp
    · rw [← addr_add_add]
      exact hfb p hp
  · -- the 16 bytes the same and not 0
    intro hcc
    rw [cond_5, hz] at hcc
    have h0 : cmask Yb Xa - BitVec.ofNat 32 65535 = 0 := by simpa using hcc
    have hall := (cmask_sub_zero Yb Xa).1 h0
    have hs16 : Same V a b (u + 16) := by
      refine same_chunk hsame (fun i hi => ?_) (Nat.le_refl _)
      rw [hYb, hXa]
      exact hall i hi
    have hz0 : peqb 0 Yb = 0 := peqb0_nz fun j hj => (hall j hj).2
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    -- `sub r11, 16`
    refine c.s_blkV hin hb₃ hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ hv₄
    have hc : Y₄.cpu.rflags.cond 6 = decide (n - u ≤ 16) := by
      rw [hf₄, hfl, cond_6, subF_cf, subF_zf]
      simp only [Src.val, gv, get11, BitVec.setWidth_eq, hg₃, h11₂]
      exact be_ofNat (by omega) (by decide)
    simp only [wr, gv, Src.val, get11, BitVec.setWidth_eq, set11, subR_eq, hg₃] at hg₄
    -- `jbe 6212`
    refine c.s_jccV hK₄ hA₄ hin hl₄ hr₄ hd₄ ht₄ (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have hle : n - u ≤ 16 := by
        rw [hc] at hcc
        exact of_decide_eq_true hcc
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, -⟩
      exact ret0 c hin hK₅ hA₅ hr₅ (by rw [hg₅]; simp only [KpN, hg₄]; exact hkp₂)
        (hP 0 (nres_zero hs16 (by omega))) hR
    · intro hcc
      have hlt : 16 < n - u := by
        rw [hc] at hcc
        exact Nat.lt_of_not_le (of_decide_eq_false hcc)
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hv₅⟩
      -- `add rcx, 16`
      refine c.s_blkV hin hb₅ hK₅ hA₅ hr₅ ?_
      refine wpV_reg fun _ _ => wpV_nil ?_
      intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ _ hv₆
      simp only [wr, gv, Src.val, get1, BitVec.setWidth_eq, set_rcx, addR_eq, hg₅, hg₄] at hg₆
      refine K Y₆ t₆ hK₆ hA₆ hr₆ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ (by omega) hs16
      · simp only [KpN, hg₆]
        exact hkp₂
      · simp only [hg₆]
        rw [← addr_add_add, hdi₂, addr_add_add]
      · simp only [hg₆]
        rw [← addr_add_add, hsi₂, addr_add_add]
      · simp only [hg₆, hcx₂]
        exact BitVec.ofNat_add_ofNat _ _
      · simp only [hg₆]
        exact h9₂
      · simp only [hg₆]
        exact h8₂
      · simp only [hg₆, h11₂]
        rw [← Nat.sub_sub]
        exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
      · rw [hv₆, hv₅, hv₄, hv₃, hv₂, hxm0]
        exact hz0

/-- The loop at `288`, by induction on the bytes left. -/
theorem loop288 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {g₀ : Gprs} {a b : Addr} {n : Nat}
    {P : BitVec 32 → Prop} (hn64 : n < 2 ^ 64) (hpa : Str.StrPg F V a n) (hpb : Str.StrPg F V b n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    ∀ m u k (Y : State) (t : Nat), n - u = m → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 288 →
      InvL g₀ Y.cpu.gpr a b n u k → xsOf Y.cpu.vec.zmm (xmmOf 0) = 0 → u < n → Same V a b u →
      (a.add u).toNat % 16 = 0 → (b.add u).toNat % 16 = 0 → GoG prof L o gev gP gE Y t := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro u k Y t hm hK hA hrip hI hx0 hu hsame hal hbl
  refine half c hin (b288 prof) (b314 prof) (d320 prof.feat) (lt_scm (by decide)) (by decide) (b326 prof)
    (d330 prof.feat) (lt_scm (by decide)) (by decide) (b336 prof) hK hA hrip hI hx0 hn64 hu hsame hpa hpb hal hbl
    hP hR ?_
  intro Z tZ hKZ hAZ hrZ hIZ hxZ huZ hsZ
  have halZ : (a.add (u + 16)).toNat % 16 = 0 := by rw [← addr_add_add]; exact al_add hal (by decide)
  have hblZ : (b.add (u + 16)).toNat % 16 = 0 := by rw [← addr_add_add]; exact al_add hbl (by decide)
  refine half c hin (b340 prof) (b366 prof) (d372 prof.feat) (lt_scm (by decide)) (by decide) (b378 prof)
    (d382 prof.feat) (lt_scm (by decide)) (by decide) (b388 prof) hKZ hAZ hrZ hIZ hxZ hn64 huZ hsZ hpa hpb halZ hblZ
    hP hR ?_
  intro W tW hKW hAW hrW hIW hxW huW hsW
  -- `jmp 288`
  refine c.s_jmpV hKW hAW hin (lt_scm (by decide)) hrW (d392 prof.feat) (by decide) (lt_scm (by decide)) ?_
  rintro X tX hKX hAX ⟨hrX, hgX, hvX⟩
  refine ih (n - (u + 16 + 16)) (by omega) (u + 16 + 16) (k + 16 + 16) X tX rfl hKX hAX hrX (by rw [hgX]; exact hIW)
    (by rw [hvX]; exact hxW) huW hsW ?_ ?_
  · rw [← addr_add_add]
    exact al_add halZ (by decide)
  · rw [← addr_add_add]
    exact al_add hblZ (by decide)

/-- From `192`, the strings' offsets `d` in their 16 bytes the same: the first 16 bytes from `d` on compared, then
the loop. -/
theorem ashr0 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b : Addr} {n q : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 192)
    (hab : a.toNat % 16 = b.toNat % 16) (hL : AtL g₀ Y.cpu.gpr a b n q false)
    (hn64 : n < 2 ^ 64) (hq : q < n) (hsame : Same V a b q) (hpa : Str.StrPg F V a n) (hpb : Str.StrPg F V b n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hkp, hdi0, hdi, hsi0, hsi, h11, hcx, hax, hdx, h8⟩ := hL
  have h80 : Y.cpu.gpr.r8 = 0 := h8
  rw [hab] at hdi hax
  generalize hd : b.toNat % 16 = d at hdi hsi hcx hax
  have hd16 : d < 16 := hd ▸ Nat.mod_lt _ (by decide)
  have hfa : ∀ i < 16, Foot F.data (Y.cpu.gpr.rdi.add i) :=
    foot_chunk hdi0 hd16 (by rw [hdi]; exact pg_of hpa hq fun i hi => (hsame i hi).2)
  have hfb : ∀ i < 16, Foot F.data (Y.cpu.gpr.rsi.add i) :=
    foot_chunk hsi0 hd16 (by
      rw [hsi]
      exact pg_of hpb hq fun i hi h0 => (hsame i hi).2 ((hsame i hi).1.trans h0))
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
  -- `movdqa xmm1, [rsi]; pxor xmm0, xmm0; pcmpeqb xmm0, xmm1; pcmpeqb xmm1, [rdi]; psubb xmm1, xmm0;
  -- pmovmskb r9d, xmm1`
  refine c.s_blkV hin (b192 prof) hK hA hrip ?_
  refine wpV_v hfb' (fun _ => hbl') <| wpV_v0 <| wpV_v0 <| wpV_v hfa' (fun _ => hal') <| wpV_v0 <| wpV_v0 <|
    wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have h9₁ : Y₁.cpu.gpr.r9 = (cmask (rd16 V Y.cpu.gpr.rsi) (rd16 V Y.cpu.gpr.rdi)).setWidth 64 := by
    rw [hg₁]
    simp (disch := decide) only [set_r9n, xset_same, xset_ne, xor_z, heB, heA, cmask, rd16]
  have hdx₁ : Y₁.cpu.gpr.rdx = BitVec.ofNat 64 65535 := by rw [hg₁]; exact hdx
  have hcx₁ : Y₁.cpu.gpr.rcx = BitVec.ofNat 64 d := by rw [hg₁]; exact hcx
  generalize hYb : rd16 V Y.cpu.gpr.rsi = Yb at h9₁
  generalize hXa : rd16 V Y.cpu.gpr.rdi = Xa at h9₁
  have hYl : ∀ j, d ≤ j → j < 16 → lane 8 Yb j = V (b.add (q + (j - d))) := fun j hdj hj => by
    rw [← hYb, lane_rd16 V _ hj, add_shift hsi hdj]
  have hXl : ∀ j, d ≤ j → j < 16 → lane 8 Xa j = V (a.add (q + (j - d))) := fun j hdj hj => by
    rw [← hXa, lane_rd16 V _ hj, add_shift hdi hdj]
  -- `shr edx, cl; shr r9d, cl; sub edx, r9d`
  refine c.s_blkV hin (b217 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  have hdx₂ : Y₂.cpu.gpr.rdx = ((BitVec.ofNat 32 65535 >>> d) - (cmask Yb Xa >>> d)).setWidth 64 := by
    rw [hg₂]
    simp only [wr, gv, Src.val, set_rdx, set_r9n, get2, get_r9n, get1, hcx₁, hdx₁, h9₁, sw_64_32, shr_cnt hd16,
      BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), subR_eq]
  have hz₂ : Y₂.cpu.rflags.zf = decide ((BitVec.ofNat 32 65535 >>> d) - (cmask Yb Xa >>> d) = 0) := by
    rw [hf₂, hfl, subF_zf]
    simp only [wr, gv, Src.val, set_rdx, set_r9n, get2, get_r9n, get1, hcx₁, hdx₁, h9₁, sw_64_32, shr_cnt hd16,
      BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), sub_eq_zero_iff]
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂, hg₁, wr, set_rdx, set_r9n]; exact hkp
  have hdi₂ : Y₂.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₂, hg₁, wr, set_rdx, set_r9n]
  have hsi₂ : Y₂.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₂, hg₁, wr, set_rdx, set_r9n]
  have hcx₂ : Y₂.cpu.gpr.rcx = BitVec.ofNat 64 d := by simp only [hg₂, wr, set_rdx, set_r9n]; exact hcx₁
  have hax₂ : Y₂.cpu.gpr.rax = BitVec.ofNat 64 d := by simp only [hg₂, hg₁, wr, set_rdx, set_r9n]; exact hax
  have h11₂ : Y₂.cpu.gpr.r11 = BitVec.ofNat 64 (n - q) := by simp only [hg₂, hg₁, wr, set_rdx, set_r9n]; exact h11
  have h8₂ : Y₂.cpu.gpr.r8 = 0 := by simp only [hg₂, hg₁, wr, set_rdx, set_r9n]; exact h80
  -- `jne 6165`
  refine c.s_jcc (tgt := 6165) hK₂ hA₂ hin (lt_scm (by decide)) hr₂ (d225 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · -- a stop in the bytes from `d` on
    intro hcc
    rw [cond_5, hz₂] at hcc
    have hne : (BitVec.ofNat 32 65535 >>> d) - (cmask Yb Xa >>> d) ≠ 0 := fun h => by simp [h] at hcc
    have hex : ∃ j < 16 - d, decide (lane 8 Yb (d + j) = lane 8 Xa (d + j) ∧ lane 8 Yb (d + j) ≠ 0) = false := by
      refine Classical.byContradiction fun hn => hne ((shr_sub_zero Yb Xa d).2 fun j hdj hj => ?_)
      have e : d + (j - d) = j := by omega
      rw [← e]
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 Yb (d + (j - d)) = lane 8 Xa (d + (j - d)) ∧ lane 8 Yb (d + (j - d)) ≠ 0)
      · exact absurd ⟨j - d, by omega, h⟩ hn
      · rfl
    obtain ⟨j₀, hj₀, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 Yb (d + j₀) = lane 8 Xa (d + j₀) ∧ lane 8 Yb (d + j₀) ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i, d ≤ i → i < d + j₀ → lane 8 Yb i = lane 8 Xa i ∧ lane 8 Yb i ≠ 0 := fun i h1 h2 => by
      have h := of_decide_eq_true (hpt (i - d) (by omega))
      rwa [show d + (i - d) = i by omega] at h
    obtain ⟨hnz, hlow⟩ := shr_sub_low Yb Xa (c := d) (p := d + j₀) (by omega) (by omega) hpf' hpt'
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    refine exit6165 (ka := d) (kc := d) (q := q) (R := n - q) (p := j₀) (sw := false) (x := a) (y := b) c hin
      hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hax₂) (by rw [hg₃]; exact hcx₂)
      (by rw [hg₃, hdi₂]; exact hdi) (by rw [hg₃, hsi₂]; exact hsi) (by rw [hg₃]; exact h8₂)
      (Or.inl ⟨rfl, rfl, rfl⟩) (by rw [hg₃]; exact h11₂) (by omega) (by omega) (by rw [hg₃, hdx₂]; exact hnz)
      (by rw [hg₃, hdx₂, hlow]; omega) (by omega) ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · intro i hi
      by_cases hiq : i < q
      · exact hsame i hiq
      · have h := hpt' (i - q + d) (by omega) (by omega)
        rw [hYl _ (by omega) (by omega), hXl _ (by omega) (by omega), show q + (i - q + d - d) = i by omega] at h
        exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩
    · refine stop_comm ?_
      rw [show q + j₀ = q + (d + j₀ - d) by omega, ← hYl (d + j₀) (by omega) (by omega),
        ← hXl (d + j₀) (by omega) (by omega)]
      exact hpf'
    · rw [show q + j₀ = q + (d + j₀ - d) by omega, ← add_shift hdi (by omega : d ≤ d + j₀)]
      exact hfa _ (by omega)
    · rw [show q + j₀ = q + (d + j₀ - d) by omega, ← add_shift hsi (by omega : d ≤ d + j₀)]
      exact hfb _ (by omega)
  · -- the bytes from `d` on the same and not 0
    intro hcc
    rw [cond_5, hz₂] at hcc
    have h0 : (BitVec.ofNat 32 65535 >>> d) - (cmask Yb Xa >>> d) = 0 := by simpa using hcc
    have hall := (shr_sub_zero Yb Xa d).1 h0
    have hs : Same V a b (q + (16 - d)) := by
      intro i hi
      by_cases hiq : i < q
      · exact hsame i hiq
      · have h := hall (i - q + d) (by omega) (by omega)
        rw [hYl _ (by omega) (by omega), hXl _ (by omega) (by omega), show q + (i - q + d - d) = i by omega] at h
        exact ⟨h.1.symm, fun h0 => h.2 (h.1.trans h0)⟩
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    -- `lea r9, [rcx + r11 - 16]; cmp r11, r9`
    refine c.s_blkV hin (b231 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ _
    have h9₄ : Y₄.cpu.gpr.r9 = BitVec.ofNat 64 d + BitVec.ofNat 64 (n - q) * BitVec.ofNat 64 1 +
        BitVec.ofNat 64 18446744073709551600 := by
      rw [hg₄]
      simp only [wr, eaG, optV, set_r9n, get1, get11, BitVec.setWidth_eq, hg₃, hcx₂, h11₂]
    have hc2 : Y₄.cpu.rflags.cond 2 = decide (n - q < (BitVec.ofNat 64 d + BitVec.ofNat 64 (n - q) *
        BitVec.ofNat 64 1 + BitVec.ofNat 64 18446744073709551600).toNat) := by
      rw [hf₄, hfl, cond_2, subF_cf]
      simp only [wr, gv, Src.val, eaG, optV, set_r9n, get1, get11, get_r9n, BitVec.setWidth_eq, hg₃, hcx₂, h11₂]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n - q < 2 ^ 64 by omega)]
    have hkp₄ : KpN g₀ Y₄.cpu.gpr := by rw [hg₄, hg₃]; exact hkp₂
    have hdi₄ : Y₄.cpu.gpr.rdi = Y.cpu.gpr.rdi := by rw [hg₄, hg₃]; exact hdi₂
    have hsi₄ : Y₄.cpu.gpr.rsi = Y.cpu.gpr.rsi := by rw [hg₄, hg₃]; exact hsi₂
    have h8₄ : Y₄.cpu.gpr.r8 = 0 := by rw [hg₄, hg₃]; exact h8₂
    -- `jb 6212`
    refine c.s_jcc (tgt := 6212) hK₄ hA₄ hin (lt_scm (by decide)) hr₄ (d239 prof.feat) (by decide)
      (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have hle : n ≤ q + (16 - d) := by
        refine Nat.le_of_not_lt fun hgt => ?_
        rw [hc2, lea_m16 (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show d + (n - q) - 16 < 2 ^ 64 by omega)] at hcc
        exact absurd (of_decide_eq_true hcc) (by omega)
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      exact ret0 c hin hK₅ hA₅ hr₅ (by rw [hg₅]; exact hkp₄) (hP 0 (nres_zero hs hle)) hR
    intro hcc
    have hge : 16 ≤ d + (n - q) := by
      refine Nat.le_of_not_lt fun hw => ?_
      rw [hc2, decide_eq_true (lea_wrap (by omega))] at hcc
      exact absurd hcc (by decide)
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
    have h9₅ : Y₅.cpu.gpr.r9 = BitVec.ofNat 64 (d + (n - q) - 16) := by rw [hg₅, h9₄]; exact lea_m16 hge
    -- `test r9, r9`
    refine c.s_blkV hin (b245 prof) hK₅ hA₅ hr₅ ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ hf₆ _
    have hz₆ : Y₆.cpu.rflags.cond 4 = decide (d + (n - q) - 16 = 0) := by
      rw [hf₆, cond4_log hfl]
      simp only [gv, Src.val, get_r9n, BitVec.setWidth_eq, BitVec.and_self, h9₅]
      exact ofNat_beq_zero (by omega)
    have hg₆' : Y₆.cpu.gpr = Y₄.cpu.gpr := by rw [hg₆, hg₅]
    -- `je 6212`
    refine c.s_jcc (tgt := 6212) hK₆ hA₆ hin (lt_scm (by decide)) hr₆ (d248 prof.feat) (by decide)
      (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have h16 : d + (n - q) - 16 = 0 := by
        rw [hz₆] at hcc
        exact of_decide_eq_true hcc
      rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
      exact ret0 c hin hK₇ hA₇ hr₇ (by rw [hg₇, hg₆']; exact hkp₄) (hP 0 (nres_zero hs (by omega))) hR
    intro hcc
    have hgt : 16 < d + (n - q) := by
      rw [hz₆] at hcc
      have := of_decide_eq_false hcc
      omega
    rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
    -- `mov r11, r9; mov rcx, 16; mov r9, 16; pxor xmm0, xmm0; nop; nop`
    refine c.s_blkV hin (b254 prof) hK₇ hA₇ hr₇ ?_
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 <| wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_nil ?_
    intro Y₈ t₈ hK₈ hA₈ hr₈ hg₈ _ hv₈
    simp only [wr, gv, Src.val, set11, set_rcx, set_r9n, get_r9n, BitVec.setWidth_eq, hg₇, hg₆'] at hg₈
    refine loop288 c hin hn64 hpa hpb hP hR _ (q + (16 - d)) 16 Y₈ t₈ rfl hK₈ hA₈ hr₈
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ (by omega) hs ?_ ?_
    · simp only [KpN, hg₈]
      exact hkp₄
    · simp only [hg₈, hdi₄]
      exact add_shift hdi (by omega)
    · simp only [hg₈, hsi₄]
      exact add_shift hsi (by omega)
    · simp only [hg₈]
    · simp only [hg₈]
    · simp only [hg₈]
      exact h8₄
    · simp only [hg₈, h9₄]
      rw [lea_m16 hge, show d + (n - q) - 16 = n - (q + (16 - d)) by omega]
    · rw [hv₈]
      simp only [xset_same, xor_z]
    · rw [← add_shift hdi (by omega : d ≤ 16)]
      exact al_add hdi0 (by decide)
    · rw [← add_shift hsi (by omega : d ≤ 16)]
      exact al_add hsi0 (by decide)

end FV7z.Strncmp
