import FV7z.Strncmp.AshrB
/-!
# The shifted loops of `__strncmp_sse2`: pages and the end (PLAN.md G3, `strncmp`)

Before each round the loop shifting by `k` adds 16 to `r10` (`add r10, 16; jg`, at `132` and `216`): not taken, the
round's 16 bytes of `rdi`'s string are in the page of the last (`stepS`). Taken, they begin a page, and from `304`
(`crossS`) it first checks that the bytes it still has of `x` (from byte `k` of `xmm3`) are not 0 and that more than
`16 - k` are to be compared: then that page holds a byte of `x` with none 0 before it, and the round goes on at `138`
with `r10` less 4096. Otherwise from `352` (`tailS`) it compares those bytes with `rsi`'s at `6144` (`at6144`) and
leaves by `6160`: a stop among them, or none and no more to compare.

- `RegS`: the loop's registers; `AtG`: what holds at its `jg`.
- `rip_at`: the same place written two ways.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem rip_at {Y : State} {e' : Addr} {i j : Nat} (h : Y.cpu.rip = e'.add i) (he : i = j) :
    Y.cpu.rip = e'.add j := he ▸ h

/-- The registers of the loop shifting by `k` at `rcx = K`, byte `u` of `y` (see `AtB`). -/
structure RegS (g₀ g : Gprs) (x y : Addr) (sw : Bool) (n k u K : Nat) : Prop where
  kp : KpN g₀ g
  di : Addr.add g.rdi K = x.add (u + 16 - k)
  si : Addr.add g.rsi K = y.add u
  cx : g.rcx = BitVec.ofNat 64 K
  r9 : g.r9 = BitVec.ofNat 64 k
  r8 : g.r8 = if sw then BitVec.ofNat 64 65535 else 0
  r11 : g.r11 = BitVec.ofNat 64 (n - u)

/-- At the loop's `jg` (`132` or `216`), `r10` just added to: the last 16 bytes of `rdi`'s at `rdi + K - 16`. -/
structure AtG (g₀ : Gprs) (Y : State) (F : Footprint) (V : Addr → Byte) (x y : Addr) (sw : Bool)
    (n k u K : Nat) : Prop where
  reg : RegS g₀ Y.cpu.gpr x y sw n k u K
  K16 : 16 ≤ K
  r10 : Y.cpu.gpr.r10 =
    BitVec.ofNat 64 (2 ^ 64 - 4096 + (Addr.add Y.cpu.gpr.rdi (K - 16)).toNat % 4096 + k) + BitVec.ofNat 64 16
  jg : Y.cpu.rflags.cond 15 = decide ((Addr.add Y.cpu.gpr.rdi (K - 16)).toNat % 4096 = 4080)
  di0 : (Addr.add Y.cpu.gpr.rdi (K - 16)).toNat % 16 = 0
  si16 : (Addr.add Y.cpu.gpr.rsi K).toNat % 16 = 0
  pg : ∀ z : Addr, z.toNat / 4096 = (Addr.add Y.cpu.gpr.rdi (K - 16)).toNat / 4096 → Foot F.data z
  x0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = 0
  x3 : ∀ i, k ≤ i → i < 16 → lane 8 (xsOf Y.cpu.vec.zmm (xmmOf 3)) i = V (x.add (u + (i - k)))
  hu : u < n
  same : Same V x y u

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `6144`: `pcmpeqb xmm1, xmm3; psubb xmm1, xmm0; pmovmskb edx, xmm1; not edx`, `xmm1` the 16 bytes at byte
`u` of `y`, `xmm3` and `xmm0` the bytes of `x` from `u` and their 0s, lined up; then `6160`. -/
theorem at6144 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b x y : Addr} {sw : Bool} {n k u K : Nat} {P : BitVec 32 → Prop} {Yb X3 : BitVec 128}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 6144)
    (hG : RegS g₀ Y.cpu.gpr x y sw n k u K) (hK16 : 16 ≤ K) (hk : k < 16)
    (hx1 : xsOf Y.cpu.vec.zmm (xmmOf 1) = Yb) (hx3 : xsOf Y.cpu.vec.zmm (xmmOf 3) = X3 >>> (8 * k))
    (hx0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = peqb 0 X3 >>> (8 * k))
    (hYl : ∀ j < 16, lane 8 Yb j = V (y.add (u + j)))
    (hX3 : ∀ i, k ≤ i → i < 16 → lane 8 X3 i = V (x.add (u + (i - k))))
    (hu : u < n) (hsame : Same V x y u) (hend : (∃ j < 16 - k, V (x.add (u + j)) = 0) ∨ n - u ≤ 16 - k)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin (b6144 prof) hK hA hrip ?_
  refine wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hdx : Y₁.cpu.gpr.rdx = (tmask Yb X3 k).setWidth 64 := by
    rw [hg₁]
    simp (disch := decide) only [wr, gv, set_rdx, get2, sw_64_32, xset_same, xset_ne, hx0, hx1, hx3, tmask]
  simp only [wr, set_rdx] at hg₁
  have hG₁ : RegS g₀ Y₁.cpu.gpr x y sw n k u K := by
    rw [hg₁]
    exact ⟨hG.kp, hG.di, hG.si, hG.cx, hG.r9, hG.r8, hG.r11⟩
  have hlY : ∀ j, j + k < 16 → lane 8 Yb j = V (y.add (u + j)) := fun j hj => hYl j (by omega)
  have hlX : ∀ j, j + k < 16 → lane 8 X3 (j + k) = V (x.add (u + j)) := fun j hj => by
    rw [hX3 _ (by omega) hj, Nat.add_sub_cancel]
  have hupto : ∀ m, m + k ≤ 16 → (∀ i < m, lane 8 Yb i = lane 8 X3 (i + k) ∧ lane 8 X3 (i + k) ≠ 0) →
      Same V x y (u + m) := fun m hm ht i hi => by
    by_cases hiu : i < u
    · exact hsame i hiu
    · have h := ht (i - u) (by omega)
      rw [hlY _ (by omega), hlX _ (by omega), show u + (i - u) = i by omega] at h
      exact ⟨h.1.symm, h.2⟩
  by_cases hex : ∃ j < 16 - k, decide (lane 8 Yb j = lane 8 X3 (j + k) ∧ lane 8 X3 (j + k) ≠ 0) = false
  · -- a stop among the bytes of `x` left
    obtain ⟨p, hp, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 Yb p = lane 8 X3 (p + k) ∧ lane 8 X3 (p + k) ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i < p, lane 8 Yb i = lane 8 X3 (i + k) ∧ lane 8 X3 (i + k) ≠ 0 :=
      fun i hi => of_decide_eq_true (hpt i hi)
    obtain ⟨hnz, hlow⟩ := tail_low_stop Yb X3 (by omega) hpf' hpt'
    have hsp : Same V x y (u + p) := hupto p (by omega) hpt'
    refine exit6160 (k₉ := k) (kc := K) (q := u) (R := n - u) (p := p) (sw := sw) (x := x) (y := y) c hin
      hK₁ hA₁ hr₁ hG₁.kp hG₁.r9 hG₁.cx (by omega) (addr_shift hG₁.di (by omega)) hG₁.si hG₁.r8 hxy hG₁.r11
      (by omega) (by omega) (by rw [hdx]; exact hnz) (by rw [hdx]; exact hlow) (by omega) (hsp.mono (by omega))
      (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · rw [← hlY p (by omega), ← hlX p (by omega)]
      exact fun h => hpf' ⟨h.1.symm, h.2⟩
    · exact foot_of hpx (by omega) fun i hi => (hsp i hi).2
    · exact foot_of hpy (by omega) fun i hi h0 => (hsp i hi).2 ((hsp i hi).1.trans h0)
  · -- none: then no more were to be compared
    have hall : ∀ i, i + k < 16 → lane 8 Yb i = lane 8 X3 (i + k) ∧ lane 8 X3 (i + k) ≠ 0 := fun i hi => by
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 Yb i = lane 8 X3 (i + k) ∧ lane 8 X3 (i + k) ≠ 0)
      · exact absurd ⟨i, by omega, h⟩ hex
      · rfl
    obtain ⟨hnz, hge, hlt⟩ := tail_low_none Yb X3 hall
    have hR16 : n - u ≤ 16 - k := by
      rcases hend with ⟨j, hj, h0⟩ | h
      · exact absurd ((hlX j (by omega)).trans h0) (hall j (by omega)).2
      · exact h
    have hsn : Same V x y (u + (n - u)) := hupto (n - u) (by omega) fun i hi => hall i (by omega)
    refine exit6160 (k₉ := k) (kc := K) (q := u) (R := n - u) (p := lowestSetBit ((tmask Yb X3 k).setWidth 64))
      (sw := sw) (x := x) (y := y) c hin hK₁ hA₁ hr₁ hG₁.kp hG₁.r9 hG₁.cx (by omega) (addr_shift hG₁.di (by omega))
      hG₁.si hG₁.r8 hxy hG₁.r11 (by omega) (by omega) (by rw [hdx]; exact hnz) (by rw [hdx]) hlt ?_
      (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hP hR
    rw [Nat.min_eq_right (by omega)]
    exact hsn

/-- From `352`: `movdqa xmm1, [rsi + rcx]; psrldq xmm0, k; psrldq xmm3, k` (in either order), then `6144`. -/
theorem tailS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat}
    {P : BitVec 32 → Prop} {X3 : BitVec 128}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add (cL + 352))
    (hG : RegS g₀ Y.cpu.gpr x y sw n k u K) (hK16 : 16 ≤ K) (hsi16 : (Addr.add Y.cpu.gpr.rsi K).toNat % 16 = 0)
    (hk : k < 16) (hx3 : xsOf Y.cpu.vec.zmm (xmmOf 3) = X3) (hx0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = peqb 0 X3)
    (hX3 : ∀ i, k ≤ i → i < 16 → lane 8 X3 i = V (x.add (u + (i - k))))
    (hu : u < n) (hsame : Same V x y u) (hend : (∃ j < 16 - k, V (x.add (u + j)) = 0) ∨ n - u ≤ 16 - k)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  have hfb : ∀ i < 16, Foot F.data ((y.add u).add i) :=
    foot_chunk (d := 0) (by rw [← hG.si]; exact hsi16) (by decide) (by
      rw [addr_add_zero]
      exact pg_of hpy hu fun i hi h0 => (hsame i hi).2 ((hsame i hi).1.trans h0))
  have heb : VOp.eaBI Y.cpu.gpr 6 1 0 = y.add u := by
    show Y.cpu.gpr.rsi + Y.cpu.gpr.rcx + BitVec.ofNat 64 0 = y.add u
    rw [hG.cx, BitVec.add_zero]
    exact hG.si
  have hfb' : ∀ i < 16, Foot F.data ((VOp.eaBI Y.cpu.gpr 6 1 0).add i) := by rw [heb]; exact hfb
  have hbl' : (VOp.eaBI Y.cpu.gpr 6 1 0).toNat % 16 = 0 := by rw [heb, ← hG.si]; exact hsi16
  have hYl : ∀ j < 16, lane 8 (rd16 V (y.add u)) j = V (y.add (u + j)) := fun j hj => lane_at V y u hj
  rcases A.tail with ⟨hb, hjm⟩ | ⟨hb, he⟩
  · refine c.s_blkV hin hb hK hA hrip ?_
    refine wpV_v hfb' (fun _ => hbl') <| wpV_v0 <| wpV_v0 <| wpV_nil ?_
    intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
    have hg₁' : Y₁.cpu.gpr = Y.cpu.gpr := by rw [hg₁]
    obtain ⟨rel, hd, ht⟩ := hjm
    refine c.s_jmpV (tgt := 6144) hK₁ hA₁ hin (lt_scm (by omega)) hr₁ hd ht (lt_scm (by decide)) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    refine at6144 c hin hK₂ hA₂ hr₂ (by rw [hg₂, hg₁']; exact hG) hK16 hk ?_ ?_ ?_ hYl hX3 hu hsame hend hn64 hxy
      hpx hpy hP hR
    · rw [hv₂, hv₁]
      simp (disch := decide) only [xset_same, xset_ne, heb, rd16]
    · rw [hv₂, hv₁]
      simp (disch := decide) only [xset_same, xset_ne, hx3]
    · rw [hv₂, hv₁]
      simp (disch := decide) only [xset_same, xset_ne, hx0]
  · refine c.s_blkV hin hb hK hA hrip ?_
    refine wpV_v hfb' (fun _ => hbl') <| wpV_v0 <| wpV_v0 <| wpV_reg fun _ _ => wpV_nil ?_
    intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
    have hg₁' : Y₁.cpu.gpr = Y.cpu.gpr := by rw [hg₁]
    refine at6144 c hin hK₁ hA₁ (rip_at hr₁ he) (by rw [hg₁']; exact hG) hK16 hk ?_ ?_ ?_ hYl hX3 hu hsame hend
      hn64 hxy hpx hpy hP hR
    · rw [hv₁]
      simp (disch := decide) only [xset_same, xset_ne, heb, rd16]
    · rw [hv₁]
      simp (disch := decide) only [xset_same, xset_ne, hx3]
    · rw [hv₁]
      simp (disch := decide) only [xset_same, xset_ne, hx0]

/-- From `304`, the round's 16 bytes of `rdi`'s at `rdi + K` beginning a page: `pcmpeqb xmm0, xmm3; pmovmskb edx,
xmm0; test edx, 0x10000 - 2 ^ k; jne 352; cmp r11, 16 - k; jbe 352; pxor xmm0, xmm0; sub r10, 4096; jmp 138`. -/
theorem crossS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat}
    {P : BitVec 32 → Prop} {X3 : BitVec 128}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add (cL + 304))
    (hG : RegS g₀ Y.cpu.gpr x y sw n k u K) (hK16 : 16 ≤ K) (hk : k < 16)
    (h10 : Y.cpu.gpr.r10 = BitVec.ofNat 64 (2 ^ 64 - 4096 + 4080 + k) + BitVec.ofNat 64 16)
    (hw0 : (Addr.add Y.cpu.gpr.rdi K).toNat % 4096 = 0) (hdi16 : (Addr.add Y.cpu.gpr.rdi K).toNat % 16 = 0)
    (hsi16 : (Addr.add Y.cpu.gpr.rsi K).toNat % 16 = 0)
    (hx0 : xsOf Y.cpu.vec.zmm (xmmOf 0) = 0) (hx3 : xsOf Y.cpu.vec.zmm (xmmOf 3) = X3)
    (hX3 : ∀ i, k ≤ i → i < 16 → lane 8 X3 i = V (x.add (u + (i - k))))
    (hu : u < n) (hsame : Same V x y u)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (H138 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
      AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  -- `pcmpeqb xmm0, xmm3; pmovmskb edx, xmm0; test edx, 0x10000 - 2 ^ k`
  refine c.s_blkV hin A.p304 hK hA hrip ?_
  refine wpV_v0 <| wpV_v0 <| wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  have hz : Y₁.cpu.rflags.cond 4 = (pmsk (peqb 0 X3) &&& BitVec.ofNat 32 (65536 - 2 ^ k) == 0) := by
    rw [hf₁, cond4_log hfl]
    simp (disch := decide) only [gv, Src.val, get2, set_rdx, sw_64_32, xset_same, hx0, hx3]
  have hx0₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = peqb 0 X3 := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, hx0, hx3]
  have hx3₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 3) = X3 := by
    rw [hv₁]
    simp (disch := decide) only [xset_ne, hx3]
  simp only [set_rdx] at hg₁
  have hG₁ : RegS g₀ Y₁.cpu.gpr x y sw n k u K := by
    rw [hg₁]
    exact ⟨hG.kp, hG.di, hG.si, hG.cx, hG.r9, hG.r8, hG.r11⟩
  have hdi₁ : Y₁.cpu.gpr.rdi = Y.cpu.gpr.rdi := by rw [hg₁]
  have hsi₁ : Y₁.cpu.gpr.rsi = Y.cpu.gpr.rsi := by rw [hg₁]
  have h10₁ : Y₁.cpu.gpr.r10 = Y.cpu.gpr.r10 := by rw [hg₁]
  -- `jne 352`
  obtain ⟨r₁, hd₁, ht₁⟩ := A.j318
  refine c.s_jccV hK₁ hA₁ hin (lt_scm (by omega)) hr₁ hd₁ ht₁ (lt_scm (by omega)) ?_ ?_
  · -- a 0 among the bytes of `x` left: the end
    intro hcc
    rw [cond_5, ← cond_4, hz] at hcc
    have hne : pmsk (peqb 0 X3) &&& BitVec.ofNat 32 (65536 - 2 ^ k) ≠ 0 := fun h => by
      rw [h] at hcc
      exact absurd hcc (by decide)
    have hend : ∃ j < 16 - k, V (x.add (u + j)) = 0 := by
      refine Classical.byContradiction fun hn => hne ((test_hi X3 (by omega)).2 fun i hki hi h0 =>
        hn ⟨i - k, by omega, ?_⟩)
      rw [← hX3 i hki hi]
      exact h0
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    exact tailS c hin A hcl hK₂ hA₂ hr₂ (by rw [hg₂]; exact hG₁) hK16 (by rw [hg₂, hsi₁]; exact hsi16) hk
      (by rw [hv₂]; exact hx3₁) (by rw [hv₂]; exact hx0₁) hX3 hu hsame (Or.inl hend) hn64 hxy hpx hpy hP hR
  · intro hcc
    rw [cond_5, ← cond_4, hz] at hcc
    have h0 : pmsk (peqb 0 X3) &&& BitVec.ofNat 32 (65536 - 2 ^ k) = 0 := by simpa using hcc
    have hnz3 := (test_hi X3 (by omega)).1 h0
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    -- `cmp r11, 16 - k`
    refine c.s_blkV hin A.p320 hK₂ hA₂ (rip_at hr₂ (by omega)) ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ hv₃
    have hc : Y₃.cpu.rflags.cond 6 = decide (n - u ≤ 16 - k) := by
      rw [hf₃, hfl, cond_6, subF_cf, subF_zf]
      simp only [Src.val, gv, get11, BitVec.setWidth_eq, hg₂, hG₁.r11]
      exact be_ofNat (by omega) (by omega)
    have hg₃' : Y₃.cpu.gpr = Y₁.cpu.gpr := by rw [hg₃, hg₂]
    -- `jbe 352`
    obtain ⟨r₂, hd₂, ht₂⟩ := A.j324
    refine c.s_jccV hK₃ hA₃ hin (lt_scm (by omega)) hr₃ hd₂ ht₂ (lt_scm (by omega)) ?_ ?_
    · intro hcc
      have hle : n - u ≤ 16 - k := by
        rw [hc] at hcc
        exact of_decide_eq_true hcc
      rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
      exact tailS c hin A hcl hK₄ hA₄ hr₄ (by rw [hg₄, hg₃']; exact hG₁) hK16
        (by rw [hg₄, hg₃', hsi₁]; exact hsi16) hk (by rw [hv₄, hv₃, hv₂]; exact hx3₁)
        (by rw [hv₄, hv₃, hv₂]; exact hx0₁) hX3 hu hsame (Or.inr hle) hn64 hxy hpx hpy hP hR
    · intro hcc
      have hgt : 16 - k < n - u := by
        rw [hc] at hcc
        exact Nat.lt_of_not_le (of_decide_eq_false hcc)
      rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
      -- `pxor xmm0, xmm0; sub r10, 4096`
      refine c.s_blkV hin A.p326 hK₄ hA₄ (rip_at hr₄ (by omega)) ?_
      refine wpV_v0 <| wpV_reg fun _ _ => wpV_nil ?_
      intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ hv₅
      simp only [wr, gv, Src.val, get_r10n, set_r10n, BitVec.setWidth_eq, subR_eq, hg₄, hg₃'] at hg₅
      have hx0₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 0) = 0 := by
        rw [hv₅]
        simp only [xset_same, xor_z]
      have hx3₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 3) = X3 := by
        rw [hv₅]
        simp (disch := decide) only [xset_ne, hv₄, hv₃, hv₂, hx3₁]
      -- `jmp 138`
      obtain ⟨r₃, hd₃, ht₃⟩ := A.j337
      refine c.s_jmpV (tgt := cL + 138) hK₅ hA₅ hin (lt_scm (by omega)) hr₅ hd₃ ht₃ (lt_scm (by omega)) ?_
      rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
      have hdi₆ : Y₆.cpu.gpr.rdi = Y.cpu.gpr.rdi := by rw [hg₆, hg₅]; exact hdi₁
      have hsi₆ : Y₆.cpu.gpr.rsi = Y.cpu.gpr.rsi := by rw [hg₆, hg₅]; exact hsi₁
      have hpg : ∀ z : Addr, z.toNat / 4096 = (Addr.add Y.cpu.gpr.rdi K).toNat / 4096 → Foot F.data z := by
        rw [hG.di]
        refine pg_of hpx (by omega) fun i hi => ?_
        by_cases hiu : i < u
        · exact (hsame i hiu).2
        · rw [show i = u + (i - u + k - k) by omega, ← hX3 (i - u + k) (by omega) (by omega)]
          exact hnz3 _ (by omega) (by omega)
      refine H138 Y₆ t₆ hK₆ hA₆ hr₆
        { kp := by rw [hg₆, hg₅]; exact hG₁.kp
          di := by rw [hdi₆]; exact hG.di
          si := by rw [hsi₆]; exact hG.si
          cx := by rw [hg₆, hg₅]; exact hG₁.cx
          r9 := by rw [hg₆, hg₅]; exact hG₁.r9
          r8 := by rw [hg₆, hg₅]; exact hG₁.r8
          r11 := by rw [hg₆, hg₅]; exact hG₁.r11
          r10 := ?_
          K16 := hK16
          di16 := by rw [hdi₆]; exact hdi16
          si16 := by rw [hsi₆]; exact hsi16
          pg := by rw [hdi₆]; exact hpg
          x0 := by rw [hv₆]; exact hx0₅
          x3 := by rw [hv₆, hx3₅]; exact hX3
          hu := hu
          same := hsame }
      rw [hdi₆, hw0, hg₆, hg₅]
      show Y₁.cpu.gpr.r10 - BitVec.ofNat 64 4096 = _
      rw [h10₁, h10]
      exact r10_cross

/-- At the loop's `jg` at `j` (`132` or `216`): on to the round at `j + len`, or to `304`. -/
theorem stepS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e j len : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (hj : JccAt prof 15 j len (cL + 304)) (hjl : j < scm.length)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j)
    (hG : AtG g₀ Y F V x y sw n k u K) (hk : k < 16)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (Hb : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (j + len) →
      AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t')
    (H138 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
      AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hz : Addr.add Y.cpu.gpr.rdi K = (Addr.add Y.cpu.gpr.rdi (K - 16)).add 16 := by
    rw [addr_add_add, Nat.sub_add_cancel hG.K16]
  have hdi16 : (Addr.add Y.cpu.gpr.rdi K).toNat % 16 = 0 := by rw [hz]; exact al_add hG.di0 (by decide)
  obtain ⟨rel, hd, ht⟩ := hj
  refine c.s_jccV hK hA hin hjl hrip hd ht (lt_scm (by omega)) ?_ ?_
  · intro hcc
    rw [hG.jg] at hcc
    have hw := of_decide_eq_true hcc
    rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁, hv₁⟩
    refine crossS c hin A hcl hK₁ hA₁ hr₁ (by rw [hg₁]; exact hG.reg) hG.K16 hk ?_ ?_ ?_ ?_ ?_ ?_ hG.x3 hG.hu
      hG.same hn64 hxy hpx hpy hP hR H138
    · rw [hg₁, hG.r10, hw]
    · rw [hg₁, hz, pg_next hG.di0]
      simp only [hw, ↓reduceIte]
    · rw [hg₁]
      exact hdi16
    · rw [hg₁]
      exact hG.si16
    · rw [hv₁]
      exact hG.x0
    · rw [hv₁]
  · intro hcc
    rw [hG.jg] at hcc
    have hw : ¬ (Addr.add Y.cpu.gpr.rdi (K - 16)).toNat % 4096 = 4080 := of_decide_eq_false hcc
    rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁, hv₁⟩
    refine Hb Y₁ t₁ hK₁ hA₁ hr₁
      { kp := by rw [hg₁]; exact hG.reg.kp
        di := by rw [hg₁]; exact hG.reg.di
        si := by rw [hg₁]; exact hG.reg.si
        cx := by rw [hg₁]; exact hG.reg.cx
        r9 := by rw [hg₁]; exact hG.reg.r9
        r8 := by rw [hg₁]; exact hG.reg.r8
        r11 := by rw [hg₁]; exact hG.reg.r11
        r10 := ?_
        K16 := hG.K16
        di16 := by rw [hg₁]; exact hdi16
        si16 := by rw [hg₁]; exact hG.si16
        pg := ?_
        x0 := by rw [hv₁]; exact hG.x0
        x3 := by rw [hv₁]; exact hG.x3
        hu := hG.hu
        same := hG.same }
    · rw [hg₁, hG.r10, r10_add, hz, pg_next hG.di0]
      simp only [hw, ↓reduceIte]
    · rw [hg₁, hz, pg_same hG.di0 hw]
      exact hG.pg

end FV7z.Strncmp
