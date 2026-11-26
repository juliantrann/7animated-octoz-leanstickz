import FV7z.Strncmp.AshrL
/-!
# The shifted loops of `__strncmp_sse2`: the loop (PLAN.md G3, `strncmp`)

The loop shifting by `k` is two rounds (`138`, `218`; `bodyS`), each followed by a step: after the first,
`add rcx, 16; movdqa xmm3, xmm4; add r10, 16` and the `jg` at `216` (`round138`); after the second,
`add rcx, 16; movdqa xmm3, xmm4; jmp 128`, where `add r10, 16` and the `jg` at `132` (`at128`) lead back to the
first (`round218`). `AtP` is what holds at `128`: `AtG` before `add r10, 16`. `loopS` closes the loop by induction on
the bytes left to compare.

- `jg_at`: the `jg` after `add r10, 16` taken just when the 16 bytes at `z` are the last of their page.
- `blkV_at`: a block from a place written two ways.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem jg_at (f : Rflags) {z : Addr} {k : Nat} (hz : z.toNat % 16 = 0) (hk1 : 1 ≤ k) (hk : k < 16) :
    (addF f (BitVec.ofNat 64 (2 ^ 64 - 4096 + z.toNat % 4096 + k)) (BitVec.ofNat 64 16)).cond 15 =
      decide (z.toNat % 4096 = 4080) :=
  jg_r10 f (Nat.mod_lt _ (by decide)) (by omega) hk1 hk

theorem blkV_at {prof : Profile} {i i' j : Nat} {ops : List VOp} (h : BlkV prof scm i j ops) (he : i = i') :
    BlkV prof scm i' j ops := he ▸ h

/-- At `128` of the loop shifting by `k`, at `rcx = K`: the last 16 bytes of `rdi`'s at `rdi + K - 16`. -/
structure AtP (g₀ : Gprs) (Y : State) (F : Footprint) (V : Addr → Byte) (x y : Addr) (sw : Bool)
    (n k u K : Nat) : Prop where
  reg : RegS g₀ Y.cpu.gpr x y sw n k u K
  K16 : 16 ≤ K
  r10 : Y.cpu.gpr.r10 = BitVec.ofNat 64 (2 ^ 64 - 4096 + (Addr.add Y.cpu.gpr.rdi (K - 16)).toNat % 4096 + k)
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

/-- From `128`: `add r10, 16`, then the `jg` at `132` to the round at `138`, or by `304` to it or the end. -/
theorem at128 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (hk1 : 1 ≤ k) (hk : k < 16)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add (cL + 128))
    (hQ : AtP g₀ Y F V x y sw n k u K)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (H138 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
      AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin A.p128 hK hA hrip ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [wr, gv, Src.val, get_r10n, set_r10n, BitVec.setWidth_eq, addR_eq] at hg₁
  have hdi₁ : Y₁.cpu.gpr.rdi = Y.cpu.gpr.rdi := by rw [hg₁]
  have hsi₁ : Y₁.cpu.gpr.rsi = Y.cpu.gpr.rsi := by rw [hg₁]
  have h10₁ : Y₁.cpu.gpr.r10 = Y.cpu.gpr.r10 + BitVec.ofNat 64 16 := by rw [hg₁]
  refine stepS c hin A hcl A.j132 (lt_scm (by omega)) hK₁ hA₁ hr₁ ?_ hk hn64 hxy hpx hpy hP hR
    (fun Z t' hKZ hAZ hrZ hB => H138 Z t' hKZ hAZ (rip_at hrZ (by omega)) hB) H138
  exact
    { reg := by rw [hg₁]; exact ⟨hQ.reg.kp, hQ.reg.di, hQ.reg.si, hQ.reg.cx, hQ.reg.r9, hQ.reg.r8, hQ.reg.r11⟩
      K16 := hQ.K16
      r10 := by rw [h10₁, hdi₁, hQ.r10]
      jg := by
        rw [hf₁, hfl]
        simp only [gv, Src.val, get_r10n, BitVec.setWidth_eq, hdi₁, hQ.r10]
        exact jg_at _ hQ.di0 hk1 hk
      di0 := by rw [hdi₁]; exact hQ.di0
      si16 := by rw [hsi₁]; exact hQ.si16
      pg := by rw [hdi₁]; exact hQ.pg
      x0 := by rw [hv₁]; exact hQ.x0
      x3 := by rw [hv₁]; exact hQ.x3
      hu := hQ.hu
      same := hQ.same }

/-- The round at `138`, then `add rcx, 16; movdqa xmm3, xmm4; add r10, 16` and the `jg` at `216`: on to the round
at `218`, or by `304` to the one at `138` or the end, `16` bytes on. -/
theorem round138 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (hk1 : 1 ≤ k) (hk : k < 16)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add (cL + 138))
    (hB : AtB g₀ Y F V x y sw n k u K)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (H218 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 218) →
      AtB g₀ Z F V x y sw n k (u + 16) (K + 16) → GoG prof L o gev gP gE Z t')
    (H138 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
      AtB g₀ Z F V x y sw n k (u + 16) (K + 16) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine bodyS c hin A.p138 A.p166 A.j188 (lt_scm (by omega)) (blkV_at A.p194 (by omega)) A.j198
    (lt_scm (by omega)) hK hA hrip hB hk hn64 hxy hpx hpy hP hR ?_
  intro Z tZ hKZ hAZ hrZ hkpZ hdiZ hsiZ hcxZ h9Z h8Z h10Z h11Z hx0Z hx4Z huZ hsZ
  -- `add rcx, 16; movdqa xmm3, xmm4; add r10, 16`
  refine c.s_blkV hin A.p204 hKZ hAZ (rip_at hrZ (by omega)) ?_
  refine wpV_reg fun _ _ => wpV_v0 <| wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  have hjg : Y₁.cpu.rflags.cond 15 = decide ((Addr.add Y.cpu.gpr.rdi K).toNat % 4096 = 4080) := by
    rw [hf₁, hfl]
    simp only [wr, gv, Src.val, get1, get_r10n, set_rcx, BitVec.setWidth_eq, h10Z, hB.r10]
    exact jg_at _ hB.di16 hk1 hk
  simp only [wr, gv, Src.val, get1, get_r10n, set_rcx, set_r10n, BitVec.setWidth_eq, addR_eq] at hg₁
  have hkp₁ : KpN g₀ Y₁.cpu.gpr := by simp only [KpN, hg₁]; exact hkpZ
  have hdi₁ : Y₁.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₁, hdiZ]
  have hsi₁ : Y₁.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₁, hsiZ]
  have hcx₁ : Y₁.cpu.gpr.rcx = BitVec.ofNat 64 (K + 16) := by
    simp only [hg₁, hcxZ, hB.cx]
    exact BitVec.ofNat_add_ofNat _ _
  have h9₁ : Y₁.cpu.gpr.r9 = Y.cpu.gpr.r9 := by simp only [hg₁, h9Z]
  have h8₁ : Y₁.cpu.gpr.r8 = Y.cpu.gpr.r8 := by simp only [hg₁, h8Z]
  have h10₁ : Y₁.cpu.gpr.r10 = Y.cpu.gpr.r10 + BitVec.ofNat 64 16 := by simp only [hg₁, h10Z]
  have h11₁ : Y₁.cpu.gpr.r11 = BitVec.ofNat 64 (n - (u + 16)) := by simp only [hg₁]; exact h11Z
  have h3₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 3) = xsOf Z.cpu.vec.zmm (xmmOf 4) := by
    rw [hv₁]
    simp only [xset_same]
  have hx0₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = 0 := by
    rw [hv₁]
    simp (disch := decide) only [xset_ne, hx0Z]
  refine stepS c hin A hcl A.j216 (lt_scm (by omega)) hK₁ hA₁ hr₁ ?_ hk hn64 hxy hpx hpy hP hR
    (fun W tW hKW hAW hrW hBW => H218 W tW hKW hAW (rip_at hrW (by omega)) hBW) H138
  exact
    { reg :=
        { kp := hkp₁
          di := by rw [hdi₁]; exact addr_shift hB.di (by omega)
          si := by rw [hsi₁]; exact addr_shift hB.si (by omega)
          cx := hcx₁
          r9 := by rw [h9₁]; exact hB.r9
          r8 := by rw [h8₁]; exact hB.r8
          r11 := h11₁ }
      K16 := by omega
      r10 := by rw [h10₁, hdi₁, Nat.add_sub_cancel, hB.r10]
      jg := by rw [hjg, hdi₁, Nat.add_sub_cancel]
      di0 := by rw [hdi₁, Nat.add_sub_cancel]; exact hB.di16
      si16 := by rw [hsi₁, ← addr_add_add]; exact al_add hB.si16 (by decide)
      pg := by rw [hdi₁, Nat.add_sub_cancel]; exact hB.pg
      x0 := hx0₁
      x3 := by rw [h3₁]; exact hx4Z
      hu := huZ
      same := hsZ }

/-- The round at `218`, then `add rcx, 16; movdqa xmm3, xmm4; jmp 128`, and `at128`: on to the round at `138`,
`16` bytes on. -/
theorem round218 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (he : e ≤ 4) (hk1 : 1 ≤ k) (hk : k < 16)
    {Y : State} {t : Nat} {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n u K : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add (cL + 218))
    (hB : AtB g₀ Y F V x y sw n k u K)
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (H138 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
      AtB g₀ Z F V x y sw n k (u + 16) (K + 16) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine bodyS c hin A.p218 A.p246 A.j268 (lt_scm (by omega)) (blkV_at A.p274 (by omega)) A.j278
    (lt_scm (by omega)) hK hA hrip hB hk hn64 hxy hpx hpy hP hR ?_
  intro Z tZ hKZ hAZ hrZ hkpZ hdiZ hsiZ hcxZ h9Z h8Z h10Z h11Z hx0Z hx4Z huZ hsZ
  -- `add rcx, 16; movdqa xmm3, xmm4`
  refine c.s_blkV hin A.p284 hKZ hAZ (rip_at hrZ (by omega)) ?_
  refine wpV_reg fun _ _ => wpV_v0 <| wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, get1, set_rcx, BitVec.setWidth_eq, addR_eq] at hg₁
  -- `jmp 128`
  obtain ⟨r, hd, ht⟩ := A.j292
  refine c.s_jmpV (tgt := cL + 128) hK₁ hA₁ hin (lt_scm (by omega)) hr₁ hd ht (lt_scm (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂, hg₁]; exact hkpZ
  have hdi₂ : Y₂.cpu.gpr.rdi = Y.cpu.gpr.rdi := by simp only [hg₂, hg₁, hdiZ]
  have hsi₂ : Y₂.cpu.gpr.rsi = Y.cpu.gpr.rsi := by simp only [hg₂, hg₁, hsiZ]
  have hcx₂ : Y₂.cpu.gpr.rcx = BitVec.ofNat 64 (K + 16) := by
    simp only [hg₂, hg₁, hcxZ, hB.cx]
    exact BitVec.ofNat_add_ofNat _ _
  have h9₂ : Y₂.cpu.gpr.r9 = Y.cpu.gpr.r9 := by simp only [hg₂, hg₁, h9Z]
  have h8₂ : Y₂.cpu.gpr.r8 = Y.cpu.gpr.r8 := by simp only [hg₂, hg₁, h8Z]
  have h10₂ : Y₂.cpu.gpr.r10 = Y.cpu.gpr.r10 := by simp only [hg₂, hg₁, h10Z]
  have h11₂ : Y₂.cpu.gpr.r11 = BitVec.ofNat 64 (n - (u + 16)) := by simp only [hg₂, hg₁]; exact h11Z
  have h3₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 3) = xsOf Z.cpu.vec.zmm (xmmOf 4) := by
    rw [hv₂, hv₁]
    simp only [xset_same]
  have hx0₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 0) = 0 := by
    rw [hv₂, hv₁]
    simp (disch := decide) only [xset_ne, hx0Z]
  refine at128 c hin A hcl hk1 hk hK₂ hA₂ hr₂ ?_ hn64 hxy hpx hpy hP hR H138
  exact
    { reg :=
        { kp := hkp₂
          di := by rw [hdi₂]; exact addr_shift hB.di (by omega)
          si := by rw [hsi₂]; exact addr_shift hB.si (by omega)
          cx := hcx₂
          r9 := by rw [h9₂]; exact hB.r9
          r8 := by rw [h8₂]; exact hB.r8
          r11 := h11₂ }
      K16 := by omega
      r10 := by rw [h10₂, hdi₂, Nat.add_sub_cancel]; exact hB.r10
      di0 := by rw [hdi₂, Nat.add_sub_cancel]; exact hB.di16
      si16 := by rw [hsi₂, ← addr_add_add]; exact al_add hB.si16 (by decide)
      pg := by rw [hdi₂, Nat.add_sub_cancel]; exact hB.pg
      x0 := hx0₂
      x3 := by rw [h3₂]; exact hx4Z
      hu := huZ
      same := hsZ }

/-- The loop shifting by `k`, by induction on the bytes left: from either round, what is returned is what `strncmp`
of `a`, `b`, `n` may return. -/
theorem loopS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {k cL e : Nat} (A : AshrC prof k cL e)
    (hcl : cL + 368 ≤ 6144) (he : e ≤ 4) (hk1 : 1 ≤ k) (hk : k < 16)
    {g₀ : Gprs} {a b x y : Addr} {sw : Bool} {n : Nat} {P : BitVec 32 → Prop}
    (hn64 : n < 2 ^ 64) (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (hpx : Str.StrPg F V x n) (hpy : Str.StrPg F V y n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    ∀ m u, n - u ≤ m →
      (∀ Z t' K, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 138) →
        AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t') ∧
      (∀ Z t' K, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add (cL + 218) →
        AtB g₀ Z F V x y sw n k u K → GoG prof L o gev gP gE Z t') := by
  intro m
  induction m with
  | zero =>
    intro u hm
    exact ⟨fun _ _ _ _ _ _ hB => absurd hB.hu (by omega), fun _ _ _ _ _ _ hB => absurd hB.hu (by omega)⟩
  | succ m ih =>
    intro u hm
    refine ⟨fun Z t' K hKZ hAZ hrZ hB => ?_, fun Z t' K hKZ hAZ hrZ hB => ?_⟩
    · have hu := hB.hu
      exact round138 c hin A hcl hk1 hk hKZ hAZ hrZ hB hn64 hxy hpx hpy hP hR
        ((ih (u + 16) (by omega)).2 · · (K + 16)) ((ih (u + 16) (by omega)).1 · · (K + 16))
    · have hu := hB.hu
      exact round218 c hin A hcl he hk1 hk hKZ hAZ hrZ hB hn64 hxy hpx hpy hP hR
        ((ih (u + 16) (by omega)).1 · · (K + 16))

end FV7z.Strncmp
