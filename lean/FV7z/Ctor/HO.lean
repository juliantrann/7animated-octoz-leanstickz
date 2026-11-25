import FV7z.Ctor.Spec
import FV7z.Ctor.AtCtor
/-!
# `at_ctor` for `spec V hi` and `Gs` (PLAN.md §M, constructors)

`CEnv`: what the constructors not `Done` need of the start, besides the invariant: the code, the writable bytes
(`.data`/`.bss` up to `0x7a86c0`, the stack's frames between the heap's top `hi` and `sp - 64`), the readable ones,
the layout `8029928 ≤ fb`, `fb + 64 ≤ hi`, `hi + 1024 ≤ sp`, and the tables the constructors `82`, `87` read.

`oN`: the constructor `N` runs for `Jg V sp (spec V hi) (Gs … 1 k)`, from its `*_jg` and the step `gN` of `Gs`.
`hO_of`: all those not `Done`. `at_ctor_gs`: `AtCtor` from `CEnv`, `Gs … 3 V` and the run from `main` on.
-/
namespace FV7z.Ctor

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Mal FV7z.Prepare

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- What the constructors not `Done` need of the start. -/
structure CEnv (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (sp fb : Addr) (hi : Nat) : Prop where
  c : Seg prof F Wl L s₀ o
  hC : Csu.Env F Wl L sp csuTg
  hin : CodeIn L sti_at sti
  hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r)
  hinR : ∀ r, CodeIn L (regAt r) (regCode r)
  hP : PEnv prof F Wl s₀ sp
  hfs : s₀.cpu.seg.fsBase = fb
  hU : InsOK 95 gP gE
  hrs : s₀.thread.rseq = none
  hCe : Glibc.CacheEnds prof
  hfb : 8029928 ≤ fb.toNat
  hfh : fb.toNat + 64 ≤ hi
  hhs : hi + 1024 ≤ sp.toNat
  hW : ∀ a : Addr, 7938048 ≤ a.toNat → a.toNat < 8029888 → Foot Wl a
  hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < sp.toNat - 64 → Foot Wl a
  hst72 : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8) i)
  hst80 : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8 - 8) i)
  hRo : ∀ a : Addr, 7176192 ≤ a.toNat → a.toNat < 7822313 → Foot F.data a
  hRw : ∀ a : Addr, 7938048 ≤ a.toNat → a.toNat < 8029888 → Foot F.data a
  hft : ∀ i < 56, Foot F.data (Addr.add fb i)
  hcn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  hld : ∀ i < 200, Foot F.data (Addr.add (sp - 256#64) i)
  hSb : ∀ y, Foot [canary s₀, ⟨0x6d8040, 256⟩] y → Foot F.writes y ∨ Foot F.reads y
  hTb : C82.Tb V
  hT3 : C87.T3 V
  i3 : CodeIn L C3.c3_at C3.c3
  i15 : CodeIn L C15.c15_at C15.c15
  i78 : CodeIn L C78.c78_at C78.c78
  iF17 : CodeIn L cf17_at cf17
  iU17 : CodeIn L umk_at umk
  iLz : CodeIn L 0x427de0 lz
  iSse41 : CodeIn L 0x424390 sse41
  iAvx2 : CodeIn L 0x4244b0 avx2
  iAvx : CodeIn L 0x424440 avx
  iMaxf : CodeIn L 0x4242b0 maxf
  iCpuid : CodeIn L 0x424290 cpuid
  iSha1p : CodeIn L 0x43a740 sha1p
  iSha : CodeIn L 0x4243e0 sha
  iSsse3 : CodeIn L 0x424340 ssse3
  iSha256p : CodeIn L 0x43b3e0 sha256p
  iAesg : CodeIn L 0x41e540 aesg
  iAes : CodeIn L 0x4242f0 aes
  iVaes : CodeIn L 0x4245a0 vaes
  iB2s : CodeIn L 0x422a20 b2s
  iSwap : CodeIn L 0x43d3d0 swap
  iMxs : CodeIn L Mxs.mxs_at Mxs.mxs
  iMxi : CodeIn L Mxi.mxi_at Mxi.mxi
  iCxa : CodeIn L Cxa.cxa_at Cxa.cxa
  iNef : CodeIn L Nef.nef_at Nef.nef
  iOin : CodeIn L Oin.oin_at Oin.oin
  iNst : CodeIn L Nst.nst_at Nst.nst
  iOnw : CodeIn L Onw.onw_at Onw.onw
  iMnx : CodeIn L Mnx.mnx_at Mnx.mnx
  iImm : CodeIn L Imm.imm_at Imm.imm
  iHca : CodeIn L Hca.hca_at Hca.hca

variable {V : Addr → Byte} {sp fb : Addr} {hi k : Nat} {a₀ a₁ a₂ : BitVec 64}

section env
variable (E : CEnv prof F Wl L s₀ o gP gE V sp fb hi)
include E

theorem CEnv.lay : 8029928 ≤ fb.toNat ∧ fb.toNat + 64 ≤ hi ∧ hi + 1024 ≤ sp.toNat ∧ sp.toNat < 2 ^ 64 :=
  ⟨E.hfb, E.hfh, E.hhs, sp.isLt⟩

theorem CEnv.hhi : 8029888 ≤ hi := by
  have := E.lay
  omega

/-- Bytes of `.data`/`.bss` that may be stored. -/
theorem CEnv.w {C n : Nat} (h1 : 7938048 ≤ C) (h2 : C + n ≤ 8029888) :
    ∀ i < n, Foot Wl (Addr.add (BitVec.ofNat 64 C) i) := fun i hj => by
  have e := ofNat_add_toNat (x := C) hj (by omega)
  exact E.hW _ (by rw [e]; omega) (by rw [e]; omega)

/-- Bytes of `.data`/`.bss` that may be read. -/
theorem CEnv.rw {C n : Nat} (h1 : 7938048 ≤ C) (h2 : C + n ≤ 8029888) :
    ∀ i < n, Foot F.data (Addr.add (BitVec.ofNat 64 C) i) := fun i hj => by
  have e := ofNat_add_toNat (x := C) hj (by omega)
  exact E.hRw _ (by rw [e]; omega) (by rw [e]; omega)

/-- Bytes of `.rodata` that may be read. -/
theorem CEnv.ro {C n : Nat} (h1 : 7176192 ≤ C) (h2 : C + n ≤ 7822313) :
    ∀ i < n, Foot F.data (Addr.add (BitVec.ofNat 64 C) i) := fun i hj => by
  have e := ofNat_add_toNat (x := C) hj (by omega)
  exact E.hRo _ (by rw [e]; omega) (by rw [e]; omega)

/-- Bytes of the stack's frames below `sp - 64` that may be stored. -/
theorem CEnv.st {j n : Nat} (hn : n + 64 ≤ j) (hj : j ≤ 1024) :
    ∀ i < n, Foot Wl (Addr.add (sp - BitVec.ofNat 64 j) i) := fun i hi' => by
  have hL := E.lay
  have e := subk_toNat (D := sp) (k := j) (by omega)
  have e2 : (Addr.add (sp - BitVec.ofNat 64 j) i).toNat = sp.toNat - j + i := by
    rw [toNat_add_of_fits (n := n) hi' (by rw [e]; omega), e]
  exact E.hsw _ (by rw [e2]; omega) (by rw [e2]; omega)

theorem CEnv.fb40 : (fb + 40#64).toNat = fb.toNat + 40 := by
  have := E.lay
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end env

theorem Gs.cx {n₀ m : Nat} {W : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) : CxPre fb xl (nOf n₀ m) W := by
  unfold Gs Gn at h
  exact h.2.1

theorem Gs.hp {n₀ m : Nat} {W : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) : Hp F Wl fb hi (kOf k m) W := by
  unfold Gs Gn at h
  exact h.2.2

/-- The invariant of the constructors. -/
abbrev JG (V : Addr → Byte) (sp : Addr) (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi k : Nat) :=
  Jg V sp.toNat (spec V hi) (Gs F Wl fb hi 1 k)

section runs
variable (E : CEnv prof F Wl L s₀ o gP gE V sp fb hi) (hk : 16 ≤ k)
include E hk

theorem o3 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 3 (csuTg 3) := by
  have hL := E.lay
  exact C3.runs3_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hinE := E.i3) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 3) (by decide))
    (hG := g3 (by decide) hk)

theorem o15 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 15 (csuTg 15) := by
  have hL := E.lay
  exact C15.runs15_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hinE := E.i15) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 15) (by decide))
    (hG := g15 (by decide) hk)

theorem o37 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 37 (csuTg 37) := by
  have hL := E.lay
  exact C37.runs37_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hR := E.hR 0) (hinR := E.hinR 0) (hspec := rfl) (hD := spec_dep) (hT := spec_T)
    (hXw := spec_Xw (m := 37) (by decide)) (hG := g37 (by decide) hk)

theorem o55 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 55 (csuTg 55) := by
  have hL := E.lay
  exact C55.runs55_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hR := E.hR 0) (hinR := E.hinR 0) (hspec := rfl) (hD := spec_dep) (hT := spec_T)
    (hXw := spec_Xw (m := 55) (by decide)) (hG := g55 (by decide) hk)

theorem o61 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 61 (csuTg 61) := by
  have hL := E.lay
  exact C61.runs61_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hR := E.hR 0) (hinR := E.hinR 0) (hspec := rfl) (hD := spec_dep) (hT := spec_T)
    (hXw := spec_Xw (m := 61) (by decide)) (hG := g61 (by decide) hk)

theorem o70 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 70 (csuTg 70) := by
  have hL := E.lay
  exact C70.runs70_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 70) (by decide))
    (hG := g70 (by decide) hk)

theorem o75 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 75 (csuTg 75) := by
  have hL := E.lay
  exact C75.runs75_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 75) (by decide))
    (hG := g75 (by decide) hk)

theorem o78 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 78 (csuTg 78) := by
  have hL := E.lay
  exact C78.runs78_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hinE := E.i78) (hw := E.w (by decide) (by decide))
    (hsp := by omega) (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 78) (by decide))
    (hG := g78 (by decide) hk)

theorem o82 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 82 (csuTg 82) := by
  have hL := E.lay
  exact C82.runs82_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hS := by omega)
    (hw := E.w (by decide) (by decide)) (hstk := E.hst72) (hF1 := E.ro (by decide) (by decide))
    (hF2 := E.ro (by decide) (by decide)) (hF3 := E.ro (by decide) (by decide)) (hTV := E.hTb) (hspec := rfl)
    (hD := spec_dep) (hB := spec_B E.hhi E.hhs) (hlo := fun k x hx => by have := spec_lo k x hx; omega)
    (hXw := spec_Xw (m := 82) (by decide)) (hG := g82 (by decide) hk E.hhs)

theorem o87 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 87 (csuTg 87) := by
  have hL := E.lay
  exact C87.runs87_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hS := by omega)
    (hw := E.w (by decide) (by decide)) (hF3 := E.ro (by decide) (by decide))
    (hF4 := E.ro (by decide) (by decide)) (hTV := E.hT3) (hspec := rfl) (hD := spec_dep)
    (hlo := fun k x hx => by have := spec_lo k x hx; omega)
    (hXw := spec_Xw (m := 87) (by decide)) (hG := g87 (by decide) hk)

theorem o5 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 5 (csuTg 5) :=
  runs5_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hinE := E.iLz) (hinS := E.iSse41)
    (hinA2 := E.iAvx2) (hinA := E.iAvx) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w5, InR] at h
      exact E.hW y (by omega) (by omega))
    (hspec := rfl) (hD := spec_dep) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 5) (by decide))
    (hG := fun _ _ _ _ ho _ h => gB (by decide) hk E.hhs hw5 ⟨by simp [nOf], by simp [kOf]⟩ ho h)

theorem o7 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 7 (csuTg 7) :=
  runs7_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hinE := E.iSha1p) (hinH := E.iSha)
    (hinS := E.iSsse3) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w7, InR] at h
      exact E.hW y (by omega) (by omega))
    (hspec := rfl) (hD := spec_dep) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 7) (by decide))
    (hG := fun _ _ _ _ ho _ h => gB (by decide) hk E.hhs hw7 ⟨by simp [nOf], by simp [kOf]⟩ ho h)

theorem o9 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 9 (csuTg 9) :=
  runs9_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hinE := E.iSha256p) (hinH := E.iSha)
    (hinS := E.iSsse3) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w9, InR] at h
      exact E.hW y (by omega) (by omega))
    (hspec := rfl) (hD := spec_dep) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 9) (by decide))
    (hG := fun _ _ _ _ ho _ h => gB (by decide) hk E.hhs hw9 ⟨by simp [nOf], by simp [kOf]⟩ ho h)

theorem o92 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 92 (csuTg 92) := by
  have hL := E.lay
  exact runs92_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hinE := E.iAesg) (hinA := E.iAes)
    (hinV := E.iVaes) (hinX := E.iAvx) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w92, InR] at h
      exact E.hW y (by omega) (by omega))
    (hSb := E.hSb) (hS92 := by omega)
    (hspec := rfl) (hD := spec_dep) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 92) (by decide))
    (hG := fun _ _ _ _ ho _ h => gB (by decide) hk E.hhs hw92 ⟨by simp [nOf], by simp [kOf]⟩ ho h)

theorem o67 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 67 (csuTg 67) :=
  runs67_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hR := E.hR) (hinR := E.hinR) (hinE := E.iB2s)
    (hinS := E.iSse41) (hinA2 := E.iAvx2) (hinA := E.iAvx) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hst := E.hst80)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w67, InR] at h
      exact E.hW y (by omega) (by omega))
    (hspec := rfl) (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs)
    (hXw := spec_Xw (m := 67) (by decide))
    (hG := fun _ _ _ _ hc _ ho _ h => g67 (by decide) hk E.hhs hc ho h)

theorem o77 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 77 (csuTg 77) :=
  runs77_jg (c := E.c) (hC := E.hC) (hP := E.hP) (hin := E.hin) (hR := E.hR) (hinR := E.hinR) (hinE := E.iSwap)
    (hinS := E.iSsse3) (hinA2 := E.iAvx2) (hinA := E.iAvx) (hinM := E.iMaxf) (hinC := E.iCpuid)
    (hst := E.hst80)
    (hWl := fun y hy => by
      have h := foot_wrOf hy
      simp [wrOf, w77, InR] at h
      exact E.hW y (by omega) (by omega))
    (hspec := rfl) (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs)
    (hXw := spec_Xw (m := 77) (by decide))
    (hG := fun _ _ _ _ _ ho _ hc h => g77 (by decide) hk E.hhs ho hc h)

theorem o96 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 96 (csuTg 96) := by
  have hL := E.lay
  exact runs96_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hl := E.rw (by decide) (by decide))
    (hw8 := E.w (by decide) (by decide)) (hw4 := E.w (by decide) (by decide)) (hsp := by omega)
    (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 96) (by decide)) (hXr := spec_R96)
    (hG := g96 (by decide) hk)

theorem o97 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 97 (csuTg 97) := by
  have hL := E.lay
  exact runs97_jg (c := E.c) (hC := E.hC) (hin := E.hin) (hl1 := E.rw (by decide) (by decide))
    (hl2 := E.rw (by decide) (by decide)) (hw := E.w (by decide) (by decide)) (hsp := by omega)
    (hspec := rfl) (hD := spec_dep) (hXw := spec_Xw (m := 97) (by decide)) (hXr := spec_R97)
    (hG := g97 (by decide) hk)

theorem o17 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 17 (csuTg 17) := by
  have hL := E.lay
  exact c17_jg (hU := E.hU) (hrs := E.hrs) (c := E.c) (hC := E.hC) (hin := E.hin) (hinF := E.iF17)
    (hinU := E.iU17) (hs72 := E.st (by decide) (by decide)) (hs80 := E.st (by decide) (by decide))
    (hgw := E.w (by decide) (by decide)) (hS := by omega) (hspec := rfl) (hD := spec_dep)
    (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 17) (by decide)) (hG := g17 (by decide) hk E.hhs)

theorem o90 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 90 (csuTg 90) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact c90_jg (m := 90) (n := 1) (l := xl) (ex := exH hi) (c := E.c) (hC := E.hC) (hin := E.hin)
    (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa) (hinN := E.iNef) (htg := tg90)
    (hst := E.st (by decide) (by decide)) (hS := by omega) (hft := E.hft) (hfn := by omega)
    (hfsd := by omega) (hfO := by omega) (hfld := by omega) (hfcd := by omega)
    (hfl := E.rw (by decide) (by decide)) (hp := E.rw (by decide) (by decide)) (hl0 := by omega)
    (hn := by decide) (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega)
    (hkw := E.w (by decide) (by decide)) (hlc := by omega) (hmw := E.w (by decide) (by decide))
    (hob := E.w (by decide) (by decide)) (hm := by decide) (hc := by decide +kernel) (hspec := rfl)
    (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_X90)
    (hGx := fun _ h => h.cx)
    (hG := fun _ _ _ _ _ h hv hR₁ hmo hR₂ => g90 (by decide) hk E.hhs h hv hR₁ hmo hR₂)

theorem o94 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 94 (csuTg 94) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact c94_jg (m := 94) (n := 3) (k₀ := 90) (l := xl) (c := E.c) (hC := E.hC) (hin := E.hin)
    (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa) (hinN := E.iNef) (htg := tg94)
    (hst := E.st (by decide) (by decide)) (hS := by omega) (hft := E.hft) (hfn := by omega)
    (hfsd := by omega) (hfM := by omega) (hfld := by omega) (hfcd := by omega)
    (hfl := E.rw (by decide) (by decide)) (hp := E.rw (by decide) (by decide)) (hl0 := by omega)
    (hn := by decide) (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega)
    (hkw := E.w (by decide) (by decide)) (hlc := by omega) (hm1 := E.w (by decide) (by decide))
    (hb := E.w (by decide) (by decide)) (hm := by decide) (hc := by decide +kernel) (hspec := rfl)
    (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 94) (by decide))
    (hk₀ := by decide) (hk₀m := by decide) (hSh := fun x h => spec_Sh x (InR_append_left h))
    (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 94) (by decide) k h1 h2 h3 x hx (InR_append_left h))
    (hGx := fun _ h => h.cx) (hG := fun _ _ _ h hv hR => g94 (by decide) hk E.hhs h hv hR)

theorem o95 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 95 (csuTg 95) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact c95_jg (m := 95) (n := 4) (k₀ := 90) (l := xl) (c := E.c) (hC := E.hC) (hin := E.hin)
    (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa) (hinN := E.iNef) (hinO := E.iOin)
    (htg := tg95) (hst := E.st (by decide) (by decide)) (hS := by omega) (hft := E.hft) (hfn := by omega)
    (hfsd := by omega) (hfO := by omega) (hfld := by omega) (hfcd := by omega)
    (hfl := E.rw (by decide) (by decide)) (hp := E.rw (by decide) (by decide)) (hl0 := by omega)
    (hn := by decide) (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega)
    (hkw := E.w (by decide) (by decide)) (hlc := by omega) (hmw := E.w (by decide) (by decide))
    (hw := E.w (by decide) (by decide)) (hm := by decide) (hc := by decide +kernel) (hspec := rfl)
    (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 95) (by decide))
    (hk₀ := by decide) (hk₀m := by decide) (hSh := fun x h => spec_Sh x (InR_append_left h))
    (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 95) (by decide) k h1 h2 h3 x hx (InR_append_left h))
    (hGx := fun _ h => h.cx)
    (hG := fun _ _ _ _ _ h hv hR₁ hmo hR₂ => g95 (by decide) hk E.hhs h hv hR₁ hmo hR₂)

theorem o99 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 99 (csuTg 99) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact c99_jg (m := 99) (n := 7) (k₀ := 90) (l := xl) (c := E.c) (hC := E.hC) (hin := E.hin)
    (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa) (hinN := E.iNef) (htg := tg99)
    (hst := E.st (by decide) (by decide)) (hS := by omega) (hft := E.hft) (hfn := by omega)
    (hfsd := by omega) (hfM := by omega) (hfld := by omega) (hfcd := by omega)
    (hfl := E.rw (by decide) (by decide)) (hp := E.rw (by decide) (by decide)) (hl0 := by omega)
    (hn := by decide) (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega)
    (hkw := E.w (by decide) (by decide)) (hlc := by omega) (hm1 := E.w (by decide) (by decide))
    (hm2 := E.w (by decide) (by decide)) (hm := by decide) (hc := by decide +kernel) (hspec := rfl)
    (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 99) (by decide))
    (hk₀ := by decide) (hk₀m := by decide) (hSh := fun x h => spec_Sh x (InR_append_left h))
    (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 99) (by decide) k h1 h2 h3 x hx (InR_append_left h))
    (hGx := fun _ h => h.cx)
    (hG := fun _ _ _ _ _ h hv hR₁ hmo hR₂ => g99 (by decide) hk E.hhs h hv hR₁ hmo hR₂)

theorem o100 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 100 (csuTg 100) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact mc_jg (m := 100) (j := 3088) (M := 7991456) (D := 5875232) (n := 9) (k₀ := 90) (l := xl) (c := E.c)
    (hC := E.hC) (hin := E.hin) (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa)
    (hinN := E.iNef) (htg := tg100) (hpro := pb3088 prof) (hlea := lb3088 prof) (hcd := cd3088 prof.feat)
    (htc := by decide +kernel) (htl := tb3088 prof) (hjd := jd3088 prof.feat) (htj := by decide +kernel)
    (hj := by rw [sti_length]; decide) (hst := E.st (by decide) (by decide)) (hS := by omega)
    (hM0 := by decide) (hMg := by decide) (hMl := by omega) (hmw := E.w (by decide) (by decide))
    (hD0 := by decide) (hft := E.hft) (hfn := by omega) (hfsd := by omega) (hfM := by omega)
    (hfld := by omega) (hfcd := by omega) (hfl := E.rw (by decide) (by decide))
    (hp := E.rw (by decide) (by decide)) (hl0 := by decide) (hn := by decide)
    (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega) (hkw := E.w (by decide) (by decide))
    (hlc := by omega) (hm := by decide) (hc := by decide +kernel) (hspec := rfl) (hD := spec_dep)
    (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 100) (by decide))
    (hk₀ := by decide) (hk₀m := by decide) (hSh := fun x h => spec_Sh x (InR_append_left h))
    (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 100) (by decide) k h1 h2 h3 x hx (InR_append_left h))
    (hGx := fun _ h => h.cx)
    (hG := fun _ _ _ h hv hR => gmc (by decide) hk E.hhs ⟨by simp [nOf], by simp [kOf]⟩
      (fun a ha => by unfold GRd at ha; omega) h hv hR)

theorem o101 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 101 (csuTg 101) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  exact mc_jg (m := 101) (j := 3312) (M := 7991520) (D := 5875232) (n := 10) (k₀ := 90) (l := xl) (c := E.c)
    (hC := E.hC) (hin := E.hin) (hfs := E.hfs) (hinM := E.iMxs) (hinI := E.iMxi) (hinC := E.iCxa)
    (hinN := E.iNef) (htg := tg101) (hpro := pb3312 prof) (hlea := lb3312 prof) (hcd := cd3312 prof.feat)
    (htc := by decide +kernel) (htl := tb3312 prof) (hjd := jd3312 prof.feat) (htj := by decide +kernel)
    (hj := by rw [sti_length]; decide) (hst := E.st (by decide) (by decide)) (hS := by omega)
    (hM0 := by decide) (hMg := by decide) (hMl := by omega) (hmw := E.w (by decide) (by decide))
    (hD0 := by decide) (hft := E.hft) (hfn := by omega) (hfsd := by omega) (hfM := by omega)
    (hfld := by omega) (hfcd := by omega) (hfl := E.rw (by decide) (by decide))
    (hp := E.rw (by decide) (by decide)) (hl0 := by decide) (hn := by decide)
    (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega) (hkw := E.w (by decide) (by decide))
    (hlc := by omega) (hm := by decide) (hc := by decide +kernel) (hspec := rfl) (hD := spec_dep)
    (hT := spec_T) (hB := spec_B E.hhi E.hhs) (hXw := spec_Xw (m := 101) (by decide))
    (hk₀ := by decide) (hk₀m := by decide) (hSh := fun x h => spec_Sh x (InR_append_left h))
    (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 101) (by decide) k h1 h2 h3 x hx (InR_append_left h))
    (hGx := fun _ h => h.cx)
    (hG := fun _ _ _ h hv hR => gmc (by decide) hk E.hhs ⟨by simp [nOf], by simp [kOf]⟩
      (fun a ha => by unfold GRd at ha; omega) h hv hR)

theorem o98 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 98 (csuTg 98) := by
  have hL := E.lay
  have el : xl.toNat = 8010400 := rfl
  have e98 : kOf k 98 = k + 72752 + 1072 := by
    unfold kOf
    split <;> omega
  exact c98_jg (m := 98) (n := 6) (k₀ := 90) (hi := hi) (k := k + 72752) (l := xl) (c := E.c) (hC := E.hC)
    (hin := E.hin) (hfs := E.hfs) (hinS := E.iNst) (hinW := E.iOnw) (hinM := E.iMnx) (hinI := E.iImm)
    (hinC := E.iCxa) (hinN := E.iNef) (htg := tg98) (hsw := E.hsw) (hhs := E.hhs) (hS := by omega)
    (hk := by omega) (hOw := fun a h1 h2 => E.hW a (by omega) (by omega)) (hft := E.hft) (hfn := by omega)
    (hfsd := by omega) (hf7 := by omega) (hfO := by omega) (hfld := by omega) (hfcd := by omega)
    (hfl := E.rw (by decide) (by decide)) (hp := E.rw (by decide) (by decide)) (hl0 := by omega)
    (hn := by decide) (hlw := E.w (C := 8010400) (by decide) (by decide)) (hld := by omega)
    (hkw := E.w (by decide) (by decide)) (hlc := by omega) (hm := by decide) (hc := by decide +kernel)
    (hspec := rfl) (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs)
    (hXw := spec_Xw (m := 98) (by decide)) (hk₀ := by decide) (hk₀m := by decide)
    (hSh := fun x h => spec_Sh x h) (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 98) (by decide) k h1 h2 h3 x hx h)
    (hGx := fun _ h => ⟨h.cx, e98 ▸ h.hp⟩)
    (hG := fun _ _ _ _ h hv _ _ _ _ hp _ _ hH hR => g98 (by decide) hk E.hhs h hv hp hH hR)

theorem o102 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 102 (csuTg 102) := by
  have hL := E.lay
  exact c102_jg (m := 102) (k₀ := 90) (hi := hi) (k := k) (c := E.c) (hC := E.hC) (hin := E.hin)
    (hfs := E.hfs) (hinM := E.iMnx) (hinI := E.iImm) (htg := tg102) (hsw := E.hsw) (hhs := E.hhs)
    (hS := by omega) (hk := hk) (hgw := E.w (by decide) (by decide)) (hm := by decide)
    (hc := by decide +kernel) (hspec := rfl) (hD := spec_dep) (hT := spec_T) (hB := spec_B E.hhi E.hhs)
    (hXw := spec_Xw (m := 102) (by decide)) (hk₀ := by decide) (hk₀m := by decide)
    (hSh := fun x h => spec_Sh x (InR_append_right h)) (hP₀ := spec_P90)
    (hShD := fun k h1 h2 h3 x hx h => spec_ShD (m := 102) (by decide) k h1 h2 h3 x hx (InR_append_right h))
    (hGx := fun _ h => h.hp)
    (hG := fun _ _ _ h hv _ _ _ _ _ _ _ hp _ _ hH => g102 (by decide) hk E.hhs h hv hp hH)

theorem o103 : Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ 103 (csuTg 103) := by
  have hL := E.lay
  have e40 := E.fb40
  exact c103_jg (m := 103) (hCe := E.hCe) (c := E.c) (hC := E.hC) (hin := E.hin) (hinH := E.iHca)
    (hfs := E.hfs) (htg := tg103) (hst := E.st (by decide) (by decide)) (hld := E.hld) (hS := by omega)
    (hcn := E.hcn) (hcnf := by omega) (hcna := by omega)
    (hcpu := fun x h1 h2 => E.hRw x (by omega) (by omega))
    (htab := fun x h1 h2 => E.hRo x (by omega) (by omega))
    (hgw := fun x hx => by
      unfold C103.Gw at hx
      exact ⟨E.hW x (by omega) (by omega), E.hRw x (by omega) (by omega)⟩)
    (hm := by decide) (hc := by decide +kernel) (hspec := rfl) (hD := spec_dep) (hB := spec_B E.hhi E.hhs)
    (hXw := spec_X103) (htb := fun _ h => tb103 h) (hG := g103 (by decide) hk E.hhs)

end runs

/-- The constructors not `Done`. -/
def todo : List Nat :=
  [3, 5, 7, 9, 15, 17, 37, 55, 61, 67, 70, 75, 77, 78, 82, 87, 90, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]

theorem nd : ∀ m < 104, 3 ≤ m →
    ¬ ((∃ x ∈ leas, x.1 = m) ∨ (∃ x ∈ chains, x.1 = m) ∨ m = 12) → m ∈ todo := by
  decide +kernel

/-- `at_ctor`'s `hO`. -/
theorem hO_of (E : CEnv prof F Wl L s₀ o gP gE V sp fb hi) (hk : 16 ≤ k) : ∀ m, 3 ≤ m → m < 104 → ¬ Done m →
    Csu.Runs prof F Wl L s₀ o gev gP gE (JG V sp F Wl fb hi k) sp a₀ a₁ a₂ m (csuTg m) := by
  intro m h3 h104 hd
  have h := nd m h104 h3 hd
  simp only [todo, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact o3 E hk
  · exact o5 E hk
  · exact o7 E hk
  · exact o9 E hk
  · exact o15 E hk
  · exact o17 E hk
  · exact o37 E hk
  · exact o55 E hk
  · exact o61 E hk
  · exact o67 E hk
  · exact o70 E hk
  · exact o75 E hk
  · exact o77 E hk
  · exact o78 E hk
  · exact o82 E hk
  · exact o87 E hk
  · exact o90 E hk
  · exact o92 E hk
  · exact o94 E hk
  · exact o95 E hk
  · exact o96 E hk
  · exact o97 E hk
  · exact o98 E hk
  · exact o99 E hk
  · exact o100 E hk
  · exact o101 E hk
  · exact o102 E hk
  · exact o103 E hk

theorem leasM : ∀ x ∈ leas, x.1 ≠ 90 ∧ x.1 ≠ 94 ∧ x.1 ≠ 95 ∧ x.1 ≠ 98 ∧ x.1 ≠ 99 ∧ x.1 ≠ 100 ∧ x.1 ≠ 101 ∧
    x.1 ≠ 102 := by decide +kernel
theorem chainsM : ∀ x ∈ chains, x.1 ≠ 90 ∧ x.1 ≠ 94 ∧ x.1 ≠ 95 ∧ x.1 ≠ 98 ∧ x.1 ≠ 99 ∧ x.1 ≠ 100 ∧
    x.1 ≠ 101 ∧ x.1 ≠ 102 := by decide +kernel

/-- `nOf`, `kOf` are the same after a constructor `Done`. -/
theorem done_e {n₀ m : Nat} (h : Done m) : nOf n₀ (m + 1) = nOf n₀ m ∧ kOf k (m + 1) = kOf k m := by
  have hm : m ≠ 90 ∧ m ≠ 94 ∧ m ≠ 95 ∧ m ≠ 98 ∧ m ≠ 99 ∧ m ≠ 100 ∧ m ≠ 101 ∧ m ≠ 102 := by
    rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl
    · exact leasM x hx
    · exact chainsM x hx
    · decide
  constructor
  · unfold nOf
    repeat' split
    all_goals omega
  · unfold kOf
    repeat' split
    all_goals omega

/-- `AtCtor` from `CEnv`, the invariant `Gs` at `3` of the bytes at the call of `__libc_csu_init`, and the run from
`main` on. -/
theorem at_ctor_gs {K : Ctx} {fb : Addr} {V : Addr → Byte} {hi k : Nat} {sp : Addr}
    (esp : K.bp + 112#64 - 8#64 = sp) (E : CEnv prof F Wl L s₀ o gP gE V sp fb hi) (hk : 16 ≤ k)
    (hinN : CodeIn L nret_at nret) (hst : ∀ i < 8, Foot Wl (Addr.add (K.bp + 112#64 - 8#64 - 64#64 - 8 - 8) i))
    (hbp : K.bp.toNat + 392 ≤ 2 ^ 64) (hz : ∀ r < 3, rdd(V, regCnt r) = 0) (hV : Gs F Wl fb hi 1 k 3 V)
    (hmain : ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm →
      JG V sp F Wl fb hi k 104 V₁ →
      (∀ a : Addr, ¬ ((K.bp + 112#64).toNat - 16 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat) →
        ¬ ((K.bp + 112#64).toNat + 112 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 208) →
        ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) →
        Vm a = V₁ a) →
      rdq(Vm, K.bp + 112#64 - 8#64) = lsm_at.add 1168 →
      Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = K.bp + 112#64 - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
      Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) → GoG prof L o gev gP gE Z' t') :
    AtCtor prof F Wl L s₀ o gev gP gE K fb V := by
  have hL := E.lay
  have ob : (7947808#64 : Addr).toNat = 7947808 := rfl
  exact at_ctor (spec := spec V hi) (G := Gs F Wl fb hi 1 k) esp E.c E.hC E.hin E.hR E.hinR hinN hst hbp
    (by omega) hz spec_dep spec_T (spec_B E.hhi E.hhs) spec_E spec_done
    (fun m W W' h ho => h.out (by decide) hk ⟨rfl, rfl⟩ (fun a ha => by unfold GRd at ha; omega) ho)
    (fun W W' hN hd => hV.kept (by decide) hk fun a ha =>
      (hd.out a (by unfold GRd at ha; omega) (fun h => by unfold Rfi.Wr at h; unfold GRd at ha; omega)).trans
        (hN a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega)))
    (fun m W W' hd h ho => Gs.step (done_e hd)
      (h.kept (by decide) hk fun a ha => ho a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega)))
    (hO_of E hk) hmain

end FV7z.Ctor
