import FV7z.Strncmp.Exit
import FV7z.Strncmp.Vec16
/-!
# `__strncmp_sse2`: the head (PLAN.md G3, `strncmp`)

From the entry (`head`): `rdx = 0` returns 0 (`ret0`), `rdx = 1` the difference of the first bytes (`nres_one`).
Otherwise, when both strings are at most 48 bytes into their 64 bytes, their first 16 bytes are compared without
alignment (`at48`): a stop there ends at `6192` (`exit6192`); none and `n ≤ 16` returns 0; else both move on 16
bytes. Either way the run reaches `128`, the alignment, with 0 or 16 bytes compared (`At128`, `Go128`).
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

/-! ## Numbers and flags -/

theorem ofNat_inj {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    BitVec.ofNat w x = BitVec.ofNat w y ↔ x = y := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
  · rintro rfl
    rfl

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl]
  by_cases h : n = 0
  · subst h
    rfl
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun e => h ((ofNat_inj hn (by decide)).1 e)

/-- `cmp`, then `jbe`, of two numbers: taken just when `R ≤ p`. -/
theorem be_ofNat {w R p : Nat} (hR : R < 2 ^ w) (hp : p < 2 ^ w) :
    (decide ((BitVec.ofNat w R).toNat < (BitVec.ofNat w p).toNat) || decide (BitVec.ofNat w R = BitVec.ofNat w p)) =
      decide (R ≤ p) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hp]
  by_cases h : R < p
  · rw [decide_eq_true h, decide_eq_true (Nat.le_of_lt h)]
    rfl
  · rw [decide_eq_false h, Bool.false_or]
    exact decide_eq_decide.mpr ((ofNat_inj hR hp).trans ⟨fun e => e ▸ Nat.le_refl _, fun e => by omega⟩)

/-- `mov ecx, esi; and rcx, 63`: the offset in 64 bytes. -/
theorem and63 (b : BitVec 64) :
    (b.setWidth 32).setWidth 64 &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : b.toNat % 2 ^ 32 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have h2 : b.toNat % 64 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2, show 63 % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 6 ∣ 2 ^ 32)]

theorem off64_lt (a : Addr) : a.toNat % 64 < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

theorem cond4_log {w : Nat} {f fl : Rflags} {M : BitVec w} (h : LogF f M fl) : fl.cond 4 = (M == 0) := by
  obtain ⟨af, rfl⟩ := h
  rw [cond_4, arith_zf]

theorem xor_z {w : Nat} (a : BitVec w) : a ^^^ a = 0 := BitVec.xor_self

/-! ## Addresses -/

theorem eaB_add {g : Gprs} {r d : Nat} {a : Addr} (h : g.get (regOf r) = a) (i : Nat) :
    (eaB g r d).add i = a.add (d + i) := by
  show (g.get (regOf r) + BitVec.ofNat 64 d).add i = _
  rw [h]
  exact addr_add_add a d i

theorem foot_ea {F : Footprint} {g : Gprs} {r d m : Nat} {a : Addr} (h : g.get (regOf r) = a)
    (hf : ∀ i < d + m, Foot F.data (a.add i)) : ∀ i < m, Foot F.data ((eaB g r d).add i) := fun i hi => by
  rw [eaB_add h i]
  exact hf _ (by omega)

/-- The address `[b]`. -/
theorem ea_b0 {g : Gprs} {b : Nat} {a : Addr} (hb : g.get (regOf b) = a) : eaG g (some b) none 1 0 = a := by
  simp [eaG, optV, hb]

/-- At most 48 bytes into its 64 bytes, 16 bytes from `a` are in its page. -/
theorem foot16 {F : Footprint} {a : Addr} (hpg : ∀ x : Addr, x.toNat / 4096 = a.toNat / 4096 → Foot F.data x)
    (h : a.toNat % 64 ≤ 48) : ∀ i < 16, Foot F.data (a.add i) := by
  intro i hi
  apply hpg
  have h1 : a.toNat % 4096 % 64 = a.toNat % 64 := Nat.mod_mod_of_dvd _ (by decide)
  have h2 : a.toNat % 4096 ≤ 4080 := by omega
  have ha := a.isLt
  have e : (a.add i).toNat = a.toNat + i := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  omega

/-! ## What is returned -/

/-- `strncmp` of 1 byte. -/
theorem nres_one {V : Addr → Byte} {a b : Addr} {r : BitVec 32} (hr : r = 0 ↔ V a = V b) : NRes V a b 1 r := by
  intro m hm hs
  rcases Nat.lt_or_eq_of_le hm with h | rfl
  · obtain rfl : m = 0 := by omega
    rw [addr_add_zero, addr_add_zero]
    exact ⟨fun h' => absurd h' (by decide), fun _ he _ => hr.2 he, fun _ hne h0 => hne (hr.1 h0)⟩
  · have e := (hs 0 (by decide)).1
    rw [addr_add_zero, addr_add_zero] at e
    exact ⟨fun _ => hr.2 e, fun h' => absurd h' (Nat.lt_irrefl _), fun h' => absurd h' (Nat.lt_irrefl _)⟩

/-- At `128`: `rdi` and `rsi` `q` bytes into the strings, `r11` the bytes left, `rcx` and `rax` the strings'
offsets in their 64 bytes. -/
def At128 (g₀ g : Gprs) (a b : Addr) (n q : Nat) : Prop :=
  KpN g₀ g ∧ g.rdi = a.add q ∧ g.rsi = b.add q ∧ g.r11 = BitVec.ofNat 64 (n - q) ∧
    g.rcx = BitVec.ofNat 64 (b.toNat % 64) ∧ g.rax = BitVec.ofNat 64 (a.toNat % 64)

/-- What a run from `128` does: with `q` (0 or 16) bytes compared, the same and not 0, and fewer than `n`. -/
def Go128 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (e' : Addr) (g₀ : Gprs) (a b : Addr) (n : Nat) : Prop :=
  ∀ Z t' q, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add 128 → At128 g₀ Z.cpu.gpr a b n q →
    q < n → (q = 0 ∨ q = 16) → Same V a b q → GoG prof L o gev gP gE Z t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `6212`: `xor eax, eax; ret`. -/
theorem ret0 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {P : BitVec 32 → Prop} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 6212)
    (hkp : KpN g₀ Y.cpu.gpr) (hP : P 0) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin (b6212 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hkp₁ : KpN g₀ Y₁.cpu.gpr := by simp only [KpN, hg₁, wr, set_rax]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax.setWidth 32 = 0 := by
    simp only [hg₁, wr, gv, Src.val, set_rax, sw_64_32, BitVec.xor_self]
    all_goals rfl
  refine retN_at c hin (lt_scm (by decide)) (d6214 prof.feat) hK₁ hA₁ hr₁ hkp₁ ?_ hR
  rw [hax₁]
  exact hP

/-- From `48`: the first 16 bytes of both strings in their pages, compared. -/
theorem at48 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b : Addr} {n : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 48)
    (hg : At128 g₀ Y.cpu.gpr a b n 0) (hn64 : n < 2 ^ 64) (hn2 : 2 ≤ n)
    (hfa : ∀ i < 16, Foot F.data (a.add i)) (hfb : ∀ i < 16, Foot F.data (b.add i))
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (K : Go128 prof F Wl L s₀ o gev gP gE V e' g₀ a b n) : GoG prof L o gev gP gE Y t := by
  obtain ⟨hkp, hdi, hsi, h11, hcx, hax⟩ := hg
  rw [addr_add_zero] at hdi hsi
  rw [Nat.sub_zero] at h11
  -- `movlpd xmm1, [rdi]; movlpd xmm2, [rsi]; movhpd xmm1, [rdi + 8]; movhpd xmm2, [rsi + 8]; pxor xmm0, xmm0;
  -- pcmpeqb xmm0, xmm1`
  refine c.s_blkV hin (b48 prof) hK hA hrip ?_
  refine wpV_v (foot_ea (r := 7) (d := 0) (by rw [get7]; exact hdi) fun i hi => hfa i (by omega))
    (fun h => nomatch h) <|
    wpV_v (foot_ea (r := 6) (d := 0) (by rw [get6]; exact hsi) fun i hi => hfb i (by omega)) (fun h => nomatch h) <|
    wpV_v (foot_ea (r := 7) (d := 8) (by rw [get7]; exact hdi) fun i hi => hfa i (by omega)) (fun h => nomatch h) <|
    wpV_v (foot_ea (r := 6) (d := 8) (by rw [get6]; exact hsi) fun i hi => hfb i (by omega)) (fun h => nomatch h) <|
    wpV_v0 <| wpV_v0 <| wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  have hx1 : ∀ j < 16, lane 8 (xsOf Y₁.cpu.vec.zmm (xmmOf 1)) j = V (a.add j) := fun j hj => by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, eaB, get7, hdi]
    exact lohi_lane V a _ hj
  have hx2 : ∀ j < 16, lane 8 (xsOf Y₁.cpu.vec.zmm (xmmOf 2)) j = V (b.add j) := fun j hj => by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, eaB, get6, hsi]
    exact lohi_lane V b _ hj
  have hx0 : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = peqb 0 (xsOf Y₁.cpu.vec.zmm (xmmOf 1)) := by
    rw [hv₁]
    simp (disch := decide) only [xset_same, xset_ne, xor_z]
  have hkp₁ : KpN g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = a := by rw [hg₁]; exact hdi
  have hsi₁ : Y₁.cpu.gpr.rsi = b := by rw [hg₁]; exact hsi
  have h11₁ : Y₁.cpu.gpr.r11 = BitVec.ofNat 64 n := by rw [hg₁]; exact h11
  have hcx₁ : Y₁.cpu.gpr.rcx = BitVec.ofNat 64 (b.toNat % 64) := by rw [hg₁]; exact hcx
  have hax₁ : Y₁.cpu.gpr.rax = BitVec.ofNat 64 (a.toNat % 64) := by rw [hg₁]; exact hax
  generalize hAx : xsOf Y₁.cpu.vec.zmm (xmmOf 1) = A at hx1 hx0
  generalize hBx : xsOf Y₁.cpu.vec.zmm (xmmOf 2) = B at hx2
  -- `pcmpeqb xmm1, xmm2; psubb xmm1, xmm0; pmovmskb edx, xmm1; sub edx, 0xffff`
  refine c.s_blkV hin (b74 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v0 <| wpV_v0 <| wpV_v0 <| wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  have hdx₂ : Y₂.cpu.gpr.rdx = (cmask A B - BitVec.ofNat 32 65535).setWidth 64 := by
    rw [hg₂]
    simp (disch := decide) only [wr, gv, Src.val, set_rdx, get2, xset_same, xset_ne, hx0, hAx, hBx, sw_64_32,
      subR_eq, cmask]
  have hz : Y₂.cpu.rflags.zf = decide (cmask A B - BitVec.ofNat 32 65535 = 0) := by
    rw [hf₂, hfl, subF_zf]
    simp (disch := decide) only [gv, Src.val, set_rdx, get2, xset_same, xset_ne, hx0, hAx, hBx, sw_64_32, cmask,
      sub_eq_zero_iff]
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂, wr, set_rdx]; exact hkp₁
  have hdi₂ : Y₂.cpu.gpr.rdi = a := by simp only [hg₂, wr, set_rdx]; exact hdi₁
  have hsi₂ : Y₂.cpu.gpr.rsi = b := by simp only [hg₂, wr, set_rdx]; exact hsi₁
  have h11₂ : Y₂.cpu.gpr.r11 = BitVec.ofNat 64 n := by simp only [hg₂, wr, set_rdx]; exact h11₁
  have hcx₂ : Y₂.cpu.gpr.rcx = BitVec.ofNat 64 (b.toNat % 64) := by simp only [hg₂, wr, set_rdx]; exact hcx₁
  have hax₂ : Y₂.cpu.gpr.rax = BitVec.ofNat 64 (a.toNat % 64) := by simp only [hg₂, wr, set_rdx]; exact hax₁
  -- `jne 6192`
  refine c.s_jcc (tgt := 6192) hK₂ hA₂ hin (lt_scm (by decide)) hr₂ (d92 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · -- a stop in the 16 bytes
    intro hcc
    rw [cond_5, hz] at hcc
    have hne : cmask A B - BitVec.ofNat 32 65535 ≠ 0 := fun h => by simp [h] at hcc
    have hex : ∃ j < 16, decide (lane 8 A j = lane 8 B j ∧ lane 8 A j ≠ 0) = false := by
      refine Classical.byContradiction fun hn => hne ((cmask_sub_zero A B).2 fun j hj => ?_)
      refine of_decide_eq_true ?_
      cases h : decide (lane 8 A j = lane 8 B j ∧ lane 8 A j ≠ 0)
      · exact absurd ⟨j, hj, h⟩ hn
      · rfl
    obtain ⟨p, hp, hpf, hpt⟩ := exists_first _ hex
    have hpf' : ¬ (lane 8 A p = lane 8 B p ∧ lane 8 A p ≠ 0) := of_decide_eq_false hpf
    have hpt' : ∀ i < p, lane 8 A i = lane 8 B i ∧ lane 8 A i ≠ 0 := fun i hi => of_decide_eq_true (hpt i hi)
    obtain ⟨hnz, hlow⟩ := cmask_sub_low A B hp hpf' hpt'
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    refine exit6192 c hin hK₃ hA₃ hr₃ (q := 0) (R := n) (p := p) (by rw [hg₃]; exact hkp₂)
      (by rw [hg₃, addr_add_zero]; exact hdi₂) (by rw [hg₃, addr_add_zero]; exact hsi₂) (by rw [hg₃]; exact h11₂)
      hn64 (Nat.zero_add n) (by rw [hg₃, hdx₂]; exact hnz) (by rw [hg₃, hdx₂]; exact hlow) (by omega) ?_
      (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) hP hR
    · intro i hi
      rw [← hx1 i (by omega), ← hx2 i (by omega)]
      exact hpt' i (by omega)
    · rw [Nat.zero_add, ← hx1 p hp, ← hx2 p hp]
      exact hpf'
    · rw [Nat.zero_add]
      exact hfa p hp
    · rw [Nat.zero_add]
      exact hfb p hp
  · -- the 16 bytes the same and not 0
    intro hcc
    rw [cond_5, hz] at hcc
    have h0 : cmask A B - BitVec.ofNat 32 65535 = 0 := by simpa using hcc
    have hall := (cmask_sub_zero A B).1 h0
    have hs16 : Same V a b 16 := by
      intro i hi
      rw [← hx1 i hi, ← hx2 i hi]
      exact hall i hi
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    -- `sub r11, 16`
    refine c.s_blkV hin (b98 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun fl hfl => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ _
    have hc : Y₄.cpu.rflags.cond 6 = decide (n ≤ 16) := by
      rw [hf₄, hfl, cond_6, subF_cf, subF_zf]
      simp only [Src.val, gv, get11, BitVec.setWidth_eq, hg₃, h11₂]
      exact be_ofNat hn64 (by decide)
    simp only [wr, gv, Src.val, get11, BitVec.setWidth_eq, set11, subR_eq, hg₃] at hg₄
    have hkp₄ : KpN g₀ Y₄.cpu.gpr := by simp only [KpN, hg₄]; exact hkp₂
    -- `jbe 6212`
    refine c.s_jcc (tgt := 6212) hK₄ hA₄ hin (lt_scm (by decide)) hr₄ (d102 prof.feat) (by decide)
      (lt_scm (by decide)) ?_ ?_
    · intro hcc
      have hle : n ≤ 16 := by
        rw [hc] at hcc
        exact of_decide_eq_true hcc
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      exact ret0 c hin hK₅ hA₅ hr₅ (by rw [hg₅]; exact hkp₄) (hP 0 (nres_zero hs16 hle)) hR
    · intro hcc
      have hlt : 16 < n := by
        rw [hc] at hcc
        exact Nat.lt_of_not_le (of_decide_eq_false hcc)
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      -- `add rsi, 16; add rdi, 16`
      refine c.s_blkV hin (b108 prof) hK₅ hA₅ hr₅ ?_
      refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
      intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ _ _
      simp only [wr, gv, Src.val, get6, get7, BitVec.setWidth_eq, set_rsi, set_rdi, addR_eq, hg₅, hg₄] at hg₆
      refine K Y₆ t₆ 16 hK₆ hA₆ hr₆ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hlt (Or.inr rfl) hs16
      · simp only [KpN, hg₆]
        exact hkp₂
      · simp only [hg₆, hdi₂]
        rfl
      · simp only [hg₆, hsi₂]
        rfl
      · simp only [hg₆, h11₂]
        exact BitVec.ofNat_sub_ofNat_of_le n 16 (by decide) (by omega)
      · simp only [hg₆]
        exact hcx₂
      · simp only [hg₆]
        exact hax₂

/-- From the entry: `rdi` the string at `a`, `rsi` at `b`, `rdx` the bytes `n` at most, each string's page to read
if `n` is not 0. -/
theorem head (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b : Addr} {n : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 0) (hkp : KpN g₀ Y.cpu.gpr)
    (hdi : Y.cpu.gpr.rdi = a) (hsi : Y.cpu.gpr.rsi = b) (hdx : Y.cpu.gpr.rdx = BitVec.ofNat 64 n)
    (hn64 : n < 2 ^ 64)
    (hpa : 0 < n → ∀ x : Addr, x.toNat / 4096 = a.toNat / 4096 → Foot F.data x)
    (hpb : 0 < n → ∀ x : Addr, x.toNat / 4096 = b.toNat / 4096 → Foot F.data x)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P)
    (K : Go128 prof F Wl L s₀ o gev gP gE V e' g₀ a b n) : GoG prof L o gev gP gE Y t := by
  -- `endbr64; test rdx, rdx`
  refine c.s_blkV hin (b0 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  have hz₁ : Y₁.cpu.rflags.cond 4 = decide (n = 0) := by
    rw [hf₁, cond4_log hfl]
    simp only [gv, Src.val, get2, BitVec.setWidth_eq, BitVec.and_self, hdx]
    exact ofNat_beq_zero hn64
  -- `je 6212`
  refine c.s_jcc (tgt := 6212) hK₁ hA₁ hin (lt_scm (by decide)) hr₁ (d7 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · intro hcc
    have h0 : n = 0 := by
      rw [hz₁] at hcc
      exact of_decide_eq_true hcc
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact ret0 c hin hK₂ hA₂ hr₂ (by rw [hg₂, hg₁]; exact hkp)
      (hP 0 (nres_zero (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero _)) (by omega))) hR
  intro hcc
  have hn0 : 0 < n := by
    rw [hz₁] at hcc
    exact Nat.pos_of_ne_zero (of_decide_eq_false hcc)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hgY₂ : Y₂.cpu.gpr = Y.cpu.gpr := hg₂.trans hg₁
  -- `cmp rdx, 1`
  refine c.s_blkV hin (b13 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  have hz₃ : Y₃.cpu.rflags.cond 4 = decide (n = 1) := by
    rw [hf₃, hfl, cond_4, subF_zf]
    simp only [gv, Src.val, get2, BitVec.setWidth_eq, hgY₂, hdx]
    exact decide_eq_decide.mpr (ofNat_inj hn64 (by decide))
  have hgY₃ : Y₃.cpu.gpr = Y.cpu.gpr := hg₃.trans hgY₂
  -- `je 6224`
  refine c.s_jcc (tgt := 6224) hK₃ hA₃ hin (lt_scm (by decide)) hr₃ (d17 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · -- one byte: `movzx ecx, byte [rsi]; movzx eax, byte [rdi]; sub eax, ecx; ret`
    intro hcc
    have h1 : n = 1 := by
      rw [hz₃] at hcc
      exact of_decide_eq_true hcc
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have hgY₄ : Y₄.cpu.gpr = Y.cpu.gpr := hg₄.trans hgY₃
    refine c.s_blkV hin (b6224 prof) hK₄ hA₄ hr₄ ?_
    refine wpV_ldzx8 (ea_b0 (by rw [get6, hgY₄]; exact hsi)) (hpb hn0 b rfl) <|
      wpV_ldzx8 (ea_b0 (by simp only [wr, set_rcx, get7, hgY₄]; exact hdi)) (hpa hn0 a rfl) <|
      wpV_reg fun _ _ => wpV_nil ?_
    intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ _
    have hkp₅ : KpN g₀ Y₅.cpu.gpr := by simp only [KpN, hg₅, wr, set_rax, set_rcx, hgY₄]; exact hkp
    have hax₅ : Y₅.cpu.gpr.rax.setWidth 32 = (V a).setWidth 32 - (V b).setWidth 32 := by
      simp only [hg₅, wr, gv, Src.val, set_rax, set_rcx, get0, get1, sw_64_32, subR_eq]
    refine retN_at c hin (lt_scm (by decide)) (d6232 prof.feat) hK₅ hA₅ hr₅ hkp₅ ?_ hR
    rw [hax₅]
    subst h1
    exact hP _ (nres_one (zsub_eq_zero _ _))
  intro hcc
  have hn2 : 2 ≤ n := by
    rw [hz₃] at hcc
    have := of_decide_eq_false hcc
    omega
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  have hgY₄ : Y₄.cpu.gpr = Y.cpu.gpr := hg₄.trans hgY₃
  -- `mov r11, rdx; mov ecx, esi; mov eax, edi; and rcx, 63; and rax, 63; cmp ecx, 48`
  refine c.s_blkV hin (b23 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ _
  have hja₅ : Y₅.cpu.rflags.cond 7 = !decide (b.toNat % 64 ≤ 48) := by
    rw [hf₅, hfl, cond_7, subF_cf, subF_zf]
    simp only [wr, gv, Src.val, set_rcx, set_rax, set11, get0, get1, get2, get6, get7, BitVec.setWidth_eq, hgY₄,
      hsi, and63, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rw [be_ofNat (off64_lt b) (by decide)]
  simp only [wr, gv, Src.val, set_rcx, set_rax, set11, get0, get1, get2, get6, get7, BitVec.setWidth_eq, hgY₄,
    hsi, hdi, hdx, and63] at hg₅
  have hg128 : At128 g₀ Y₅.cpu.gpr a b n 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hg₅, KpN, addr_add_zero, Nat.sub_zero]
    exact hkp
  -- `ja 128`
  refine c.s_jcc (tgt := 128) hK₅ hA₅ hin (lt_scm (by decide)) hr₅ (d41 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · intro _
    rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
    exact K Y₆ t₆ 0 hK₆ hA₆ hr₆ (hg₆ ▸ hg128) hn0 (Or.inl rfl) (fun i hi => absurd hi (Nat.not_lt_zero _))
  intro hcc
  have hb48 : b.toNat % 64 ≤ 48 := by
    rw [hja₅] at hcc
    simpa using hcc
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  rw [← hg₆] at hg128
  -- `cmp eax, 48`
  refine c.s_blkV hin (b43 prof) hK₆ hA₆ hr₆ ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₇ t₇ hK₇ hA₇ hr₇ hg₇ hf₇ _
  have hja₇ : Y₇.cpu.rflags.cond 7 = !decide (a.toNat % 64 ≤ 48) := by
    rw [hf₇, hfl, cond_7, subF_cf, subF_zf]
    simp only [gv, Src.val, get0, hg128.2.2.2.2.2, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rw [be_ofNat (off64_lt a) (by decide)]
  rw [← hg₇] at hg128
  -- `ja 128`
  refine c.s_jcc (tgt := 128) hK₇ hA₇ hin (lt_scm (by decide)) hr₇ (d46 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · intro _
    rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
    exact K Y₈ t₈ 0 hK₈ hA₈ hr₈ (hg₈ ▸ hg128) hn0 (Or.inl rfl) (fun i hi => absurd hi (Nat.not_lt_zero _))
  intro hcc
  have ha48 : a.toNat % 64 ≤ 48 := by
    rw [hja₇] at hcc
    simpa using hcc
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  exact at48 c hin hK₈ hA₈ hr₈ (hg₈ ▸ hg128) hn64 hn2 (foot16 (hpa hn0) ha48) (foot16 (hpb hn0) hb48) hP hR K

end FV7z.Strncmp
