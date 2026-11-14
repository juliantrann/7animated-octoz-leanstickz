import FV7z.Hwc.Vc2
import FV7z.Hwc.Zero
import FV7z.Gor.Mem
/-!
# `_dl_important_hwcaps`: the strings of the combinations, 1248 → 1392 (PLAN.md G3, startup)

The loop of `Vc2` with its three `call`s of `mempcpy` (1260, 1325, 1350; `Gor.PcpyAt`, the contract of `mempcpy`).
Only where the bytes go is followed, not what they are: from `A` (the first byte after the table) the strings and
their `/` are written up to `pe ≤ B`, below the slot of the return address of the `call`s (`sp - 8`), and the rest of
the memory stays as it was (`Outs`).

- `mcpy`: one `call` of `mempcpy (p, S, ℓ)`, `Outs` from `p` to `p + ℓ`.
- `inner`: the bits `m, …, 1` of `n` (from 1294, or 1343 when `m = 0`): `temp[m']` and `/` for each set bit
  (`bts`).
- `loop`: the combinations `n = 2 i, …, 0` (from 1248, `r12 = n + 2`): `temp[cnt-1]`, the bits, `temp[0]` (`wid`), to
  1392 (`rem`, the bytes of all of them).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

set_option maxRecDepth 100000

/-! ## The `call`s of `mempcpy` -/

def pc1260 : List Byte := [0xe8, 0x8f, 0x3a, 0xd5, 0xff]
theorem pc1260_0 : ∀ feat, Dec feat pc1260 0 (FV7z.mk .call 64 [.rel 18446744073706748559] 5) := by dec_rfl
theorem w_1260 : pc1260 <+: hwc.drop 1260 := by decide +kernel
theorem call_1260 (feat : Features) : Dec feat hwc 1260 (FV7z.mk .call 64 [.rel 18446744073706748559] 5) :=
  Dec.shift (j := 1260) (k := 0) (pc1260_0 feat) w_1260 (Nat.zero_le _)

def pc1325 : List Byte := [0xe8, 0x4e, 0x3a, 0xd5, 0xff]
theorem pc1325_0 : ∀ feat, Dec feat pc1325 0 (FV7z.mk .call 64 [.rel 18446744073706748494] 5) := by dec_rfl
theorem w_1325 : pc1325 <+: hwc.drop 1325 := by decide +kernel
theorem call_1325 (feat : Features) : Dec feat hwc 1325 (FV7z.mk .call 64 [.rel 18446744073706748494] 5) :=
  Dec.shift (j := 1325) (k := 0) (pc1325_0 feat) w_1325 (Nat.zero_le _)

def pc1350 : List Byte := [0xe8, 0x35, 0x3a, 0xd5, 0xff]
theorem pc1350_0 : ∀ feat, Dec feat pc1350 0 (FV7z.mk .call 64 [.rel 18446744073706748469] 5) := by dec_rfl
theorem w_1350 : pc1350 <+: hwc.drop 1350 := by decide +kernel
theorem call_1350 (feat : Features) : Dec feat hwc 1350 (FV7z.mk .call 64 [.rel 18446744073706748469] 5) :=
  Dec.shift (j := 1350) (k := 0) (pc1350_0 feat) w_1350 (Nat.zero_le _)

/-! ## Where the bytes go -/

/-- The bytes below `A`, from `p` to the slot `sp - 8`, from `sp` up as they were in `V₀`. -/
def Outs (V₀ W : Addr → Byte) (A p sp : Nat) : Prop :=
  Same V₀ W 0 A ∧ Same V₀ W p (sp - 8) ∧ Same V₀ W sp (2 ^ 64)

theorem Same.mono {V W : Addr → Byte} {lo hi lo' hi' : Nat} (h : Same V W lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    Same V W lo' hi' := fun a a1 a2 => h a (by omega) (by omega)

/-- The `/` at `p`. -/
theorem Outs.sl {V₀ W : Addr → Byte} {A p sp : Nat} {x : Addr} (hO : Outs V₀ W A p sp) (hx : x.toNat = p)
    (hA : A ≤ p) (hps : p + 1 ≤ sp - 8) (hsp : sp ≤ 2 ^ 64) :
    Outs V₀ (Vst W x (toBytesLE 47#8 1)) A (p + 1) sp :=
  ⟨hO.1.st (by rw [toBytesLE_length]; omega) (.inr (by omega)),
    (hO.2.1.mono (by omega) (Nat.le_refl _)).st (by rw [toBytesLE_length]; omega)
      (.inl (by rw [toBytesLE_length]; omega)),
    hO.2.2.st (by rw [toBytesLE_length]; omega) (.inl (by rw [toBytesLE_length]; omega))⟩

theorem sub8 {sp : Addr} (h : 8 ≤ sp.toNat) : (sp - 8).toNat = sp.toNat - 8 := by
  bv_omega

theorem sub8_add (sp : Addr) : sp - 8 + 8 = sp := BitVec.sub_add_cancel _ _

theorem addN {a b : Addr} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem add1 {a : Addr} (h : a.toNat + 1 < 2 ^ 64) : (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem addO {R : Addr} {c : Nat} (h : R.toNat + c < 2 ^ 64) : (R + BitVec.ofNat 64 c).toNat = R.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy : List Byte} {Pm : (Addr → Byte) → Prop}

/-- The `call` of `mempcpy (p, S, ℓ)` at `j` (`p = rdi` from `A`, `p + ℓ ≤ B`, `S` apart from `A`, `B`): back at `j + 5`
with `rax = p + ℓ`, the callee-saved registers, `Outs` up to `p + ℓ`. -/
theorem mcpy (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hwc_at hwc) {j rel : Nat} (hj : j + 5 < 2345)
    (hd : Dec prof.feat hwc j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : hwc_at.add (j + 5) + BitVec.ofNat 64 rel = 4198592#64)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    {V₀ : Addr → Byte} (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V₀ a) → Pm W)
    {A B : Nat} {sp : Addr} (hlo : 7940480 ≤ A) (hB : B ≤ sp.toNat - 8) (hsp8 : 8 ≤ sp.toNat)
    (hbuf : ∀ a : Addr, A ≤ a.toNat → a.toNat < B → Foot Wl a)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    {X : State} {t : Nat} {V : Addr → Byte} {S Ln : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = hwc_at.add j)
    (hsp : X.cpu.gpr.rsp = sp) (hsi : X.cpu.gpr.rsi = S) (hdx : X.cpu.gpr.rdx = Ln)
    (hp : A ≤ X.cpu.gpr.rdi.toNat) (hpe : X.cpu.gpr.rdi.toNat + Ln.toNat ≤ B)
    (hO : Outs V₀ V A X.cpu.gpr.rdi.toNat sp.toNat)
    (hfS : ∀ i < Ln.toNat, Foot F.data (S.add i)) (hS : S.toNat + Ln.toNat ≤ 2 ^ 64)
    (hSd : S.toNat + Ln.toNat ≤ A ∨ B ≤ S.toNat)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = hwc_at.add (j + 5) →
      Z.cpu.gpr.rsp = sp → Z.cpu.gpr.rax = X.cpu.gpr.rdi + Ln → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      Outs V₀ W A (X.cpu.gpr.rdi.toNat + Ln.toNat) sp.toNat → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := sp.isLt
  have hb8 := sub8 hsp8
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd hinc hc0 htgt (fun i hi => by rw [hsp]; exact hst i hi) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hsp] at hA₁ hg₁
  have hdi₁ : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₁]; rfl
  have hsi₁ : Y.cpu.gpr.rsi = S := by rw [hg₁]; exact hsi
  have hdx₁ : Y.cpu.gpr.rdx = Ln := by rw [hg₁]; exact hdx
  have hsp₁ : Y.cpu.gpr.rsp = sp - 8 := by rw [hg₁]; rfl
  have hfit : X.cpu.gpr.rdi.toNat + Ln.toNat ≤ 2 ^ 64 := by omega
  refine hcpy c hK₁ hA₁ hr₁ (hPm _ fun a ha => ?_) hin (j := j + 5) (lt_len (by omega)) ?_ (fun i hi => ?_)
    (fun i hi => ?_) (fun i hi => ?_) (by rw [hsi₁, hdx₁]; exact hS) (by rw [hdi₁, hdx₁]; exact hfit)
    (by rw [hsi₁, hdi₁, hdx₁]; omega) (by rw [hdi₁, hdx₁, hsp₁, hb8]; omega) ?_
  · rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (.inl (by rw [hb8]; omega))]
    exact hO.1 a (Nat.zero_le _) (by omega)
  · rw [hsp₁, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hb8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₁]
    exact c.hws _ (hst i hi)
  · rw [hdx₁] at hi
    rw [hsi₁]
    exact hfS i hi
  · rw [hdx₁] at hi
    rw [hdi₁]
    exact hbuf _ (by rw [toNat_add_of_fits hi hfit]; omega) (by rw [toNat_add_of_fits hi hfit]; omega)
  intro Z t₂ V₂ hK₂ hA₂ hr₂ hsp₂ hax₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂ _ hf₂
  rw [hdi₁, hdx₁] at hf₂ hax₂
  have hv : ∀ a : Addr, (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + Ln.toNat ≤ a.toNat) →
      (a.toNat < sp.toNat - 8 ∨ sp.toNat ≤ a.toNat) → V₂ a = V a := fun a h1 h2 => by
    rw [hf₂ a (by omega), Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega)
      (by rw [toBytesLE_length, hb8]; omega)]
  refine k Z t₂ V₂ hK₂ hA₂ hr₂ (by rw [hsp₂, hsp₁]; exact sub8_add sp) hax₂ (by rw [hbx₂, hg₁]; rfl)
    (by rw [hbp₂, hg₁]; rfl) (by rw [h12₂, hg₁]; rfl) (by rw [h13₂, hg₁]; rfl) (by rw [h14₂, hg₁]; rfl)
    (by rw [h15₂, hg₁]; rfl) ⟨fun a h1 h2 => ?_, fun a h1 h2 => ?_, fun a h1 h2 => ?_⟩
  · rw [hv a (by omega) (by omega)]
    exact hO.1 a h1 h2
  · rw [hv a (by omega) (by omega)]
    exact hO.2.1 a (by omega) h2
  · rw [hv a (by omega) (by omega)]
    exact hO.2.2 a h1 h2

/-! ## The bytes written -/

/-- `temp[m']` and its `/` for the set bits `m'` of `n`, `m ≥ m' ≥ 1`. -/
def bts (ln : Nat → Addr) (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => (if n.testBit (m + 1) then (ln (m + 1)).toNat + 1 else 0) + bts ln n m

/-- The combination `n`: `temp[cnt-1]`, the bits, `temp[0]`, each with its `/`. -/
def wid (cnt : Nat) (ln : Nat → Addr) (n : Nat) : Nat :=
  (ln (cnt - 1)).toNat + 1 + bts ln n (cnt - 2) + ((ln 0).toNat + 1)

/-- The combinations below `n` (step 2). -/
def rem (cnt : Nat) (ln : Nat → Addr) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => wid cnt ln n + rem cnt ln n

theorem rem_step (cnt : Nat) (ln : Nat → Addr) (i : Nat) :
    rem cnt ln (2 * i + 2) = wid cnt ln (2 * i) + rem cnt ln (2 * i) := rfl

/-- Bit `m + 1` of `n` (`cnt` = 3 or 4) as `vc_1294c`, `vc_1294s` take it. -/
theorem bit_cases {cnt n m : Nat} (hc : cnt = 3 ∧ (n = 0 ∨ n = 2) ∨ cnt = 4 ∧ (n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6))
    (hm : m + 1 + 2 ≤ cnt) :
    (n.testBit (m + 1) = false ∧ (m + 1 = 1 ∧ (n = 0 ∨ n = 4) ∧ (if m = 0 then 1343 else 1294) = 1343 ∨
      m + 1 = 2 ∧ (n = 0 ∨ n = 2) ∧ (if m = 0 then 1343 else 1294) = 1294)) ∨
    (n.testBit (m + 1) = true ∧ (m + 1 = 1 ∧ (n = 2 ∨ n = 6) ∨ m + 1 = 2 ∧ (n = 4 ∨ n = 6))) := by
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  all_goals
    revert hm
    rcases hc with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩
    all_goals decide

theorem jm {m : Nat} (h : m + 1 ≤ 2) :
    m + 1 = 1 ∧ (if m = 0 then 1343 else 1294) = 1343 ∨ m + 1 = 2 ∧ (if m = 0 then 1343 else 1294) = 1294 := by
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  all_goals decide

/-! ## The bits -/

/-- The bits `m, …, 1` of `n` (from 1294, at 1343 when `m = 0`): `rdi` from `p` to `pe = p + bts n m`. -/
theorem inner (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    {V₀ : Addr → Byte} (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V₀ a) → Pm W)
    {A B pe cnt n : Nat} {sp R bp S0 : Addr} {ln st : Nat → Addr}
    (hc : cnt = 3 ∧ (n = 0 ∨ n = 2) ∨ cnt = 4 ∧ (n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6))
    (hlo : 7940480 ≤ A) (hB : B ≤ sp.toNat - 8) (hsp8 : 8 ≤ sp.toNat) (hpeB : pe ≤ B)
    (hbuf : ∀ a : Addr, A ≤ a.toNat → a.toNat < B → Foot Wl a)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hRs : sp.toNat ≤ R.toNat) (hRC : R.toNat + 16 * cnt ≤ 2 ^ 64)
    (hfR : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hlm : ∀ m, 1 ≤ m → m + 2 ≤ cnt → rdq(V₀, R + BitVec.ofNat 64 (16 * m + 8)) = ln m ∧
      rdq(V₀, R + BitVec.ofNat 64 (16 * m)) = st m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ A ∨ B ≤ (st m).toNat)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = hwc_at.add 1343 →
      Z.cpu.gpr.rsp = sp → Z.cpu.gpr.rbx = R → Z.cpu.gpr.rbp = bp → Z.cpu.gpr.r12 = BitVec.ofNat 64 n →
      Z.cpu.gpr.r13 = 1#64 → Z.cpu.gpr.r15 = S0 → Z.cpu.gpr.rdi.toNat = pe →
      Outs V₀ W A pe sp.toNat → GoG prof L o gev gP gE Z t') :
    ∀ m, m + 2 ≤ cnt → ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = hwc_at.add (if m = 0 then 1343 else 1294) → X.cpu.gpr.rsp = sp → X.cpu.gpr.rbx = R →
      X.cpu.gpr.rbp = bp → X.cpu.gpr.r12 = BitVec.ofNat 64 n → X.cpu.gpr.r13 = 1#64 →
      X.cpu.gpr.r14 = BitVec.ofNat 64 m → X.cpu.gpr.r15 = S0 → A ≤ X.cpu.gpr.rdi.toNat →
      X.cpu.gpr.rdi.toNat + bts ln n m = pe → Outs V₀ V A X.cpu.gpr.rdi.toNat sp.toNat →
      GoG prof L o gev gP gE X t := by
  have hsl := sp.isLt
  intro m
  induction m with
  | zero =>
    intro _ X t V hK hA hrip hsp hbx hbp h12 h13 _ h15 _ hpe hO
    simp only [bts, Nat.add_zero] at hpe
    exact k X t V hK hA (by rw [hrip, if_pos (rfl : (0 : Nat) = 0)]) hsp hbx hbp h12 h13 h15 hpe
      (by rw [← hpe]; exact hO)
  | succ m ih =>
    intro hm X t V hK hA hrip hsp hbx hbp h12 h13 h14 h15 hp hpe hO
    have hr : X.cpu.rip = hwc_at.add 1294 := by rw [hrip, if_neg (Nat.succ_ne_zero m)]
    rcases bit_cases hc hm with ⟨hb, hcc⟩ | ⟨hb, hcs⟩
    · -- the bit clear
      simp only [bts, hb, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hpe
      refine (c_1294 prof fb).run c hfs hin _ hK hA hr
        (vc_1294c (m := m + 1) (r := n) (j := if m = 0 then 1343 else 1294) hcc h13 h14 h12) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      exact ih (by omega) Y t' V hKY hAY hrY (by rw [hgY]; exact hsp) (by rw [hgY]; exact hbx)
        (by rw [hgY]; exact hbp) (by rw [hgY]; exact h12) (by rw [hgY]; exact h13)
        (by simp only [hgY, Nat.add_sub_cancel]) (by rw [hgY]; exact h15) (by rw [hgY]; exact hp)
        (by rw [hgY]; exact hpe) (by rw [hgY]; exact hO)
    · -- the bit set: `temp[m + 1]`
      simp only [bts, hb, ↓reduceIte] at hpe
      obtain ⟨hL, hS⟩ := hlm (m + 1) (by omega) (by omega)
      have e8 : (R + BitVec.ofNat 64 (16 * (m + 1) + 8)).toNat = R.toNat + (16 * (m + 1) + 8) := addO (by omega)
      have e0 : (R + BitVec.ofNat 64 (16 * (m + 1))).toNat = R.toNat + 16 * (m + 1) := addO (by omega)
      refine (c_1294 prof fb).run c hfs hin _ hK hA hr
        (vc_1294s (m := m + 1) (r := n) (L := ln (m + 1)) (S := st (m + 1)) hcs h13 h14 h12
          (by rw [hbx, hO.2.2.rdq (by omega) (by omega) (by omega)]; exact hL)
          (by rw [hbx, hO.2.2.rdq (by omega) (by omega) (by omega)]; exact hS)
          (fun i hi => by
            rw [hbx]
            exact hfR _ (by rw [toNat_add_of_fits hi (by omega)]; omega)
              (by rw [toNat_add_of_fits hi (by omega)]; omega))
          (fun i hi => by
            rw [hbx]
            exact hfR _ (by rw [toNat_add_of_fits hi (by omega)]; omega)
              (by rw [toNat_add_of_fits hi (by omega)]; omega))) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]
      refine mcpy c hin (j := 1325) (by omega) (call_1325 _) (by decide) hinc hc0 hcpy hPm hlo hB hsp8 hbuf hst
        (S := st (m + 1)) (Ln := ln (m + 1)) hKY hAY hrY (by rw [hgY]; exact hsp) (by rw [hgY]) (by rw [hgY])
        (by rw [hdi]; exact hp) (by rw [hdi]; omega) (by rw [hdi]; exact hO) (hsrc _ (by omega))
        (hs64 _ (by omega)) (hsd _ (by omega)) ?_
      intro Z t₂ V₂ hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hOZ
      rw [hdi] at haxZ hOZ
      have hax : Z.cpu.gpr.rax.toNat = X.cpu.gpr.rdi.toNat + (ln (m + 1)).toNat := by
        rw [haxZ]; exact addN (by omega)
      refine (c_1330 prof fb).run c hfs hin _ hKZ hAZ hrZ
        (vc_1330 (m := m + 1) (j := if m = 0 then 1343 else 1294) (jm (by omega))
          (h14Z.trans (by rw [hgY]; exact h14))
          (fun i hi => by
            obtain rfl : i = 0 := by omega
            rw [addr_add_zero]
            exact hbuf _ (by omega) (by omega))) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
      have hdiU : U.cpu.gpr.rdi.toNat = X.cpu.gpr.rdi.toNat + (ln (m + 1)).toNat + 1 := by
        rw [hgU]
        show (Z.cpu.gpr.rax + 1#64).toNat = _
        rw [add1 (by omega), hax]
      refine ih (by omega) U t₃ _ hKU hAU hrU (by rw [hgU]; exact hspZ)
        (by rw [hgU]; exact hbxZ.trans (by rw [hgY]; exact hbx))
        (by rw [hgU]; exact hbpZ.trans (by rw [hgY]; exact hbp))
        (by rw [hgU]; exact h12Z.trans (by rw [hgY]; exact h12))
        (by rw [hgU]; exact h13Z.trans (by rw [hgY]; exact h13)) (by simp only [hgU, Nat.add_sub_cancel])
        (by rw [hgU]; exact h15Z.trans (by rw [hgY]; exact h15)) (by rw [hdiU]; omega) (by rw [hdiU]; omega)
        (by rw [hdiU]; exact hOZ.sl hax (by omega) (by omega) (by omega))

/-! ## The combinations -/

theorem o60 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551520#64).toNat = (r + 18446744073709551448#64).toNat + 72 := by
  bv_omega

theorem o58 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551528#64).toNat = (r + 18446744073709551448#64).toNat + 80 := by
  bv_omega

theorem o50 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551536#64).toNat = (r + 18446744073709551448#64).toNat + 88 := by
  bv_omega

theorem o48 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551544#64).toNat = (r + 18446744073709551448#64).toNat + 96 := by
  bv_omega

theorem oa0 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551456#64).toNat = (r + 18446744073709551448#64).toNat + 8 := by
  bv_omega

theorem o80 {r : Addr} (h : (r + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64) :
    (r + 18446744073709551488#64).toNat = (r + 18446744073709551448#64).toNat + 40 := by
  bv_omega

/-- The combinations `n = 2 i, 2 i - 2, …, 0` (from 1248 with `r12 = 2 i + 2`, `rdi = p`): to 1392 with `rax = 0`,
`rcx = Ev`, `r12 = Cv`, `r14 = Pv` (from the frame), the bytes from `A` to `pe = p + rem (2 i + 2)` written. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    {V₀ : Addr → Byte} (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V₀ a) → Pm W)
    {A B pe cnt : Nat} {sp R bp Ev Cv Pv : Addr} {ln st : Nat → Addr} (hcn : cnt = 3 ∨ cnt = 4)
    (hlo : 7940480 ≤ A) (hB : B ≤ sp.toNat - 8) (hsp8 : 8 ≤ sp.toNat) (hpeB : pe ≤ B)
    (hbuf : ∀ a : Addr, A ≤ a.toNat → a.toNat < B → Foot Wl a)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hRs : sp.toNat ≤ R.toNat) (hRC : R.toNat + 16 * cnt ≤ 2 ^ 64)
    (hfR : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hlm : ∀ m, 1 ≤ m → m + 2 ≤ cnt → rdq(V₀, R + BitVec.ofNat 64 (16 * m + 8)) = ln m ∧
      rdq(V₀, R + BitVec.ofNat 64 (16 * m)) = st m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ A ∨ B ≤ (st m).toNat)
    (hsf : sp.toNat ≤ (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hq₀ : rdq(V₀, bp + 18446744073709551520#64) = BitVec.ofNat 64 (cnt - 2))
    (hS₀ : rdq(V₀, bp + 18446744073709551528#64) = st (cnt - 1))
    (hL₀ : rdq(V₀, bp + 18446744073709551536#64) = ln (cnt - 1))
    (hl₀ : rdq(V₀, bp + 18446744073709551544#64) = ln 0)
    (hC₀ : rdq(V₀, bp + 18446744073709551456#64) = Cv)
    (hP₀ : rdq(V₀, bp + 18446744073709551448#64) = Pv)
    (hE₀ : rdq(V₀, bp + 18446744073709551488#64) = Ev)
    (hf60 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551520#64) i))
    (hf58 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551528#64) i))
    (hf50 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551536#64) i))
    (hf48 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551544#64) i))
    (hfa0 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551456#64) i))
    (hfa8 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551448#64) i))
    (hf80 : ∀ i < 8, Foot F.data (Addr.add (bp + 18446744073709551488#64) i))
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = hwc_at.add 1392 →
      Z.cpu.gpr.rax = 0#64 → Z.cpu.gpr.rcx = Ev → Z.cpu.gpr.r12 = Cv → Z.cpu.gpr.r14 = Pv →
      Z.cpu.gpr.rsp = sp → Z.cpu.gpr.rbx = R → Z.cpu.gpr.rbp = bp → Z.cpu.gpr.rdi.toNat = pe →
      Outs V₀ W A pe sp.toNat → GoG prof L o gev gP gE Z t') :
    ∀ i, 2 * i + 2 ≤ 2 ^ (cnt - 1) → ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1248 → X.cpu.gpr.rsp = sp → X.cpu.gpr.rbx = R →
      X.cpu.gpr.rbp = bp → X.cpu.gpr.r12 = BitVec.ofNat 64 (2 * i + 2) → X.cpu.gpr.r13 = 1#64 →
      X.cpu.gpr.r15 = st 0 → A ≤ X.cpu.gpr.rdi.toNat → X.cpu.gpr.rdi.toNat + rem cnt ln (2 * i + 2) = pe →
      Outs V₀ V A X.cpu.gpr.rdi.toNat sp.toNat → GoG prof L o gev gP gE X t := by
  have hsl := sp.isLt
  have rdF : ∀ {W : Addr → Byte} {a p : Nat} {x : Addr}, Outs V₀ W a p sp.toNat →
      (bp + 18446744073709551448#64).toNat ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 → rdq(W, x) = rdq(V₀, x) :=
    fun hO h1 h2 => hO.2.2.rdq (by omega) h2 h2
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hN X t V hK hA hrip hsp hbx hbp h12 h13 h15 hp hpe hO
    have hi : cnt = 3 ∧ i ≤ 1 ∨ cnt = 4 ∧ i ≤ 3 := by
      rcases hcn with rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] at hN <;> omega
    rw [rem_step] at hpe
    have hw : wid cnt ln (2 * i) = (ln (cnt - 1)).toNat + 1 + bts ln (2 * i) (cnt - 2) + ((ln 0).toNat + 1) := rfl
    -- `temp[cnt-1]`
    refine (c_1248 prof fb).run c hfs hin _ hK hA hrip
      (vc_1248 (r := 2 * i + 2) (L := ln (cnt - 1)) (S := st (cnt - 1)) h12 (by omega)
        (by rw [hbp, rdF hO (by rw [o50 hfb]; omega) (by rw [o50 hfb]; omega)]; exact hL₀)
        (by rw [hbp, rdF hO (by rw [o58 hfb]; omega) (by rw [o58 hfb]; omega)]; exact hS₀)
        (by rw [hbp]; exact hf50) (by rw [hbp]; exact hf58)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
    have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]
    refine mcpy c hin (j := 1260) (by omega) (call_1260 _) (by decide) hinc hc0 hcpy hPm hlo hB hsp8 hbuf hst
      (S := st (cnt - 1)) (Ln := ln (cnt - 1)) hKY hAY hrY (by rw [hgY]; exact hsp) (by rw [hgY]) (by rw [hgY])
      (by rw [hdi]; exact hp) (by rw [hdi]; omega) (by rw [hdi]; exact hO) (hsrc _ (by omega)) (hs64 _ (by omega))
      (hsd _ (by omega)) ?_
    intro Z t₂ V₂ hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hOZ
    rw [hdi] at haxZ hOZ
    have hax : Z.cpu.gpr.rax.toNat = X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat := by
      rw [haxZ]; exact addN (by omega)
    have hbpZ' : Z.cpu.gpr.rbp = bp := hbpZ.trans (by rw [hgY]; exact hbp)
    -- `/`, `m = cnt - 2`
    refine (c_1265 prof fb).run c hfs hin _ hKZ hAZ hrZ
      (vc_1265 (q := BitVec.ofNat 64 (cnt - 2))
        (by rw [hbpZ', rdF hOZ (by rw [o60 hfb]; omega) (by rw [o60 hfb]; omega)]; exact hq₀)
        (by rw [hbpZ']; exact hf60)
        (fun i hi => by
          obtain rfl : i = 0 := by omega
          rw [addr_add_zero]
          exact hbuf _ (by omega) (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
    have hdiU : U.cpu.gpr.rdi.toNat = X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat + 1 := by
      rw [hgU]
      show (Z.cpu.gpr.rax + 1#64).toNat = _
      rw [add1 (by omega), hax]
    -- the bits, to 1343
    refine inner c hfs hin hinc hc0 hcpy hPm (n := 2 * i) (bp := bp) (S0 := st 0)
      (pe := X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat + 1 + bts ln (2 * i) (cnt - 2)) (by omega) hlo hB hsp8
      (by omega) hbuf hst hRs hRC hfR hlm hsrc hs64 hsd ?_ (cnt - 2) (by omega) U t₃ _ hKU hAU
      (by rw [hrU, if_neg (show cnt - 2 ≠ 0 by omega)]) (by rw [hgU]; exact hspZ)
      (by rw [hgU]; exact hbxZ.trans (by rw [hgY]; exact hbx))
      (by rw [hgU]; exact hbpZ') (by rw [hgU]; exact h12Z.trans (by simp only [hgY, Nat.add_sub_cancel]))
      (by rw [hgU]; exact h13Z.trans (by rw [hgY]; exact h13)) (by simp only [hgU])
      (by rw [hgU]; exact h15Z.trans (by rw [hgY]; exact h15)) (by rw [hdiU]; omega) (by rw [hdiU])
      (by rw [hdiU]; exact hOZ.sl hax (by omega) (by omega) (by omega))
    intro Z₁ t₄ W₁ hK₁ hA₁ hr₁ hsp₁ hbx₁ hbp₁ h12₁ h13₁ h15₁ hdi₁ hO₁
    -- `temp[0]`
    refine (c_1343 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
      (vc_1343 (L := ln 0) (by rw [hbp₁, rdF hO₁ (by rw [o48 hfb]; omega) (by rw [o48 hfb]; omega)]; exact hl₀)
        (by rw [hbp₁]; exact hf48)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₂ t₅ hKY₂ hAY₂ hrY₂ hgY₂ -
    have hdi₂ : Y₂.cpu.gpr.rdi = Z₁.cpu.gpr.rdi := by rw [hgY₂]
    refine mcpy c hin (j := 1350) (by omega) (call_1350 _) (by decide) hinc hc0 hcpy hPm hlo hB hsp8 hbuf hst
      (S := st 0) (Ln := ln 0) hKY₂ hAY₂ hrY₂ (by rw [hgY₂]; exact hsp₁) (by rw [hgY₂]; exact h15₁) (by rw [hgY₂])
      (by rw [hdi₂, hdi₁]; omega) (by rw [hdi₂, hdi₁]; omega) (by rw [hdi₂, hdi₁]; exact hO₁) (hsrc _ (by omega))
      (hs64 _ (by omega)) (hsd _ (by omega)) ?_
    intro Z₂ t₆ V₃ hKZ₂ hAZ₂ hrZ₂ hspZ₂ haxZ₂ hbxZ₂ hbpZ₂ h12Z₂ h13Z₂ h14Z₂ h15Z₂ hOZ₂
    rw [hdi₂, hdi₁] at hOZ₂
    rw [hdi₂] at haxZ₂
    have hax₂ : Z₂.cpu.gpr.rax.toNat = X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat + 1 + bts ln (2 * i) (cnt - 2) +
        (ln 0).toNat := by
      rw [haxZ₂, addN (by omega), hdi₁]
    have hbp₂ : Z₂.cpu.gpr.rbp = bp := hbpZ₂.trans (by rw [hgY₂]; exact hbp₁)
    have hO₂ := hOZ₂.sl hax₂ (by omega) (by omega) (by omega)
    have hs₂ : ∀ i < 1, Foot Wl (Addr.add Z₂.cpu.gpr.rax i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero]
      exact hbuf _ (by omega) (by omega)
    have h12₂ : Z₂.cpu.gpr.r12 = BitVec.ofNat 64 (2 * i) := h12Z₂.trans (by rw [hgY₂]; exact h12₁)
    rcases i with _ | i
    · -- `n = 0`: to 1392
      refine (c_1355 prof fb).run c hfs hin _ hKZ₂ hAZ₂ hrZ₂
        (vc_1355e (c := Cv) (P := Pv) (E := Ev) (h12₂.trans rfl)
          (by rw [hbp₂, rdF hO₂ (by rw [oa0 hfb]; omega) (by rw [oa0 hfb]; omega)]; exact hC₀)
          (by rw [hbp₂, rdF hO₂ (by omega) (by omega)]; exact hP₀)
          (by rw [hbp₂, rdF hO₂ (by rw [o80 hfb]; omega) (by rw [o80 hfb]; omega)]; exact hE₀)
          hs₂ (by rw [hbp₂]; exact hfa0) (by rw [hbp₂]; exact hfa8) (by rw [hbp₂]; exact hf80)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U₂ t₇ hKU₂ hAU₂ hrU₂ hgU₂ -
      have hpe' : X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat + 1 + bts ln (2 * 0) (cnt - 2) + (ln 0).toNat + 1 =
          pe := by
        have : rem cnt ln (2 * 0) = 0 := rfl
        omega
      refine k U₂ t₇ _ hKU₂ hAU₂ hrU₂ (by rw [hgU₂]) (by rw [hgU₂]) (by rw [hgU₂]) (by rw [hgU₂])
        (by rw [hgU₂]; exact hspZ₂.trans (by rw [hgY₂]; exact hsp₁))
        (by rw [hgU₂]; exact hbxZ₂.trans (by rw [hgY₂]; exact hbx₁)) (by rw [hgU₂]; exact hbp₂)
        (by rw [hgU₂]; show (Z₂.cpu.gpr.rax + 1#64).toNat = pe; rw [add1 (by omega), hax₂]; exact hpe')
        (by rw [← hpe']; exact hO₂)
    · -- `n = 2 i + 2`: the next combination
      refine (c_1355 prof fb).run c hfs hin _ hKZ₂ hAZ₂ hrZ₂ (vc_1355l (r := 2 * (i + 1)) h12₂ (by omega) hs₂) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U₂ t₇ hKU₂ hAU₂ hrU₂ hgU₂ -
      have hr2 : rem cnt ln (2 * (i + 1)) = rem cnt ln (2 * i + 2) := congrArg _ (by omega)
      have hdiU₂ : U₂.cpu.gpr.rdi.toNat = X.cpu.gpr.rdi.toNat + (ln (cnt - 1)).toNat + 1 +
          bts ln (2 * (i + 1)) (cnt - 2) + (ln 0).toNat + 1 := by
        rw [hgU₂]
        show (Z₂.cpu.gpr.rax + 1#64).toNat = _
        rw [add1 (by omega), hax₂]
      refine ih i (by omega) (by omega) U₂ t₇ _ hKU₂ hAU₂ hrU₂
        (by rw [hgU₂]; exact hspZ₂.trans (by rw [hgY₂]; exact hsp₁))
        (by rw [hgU₂]; exact hbxZ₂.trans (by rw [hgY₂]; exact hbx₁)) (by rw [hgU₂]; exact hbp₂)
        (by rw [hgU₂]; exact h12₂.trans (congrArg (BitVec.ofNat 64) (by omega)))
        (by rw [hgU₂]; exact h13Z₂.trans (by rw [hgY₂]; exact h13₁))
        (by rw [hgU₂]; exact h15Z₂.trans (by rw [hgY₂]; exact h15₁)) (by rw [hdiU₂]; omega)
        (by rw [hdiU₂]; omega) (by rw [hdiU₂]; exact hO₂)

end FV7z.Hwc
