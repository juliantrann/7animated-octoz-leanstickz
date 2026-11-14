import FV7z.Hwc.Ptrs
/-!
# `_dl_important_hwcaps`: from 1392 to the `ret` (PLAN.md G3, startup)

`zero` (the lengths 0, 1392 → 1448), `caps_loop` (the capabilities, → 1522), `vc_1522`, `half1` (1568 → 1602),
`mid` (→ 1681). With `cnt` = 3 or 4 capabilities, `E = 2^cnt` entries at `P = r14`, `temp` at `rbx` (`cnt` entries),
the frame above the table: the lengths `caps E (tlen V₀ rbx) cnt 0`, the pointers `pt σ₀ … (2^(cnt-1)) T` (`σ₀` the
pointers at 1392: `str[0]`, `str[1]`), `*Q = len[0]`, the callee-saved registers from the frame.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

theorem off8c {r : Addr} (h : (r + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64) :
    (r + 18446744073709551476#64).toNat = (r + 18446744073709551464#64).toNat + 12 := by
  bv_omega

theorem off78 {r : Addr} (h : (r + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64) :
    (r + 18446744073709551496#64).toNat = (r + 18446744073709551464#64).toNat + 32 := by
  bv_omega

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}

/-- 1392 (`rax = 0`, `rcx = E`, `r12 = cnt`) to the `ret` (1681). -/
theorem post (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    {g₀ : Gprs} {cnt E D H : Nat} {T Q : Addr} {V₀ : Addr → Byte}
    (hcnt : cnt = 3 ∧ E = 8 ∧ D = 48 ∧ H = 4 ∨ cnt = 4 ∧ E = 16 ∧ D = 64 ∧ H = 8)
    (hrcx : g₀.rcx = BitVec.ofNat 64 E) (hr12 : g₀.r12 = BitVec.ofNat 64 cnt)
    (hPR : g₀.r14.toNat + 16 * E ≤ g₀.rbx.toNat) (hRC : g₀.rbx.toNat + 16 * cnt ≤ 2 ^ 64)
    (hfr : g₀.r14.toNat + 16 * E ≤ (g₀.rbp + 18446744073709551464#64).toNat)
    (hfr' : (g₀.rbp + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64)
    (hR : rdq(V₀, g₀.rbp + 18446744073709551480#64) = BitVec.ofNat 64 E)
    (hD : rdq(V₀, g₀.rbp + 18446744073709551464#64) = BitVec.ofNat 64 D)
    (hE4 : rdd(V₀, g₀.rbp + 18446744073709551476#64) = BitVec.ofNat 32 E)
    (hm : ofBytesLE 8 (List.map V₀ (byteAddrs (g₀.rbp + 18446744073709551496#64) 1)) = BitVec.ofNat 8 (cnt - 1))
    (hq₀ : rdd(V₀, g₀.rbp + 18446744073709551512#64) = BitVec.ofNat 32 H)
    (hT₀ : rdq(V₀, g₀.rbp + 18446744073709551536#64) = T)
    (hQ₀ : rdq(V₀, g₀.rbp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hW : ∀ a : Addr, g₀.r14.toNat ≤ a.toNat → a.toNat < g₀.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, g₀.rbx.toNat ≤ a.toNat → a.toNat < g₀.rbx.toNat + 16 * cnt → Foot F.data a)
    (hf88 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551480#64) i))
    (hf98 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551464#64) i))
    (hf8c : ∀ i < 4, Foot F.data (Addr.add (g₀.rbp + 18446744073709551476#64) i))
    (hf78 : ∀ i < 1, Foot F.data (Addr.add (g₀.rbp + 18446744073709551496#64) i))
    (hfq : ∀ i < 4, Foot F.data (Addr.add (g₀.rbp + 18446744073709551512#64) i))
    (hfT : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551536#64) i))
    (hfQ : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551504#64) i))
    (hf0 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551576#64) i))
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551584#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551592#64) i))
    (hf3 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551600#64) i))
    (hf4 : ∀ i < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551608#64) i))
    (hf5 : ∀ i < 8, Foot F.data (Addr.add g₀.rbp i))
    (k : ∀ Y t' (W : Addr → Byte) (σF : Nat → Addr) (a9 : Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 →
      Y.cpu.gpr = { g₀ with
        rax := g₀.r14, rcx := 0#64, rdx := 0#64 - BitVec.ofNat 64 (16 * H),
        rsi := g₀.r14 + BitVec.ofNat 64 (16 * E), rdi := T + 1#64, r8 := BitVec.ofNat 64 (16 * (E - 2 - H)),
        r9 := a9, r10 := BitVec.ofNat 64 E,
        rbx := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8),
          g₀.rbp + 18446744073709551576#64),
        r12 := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8),
          g₀.rbp + 18446744073709551584#64),
        r13 := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8),
          g₀.rbp + 18446744073709551592#64),
        r14 := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8),
          g₀.rbp + 18446744073709551600#64),
        r15 := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8),
          g₀.rbp + 18446744073709551608#64),
        rbp := rdq(Vst W Q (toBytesLE (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64) 0) 8), g₀.rbp),
        rsp := g₀.rbp + 8#64 } →
      Tab W g₀.r14 E σF (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64)) →
      (∀ j < E, σF j = pt (fun i => rdq(V₀, g₀.r14 + BitVec.ofNat 64 (16 * i)))
        (caps E (tlen V₀ g₀.rbx) cnt (fun _ => 0#64)) H T j) →
      Same V₀ W (g₀.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ W 0 g₀.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V₀ → X.cpu.rip = hwc_at.add 1392 →
      X.cpu.gpr = { g₀ with rax := 0#64 } → GoG prof L o gev gP gE X t := by
  intro X t hK hA hrip hgx
  have hED : E = 8 ∧ D = 48 ∨ E = 16 ∧ D = 64 := by omega
  have hn : cnt = 3 ∧ E = 8 ∨ cnt = 4 ∧ E = 16 := by omega
  have hHE : H = 4 ∧ E = 8 ∨ H = 8 ∧ E = 16 := by omega
  have hE0 : 0 < E := by omega
  have hE32 : E < 2 ^ 32 := by omega
  have hC : cnt ≤ 4 := by omega
  have hc3 : 3 ≤ cnt := by omega
  obtain rfl : H = 2 ^ (cnt - 1) := by
    rcases hcnt with ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ <;> rfl
  obtain rfl : D = 16 * cnt := by omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hrcx hr12 hPR hRC hfr hfr' hW hFT
  subst hrcx hr12
  have hPE : r14.toNat + 16 * E ≤ 2 ^ 64 := by have := rbx.isLt; omega
  refine zero (g₀ := ⟨rax, BitVec.ofNat 64 E, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11,
      BitVec.ofNat 64 cnt, r13, r14, r15⟩) (σ := fun i => rdq(V₀, r14 + BitVec.ofNat 64 (16 * i))) (V₀ := V₀)
    c hfs hin hED rfl hfr
    (by dsimp only; omega) hR hD (fun a h1 h2 => (hW a h1 h2).1) hf88 hf98 ?_ (E - 1) 0 (by omega) X t V₀
    (fun i => rdq(V₀, r14 + BitVec.ofNat 64 (16 * i + 8))) rdx hK hA hrip (hgx.trans rfl)
    (fun _ _ => ⟨rfl, rfl⟩) (fun j hj => absurd hj (Nat.not_lt_zero _)) (Same.refl _ _ _) (Same.refl _ _ _)
  -- 1448: the capabilities
  intro Y t' V' hKY hAY hrY hgY hT hS1 hS0
  refine caps_loop (g₂ := ⟨BitVec.ofNat 64 E, BitVec.ofNat 64 cnt, BitVec.ofNat 64 (16 * (E - 1)),
      rbx + BitVec.ofNat 64 (16 * cnt), rsp, rbp, rsi, 1#64, r8, r9, BitVec.ofNat 64 E, r11,
      BitVec.ofNat 64 cnt, r13, r14, r15⟩) (C := cnt) (R := rbx) (ℓF := caps E (tlen V₀ rbx) cnt (fun _ => 0#64))
    c hfs hin hE0 hE32 hC
    rfl rfl hPR hRC hW hFT ?_ (cnt - 1) (by omega) _ (by rw [show cnt - 1 + 1 = cnt by omega]) Y t' V'
    (BitVec.ofNat 64 E) (BitVec.ofNat 64 (16 * (E - 1))) rsi r8 r9 hKY hAY hrY
    (by rw [hgY, show cnt - 1 + 1 = cnt by omega]; try rfl) hT hS1 hS0
  -- 1522: the pointers
  intro Z t'' V'' a8 a9 hKZ hAZ hrZ hgZ hT2 hS1' hS0'
  dsimp only at hS1' hS0' hT2
  have hrbp : Z.cpu.gpr.rbp = rbp := by rw [hgZ]
  have hE' : rdd(V'', Z.cpu.gpr.rbp + 18446744073709551476#64) = BitVec.ofNat 32 E := by
    rw [hrbp, hS1'.rd (n := 4) (by rw [off8c hfr']; omega) (by rw [off8c hfr']; omega)
      (by rw [off8c hfr']; omega)]
    exact hE4
  have hm' : ofBytesLE 8 (List.map V'' (byteAddrs (Z.cpu.gpr.rbp + 18446744073709551496#64) 1)) =
      BitVec.ofNat 8 (cnt - 1) := by
    rw [hrbp, hS1'.rd (n := 1) (by rw [off78 hfr']; omega) (by rw [off78 hfr']; omega)
      (by rw [off78 hfr']; omega)]
    exact hm
  refine (c_1522 prof fb).run c hfs hin _ hKZ hAZ hrZ
    (vc_1522 (n := cnt) (E := E) hn hE' hm' (by rw [hrbp]; exact hf8c) (by rw [hrbp]; exact hf78)) ?_
  rintro j' g fl V3 ⟨rfl, rfl, rfl⟩ U t3 hKU hAU hrU hgU -
  rw [hgZ] at hgU
  exact half1 (g₃ := ⟨r14 + 32#64, BitVec.ofNat 64 (2 ^ (cnt - 1)), BitVec.ofNat 64 (E - 2), rbx, rsp, rbp,
      r14 + 32#64, 1#64, BitVec.ofNat 64 (E - 2), a9, BitVec.ofNat 64 E, r11, BitVec.ofNat 64 cnt, r13, r14, r15⟩)
    c hfs hin hHE rfl hPE hW
    (mid c hfs hin hHE rfl rfl rfl hPE hW hfr hfr' hq₀ hT₀ hfq hfT hQ₀ hsQ hfQ hf0 hf1 hf2 hf3 hf4 hf5
      (fun Y4 t4 W σF hK4 hA4 hr4 hg4 hT4 hσ hS4 hS4' =>
        k Y4 t4 W σF a9 hK4 hA4 hr4 (hg4.trans rfl) hT4 hσ hS4 hS4'))
    (2 ^ (cnt - 1) - 3) 2 (by omega) (Nat.le_refl _) U t3 _ 1#64 _ hKU hAU hrU (hgU.trans rfl) hT2
    (PD.two _ _) hS1' hS0'

end FV7z.Hwc
