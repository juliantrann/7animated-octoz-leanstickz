import FV7z.Acs.Holds
import FV7z.Asl.New
/-!
# `AString (s1, num1, s2, num2)` with `operator new` (PLAN.md §M, M1)

`acs_ok` takes `SetStartLen`'s call of `operator new` as a hypothesis (`kf`); `acs_okH` discharges it by
`Asl.kf_hpW` (`Onw.onw_hpW`), with `Mal.MalB (num1 + num2 + 1) B`, `Mal.Hp` with a top of at least `m + B` bytes
below `hi` at the entry, `hi` 312 bytes below `rsp` and `[hi, rsp)` in what the run may store into. `P1` is `Asl.Po`
for the registers and the bytes at `SetStartLen`'s entry (`gY`, `VY`): the block `_chars` below `hi` in the
footprint, `Mal.Hp … m` for the bytes outside it, the bytes outside the heap's words, the block and `_chars` as at
`SetStartLen`'s entry. `memcpy` (`km`, `kj`) stays a hypothesis.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Acs

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `acs_ok` with `operator new` by `Asl.kf_hpW`: see the module doc. -/
theorem acs_okH {P2 : State → (Addr → Byte) → Prop} {fb : Addr} {hi m B : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L acs_at acs)
    (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw) (hinN : CodeIn L mnx_at mnx)
    (hinI : CodeIn L imm_at imm) {codeM : List Byte} (hinM : CodeIn L 0x401070#64 codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acs_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (BitVec.setWidth 64 (nl X.cpu.gpr) + 1#64) B)
    (hhi : hi + 312 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    (km : ∀ (Z : State) (V' : Addr → Byte), Asl.Po F Wl fb hi m (gY X.cpu.gpr) (VY V X.cpu.gpr) Z V' →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V1 V' X.cpu.gpr.rdi (nl X.cpu.gpr) Z.cpu.gpr.rax) (X.cpu.gpr.rsp - 48)
          (toBytesLE (acs_at.add 50) 8)) →
      Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        ({ Z.cpu.gpr with
            rbx := zd X.cpu.gpr
            rbp := zr X.cpu.gpr
            rdi := Z.cpu.gpr.rax
            rdx := zd X.cpu.gpr
            rsi := X.cpu.gpr.rsi } : Gprs).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = acs_at.add 50 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = zd X.cpu.gpr →
        Z₂.cpu.gpr.rbp = zr X.cpu.gpr → Z₂.cpu.gpr.r13 = X.cpu.gpr.rcx → Sv V'' X.cpu.gpr → P2 Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kj : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V'' → Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        { Z₂.cpu.gpr with
            rdx := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.r8 + 1#32)
            rsi := X.cpu.gpr.rcx
            rdi := Z₂.cpu.gpr.rax + zd X.cpu.gpr
            rbx := X.cpu.gpr.rbx
            rbp := X.cpu.gpr.rbp
            r12 := X.cpu.gpr.r12
            r13 := X.cpu.gpr.r13
            r14 := X.cpu.gpr.r14
            rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hB3 : 64 ≤ B := hB.2.2
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn56 : (X.cpu.gpr.rsp - 56).toNat = X.cpu.gpr.rsp.toNat - 56 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn64 : (X.cpu.gpr.rsp - 64).toNat = X.cpu.gpr.rsp.toNat - 64 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn80 : (X.cpu.gpr.rsp - 80).toNat = X.cpu.gpr.rsp.toNat - 80 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 80 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  have vo : ∀ (W : Addr → Byte) (x : Addr) (v : BitVec 64) (a : Addr), a.toNat < x.toNat →
      x.toNat + 8 ≤ 2 ^ 64 → Vst W x (toBytesLE v 8) a = W a := fun W x v a h1 h2 =>
    Tun.Vst_out W x _ a (by rw [l8]; exact h2) (.inl h1)
  -- the bytes at `SetStartLen`'s entry below the pushes
  have hVY : ∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 48 → VY V X.cpu.gpr a = V a := by
    intro a ha
    show Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (acs_at.add 35) 8) a = V a
    rw [vo _ (X.cpu.gpr.rsp - 48) _ a (by rw [tn48]; omega) (by rw [tn48]; omega)]
    dsimp only [V0]
    rw [vo _ (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) _ a (by rw [e40, tn40]; omega) (by rw [e40, tn40]; omega),
      vo _ (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) _ a (by rw [e32, tn32]; omega) (by rw [e32, tn32]; omega),
      vo _ (X.cpu.gpr.rsp - 8 - 8 - 8) _ a (by rw [e24, tn24]; omega) (by rw [e24, tn24]; omega),
      vo _ (X.cpu.gpr.rsp - 8 - 8) _ a (by rw [e16, tn16]; omega) (by rw [e16, tn16]; omega),
      vo _ (X.cpu.gpr.rsp - 8) _ a (by rw [tn8]; omega) (by rw [tn8]; omega)]
  have hH' : Mal.Hp F Wl fb hi (m + B) (VY V X.cpu.gpr) := Mal.Hp.mv hH (by omega) fun a _ a2 => hVY a (by omega)
  have hgs : (gY X.cpu.gpr).rsp = X.cpu.gpr.rsp - 48 := rfl
  have hgd : (gY X.cpu.gpr).rdi = X.cpu.gpr.rdi := rfl
  refine acs_ok (P1 := Asl.Po F Wl fb hi m (gY X.cpu.gpr) (VY V X.cpu.gpr)) c hin hinS hinW hinM hM hK hA hrip
    (by omega) hp8 (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega))
    (hfw _ 24 tn24 (by omega) (by omega)) (hfw _ 32 tn32 (by omega) (by omega)) (hfw _ 40 tn40 (by omega) (by omega))
    (hfw _ 48 tn48 (by omega) (by omega)) (hfw _ 56 tn56 (by omega) (by omega)) (hfw _ 64 tn64 (by omega) (by omega))
    (hfw _ 80 tn80 (by omega) (by omega)) fw0 fw8 fw12 hq hd ?_ km kj
  intro Y t' hKY hAY hrY hgY k
  refine Asl.kf_hpW (g := gY X.cpu.gpr) (ra := acs_at.add 35) c hfs hinS hinW hinN hinI hH'
    (by show Mal.MalB (BitVec.setWidth 64 (BitVec.setWidth 32 (gS X.cpu.gpr).rsi) + 1#64) B; rw [lnE]; exact hB)
    (by rw [hgs, tn48]; omega) (by rw [hgs, tn48]; omega) (fun a h1 h2 => hsw a h1 (by rw [hgs, tn48] at h2; omega))
    (by rw [hgd]; exact hq) (by rw [hgd, hgs, tn48]; omega) (by rw [hgd]; exact hdh) ?_ Y t' hKY hAY hrY hgY ?_
  · rw [hgs]
    show rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (acs_at.add 35) 8), X.cpu.gpr.rsp - 48) =
      acs_at.add 35
    rw [Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (acs_at.add 35) 8) (l8 _)
      (by rw [tn48]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  · intro Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 hPo
    exact k Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 ⟨hPo.1, hPo.2.1, hPo.2.2.1, hPo⟩

end FV7z.Acs
