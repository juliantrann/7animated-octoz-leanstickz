import FV7z.Uct.Holds
/-!
# `UString::UString ()` with `operator new` (PLAN.md §M, M1)

`uct_ok` takes the call of `operator new (16)` as a hypothesis (`kf`); `uct_okH` discharges it by `Onw.onw_hpW`
(`Mal.MalB 16 64`): with `Mal.Hp` with a top of at least `m + 64` bytes below `hi` at the entry, `hi` 248 bytes below
`rsp` and `[hi, rsp)` in what the run may store into, the object apart from the heap's bytes, the run reaches the
return address with `_chars` = the block `p` (16 bytes below `hi`, above the TLS block's words), `Mal.Hp … m` for the
bytes at the end, the bytes outside the heap's words, the block, the frame and `_chars` as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Uct

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `uct_ok` with `operator new` by `Onw.onw_hpW`: see the module doc. -/
theorem uct_okH {fb : Addr} {hi m : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L uct_at uct) (hinW : CodeIn L Onw.onw_at Onw.onw) (hinM : CodeIn L mnx_at mnx)
    (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uct_at)
    (hH : Mal.Hp F Wl fb hi (m + 64) V) (hhi : hi + 248 ≤ X.cpu.gpr.rsp.toNat)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64) (hR : X.cpu.gpr.rsp.toNat + 24 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat →
      Z.cpu.gpr.rax.toNat + 16 ≤ hi → Mal.Hp F Wl fb hi m (V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax) →
      (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
        X.cpu.gpr.rsp.toNat ≤ a.toNat) → (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        V' a = V a) →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (V1 V' X.cpu.gpr.rdi Z.cpu.gpr.rax) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rdx := 12884901888#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hTl : 8032256 ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', -⟩ := hH
    omega
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi' => by
    have e := toNat_add_of_fits (a := X.cpu.gpr.rsp - 8) (i := i) (n := 8) hi' (by rw [tn8]; omega)
    exact hsw _ (by rw [e, tn8]; omega) (by rw [e, tn8]; omega)
  have hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi' => by
    have e := toNat_add_of_fits (a := X.cpu.gpr.rsp - 16) (i := i) (n := 8) hi' (by rw [tn16]; omega)
    exact hsw _ (by rw [e, tn16]; omega) (by rw [e, tn16]; omega)
  refine uct_ok (Pc := fun Z V' => fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat ∧ Z.cpu.gpr.rax.toNat + 16 ≤ hi ∧
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < Z.cpu.gpr.rax.toNat ∨ Z.cpu.gpr.rax.toNat + 16 ≤ a.toNat) → W a = V' a) →
        Mal.Hp F Wl fb hi m W) ∧
      (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
        X.cpu.gpr.rsp.toNat ≤ a.toNat) → (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        V' a = V a))
    c hin hinW hK hA hrip (by omega) hp8 hs1 hs2 hl fw0 fw8 hq hd hin₂ h₂ ?_ ?_
  · intro Y t' hKY hAY hrY hgY k
    have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 16 := by rw [hgY]; try rfl
    have hYd : Y.cpu.gpr.rdi = 16#64 := by rw [hgY]; try rfl
    have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]; try rfl
    have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [hYs, tn16]
    -- the bytes at `operator new`'s entry outside the pushes and `_chars`
    have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
        (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) a = V a := by
      intro a h1 h2
      have s1 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) a
        (by rw [l8, tn16]; omega) (by rw [l8, tn16]; omega)
      have s2 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi
        (toBytesLE 0#64 8) a (by rw [l8]; omega) (by rw [l8]; omega)
      have s3 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) a (by rw [l8, tn8]; omega)
        (by rw [l8, tn8]; omega)
      exact s1.trans (s2.trans s3)
    have hH' : Mal.Hp F Wl fb hi (m + 64)
        (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8)) :=
      Mal.Hp.mv hH (by omega) fun a a1 a2 => hVo a (.inl (by omega)) (by rcases hdh with h | h <;> omega)
    have hra' : rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8), Y.cpu.gpr.rsp) =
        uct_at.add 25 := by
      rw [hYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) (l8 _)
        (by rw [tn16]; omega),
        ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
    have t16 : (16#64 : BitVec 64).toNat = 16 := rfl
    refine Onw.onw_hpW (B := 64) (m := m) c hfs hinW hinM hinI hKY hAY hrY hH' (by rw [hYd]; decide)
      (by rw [hYd]; exact ⟨by decide, by decide, by decide⟩) (by rw [hYt]; omega) (by rw [hYt]; omega)
      (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) hin (lt_len (by decide)) hra' ?_
    intro Z t'' V₂ p hKZ hAZ hrZ zsp zax zbx _ _ _ _ _ _ hpf hpe hfoot hV hPm
    rw [hYd, t16] at hpe hfoot
    rw [hYd, t16] at hPm
    -- what `operator new` keeps from `rsp` up
    have hVr : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat →
        V₂ a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) a := fun a ha =>
      hV a (.inr (.inr ⟨by omega, .inr (by rw [hYt]; exact ha)⟩))
    have hb : rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8))
        (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [tn8]; omega) fun a a1 _ => hVr a (by rw [tn8] at a1; omega)]
      rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) (X.cpu.gpr.rsp - 8) 8
        (by rw [l8, tn16]; omega) (by rw [tn8]; omega) (by rw [l8, tn16, tn8]; omega)]
      rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8)
        (X.cpu.gpr.rsp - 8) 8 (by rw [l8]; omega) (by rw [tn8]; omega) (by rw [l8, tn8]; omega)]
      rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) (l8 _) (by rw [tn8]; omega),
        ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
    have hr : rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8))
        (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 _ => hVr a (by omega)]
      rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) X.cpu.gpr.rsp 8
        (by rw [l8, tn16]; omega) hp8 (by rw [l8, tn16]; omega)]
      rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8)
        X.cpu.gpr.rsp 8 (by rw [l8]; omega) hp8 (by rw [l8]; omega)]
      rw [Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsp 8 (by rw [l8, tn8]; omega)
        hp8 (by rw [l8, tn8]; omega)]
      exact hra
    refine k Z V₂ t'' hKZ hAZ hrZ ?_ (by rw [zbx, hYb]) hb hr ?_ (by rw [zax]; omega) (.inl (by rw [zax]; omega))
      ⟨by rw [zax]; exact hpf, by rw [zax]; exact hpe, by rw [zax]; exact hPm, ?_⟩
    · rw [zsp, hYs]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, tn16, tn8]
      simp <;> omega
    · intro i hi'
      rw [zax]
      have e := toNat_add_of_fits (a := p) (i := i) (n := 16) (by omega) (by omega)
      exact (hfoot _ (by rw [e]; omega) (by rw [e]; omega)).1
    · intro a h1 h2
      rw [zax] at h1
      have hva : V₂ a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uct_at.add 25) 8) a := by
        rcases h1 with h1 | h1 | h1
        · exact hV a (.inl h1)
        · exact hV a (.inr (.inl h1))
        · exact hVr a (by omega)
      rw [hva]
      exact hVo a (by rcases h1 with h1 | h1 | h1 <;> omega) h2
  · intro Z V' Z' t' ⟨hp1, hp2, hPm, hfr⟩ hKZ' hAZ' hrZ' hgZ'
    refine kr Z V' Z' t' hp1 hp2 (hPm _ fun a a1 a2 a3 => ?_) hfr hKZ' hAZ' hrZ' hgZ'
    have s1 := Tun.Vst_out (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE Z.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 8#64)
      (toBytesLE 12884901888#64 8)) Z.cpu.gpr.rax (toBytesLE 0#32 4) a
      (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
    have s2 := Tun.Vst_out (Vst V' X.cpu.gpr.rdi (toBytesLE Z.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 8#64)
      (toBytesLE 12884901888#64 8) a (by rw [l8, t8]; omega) (by rw [l8, t8]; rcases hdh with h | h <;> omega)
    have s3 := Tun.Vst_out V' X.cpu.gpr.rdi (toBytesLE Z.cpu.gpr.rax 8) a (by rw [l8]; omega)
      (by rw [l8]; rcases hdh with h | h <;> omega)
    exact s1.trans (s2.trans s3)

end FV7z.Uct
