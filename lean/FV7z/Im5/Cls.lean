import FV7z.Im2.RunN
/-!
# `_int_malloc`: the request classes and the second call as a statement (PLAN.md G3, `malloc`)

- `clsL`: `n + 23` above 31 and rounded to `16 k`, `64 ≤ k ≤ 257` (a largebin size).
- `ClsA n nb`: `nb` the chunk size of a request `n ≤ 4104`: `Im3.Cls` (`n ≤ 1000`, the fastbin and smallbin sizes) or
  `1001 ≤ n ≤ 4104` (a largebin size); `ClsA.cases` (`nb = 16 k`, `2 ≤ k ≤ 257`), `ClsA.bnd`.
- `SecA n nb`: what `_int_malloc` does on the second call for `n` (the statement of `RunA.im_secondA` for one class):
  the code that calls it (`Mhi.mhi_tailn`, `Mnx.mal_next`) takes it as a hypothesis, so it does not import the
  largebin path (`Im5.L1` … `L6`). `secS`: every `Im3.Cls` request (`Im2.im_secondn`); `RunA.secA`: every `ClsA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at)
open FV7z.Im2 (VspN and_m16)
namespace FV7z.Im5

/-- A request `1001 ≤ n ≤ 4104`: `n + 23` is above 31 and rounds to `16 k`, `64 ≤ k ≤ 257`. -/
theorem clsL {n : Addr} (h1 : 1001 ≤ n.toNat) (h2 : n.toNat ≤ 4104) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    ∃ k, 64 ≤ k ∧ k ≤ 257 ∧ n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega),
    (n.toNat + 23) / 16, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e, BitVec.toNat_ofNat]; omega

/-- `nb` the chunk size of a request `n ≤ 4104`. -/
def ClsA (n nb : Addr) : Prop :=
  Im3.Cls n nb ∨ (1001 ≤ n.toNat ∧ n.toNat ≤ 4104 ∧ n + 23#64 &&& 18446744073709551600#64 = nb)

theorem ClsA.cases {n nb : Addr} (h : ClsA n nb) : ∃ k, 2 ≤ k ∧ k ≤ 257 ∧ nb = BitVec.ofNat 64 (16 * k) := by
  rcases h with h | ⟨h1, h2, rfl⟩
  · obtain ⟨k, k1, k2, e⟩ := h.cases
    exact ⟨k, k1, by omega, e⟩
  · obtain ⟨-, -, -, k, k1, k2, e⟩ := clsL h1 h2
    exact ⟨k, by omega, k2, e⟩

theorem ClsA.bnd {n nb : Addr} (h : ClsA n nb) : 32 ≤ nb.toNat ∧ nb.toNat ≤ 4112 := by
  obtain ⟨k, h1, h2, rfl⟩ := h.cases
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `_int_malloc` on the second call for the request `n` (`nb` its chunk size): the hypotheses of `RunA.im_secondA`
but the class. -/
def SecA (n nb : Addr) : Prop :=
  ∀ {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle}
    {t : Nat} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {V : Addr → Byte} {fb S T szw sm : Addr}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = n) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 →
      rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (hlb : ∀ i, 64 ≤ i → i ≤ 99 →
      rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ M Z t', Im2.Fr S X.cpu.gpr V M → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw nb M) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t'),
    GoG prof L o gev gP gE X t

/-- Every fastbin or smallbin request (`Im3.Cls`): `Im2.im_secondn`. -/
theorem secS {n nb : Addr} (h : Im3.Cls n nb) : SecA n nb := by
  intro prof F Wl L s₀ X o t gev gP gE V fb S T szw sm c hfs hin hK hA hrip hrsp hsi hdi hS hlo hfb hgm hfc hfz hbk
    hlb htc htb hun hm0 hm1 hm2 hm3 hW hgf htf hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge e₂ code₂ hin₂ j₂ h₂ hra k
  exact Im2.im_secondn c hfs hin hK hA hrip hrsp hsi hdi h hS hlo hfb hgm hfz hbk htc htb hun hm0 hm1 hm2 hm3 hW
    hgf htf hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge hin₂ h₂ hra
    (fun Z t' => k _ Z t' (Im2.Fr.v2n S X.cpu.gpr n nb V hS))

end FV7z.Im5
