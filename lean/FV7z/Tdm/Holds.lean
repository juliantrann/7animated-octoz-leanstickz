import FV7z.Tdm.Vc1
import FV7z.Tdm.Vc2
import FV7z.Tdm.Vc3
import FV7z.Tun.Inv
/-!
# `LzmaDec_TryDummy` from its entry to the return address (PLAN.md §M, M1)

`vcAll`: every cut point's condition holds through its stretch (`Vc1`–`Vc3`). `tdm_ok`: `Seg.cfg` over the 37 cut
points, then the `ret` at 354 or 765: the five registers popped as pushed (`rd1`), the return address as at the
entry, `*bufOut` stored or not (`rdv`).

## Status (2026-11-27, kt2309 = run 45963066487, not green yet)

The Vc files are generated: `python3 tools/tdm_gen/gen.py lean/FV7z/Tdm` (cuts in `tools/tdm_gen/cuts.py`, the
head of `Ctx` in `tools/tdm_gen/ctx_head.lean`). Design: `Seg.cfg` with `Inv` = entry ∨ 36 cut disjuncts; each `vc_k`
is `wpx` then a `repeat' (first | …)` loop of foot closers (`fA`, `fIn`, `fP`, `fD`, frame reads) and exits `xJ`,
written `(refine xJ ?hc rfl ?hI ?hm; (case hc => tcm); …)` so that the side goals run after `K`/`g` are fixed, and
with `with_reducible` (default-transparency `exact`/`assumption` hit uncatchable whnf timeouts / maxRecDepth).

Green: `Ctx`, `Vc1`, `Vc2`, `Vc3` at f884b51 (kt2308 = run 45962344429, generated without `TDM_DBG`). What it took:
`dec_true`/`dec_false`/`nd_true`/`nd_false` and the guarded `dcd` elab (casts a jump's `decide` hypothesis by
`MVarId.replace`, no elaboration: the `cast` macro hit maxRecDepth at 648); `lits` (closed `BitVec.toNat` terms as
numerals, e.g. `(BitVec.setWidth 64 4#32).toNat` from a 32-bit `mov` of an immediate); `true_and`, `and_true`,
`true_or`, `or_true` in `tfo` (simp left `256 = 0 ∨ True`, which omega does not take); `MOD` for 1420→1432,
1472→1420, 1537→1400; `TDM_DBG` now overrides `MOD`.

Holds: kt2308 failed with three errors, fixed at e7ef035 (`vc_1537 (f := f)`; the `{ K.g0 with … }` of `k` on one
line, since the fields broke over lines do not parse; heartbeats). kt2309 then ran Holds ~55 min and out of memory
(runner shut down, exit 143), most likely in `tbo` (`bv_omega` over the frame's nested `- 8`/`+ 8` in the big
contexts of `rd1` and `tdm_ok`, ~37 calls). Plan B in this file (not built yet): `s8`/`a8` and `fr` give each frame
address's `toNat` one step at a time in a small context, and `tbo` is `eq_of_toNat_eq` then plain `omega` over those
atoms; heartbeats at 400000 so a blow-up fails fast.

Next steps in order:
1. Triage `FV7z.Tdm.Holds -- FV7z.Tdm.tdm_ok` (Vc1–Vc3 are cached on lane tri10); watch memory in live-j0 and stop
   at once if Holds grows past a few GB. If `fr` itself fails, split it into one lemma per fact.
2. `#print axioms tdm_ok` (propext, Classical.choice, Quot.sound); add the Tdm imports to `FV7z.lean` after the Dr2
   lines.

Triage: `triage.sh ktNNNN -L tri10 FV7z.Tdm.Ctx FV7z.Tdm.Vc1 FV7z.Tdm.Vc2 FV7z.Tdm.Vc3 FV7z.Tdm.Holds --
FV7z.Tdm.tdm_ok @sha`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tdm
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_354 : pret <+: tdm.drop 354 := by decide +kernel
theorem ret_354 (feat : Features) : Dec feat tdm 354 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 354) (k := 0) (pret_0 feat) w_354 (Nat.zero_le _)
theorem w_765 : pret <+: tdm.drop 765 := by decide +kernel
theorem ret_765 (feat : Features) : Dec feat tdm 765 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 765) (k := 0) (pret_0 feat) w_765 (Nat.zero_le _)

variable {K : Ctx} {F : Footprint} {Wl : List Rgn}

theorem vcAll (hO : Ok K) (hE : Env K F Wl) (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv K ℓ m g V) : Wt ℓ F Wl (Nx K m) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hc,
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ | ⟨rfl, rfl, hI, rfl⟩ |
    ⟨rfl, rfl, hI, rfl⟩⟩
  · exact vc_0 hO hE
  · exact vc_103 hO hE hc hI
  · exact vc_180 hO hE hc hI
  · exact vc_210 hO hE hc hI
  · exact vc_248 hO hE hc hI
  · exact vc_288 hO hE hc hI
  · exact vc_314 hO hE hc hI
  · exact vc_320 hO hE hc hI
  · exact vc_340 hO hE hc hI
  · exact vc_343 hO hE hc hI
  · exact vc_411 hO hE hc hI
  · exact vc_443 hO hE hc hI
  · exact vc_481 hO hE hc hI
  · exact vc_510 hO hE hc hI
  · exact vc_532 hO hE hc hI
  · exact vc_572 hO hE hc hI
  · exact vc_594 hO hE hc hI
  · exact vc_648 hO hE hc hI
  · exact vc_657 hO hE hc hI
  · exact vc_696 hO hE hc hI
  · exact vc_751 hO hE hc hI
  · exact vc_794 hO hE hc hI
  · exact vc_821 hO hE hc hI
  · exact vc_833 hO hE hc hI
  · exact vc_880 hO hE hc hI
  · exact vc_960 hO hE hc hI
  · exact vc_1024 hO hE hc hI
  · exact vc_1105 hO hE hc hI
  · exact vc_1200 hO hE hc hI
  · exact vc_1261 hO hE hc hI
  · exact vc_1288 hO hE hc hI
  · exact vc_1400 hO hE hc hI
  · exact vc_1420 hO hE hc hI
  · exact vc_1432 hO hE hc hI
  · exact vc_1472 hO hE hc hI
  · exact vc_1504 hO hE hc hI
  · exact vc_1537 (f := f) hO hE hc hI

/-! ## The stack at the `ret` -/

/-- A read apart from an 8-byte store. -/
theorem rdo {V : Addr → Byte} {a x : Addr} {r : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) : rdq(Vst V a (toBytesLE r 8), x) = rdq(V, x) := by
  rw [FV7z.Tun.rd_Vst V a (toBytesLE r 8) x 8 (by rw [toBytesLE_length]; exact ha) hx
    (by rw [toBytesLE_length]; exact h)]

/-- The read of an 8-byte store. -/
theorem rds {V : Addr → Byte} {a x : Addr} {r : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) (e : x = a) :
    rdq(Vst V a (toBytesLE r 8), x) = r := by
  subst e
  rw [FV7z.Tun.rd_Vst_self V x (toBytesLE r 8) (toBytesLE_length _ _) ha, ofBytesLE_toBytesLE (n := 8) rfl]

/-- `x - 8` as a number, when it does not wrap. -/
theorem s8 (x : BitVec 64) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega

/-- `x + 8` as a number, when it does not wrap. -/
theorem a8 (x : BitVec 64) (h : x.toNat + 8 < 2 ^ 64) : (x + 8).toNat = x.toNat + 8 := by bv_omega

/-- The frame's addresses as numbers, one `bv_omega` step at a time (`bv_omega` over the nested `- 8`s and `+ 8`s in
the big contexts of `rd1` and `tdm_ok` ran ~55 min and out of memory, kt2309). -/
theorem fr (hs : 40 ≤ K.g0.rsp.toNat) (hs8 : K.g0.rsp.toNat + 8 ≤ 2 ^ 64) :
    (K.g0.rsp - 8).toNat = K.g0.rsp.toNat - 8 ∧ (K.g0.rsp - 8 - 8).toNat = K.g0.rsp.toNat - 16 ∧
    (K.g0.rsp - 8 - 8 - 8).toNat = K.g0.rsp.toNat - 24 ∧ (K.g0.rsp - 8 - 8 - 8 - 8).toNat = K.g0.rsp.toNat - 32 ∧
    (K.g0.rsp - 8 - 8 - 8 - 8 - 8).toNat = K.g0.rsp.toNat - 40 ∧ K.sp.toNat = K.g0.rsp.toNat - 40 ∧
    (K.sp + 8).toNat = K.g0.rsp.toNat - 32 ∧ (K.sp + 8 + 8).toNat = K.g0.rsp.toNat - 24 ∧
    (K.sp + 8 + 8 + 8).toNat = K.g0.rsp.toNat - 16 ∧ (K.sp + 8 + 8 + 8 + 8).toNat = K.g0.rsp.toNat - 8 ∧
    (K.sp + 8 + 8 + 8 + 8 + 8).toNat = K.g0.rsp.toNat := by
  have h1 := s8 K.g0.rsp (by omega)
  have h2 := s8 (K.g0.rsp - 8) (by omega)
  have h3 := s8 (K.g0.rsp - 8 - 8) (by omega)
  have h4 := s8 (K.g0.rsp - 8 - 8 - 8) (by omega)
  have h5 := s8 (K.g0.rsp - 8 - 8 - 8 - 8) (by omega)
  have h0 : K.sp.toNat = K.g0.rsp.toNat - 40 := by
    show (K.g0.rsp - 8 - 8 - 8 - 8 - 8).toNat = _
    omega
  have a1 := a8 K.sp (by omega)
  have a2 := a8 (K.sp + 8) (by omega)
  have a3 := a8 (K.sp + 8 + 8) (by omega)
  have a4 := a8 (K.sp + 8 + 8 + 8) (by omega)
  have a5 := a8 (K.sp + 8 + 8 + 8 + 8) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The address arithmetic of the frame, with `fr`'s facts in the context: `omega` over the `toNat` atoms. -/
local macro "tbo" : tactic => `(tactic| ((try apply BitVec.eq_of_toNat_eq) <;> omega))

set_option maxHeartbeats 400000 in
/-- The five saved registers and the return address under `V1`. -/
theorem rd1 (hO : Ok K) (hs : 40 ≤ K.g0.rsp.toNat) (hs8 : K.g0.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(K.V1, K.sp) = K.g0.rbx ∧ rdq(K.V1, K.sp + 8) = K.g0.rbp ∧ rdq(K.V1, K.sp + 8 + 8) = K.g0.r12 ∧
    rdq(K.V1, K.sp + 8 + 8 + 8) = K.g0.r13 ∧ rdq(K.V1, K.sp + 8 + 8 + 8 + 8) = K.g0.r14 ∧
    rdq(K.V1, K.g0.rsp) = rdq(K.V0, K.g0.rsp) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := fr (K := K) hs hs8
  rw [hO.eV1]
  refine ⟨rds ?_ ?_, (rdo ?_ ?_ ?_).trans (rds ?_ ?_), (rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans (rds ?_ ?_)),
    (rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans (rds ?_ ?_))),
    (rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans (rds ?_ ?_)))),
    (rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans ((rdo ?_ ?_ ?_).trans (rdo ?_ ?_ ?_))))⟩
  all_goals tbo

/-- Reads in the frame or of the return address, with `*bufOut` stored or not. -/
theorem rdv {V' : Addr → Byte} {x : Addr} (hv : V' = K.V1 ∨ ∃ s : BitVec 64, V' = Vst K.V1 K.g0.rdx (toBytesLE s 8))
    (hr : K.g0.rdx.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : K.g0.rdx.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ K.g0.rdx.toNat) : rdq(V', x) = rdq(K.V1, x) := by
  rcases hv with rfl | ⟨s, rfl⟩
  · rfl
  · exact rdo hr hx h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

set_option maxHeartbeats 400000 in
/-- `LzmaDec_TryDummy (p, buf, bufOut)` from its entry, with `Ok K` and `Env K F Wl` of the names `K` (the registers
`K.g0` and bytes `K.V0` at the entry): at the return address, the return address popped, `rbx`, `rbp`, `r12`–`r15`
and `rdx` as they were, `r9 = *bufOut`, `rax` the result (at most 3) and `rsi` between `buf` and `*bufOut`; the bytes
those after the five pushes (`V1`), with `*bufOut = rsi` stored when `rax` is not 0. -/
theorem tdm_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tdm_at tdm) (hO : Ok K) (hE : Env K F Wl)
    (hKw : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem K.V0) (hrip : X.cpu.rip = tdm_at) (hg : X.cpu.gpr = K.g0)
    (hs : 40 ≤ K.g0.rsp.toNat) (hs8 : K.g0.rsp.toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add K.g0.rsp i))
    (hr : K.g0.rdx.toNat + 8 ≤ 2 ^ 64)
    (hsep : K.g0.rdx.toNat + 8 ≤ K.g0.rsp.toNat - 40 ∨ K.g0.rsp.toNat + 8 ≤ K.g0.rdx.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(K.V0, K.g0.rsp) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ →
      (∃ a cc si di x8 x10 x11 : BitVec 64, Z.cpu.gpr =
        ({ K.g0 with rax := a, rcx := cc, rsi := si, rdi := di, r8 := x8, r9 := K.B, r10 := x10, r11 := x11 } :
          Gprs).set 4 (K.g0.rsp + 8) ∧
        a.toNat ≤ 3 ∧ K.g0.rsi.toNat ≤ si.toNat ∧ si.toNat ≤ K.B.toNat ∧
        ((a.toNat = 0 ∧ V' = K.V1) ∨ (1 ≤ a.toNat ∧ V' = Vst K.V1 K.g0.rdx (toBytesLE si 8)))) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv K ℓ m g V') (fun j g _ V' => Fz K j g V')
    (fun ℓ m g f V' h => vcAll hO hE ℓ m g f V' h) ?_ 6300 0 hKw hA (by rw [addr_add_zero]; exact hrip)
    (Or.inl ⟨rfl, rfl, hg, rfl⟩)
  rintro j G fl V' ⟨hj, hF⟩ Y t' hKY hAY hrY hgY -
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := G
  obtain ⟨hsp, hdx, hr9, hr15, hbx, hbp, h12, h13, h14, hs1, hs2, hv⟩ := hF
  dsimp only at hsp hdx hr9 hr15 hbx hbp h12 h13 h14 hs1 hs2 hv
  have hv' : V' = K.V1 ∨ ∃ s : BitVec 64, V' = Vst K.V1 K.g0.rdx (toBytesLE s 8) := by
    rcases hv with ⟨_, h⟩ | ⟨_, _, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, h⟩
  have hax : rax.toNat ≤ 3 := by rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega
  have hvv : (rax.toNat = 0 ∧ V' = K.V1) ∨ (1 ≤ rax.toNat ∧ V' = Vst K.V1 K.g0.rdx (toBytesLE rsi 8)) := by
    rcases hv with h | ⟨h1, _, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := rd1 hO hs hs8
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := fr (K := K) hs hs8
  rw [rdv (x := K.sp) hv' hr (by tbo) (by tbo), e0] at hbx
  rw [rdv (x := K.sp + 8) hv' hr (by tbo) (by tbo), e1] at hbp
  rw [rdv (x := K.sp + 8 + 8) hv' hr (by tbo) (by tbo), e2] at h12
  rw [rdv (x := K.sp + 8 + 8 + 8) hv' hr (by tbo) (by tbo), e3] at h13
  rw [rdv (x := K.sp + 8 + 8 + 8 + 8) hv' hr (by tbo) (by tbo), e4] at h14
  have hra' : rdq(V', K.g0.rsp) = e₂.add j₂ := by rw [rdv (x := K.g0.rsp) hv' hr (by tbo) (by tbo), e5]; exact hra
  have hsp' : rsp = K.g0.rsp := by rw [hsp]; tbo
  subst hsp' hdx hr9 hr15 hbx hbp h12 h13 h14
  have hl' : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by rw [hgY]; exact hl
  have hra'' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by rw [hgY]; exact hra'
  have kk : ∀ (Z : State) (t₂ : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ ∧ Z.cpu.gpr = Y.cpu.gpr.set 4 (Y.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t₂ := by
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k V' Z t₂ hKZ hAZ hrZ ⟨rax, rcx, rsi, rdi, r8, r10, r11, by rw [hgZ, hgY] <;> rfl, hax, hs1, hs2, hvv⟩
  rcases hj with rfl | rfl
  · exact c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_354 _) hl' hin₂ h₂ hra'' kk
  · exact c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_765 _) hl' hin₂ h₂ hra'' kk

end FV7z.Tdm
