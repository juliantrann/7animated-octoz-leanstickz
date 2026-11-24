import FV7z.Lemmas.SpCall
import FV7z.Lemmas.FnSteps
/-!
# Calls of functions with several `ret`s, `cpuid` at a cut point (PLAN.md M, ctor 103)

`FnAt` ends at one `ret`. glibc's `handle_amd` has four, `handle_intel` and `intel_check_word` several; here the
callee does its own `ret`:

- `FnK … e₂ T R`: the function at `e₂`, entered with `T` of the registers and the footprint's bytes (the return
  address at `rsp`), goes on to the return address it found there with `R` of the registers and bytes at the entry and
  at the return;
- `SpAt.callK`: a `call rel32` of such a function, from the `call` to the instruction after it (the return address's
  slot is the run's to store into and does not wrap);
- `SpAt.cpuid`: `cpuid` at a cut point, for every CPU of the profile (`Seg.s_cpuid`).
-/
namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

/-- A function inside a run, from its entry through its own `ret` to the return address. -/
structure FnK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (e₂ : Addr) (T : Gprs → (Addr → Byte) → Prop) (R : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop) : Prop where
  run : ∀ {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e₂ →
    T X.cpu.gpr V →
    (∀ (Y : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = ofBytesLE 64 (List.map V (byteAddrs X.cpu.gpr.rsp 8)) → R X.cpu.gpr V Y.cpu.gpr V' →
      GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {e' : Addr} {code : List Byte}

/-- What a `call` at the `j`-th byte (`len` bytes) of a function with `T` and `R` needs: the return address's slot
the run's to store into, not wrapping; `T` with the return address there; `Q` after the `call` from `R`. -/
def CallK (Wl : List Rgn) (e' : Addr) (jn : Nat) (T : Gprs → (Addr → Byte) → Prop)
    (R : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  fun Q g _ V =>
    (∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) ∧ (g.rsp - 8).toNat + 8 ≤ 2 ^ 64 ∧
    T (g.set 4 (g.rsp - 8)) (Vst V (g.rsp - 8) (toBytesLE (e'.add jn) 8)) ∧
    ∀ g' V', R (g.set 4 (g.rsp - 8)) (Vst V (g.rsp - 8) (toBytesLE (e'.add jn) 8)) g' V' → ∀ fl, Q jn g' fl V'

/-- `call rel32` of a function that does its own `ret`, to the instruction after the `call`. -/
theorem SpAt.callK (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j rel len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂)
    {T : Gprs → (Addr → Byte) → Prop} {R : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop}
    (hT : FnK prof F Wl L s₀ o e₂ T R) :
    SpAt prof F Wl L s₀ o e' j (CallK Wl e' (j + len) T R) := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip ⟨hst, hov, hTX, hR⟩ k
  refine c.s_call hK hA hin hj hrip hd hin₂ h₂ htgt hst ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine hT.run hKY hAY hrY (hgY ▸ hTX) ?_
  intro Z t₂ V' hKZ hAZ hrZ hRZ
  have hra : ofBytesLE 64 (List.map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8))
      (byteAddrs Y.cpu.gpr.rsp 8)) = e'.add (j + len) := by
    rw [hgY]
    show ofBytesLE 64 (List.map _ (byteAddrs (X.cpu.gpr.rsp - 8) 8)) = _
    have e := Vst_self (toBytesLE (e'.add (j + len)) 8) V (X.cpu.gpr.rsp - 8) (by rw [toBytesLE_length]; exact hov)
    rw [toBytesLE_length] at e
    rw [e]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  exact k _ _ _ _ (hR _ _ (hgY ▸ hRZ) Z.cpu.rflags) Z t₂ hKZ hAZ (hrZ.trans hra) rfl rfl

/-- The registers after `cpuid` on CPU `cpu`. -/
abbrev cpuidG (prof : Profile) (cpu : Nat) (g : Gprs) : Gprs :=
  let r := prof.cpuid cpu (g.rax.setWidth 32) (g.rcx.setWidth 32)
  (((g.set 0 (r.eax.setWidth 64)).set 3 (r.ebx.setWidth 64)).set 1 (r.ecx.setWidth 64)).set 2 (r.edx.setWidth 64)

/-- `cpuid` at the `j`-th byte (`len` bytes), at a cut point: `Q` after it for every CPU of the profile. -/
theorem SpAt.cpuid (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk .cpuid 32 [] len)) :
    SpAt prof F Wl L s₀ o e' j fun Q g _ V =>
      ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q (j + len) (cpuidG prof cpu g) fl V := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip hW k
  refine c.s_cpuid hK hA hin hj hrip hd ?_
  rintro Y t' hKY hAY ⟨hrY, cpu, hc, hg⟩
  exact k _ _ _ _ (hW cpu hc Y.cpu.rflags) Y t' hKY hAY hrY hg rfl

end FV7z.Fn
