import FV7z.Lemmas.SpCallK
import FV7z.Lemmas.Lock2
/-!
# Calls of a function in the middle of a code segment (PLAN.md M, ctor 103)

`SpAt.callK` for a callee whose entry is the `tgt`-th byte of its code (`Seg.s_call_x`): glibc's `handle_intel` calls
`intel_check_word`, which lies in the same code (`Hca`), at its 464th byte.
-/
namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {e' : Addr} {code : List Byte}

/-- `call rel32` of a function that does its own `ret` and starts at the `tgt`-th byte of its code. -/
theorem SpAt.callKx (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j rel len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : tgt < code₂.length)
    {e₃ : Addr} (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂.add tgt) (he : e₂.add tgt = e₃)
    {T : Gprs → (Addr → Byte) → Prop} {R : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop}
    (hT : FnK prof F Wl L s₀ o e₃ T R) :
    SpAt prof F Wl L s₀ o e' j (CallK Wl e' (j + len) T R) := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip ⟨hst, hov, hTX, hR⟩ k
  refine c.s_call_x hK hA hin hj hrip hd hin₂ h₂ htgt hst ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine hT.run hKY hAY (hrY.trans he) (hgY ▸ hTX) ?_
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

end FV7z.Fn
