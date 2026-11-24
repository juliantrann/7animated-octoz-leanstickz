import FV7z.Ctor.BlkRet
/-!
# Loops whose invariant starts from the frame (PLAN.md §M, constructors)

`cfg_runs` asks the invariant to hold at the entry for any registers and bytes. A constructor that pushes a register
(the stack below `__libc_csu_init`'s frame) or reads a table of the image (its bytes as the invariant `J` says) needs
more at the entry: `rsp` the frame's `sp - 64`, and `J m` of the bytes.

- `cfg_runsJ`: `cfg_runs` with the entry's invariant from `rsp = sp - 64` and `J m V`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `cfg_runs`, the invariant at the entry from `rsp = sp - 64` and `J m` of the bytes. -/
theorem cfg_runsJ {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j jr : Nat} {W : Nat → Wpt} {a e : Addr} {code : List Byte} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L e code) (htg : a = e.add j) (hW : ∀ ℓ, Sp prof code e ℓ (W ℓ))
    (hd : Dec prof.feat code jr (FV7z.mk .ret 64 [] 1)) (hjr : jr < code.length)
    (R : (Addr → Byte) → (Addr → Byte) → Prop)
    (Inv : Gprs → (Addr → Byte) → Nat → Nat → Gprs → Rflags → (Addr → Byte) → Prop)
    (h0 : ∀ g f V, g.rsp = sp - 64#64 → J m V → ∃ n, Inv g V j n g f V)
    (vc : ∀ g₀ V₀ ℓ n g f V, Inv g₀ V₀ ℓ n g f V → W ℓ F Wl (fun j' g' f' V' =>
      (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = jr ∧ Kp g₀ g' ∧ R V₀ V')) g f V)
    (hR : ∀ V V', R V V' → ∀ a : Addr, (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → V' a = V a)
    (hJ : ∀ V V', J m V → R V V' → J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m a := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  obtain ⟨n₀, h₀⟩ := h0 X.cpu.gpr X.cpu.rflags V hsp hI
  refine c.cfg hin hW (Inv X.cpu.gpr V) (fun j' g' _ V' => j' = jr ∧ Kp X.cpu.gpr g' ∧ R V V')
    (vc X.cpu.gpr V) ?_ n₀ j hK hA (hr.trans htg) h₀
  rintro j' g fl V' ⟨rfl, hKp, hRV⟩ Y t₁ hKY hAY hrY rfl -
  exact ret_tail c hC hin hd hjr hsp hj₂ hra hKY hAY hrY hKp (hJ V V' hI hRV) (hR V V' hRV) k

end FV7z.Ctor
