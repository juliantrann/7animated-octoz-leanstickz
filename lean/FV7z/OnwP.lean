import FV7z.Onw
/-!
# `operator new` with its post as one proposition (PLAN.md §M, M1)

- `PnW`: the post of `operator new (n)` from the bytes `V` at its entry, as `Onw.onw_hpWT` gives it: the block `rax`
  (16 above the old top `main_arena.top` or more, above the TLS block's words, `n` bytes below `hi`, in the
  footprint), `Mal.Hp … m` for the bytes outside it, and the bytes outside the heap's words and the block, from `lo`
  up, as at the entry.
- `onw_pnW`: `onw_hpWT` with `rdi.toNat = n > 0` and the post `PnW` (for the `…okH` wrappers of `FV7z/Ura`,
  `FV7z/Ur2`, `FV7z/Usf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Onw

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The post of `operator new (n)` from the bytes `V` at its entry: see the module doc. -/
abbrev PnW (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (V : Addr → Byte) (n lo : Nat) (Z : State)
    (V₁ : Addr → Byte) : Prop :=
  rdq(V, 7940768#64).toNat + 16 ≤ Z.cpu.gpr.rax.toNat ∧ fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat ∧
    Z.cpu.gpr.rax.toNat + n ≤ hi ∧
    (∀ a : Addr, Z.cpu.gpr.rax.toNat ≤ a.toNat → a.toNat < Z.cpu.gpr.rax.toNat + n → Foot Wl a ∧ Foot F.data a) ∧
    (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
      (a.toNat < Z.cpu.gpr.rax.toNat ∨ Z.cpu.gpr.rax.toNat + n ≤ a.toNat) → W a = V₁ a) →
      Mal.Hp F Wl fb hi m W) ∧
    (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨ lo ≤ a.toNat) →
      V₁ a = V a)

/-- `onw_hpWT` with the post `PnW`: see the module doc. -/
theorem onw_pnW {fb : Addr} {hi m B : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L onw_at onw) (hinM : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hrip : Y.cpu.rip = onw_at.add 64) (hH : Mal.Hp F Wl fb hi (m + B) V) {n : Nat}
    (hn : Y.cpu.gpr.rdi.toNat = n) (hn0 : 0 < n) (hB : Mal.MalB Y.cpu.gpr.rdi B)
    (hhi : hi + 232 ≤ Y.cpu.gpr.rsp.toNat) (hR : Y.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < Y.cpu.gpr.rsp.toNat + 8 → Foot Wl a)
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, Y.cpu.gpr.rsp) = e'.add j)
    (k : ∀ (Z : State) (V₂ : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ →
      Z.cpu.rip = e'.add j → Z.cpu.gpr.rsp = Y.cpu.gpr.rsp + 8 → Z.cpu.gpr.rbx = Y.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = Y.cpu.gpr.rbp → Z.cpu.gpr.r12 = Y.cpu.gpr.r12 → Z.cpu.gpr.r13 = Y.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 →
      PnW F Wl fb hi m V n Y.cpu.gpr.rsp.toNat Z V₂ → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine onw_hpWT (B := B) (m := m) c hfs hin hinM hinI hK hA hrip hH
    (fun h => by rw [h] at hn; simp at hn; omega) hB hhi hR hsw hin₂ hj hra ?_
  intro Z t' V₂ p hKZ hAZ hrZ zsp zax zbx zbp z12 z13 z14 z15 _ hpf hpe hfoot hV hPm hT
  subst zax
  rw [hn] at hpe hfoot hPm
  exact k Z V₂ t' hKZ hAZ hrZ zsp zbx zbp z12 z13 z14 z15 ⟨hT, hpf, hpe, hfoot, hPm, fun a h =>
    hV a (h.elim .inl fun h => h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr ⟨by omega, .inr h⟩))⟩

end FV7z.Onw
