import FV7z.Csu.Pre
import FV7z.Fdm.Holds
/-!
# `frame_dummy` as `__libc_csu_init` calls it (PLAN.md G3, startup)

The first entry of `.init_array` of `7zzs` (`frame_dummy` at `0x41d440`, the function 2 of `Csu.csu_ok`), by
`Fdm.fdm_ok`: it stores below the frame of `__libc_csu_init`, into its `object` and into libgcc's `object_mutex`,
`any_objects_registered` and `unseen_objects` only.

- `fd_runs`: `Runs` for the function 2, for any invariant whose `I 2` has the first word of `.eh_frame` not 0,
  nothing registered, the mutex free and of the plain kind, no elision, and gives `I 3` what `Rfi.Dat` says of the
  memory after.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Csu

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {I : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}

/-- `frame_dummy` is a function as `csu_ok` asks: it keeps the frame of `__libc_csu_init` and the arrays. -/
theorem fd_runs {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hC : Env F Wl L sp tg)
    (hE : Fdm.Env F Wl L fb (sp - 64#64)) (h2 : tg 2 = Fdm.fdm_at)
    (hU : ∀ V, I 2 V → rdd(V, 7388000#64) ≠ 0 ∧ rdd(V, 8008608#64 + 16#64) = 0 ∧ rdd(V, 7991628#64) = 0 ∧
      rdd(V, 8008608#64) = 0 ∧ rdd(V, 8008608#64 + 8#64) = 0 ∧ rdd(V, 8008648#64) = 0)
    (h23 : ∀ V V', I 2 V →
      Rfi.Dat (sp.toNat - 64 - 72) (sp.toNat - 64) (7947808#64) (7388000#64) V V' → I 3 V') :
    Runs prof F Wl L s₀ o gev gP gE I sp a₀ a₁ a₂ 2 (tg 2) := by
  intro X t V j₂ hK hA hI hr hsp _ hj hra k
  obtain ⟨hb, hkd, hfe, hlk, how, hany⟩ := hU V hI
  have hs0 := hE.s0
  have n := sp_n hC.s0
  rw [n] at hs0
  refine Fdm.fdm_ok c hfs (hsp ▸ hE) hK hA (hr.trans h2) hb hkd hfe hlk how hany hC.code hj
    (by rw [hsp]; exact hra) ?_
  intro V' Z t' hKZ hAZ hD hrZ hbk
  rw [hsp, n] at hD
  have nw : ∀ {a : Addr}, 7829400 ≤ a.toNat → (a.toNat < 7830224 ∨ 8008672 ≤ a.toNat) →
      ¬ Rfi.Wr (7947808#64) a.toNat := fun {a} h1 h2 => by
    have e : (7947808#64).toNat = 7947808 := rfl
    unfold Rfi.Wr
    omega
  exact k Z t' V' hKZ hAZ (h23 V V' hI hD) (fun a ha => hD.out a (by omega) (nw (by omega) (by omega)))
    (fun a ha => hD.out a (by omega) (nw (by omega) (by omega))) hrZ hbk

end FV7z.Csu
