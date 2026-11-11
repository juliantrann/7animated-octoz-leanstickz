import FV7z.Lemmas.Rmw3
/-!
# `rdssp` without a shadow stack (PLAN.md G3, startup)

`__sigsetjmp` reads the shadow stack pointer with `rdsspq rax` after `xor eax, eax`. A thread of the model's
launch has no user shadow stack (`ThreadK.shstk = none`), and there the instruction changes nothing:
`rdssp`, `Seg.s_rdssp`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `rdsspq r` in a thread without a shadow stack: a no-op. -/
theorem rdssp {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .rdssp 64 [gr 64 r] len))
    (hsh : s.thread.shstk = none) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.rdssp, Bool.false_eq_true, ↓reduceIte, Prog.run, bind, Prog.bind, Prog.readThread,
    pure, show (advance s len).thread.shstk = none from hsh, done]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `rdsspq r`: the run's thread has no shadow stack, so nothing changes. -/
theorem s_rdssp (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .rdssp 64 [gr 64 r] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, rdssp (s := X.withMem M) htf (c.dec hK' hin hrip hd)
    (by rw [hK'.thread]; exact c.ready.plain.2.2.1), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
