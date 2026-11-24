import FV7z.Lemmas.CallR
import FV7z.Lemmas.FnJt
/-!
# `call r64` (PLAN.md G3, startup)

`__libc_start_main` calls `init` (`__libc_csu_init`) through `rbp` (`call *%rbp` at `0x61346c`) and `main` through
`rax` (`call *%rax` at `0x6134ce`). `call_r` is the instruction on Zellic's model, `Seg.s_callr` the step of a run:
the target is the register's value, the return address is pushed.
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `call r64`: the return address pushed, then to the register's value. -/
theorem call_r {r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .call 64 [gr 64 r] len))
    (hsh : s.thread.shstk = none) (hcan : Addr.canonical prof.feat.la57 (s.cpu.gpr.get (regOf r)) = true)
    (hw : Writable prof s (s.cpu.gpr.rsp - 8) 8) :
    (instruction prof s).runStream o t = (.running (upd (st s (s.cpu.gpr.rsp - 8) (toBytesLE (s.cpu.rip.add len) 8))
      (s.cpu.gpr.get (regOf r)) (s.cpu.gpr.set 4 (s.cpu.gpr.rsp - 8)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  have hg : (advance s len).cpu.gpr = s.cpu.gpr := rfl
  simp only [exec, Sem.call, push64, mk, gr, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readRip, Prog.readReg,
    Prog.write, Prog.writeReg, Prog.writeRip, pure, show (advance s len).thread.shstk = none from hsh,
    Bool.false_eq_true, ↓reduceIte, done, readOp, hg, BitVec.setWidth_eq, hcan, Bool.not_true]
  rw [checkAccess_ok (s := advance s len) hac hw]
  rfl

end

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `call r64` to a segment's first byte, pushing into bytes the run may store into. -/
theorem s_callr (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [gr 64 r] len))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : X.cpu.gpr.get (regOf r) = e₂)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8))
      fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hra : (X.withMem M).cpu.rip.add len = e'.add (j + len) := rip_add hrip M len
    have hca := ((c.codeAt hK' hin₂) 0 h₂).1
    rw [addr_add_zero] at hca
    have hT : (X.withMem M).cpu.gpr.get (regOf r) = e₂ := htgt
    obtain ⟨hw, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (e'.add (j + len)) 8) (a := X.cpu.gpr.rsp - 8) (by simpa using hst)
    rw [toBytesLE_length] at hw
    have hr := call_r (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd)
      (by rw [hK'.thread]; exact c.ready.plain.2.2.1) (by rw [hT]; exact hca) hw
    rw [hra, hT] at hr
    exact ⟨_, _, hr, hKs.upd rfl rfl rfl, hAs, rfl, rfl⟩) k'

end FV7z.Fn.Seg
