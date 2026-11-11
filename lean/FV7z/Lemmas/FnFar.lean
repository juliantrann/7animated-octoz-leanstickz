import FV7z.Lemmas.FnSib
/-!
# Branches to another segment, a branch known not taken, `mov qword [rip + d], imm` (PLAN.md G2)

glibc's `init_cpu_features` is laid out in pieces: the part for Intel's kind (`0x613592`) jumps back into the part
every vendor runs (`0x613232`), whose `je` to it is a branch to another segment (`Seg.s_jcc_x`, `Seg.s_jmp_x`); the
`je` after `arch_prctl` is never taken, `rax` being `-EINVAL` (`Seg.s_jcc_f`). Beside them: `movq $imm, [rip + d]`
(`Seg.s_mov_rip_i64`).
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `mov qword [rip + d], imm`. -/
theorem mov_rip_i64 {d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [.mem (mrip d 64), .imm 64 imm] len))
    (hwr : Writable prof s (eaR s len d) 8) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaR s len d) (toBytesLE (BitVec.ofNat 64 imm) 8)) len
      s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readRip, Prog.write, Prog.run, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- `jcc` known not taken. -/
theorem s_jcc_f (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {rel len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len)) (hcc : X.cpu.rflags.cond cc = false)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf
    (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `jcc` to the `tgt`-th byte of a segment, maybe another. -/
theorem s_jcc_x (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {rel len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂.add tgt)
    (taken : X.cpu.rflags.cond cc = true →
      ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add tgt ∧ Y.cpu.gpr = X.cpu.gpr)
    (fall : X.cpu.rflags.cond cc = false →
      ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.s_jcc_f hK hA hin hj hrip hd hcc (fall hcc)
  · refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) (taken hcc)
    have hca := ((c.codeAt hK' hin₂) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e₂.add tgt := by
      rw [rip_add hrip M len]; exact htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hin hrip hd) hcc (by rw [ha]; exact hca),
      hK'.upd rfl rfl rfl, hA', ha, rfl⟩

/-- `jmp` to the `tgt`-th byte of a segment, maybe another. -/
theorem s_jmp_x (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {rel len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂.add tgt)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add tgt ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) k'
  have hca := ((c.codeAt hK' hin₂) tgt ht).1
  have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e₂.add tgt := by
    rw [rip_add hrip M len]; exact htgt
  exact ⟨_, _, jmp_rel (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl⟩

/-- `mov qword [rip + d], imm`, into bytes the run may store into. -/
theorem s_mov_rip_i64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 64 [.mem (mrip d 64), .imm 64 imm] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 8, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (BitVec.ofNat 64 imm) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (BitVec.ofNat 64 imm) 8) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    have hr := mov_rip_i64 (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr
    rw [he] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

end Seg

end FV7z.Fn
