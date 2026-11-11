import FV7z.Lemmas.Rmw
import FV7z.Lemmas.FnJt
/-!
# Locked read-modify-writes (PLAN.md G3, startup)

glibc's low-level lock (`lll_lock`, `lll_unlock`) on a word of `.bss`, one instruction of the model each
(`Prog.lockedRmw`); a locked access is atomic unless it crosses a line of the cache (64 bytes), which a word aligned
to 4 does not.

- `lockCmpxchg32`, `lock_cmpxchg_rip32`, `Seg.s_lock_cmpxchg_rip32`: `lock cmpxchg dword [rip + d], r32` where the
  word is `eax`: it becomes the register, `ZF` is set.
- `xchg_rip32`, `Seg.s_xchg_rip32`: `xchg dword [rip + d], r32`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `lock cmpxchg dword [rip + d], r32` as the decoder gives it. -/
abbrev lockCmpxchg32 (d r len : Nat) : Inst :=
  { mn := .cmpxchg, opsz := 32, len, rep := none, lock := true, mask := none, zero := false, fop := 0,
    ops := [.mem (mrip d 32), .reg ⟨32, r, false⟩] }

/-- `lock cmpxchg dword [rip + d], r32`, the word being `eax`. -/
theorem lock_cmpxchg_rip32 {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (lockCmpxchg32 d r len))
    (hsl : (eaR s len d).toNat % 64 + 4 ≤ 64) (hwr : Writable prof s (eaR s len d) 4)
    (hold : ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) = rv s 32 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d) (toBytesLE (rv s 32 r) 4)) len s.cpu.gpr fl) none, t') ∧
      fl.zf = true ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  have hns : ¬ ((eaR s len d).toNat % 64 + 32 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3, ?h4⟩
  case h =>
    simp only [exec, execLocked, Sem.cmpxchg, accOf, subOp, mrip, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.readReg, Prog.run, writeOp,
      Prog.readFlags, Prog.writeFlags, Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaR_adv]
    have hold' : ofBytesLE 32 (readBytes (advance s len).proc.mm.mem (eaR s len d) 4) =
        BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 0)) := hold
    simp only [hns, ↓reduceIte, Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, hold']
    rfl
  case h1 =>
    simp
  all_goals rfl

/-- `xchg dword [rip + d], r32`: locked whether or not it has the prefix. -/
theorem xchg_rip32 {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xchg 32 [.mem (mrip d 32), gr 32 r] len))
    (hsl : (eaR s len d).toNat % 64 + 4 ≤ 64) (hwr : Writable prof s (eaR s len d) 4) :
    ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d) (toBytesLE (rv s 32 r) 4)) len
          (s.cpu.gpr.set (regOf r) ((ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4)).setWidth 64)) (rf0 s))
          none, t') := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  have hns : ¬ ((eaR s len d).toNat % 64 + 32 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?t', instruction_next htf hdec ?h⟩
  case h =>
    simp only [exec, Sem.xchg, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.readReg, Prog.run, writeOp,
      Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaR_adv]
    simp only [hns, ↓reduceIte, Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc]
    rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `lock cmpxchg dword [rip + d], r32` on a word the run may store into that is `eax`: the lock is taken. -/
theorem s_lock_cmpxchg_rip32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (lockCmpxchg32 d r len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hsl : g.toNat % 64 + 4 ≤ 64)
    (hst : ∀ i < 4, Foot Wl (g.add i)) (hold : ofBytesLE 32 ((byteAddrs g 4).map V) = rv X 32 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.rflags.zf = true) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, hz, h1, h2, h3⟩ := lock_cmpxchg_rip32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) (by rw [he]; exact hsl) hwr (by rw [he, hv]; exact hold)
    rw [he] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl, hz⟩) k'

/-- `xchg dword [rip + d], r32` on a word the run may store into. -/
theorem s_xchg_rip32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .xchg 32 [.mem (mrip d 32), gr 32 r] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hsl : g.toNat % 64 + 4 ≤ 64)
    (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧
        Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 32 ((byteAddrs g 4).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨t', hr⟩ := xchg_rip32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) (by rw [he]; exact hsl) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
