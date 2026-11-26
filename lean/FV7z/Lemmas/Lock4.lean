import FV7z.Lemmas.Lock
/-!
# Read-modify-writes of a counter at a fixed address (PLAN.md §M, M1)

`munmap_chunk`'s statistics (`mp_.n_mmaps`, `mp_.mmapped_mem`, updated by `atomic_decrement` and
`atomic_add`) and `systrim`'s `main_arena.system_mem -= released`.

- `lockDec32`, `lock_dec_rip32`, `Seg.s_lock_dec_rip32`: `lock dec dword [rip + d]`.
- `lockAdd64r`, `lock_add_rip64r`, `Seg.s_lock_add_rip64r`: `lock add qword [rip + d], r64`.
- `sub_rip64r`, `Seg.s_sub_rip64r`: `sub qword [rip + d], r64`.

As in `Lemmas/Lock.lean`, a locked word within one cache line (64 bytes).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `lock dec dword [rip + d]` as the decoder gives it. -/
abbrev lockDec32 (d len : Nat) : Inst :=
  { mn := .dec, opsz := 32, len, rep := none, lock := true, mask := none, zero := false, fop := 0,
    ops := [.mem (mrip d 32)] }

/-- `lock add qword [rip + d], r64` as the decoder gives it. -/
abbrev lockAdd64r (d r len : Nat) : Inst :=
  { mn := .add, opsz := 64, len, rep := none, lock := true, mask := none, zero := false, fop := 0,
    ops := [.mem (mrip d 64), .reg ⟨64, r, false⟩] }

/-- `lock dec dword [rip + d]`. -/
theorem lock_dec_rip32 {d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (lockDec32 d len))
    (hsl : (eaR s len d).toNat % 64 + 4 ≤ 64) (hwr : Writable prof s (eaR s len d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) - 1#32) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  have hns : ¬ ((eaR s len d).toNat % 64 + 32 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, execLocked, Sem.lockDec, subOp, mrip, bind, Prog.bind, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.run, Prog.readFlags, Prog.writeFlags, Prog.lockedRmw,
      BitVec.mul_one, done]
    rw [eaR_adv]
    simp only [hns, ↓reduceIte, Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc]
    rfl
  all_goals rfl

/-- `lock add qword [rip + d], r64`. -/
theorem lock_add_rip64r {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (lockAdd64r d r len))
    (hsl : (eaR s len d).toNat % 64 + 8 ≤ 64) (hwr : Writable prof s (eaR s len d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8) + rv s 64 r) 8)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 8) hac hwr
  have hns : ¬ ((eaR s len d).toNat % 64 + 64 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, execLocked, Sem.lockAdd, lockedAlu, addOp, mrip, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.readReg, Prog.run, Prog.readFlags, Prog.writeFlags,
      Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaR_adv]
    simp only [hns, ↓reduceIte, Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc]
    rfl
  all_goals rfl

/-- `sub qword [rip + d], r64`. -/
theorem sub_rip64r {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 64 [.mem (mrip d 64), gr 64 r] len))
    (hwr : Writable prof s (eaR s len d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8) - rv s 64 r) 8)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 8) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp,
      Prog.readFlags, Prog.writeFlags, BitVec.mul_one, done]
    rw [eaR_adv]
    have z : BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 := rfl
    simp only [Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `lock dec dword [rip + d]` on a word the run may store into. -/
theorem s_lock_dec_rip32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d len : Nat}
    (hd : Dec prof.feat code j (lockDec32 d len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hsl : g.toNat % 64 + 4 ≤ 64)
    (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) - 1#32) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) - 1#32) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := lock_dec_rip32 (s := X.withMem M) (o := o) (t := t + 1) htf
      hac (c.dec hK' hin hrip hd) (by rw [he]; exact hsl) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

/-- `lock add qword [rip + d], r64` on a quadword the run may store into. -/
theorem s_lock_add_rip64r (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (lockAdd64r d r len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hsl : g.toNat % 64 + 8 ≤ 64)
    (hst : ∀ i < 8, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) + rv X 64 r) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) + rv X 64 r) 8) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := lock_add_rip64r (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) (by rw [he]; exact hsl) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

/-- `sub qword [rip + d], r64` on a quadword the run may store into. -/
theorem s_sub_rip64r (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 64 [.mem (mrip d 64), gr 64 r] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 8, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) - rv X 64 r) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) - rv X 64 r) 8) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_rip64r (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
