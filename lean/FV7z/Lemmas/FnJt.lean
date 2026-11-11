import FV7z.Lemmas.FnFar
/-!
# A jump table, `or r8h, imm8`, `and dword [rip + d], imm32`, `lea r32, [b + d]` (PLAN.md G2)

glibc's `init_cpu_features` picks, for Intel's family 6, the model's case by a jump table: `lea ecx, [rax - 0x1a]`,
`cmp ecx, 0x45`, `ja`, `lea rsi, [rip + table]`, `movsxd rcx, dword [rsi + rcx·4]`, `add rcx, rsi`,
`notrack jmp rcx`. The cases set bits of `feature[1]` (`or ah, imm`) and clear `RTM` in `cpuid[7].ebx`
(`and dword [rip + d], imm`).
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `and dword [rip + d], imm32`: a read-modify-write. -/
theorem and_m32i_rip {d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 32 [.mem (mrip d 32), .imm 32 imm] len))
    (hwr : Writable prof s (eaR s len d) 4) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx (st s (eaR s len d)
      (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) &&& BitVec.ofNat 32 imm) 4)) len s.cpu.gpr
      ((rf0 s).arith (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) &&& BitVec.ofNat 32 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec (by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  have hp : ∀ {α : Type} (x : α), Req.runStream o (pure x : Req α) t = (x, t) := fun _ => rfl
  simp only [exec, Sem.and, alu, logicOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hwr, Req.runStream_bind]
  simp only [hp, Prog.run, Prog.readFlags, Prog.undefinedBit, Prog.write, Prog.writeFlags, Prog.bind,
    Prog.undefined, Nat.reduceDiv]
  simp only [Prog.bind, Prog.run, Req.runStream, bind, pure]
  simp only [Prog.run, eaR_adv, Bool.not_true, Bool.and_false, Bool.false_and, Nat.reduceDiv, hc]
  rfl)⟩

/-- `or r8h, imm8` (`ah`, …, of general register `r`). -/
theorem or_h8i {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 8 [gh r, .imm 8 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((s.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        ((((s.cpu.gpr.get (regOf r)) >>> 8).setWidth 8 ||| BitVec.ofNat 8 imm).setWidth 64 <<< 8)))
      ((rf0 s).arith (((s.cpu.gpr.get (regOf r)) >>> 8).setWidth 8 ||| BitVec.ofNat 8 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `lea r32, [b + d]`. -/
theorem lea32_bd {r b d len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .lea 32 [gr 32 r, .mem (mbd b d 0)] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) (((eaD s b d).setWidth 32).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.lea, mk, mbd, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg, Bool.false_eq_true,
    ↓reduceIte, writeOp, BitVec.mul_one]
  rw [eaD_adv]
  rfl

/-- `movsxd r64, dword [b + i·sc + d]`. -/
theorem movsxd_si {r i sc d len : Nat} {b : Option Nat} (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movsxd 64 [gr 64 r, .mem (msi b i sc d 32)] len))
    (hld : Readable prof s (eaS s b i sc d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ofBytesLE 32 (readBytes s.proc.mm.mem (eaS s b i sc d) 4)).signExtend 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  cases b with
  | none =>
    simp only [exec, Sem.movsxd, movSigned, mk, msi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, Nat.reduceDiv, writeOp]
    rw [show (0 : Addr) + (advance s len).cpu.gpr.get (regOf i) * BitVec.ofNat 64 sc + BitVec.ofNat 64 d =
      eaS s none i sc d from rfl, checkAccess_ok (s := advance s len) hac hld]
    rfl
  | some b =>
    simp only [exec, Sem.movsxd, movSigned, mk, msi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, Nat.reduceDiv, writeOp]
    rw [show (advance s len).cpu.gpr.get (regOf b) + (advance s len).cpu.gpr.get (regOf i) * BitVec.ofNat 64 sc +
      BitVec.ofNat 64 d = eaS s (some b) i sc d from rfl, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `jmp r64`. -/
theorem jmp_r {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .jmp 64 [gr 64 r] len))
    (hcan : Addr.canonical prof.feat.la57 (s.cpu.gpr.get (regOf r)) = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (s.cpu.gpr.get (regOf r)) s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jmp, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, advance, State.modCpu,
    jumpTo, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done, pure, BitVec.setWidth_eq]
  simp only [hcan, ↓reduceIte]
  rfl

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- `and dword [rip + d], imm32`, on a word the run may store into. -/
theorem s_and_rip_i32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .and 32 [.mem (mrip d 32), .imm 32 imm] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V g (toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) &&& BitVec.ofNat 32 imm) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) &&& BitVec.ofNat 32 imm) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨af, t', hr⟩ := and_m32i_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `or r8h, imm8`, with its value. -/
theorem s_or_h8i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .or 8 [gh r, .imm 8 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((X.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        (((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 ||| BitVec.ofNat 8 imm).setWidth 64 <<< 8))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := or_h8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `lea r32, [b + d]`. -/
theorem s_lea32_bd (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .lea 32 [gr 32 r, .mem (mbd b d 0)] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (((eaD X b d).setWidth 32).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, lea32_bd (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `movsxd r64, dword [b + i·sc + d]`, from the footprint's data. -/
theorem s_movsxd_si (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r i sc d len : Nat} {b : Option Nat}
    (hd : Dec prof.feat code j (FV7z.mk .movsxd 64 [gr 64 r, .mem (msi b i sc d 32)] len))
    (hl : ∀ k < 4, Foot F.data ((eaS X b i sc d).add k))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 32 ((byteAddrs (eaS X b i sc d) 4).map V)).signExtend 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaS (X.withMem M) b i sc d = eaS X b i sc d := by cases b <;> rfl
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) (n := 4) (a := eaS X b i sc d) hK' hA' hl
    have hr := movsxd_si (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd)
      (by rw [he]; exact hrd)
    rw [he, hv] at hr
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `add r64, r64'`, with its value. -/
theorem s_add_rr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 64 [gr 64 r, gr 64 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((addR (rv X 64 r) (rv X 64 q)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, add_rr (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `jmp r64` to the `tgt`-th byte of a segment. -/
theorem s_jmp_rx (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [gr 64 r] len))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : X.cpu.gpr.get (regOf r) = e₂.add tgt)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add tgt ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) k'
  have hca := ((c.codeAt hK' hin₂) tgt ht).1
  have ha : (X.withMem M).cpu.gpr.get (regOf r) = e₂.add tgt := htgt
  exact ⟨_, _, jmp_r (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl⟩

end Seg

end FV7z.Fn
