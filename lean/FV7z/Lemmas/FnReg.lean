import FV7z.Lemmas.FnSteps
/-!
# Steps whose value the proof does not follow; byte accesses `[b + i]` (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`AesGenTables` computes its tables with some hundred register instructions a round, whose values do not matter for
what it installs: only where it stores does. `WR prof i r`: the instruction `i` writes at most the register `r`, with
some value, and the status flags. One step lemma (`Seg.s_wr`) runs any such instruction; the instances here are the
forms of `AesGenTables`. Beside them: `movzx r32, byte [b + i]` and `mov byte [b + i], r8`, and `cmp r64, imm`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem set_get_self (g : Gprs) (n : Nat) : g.set (regOf n) (g.get (regOf n)) = g := by
  unfold Gprs.set Gprs.get
  generalize (regOf n).val = m
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> rfl

/-- The instruction `i` writes at most the register `r` and the status flags: never `TF`, `AC` or `DF`. -/
def WR (prof : Profile) (i : Inst) (r : Nat) : Prop :=
  ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false →
    Decode.decode prof.feat (fetchByte prof.feat s) = .ok i →
    ∃ v fl t', (instruction prof s).runStream o t = (.running (nx s i.len (s.cpu.gpr.set (regOf r) v) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df

theorem wr_mov_rr32 {r q len : Nat} : WR prof (mk .mov 32 [gr 32 r, gr 32 q] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, mov_rr32 htf hdec, rfl, rfl, rfl⟩

theorem wr_movzx_rr8 {r q len : Nat} : WR prof (mk .movzx 32 [gr 32 r, gr 8 q] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, movzx_rr8 htf hdec, rfl, rfl, rfl⟩

theorem wr_xor_rr32 {r q len : Nat} : WR prof (mk .xor 32 [gr 32 r, gr 32 q] len) r := fun _ _ _ htf hdec => by
  obtain ⟨fl, t', hr, h1, h2, h3⟩ := xor_rr (r := r) (q := q) htf hdec
  exact ⟨_, _, _, hr, h1, h2, h3⟩

theorem wr_and_ri32 {r imm len : Nat} : WR prof (mk .and 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_xor_ri32 {r imm len : Nat} : WR prof (mk .xor 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_or_rr32 {r q len : Nat} : WR prof (mk .or 32 [gr 32 r, gr 32 q] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_shl32 {r n len : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 24) : WR prof (mk .shl 32 [gr 32 r, .imm 8 n] len) r :=
  fun _ _ _ htf hdec => by
    rcases hn with rfl | rfl | rfl <;> exact ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_lea32 {r b i len : Nat} : WR prof (mk .lea 32 [gr 32 r, .mem (mbi b i 0 0)] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_cmov32 {cc : Cond} {r q len : Nat} : WR prof (mk (.cmovcc cc) 32 [gr 32 r, gr 32 q] len) r :=
  fun s o t htf hdec => by
    cases h : s.cpu.rflags.cond cc
    · refine ⟨(rv s 32 r).setWidth 64, rf0 s, t, ?_, rfl, rfl, rfl⟩
      refine instruction_next htf hdec ?_
      simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
        State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
      simp only [pure, Prog.run, Prog.bind, cond_rf0, h, Bool.false_eq_true, ↓reduceIte]; rfl
    · refine ⟨(rv s 32 q).setWidth 64, rf0 s, t, ?_, rfl, rfl, rfl⟩
      refine instruction_next htf hdec ?_
      simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
        State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
      simp only [pure, Prog.run, Prog.bind, cond_rf0, h, ↓reduceIte]; rfl

theorem wr_test_rr8 {r q len : Nat} : WR prof (mk .test 8 [gr 8 r, gr 8 q] len) r := fun s o t htf hdec => by
  obtain ⟨fl, t', hr, h1, h2, h3⟩ : ∃ fl t', (instruction prof s).runStream o t =
      (.running (nx s len s.cpu.gpr fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
    ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩
  exact ⟨_, fl, t', by rw [set_get_self]; exact hr, h1, h2, h3⟩

theorem wr_test_ri8 {r imm len : Nat} : WR prof (mk .test 8 [gr 8 r, .imm 8 imm] len) r := fun s o t htf hdec => by
  obtain ⟨fl, t', hr, h1, h2, h3⟩ : ∃ fl t', (instruction prof s).runStream o t =
      (.running (nx s len s.cpu.gpr fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
    ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩
  exact ⟨_, fl, t', by rw [set_get_self]; exact hr, h1, h2, h3⟩

/-- From the `j`-th byte of `code` to the `j'`-th, instructions each writing at most a register, every one of
which keeps `P`. -/
inductive WRun (prof : Profile) (code : List Byte) (P : Gprs → Prop) : Nat → Nat → Prop
  | done (j : Nat) : WRun prof code P j j
  | step {j j' : Nat} {i : Inst} {r : Nat} : Leaf.Dec prof.feat code j i → WR prof i r →
      (∀ g v, P g → P (g.set (regOf r) v)) → j < code.length → WRun prof code P (j + i.len) j' →
      WRun prof code P j j'

/-- `mov byte [b + i + d], r8` (a low byte). -/
theorem mov_m8i {b i d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 8 [.mem (mbi b i d 8), gr 8 r] len))
    (hwr : Writable prof s (eaI s b i d) 1) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaI s b i d) (toBytesLE (rv s 8 r) 1)) len
      s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mbi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, BitVec.mul_one]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- An instruction that writes at most the register `r`, with a value not followed. -/
theorem s_wr (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {i : Inst} {r : Nat} (hw : WR prof i r) (hd : Dec prof.feat code j i)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
      ∃ v, Y.cpu.gpr = X.cpu.gpr.set (regOf r) v) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨v, fl, t', hr, h1, h2, h3⟩ := hw (X.withMem M) o (t + 1) htf (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, v, rfl⟩) k'

/-- A run of instructions each writing at most a register, keeping `P`. -/
theorem s_wrun (c : Seg prof F Wl L s₀ o) {P : Gprs → Prop} {j j' : Nat}
    (h : WRun prof code P j j') (hin : CodeIn L e' code) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j → P X.cpu.gpr →
      ContG prof F Wl L s₀ o gev gP gE V (fun Y => Y.cpu.rip = e'.add j' ∧ P Y.cpu.gpr) →
      GoG prof L o gev gP gE X t := by
  induction h with
  | done j => intro X t V hK hA hrip hP k'; exact k' X t hK hA ⟨hrip, hP⟩
  | step hd hw hs hj _ ih =>
    intro X t V hK hA hrip hP k'
    refine c.s_wr hK hA hin hj hrip hw hd ?_
    rintro Y t' hK' hA' ⟨hr, v, hg⟩
    exact ih hK' hA' hr (hg ▸ hs _ v hP) k'

/-- `movzx r32, byte [b + i + d]`, from a byte of the footprint's data. -/
theorem s_movzx8_i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r b i d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .movzx 32 [gr 32 r, .mem (mbi b i d 8)] len))
    (hl : Foot F.data (eaI X b i d))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (((ofBytesLE 8 ((byteAddrs (eaI X b i d) 1).map V)).setWidth 32).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) (n := 1) hK' hA' fun i hi => by
      rw [show i = 0 by omega, addr_add_zero]; exact hl
    have hr := movzx8_i (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu]
      exact congrArg (fun z => X.cpu.gpr.set (regOf r) (((ofBytesLE 8 z).setWidth 32).setWidth 64)) hv⟩) k'

/-- `mov byte [b + i + d], r8`, into a byte the run may store into. -/
theorem s_mov_m8i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b i d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 8 [.mem (mbi b i d 8), gr 8 r] len))
    (hst : Foot Wl (eaI X b i d))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaI X b i d) (toBytesLE (rv X 8 r) 1))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 8 r) 1) (a := eaI X b i d) (by
        intro i hi; rw [toBytesLE_length] at hi; rw [show i = 0 by omega, addr_add_zero]; exact hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, mov_m8i (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩) k'

theorem s_cmp_ri64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 64 [gr 64 r, .imm 64 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (rv X 64 r) (BitVec.ofNat 64 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, cmp_ri (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

end Seg

end FV7z.Fn
