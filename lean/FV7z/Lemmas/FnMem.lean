import FV7z.Lemmas.FnReg
import FV7z.Lemmas.InsMem
/-!
# Steps on memory words, flags and bits for functions with a stack frame (PLAN.md G2, glibc `init_cpu_features`)

`Fn.Seg` steps (as `FnSteps.lean`) for the forms of `InsMem.lean` and of `InsRip.lean` that 7-Zip's functions did not
use: a read-modify-write `or [rip + d], imm` of a word the run may store into, loads and `cmp` of memory words,
`add` with memory, `mov [b + d], imm`, `lea [b + d]`, the `test`s whose `ZF`/`SF` a branch reads, and any instruction
that writes only flags (`FL`).
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `test r64, r64'`: `AF` undefined. -/
theorem test_rr64 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 64 [gr 64 r, gr 64 q] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (rv s 64 r &&& rv s 64 q) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `cmovcc r32, r32'`: the destination's low half zero-extended, or the source's. -/
theorem cmov32 {cc : Cond} {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.cmovcc cc) 32 [gr 32 r, gr 32 q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((if s.cpu.rflags.cond cc then rv s 32 q else rv s 32 r).setWidth 64)) (rf0 s)) none, t) := by
  cases h : s.cpu.rflags.cond cc
  · refine instruction_next htf hdec ?_
    simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
      State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
    simp only [pure, Prog.run, Prog.bind, cond_rf0, h, Bool.false_eq_true, ↓reduceIte]; rfl
  · refine instruction_next htf hdec ?_
    simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
      State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
    simp only [pure, Prog.run, Prog.bind, cond_rf0, h, ↓reduceIte]; rfl

theorem wr_and_h8i {r imm len : Nat} : WR prof (mk .and 8 [gh r, .imm 8 imm] len) r := fun s o t htf hdec => by
  obtain ⟨af, t', hr⟩ := and_h8i (s := s) (o := o) (t := t) (r := r) (imm := imm) (len := len) htf hdec
  exact ⟨_, _, _, hr, rfl, rfl, rfl⟩

theorem wr_and_r8i {r imm len : Nat} : WR prof (mk .and 8 [gr 8 r, .imm 8 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_shr32 {r n len : Nat} (hn : n = 4 ∨ n = 8 ∨ n = 12 ∨ n = 20) :
    WR prof (mk .shr 32 [gr 32 r, .imm 8 n] len) r :=
  fun _ _ _ htf hdec => by
    rcases hn with rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_add_ri32 {r imm len : Nat} : WR prof (mk .add 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_mov_ri32 {r imm len : Nat} : WR prof (mk .mov 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_or_ri32 {r imm len : Nat} : WR prof (mk .or 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem wr_mov_rr64 {r q len : Nat} : WR prof (mk .mov 64 [gr 64 r, gr 64 q] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- An instruction that writes only flags (`FL`), whose flags are not followed. -/
theorem s_fl (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {i : Inst} (hw : FL prof i) (hd : Dec prof.feat code j i)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + i.len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := hw (X.withMem M) o (t + 1) htf (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, rfl⟩) k'

/-- `or dword [rip + d], imm32`, on a word the run may store into. -/
theorem s_or_rip_i32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .or 32 [.mem (mrip d 32), .imm 32 imm] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V g (toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) ||| BitVec.ofNat 32 imm) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) ||| BitVec.ofNat 32 imm) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨af, t', hr⟩ := or_m32i_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `mov r32, dword [rip + d]`, from bytes of the footprint's data. -/
theorem s_mov_r32_rip (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 32 [gr 32 r, .mem (mrip d 32)] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hl : ∀ i < 4, Foot F.data (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 32 ((byteAddrs g 4).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    rw [← he] at hrd
    have hr := mov_r32_rip (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hrd
    rw [he, hv] at hr
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `test byte [rip + d], imm8`, from a byte of the footprint's data: `ZF`. -/
theorem s_test_m8i_rip (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 imm] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hl : Foot F.data g)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (ofBytesLE 8 ((byteAddrs g 1).map V) &&& BitVec.ofNat 8 imm == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (n := 1) (a := g)
      (fun i hi => by rw [show i = 0 by omega, addr_add_zero]; exact hl)
    rw [← he] at hrd
    obtain ⟨af, t', hr⟩ := test_m8i_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd
    rw [he, hv] at hr
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `cmp dword [rip + d], imm32`, from bytes of the footprint's data; flags not followed. -/
theorem s_cmp_m32i_rip (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 32 [.mem (mrip d 32), .imm 32 imm] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hl : ∀ i < 4, Foot F.data (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hrd, -⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    rw [← he] at hrd
    exact ⟨_, _, cmp_m32i_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd,
      hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `cmp dword [b + d], imm32`, from bytes of the footprint's data; flags not followed. -/
theorem s_cmp_m32i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 32 [.mem (mbd b d 32), .imm 32 imm] len))
    (hl : ∀ i < 4, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, -⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    exact ⟨_, _, cmp_m32i (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd,
      hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `add r32, dword [b + d]`, from bytes of the footprint's data. -/
theorem s_add_rm32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 32 [gr 32 r, .mem (mbd b d 32)] len))
    (hl : ∀ i < 4, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r + ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := add_rm32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu, addR_eq]
      exact congrArg (fun z => X.cpu.gpr.set (regOf r) ((rv X 32 r + ofBytesLE 32 z).setWidth 64)) hv⟩) k'

/-- `add dword [b + d], r32`, on a word the run may store into. -/
theorem s_add_mr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 32 [.mem (mbd b d 32), gr 32 r] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) + rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) + rv X 32 r) 4) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    have hr := add_mr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hwr
    simp only [withMem_cpu, addR_eq] at hr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `mov dword [b + d], imm32`, into bytes the run may store into. -/
theorem s_mov_mi32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 32 [.mem (mbd b d 32), .imm 32 imm] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (BitVec.ofNat 32 imm) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (BitVec.ofNat 32 imm) 4) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, mov_mi32 (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr,
      hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `lea r64, [b + d]`. -/
theorem s_lea_bd (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .lea 64 [gr 64 r, .mem (mbd b d 0)] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (eaD X b d)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, lea_bd (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `test r32, imm32`: `ZF` and `SF`. -/
theorem s_test_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (rv X 32 r &&& BitVec.ofNat 32 imm == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := test_ri32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `test r32, r32'`: `SF`. -/
theorem s_test_rr32s (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.sf = (rv X 32 r &&& rv X 32 q).msb) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := test_rr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `test r8h, imm8` (`ah`, `ch`, `dh`, `bh`): `ZF`. -/
theorem s_test_h8i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 8 [gh r, .imm 8 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = ((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := test_h8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `or r32, imm32`. -/
theorem s_or_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .or 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r ||| BitVec.ofNat 32 imm).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := or_ri (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

/-- `test r64, r64'`: `ZF`. -/
theorem s_test_rr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 64 [gr 64 r, gr 64 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (rv X 64 r &&& rv X 64 q == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := test_rr64 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `s_wr` for an instruction built by `mk`: the next `rip` with its length. -/
theorem s_wrl (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {mn : Mn} {opsz len r : Nat} {ops : List Opd}
    (hw : WR prof (FV7z.mk mn opsz ops len) r) (hd : Dec prof.feat code j (FV7z.mk mn opsz ops len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      ∃ v, Y.cpu.gpr = X.cpu.gpr.set (regOf r) v) :
    GoG prof L o gev gP gE X t :=
  c.s_wr hK hA hin hj hrip hw hd k'

/-- `s_fl` for an instruction built by `mk`. -/
theorem s_fll (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {mn : Mn} {opsz len : Nat} {ops : List Opd}
    (hw : FL prof (FV7z.mk mn opsz ops len)) (hd : Dec prof.feat code j (FV7z.mk mn opsz ops len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.s_fl hK hA hin hj hrip hw hd k'

/-- `cmovcc r32, r32'`. -/
theorem s_cmov32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.cmovcc cc) 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((if X.cpu.rflags.cond cc then rv X 32 q else rv X 32 r).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, cmov32 (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

end Seg

end FV7z.Fn
