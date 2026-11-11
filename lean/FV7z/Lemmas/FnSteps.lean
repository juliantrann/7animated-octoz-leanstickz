import FV7z.Lemmas.Fn
import FV7z.Lemmas.InsFn
import FV7z.Lemmas.Agree
/-!
# A call of a function with a stack frame, an instruction at a time (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`LeafSteps.lean` for the contract `fn` (`Fn.lean`): from a state `X` at the `j`-th byte of a code segment, where the
code decodes to the instruction (`Dec`), the rest of the run goes on from every state `Y` it may leave (`Cont`), given
what `Y`'s `rip`, registers and the flags the code tests are in terms of `X`'s, and the footprint's bytes as a function
`V` (`Agree`): a store changes `V` (`Vst`), a load reads it. The code of each step is given at the step, so that a
caller's proof follows its callees' code.
-/
namespace FV7z
open ZellicX86

theorem ofBytesLE_toBytesLE {w n : Nat} (hw : w = 8 * n) (v : BitVec w) : ofBytesLE w (toBytesLE v n) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : i / 8 < n := by omega
  rw [getLsbD_ofBytesLE]
  simp only [toBytesLE, hi, h1, decide_true, Bool.true_and, List.length_map, List.length_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have h2 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  rw [show 8 * (i / 8) + i % 8 = i by omega]
  simp [h2]

@[simp] theorem toBytesLE_length {w : Nat} (v : BitVec w) (n : Nat) : (toBytesLE v n).length = n := by
  simp [toBytesLE]

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- The rest of the run, from every state the step may leave of which `Pr` holds, with the footprint's bytes `V`, to
the goal `gP`/`gE` with the events `gev` so far. -/
abbrev ContG (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (Pr : State → Prop) : Prop :=
  ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Pr Y → GoG prof L o gev gP gE Y t'

/-- `ContG` for a call: the rest of the run returns as the contract says. -/
abbrev Cont (prof : Profile) (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop)
    (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (V : Addr → Byte) (Pr : State → Prop) :
    Prop :=
  ∀ Y t', KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V → Pr Y →
    Go prof k W R pre post L s₀ ra o Y t'

namespace Seg

/-- The kernel's stores of the `rseq` ids keep `Agree`. -/
theorem agreeK (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) {M : Memory}
    (hM : Calm (IdAddr X.thread.rseq) X.proc.mm.mem M) : Agree F M V := by
  rw [hK.thread] at hM
  exact Agree.kernel c.foot c.ready.rseq hK.calm hA hM

/-- A step to a state of which `Pr` holds, with the footprint's bytes `V'`. -/
theorem next (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {V' : Addr → Byte} {Pr : State → Prop}
    (hrun : ∀ M, KeptW Wl s₀ (X.withMem M) → Agree F M V →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧
        KeptW Wl s₀ Y ∧ Agree F Y.proc.mm.mem V' ∧ Pr Y)
    (k' : ContG prof F Wl L s₀ o gev gP gE V' Pr) : GoG prof L o gev gP gE X t :=
  c.step hK hin hj hrip fun M hM hK' htf hac => by
    obtain ⟨Y, t', hr, hKY, hAY, hP⟩ := hrun M hK' (c.agreeK hK hA hM) htf hac
    exact ⟨Y, t', hr, k' Y t' hKY hAY hP⟩

/-! ## Accesses -/

/-- A byte the run may store into: data of the footprint, which the thread may write, in its own memory. -/
theorem ws_acc (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) {y : Addr}
    (hy : Foot Wl y) :
    Foot F.data y ∧ y.canonical prof.feat.la57 = true ∧
      X.proc.mm.mem.check prof.feat X.cpu.pkru .write y = none ∧ OwnAt X.proc.mm.mem y := by
  have hd := c.hws y hy
  obtain ⟨q, hq, hqm⟩ := c.hww y hy
  have hw := c.foot.writable q hq y hqm
  refine ⟨hd, hw.1, by rw [hK.calm.check, hK.pkru]; exact hw.2, hK.calm.ownAt (ownAt_of (rs := [q]) ?_ ?_
    ⟨q, List.mem_singleton_self _, hqm⟩)⟩
  · rintro a ⟨q', hq', hm'⟩
    simp only [List.mem_singleton] at hq'
    subst hq'
    exact c.foot.notKernel a ⟨q', List.mem_append_left _ (by simp [Footprint.data, hq]), hm'⟩
  · rintro a ⟨q', hq', hm'⟩
    simp only [List.mem_singleton] at hq'
    subst hq'
    exact c.foot.notShared a ⟨q', List.mem_append_left _ hq, hm'⟩

/-- A byte of the footprint's data can be read. -/
theorem data_rd (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) {y : Addr}
    (hy : Foot F.data y) :
    y.canonical prof.feat.la57 = true ∧ X.proc.mm.mem.check prof.feat X.cpu.pkru .read y = none := by
  obtain ⟨r, hr, hm⟩ := hy
  rw [hK.calm.check, hK.pkru]
  simp only [Footprint.data, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · have hw := c.foot.writable r hr y hm
    exact ⟨hw.1, check_read_of_write hw.2⟩
  · rw [c.own] at hr; simp at hr
  · exact c.foot.readable r hr y hm

/-- A store of `bs` at `a`, bytes the run may store into: they can be written, and the state it leaves keeps
`KeptW` and `Agree` with `V` as the store changes it. -/
theorem store_ok (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) {a : Addr} {bs : List Byte}
    (hst : ∀ i < bs.length, Foot Wl (a.add i)) :
    Writable prof X a bs.length ∧ KeptW Wl s₀ (st X a bs) ∧
      Agree F (st X a bs).proc.mm.mem (Vst V a bs) := by
  refine ⟨fun x hx => ?_, hK.store (feat := prof.feat) fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    obtain ⟨-, h1, h2, -⟩ := c.ws_acc hK (hst i hi)
    exact ⟨h1, h2⟩
  · obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    obtain ⟨-, -, h2, h3⟩ := c.ws_acc hK (hst i hi)
    exact ⟨hst i hi, h2, h3⟩
  · exact Agree.writeBytes c.foot bs X.proc.mm.mem a V (hK.calm.mono fun _ _ => trivial)
      (fun i hi => by
        obtain ⟨h0, -, h2, h3⟩ := c.ws_acc hK (hst i hi)
        exact ⟨h0, h2, h3⟩) hA

/-- A load of `n` bytes of the footprint's data at `a`: they can be read, and are those of `V`. -/
theorem load_ok (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) {a : Addr} {n : Nat}
    (hl : ∀ i < n, Foot F.data (a.add i)) :
    Readable prof X a n ∧ readBytes X.proc.mm.mem a n = (byteAddrs a n).map V := by
  refine ⟨fun x hx => ?_, hA.read hl⟩
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  exact c.data_rd hK (hl i hi)

/-! ## Instructions without memory operands -/

theorem s_endbr (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .endbr64 32 [] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, endbr (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

theorem s_sub_ri64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 64 [gr 64 r, .imm 64 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) - BitVec.ofNat 64 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, sub_ri (s := X.withMem M) (Or.inr rfl) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [rv, BitVec.setWidth_eq]⟩) k'

theorem s_add_ri64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 64 [gr 64 r, .imm 64 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) + BitVec.ofNat 64 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, add_ri (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [rv, BitVec.setWidth_eq]⟩) k'

theorem s_mov_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((BitVec.ofNat 32 imm).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, mov_ri32 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

theorem s_mov_rr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 q).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, mov_rr32 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

theorem s_mov_rr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 64 [gr 64 r, gr 64 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf q))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, mov_rr (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [rv, BitVec.setWidth_eq]⟩) k'

theorem s_xor_rr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .xor 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r ^^^ rv X 32 q).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := xor_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

theorem s_and_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .and 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r &&& BitVec.ofNat 32 imm).setWidth 64) ∧
      Y.cpu.rflags.zf = (rv X 32 r &&& BitVec.ofNat 32 imm == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ : ∃ af t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running (nx (X.withMem M)
        len (X.cpu.gpr.set (regOf r) ((rv X 32 r &&& BitVec.ofNat 32 imm).setWidth 64))
        ((rf0 X).arith (rv X 32 r &&& BitVec.ofNat 32 imm) false false af)) none, t') :=
      ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) rfl⟩
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

theorem s_and_rr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .and 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r &&& rv X 32 q).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := and_rr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

theorem s_shr_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat} (hi : imm ∈ [1, 2, 5, 9, 19, 25, 27, 28, 29])
    (hd : Dec prof.feat code j (FV7z.mk .shr 32 [gr 32 r, .imm 8 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r >>> imm).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := shr_ri32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) hi htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

theorem s_test_rr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .test 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (rv X 32 r &&& rv X 32 q == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := test_rr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

theorem s_cmp_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (rv X 32 r) (BitVec.ofNat 32 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, cmp_ri (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, rfl⟩) k'

/-- `lea r64, [rip + d]`, the address `v`. -/
theorem s_lea_rip (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .lea 64 [gr 64 r, .mem (mrip d 0)] len)) {v : Addr}
    (hv : e'.add (j + len) + BitVec.ofNat 64 d = v)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) v ∧ Y.cpu.rflags = rf0 X) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, lea_rip (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      show X.cpu.gpr.set (regOf r) (X.cpu.rip.add len + _) = _
      rw [hrip, addr_add_add, hv], rfl⟩) k'

theorem s_cmov (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.cmovcc cc) 64 [gr 64 r, gr 64 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (if X.cpu.rflags.cond cc then X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf q)) else X.cpu.gpr) ∧
      Y.cpu.rflags = rf0 X) :
    GoG prof L o gev gP gE X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, cmov_n (s := X.withMem M) htf
      (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [hcc], rfl⟩) k'
  · exact c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, cmov_t (s := X.withMem M) htf
      (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len,
      by simp [hcc, rv, BitVec.setWidth_eq], rfl⟩) k'

/-- `jcc` to the `tgt`-th byte of the same segment. -/
theorem s_jcc (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {rel len tgt : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true →
      ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr)
    (fall : X.cpu.rflags.cond cc = false →
      ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf
      (c.dec hK' hin hrip hd) hcc, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) (fall hcc)
  · refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) (taken hcc)
    have hca := ((c.codeAt hK' hin) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
      rw [withMem_cpu, hrip]; exact addr_rel htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hin hrip hd) hcc (by rw [ha]; exact hca),
      hK'.upd rfl rfl rfl, hA', ha, rfl⟩

/-- `jmp` to the `tgt`-th byte of the same segment. -/
theorem s_jmp (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {rel len tgt : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.rel rel] len))
    (htgt : (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  refine c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) k'
  have hca := ((c.codeAt hK' hin) tgt ht).1
  have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e'.add tgt := by
    rw [withMem_cpu, hrip]; exact addr_rel htgt
  exact ⟨_, _, jmp_rel (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl⟩

/-- `cpuid`, on some CPU of the profile. -/
theorem s_cpuid (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .cpuid 32 [] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      ∃ cpu, cpu < max prof.cpus 1 ∧
        let r := prof.cpuid cpu (X.cpu.gpr.rax.setWidth 32) (X.cpu.gpr.rcx.setWidth 32)
        Y.cpu.gpr = (((X.cpu.gpr.set 0 (r.eax.setWidth 64)).set 3 (r.ebx.setWidth 64)).set 1
          (r.ecx.setWidth 64)).set 2 (r.edx.setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ =>
    ⟨_, _, cpuid_i (s := X.withMem M) htf (c.dec hK' hin hrip hd)
      (by rw [hK'.thread]; exact c.ready.plain.2.2.2), hK'.nx rfl rfl rfl, hA', rip_add hrip M len,
      _, by have := (o (t + 1) (.pick (prof.cpus - 1))).isLt; omega, rfl⟩) k'

/-- `xgetbv` with `ECX = 0`: `XCR0`. -/
theorem s_xgetbv (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .xgetbv 32 [] len))
    {x : BitVec 64} (hx : prof.xcr0 = some x) (hc : X.cpu.gpr.rcx.setWidth 32 = 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (X.cpu.gpr.set 0 ((x.setWidth 32).setWidth 64)).set 2 ((x.extractLsb' 32 32).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ =>
    ⟨_, _, xgetbv0 (s := X.withMem M) htf (c.dec hK' hin hrip hd) hx hc, hK'.nx rfl rfl rfl, hA',
      rip_add hrip M len, rfl⟩) k'

/-! ## Stores -/

/-- `push r64`, into bytes the run may store into. -/
theorem s_push (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r len : Nat} (hd : Dec prof.feat code j (FV7z.mk .push 64 [gr 64 r] len))
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (X.cpu.gpr.get (regOf r)) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hw, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (X.cpu.gpr.get (regOf r)) 8) (a := X.cpu.gpr.rsp - 8) (by simpa using hst)
    rw [toBytesLE_length] at hw
    refine ⟨_, _, push_r (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hw, hKs.nx rfl rfl rfl, ?_,
      rip_add hrip M len, rfl⟩
    simpa [rv, BitVec.setWidth_eq] using hAs) k'

/-- `mov [b + d], rW`, into bytes the run may store into. -/
theorem s_mov_mr (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {w b d r len : Nat} (hw : w = 32 ∨ w = 64)
    (hd : Dec prof.feat code j (FV7z.mk .mov w [.mem (mbd b d w), gr w r] len))
    (hst : ∀ i < w / 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (rv X w r) (w / 8)))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X w r) (w / 8)) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, mov_mr (s := X.withMem M) hw htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩) k'

/-- `mov [rip + d], r64`, into bytes the run may store into. -/
theorem s_mov_rip_r64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 64 [.mem (mrip d 64), gr 64 r] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 8, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (X.cpu.gpr.get (regOf r)) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (X.cpu.gpr.get (regOf r)) 8) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    have hr := mov_rip_r64 (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr
    rw [he] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, by simpa [rv, BitVec.setWidth_eq] using hAs, rip_add hrip M len, rfl⟩) k'

/-- `call rel32` to a segment's first byte, pushing into bytes the run may store into. -/
theorem s_call (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {rel len : Nat} (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8))
      fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hra : (X.withMem M).cpu.rip.add len = e'.add (j + len) := rip_add hrip M len
    have hca := ((c.codeAt hK' hin₂) 0 h₂).1
    rw [addr_add_zero] at hca
    obtain ⟨hw, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (e'.add (j + len)) 8) (a := X.cpu.gpr.rsp - 8) (by simpa using hst)
    rw [toBytesLE_length] at hw
    have hr := call_rel (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd)
      (by rw [hK'.thread]; exact c.ready.plain.2.2.1) (by rw [hra, htgt]; exact hca) hw
    rw [hra, htgt] at hr
    exact ⟨_, _, hr, hKs.upd rfl rfl rfl, hAs, rfl, rfl⟩) k'

/-! ## Loads -/

/-- `pop r64`, from bytes of the footprint's data. -/
theorem s_pop (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r len : Nat} (hd : Dec prof.feat code j (FV7z.mk .pop 64 [gr 64 r] len))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)).set (regOf r)
        (ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := pop_r (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu, BitVec.setWidth_eq]
      exact congrArg (fun z => (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)).set (regOf r) (ofBytesLE 64 z)) hv⟩) k'

/-- `mov rW, [b + d]`, from bytes of the footprint's data. -/
theorem s_mov_rm (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {w r b d len : Nat} (hw : w = 32 ∨ w = 64)
    (hd : Dec prof.feat code j (FV7z.mk .mov w [gr w r, .mem (mbd b d w)] len))
    (hl : ∀ i < w / 8, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE w ((byteAddrs (eaD X b d) (w / 8)).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := mov_rm (s := X.withMem M) (o := o) (t := t + 1) (r := r) hw htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu]
      exact congrArg (fun z => X.cpu.gpr.set (regOf r) ((ofBytesLE w z).setWidth 64)) hv⟩) k'

/-- `mov r64, fs:[d]`, from bytes of the footprint's data. -/
theorem s_mov_fs (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 64 [gr 64 r, .mem (mfs d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaF X d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (ofBytesLE 64 ((byteAddrs (eaF X d) 8).map V))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := mov_r64_fs (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu, BitVec.setWidth_eq]
      exact congrArg (fun z => X.cpu.gpr.set (regOf r) (ofBytesLE 64 z)) hv⟩) k'

/-- `xor r64, fs:[d]`, from bytes of the footprint's data. -/
theorem s_xor_fs (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .xor 64 [gr 64 r, .mem (mfs d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaF X d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) ^^^ ofBytesLE 64 ((byteAddrs (eaF X d) 8).map V)) ∧
      Y.cpu.rflags.zf = (X.cpu.gpr.get (regOf r) ^^^ ofBytesLE 64 ((byteAddrs (eaF X d) 8).map V) == 0)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    obtain ⟨af, t', hr⟩ := xor_r64_fs (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac
      (c.dec hK' hin hrip hd) hrd
    rw [show (X.withMem M).proc.mm.mem = M from rfl, show eaF (X.withMem M) d = eaF X d from rfl] at hr
    rw [show (X.withMem M).proc.mm.mem = M from rfl] at hv
    rw [hv] at hr
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [rv, BitVec.setWidth_eq],
      by simp [rv, BitVec.setWidth_eq]⟩) k'

/-- `ret` inside the run (a callee's), to the address the bytes at `rsp` hold. -/
theorem s_ret (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) (hd : Dec prof.feat code j (FV7z.mk .ret 64 [] 1))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧
      Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hca := ((c.codeAt hK' hin₂) j₂ h₂).1
    have hw : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsp 8) = e₂.add j₂ := by
      exact (congrArg (ofBytesLE 64) hv).trans hra
    exact ⟨_, _, FV7z.ret htf hac (c.dec hK' hin hrip hd) (by rw [hK'.thread]; exact c.ready.plain.2.2.1)
      hw hca hrd, hK'.upd rfl rfl rfl, hA', rfl, rfl⟩) k'

theorem s_add_ri32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 32 [gr 32 r, .imm 32 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r + BitVec.ofNat 32 imm).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, add_ri32 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp only [nx_gpr, addR_eq]; rfl⟩) k'

/-- `setcc r8`: the low byte of the register is the condition. -/
theorem s_setcc (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {cc : Cond} {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.setcc cc) 8 [gr 8 r] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      ∃ v : BitVec 64, Y.cpu.gpr = X.cpu.gpr.set (regOf r) v ∧
        v.setWidth 8 = (BitVec.ofBool (X.cpu.rflags.cond cc)).setWidth 8) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, setcc_r8 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, _, rfl, setcc_low _ _⟩) k'

/-- `movzx r32, r8`. -/
theorem s_movzx_rr8 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .movzx 32 [gr 32 r, gr 8 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (((rv X 8 q).setWidth 32).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, movzx_rr8 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `mov [rip + d], r32`, into bytes the run may store into. -/
theorem s_mov_rip_r32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 32 [.mem (mrip d 32), gr 32 r] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    have hr := mov_rip_r32 (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hwr
    rw [he] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `mov r64, imm` (the immediate as the decoder gives it). -/
theorem s_mov_ri64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .mov 64 [gr 64 r, .imm 64 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (BitVec.ofNat 64 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, mov_ri64 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- `sbb r32, r32`. -/
theorem s_sbb_rr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sbb 32 [gr 32 r, gr 32 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r)
        ((rv X 32 r - rv X 32 q - (BitVec.ofBool X.cpu.rflags.cf).setWidth 32).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, sbb_rr32 (s := X.withMem M) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

end Seg

end FV7z.Fn
