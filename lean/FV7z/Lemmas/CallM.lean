import FV7z.Lemmas.CallFn
import FV7z.Lemmas.FnMem
/-!
# `call qword [b + d]`, and a call of a leaf function by its `ImplementsCall` (PLAN.md G2, glibc `apply_irel`)

`apply_irel`, inlined in `__libc_start_main`, calls each IFUNC resolver through its relocation's addend
(`call *0x10(%rbx)`) and stores what it returns into the relocation's GOT slot. The resolvers are leaf functions with
their own proofs; for the run to go on past the call the contract has to say what the callee kept (`Leaf.leafK`),
as `fnK` does for a function with a frame (`CallFn.lean`).

`Seg.s_callM` is the call's step, `Seg.enterK` the callee's run from its entry (for any form of call), and
`fnK_of_leafK` gives a leaf function's theorem the form `enterK` takes.

Also `cmp dword [b + d], imm32` with its flags followed (the relocation's type), and `mov` with the flags kept.
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `call qword [b + d]`: the target is read, then the return address pushed. -/
theorem call_m {b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .call 64 [.mem (mbd b d 64)] len))
    (hsh : s.thread.shstk = none) (hld : Readable prof s (eaD s b d) 8)
    (hcan : Addr.canonical prof.feat.la57 (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) = true)
    (hw : Writable prof s (s.cpu.gpr.rsp - 8) 8) :
    (instruction prof s).runStream o t = (.running (upd (st s (s.cpu.gpr.rsp - 8) (toBytesLE (s.cpu.rip.add len) 8))
      (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) (s.cpu.gpr.set 4 (s.cpu.gpr.rsp - 8)) (rf0 s)) none,
      t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.call, push64, mbd, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readRip, Prog.readReg,
    Prog.write, Prog.writeReg, Prog.writeRip, pure, show (advance s len).thread.shstk = none from hsh,
    Bool.false_eq_true, ↓reduceIte, done, readOp, memRef, effOffset, Prog.read, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rw [show (advance s len).proc.mm.mem = s.proc.mm.mem from rfl, hcan]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prog.run, bind, pure]
  rw [checkAccess_ok (s := advance s len) hac hw]
  rfl

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}
  {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}

/-- A leaf function with its own proof (`Leaf.leafK`), by the contract a caller's run goes on with (`fnK`, no frame,
no region of its own to store into). -/
theorem fnK_of_leafK {e : Addr} {Q : State → BitVec 64 → Prop} (h : ImplementsCall prof e L (leafK R pre Q)) :
    ImplementsCall prof e L (fnK 0 (fun _ => []) R pre fun s Z => Q s Z.cpu.gpr.rax) := by
  intro s₀ ra hc o ho t
  obtain ⟨n, st, evs, t', hrun, hI, hP⟩ := h s₀ ra ⟨hc.shape, hc.ready, hc.foot, hc.pre⟩ o ho t
  refine ⟨n, st, evs, t', hrun, hI, ?_⟩
  cases st with
  | running s => exact ⟨hP.1, hP.2.1, ⟨hP.2.2.1.1, KeptW.of_kept hP.2.2.1.2⟩, hP.2.2.2⟩
  | done out => exact hP

namespace Seg

/-- `mov rW, [b + d]`, from bytes of the footprint's data, with the flags it leaves as they were. -/
theorem s_mov_rm_f (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {w r b d len : Nat} (hw : w = 32 ∨ w = 64)
    (hd : Dec prof.feat code j (FV7z.mk .mov w [gr w r, .mem (mbd b d w)] len))
    (hl : ∀ i < w / 8, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE w ((byteAddrs (eaD X b d) (w / 8)).map V)).setWidth 64) ∧
      Y.cpu.rflags = rf0 X) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := mov_rm (s := X.withMem M) (o := o) (t := t + 1) (r := r) hw htf hac (c.dec hK' hin hrip hd) hrd
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by
      simp only [nx_gpr, withMem_cpu]
      exact congrArg (fun z => X.cpu.gpr.set (regOf r) ((ofBytesLE w z).setWidth 64)) hv, rfl⟩) k'

/-- `cmp dword [b + d], imm32`, from bytes of the footprint's data, with its flags. -/
theorem s_cmp_m32i_f (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 32 [.mem (mbd b d 32), .imm 32 imm] len))
    (hl : ∀ i < 4, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V)) (BitVec.ofNat 32 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    exact ⟨_, _, cmp_m32i (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd,
      hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl,
      congrArg (fun z => subF (rf0 X) (ofBytesLE 32 z) (BitVec.ofNat 32 imm)) hv⟩) k'

/-- `call qword [b + d]` to a segment's first byte, the target read from the footprint's data, pushing into bytes
the run may store into. -/
theorem s_callM (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.mem (mbd b d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaD X b d).add i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) = e₂)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8))
      fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hra : (X.withMem M).cpu.rip.add len = e'.add (j + len) := rip_add hrip M len
    have hca := ((c.codeAt hK' hin₂) 0 h₂).1
    rw [addr_add_zero] at hca
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hT : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8) = e₂ :=
      (congrArg (ofBytesLE 64) hv).trans htgt
    obtain ⟨hw, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (e'.add (j + len)) 8) (a := X.cpu.gpr.rsp - 8) (by simpa using hst)
    rw [toBytesLE_length] at hw
    have hr := call_m (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd)
      (by rw [hK'.thread]; exact c.ready.plain.2.2.1) hrd (by rw [hT]; exact hca) hw
    rw [hra, hT] at hr
    exact ⟨_, _, hr, hKs.upd rfl rfl rfl, hAs, rfl, rfl⟩) k'

/-- The callee's entry, after a `call` (of any form) left the return address `ra` in the stack: a function with its
own proof (`ImplementsCall` of `fnK`) returns, and the run goes on from every state it may return in, with the bytes
of `F` the callee does not store into as at its entry. -/
theorem enterK (c : Seg prof F Wl L s₀ o) {Y : State} {t₁ : Nat} {V' : Addr → Byte} {ra e₂ : Addr}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V') (hrY : Y.cpu.rip = e₂)
    (hsl : ∀ i < 8, Foot Wl (Addr.add Y.cpu.gpr.rsp i))
    (hword : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = ra)
    (himp : ImplementsCall prof e₂ L (fnK k W R pre post))
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hcan : ra.canonical prof.feat.la57 = true) (hal : (Y.cpu.gpr.rsp + 8).toNat % 16 = 0)
    (hsub : Sub F ((fnK k W R pre post).footprint L Y)) (hwsW : ∀ y, Foot (ws k W Y) y → Foot Wl y) (hpre : pre Y)
    (k' : ∀ Z t', KeptW Wl s₀ Z →
      (∀ y, Foot F.data y → ¬ Foot (ws k W Y) y → Z.proc.mm.mem.readByte y = V' y) →
      Returns sysv Y ra Z → post Y Z → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have hokY : F.Ok prof.feat Y := c.foot.keptW c.ready.rseq c.hws hKY c.sub_self
  have hRY : Ready prof.feat Y := c.ready.keptW c.foot c.hws hKY
  have hGok := c.foot.keptW c.ready.rseq c.hws hKY hsub
  have hword' : Word Y Y.cpu.gpr.rsp ra := by
    unfold Word
    rw [hAY.read (fun i hi => c.hws _ (hsl i hi))]
    exact hword
  have hent : sysv.entry Y := ⟨hal, by rw [hKY.df]; exact hdf, by rw [hKY.x87]; exact hx87⟩
  have hcall : CallOf prof e₂ L (fnK k W R pre post) Y ra := ⟨⟨hrY, hword', hcan, hent⟩, hRY, hGok, hpre⟩
  refine RunsFrom.bind (runsFrom_of_reach (himp Y _ hcall) c.env t₁ (gE := gE) fun _ _ h => h.elim) ?_
  rintro Z T _ ⟨evs, rfl, hret, -, ⟨hpost, hKZ⟩, hev⟩
  have hev' : evs = [] := hev
  subst hev'
  rw [List.append_nil]
  refine k' Z T (hKY.trans hKZ hwsW) (fun y hy hny => ?_) hret hpost
  rw [hKZ.calm.readByte_apart hokY hRY.rseq (fun y hy => c.hws y (hwsW y hy)) (foot_append_iff.2 (Or.inl hy)) hny]
  exact hAY y hy

end Seg

end FV7z.Fn
