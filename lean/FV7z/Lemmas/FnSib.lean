import FV7z.Lemmas.FnMem
/-!
# Scaled indices: `lea` and `cmp byte` with `[b + i·s + d]`, `sub r64, r64` (PLAN.md G2, glibc `__tunable_get_val`)

glibc's `__tunable_get_val` finds its tunable's entry as `tunable_list + 56·id`: `lea rax, [rdi·8]`, `sub rax, rdi`,
`lea rax, [rcx + rax·8]`, and tests the entry's `initialized` byte with `cmp byte [rcx + rax·8 + 40], 0`. The
memory operand with an index scaled by `sc` and an optional base (`msi`), its address (`eaS`), and the `Fn.Seg` steps.
-/
namespace FV7z
open ZellicX86 Decode

/-- The memory operand `[b + i·sc + disp]` (no base if `b` is `none`) of `width` bits. -/
def msi (b : Option Nat) (i sc disp width : Nat) : MemOp :=
  { seg := none, base := b, index := some i, scale := sc, disp, ripRel := false, addr32 := false, width }

/-- The base's value: `0` without one. -/
def baseV (s : State) : Option Nat → Addr
  | some b => s.cpu.gpr.get (regOf b)
  | none => 0

/-- The address `[b + i·sc + d]`. -/
abbrev eaS (s : State) (b : Option Nat) (i sc d : Nat) : Addr :=
  baseV s b + s.cpu.gpr.get (regOf i) * BitVec.ofNat 64 sc + BitVec.ofNat 64 d

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `lea r64, [b + i·sc + d]`. -/
theorem lea_si {r i sc d len : Nat} {b : Option Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .lea 64 [gr 64 r, .mem (msi b i sc d 0)] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) (eaS s b i sc d)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  cases b <;>
  · simp only [exec, Sem.lea, mk, msi, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg,
      Bool.false_eq_true, ↓reduceIte, writeOp, BitVec.setWidth_eq]
    rfl

/-- `cmp byte [b + i·sc + d], imm8`. -/
theorem cmp_m8i_si {i sc d imm len : Nat} {b : Option Nat} (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmp 8 [.mem (msi b i sc d 8), .imm 8 imm] len))
    (hld : Readable prof s (eaS s b i sc d) 1) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      (subF (rf0 s) (ofBytesLE 8 (readBytes s.proc.mm.mem (eaS s b i sc d) 1)) (BitVec.ofNat 8 imm))) none, t) := by
  refine instruction_next htf hdec ?_
  cases b with
  | none =>
    simp only [exec, Sem.cmp, alu, subOp, mk, msi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, Nat.reduceDiv]
    rw [show (0 : Addr) + (advance s len).cpu.gpr.get (regOf i) * BitVec.ofNat 64 sc + BitVec.ofNat 64 d =
      eaS s none i sc d from rfl, checkAccess_ok (s := advance s len) hac hld]
    rfl
  | some b =>
    simp only [exec, Sem.cmp, alu, subOp, mk, msi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, Nat.reduceDiv]
    rw [show (advance s len).cpu.gpr.get (regOf b) + (advance s len).cpu.gpr.get (regOf i) * BitVec.ofNat 64 sc +
      BitVec.ofNat 64 d = eaS s (some b) i sc d from rfl, checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- `lea r64, [b + i·sc + d]`. -/
theorem s_lea_si (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r i sc d len : Nat} {b : Option Nat}
    (hd : Dec prof.feat code j (FV7z.mk .lea 64 [gr 64 r, .mem (msi b i sc d 0)] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (eaS X b i sc d) ∧ Y.cpu.rflags = rf0 X) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, lea_si (s := X.withMem M) htf (c.dec hK' hin hrip hd),
    hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by cases b <;> rfl, rfl⟩) k'

/-- `sub r64, r64'`. -/
theorem s_sub_rr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 64 [gr 64 r, gr 64 q] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) - X.cpu.gpr.get (regOf q))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => ⟨_, _, sub_rr (s := X.withMem M) (Or.inr rfl) htf
    (c.dec hK' hin hrip hd), hK'.nx rfl rfl rfl, hA', rip_add hrip M len, by simp [rv, BitVec.setWidth_eq]⟩) k'

/-- `cmp byte [b + i·sc + d], imm8`, from a byte of the footprint's data. -/
theorem s_cmp_m8i_si (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {i sc d imm len : Nat} {b : Option Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmp 8 [.mem (msi b i sc d 8), .imm 8 imm] len))
    (hl : Foot F.data (eaS X b i sc d))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (V (eaS X b i sc d)) (BitVec.ofNat 8 imm)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaS (X.withMem M) b i sc d = eaS X b i sc d := by cases b <;> rfl
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) (n := 1) (a := eaS X b i sc d) hK' hA' fun i hi => by
      rw [show i = 0 by omega, addr_add_zero]; exact hl
    have hr := cmp_m8i_si (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) (by rw [he]; exact hrd)
    rw [he, hv] at hr
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl, by
      show subF (rf0 X) (ofBytesLE 8 ((byteAddrs _ 1).map V)) _ = _
      congr 1; simp [byteAddrs, ofBytesLE, Addr.add]⟩) k'

end Seg

end FV7z.Fn
