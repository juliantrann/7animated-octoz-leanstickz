import FV7z.Lemmas.SysMm
import FV7z.Lemmas.FnSteps
/-!
# `uname`: the kernel copies bytes to the process (PLAN.md G3, startup)

What the instruction `syscall` leaves for `uname (buf)` on Zellic's model, with `buf`'s 390 bytes writable: the
kernel's answer (`Request.uname`, a `struct new_utsname`, `UtsnameOk`) is in them, `rax` is 0.

- `firstRejected_none`, `growFor_ok`: the kernel's access to bytes it can all make grows no stack.
- `copyOut_ok`: `copy_to_user` to a range that passes `access_ok` and is all writable writes all the bytes.
- `syscall_uname`: the instruction. One answer of the stream is used.
- `Seg.s_uname`: the step of a run that `Fn.Seg` describes, the bytes in what the run may store into.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem firstRejected_none {ok : Nat → Bool} {n : Nat} (start : Nat)
    (h : ∀ i, start ≤ i → i < start + n → ok i = true) :
    firstRejected ok start n = none := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [firstRejected, h start (Nat.le_refl _) (by omega)]
    exact ih (start + 1) fun i h1 h2 => h i (by omega) (by omega)

/-- The kernel's access to bytes it can all make grows no stack. -/
theorem growFor_ok {acc : Access} {a : Addr} {n : Nat}
    (h : ∀ x ∈ byteAddrs a n,
      x.canonical prof.feat.la57 = true ∧ s.proc.mm.mem.check prof.feat s.cpu.pkru acc x = none) :
    growFor prof s acc a n = Pure.pure s := by
  have hg : growthFault prof.feat s.proc.mm.mem (userAccessible prof.feat s acc) a n = none := by
    unfold growthFault
    rw [firstRejected_none 0 fun i _ hi => ?_]
    · rfl
    · obtain ⟨h1, h2⟩ := h (a.add i) (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)
      simp only [userAccessible, h1, h2, Option.isNone_none, Bool.and_self]
  unfold growFor growFor.go
  simp only [hg]

/-- `copy_to_user` to a range that passes `access_ok` and is all writable, in the process's own memory. -/
theorem copyOut_ok {a : Addr} {bs : List Byte} (hacc : accessOk prof.feat a bs.length = true)
    (h : ∀ x ∈ byteAddrs a bs.length, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none) :
    copyOut prof s a bs = Pure.pure (s.withMem (writeBytes s.proc.mm.mem a bs), bs.length, true) := by
  have hk : kernelWrite prof.feat s a bs = some (s.withMem (writeBytes s.proc.mm.mem a bs)) := by
    unfold kernelWrite
    rw [ite_eq_left]
    simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact h
  unfold copyOut
  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, growFor_ok h]
  show (match kernelWrite prof.feat s a bs with
    | some s' => (Pure.pure (s', bs.length, true) : Req (State × Nat × Bool))
    | none => _) = _
  rw [hk]

/-- The event of `uname (buf)` from registers `g`, answered with the bytes `bs`. -/
abbrev unameEv (g : Gprs) (bs : List Byte) : Event := ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], 0, [], bs⟩

/-- `uname (buf)` with `buf`'s bytes writable and below the end of the user address space: the kernel's answer is
in them, `rax` is 0. -/
theorem syscall_uname {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 63) (htop : s.cpu.gpr.rdi.toNat + 390 ≤ userPtrMax prof.feat)
    (hw : ∀ x ∈ byteAddrs s.cpu.gpr.rdi 390, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.withMem (writeBytes s.proc.mm.mem s.cpu.gpr.rdi (o t .uname).val)) len 0)
        (some (unameEv s.cpu.gpr (o t .uname).val)), t + 1) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hlen : (o t .uname).val.length = 390 := (o t .uname).property.1
  have hacc : accessOk prof.feat s.cpu.gpr.rdi (o t .uname).val.length = true := by
    have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
    have e : (s.cpu.gpr.rdi + BitVec.ofNat 64 390).toNat = s.cpu.gpr.rdi.toNat + 390 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [accessOk, hlen, e, decide_eq_true_eq, Bool.and_eq_true]
    omega
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (63 ≥ 2 ^ 31) by decide, show ¬ (63 ≥ x32Bit) by decide, show ¬ (63 ≥ nrSyscalls) by decide,
    show niSyscall 63 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysUname
  show (Req.bind (Req.request .uname) _).runStream o t = _
  rw [Req.runStream_bind]
  show (Req.bind (copyOut prof _ _ (o t .uname).val) _).runStream o (t + 1) = _
  rw [hrdi, copyOut_ok hacc (by rw [hlen]; exact hw)]
  show (sysReturn _ 0 [] (List.take (o t .uname).val.length (o t .uname).val), t + 1) = _
  rw [List.take_length]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `uname (buf)`, `buf`'s 390 bytes in what the run may store into: they are the kernel's answer `u`,
a `struct new_utsname`; `rax` is 0, `rcx` and `r11` as `syscall` sets them. What all the stream's answers to `uname`
have (`P`), `u` has. -/
theorem s_uname (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 63)
    (htop : X.cpu.gpr.rdi.toNat + 390 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 390, Foot Wl (Addr.add X.cpu.gpr.rdi i)) {P : List Byte → Prop} (hP : ∀ t, P (o t .uname).val)
    (k' : ∀ u : List Byte, UtsnameOk u → P u → ContG prof F Wl L s₀ o (gev ++ [unameEv X.cpu.gpr u]) gP gE
      (Vst V X.cpu.gpr.rdi u) fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 0) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hlen : (o (t + 1) .uname).val.length = 390 := (o (t + 1) .uname).property.1
    obtain ⟨hw, hK2, hA2⟩ := c.store_ok (a := X.cpu.gpr.rdi) (bs := (o (t + 1) .uname).val) hK'
      (c.agreeK hK hA hM) (by rw [hlen]; exact hst)
    rw [hlen] at hw
    exact ⟨_, _, _, syscall_uname (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr htop hw,
      k' _ (o (t + 1) .uname).property (hP (t + 1)) _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg
