import FV7z.Lemmas.SysUname
import FV7z.Lemmas.SysLseek
import FV7z.Write.Holds
/-!
# `ioctl (fd, TCGETS, buf)`: the kernel copies a terminal's settings to the process (PLAN.md §M, M1)

What the instruction `syscall` leaves for `ioctl (fd, TCGETS, buf)` on Zellic's model (`sysIoctl`), with `buf`'s 36
bytes writable: a descriptor that is not open (or `O_PATH`) is `EBADF`; the file's answer (`Request.ioctlGet`) is an
error, returned, or 36 bytes (a `struct termios` of the kernel), which are copied to `buf`, `rax` 0. Neither the
address space's mappings nor the process change: the run goes on in the same `Fn.Seg`, the bytes in what it may
store into.

- `tcEv`: the event; `errRet_err`: an error number's answer is an error (`Write.WrErr`).
- `syscall_tcgets`: the instruction, its two kinds of outcome.
- `Seg.s_tcgets`: the step of a run that `Fn.Seg` describes.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Write

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- The event of `ioctl (fd, TCGETS, buf)` from registers `g`, answered `r`, the bytes `bs` copied to `buf`. -/
abbrev tcEv (g : Gprs) (r : BitVec 64) (bs : List Byte) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r, [], bs⟩

/-- An error number's answer `-e` is an error. -/
theorem errRet_err {e : Nat} (h0 : 0 < e) (h1 : e < 4096) : WrErr (errRet e) := by
  have he : e % 2 ^ 64 = e := Nat.mod_eq_of_lt (by omega)
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  unfold WrErr errRet
  first
  | (rw [BitVec.toNat_sub, BitVec.toNat_ofNat, he, h0]; omega)
  | (rw [BitVec.toNat_sub, BitVec.toNat_ofNat, he, h0]; simp; omega)
  | (simp only [bv_toNat]; omega)
  | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.zero_mod,
      Nat.add_zero, Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]; omega)

/-- `syscall` for `ioctl (rdi, TCGETS, rdx)`, `rdx`'s 36 bytes writable and below the end of the user address space:
either an error, nothing copied, or 36 bytes copied to `rdx` and `rax` 0. -/
theorem syscall_tcgets {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 16) (hcmd : arg32 s.cpu.gpr.rsi = 21505)
    (htop : s.cpu.gpr.rdx.toNat + 36 ≤ userPtrMax prof.feat)
    (hw : ∀ x ∈ byteAddrs s.cpu.gpr.rdx 36, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none) {P : StepResult × Nat → Prop}
    (h0 : ∀ (r : BitVec 64) (t' : Nat), WrErr r → P (.running (sysSt s len r) (some (tcEv s.cpu.gpr r [])), t'))
    (h1 : ∀ (bs : List Byte) (t' : Nat), bs.length = 36 →
      P (.running (sysSt (s.withMem (writeBytes s.proc.mm.mem s.cpu.gpr.rdx bs)) len 0)
        (some (tcEv s.cpu.gpr 0 bs)), t')) :
    P ((instruction prof s).runStream o t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (16 ≥ 2 ^ 31) by decide, show ¬ (16 ≥ x32Bit) by decide, show ¬ (16 ≥ nrSyscalls) by decide,
    show niSyscall 16 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show P ((sysIoctl prof (nx s len (sysGpr s len) (rf0 s))).runStream o t)
  have hn1 : ¬ ((21505 : Nat) = TCGETS2) := by decide
  have hn2 : ((21505 : Nat) ≠ TCGETS2 ∧ (21505 : Nat) ≠ TCGETS) = False := by
    apply propext; constructor
    · intro h; exact h.2 rfl
    · intro h; exact h.elim
  unfold sysIoctl
  try simp only [hrsi, hcmd, hn2, ↓reduceIte]
  split
  · exact h0 (errRet EBADF) t (errRet_err (by decide) (by decide))
  · try simp only [hrsi, hcmd, hn2, ↓reduceIte]
    rw [runStream_req_bind]
    split
    · rename_i e _
      exact h0 (errRet e.val) (t + 1) (errRet_err e.property.1 e.property.2)
    · rename_i bs hb _
      have hb' : bs.length = 36 := by simp only [hb, hrsi, hcmd, hn1, ↓reduceIte]
      have hacc : accessOk prof.feat s.cpu.gpr.rdx bs.length = true := by
        have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
        have e : (s.cpu.gpr.rdx + BitVec.ofNat 64 36).toNat = s.cpu.gpr.rdx.toNat + 36 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        simp only [accessOk, hb', e, decide_eq_true_eq, Bool.and_eq_true]
        omega
      show P ((Req.bind (copyOut prof _ _ bs) _).runStream o (t + 1))
      try rw [hrdx]
      rw [copyOut_ok hacc (by rw [hb']; exact hw)]
      show P (sysReturn _ (if true = true then 0 else errRet EFAULT) [] (List.take bs.length bs), t + 1)
      rw [List.take_length]
      exact h1 bs (t + 1) hb'

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Write

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `ioctl (rdi, TCGETS, rdx)`, `rdx`'s 36 bytes in what the run may store into: the run goes on with
`rax` an error and nothing copied, or `rax` 0 and 36 bytes `bs` (the kernel's `struct termios`) at `rdx`; `rcx` and
`r11` as `syscall` sets them. -/
theorem s_tcgets (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 16)
    (hcmd : arg32 X.cpu.gpr.rsi = 21505) (htop : X.cpu.gpr.rdx.toNat + 36 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 36, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (k' : ∀ (r : BitVec 64) (bs : List Byte), (WrErr r ∧ bs = []) ∨ (r = 0 ∧ bs.length = 36) →
      ContG prof F Wl L s₀ o (gev ++ [tcEv X.cpu.gpr r bs]) gP gE (Vst V X.cpu.gpr.rdx bs)
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 r) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    obtain ⟨hw, -, -⟩ := c.store_ok (a := X.cpu.gpr.rdx) (bs := List.replicate 36 0) hK' hA'
      (fun i hi => hst i (by rw [List.length_replicate] at hi; exact hi))
    rw [List.length_replicate] at hw
    refine syscall_tcgets (s := X.withMem M) (o := o) (t := t + 1)
      (P := fun res => ∃ Y t' ev, res = (.running Y ev, t') ∧ GoG prof L o (gev ++ ev.toList) gP gE Y t')
      htf (c.dec hK' hin hrip hd) hnr hcmd htop hw ?_ ?_
    · intro r t' he
      exact ⟨_, _, _, rfl, k' r [] (Or.inl ⟨he, rfl⟩) _ _ (hK'.nx rfl rfl rfl) hA' ⟨rip_add hrip M len, rfl⟩⟩
    · intro bs t' hb
      obtain ⟨-, hK2, hA2⟩ := c.store_ok (a := X.cpu.gpr.rdx) (bs := bs) hK' hA' (fun i hi => hst i (by omega))
      exact ⟨_, _, _, rfl, k' 0 bs (Or.inr ⟨rfl, hb⟩) _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg
