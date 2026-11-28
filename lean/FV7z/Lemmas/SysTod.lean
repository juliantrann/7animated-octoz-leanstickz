import FV7z.Lemmas.SysRead
/-!
# `gettimeofday`: the kernel writes the time (PLAN.md §M, M1)

What the instruction `syscall` leaves for `gettimeofday (tv, tz)` on Zellic's model (`sysGettimeofday`, number 96),
`tv` not 0 with its 16 bytes writable, and `tz` 0 or with its 8 bytes writable: the clock's answer
(`Request.clock 0`) as `struct timeval` (seconds, then microseconds, 8 bytes each) in `tv`, then unless `tz` is 0 the
kernel's time zone (`Request.timezone`, 8 bytes) in `tz`; `rax` 0.

- `putUser_ok`: `put_user` to a range that passes `access_ok` and is all writable writes all the bytes.
- `todMem`, `todV`, `todBs`, `todT`: the memory after, the bytes after, the bytes to the process, the stream's next
  time.
- `syscall_gettimeofday`: the instruction. One or two answers of the stream are used.
- `Seg.s_gettimeofday_re`: the step of a run that `Fn.Seg` describes, the bytes in what the run may store into; the
  run goes on from the state after, its own start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `put_user` to a range that passes `access_ok` and is all writable, in the process's own memory. -/
theorem putUser_ok {a : Addr} {bs : List Byte} (hacc : accessOk prof.feat a bs.length = true)
    (h : Writable prof s a bs.length) :
    putUser prof s a bs = Pure.pure (st s a bs, true) := by
  have hk : kernelWrite prof.feat s a bs = some (s.withMem (writeBytes s.proc.mm.mem a bs)) := by
    unfold kernelWrite
    rw [ite_eq_left]
    simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact h
  unfold putUser
  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, growFor_ok h]
  show (match kernelWrite prof.feat s a bs with
    | some s' => (Pure.pure (s', true) : Req (State × Bool))
    | none => _) = _
  rw [hk]

/-- `struct timeval`'s seconds from the clock's answer at `t`. -/
abbrev tvSec (o : Oracle) (t : Nat) : List Byte := toBytesLE (o t (.clock 0)).sec 8

/-- `struct timeval`'s microseconds from the clock's answer at `t`. -/
abbrev tvUsec (o : Oracle) (t : Nat) : List Byte :=
  toBytesLE (BitVec.ofNat 64 ((o t (.clock 0)).nsec.val / 1000)) 8

/-- The kernel's time zone, the answer at `t`. -/
abbrev tzB (o : Oracle) (t : Nat) : List Byte := toBytesLE (o t .timezone) 8

theorem tvSec_len : (tvSec o t).length = 8 := toBytesLE_length _ _
theorem tvUsec_len : (tvUsec o t).length = 8 := toBytesLE_length _ _
theorem tzB_len : (tzB o t).length = 8 := toBytesLE_length _ _

/-- The memory `m` after `gettimeofday (tv, tz)` with the stream at `t`: `tv` written, then `tz` unless it is 0. -/
def todMem (o : Oracle) (t : Nat) (tv tz : Addr) (m : Memory) : Memory :=
  if tz = 0 then writeBytes (writeBytes m tv (tvSec o t)) (tv.add 8) (tvUsec o t)
  else writeBytes (writeBytes (writeBytes m tv (tvSec o t)) (tv.add 8) (tvUsec o t)) tz (tzB o (t + 1))

/-- The bytes `V` after `gettimeofday (tv, tz)`, as `todMem`. -/
def todV (o : Oracle) (t : Nat) (tv tz : Addr) (V : Addr → Byte) : Addr → Byte :=
  if tz = 0 then Vst (Vst V tv (tvSec o t)) (tv.add 8) (tvUsec o t)
  else Vst (Vst (Vst V tv (tvSec o t)) (tv.add 8) (tvUsec o t)) tz (tzB o (t + 1))

/-- The bytes `gettimeofday (_, tz)` gives the process. -/
def todBs (o : Oracle) (t : Nat) (tz : Addr) : List Byte :=
  if tz = 0 then tvSec o t ++ tvUsec o t else tvSec o t ++ tvUsec o t ++ tzB o (t + 1)

/-- The stream's time after `gettimeofday (_, tz)`. -/
def todT (t : Nat) (tz : Addr) : Nat := if tz = 0 then t + 1 else t + 2

/-- The state after `gettimeofday (rdi, rsi)` from `s`, before `rax`. -/
abbrev todSt (o : Oracle) (t : Nat) (s : State) : State :=
  s.withMem (todMem o t s.cpu.gpr.rdi s.cpu.gpr.rsi s.proc.mm.mem)

/-- What `gettimeofday` needs of `s`: `tv` not 0, its 16 bytes below the end of the user address space and writable
(the second 8 after the first are written), `tz` 0 or its 8 bytes so after `tv`. -/
structure TodOk (prof : Profile) (o : Oracle) (t : Nat) (s : State) : Prop where
  tv0 : s.cpu.gpr.rdi ≠ 0
  tvTop : s.cpu.gpr.rdi.toNat + 16 ≤ userPtrMax prof.feat
  w1 : Writable prof s s.cpu.gpr.rdi 8
  w2 : Writable prof (st s s.cpu.gpr.rdi (tvSec o t)) (s.cpu.gpr.rdi.add 8) 8
  tz : s.cpu.gpr.rsi ≠ 0 → s.cpu.gpr.rsi.toNat + 8 ≤ userPtrMax prof.feat ∧
    Writable prof (st (st s s.cpu.gpr.rdi (tvSec o t)) (s.cpu.gpr.rdi.add 8) (tvUsec o t)) s.cpu.gpr.rsi 8

/-- `gettimeofday (rdi, rsi)` on Zellic's model, as `TodOk` needs: as `todSt` says, `rax` 0. -/
theorem sysGettimeofday_ok (h : TodOk prof o t s) :
    (sysGettimeofday prof s).runStream o t =
      (sysReturn (todSt o t s) 0 [] (todBs o t s.cpu.gpr.rsi), todT t s.cpu.gpr.rsi) := by
  have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
  have htop := h.tvTop
  have e8 : (s.cpu.gpr.rdi.add 8).toNat = s.cpu.gpr.rdi.toNat + 8 := by
    show (s.cpu.gpr.rdi + BitVec.ofNat 64 8).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have p1 : putUser prof s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8) =
      Pure.pure (st s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8), true) :=
    putUser_ok (by rw [toBytesLE_length]; exact accessOk_le (by omega)) (by rw [toBytesLE_length]; exact h.w1)
  have p2 : putUser prof (st s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8)) (s.cpu.gpr.rdi.add 8)
      (toBytesLE (BitVec.ofNat 64 ((o t (.clock 0)).nsec.val / 1000)) 8) =
      Pure.pure (st (st s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8)) (s.cpu.gpr.rdi.add 8)
        (toBytesLE (BitVec.ofNat 64 ((o t (.clock 0)).nsec.val / 1000)) 8), true) :=
    putUser_ok (by rw [toBytesLE_length]; exact accessOk_le (by omega)) (by rw [toBytesLE_length]; exact h.w2)
  unfold sysGettimeofday todSt todMem todBs todT
  simp only [h.tv0, ↓reduceIte]
  rw [req_ask_run]
  simp only [p1, req_pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [p2, req_pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, eq_self_iff_true]
  by_cases hz : s.cpu.gpr.rsi = 0
  · simp only [if_pos hz]
    rfl
  · obtain ⟨ht, w3⟩ := h.tz hz
    have p3 : copyOut prof (st (st s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8)) (s.cpu.gpr.rdi.add 8)
        (toBytesLE (BitVec.ofNat 64 ((o t (.clock 0)).nsec.val / 1000)) 8)) s.cpu.gpr.rsi
        (toBytesLE (o (t + 1) .timezone) 8) =
        Pure.pure (st (st (st s s.cpu.gpr.rdi (toBytesLE (o t (.clock 0)).sec 8)) (s.cpu.gpr.rdi.add 8)
          (toBytesLE (BitVec.ofNat 64 ((o t (.clock 0)).nsec.val / 1000)) 8)) s.cpu.gpr.rsi
          (toBytesLE (o (t + 1) .timezone) 8), (toBytesLE (o (t + 1) .timezone) 8).length, true) :=
      copyOut_ok (by rw [toBytesLE_length]; exact accessOk_le ht) (by rw [toBytesLE_length]; exact w3)
    simp only [if_neg hz]
    rw [req_ask_run]
    simp only [p3, req_pure_bind, ↓reduceIte, eq_self_iff_true]
    rfl

/-- `syscall` for `gettimeofday (rdi, rsi)`, as `TodOk` needs: `todMem`'s writes, `rax` 0. -/
theorem syscall_gettimeofday {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 96) (h : TodOk prof o t (nx s len (sysGpr s len) (rf0 s))) :
    (instruction prof s).runStream o t =
      (sysReturn (todSt o t (nx s len (sysGpr s len) (rf0 s))) 0 [] (todBs o t s.cpu.gpr.rsi),
        todT t s.cpu.gpr.rsi) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (96 ≥ 2 ^ 31) by decide, show ¬ (96 ≥ x32Bit) by decide,
    show ¬ (96 ≥ nrSyscalls) by decide, show niSyscall 96 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysGettimeofday prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  exact sysGettimeofday_ok h

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- The state after the `syscall` of `gettimeofday` from `S`, `len` its length, the stream at `t`. -/
abbrev todY (S : State) (len : Nat) (o : Oracle) (t : Nat) : State :=
  (todSt o t (nx S len (sysGpr S len) (rf0 S))).setRax 0

/-- The event of `gettimeofday` from registers `g`, the stream at `t`. -/
abbrev todEv (g : Gprs) (o : Oracle) (t : Nat) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], 0, [], todBs o t g.rsi⟩

/-- `syscall` for `gettimeofday (rdi, rsi)` (a start with no `rseq` area), `rdi` not 0, its 16 bytes below the end of
the user address space and in what the run may store into, `rsi` 0 or its 8 bytes so: the run goes on from the state
after, its own start, with `todV`'s bytes, `rax` 0, the stream of answers at some `t₁` before the call. -/
theorem s_gettimeofday_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 96)
    (htv : X.cpu.gpr.rdi ≠ 0) (htop : X.cpu.gpr.rdi.toNat + 16 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 16, Foot Wl (X.cpu.gpr.rdi.add i))
    (hz : X.cpu.gpr.rsi ≠ 0 → X.cpu.gpr.rsi.toNat + 8 ≤ userPtrMax prof.feat ∧
      ∀ i < 8, Foot Wl (X.cpu.gpr.rsi.add i))
    (k' : ∀ (M : Memory) (t₁ : Nat), KeptW Wl s₀ (X.withMem M) → Agree F M V →
      Seg prof F Wl L (todY (X.withMem M) len o t₁) o →
      Agree F (todY (X.withMem M) len o t₁).proc.mm.mem (todV o t₁ X.cpu.gpr.rdi X.cpu.gpr.rsi V) →
      GoG prof L o (gev ++ [todEv X.cpu.gpr o t₁]) gP gE (todY (X.withMem M) len o t₁) (todT t₁ X.cpu.gpr.rsi)) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    obtain ⟨hw1, hK1, hA1⟩ := c.store_ok (a := X.cpu.gpr.rdi) (bs := tvSec o (t + 1)) hK' hA'
      (fun i hi => hst i (show i < 16 by rw [tvSec_len] at hi; omega))
    obtain ⟨hw2, hK2, hA2⟩ := c.store_ok (a := Addr.add X.cpu.gpr.rdi 8) (bs := tvUsec o (t + 1)) hK1 hA1
      (fun i hi => by
        rw [tvUsec_len] at hi
        rw [addr_add_add]
        exact hst (8 + i) (by omega))
    rw [tvSec_len] at hw1
    rw [tvUsec_len] at hw2
    have hT : TodOk prof o (t + 1) (nx (X.withMem M) len (sysGpr (X.withMem M) len) (rf0 (X.withMem M))) :=
      { tv0 := htv, tvTop := htop, w1 := hw1, w2 := hw2
        tz := fun h0 => by
          obtain ⟨ht, hf⟩ := hz h0
          obtain ⟨hw3, -, -⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := tzB o (t + 1 + 1)) hK2 hA2
            (fun i hi => hf i (show i < 8 by rw [tzB_len] at hi; exact hi))
          rw [tzB_len] at hw3
          exact ⟨ht, hw3⟩ }
    have hKA : KeptW Wl s₀ ((X.withMem M).withMem (todMem o (t + 1) X.cpu.gpr.rdi X.cpu.gpr.rsi M)) ∧
        Agree F (todMem o (t + 1) X.cpu.gpr.rdi X.cpu.gpr.rsi M) (todV o (t + 1) X.cpu.gpr.rdi X.cpu.gpr.rsi V) := by
      by_cases h0 : X.cpu.gpr.rsi = 0
      · simp only [todMem, todV, if_pos h0]
        exact ⟨hK2, hA2⟩
      · obtain ⟨-, hf⟩ := hz h0
        obtain ⟨-, hK3, hA3⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := tzB o (t + 1 + 1)) hK2 hA2
          (fun i hi => hf i (show i < 8 by rw [tzB_len] at hi; exact hi))
        simp only [todMem, todV, if_neg h0]
        exact ⟨hK3, hA3⟩
    exact ⟨_, _, _, syscall_gettimeofday (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hT,
      k' M _ hK' hA' (c.reroot hKA.1 rfl rfl rfl rfl rfl htf hac hrs) hKA.2⟩

end FV7z.Fn.Seg
