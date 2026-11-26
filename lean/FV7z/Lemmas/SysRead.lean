import FV7z.Start.TaskSeg
import FV7z.Lemmas.CallFn
import FV7z.Lemmas.SysLink
/-!
# `read`: the kernel copies a file's bytes to the process (PLAN.md §M, M1)

`read (fd, buf, count)` on Zellic's model (`sysRead`) with `buf`'s `count` bytes writable: the bytes the kernel delivers
(a file's pages from the open file's position, or the environment's answer for another file) are in `buf`, their
number or an error in `rax`, and the open file's position moves by them. The position is part of the process, which
`KeptW` keeps, so the run goes on from the state after as a new start (`Seg.reroot`), as after `close`
(`Lemmas/SysClose.lean`).

- `RdOut`, `readRes`: what `read` from a state delivers, returns, leaves as the open files' positions, and where the
  stream of answers is after it; `readRes_len`: it delivers at most `count` bytes.
- `rdSt`: the state after it, the bytes in `buf`; `rdEv`: its event.
- `writable_le`, `deliverRead_ok`, `sysRead_ok`: Zellic's `read` from a state with `buf`'s bytes writable.
- `syscall_read`: what the instruction `syscall` leaves for `read (rdi, rsi, rdx)`.
- `Seg.s_read_re`: the step of a run that `Fn.Seg` describes, `buf`'s bytes in what the run may store into; the run
  goes on from the state after as a new start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- What a `read` delivers (`bs`), returns (`ret`), leaves as the open files' positions (`pos`), and where the stream
of answers is after it (`t'`). -/
structure RdOut where
  bs : List Byte
  ret : BitVec 64
  pos : OpenFile → FilePos
  t' : Nat

/-- What `read (rdi, rsi, rdx)` from `s` does, the stream of answers at `t` (as `sysRead`): `EBADF` for a descriptor
not open or not open for reading, `EFAULT` for a buffer that fails `access_ok`; for a file with pages, `EINVAL` for a
position and count that reach `2 ^ 63`, else the file's bytes from the position up to its end (`Request.readFail`: up
to a failure, or its error if there are none), the position moved by them; for another file, the environment's bytes
or error (`Request.read`). -/
def readRes (prof : Profile) (o : Oracle) (t : Nat) (s : State) : RdOut :=
  let count := s.cpu.gpr.rdx.toNat
  let P := s.proc.opens.pos
  match s.proc.files.desc (s.cpu.gpr.rdi.toNat % 2 ^ 32) with
  | none => ⟨[], errRet EBADF, P, t⟩
  | some f =>
    if !f.readable then ⟨[], errRet EBADF, P, t⟩
    else if !accessOk prof.feat s.cpu.gpr.rsi count then ⟨[], errRet EFAULT, P, t⟩
    else match f.map with
    | .pages id =>
      let p := P f
      if 2 ^ 63 ≤ p.offset + count then ⟨[], errRet EINVAL, P, t⟩ else
      let fs := s.proc.mm.mem.files
      let want := min (min count maxRwCount) (fs.size id - p.offset)
      let dl (k : Nat) : RdOut := ⟨fs.bytes id p.offset k, BitVec.ofNat 64 (fs.bytes id p.offset k).length,
        fun g => if g = f then { p with offset := p.offset + k } else P g, t + 1⟩
      match o t (.readFail f.id want) with
      | none => dl want
      | some (e, k) => if k.val = 0 then ⟨[], errRet e.val, P, t + 1⟩ else dl k.val
    | _ =>
      match o t (.read f.id (min count maxRwCount)) with
      | .error e => ⟨[], errRet e.val, P, t + 1⟩
      | .data bs _ => ⟨bs, BitVec.ofNat 64 bs.length, P, t + 1⟩

/-- The state after `read` from `s` with result `r`: the bytes in `buf` (`rsi`), the open files' positions. -/
def rdSt (s : State) (r : RdOut) : State := { st s s.cpu.gpr.rsi r.bs with proc.opens.pos := r.pos }

/-- The event of `read` from registers `g` with result `r`: the bytes go to the process. -/
abbrev rdEv (g : Gprs) (r : RdOut) : Event := ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r.ret, [], r.bs⟩

/-- `read` delivers at most `count` bytes. -/
theorem readRes_len : (readRes prof o t s).bs.length ≤ s.cpu.gpr.rdx.toNat := by
  unfold readRes
  dsimp only
  repeat' split
  all_goals (try dsimp only)
  all_goals first
    | exact Nat.zero_le _
    | omega
    | (simp only [Files.bytes, List.length_map, List.length_range]; omega)
    | (simp only [Files.bytes, List.length_map, List.length_range]; have := Fin.isLt ‹Fin _›; omega)

/-- Fewer bytes from the same place are writable too. -/
theorem writable_le {a : Addr} {n k : Nat} (h : Writable prof s a n) (hk : k ≤ n) : Writable prof s a k :=
  fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact h _ (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)

/-- Bytes delivered into writable bytes: they are written, their number returned. -/
theorem deliverRead_ok {buf : Addr} {bs : List Byte} {done : State → State} (hw : Writable prof s buf bs.length) :
    deliverRead prof s buf bs done = Pure.pure (sysReturn (done (st s buf bs)) (BitVec.ofNat 64 bs.length) [] bs) := by
  have hk : kernelWrite prof.feat s buf bs = some (s.withMem (writeBytes s.proc.mm.mem buf bs)) := by
    unfold kernelWrite
    rw [ite_eq_left]
    simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact hw
  unfold deliverRead
  rw [growFor_ok hw]
  simp only [req_pure_bind, hk]

/-- One request, then the rest from its answer. -/
theorem req_ask_run {α : Type} {r : Request} {f : r.Answer → Req α} :
    (Req.request r >>= f).runStream o t = (f (o t r)).runStream o (t + 1) := rfl

/-- `read (rdi, rsi, rdx)` on Zellic's model, `rsi`'s `rdx` bytes writable: as `readRes` says. -/
theorem sysRead_ok (hw : Writable prof s s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat) :
    (sysRead prof s).runStream o t =
      (sysReturn (rdSt s (readRes prof o t s)) (readRes prof o t s).ret [] (readRes prof o t s).bs,
        (readRes prof o t s).t') := by
  have D : ∀ (bs : List Byte) (done : State → State) (t₁ : Nat), bs.length ≤ s.cpu.gpr.rdx.toNat →
      (deliverRead prof s s.cpu.gpr.rsi bs done).runStream o t₁ =
        (sysReturn (done (st s s.cpu.gpr.rsi bs)) (BitVec.ofNat 64 bs.length) [] bs, t₁) := by
    intro bs done t₁ hl
    rw [deliverRead_ok (writable_le hw hl)]
    rfl
  unfold sysRead readRes
  try dsimp only
  split
  · rfl
  · cases hr : (‹OpenFile›).readable
    · rfl
    · cases ha : accessOk prof.feat s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hm : (‹OpenFile›).map with
        | pages id =>
          try dsimp only
          unfold readPages readPagesAt
          try dsimp only
          split
          · rfl
          · rw [req_ask_run]
            try dsimp only
            split
            · rw [D]
              · rfl
              · simp only [Files.bytes, List.length_map, List.length_range]
                omega
            · split
              · rfl
              · rw [D]
                · rfl
                · simp only [Files.bytes, List.length_map, List.length_range]
                  have := Fin.isLt ‹Fin _›
                  omega
        | none | path | other =>
          try dsimp only
          rw [req_ask_run]
          try dsimp only
          split
          · rfl
          · rw [D]
            · rfl
            · omega

/-- `syscall` for `read (rdi, rsi, rdx)`, `rsi`'s `rdx` bytes writable: `readRes`'s bytes in them, its answer in
`rax`, the open files' positions its. -/
theorem syscall_read {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 0) (hw : Writable prof s s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat) :
    (instruction prof s).runStream o t =
      (.running (sysSt (rdSt s (readRes prof o t s)) len (readRes prof o t s).ret)
        (some (rdEv s.cpu.gpr (readRes prof o t s))), (readRes prof o t s).t') := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (0 ≥ 2 ^ 31) by decide, show ¬ (0 ≥ x32Bit) by decide, show ¬ (0 ≥ nrSyscalls) by decide,
    show niSyscall 0 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysRead prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  rw [sysRead_ok (s := nx s len (sysGpr s len) (rf0 s)) hw]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `read (rdi, rsi, rdx)` (a start with no `rseq` area), `rsi`'s `rdx` bytes in what the run may store
into: the run goes on from the state after, its own start, with `readRes`'s bytes in them, its answer in `rax`, the
stream of answers at some `t₁` before the call. -/
theorem s_read_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 0)
    (hst : ∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (X.cpu.gpr.rsi.add i))
    (k' : ∀ (M : Memory) (t₁ t' : Nat), KeptW Wl s₀ (X.withMem M) → Agree F M V →
      Seg prof F Wl L (sysSt (rdSt (X.withMem M) (readRes prof o t₁ (X.withMem M))) len
        (readRes prof o t₁ (X.withMem M)).ret) o →
      Agree F (rdSt (X.withMem M) (readRes prof o t₁ (X.withMem M))).proc.mm.mem
        (Vst V X.cpu.gpr.rsi (readRes prof o t₁ (X.withMem M)).bs) →
      GoG prof L o (gev ++ [rdEv X.cpu.gpr (readRes prof o t₁ (X.withMem M))]) gP gE
        (sysSt (rdSt (X.withMem M) (readRes prof o t₁ (X.withMem M))) len (readRes prof o t₁ (X.withMem M)).ret)
        t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    obtain ⟨hw, -, -⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := List.replicate X.cpu.gpr.rdx.toNat 0) hK' hA'
      (fun i hi => hst i (by rw [List.length_replicate] at hi; exact hi))
    rw [List.length_replicate] at hw
    have hl : (readRes prof o (t + 1) (X.withMem M)).bs.length ≤ X.cpu.gpr.rdx.toNat := readRes_len
    obtain ⟨-, hK2, hA2⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := (readRes prof o (t + 1) (X.withMem M)).bs) hK'
      hA' (fun i hi => hst i (by omega))
    exact ⟨_, _, _, syscall_read (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hw,
      k' M _ _ hK' hA' (c.reroot hK2 rfl rfl rfl rfl rfl htf hac hrs) hA2⟩

end FV7z.Fn.Seg
