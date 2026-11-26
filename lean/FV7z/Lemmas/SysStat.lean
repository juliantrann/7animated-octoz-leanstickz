import FV7z.Lemmas.SysRead
/-!
# `fstat`: the kernel copies a file's status to the process (PLAN.md §M, M1)

`fstat (fd, buf)` on Zellic's model (`sysFstat`) with `buf`'s 144 bytes writable and below the end of the user address
space: `EBADF` for a descriptor not open, else the environment's answer to `Request.stat`: an error, or a status whose
`struct stat` (`Stat.bytes`, `statOf`) goes to `buf`, 0 in `rax`. Only the process's memory changes, so the run goes
on with the same start, as after `uname` (`Lemmas/SysUname.lean`).

- `FsOut`, `fstatRes`: what `fstat` from a state delivers, returns, and where the stream of answers is after it;
  `FsOk`, `fstatRes_ok`: 144 bytes and 0, or no bytes and `-e` for an error `e` from 1 to 4095.
- `fsEv`: its event.
- `sysFstat_ok`: Zellic's `fstat` from a state with `buf`'s bytes writable.
- `syscall_fstat`: what the instruction `syscall` leaves for `fstat (rdi, rsi)`.
- `Seg.s_fstat`: the step of a run that `Fn.Seg` describes, `buf`'s bytes in what the run may store into.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- What an `fstat` delivers (`bs`), returns (`ret`), and where the stream of answers is after it (`t'`). -/
structure FsOut where
  bs : List Byte
  ret : BitVec 64
  t' : Nat

/-- What `fstat (rdi, rsi)` from `s` does, the stream of answers at `t` (as `sysFstat`): `EBADF` for a descriptor not
open; else the environment's error, or the status `statOf` makes of its answer, as `struct stat`, and 0. -/
def fstatRes (o : Oracle) (t : Nat) (s : State) : FsOut :=
  match s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => ⟨[], errRet EBADF, t⟩
  | some f =>
    match o t (.stat f.id) with
    | .error e => ⟨[], errRet e.val, t + 1⟩
    | .ok x => ⟨(statOf s.proc.mm.mem.files f x).bytes, 0, t + 1⟩

/-- A `struct stat` is 144 bytes. -/
theorem Stat.bytes_length (x : Stat) : x.bytes.length = 144 := by
  simp only [Stat.bytes, List.length_append, toBytesLE_length]

/-- What an `fstat` can deliver and return: a status of 144 bytes and 0, or no bytes and `-e` for an error `e` from
1 to 4095. -/
def FsOk (bs : List Byte) (ret : BitVec 64) : Prop :=
  (ret = 0 ∧ bs.length = 144) ∨ (bs = [] ∧ ∃ e : Nat, 0 < e ∧ e < 4096 ∧ ret = errRet e)

theorem fstatRes_ok : FsOk (fstatRes o t s).bs (fstatRes o t s).ret := by
  unfold fstatRes FsOk
  cases s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => exact Or.inr ⟨rfl, EBADF, by decide, by decide, rfl⟩
  | some f =>
    dsimp only
    cases o t (.stat f.id) with
    | error e => exact Or.inr ⟨rfl, e.val, e.property.1, e.property.2, rfl⟩
    | ok x => exact Or.inl ⟨rfl, Stat.bytes_length (statOf s.proc.mm.mem.files f x)⟩

/-- An `fstat` delivers at most 144 bytes. -/
theorem FsOk.len {bs : List Byte} {ret : BitVec 64} (h : FsOk bs ret) : bs.length ≤ 144 := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · rw [h]
    exact Nat.zero_le _

/-- The event of `fstat` from registers `g` with result `r`: the bytes go to the process. -/
abbrev fsEv (g : Gprs) (r : FsOut) : Event := ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r.ret, [], r.bs⟩

/-- `fstat (rdi, rsi)` on Zellic's model, `rsi`'s 144 bytes writable and below the end of the user address space: as
`fstatRes` says. -/
theorem sysFstat_ok (htop : s.cpu.gpr.rsi.toNat + 144 ≤ userPtrMax prof.feat)
    (hw : Writable prof s s.cpu.gpr.rsi 144) :
    (sysFstat prof s).runStream o t =
      (sysReturn (st s s.cpu.gpr.rsi (fstatRes o t s).bs) (fstatRes o t s).ret [] (fstatRes o t s).bs,
        (fstatRes o t s).t') := by
  unfold sysFstat fstatRes
  try dsimp only
  cases s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => rfl
  | some f =>
    try dsimp only
    rw [req_ask_run]
    try dsimp only
    cases o t (Request.stat f.id) with
    | error e => rfl
    | ok x =>
      try dsimp only
      have hl : (statOf s.proc.mm.mem.files f x).bytes.length = 144 := Stat.bytes_length _
      simp only [copyOut_ok (accessOk_le (by rw [hl]; exact htop)) (by rw [hl]; exact hw), req_pure_bind,
        ↓reduceIte, List.take_length]
      rfl

/-- `syscall` for `fstat (rdi, rsi)`, `rsi`'s 144 bytes writable and below the end of the user address space:
`fstatRes`'s bytes in them, its answer in `rax`. -/
theorem syscall_fstat {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 5) (htop : s.cpu.gpr.rsi.toNat + 144 ≤ userPtrMax prof.feat)
    (hw : Writable prof s s.cpu.gpr.rsi 144) :
    (instruction prof s).runStream o t =
      (.running (sysSt (st s s.cpu.gpr.rsi (fstatRes o t s).bs) len (fstatRes o t s).ret)
        (some (fsEv s.cpu.gpr (fstatRes o t s))), (fstatRes o t s).t') := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (5 ≥ 2 ^ 31) by decide, show ¬ (5 ≥ x32Bit) by decide, show ¬ (5 ≥ nrSyscalls) by decide,
    show niSyscall 5 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysFstat prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  rw [sysFstat_ok (s := nx s len (sysGpr s len) (rf0 s)) htop hw]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `fstat (rdi, rsi)`, `rsi`'s 144 bytes below the end of the user address space and in what the run
may store into: the run goes on with some result `r` (`FsOk`), its bytes in them, its answer in `rax`, `rcx` and `r11`
as `syscall` sets them. -/
theorem s_fstat (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 5)
    (htop : X.cpu.gpr.rsi.toNat + 144 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 144, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (k' : ∀ r : FsOut, FsOk r.bs r.ret → ContG prof F Wl L s₀ o (gev ++ [fsEv X.cpu.gpr r]) gP gE
      (Vst V X.cpu.gpr.rsi r.bs) fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 r.ret) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    obtain ⟨hw, -, -⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := List.replicate 144 0) hK' hA'
      (fun i hi => hst i (by rw [List.length_replicate] at hi; exact hi))
    rw [List.length_replicate] at hw
    have hok : FsOk (fstatRes o (t + 1) (X.withMem M)).bs (fstatRes o (t + 1) (X.withMem M)).ret := fstatRes_ok
    have hl := hok.len
    obtain ⟨-, hK2, hA2⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := (fstatRes o (t + 1) (X.withMem M)).bs) hK' hA'
      (fun i hi => hst i (by omega))
    exact ⟨_, _, _, syscall_fstat (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr htop hw,
      k' _ hok _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg

namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- What `stat (path, buf)` returns and writes, from the file system's answer: 0 and the status as `struct stat`, or
the error and nothing. -/
def statRes : StatResult → BitVec 64 × List Byte
  | .error e => (errRet e.val, [])
  | .ok x => (0, x.bytes)

theorem statRes_ok (r : StatResult) : FsOk (statRes r).2 (statRes r).1 := by
  cases r with
  | error e => exact Or.inr ⟨rfl, e.val, e.property.1, e.property.2, rfl⟩
  | ok x => exact Or.inl ⟨rfl, Stat.bytes_length x⟩

/-- `stat (path, buf)`: the path name `p` at `path` (`m` nonzero bytes then a NUL, `0 < m`, the word it ends in
readable, below the end of the user address space), `buf`'s 144 bytes writable and below the end of the user address
space: what the file system answers (`statRes`) is returned and written at `buf`. -/
theorem syscall_stat {len m : Nat} {p : List Byte} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 4) (hm : m < pathMax)
    (htop : s.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hr : Readable prof s s.cpu.gpr.rdi (8 * (m / 8 + 1)))
    (hnz : ∀ i < m, s.proc.mm.mem.readByte (s.cpu.gpr.rdi.add i) ≠ 0)
    (hz : s.proc.mm.mem.readByte (s.cpu.gpr.rdi.add m) = 0)
    (hp : readBytes s.proc.mm.mem s.cpu.gpr.rdi m = p) (hp0 : p ≠ [])
    (htw : s.cpu.gpr.rsi.toNat + 144 ≤ userPtrMax prof.feat) (hw : Writable prof s s.cpu.gpr.rsi 144) :
    (instruction prof s).runStream o t =
      (.running (sysSt (st s s.cpu.gpr.rsi (statRes (o t (.statPath none p true))).2)
          len (statRes (o t (.statPath none p true))).1)
        (some (linkEv s.cpu.gpr p (statRes (o t (.statPath none p true))).1
          (statRes (o t (.statPath none p true))).2)), t + 1) := by
  obtain ⟨b, q, rfl⟩ : ∃ b q, p = b :: q := by
    cases p with
    | nil => exact absurd rfl hp0
    | cons b q => exact ⟨b, q, rfl⟩
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (4 ≥ 2 ^ 31) by decide, show ¬ (4 ≥ x32Bit) by decide, show ¬ (4 ≥ nrSyscalls) by decide,
    show niSyscall 4 = false by decide, ↓reduceIte, Bool.false_eq_true]
  have hu := userPath_ok (s := nx s len (sysGpr s len) (rf0 s)) (a := s.cpu.gpr.rdi) hm htop hr hnz hz
  rw [show readBytes (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem s.cpu.gpr.rdi m = b :: q from hp] at hu
  unfold sysStat
  simp only [hrdi, hrsi, hu, req_pure_bind]
  show (Req.bind (Req.request (.statPath none (b :: q) true)) _).runStream o t = _
  rw [Req.runStream_bind,
    show (Req.request (Request.statPath none (b :: q) true)).runStream o t =
      (o t (.statPath none (b :: q) true), t + 1) from rfl]
  dsimp only
  generalize o t (.statPath none (b :: q) true) = r
  cases r with
  | error e => rfl
  | ok x =>
    have hl : x.bytes.length = 144 := Stat.bytes_length x
    simp only [copyOut_ok (s := nx s len (sysGpr s len) (rf0 s)) (accessOk_le (by rw [hl]; exact htw))
      (by rw [hl]; exact hw), req_pure_bind, ↓reduceIte, List.take_length, statRes]
    rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `stat (path, buf)`: the path name `p` at `path` (`m` nonzero bytes then a NUL, `0 < m`, the word it
ends in readable), `buf`'s 144 bytes below the end of the user address space and in what the run may store into: what
the file system answers, `r`, is returned and written at `buf` (`statRes`, `FsOk`); `rcx` and `r11` as `syscall` sets
them. -/
theorem s_stat (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len m : Nat} {p : List Byte}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 4)
    (hm : m < pathMax) (htop : X.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hl : ∀ i < 8 * (m / 8 + 1), Foot F.data (X.cpu.gpr.rdi.add i))
    (hnz : ∀ i < m, V (X.cpu.gpr.rdi.add i) ≠ 0) (hz : V (X.cpu.gpr.rdi.add m) = 0)
    (hp : (byteAddrs X.cpu.gpr.rdi m).map V = p) (hp0 : p ≠ [])
    (htw : X.cpu.gpr.rsi.toNat + 144 ≤ userPtrMax prof.feat) (hst : ∀ i < 144, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (k' : ∀ r : StatResult, FsOk (statRes r).2 (statRes r).1 →
      ContG prof F Wl L s₀ o (gev ++ [linkEv X.cpu.gpr p (statRes r).1 (statRes r).2]) gP gE
        (Vst V X.cpu.gpr.rsi (statRes r).2)
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 (statRes r).1) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hA' := c.agreeK hK hA hM
    have hrd := (c.load_ok (X := X.withMem M) hK' hA' hl).1
    have hv := (c.load_ok (X := X.withMem M) hK' hA' (n := m) fun i hi => hl i (by omega)).2
    have hw := (c.store_ok (X := X.withMem M) (a := X.cpu.gpr.rsi) (bs := List.replicate 144 0) hK' hA'
      (by rw [List.length_replicate]; exact hst)).1
    rw [List.length_replicate] at hw
    have hok := statRes_ok (o (t + 1) (.statPath none p true))
    have hlen := hok.len
    obtain ⟨-, hK2, hA2⟩ := c.store_ok (X := X.withMem M) (a := X.cpu.gpr.rsi)
      (bs := (statRes (o (t + 1) (.statPath none p true))).2) hK' hA' fun i hi => hst i (by omega)
    have hnz' : ∀ i < m, (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rdi.add i) ≠ 0 := fun i hi => by
      show M.readByte _ ≠ 0
      rw [hA' _ (hl i (by omega))]
      exact hnz i hi
    have hz' : (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rdi.add m) = 0 := by
      show M.readByte _ = 0
      rw [hA' _ (hl m (by omega))]
      exact hz
    exact ⟨_, _, _, syscall_stat (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hm htop hrd hnz' hz'
      (hv.trans hp) hp0 htw hw,
      k' _ hok _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg
