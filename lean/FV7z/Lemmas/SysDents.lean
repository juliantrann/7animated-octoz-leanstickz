import FV7z.Lemmas.SysRead
import FV7z.Lemmas.CopyP
/-!
# `getdents64`: the kernel writes a directory's entries to the process (PLAN.md §M, M1)

`getdents64 (fd, dirp, count)` on Zellic's model (`sysGetdents64`) with `dirp`'s `count` bytes writable: the entries
the directory gives (`Request.dirents`) are written one after the other into the buffer (`direntRuns`: each entry's
`struct linux_dirent64` at the end of the previous one, its padding not written), their size or an error in `rax`.
The directory's position is the file's own (no change to the process but the buffer), so the run goes on from the
state after as a new start (`Seg.reroot`), as after `read` (`Lemmas/SysRead.lean`).

- `DnOut`, `dentsRes`: what `getdents64` from a state delivers (the entries), returns, and where the stream of
  answers is after it; `dentsRes_sum`: the entries take at most `count` bytes.
- `wrRuns`, `vRuns`: pieces of bytes at offsets from an address written one after the other, into a memory and into
  bytes `V`; `dnSt`: the state after `getdents64`, the entries in the buffer; `dnBytes`, `dnEv`: its bytes and event.
- `direntRuns_in`: the entries' pieces lie within the bytes they take.
- `vRuns_one`, `dn_one`: the pieces written one after the other are one write of the buffer's bytes after them
  (`dnBuf`: each entry's bytes, the padding as it was).
- `sysGetdents64_ok`: Zellic's `getdents64` from a state with the buffer writable and the pieces written as `wrRuns`.
- `syscall_getdents`: what the instruction `syscall` leaves for `getdents64 (rdi, rsi, rdx)`.
- `Seg.runs_ok`: pieces stored one after the other into bytes the run may store into, as `kernelWrite` stores them.
- `Seg.s_getdents_re`: the step of a run that `Fn.Seg` describes, the buffer in what the run may store into; the run
  goes on from the state after as a new start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- What a `getdents64` delivers (the entries `es`), returns (`ret`), and where the stream of answers is after it
(`t'`). -/
structure DnOut where
  es : List Dirent
  ret : BitVec 64
  t' : Nat

/-- What `getdents64 (rdi, rsi, rdx)` from `s` does, the stream of answers at `t` (as `sysGetdents64`): `EBADF` for a
descriptor not open or open with `O_PATH`, `ENOTDIR` for a file with pages; for another file the entries it gives
for `count` (`rdx`, 32 bits) bytes, or its error (`Request.dirents`). -/
def dentsRes (o : Oracle) (t : Nat) (s : State) : DnOut :=
  match s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => ⟨[], errRet EBADF, t⟩
  | some f =>
    match f.map with
    | .pages _ => ⟨[], errRet ENOTDIR, t⟩
    | _ =>
      match o t (.dirents f.id (arg32 s.cpu.gpr.rdx)) with
      | .error e => ⟨[], errRet e.val, t + 1⟩
      | .entries es _ => ⟨es, BitVec.ofNat 64 (es.map Dirent.reclen).sum, t + 1⟩

/-- The memory `M` with the pieces `rs` (an offset from `a`, the bytes there) written one after the other. -/
def wrRuns : Memory → Addr → List (Nat × List Byte) → Memory
  | M, _, [] => M
  | M, a, (k, bs) :: rs => wrRuns (writeBytes M (a.add k) bs) a rs

/-- The bytes `V` with the pieces `rs` (an offset from `a`, the bytes there) stored one after the other. -/
def vRuns : (Addr → Byte) → Addr → List (Nat × List Byte) → Addr → Byte
  | V, _, [] => V
  | V, a, (k, bs) :: rs => vRuns (Vst V (a.add k) bs) a rs

/-- The pieces `getdents64` with result `r` writes: its entries, from offset 0 of the buffer. -/
abbrev dnRuns (r : DnOut) : List (Nat × List Byte) := direntRuns r.es 0

/-- The bytes `getdents64` with result `r` passes to the process. -/
abbrev dnBytes (r : DnOut) : List Byte := (dnRuns r).flatMap (·.2)

/-- The state after `getdents64` from `s` with result `r`: the entries in the buffer (`rsi`). -/
def dnSt (s : State) (r : DnOut) : State := s.withMem (wrRuns s.proc.mm.mem s.cpu.gpr.rsi (dnRuns r))

/-- The event of `getdents64` from registers `g` with result `r`: the entries' bytes go to the process. -/
abbrev dnEv (g : Gprs) (r : DnOut) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r.ret, [], dnBytes r⟩

/-- The `n` bytes from `a` after the pieces of `r` are stored into `V`: each entry's bytes, the padding as it was. -/
abbrev dnBuf (V : Addr → Byte) (a : Addr) (n : Nat) (r : DnOut) : List Byte :=
  (byteAddrs a n).map (vRuns V a (dnRuns r))

/-- The entries `getdents64` delivers take at most `count` bytes. -/
theorem dentsRes_sum : ((dentsRes o t s).es.map Dirent.reclen).sum ≤ arg32 s.cpu.gpr.rdx := by
  unfold dentsRes
  repeat' split
  all_goals (try dsimp only)
  all_goals first
    | exact Nat.zero_le _
    | assumption
    | simp

/-- An entry's bytes fit in its `d_reclen`. -/
theorem dirent_bytes_le (e : Dirent) : e.bytes.length ≤ e.reclen := by
  simp only [Dirent.bytes, Dirent.reclen, List.length_append, toBytesLE_length, List.length_cons, List.length_nil]
  omega

/-- The pieces of the entries `es` from offset `k` lie within the bytes the entries take from there. -/
theorem direntRuns_in : ∀ (es : List Dirent) (k : Nat) (r : Nat × List Byte), r ∈ direntRuns es k →
    k ≤ r.1 ∧ r.1 + r.2.length ≤ k + (es.map Dirent.reclen).sum
  | [], _, _, h => by simp [direntRuns] at h
  | e :: es, k, r, h => by
    simp only [direntRuns, List.mem_cons] at h
    have he := dirent_bytes_le e
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · dsimp only
      exact ⟨Nat.le_refl _, by omega⟩
    · have := direntRuns_in es (k + e.reclen) r h
      exact ⟨by omega, by omega⟩

/-- Bytes apart from the pieces keep their values. -/
theorem vRuns_apart : ∀ (rs : List (Nat × List Byte)) (V : Addr → Byte) (a x : Addr),
    (∀ r ∈ rs, ∀ i < r.2.length, x ≠ a.add (r.1 + i)) → vRuns V a rs x = V x
  | [], _, _, _, _ => rfl
  | (k, bs) :: rs, V, a, x, h => by
    show vRuns (Vst V (a.add k) bs) a rs x = V x
    rw [vRuns_apart rs _ a x fun r hr => h r (by simp [hr])]
    exact Vst_apart bs V (a.add k) x fun i hi => by
      rw [addr_add_add]
      exact h (k, bs) (by simp) i hi

/-- Pieces within the `n` bytes from `a`, stored one after the other: one store of those bytes as they are after. -/
theorem vRuns_one {V : Addr → Byte} {a : Addr} {n : Nat} {rs : List (Nat × List Byte)}
    (hin : ∀ r ∈ rs, r.1 + r.2.length ≤ n) (hf : a.toNat + n ≤ 2 ^ 64) :
    vRuns V a rs = Vst V a ((byteAddrs a n).map (vRuns V a rs)) := by
  have hl : ((byteAddrs a n).map (vRuns V a rs)).length = n := by rw [List.length_map, byteAddrs_len]
  funext x
  by_cases hx : ∃ i < n, x = a.add i
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [Vst_get _ V a (by rw [hl]; exact hf) (by rw [hl]; exact hi)]
    have e := map_byteAddrs_get? (vRuns V a rs) n a i hi
    rw [List.getElem?_eq_getElem (by rw [hl]; exact hi)] at e
    exact (Option.some.inj e).symm
  · rw [Vst_apart _ V a x (fun i hi h => hx ⟨i, by rw [hl] at hi; exact hi, h⟩)]
    exact vRuns_apart rs V a x fun r hr i hi h => hx ⟨r.1 + i, by have := hin r hr; omega, h⟩

/-- The entries of `r`, within `n` bytes from `a`: one store of the buffer's bytes after them (`dnBuf`). -/
theorem dn_one {V : Addr → Byte} {a : Addr} {n : Nat} {r : DnOut} (hs : (r.es.map Dirent.reclen).sum ≤ n)
    (hf : a.toNat + n ≤ 2 ^ 64) : vRuns V a (dnRuns r) = Vst V a (dnBuf V a n r) :=
  vRuns_one (fun q hq => by have := direntRuns_in r.es 0 q hq; omega) hf

/-- `getdents64 (rdi, rsi, rdx)` on Zellic's model, `rsi`'s `count` bytes writable and the pieces of any entries that
fit stored as `wrRuns`, from any state with `s`'s memory and keys: as `dentsRes` says. -/
theorem sysGetdents64_ok (hw : Writable prof s s.cpu.gpr.rsi (arg32 s.cpu.gpr.rdx))
    (hk : ∀ es : List Dirent, (es.map Dirent.reclen).sum ≤ arg32 s.cpu.gpr.rdx →
      (direntRuns es 0).foldl (fun acc (k, bs) => acc.bind fun t => kernelWrite prof.feat t (s.cpu.gpr.rsi.add k) bs)
        (some s) = some (s.withMem (wrRuns s.proc.mm.mem s.cpu.gpr.rsi (direntRuns es 0)))) :
    (sysGetdents64 prof s).runStream o t =
      (sysReturn (dnSt s (dentsRes o t s)) (dentsRes o t s).ret [] (dnBytes (dentsRes o t s)),
        (dentsRes o t s).t') := by
  unfold sysGetdents64 dentsRes
  try dsimp only
  -- Case on each test both sides make (`split` would case on one side only), the same terms on both.
  cases s.proc.files.descNoPath (arg32 s.cpu.gpr.rdi) with
  | none => rfl
  | some f =>
    try dsimp only
    cases f.map with
    | pages id => rfl
    | none | path | other =>
      try dsimp only
      rw [req_ask_run]
      try dsimp only
      cases o t (Request.dirents f.id (arg32 s.cpu.gpr.rdx)) with
      | error e => rfl
      | entries es h =>
        cases es with
        | nil => rfl
        | cons e es =>
          try dsimp only
          rw [growFor_ok (writable_le hw h), req_pure_bind]
          try dsimp only
          first
            | rw [hk (e :: es) h]
            | erw [hk (e :: es) h]
          all_goals rfl

example {len : Nat} : dentsRes o t (nx s len (sysGpr s len) (rf0 s)) = dentsRes o t s := rfl
example {len : Nat} : (nx s len (sysGpr s len) (rf0 s)).proc.files = s.proc.files := rfl
example {len : Nat} : arg32 (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = arg32 s.cpu.gpr.rdi := rfl
example {len : Nat} (R : DnOut) (v : BitVec 64) :
    (dnSt (nx s len (sysGpr s len) (rf0 s)) R).setRax v = sysSt (dnSt s R) len v := rfl
example {len : Nat} (R : DnOut) : sysReturn (dnSt (nx s len (sysGpr s len) (rf0 s)) R) R.ret [] (dnBytes R) =
    .running (sysSt (dnSt s R) len R.ret) (some (dnEv s.cpu.gpr R)) := rfl
example {len : Nat} : dentsRes o t (nx s len (sysGpr s len) (rf0 s)) = dentsRes o t s := by
  unfold dentsRes; rfl

/-- `syscall` for `getdents64 (rdi, rsi, rdx)`, `rsi`'s `count` bytes writable and the pieces of any entries that fit
stored as `wrRuns` from any state with `s`'s memory and keys: the entries in the buffer, `dentsRes`'s answer in
`rax`. -/
theorem syscall_getdents {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 217) (hw : Writable prof s s.cpu.gpr.rsi (arg32 s.cpu.gpr.rdx))
    (hk : ∀ es : List Dirent, (es.map Dirent.reclen).sum ≤ arg32 s.cpu.gpr.rdx → ∀ Y : State,
      Y.proc.mm.mem = s.proc.mm.mem → Y.cpu.pkru = s.cpu.pkru →
      (direntRuns es 0).foldl (fun acc (k, bs) => acc.bind fun t => kernelWrite prof.feat t (s.cpu.gpr.rsi.add k) bs)
        (some Y) = some (Y.withMem (wrRuns s.proc.mm.mem s.cpu.gpr.rsi (direntRuns es 0)))) :
    (instruction prof s).runStream o t =
      (.running (sysSt (dnSt s (dentsRes o t s)) len (dentsRes o t s).ret)
        (some (dnEv s.cpu.gpr (dentsRes o t s))), (dentsRes o t s).t') := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (217 ≥ 2 ^ 31) by decide, show ¬ (217 ≥ x32Bit) by decide,
    show ¬ (217 ≥ nrSyscalls) by decide, show niSyscall 217 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysGetdents64 prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  rw [sysGetdents64_ok (s := nx s len (sysGpr s len) (rf0 s)) hw fun es h => hk es h _ rfl rfl]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- Pieces at offsets from `a`, in what the run may store into, stored one after the other as `kernelWrite` stores
them, from any state with `X`'s memory and keys: they can all be written, and the state they leave keeps `KeptW` and
`Agree` with `V` as they change it. -/
theorem runs_ok (c : Seg prof F Wl L s₀ o) {a : Addr} :
    ∀ (rs : List (Nat × List Byte)) (X : State) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      (∀ r ∈ rs, ∀ i < r.2.length, Foot Wl (a.add (r.1 + i))) →
      (∀ Y : State, Y.proc.mm.mem = X.proc.mm.mem → Y.cpu.pkru = X.cpu.pkru →
        rs.foldl (fun acc (k, bs) => acc.bind fun t => kernelWrite prof.feat t (a.add k) bs) (some Y) =
          some (Y.withMem (wrRuns X.proc.mm.mem a rs))) ∧
        KeptW Wl s₀ (X.withMem (wrRuns X.proc.mm.mem a rs)) ∧ Agree F (wrRuns X.proc.mm.mem a rs) (vRuns V a rs)
  | [], X, V, hK, hA, _ => ⟨fun Y hm _ => by rw [List.foldl_nil, ← hm]; rfl, hK, hA⟩
  | (k, bs) :: rs, X, V, hK, hA, hst => by
    obtain ⟨hw, hK1, hA1⟩ := c.store_ok (a := a.add k) (bs := bs) hK hA
      (fun i hi => by rw [addr_add_add]; exact hst (k, bs) (by simp) i hi)
    obtain ⟨h1, h2, h3⟩ := runs_ok c rs (st X (a.add k) bs) (Vst V (a.add k) bs) hK1 hA1
      (fun r hr => hst r (by simp [hr]))
    refine ⟨fun Y hm hp => ?_, h2, h3⟩
    have hkw : kernelWrite prof.feat Y (a.add k) bs = some (Y.withMem (writeBytes Y.proc.mm.mem (a.add k) bs)) := by
      unfold kernelWrite
      rw [ite_eq_left]
      simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
      rw [hm, hp]
      exact hw
    have hm' : (Y.withMem (writeBytes Y.proc.mm.mem (a.add k) bs)).proc.mm.mem = (st X (a.add k) bs).proc.mm.mem := by
      show writeBytes Y.proc.mm.mem (a.add k) bs = writeBytes X.proc.mm.mem (a.add k) bs
      rw [hm]
    simp only [List.foldl_cons, Option.bind_some, hkw]
    exact h1 _ hm' hp

/-- `syscall` for `getdents64 (rdi, rsi, rdx)` (a start with no `rseq` area), `rsi`'s `count` bytes (`rdx`, 32 bits)
in what the run may store into: the run goes on from the state after, its own start, with `dentsRes`'s entries in
them (`vRuns`), its answer in `rax`, the stream of answers at some `t₁` before the call. -/
theorem s_getdents_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 217)
    (hst : ∀ i < arg32 X.cpu.gpr.rdx, Foot Wl (X.cpu.gpr.rsi.add i))
    (k' : ∀ (M : Memory) (t₁ t' : Nat), KeptW Wl s₀ (X.withMem M) → Agree F M V →
      Seg prof F Wl L (sysSt (dnSt (X.withMem M) (dentsRes o t₁ (X.withMem M))) len
        (dentsRes o t₁ (X.withMem M)).ret) o →
      Agree F (dnSt (X.withMem M) (dentsRes o t₁ (X.withMem M))).proc.mm.mem
        (vRuns V X.cpu.gpr.rsi (dnRuns (dentsRes o t₁ (X.withMem M)))) →
      GoG prof L o (gev ++ [dnEv X.cpu.gpr (dentsRes o t₁ (X.withMem M))]) gP gE
        (sysSt (dnSt (X.withMem M) (dentsRes o t₁ (X.withMem M))) len (dentsRes o t₁ (X.withMem M)).ret)
        t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    obtain ⟨hw, -, -⟩ := c.store_ok (a := X.cpu.gpr.rsi) (bs := List.replicate (arg32 X.cpu.gpr.rdx) 0) hK' hA'
      (fun i hi => hst i (by rw [List.length_replicate] at hi; exact hi))
    rw [List.length_replicate] at hw
    have hR := fun (es : List Dirent) (hs : (es.map Dirent.reclen).sum ≤ arg32 X.cpu.gpr.rdx) =>
      c.runs_ok (a := X.cpu.gpr.rsi) (direntRuns es 0) (X.withMem M) V hK' hA' fun r hr i hi =>
        hst _ (by have := direntRuns_in es 0 r hr; omega)
    obtain ⟨-, hK2, hA2⟩ := hR (dentsRes o (t + 1) (X.withMem M)).es dentsRes_sum
    exact ⟨_, _, _, syscall_getdents (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hw
        (fun es hs => (hR es hs).1),
      k' M _ _ hK' hA' (c.reroot hK2 rfl rfl rfl rfl rfl htf hac hrs) hA2⟩

end FV7z.Fn.Seg
