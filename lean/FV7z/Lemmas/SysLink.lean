import FV7z.Lemmas.SysTask
/-!
# `readlink`: the kernel reads a path name and copies a link's contents to the process (PLAN.md G3, startup)

What the instruction `syscall` leaves, on Zellic's model (`readlinkAt`), for `readlink (path, buf, n)`: the path name
`m` nonzero bytes then a NUL, readable (and the rest of its last word: the kernel reads words), below the end of the
user address space; `0 < n`; `buf`'s `n` bytes writable. The file system's answer decides:

- `req_pure_bind`, `kernelRead_ok`, `find_range`, `pathEnd_ok`, `userPath_ok`: the kernel reads the path name
  (`strncpy_from_user`).
- `ExePath.bytes_head`: an executable's path, as the kernel writes it, starts with `/`.
- `linkRes`, `linkRes_len`: what the call returns and writes, from the file system's answer (`LinkResult`).
- `syscall_readlink`: the instruction. One answer of the stream is used.
- `Seg.s_readlink`: the step of a run that `Fn.Seg` describes, `buf` in what the run may store into.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem req_pure_bind {α β : Type} (a : α) (f : α → Req β) : (Pure.pure a >>= f : Req β) = f a := rfl

/-- `copy_from_user`'s check of bytes all readable. -/
theorem kernelRead_ok {a : Addr} {n : Nat} (h : Readable prof s a n) :
    kernelRead prof.feat s a n = some (readBytes s.proc.mm.mem a n) := by
  unfold kernelRead kernelReadable
  rw [ite_eq_left]
  simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
  exact h

/-- The first index below `n` where `p` holds, `m`. -/
theorem find_range {p : Nat → Bool} {m n : Nat} (h : ∀ i < m, p i = false) (hm : p m = true) (hn : m < n) :
    (List.range n).find? p = some m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.find?_append]
    by_cases e : m < n
    · rw [ih e]
      rfl
    · obtain rfl : m = n := by omega
      rw [List.find?_eq_none.2 fun x hx => by rw [h x (List.mem_range.1 hx)]; decide]
      simp [hm]

/-- A path name of `m` nonzero bytes and a NUL, readable, below the end of the user address space: it ends at `m`. -/
theorem pathEnd_ok {a : Addr} {m : Nat} (hm : m < pathMax) (htop : a.toNat + m + 1 ≤ userPtrMax prof.feat)
    (hr : Readable prof s a (m + 1)) (hnz : ∀ i < m, s.proc.mm.mem.readByte (a.add i) ≠ 0)
    (hz : s.proc.mm.mem.readByte (a.add m) = 0) :
    pathEnd prof.feat s a = some (m, true) := by
  have hok : ∀ i ≤ m, (decide (a.toNat + i < userPtrMax prof.feat) &&
      (kernelRead prof.feat s (a.add i) 1).isSome) = true := fun i hi => by
    have hx := hr (a.add i) (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)
    rw [kernelRead_ok (n := 1) fun y hy => by
      obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
      obtain rfl : j = 0 := by omega
      rw [addr_add_zero]
      exact hx]
    simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
    omega
  simp only [pathEnd]
  rw [find_range (m := m) ?_ ?_ hm]
  · simp only [Option.map_some, hok m (Nat.le_refl m)]
  · intro i hi
    simp only [hok i (by omega), Bool.not_true, Bool.false_or]
    exact beq_eq_false_iff_ne.2 (hnz i hi)
  · simp only [hz, beq_self_eq_true, Bool.or_true]

/-- `strncpy_from_user` of a path name of `m` nonzero bytes and a NUL, the word it ends in readable: its bytes. -/
theorem userPath_ok {a : Addr} {m : Nat} (hm : m < pathMax)
    (htop : a.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat) (hr : Readable prof s a (8 * (m / 8 + 1)))
    (hnz : ∀ i < m, s.proc.mm.mem.readByte (a.add i) ≠ 0) (hz : s.proc.mm.mem.readByte (a.add m) = 0) :
    userPath prof s a = Pure.pure (s, .ok (readBytes s.proc.mm.mem a m)) := by
  have sub : ∀ k, k ≤ 8 * (m / 8 + 1) → Readable prof s a k := fun k hk x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact hr _ (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)
  have he := pathEnd_ok hm (by omega) (sub (m + 1) (by omega)) hnz hz
  have h2 : Readable prof s (a.add (m + 1)) (8 * (m / 8 + 1) - (m + 1)) := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    have e : (a.add (m + 1)).add i = a.add (m + 1 + i) := by
      simp only [Addr.add]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [e]
    exact hr _ (mem_byteAddrs.2 ⟨m + 1 + i, by omega, rfl⟩)
  simp only [userPath, he, growFor_ok (sub (m + 1) (by omega)), growFor_ok h2, req_pure_bind]

/-- An executable's path, as the kernel writes it, starts with `/`. -/
theorem ExePath.bytes_head (x : ExePath) : ∃ r, x.bytes = 0x2f :: r := by
  unfold ExePath.bytes
  rcases h : x.names with _ | ⟨n, ns⟩
  · rw [if_pos rfl]
    exact ⟨_, rfl⟩
  · rw [if_neg (List.cons_ne_nil _ _)]
    exact ⟨_, rfl⟩

/-- What `readlink` with a buffer of `n` bytes returns and writes, from the file system's answer: the link's contents
(at most `n` bytes of them), an executable's path (shorter than `PATH_MAX`, else `ENAMETOOLONG`), or the error. -/
def linkRes (n : Nat) : LinkResult → BitVec 64 × List Byte
  | .error e => (errRet e.val, [])
  | .target bs => (BitVec.ofNat 64 (bs.take n).length, bs.take n)
  | .procExe x => if x.bytes.length < pathMax then (BitVec.ofNat 64 (x.bytes.take n).length, x.bytes.take n)
      else (errRet ENAMETOOLONG, [])

theorem linkRes_len (n : Nat) (r : LinkResult) : (linkRes n r).2.length ≤ n := by
  cases r with
  | error e => exact Nat.zero_le n
  | target bs => exact List.length_take_le n bs
  | procExe x =>
    unfold linkRes
    split
    · exact List.length_take_le n x.bytes
    · exact Nat.zero_le n

/-- The event of `readlink (path, buf, n)` from registers `g`: the path `p` read, `ret` returned, `bs` written. -/
abbrev linkEv (g : Gprs) (p : List Byte) (ret : BitVec 64) (bs : List Byte) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], ret, p, bs⟩

/-- `readlink (path, buf, n)`: the path name `p` at `path` (`m` nonzero bytes then a NUL, the word it ends in readable,
below the end of the user address space), `0 < n`, `buf`'s `n` bytes writable and below the end of
the user address space: what the file system answers (`linkRes`) is returned and written at `buf`. -/
theorem syscall_readlink {len m n : Nat} {p : List Byte} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 89) (hm : m < pathMax)
    (htop : s.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hr : Readable prof s s.cpu.gpr.rdi (8 * (m / 8 + 1)))
    (hnz : ∀ i < m, s.proc.mm.mem.readByte (s.cpu.gpr.rdi.add i) ≠ 0)
    (hz : s.proc.mm.mem.readByte (s.cpu.gpr.rdi.add m) = 0)
    (hp : readBytes s.proc.mm.mem s.cpu.gpr.rdi m = p)
    (hn : argInt s.cpu.gpr.rdx = (n : Int)) (hn0 : 0 < n)
    (htw : s.cpu.gpr.rsi.toNat + n ≤ userPtrMax prof.feat) (hw : Writable prof s s.cpu.gpr.rsi n) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.withMem (writeBytes s.proc.mm.mem s.cpu.gpr.rsi (linkRes n (o t (.readlink none p))).2))
          len (linkRes n (o t (.readlink none p))).1)
        (some (linkEv s.cpu.gpr p (linkRes n (o t (.readlink none p))).1 (linkRes n (o t (.readlink none p))).2)),
        t + 1) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (89 ≥ 2 ^ 31) by decide, show ¬ (89 ≥ x32Bit) by decide, show ¬ (89 ≥ nrSyscalls) by decide,
    show niSyscall 89 = false by decide, ↓reduceIte, Bool.false_eq_true]
  have hn' : ¬ ((n : Int) ≤ 0) := by omega
  have hu := userPath_ok (s := nx s len (sysGpr s len) (rf0 s)) (a := s.cpu.gpr.rdi) hm htop hr hnz hz
  rw [show readBytes (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem s.cpu.gpr.rdi m = p from hp] at hu
  unfold sysReadlink readlinkAt
  simp only [hrdi, hrsi, hrdx, hn, hn', ↓reduceIte, hu, req_pure_bind, eq_self_iff_true, or_true,
    Int.toNat_natCast]
  show (Req.bind (Req.request (.readlink none p)) _).runStream o t = _
  rw [Req.runStream_bind]
  generalize o t (.readlink none p) = r
  -- the bytes copied: all of them
  have C : ∀ bs : List Byte, bs.length ≤ n →
      copyOut prof (nx s len (sysGpr s len) (rf0 s)) s.cpu.gpr.rsi bs =
        Pure.pure ((nx s len (sysGpr s len) (rf0 s)).withMem
          (writeBytes (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem s.cpu.gpr.rsi bs), bs.length, true) :=
    fun bs hb => copyOut_ok (s := nx s len (sysGpr s len) (rf0 s)) (accessOk_le (by omega)) fun x hx => by
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      exact hw _ (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)
  cases r with
  | error e => rfl
  | target bs =>
    simp only [C (bs.take n) (List.length_take_le n bs), req_pure_bind, ↓reduceIte, List.take_length, linkRes]
    rfl
  | procExe x =>
    by_cases hx : x.bytes.length < pathMax
    · simp only [hx, ↓reduceIte, C (x.bytes.take n) (List.length_take_le n x.bytes), req_pure_bind,
        List.take_length, linkRes]
      rfl
    · simp only [hx, ↓reduceIte, linkRes]
      rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `readlink (path, buf, n)`: the path name `p` at `path` (`m` nonzero bytes then a NUL, the word it
ends in readable), `0 < n`, `buf`'s `n` bytes in what the run may store into: what the file system
answers, `r`, is returned and written at `buf` (`linkRes`); `rcx` and `r11` as `syscall` sets them. What all the
stream's answers to `readlink` of `p` have (`P`), `r` has. -/
theorem s_readlink (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len m n : Nat} {p : List Byte}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 89)
    (hm : m < pathMax) (htop : X.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hl : ∀ i < 8 * (m / 8 + 1), Foot F.data (X.cpu.gpr.rdi.add i))
    (hnz : ∀ i < m, V (X.cpu.gpr.rdi.add i) ≠ 0) (hz : V (X.cpu.gpr.rdi.add m) = 0)
    (hp : (byteAddrs X.cpu.gpr.rdi m).map V = p)
    (hn : argInt X.cpu.gpr.rdx = (n : Int)) (hn0 : 0 < n) (htw : X.cpu.gpr.rsi.toNat + n ≤ userPtrMax prof.feat)
    (hst : ∀ i < n, Foot Wl (X.cpu.gpr.rsi.add i)) {P : LinkResult → Prop} (hP : ∀ t, P (o t (.readlink none p)))
    (k' : ∀ r : LinkResult, P r →
      ContG prof F Wl L s₀ o (gev ++ [linkEv X.cpu.gpr p (linkRes n r).1 (linkRes n r).2]) gP gE
        (Vst V X.cpu.gpr.rsi (linkRes n r).2)
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 (linkRes n r).1) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hA' := c.agreeK hK hA hM
    have hrd := (c.load_ok (X := X.withMem M) hK' hA' hl).1
    have hv := (c.load_ok (X := X.withMem M) hK' hA' (n := m) fun i hi => hl i (by omega)).2
    have hw := (c.store_ok (X := X.withMem M) (a := X.cpu.gpr.rsi) (bs := List.replicate n 0) hK' hA'
      (by rw [List.length_replicate]; exact hst)).1
    rw [List.length_replicate] at hw
    obtain ⟨-, hK2, hA2⟩ := c.store_ok (X := X.withMem M) (a := X.cpu.gpr.rsi)
      (bs := (linkRes n (o (t + 1) (.readlink none p))).2) hK' hA'
      fun i hi => hst i (Nat.lt_of_lt_of_le hi (linkRes_len _ _))
    have hnz' : ∀ i < m, (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rdi.add i) ≠ 0 := fun i hi => by
      show M.readByte _ ≠ 0
      rw [hA' _ (hl i (by omega))]
      exact hnz i hi
    have hz' : (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rdi.add m) = 0 := by
      show M.readByte _ = 0
      rw [hA' _ (hl m (by omega))]
      exact hz
    exact ⟨_, _, _, syscall_readlink (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hm htop hrd hnz' hz'
      (hv.trans hp) hn hn0 htw hw,
      k' _ (hP (t + 1)) _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg
