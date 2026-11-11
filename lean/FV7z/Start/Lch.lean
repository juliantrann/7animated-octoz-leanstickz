import FV7z.Entry.Holds
import FV7z.Start.StackAt
import FV7z.Start.AuxvFacts
/-!
# Towards `Ctx.Lch` from the launch (PLAN.md G3, startup)

`_start` writes three words below `rsp` before `__libc_start_main` reads the stack (`Entry.V1`); what `execve` put
at and above `rsp` is as it was.

- `V1_rdq`, `V1_byte`: a quadword and a byte at or above `rsp` after `_start`'s three stores.
- `StackAt.V1_word`: so are the words `execve` wrote from `rsp`, each read after those stores.
- `StackAt.lch_reads`: the environment's array and the auxiliary vector as `Ctx.Lch` reads them (`henv`, `hend`,
  `hty`, `hval`).
- `StackAt.lch_str`: the environment's strings as `Ctx.Lch` reads them (`hstr`, and the bounds for `sfit`, `cStr`).
- `V1_se`: `Ctx.Lch`'s `hse`, the `stack_end` argument `_start` pushed.
- `auxv_zzs`: `Ctx.Lch`'s `hsec0` (for an exec that is not a secure one) and `hph0`, for 7zzs.
- `bytes_drop`, `StackAt.argv_bytes`: the words after the argument count, from `rsp + 8`, as Zellic's `InitialStack`
  says them.
- `auxv_idx`: the auxiliary vector by index, as `Ctx.Lch` says it (`hnzT`, `hendT`, `hsn`/`hsec`, `hsec0`, `hph`,
  `hph0`): the entries before the last have types other than 0, the last is `AT_NULL`, there is an `AT_SECURE`
  and every one's value is 1 for a secure exec and 0 otherwise, there is an `AT_PHDR` and every one's value is the
  program headers' address.
-/
namespace FV7z.Start
open ZellicX86

theorem V1_byte {V : Addr → Byte} {sp rax : BitVec 64} (hlo : 24 ≤ sp.toNat) {y : Nat} (h1 : sp.toNat ≤ y)
    (h2 : y < 2 ^ 64) : Entry.V1 V sp rax (BitVec.ofNat 64 y) = V (BitVec.ofNat 64 y) :=
  Entry.V1_out V sp rax hlo _ (.inr (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]; exact h1))

theorem V1_rdq {V : Addr → Byte} {sp rax : BitVec 64} (hlo : 24 ≤ sp.toNat) {y : Nat} (h1 : sp.toNat ≤ y)
    (h2 : y + 8 ≤ 2 ^ 64) :
    ofBytesLE 64 (List.map (Entry.V1 V sp rax) (byteAddrs (BitVec.ofNat 64 y) 8)) =
      ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 y) 8)) := by
  congr 1
  simp only [byteAddrs, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_apply, add_ofNat]
  exact V1_byte hlo (by omega) (by omega)

theorem auxv_idx (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 ≠ 0) ∧
    (auxv prof hdr pa a c l).getD (auxCount prof.linux - 1) (0, 0) = (0, 0) ∧
    (∃ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 23) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 23 →
      ((auxv prof hdr pa a c l).getD n (0, 0)).2 = if a.secure then 1 else 0) ∧
    (∃ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 3) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 3 →
      ((auxv prof hdr pa a c l).getD n (0, 0)).2 = pa) := by
  obtain ⟨pre, hA, hnz, h3, m3, h23, m23⟩ := auxv_facts prof hdr pa a c l
  have hlen : pre.length = auxCount prof.linux - 1 := by
    have := auxv_length prof hdr pa a c l
    rw [hA] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  rw [hA, ← hlen]
  have hin : ∀ n, n < pre.length → (pre ++ [(0, 0)]).getD n (0, 0) ∈ pre := by
    intro n hn
    rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  have hof : ∀ t k : Nat, t < 64 → k < 64 → BitVec.ofNat 64 t = BitVec.ofNat 64 k → t = k := by
    intro t k ht hk h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hex : ∀ e ∈ pre, ∃ n < pre.length, (pre ++ [(0, 0)]).getD n (0, 0) = e := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 he
    exact ⟨n, hn, by
      rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn h0
    have := hnz _ (hin n hn)
    exact this.1 (hof _ 0 this.2 (by omega) h0)
  · have := getD_skip pre [((0 : Nat), (0 : Nat))] (0, 0) 0
    rw [Nat.add_zero] at this
    rw [this]
    rfl
  · obtain ⟨n, hn, e⟩ := hex _ m23
    exact ⟨n, hn, by rw [e]; rfl⟩
  · intro n hn h
    exact h23 _ (hin n hn) (hof _ 23 (hnz _ (hin n hn)).2 (by omega) h)
  · obtain ⟨n, hn, e⟩ := hex _ m3
    exact ⟨n, hn, by rw [e]; rfl⟩
  · intro n hn h
    exact h3 _ (hin n hn) (hof _ 3 (hnz _ (hin n hn)).2 (by omega) h)

/-- The words `execve` wrote from `rsp` (`argc`, the `argv` and `envp` pointers, the auxiliary vector) read the same
after `_start`'s three stores below `rsp`. -/
theorem StackAt.V1_word {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hlo : 24 ≤ (stackLayout a prof.linux c).sp) (rax : BitVec 64)
    {k : Nat} (hk : k < 1 + (a.argv'.length + 1) + (a.envp.length + 1) + 2 * auxCount prof.linux) :
    ofBytesLE 64 (List.map (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax)
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * k)) 8)) =
      ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * k)) 8)) := by
  obtain ⟨r1, r2, r3⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) h.top.1 h.align h.limits
  rw [wordBytes_length, stackWords_length, auxv_length] at r1
  have htop := h.top.2
  have hsp : (stackLayout a prof.linux c).sp + 8 * k + 8 ≤ 2 ^ 47 := by
    simp only [List.length_append] at r2
    omega
  have hrsp : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  exact V1_rdq (by omega) (by omega) (by omega)

/-- The environment's array and the auxiliary vector as `Ctx.Lch` reads them (`henv`, `hend`, `hty`, `hval`, and
`hendT` with `auxv_idx`): after `_start`'s stores, from `envp = rsp + 8 * (1 + argc + 1)`, the environment's pointers
and their null, and from `av = envp + 8 * (envc + 1)` the vector's types and values. -/
theorem StackAt.lch_reads {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hlo : 24 ≤ (stackLayout a prof.linux c).sp) (rax : BitVec 64) :
    (∀ i < a.envp.length, ofBytesLE 64 (List.map (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax)
        (byteAddrs (Addr.add (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1)))
          (8 * i)) 8)) =
      BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
        (a.argv'.length + i) 0)) ∧
    ofBytesLE 64 (List.map (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax)
        (byteAddrs (Addr.add (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1)))
          (8 * a.envp.length)) 8)) = 0 ∧
    ∀ m < auxCount prof.linux,
      ofBytesLE 64 (List.map (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax)
          (byteAddrs (Addr.add (Addr.add
            (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1)))
            (8 * (a.envp.length + 1))) (16 * m)) 8)) =
        BitVec.ofNat 64 ((auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)).getD m (0, 0)).1 ∧
      ofBytesLE 64 (List.map (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax)
          (byteAddrs (Addr.add (Addr.add
            (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1)))
            (8 * (a.envp.length + 1))) (16 * m + 8)) 8)) =
        BitVec.ofNat 64 ((auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)).getD m (0, 0)).2 := by
  obtain ⟨-, -, -, g3, g4, g5⟩ := h.args
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have e : (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) + 8 * i =
        (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1 + i) := by omega
    rw [add_ofNat, e, h.V1_word hlo rax (by omega)]
    exact g3 i hi
  · have e : (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) + 8 * a.envp.length =
        (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1 + a.envp.length) := by omega
    rw [add_ofNat, e, h.V1_word hlo rax (by omega)]
    exact g4
  · intro m hm
    have e1 : (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) + 8 * (a.envp.length + 1) + 16 * m =
        (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1 + a.envp.length + 1 + 2 * m) := by omega
    have e2 : (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) + 8 * (a.envp.length + 1) +
        (16 * m + 8) =
        (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1 + a.envp.length + 1 + (2 * m + 1)) := by
      omega
    rw [add_ofNat, add_ofNat, add_ofNat, e1, e2, h.V1_word hlo rax (by omega), h.V1_word hlo rax (by omega)]
    exact g5 m hm

/-- The environment's strings as `Ctx.Lch` reads them (`hstr`, with `sfit`, `hnz` and the bounds `cStr` needs): the
`i`-th one's address is not null, the string with its null ends below `2 ^ 47` and lies above the words `execve`
wrote from `rsp`, and after `_start`'s stores its bytes are the string's, then a 0. -/
theorem StackAt.lch_str {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hlo : 24 ≤ (stackLayout a prof.linux c).sp) (rax : BitVec 64)
    {i : Nat} (hi : i < a.envp.length) :
    (stackLayout a prof.linux c).sp +
        8 * (1 + (a.argv'.length + 1) + (a.envp.length + 1) + 2 * auxCount prof.linux) ≤
      (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 ∧
    (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 +
        (a.envp.getD i []).length + 1 + 8 ≤ 2 ^ 47 ∧
    ∀ k ≤ (a.envp.getD i []).length,
      Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax
          (Addr.add (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings
            (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0)) k) =
        (a.envp.getD i [] ++ [0]).getD k 0 := by
  obtain ⟨e1, e2⟩ := h.env_in hi
  have htop := h.top.2
  refine ⟨e1, by omega, ?_⟩
  intro k hk
  have hrsp : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [add_ofNat, V1_byte (by omega) (by omega) (by omega)]
  exact h.env hi hk

/-- `Ctx.Lch`'s `hse` with `K.bp = rsp - 400` and `K.stackEnd = rsp - 8`: the seventh argument `_start` pushed
(`stack_end`) is at `bp + 384`. -/
theorem V1_se (V : Addr → Byte) (sp rax : BitVec 64) (hlo : 24 ≤ sp.toNat) :
    ofBytesLE 64 (List.map (Entry.V1 V sp rax) (byteAddrs (sp - 400#64 + 384#64) 8)) = sp - 8#64 := by
  have e : sp - 400#64 + 384#64 = sp - 16#64 := by bv_omega
  rw [e]
  exact Entry.V1_end V sp rax hlo

/-- `Ctx.Lch`'s `hsec0` and `hph0` for 7zzs: where the exec is not a secure one, every `AT_SECURE`'s value is 0, and
every `AT_PHDR`'s value is `0x400040`, not null. -/
theorem auxv_zzs (prof : Profile) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) (hs : a.secure = false) :
    (∀ n < auxCount prof.linux - 1,
      BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
        (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c l).getD n (0, 0)).1 = 23 →
      (BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
        (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c l).getD n (0, 0)).2).setWidth 32 = 0#32) ∧
    (∀ n < auxCount prof.linux - 1,
      BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
        (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c l).getD n (0, 0)).1 = 3 →
      BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
        (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c l).getD n (0, 0)).2 ≠ 0) := by
  obtain ⟨-, -, -, h23, -, h3⟩ := auxv_idx prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c l
  constructor
  · intro n hn h
    rw [h23 n hn h, hs]
    rfl
  · intro n hn h
    rw [h3 n hn h, zzs_phdrAddr]
    decide

/-- The bytes after a run's first ones. -/
theorem bytes_drop {s : State} {a : Nat} {xs ys : List Byte} (h : Bytes s (BitVec.ofNat 64 a) (xs ++ ys)) :
    Bytes s (BitVec.ofNat 64 (a + xs.length)) ys :=
  bytes_getD fun i hi => by
    have h1 := bytes_at h (i := xs.length + i) (by rw [List.length_append]; omega)
    rw [Nat.add_assoc, h1]
    exact getD_skip xs ys 0 i

/-- The words after the argument count, from `rsp + 8`, as Zellic's `InitialStack` says them: the `argv` and `envp`
pointers with their nulls, and the auxiliary vector. -/
theorem StackAt.argv_bytes {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) :
    Bytes s (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8))
      (wordBytes ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
        (stackLayout a prof.linux c)).drop 1)) := by
  have h1 := h.bytes.1
  have e : wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
      (stackLayout a prof.linux c)) = toBytesLE (BitVec.ofNat 64 a.argv'.length) 8 ++
      wordBytes ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
        (stackLayout a prof.linux c)).drop 1) := by
    simp only [stackWords, wordBytes, List.append_assoc, List.singleton_append]
    rfl
  rw [e] at h1
  have h2 := bytes_drop h1
  rwa [toBytesLE_length] at h2

end FV7z.Start
