import FV7z.Start.Args
import FV7z.Start.Strings
/-!
# The initial stack of `7zzs` for one choice of the kernel (PLAN.md G3, startup)

`launch_stack_bytes`, `launch_words` and `launch_args` each say "for some choice the kernel can make". Here the
facts are about one choice `c`, so that they can be used together (for `Ctx.Lch`, `Start/Inv.lean`).

- `StackAt prof s a hdr phs c`: `rsp` is `stackLayout`'s `sp` for `c`, and the bytes from there to the stack's end
  are what `execve` writes (`stackRuns`).
- `launch_stackAt`: the state `execve` starts `7zzs` in has it, for a valid choice and the file's ELF header.
- `StackAt.bytes`, `StackAt.words`, `StackAt.env`: the three runs' `Bytes`; the quadword at `rsp + 8 * j`
  (`stackWords`, indexed by `stackWords_get`); the bytes of the `i`-th environment string at its address.
-/
namespace FV7z.Start
open ZellicX86

structure StackAt (prof : Profile) (s : State) (a : ExecArgs) (hdr : ElfHeader) (phs : List Phdr)
    (c : ExecChoice) : Prop where
  top : 2 ^ 46 ≤ c.stackTop ∧ c.stackTop ≤ 2 ^ 47
  align : c.stackAlign < 8192
  limits : a.withinLimits = true
  rsp : s.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout a prof.linux c).sp
  byte : ∀ y, (stackLayout a prof.linux c).sp ≤ y → y < c.stackTop →
    s.proc.mm.mem.readByte (BitVec.ofNat 64 y) = runsByte (stackRuns prof hdr phs a c) y
  page : ∀ x : Addr, (stackLayout a prof.linux c).start ≤ x.toNat → x.toNat < c.stackTop →
    ∃ mp, s.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot.read = true ∧ mp.prot.write = true ∧ mp.pkey = 0 ∧
      ∃ f, s.proc.mm.mem.backings mp.backing = .priv f

theorem launch_stackAt {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args hdr zzsPhdrs c := by
  obtain ⟨hdr, c, hr, hv, er, hlt, htop, hall, hpage⟩ := launch_stack_at h hroom
  have hT : 2 ^ 46 ≤ c.stackTop := by
    have := hv.stackTop.2.1
    simp only [stackTopMax] at this
    omega
  refine ⟨hdr, c, hr, hv, ⟨hT, htop⟩, hv.stackAlign, ExecStart.limits h.2.1, ?_, ?_, hpage⟩
  · apply BitVec.eq_of_toNat_eq
    rw [er, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro y h1 h2
    have ey : (BitVec.ofNat 64 y).toNat = y := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := hall (BitVec.ofNat 64 y) (by rw [ey]; omega) (by rw [ey]; exact h2)
    rw [ey] at this
    exact this

theorem StackAt.bytes {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) :
    Bytes s (BitVec.ofNat 64 (stackLayout a prof.linux c).sp)
        (wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
          (stackLayout a prof.linux c))) ∧
      Bytes s (BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16))
        (toBytesLE c.random 16 ++ platformString) ∧
      Bytes s (BitVec.ofNat 64 (stackLayout a prof.linux c).strings) a.strings := by
  obtain ⟨⟨hT, htop⟩, hA, hw, -, key⟩ := h
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) hT hA hw
  refine ⟨bytes_getD fun i hi => ?_, bytes_getD fun i hi => ?_, bytes_getD fun i hi => ?_⟩
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := prof) (hdr := hdr) (phs := phs) hT hA hw _).1 (by omega) (by omega)]
    congr 1
    omega
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := prof) (hdr := hdr) (phs := phs) hT hA hw _).2.1 (by omega) (by omega)]
    congr 1
    omega
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := prof) (hdr := hdr) (phs := phs) hT hA hw _).2.2 (by omega) (by omega)]
    congr 1
    omega

theorem StackAt.words {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) {j : Nat}
    (hj : j < (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
      (stackLayout a prof.linux c)).length) :
    ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * j)) 8)) =
      BitVec.ofNat 64 ((stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
        (stackLayout a prof.linux c)).getD j 0) :=
  words_rdq (fun _ hi => bytes_at h.bytes.1 hi) hj

theorem StackAt.env {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) {i : Nat} (hi : i < a.envp.length) {k : Nat}
    (hk : k ≤ (a.envp.getD i []).length) :
    s.proc.mm.mem.readByte (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings
        (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 + k)) = (a.envp.getD i [] ++ [0]).getD k 0 :=
  env_bytes h.bytes.2.2 hi hk

/-- The `i`-th environment string lies above the words `execve` writes from `rsp` and below the stack's end. -/
theorem StackAt.env_in {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) {i : Nat} (hi : i < a.envp.length) :
    (stackLayout a prof.linux c).sp +
        8 * (1 + (a.argv'.length + 1) + (a.envp.length + 1) + 2 * auxCount prof.linux) ≤
      (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 ∧
    (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 +
        (a.envp.getD i []).length + 1 + 8 ≤ c.stackTop := by
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) h.top.1 h.align h.limits
  rw [wordBytes_length, stackWords_length, auxv_length] at h12
  obtain ⟨e1, e2⟩ := FV7z.Start.env_in a (stackLayout a prof.linux c).strings hi
  constructor <;> omega

/-- `argc`, the `argv` and `envp` pointers with their nulls, and the auxiliary vector's entries, at `rsp`. -/
theorem StackAt.args {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) :
    ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * 0)) 8)) =
      BitVec.ofNat 64 a.argv'.length ∧
    (∀ i < a.argv'.length, ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + i))) 8)) =
      BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD i 0)) ∧
    ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length))) 8)) =
      BitVec.ofNat 64 0 ∧
    (∀ i < a.envp.length, ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1 + i))) 8)) =
      BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
        (a.argv'.length + i) 0)) ∧
    ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp +
          8 * (1 + a.argv'.length + 1 + a.envp.length))) 8)) = BitVec.ofNat 64 0 ∧
    ∀ m < auxCount prof.linux,
      ofBytesLE 64 (List.map s.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp +
            8 * (1 + a.argv'.length + 1 + a.envp.length + 1 + 2 * m))) 8)) =
        BitVec.ofNat 64 ((auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)).getD m (0, 0)).1 ∧
      ofBytesLE 64 (List.map s.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp +
            8 * (1 + a.argv'.length + 1 + a.envp.length + 1 + (2 * m + 1)))) 8)) =
        BitVec.ofNat 64 ((auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)).getD m (0, 0)).2 := by
  have hall := @StackAt.words _ _ _ _ _ _ h
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := stackWords_get (auxv prof hdr (phdrAddr hdr phs) a c
    (stackLayout a prof.linux c)) a (stackLayout a prof.linux c)
  have hlen := stackWords_length (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
    (stackLayout a prof.linux c)
  have hax := auxv_length prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)
  rw [hax] at hlen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hall (j := 0) (by omega)
    rwa [g0] at this
  · intro i hi
    have := hall (j := 1 + i) (by omega)
    rwa [g1 i hi] at this
  · have := hall (j := 1 + a.argv'.length) (by omega)
    rwa [g2] at this
  · intro i hi
    have := hall (j := 1 + a.argv'.length + 1 + i) (by omega)
    rwa [g3 i hi] at this
  · have := hall (j := 1 + a.argv'.length + 1 + a.envp.length) (by omega)
    rwa [g4] at this
  · intro m hm
    obtain ⟨f1, f2⟩ := g5 m (by omega)
    constructor
    · have := hall (j := 1 + a.argv'.length + 1 + a.envp.length + 1 + 2 * m) (by omega)
      rwa [f1] at this
    · have := hall (j := 1 + a.argv'.length + 1 + a.envp.length + 1 + (2 * m + 1)) (by omega)
      rwa [f2] at this

/-- `envp` as `__libc_start_main` computes it from `argc` and `argv` (`&argv[argc + 1]`) is where `execve` put the
environment's pointers. -/
theorem StackAt.envp {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) :
    s.cpu.gpr.rsp + 8#64 + BitVec.signExtend 64 ((ofBytesLE 64 (List.map s.proc.mm.mem.readByte
        (byteAddrs s.cpu.gpr.rsp 8))).setWidth 32) * 8#64 + 8#64 =
      BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1)) := by
  have g := h.args.1
  simp only [Nat.mul_zero, Nat.add_zero] at g
  rw [h.rsp, g, sext_small (args_lt h.limits).1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

end FV7z.Start
