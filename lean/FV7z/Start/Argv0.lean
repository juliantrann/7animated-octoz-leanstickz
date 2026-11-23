import FV7z.Start.PlEnt
/-!
# `argv[0]` in the launch bytes (PLAN.md G3, startup)

`__libc_init_first` (through `Lif.lif_nb`) reads `argv[0]` and runs `strrchr` over it: `Ndi.lif_ok` asks for the
pointer at `argv` (`ha0`), that it is not null (`hnz`), and that the string has no 0 before its length and a 0 there
(`nnz`, `nz`). `execve` lays the argument strings out first from `stackLayout`'s `strings`, with `argv'` (`[""]`
for an empty `argv`, as Linux 5.18 on does), so `argv[0]` is at `strings`; `ExecArgs.Ok` says no string has a 0.

- `arg0`, `argv'_cons`, `arg0_nz`: the string, and that it has no 0.
- `StackAt.arg0`: in the launch bytes `Entry.V1`, the pointer at `rsp + 8` is `strings`, the bytes there are the
  string and a 0, and where they lie.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- `argv[0]` as `execve` passes it: the first argument string, `""` for an empty `argv`. -/
def arg0 (a : ExecArgs) : List Byte := a.argv'.getD 0 []

theorem argv'_cons (a : ExecArgs) : ∃ rest, a.argv' = arg0 a :: rest := by
  unfold arg0 ExecArgs.argv'
  by_cases h : a.argv = []
  · rw [if_pos h]
    exact ⟨[], rfl⟩
  · rw [if_neg h]
    obtain ⟨x, rest, e⟩ := List.exists_cons_of_ne_nil h
    exact ⟨rest, by rw [e]; rfl⟩

theorem arg0_nz {a : ExecArgs} (hok : a.Ok) : ∀ k < (arg0 a).length, (arg0 a).getD k 0 ≠ 0 := by
  intro k hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  refine hok.1 (arg0 a) ?_ _ (List.getElem_mem hk)
  unfold arg0 ExecArgs.argv' at hk ⊢
  by_cases h : a.argv = []
  · rw [if_pos h] at hk
    simp at hk
  · rw [if_neg h]
    obtain ⟨x, rest, e⟩ := List.exists_cons_of_ne_nil h
    simp [e]

/-- `argv[0]` in the launch bytes: the pointer at `rsp + 8` is `strings`, where the string and its 0 lie, above the
words `execve` writes from `rsp` and below the stack's end. -/
theorem StackAt.arg0 {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hlo : 24 ≤ (stackLayout a prof.linux c).sp)
    (rax : BitVec 64) :
    rdq(Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax, s.cpu.gpr.rsp + 8#64) =
        BitVec.ofNat 64 (stackLayout a prof.linux c).strings ∧
      (∀ k ≤ (arg0 a).length, Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax
        (BitVec.ofNat 64 ((stackLayout a prof.linux c).strings + k)) = (arg0 a ++ [0]).getD k 0) ∧
      (stackLayout a prof.linux c).sp +
          8 * (1 + (a.argv'.length + 1) + (a.envp.length + 1) + 2 * auxCount prof.linux) ≤
        (stackLayout a prof.linux c).strings ∧
      (stackLayout a prof.linux c).strings + (arg0 a).length + 1 + 8 ≤ c.stackTop := by
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) h.top.1 h.align h.limits
  rw [wordBytes_length, stackWords_length, auxv_length] at h12
  have htop := h.top.2
  have hrsp : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest, e⟩ := argv'_cons a
  have hpos : 0 < a.argv'.length := by rw [e]; exact Nat.succ_pos _
  have e0 : (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD 0 0 =
      (stackLayout a prof.linux c).strings := by
    rw [e, List.cons_append]
    first | rfl | simp only [stringAddrs, List.getD_cons_zero]
  have hS : a.strings = (arg0 a ++ [0]) ++ ((rest ++ a.envp ++ [a.filename]).flatMap fun s => s ++ [0]) := by
    unfold ExecArgs.strings
    rw [e, List.cons_append, List.cons_append, List.flatMap_cons]
  have hSl : (arg0 a).length + 1 ≤ a.strings.length := by
    rw [hS]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  refine ⟨?_, fun k hk => ?_, by omega, by omega⟩
  · have w := h.args.2.1 0 hpos
    rw [e0] at w
    have ea : s.cpu.gpr.rsp + 8#64 = BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + 0)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hrsp]
      omega
    rw [ea, V1_rdq (by rw [hrsp]; exact hlo) (by rw [hrsp]; omega) (by omega)]
    exact w
  · rw [V1_byte (by rw [hrsp]; exact hlo) (by rw [hrsp]; omega) (by omega),
      bytes_at h.bytes.2.2 (by omega), hS, getD_in _ _ _ (by simp only [List.length_append, List.length_cons,
        List.length_nil]; omega)]

end FV7z.Start
