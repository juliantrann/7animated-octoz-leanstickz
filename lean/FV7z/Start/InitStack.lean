import FV7z.Start.Runs
import FV7z.Start.LoadedAt
/-!
# The initial stack of `7zzs` (PLAN.md G3, startup)

- `bytes_getD`: bytes read one by one are `Bytes`.
- `launch_stack_bytes`: at the first instruction of `7zzs`, for a choice the kernel can make: `rsp` is
  `stackLayout`'s `sp`; from `rsp` lie the words `execve` writes (`stackWords`: `argc`, the `argv` and `envp`
  pointers, the auxiliary vector `auxv`), at `AT_RANDOM`'s address its 16 bytes and the platform string, at
  `StackLayout.strings` the argument and environment strings: the parts of Zellic's `InitialStack` that are on
  the stack (its `Bytes`; they can be read by `launch_stack_rw`).
-/
namespace FV7z.Start
open ZellicX86

theorem bytes_getD {s : State} {a : Nat} {bs : List Byte}
    (h : ∀ i < bs.length, s.proc.mm.mem.readByte (BitVec.ofNat 64 (a + i)) = bs.getD i 0) :
    Bytes s (BitVec.ofNat 64 a) bs := by
  simp only [Bytes, readBytes, byteAddrs, List.map_map]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, add_ofNat]
  rw [h i h2]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem launch_stack_bytes {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp ∧
      Bytes l.s₀ (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp)
        (wordBytes (stackWords (auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
          (stackLayout l.args l.prof.linux c)) l.args (stackLayout l.args l.prof.linux c))) ∧
      Bytes l.s₀ (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).platform - platformString.length - 16))
        (toBytesLE c.random 16 ++ platformString) ∧
      Bytes l.s₀ (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) l.args.strings := by
  obtain ⟨hdr, c, hr, hv, er, hlt, htop, hall⟩ := launch_stack_byte h hroom
  have hw := ExecStart.limits h.2.1
  have hT : 2 ^ 46 ≤ c.stackTop := by
    have := hv.stackTop.2.1
    simp only [stackTopMax] at this
    omega
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := l.prof) (hdr := hdr) (phs := zzsPhdrs) hT hv.stackAlign hw
  have e : l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp := by
    apply BitVec.eq_of_toNat_eq
    rw [er, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have key : ∀ y : Nat, (stackLayout l.args l.prof.linux c).sp ≤ y → y < c.stackTop →
      l.s₀.proc.mm.mem.readByte (BitVec.ofNat 64 y) = runsByte (stackRuns l.prof hdr zzsPhdrs l.args c) y := by
    intro y h1 h2
    have ey : (BitVec.ofNat 64 y).toNat = y := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := hall (BitVec.ofNat 64 y) (by rw [ey]; omega) (by rw [ey]; exact h2)
    rw [ey] at this
    exact this
  refine ⟨hdr, c, hr, hv, e, bytes_getD fun i hi => ?_, bytes_getD fun i hi => ?_, bytes_getD fun i hi => ?_⟩
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := l.prof) (hdr := hdr) (phs := zzsPhdrs) hT hv.stackAlign hw _).1 (by omega) (by omega)]
    congr 1
    omega
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := l.prof) (hdr := hdr) (phs := zzsPhdrs) hT hv.stackAlign hw _).2.1 (by omega) (by omega)]
    congr 1
    omega
  · rw [key _ (by omega) (by omega),
      (runs_byte (prof := l.prof) (hdr := hdr) (phs := zzsPhdrs) hT hv.stackAlign hw _).2.2 (by omega) (by omega)]
    congr 1
    omega

end FV7z.Start
