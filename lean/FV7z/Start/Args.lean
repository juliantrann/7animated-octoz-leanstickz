import FV7z.Start.Words
import FV7z.Start.StackWords
/-!
# `argc`, `argv`, `envp` and the auxiliary vector of `7zzs` at its first instruction (PLAN.md G3, startup)

- `launch_args`: at the first instruction of `7zzs`, launched with room for `n` bytes of stack, for a choice the
  kernel can make: the quadword at `rsp` is `argc`; after it the `argv` pointers (the strings' addresses,
  `stringAddrs` from `StackLayout.strings`) and a null; the `envp` pointers and a null; then the auxiliary vector
  `auxv`, a type and a value for each entry. What `Ctx.Lch` (`Start/Inv.lean`) says of the stack's words, from
  Zellic's `execve` (`launch_words`, `stackWords_get`).
-/
namespace FV7z.Start
open ZellicX86

theorem launch_args {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp ∧
      ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp + 8 * 0)) 8)) =
        BitVec.ofNat 64 l.args.argv'.length ∧
      (∀ i < l.args.argv'.length, ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp + 8 * (1 + i))) 8)) =
        BitVec.ofNat 64 ((stringAddrs (stackLayout l.args l.prof.linux c).strings
          (l.args.argv' ++ l.args.envp)).getD i 0)) ∧
      ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp +
            8 * (1 + l.args.argv'.length))) 8)) = BitVec.ofNat 64 0 ∧
      (∀ i < l.args.envp.length, ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp +
            8 * (1 + l.args.argv'.length + 1 + i))) 8)) =
        BitVec.ofNat 64 ((stringAddrs (stackLayout l.args l.prof.linux c).strings
          (l.args.argv' ++ l.args.envp)).getD (l.args.argv'.length + i) 0)) ∧
      ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp +
            8 * (1 + l.args.argv'.length + 1 + l.args.envp.length))) 8)) = BitVec.ofNat 64 0 ∧
      ∀ m < auxCount l.prof.linux,
        ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
            (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp +
              8 * (1 + l.args.argv'.length + 1 + l.args.envp.length + 1 + 2 * m))) 8)) =
          BitVec.ofNat 64 ((auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
            (stackLayout l.args l.prof.linux c)).getD m (0, 0)).1 ∧
        ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
            (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp +
              8 * (1 + l.args.argv'.length + 1 + l.args.envp.length + 1 + (2 * m + 1)))) 8)) =
          BitVec.ofNat 64 ((auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
            (stackLayout l.args l.prof.linux c)).getD m (0, 0)).2 := by
  obtain ⟨hdr, c, hr, hv, e, hall⟩ := launch_words h hroom
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := stackWords_get (auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
    (stackLayout l.args l.prof.linux c)) l.args (stackLayout l.args l.prof.linux c)
  have hlen := stackWords_length (auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
    (stackLayout l.args l.prof.linux c)) l.args (stackLayout l.args l.prof.linux c)
  have hax := auxv_length l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c (stackLayout l.args l.prof.linux c)
  rw [hax] at hlen
  refine ⟨hdr, c, hr, hv, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hall 0 (by omega)
    rwa [g0] at this
  · intro i hi
    have := hall (1 + i) (by omega)
    rwa [g1 i hi] at this
  · have := hall (1 + l.args.argv'.length) (by omega)
    rwa [g2] at this
  · intro i hi
    have := hall (1 + l.args.argv'.length + 1 + i) (by omega)
    rwa [g3 i hi] at this
  · have := hall (1 + l.args.argv'.length + 1 + l.args.envp.length) (by omega)
    rwa [g4] at this
  · intro m hm
    obtain ⟨f1, f2⟩ := g5 m (by omega)
    constructor
    · have := hall (1 + l.args.argv'.length + 1 + l.args.envp.length + 1 + 2 * m) (by omega)
      rwa [f1] at this
    · have := hall (1 + l.args.argv'.length + 1 + l.args.envp.length + 1 + (2 * m + 1)) (by omega)
      rwa [f2] at this

end FV7z.Start
