import FV7z.Start.Plat
/-!
# The `AT_PLATFORM` string in the launch bytes (PLAN.md G3, startup)

`execve` puts the platform string (`"x86_64"` and a 0, `platformString`) on the new stack, after the 16 random
bytes; `AT_PLATFORM` has its address (`ctxOf_platform`). `_start`'s three stores are below `rsp`, so the launch
bytes `K.V0` (`Entry.V1`) have the string there.

- `StackAt.v1_pstr`: each byte of the string in `Entry.V1` of the launch state.
-/
namespace FV7z.Start
open ZellicX86

/-- The platform string in the bytes after `_start`'s stores. -/
theorem StackAt.v1_pstr {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hlo : 24 ≤ (stackLayout a prof.linux c).sp) (rax : BitVec 64)
    {k : Nat} (hk : k < platformString.length) :
    Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp rax
        (BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length + k)) =
      platformString.getD k 0 := by
  obtain ⟨r1, r2, r3⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) h.top.1 h.align h.limits
  have htop := h.top.2
  have hl : (toBytesLE c.random 16).length = 16 := toBytesLE_length _ _
  simp only [List.length_append, hl] at r2
  have hrsp : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hb := V1_byte (V := s.proc.mm.mem.readByte) (sp := s.cpu.gpr.rsp) (rax := rax)
    (y := (stackLayout a prof.linux c).platform - platformString.length + k) (by rw [hrsp]; omega)
    (by rw [hrsp]; omega) (by omega)
  rw [hb]
  have e := bytes_at h.bytes.2.1 (i := 16 + k) (by simp only [List.length_append, hl]; omega)
  have ea : (stackLayout a prof.linux c).platform - platformString.length - 16 + (16 + k) =
      (stackLayout a prof.linux c).platform - platformString.length + k := by omega
  rw [ea] at e
  have hle : (toBytesLE c.random 16).length ≤ 16 + k := by omega
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hl, Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

end FV7z.Start
