import FV7z.Efn.Cuts
/-!
# `ExtractFileNameFromPath` (PLAN.md §M, M1): design notes, no proof yet

7-Zip 26.06's `ExtractFileNameFromPath (const UString &path)` at `0x4528f0` in `7zzs`, `p` = `rdi` (the result),
`q` = `rsi` (`path`): `push r12; mov r12, rdi; mov rdi, rsi; push rbx; mov rbx, rsi; sub rsp, 8`; at 20
`call 0x44dd80` (`ReverseFind_PathSepar`, `FV7z/Rpp`, `rel` 18446744073709532279); at 25 `mov rdi, r12;
lea edx, [rax + 1]; mov rax, [rbx]; lea rsi, [rax + rdx * 4]`; at 38 `call 0x44d480` (`UString (const wchar_t *)`,
`FV7z/Ucw`, `rel` 18446744073709529957); at 43 `add rsp, 8; mov rax, r12; pop rbx; pop r12; ret` (53). Blocks and
cuts (0, 25, 43) are generated and build (kt632).

The wpx goals (kt632 probe):
- `W_0`: `Foot Wl` of `rsp - 8`, `rsp - 8 - 8` ∧ `Q 20 { g with rbx := rsi, rsp := rsp - 8 - 8 - 8#64,
  rdi := rsi, r12 := rdi } (subF …) Vp` (the same `Vp` as `Pvu`'s).
- `W_25`: `Foot F.data` of `rbx` (8) ∧ `Q 38 { g with rax := rdq(V, rbx), rdx := sw64 (sw32 (rax + 1#64)),
  rsi := rdq(V, rbx) + sw64 (sw32 (rax + 1#64)) * 4#64, rdi := r12 } (rfz f) V`.
- `W_43`: `Foot F.data` of `rsp + 8#64`, `rsp + 8#64 + 8` ∧ `Q 53 { g with rax := r12, rbx := rdq(V, rsp + 8#64),
  rsp := rsp + 8#64 + 8 + 8, r12 := rdq(V, rsp + 8#64 + 8) } … V`.

Plan (next step): as `FV7z/Pvu/Holds.lean`'s notes (same prologue, epilogue and frame; share `Fr`, `Vp`, `Fkp`,
`RK`, `fr3`, `m_vp` in one module, e.g. `FV7z/Lemmas/Fr24.lean`), straight line with two `SpAt.callK`s, both callees
`FnK … (RK A)`. `T₁`: `rsp` the slot, `rdi = q`, bytes = `V` outside the frame. `T₂`: `rsp` the slot, `rdi = p`,
`rsi = rdq(W, q) + sw64 (sw32 (a + 1#64)) * 4#64`, `A W` (needs `q`'s 8 bytes apart from `[s - 32, s + 8)`). After
the first call `rsp` is `(s - 8 - 8 - 8#64 - 8) + 8`: normalize with `simp only [BitVec.sub_add_cancel]`. Post:
`A V'`, `rax = p`, callee-saved restored, `rsp = s + 8`.
-/
