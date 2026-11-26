import FV7z.Ug1.Cuts
/-!
# `UString::Grow_1` (`0x44d0a0`, PLAN.md §M, M1): design notes, no proof yet

Blocks and cuts are generated (`tools/blk_gen.py` entry `ug1`, `hand=(0x2c,)`) and build (kt632): `W_0` (cond 7 →
37, else `W_33`: cond 6 → 42, else 37), `W_37` (→ 42), `W_42` (→ 44: the `jbe` to the throw stub `0x4013e4`, by hand),
`W_50` (`add rsp` → 54: the tail `jmp` to `0x44cfc0`, `FV7z/Ura`).

Plan (next step): read the kt632 probe goals (run 45836518817, log lines 704–952), then as `FV7z/Caa/Holds.lean`
(tail jump: `c.s_jmp_x … hinX (Ura.lt_len (j := 0) _)`, continuation `kf` at the callee's entry) plus the throw stub
as a second continuation `kt` taken by `Seg.s_jcc_x` at 44 (as `Ur2`). The arithmetic on the limit by `bv_omega`
lemmas kept standalone.
-/
