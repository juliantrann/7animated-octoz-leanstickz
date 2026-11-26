import FV7z.Ugr.Cuts
/-!
# `UString::Grow` (`0x44d0e0`, PLAN.md §M, M1): design notes, no proof yet

Blocks and cuts are generated (`tools/blk_gen.py` entry `ugr`, `hand=(0x37, 0x43)`) and build (kt632): `W_0`
(cond 3 → the `ret` at 88; else `W_16` → cond 7 → 48, or `W_41` → cond 6 → 53 / 48), `W_48` (→ 53), `W_53` (→ 55:
the `jae` to the throw stub, by hand), `W_61` (→ 67: the `jb`, by hand), `W_73` (→ 80: the tail `jmp` to `0x44cfc0`,
`FV7z/Ura`).

Plan (next step): read the kt632 probe goals (run 45836518817, log lines 1045–1518), then as `FV7z/Ug1/Holds.lean`'s
notes: the `ret` (`kn`), the tail jump (`kf`), the two throw-stub branches (`kt`, `Seg.s_jcc_x`).
-/
