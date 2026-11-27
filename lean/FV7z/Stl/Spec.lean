/-!
# Design of the `____strtoul_l_internal` proof (0x6238b0, 1220 bytes)

This file holds no declarations yet. It records the plan for the proof files `Stl/Fr.lean`, `Stl/Vc1.lean`,
`Stl/Vc2.lean` and `Stl/Holds.lean` (theorem `stl_ok`), on top of the generated `Stl/Code`, `Pats`, `Blocks*` and
`Cuts`. The weakest-precondition text of every cut point, as `wpx` prints it, is in `Stl/notes/Wp.lean` (a comment).

## Arguments and spec

`rdi` = p (the string), `rsi` = E (`endptr`, may be 0), `edx` = base, `ecx` = group flag (0 here), `r8` = the
locale. The spec ignores the result value and what is stored at `*endptr`; it states:
* the return is to the caller's address, with `rsp + 8` and `rbx`, `rbp`, `r12` to `r15` as on entry;
* memory is unchanged except in the frame [rsp - 88, rsp), in the 8 bytes at E (if E ≠ 0) and in the 4 bytes of
  `errno` at `fb - 72` (`fb + 18446744073709551544#64`);
* termination, by the measure below.

## Preconditions (`Pe F Wl fb n g V`)

* frame: 88 ≤ rsp, rsp + 8 ≤ 2^64, `Foot Wl` on [rsp - 88, rsp), `Foot F.data` on [rsp - 88, rsp + 8);
* `setWidth 32 rcx = 0` (no grouping);
* E ≠ 0 → `Foot Wl` on 8 bytes at E, and E is disjoint from the frame;
* errno: `Foot Wl` on 4 bytes at `fb - 72`, disjoint from the frame;
* string: n < 2^62, `Foot F.data` on p + k for k ≤ n, p .. p + n disjoint from the written areas,
  V (p + n) = 0 (NUL at n);
* locale: `Foot F.data` 8 bytes at r8 + 104; B = `rdq(V, r8 + 104)` is the ctype table: footprint of
  B + 2·sext w + 1 for every byte w, and B[0] has bit 32 clear (`b0`; NUL is not a space);
* CU = `rdq(V, 0x7914d8)` (7935192, toupper table): footprint of 4 bytes at CU + 4·sext w and CU + 4·zext w;
  `rdd(V, CU + 0) ≠ 88` (`u0`; toupper(0) ≠ 'X');
* CB = `rdq(V, 0x7914c8)` (7935176, ctype b table): footprint of 1 byte at CB + 2·zext w + 1;
* rodata 0x703560 (7353696) .. + 344: `Foot F.data` (the per-base tables at 7353696 and 7353760, 7353702, 7353704,
  7353808, 7353824);
* only the footprint is needed for table entries; a disjointness fact (`Ao`) only where the value matters (the
  string, r8 + 104, the CU/CB pointers and the w = 0 entries).

## Cut points (offsets) and their exits

| cut | exits |
|-----|-------|
| 0   | 696 (unreachable: ecx ≠ 0), 432 (edx = 1 or edx > 36), 99, 80 |
| 80  | 80 (skip spaces), 99 |
| 99  | 790, 448, 133 ×3 (sign '-', '+', none) |
| 133 | 171 ×2, 604 ×2, 223, 150 ×2 (base 0 / 16 with "0x" / 8) |
| 150 | 992 (unreachable: r14 = 0), 171 |
| 171 | 745 ×2, 216 |
| 216 | 223 |
| 223 | 296 |
| 265 | 368, 291 |
| 291 | 368, 296 |
| 296 | 332 ×2, 512 (unreachable: rbp = 0), 368 |
| 332 | 368, 265, 345 |
| 345 | 291, 368 |
| 368 | 748, 390 ×2 (one after storing at E) |
| 390 | 448 (errno 34, rax = -1), 429 (`ret` after a `cmov` and the pops) |
| 432 | 448 (errno 22) |
| 448 | 462 (pops, `ret`) |
| 604 | 992 (unreachable), 216, 223 |
| 745 | 748 (rdi := rbx) |
| 748 | 927, 790 ×3, 927 after storing at E |
| 790 | 448 (store r13 at E) |
| 927 | 448 |

The `ret` bytes are at 429 and 462; exits 696, 992 and 512 are closed by `absurd` from the invariant (rcx = 0, base
check, rbp = 0 and r14 = 0 in the digit loop).

## Invariant

After the prologue (cut 0): `Rk g₀ g` = rsp = fsp g₀ (= rsp₀ - 88), r13 = p, r14 = 0; `Mm` = the saved registers
and `rsi` in the frame (`pVf`: 6 pushes + the E slot at fsp + 8) and memory outside the written areas as on entry
(`Ot`). Per cut a position k with rbx = p + k (scanner) or rdi = p + k (digit loop), k ≤ n or k < n.

Measure, with K k = 100 · (n + 1 - k): entry 100 · (n + 2); 80: K k + 95; 99: K k + 94; 133: K k + 93;
604: + 92; 150: + 91; 171: + 90 (needs (setWidth 32 rax).toNat ≤ 34); 216: + 89; 223: + 88; digit loop
296: K k + 50, 332: + 40, 265 and 345: + 30, 291: + 60; then 368: 5, 745: 4, 748: 3, 390 / 927 / 432 / 790: 2,
448: 1. Each step advances k or decreases the offset.

Reads stay within [p, p + n] by `sz` (NUL at n), `b0` (the NUL is not a space) and `u0` (toupper(NUL) is not 'X').
Cut 748 reads p + k - 1 and p + k - 2; k ≥ 2 there comes from the `jle` test (cond 14 of `subF (rdi - r13) 1`)
with n < 2^62.

## Hard cuts

* 133: base 0/16 with "0x" prefix, nested `rdd(V, CU + 4·sext c) = 88` tests, and a byte store at rsp + 18.
* 748: the "0x" backtrack (`rdi - 1`, `rdi - 2`), with a conditional store of `rdi - 1` at E.
* 390: the overflow test, then a `cmov` whose `ite` stays outside `Gprs.mk` (needs `ite_mk`), then the pops.
* 171 and 604: `cdqe` leaves `Gprs.set 0` unreduced (needs a local `sk0c`, as `.set 0` is not `.set (regOf 0)`).

## Planned lemmas

`sk0c`, `ite_mk`; address steps p + k + 1 = p + (k + 1) and p + k - 1, p + k - 2; `setWidth` round trips
(8 ∘ sext 64, 8 ∘ zext 32 ∘ zext 64, 32 ∘ 64); `Tun.rd1` turns 1-byte reads into `V a`; frame `toNat` facts
(`(fsp g + d).toNat = rsp - 88 + d`); `pVf_out`, `pop_rd` for the 6 pops; `jle2` (cond 14 false → 2 ≤ k);
`ax2` ((setWidth 32 (d - 2)).toNat ≤ 34 for a valid base). Exit lemmas `eJ` per cut point (generated).
## Status and the plan for `Stl/Main.lean` (`stl_ok`)

Green (kt3211, kt3213): `Steps` (rets 429, 462), `Vc1`/`Vc2`/`Vz` (every cut's VC, with `vc_99z`/`vc_99n`,
`vc_368z`/`vc_368n`, `vc_748z`/`s`/`l` split by `E = 0`, and `vc_296x` for a byte that is neither a digit nor a
letter), `Holds` (`Kr`, `Vf`, `Env`, `Kret`, frame numbers), `Exits` (`t448`, `t432`, `t927`, `t790`), `Tail`
(`Sv`, `t390`, `t748`, `t368`, `c14_1`), `Loop` (`Sl`, `Dr`, `LpG`, `lpAll`: the digit loop from every `k ≤ n`).

Lessons: a hypothesis rewrites the goal only in the form the `wp` prints it (`== 0`, not `== 0#64`; copy the text
from `notes/Wp.lean`); split a VC by a plain equality, not by a post `(!decide P) = true`; never `subst` a register
to a literal before `stlx` (vc_296z hung > 12 min).

Left, in `Stl/Main.lean` (import `Stl.Loop`), in the style of `Ild/Main.lean`:
1. `t223` (rdi := rbx, `[rsp + 24] = rbp - 1`, `r11 = CB V`): needs `rbx = p + k`, `rbp = 0`, `r10 = CU V0`; gives
   `LpG k` through `lpAll` (`Cb V = Cb V0`, `Cu V = Cu V0` by `rdK` with `Sl.kB`, `Sv.kU`; `[rsp + 24]` is in the
   frame, `Ag.st` not needed). `t216` (r10 := CU) then `t223`.
2. `t171` (base tables at 7353696/7353760, store at `[rsp + 18]`): 745 (`cl = 0`) to `t745` (`vc_745`, then `t748`
   with `rdi = rbx`), else 216. Needs `(setWidth 32 rax).toNat ≤ 34` for the table footprints (an `Sv` field over
   all indices ≤ 34). `t150` (base 10) to `t171`. `t604` to 216 / 223.
3. `t133`: five ways (`vc_133`); the `0x` case advances `rbx` by 2 (needs `p[k] = '0'`, `p[k+1]` with `CU = 'X'`,
   so `k + 2 ≤ n` from `u0`: `CU[0] ≠ 88`). `t99` (`vc_99z`/`n` by `E = 0`): 448 / 790 / 133 with the sign stored at
   `[rsp + 20]` (frame).
4. The space loop `t80` by induction on `n - k` (as `lpAll`): `vc_80`'s 80 case gives the space bit of `p[k+1]`,
   so `p[k+1] ≠ 0` by `b0` (`B[0]` has bit 32 clear: add to `Sv` as `(rb V0 (B0 + signExtend 64 0#8 * 2#64 +
   1#64) &&& 32#8 == 0) = true`, `B0 = rdq(V0, r8 + 104)`, with `kB`-style keep fields for `r8 + 104` and the entries).
5. `t0` (`vc_0`: pushes `w1..w6` from `E.wf`, `w7` the `E` slot, `hEs : rdq(V1, S88 + 8) = rsi` by a read of the
   store) to 432 (`t432`) / 99 / 80; then `stl_ok` = `t0` at `stl_at.add 0`, as `ild_ok`.
The `Ag` invariant after `vc_0` is `Ag (Kr Kk S) (Vf V0 g0) (V1 V0 g0)`: `V1` = `fr6` + the `E` slot, outside `Kr`.
-/
