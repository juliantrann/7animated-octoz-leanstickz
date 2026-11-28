/-!
# Design of the `_nl_intern_locale_data` proof (0x615210, 485 bytes)

This file holds no declarations yet. It records the plan for `Ild/Holds.lean` (theorem `ild_ok`), on top of the
generated `Ild/Code`, `Pats`, `Blocks*` and `Cuts` (`tools/blk_gen.py`, entry `ild`). `Ild/notes/Wp.lean` holds
the weakest-precondition text of the cut points, as `wpx` prints it.

## The code

`_nl_intern_locale_data (category = edi, data = rsi, datasize = rdx)`; the frame is 6 pushes and `sub rsp, 8`,
so S - 56 with S = rsp at the entry. The registers after the prologue: `ebp` = c, `rbx` = data, `r12` = datasize,
`r13` = N (u32 at data + 4), `r14` = sext c.
* 0 → 248 (error): datasize ≤ 7. Otherwise the magic (u32 at data) is compared at 65: 0x20051017 for c = 3,
  else 0x20090720 for c = 0 (`cmove`), else c ^ 0x20031115.
* 65 → 248 (error): a wrong magic, N < `_nl_category_num_items[c]` (8 bytes at 0x6ef020 + 8c), or
  4N + 8 ≥ datasize. Otherwise 122: `call malloc` (0x633160) with rdi = 8N + 64.
* 127, after `malloc`: rax = 0 → 264 (return NULL; unreachable with `Mal.AtHW`, p ≥ 0x7a9010). Otherwise the
  header stores at p + 8, 16, 32, 40, 48 and the u32 N at p + 56. N = 0 → 264 (return p).
* 196, the loop head, cnt = rcx < N: idx = u32 at data + 8 + 4cnt; idx > datasize → 240 (free). Then
  `cmp ebp, 12; ja 435` (unreachable for c ≤ 12), then `jmp r8` through the table `ild_jt` at 0x6ee9e0 (13 entries;
  `ild_cases` = [435, 420, 402, 391, 380, 279, 435, 358, 350, 318, 279, 228, 369]).
* the cases check cnt against the bound of the category's `_nl_value_types` table. The bounds lim c for
  c = 0..12 are [85, 5, 158, 18, 45, 4, -, 2, 6, 12, 4, 1, 15]. cnt > lim c → 240, except c = 0: cnt > 85 → 299.
  435 is the case of c = 0 and of c = 6 (LC_ALL); `test ebp, ebp; jne 454` → `__assert_fail` (0x1c6 is a stop),
  unreachable for c ≠ 6.
* 288: T = 8 bytes at 0x7804c0 + 8·sext c (`_nl_value_types[c]`); u32 at T + 4cnt = 5 (a word) → 336, else 299.
* 299 (a string): the 8 bytes data + idx stored at p + 64 + 8cnt → 307.
* 336 (a word): idx & 3 ≠ 0 → 240; else the u32 at data + idx (it may lie up to 4 bytes past datasize, as in
  glibc) stored at p + 64 + 8cnt → 307.
* 307: cnt + 1 = N → 264 (return p), else → 196.
* 240: `mov rdi, rax`, then 243: `call free` (0x633750); returns to 248.
* 248: errno (fs:-0x48, `fb + 18446744073709551544#64`) = 22 (EINVAL), rax = 0 → 264.
* 264: `add rsp, 8`, the pops, then the `ret` at 278.

## Spec (planned `ild_ok`)

Preconditions:
* c = setWidth 32 rdi with c.toNat ≤ 12 and c ≠ 6;
* datasize ≤ 2^30, so 8N + 64 ≤ 2^32 for `Mal.MalB`;
* the data: `Foot F.data` on [data, data + datasize + 4), lying where `malloc` keeps bytes, i.e.
  a < 0x792aa0 (7940768) ∨ hi ≤ a ∧ (a + 272 < S ∨ S ≤ a);
* the frame: `Foot Wl` on [S - 280, S) (the call's 224 bytes for `Mal.AtHW` plus the pushes), `Foot F.data` on
  [S - 56, S + 8); hi + 280 ≤ S; 7940768 ≤ hi;
* the tables: `Foot F.data` on 0x6ef020 + 8c (8 bytes), on 0x7804c0 + 8c (8 bytes) and on T .. T + 4(lim c + 1)
  with T + 4(lim c + 1) ≤ 7940768; the jump table's 52 bytes equal `ild_jt` (as `Pcs.Pe.jt`, lemmas as Pcs's
  `jt_case`, `tg`);
* errno: `Foot Wl` on its 4 bytes;
* `malloc` as `Mal.AtHW prof F Wl L o fb hi 0x633160 Pm`, with `Pm (k + B)` for every memory equal to the entry's
  outside [S - 64, S) (as `Sdp.sdp_ok`'s `hPm`), and `MalB (8N + 64) B`;
* `free` as a continuation hypothesis `kf` (as `Stb.stb_ok`): at `free`'s entry with rdi = p, rsp = S - 64, the
  return address `ild_at + 248` at S - 64, `Pm k` of the memory (it differs from `malloc`'s result only in the block
  and in the frame, above hi); given the run from the return (rsp = S - 56, `rbx`, `rbp`, `r12`–`r15` kept, the
  bytes from S - 48 to S + 8 kept) on to the end, `GoG`.

Post (the continuation `kk`): at the return address, rsp = S + 8, `rbx`, `rbp`, `r12`–`r15` as at the entry, and
rax = 0 ∨ (8032272 ≤ rax ∧ `Pm k` of the final memory).

## Proof plan

* pre-call: `(c_0 prof fb).run`, then `(c_65 prof fb).run` (no loop), exits 248 and 122; `pVf` = the pushes.
* `from264`: W_264 (pops), then `c.s_ret` and `kk`; `from248`: W_248 (errno), then `from264` with rax = 0.
* the call at 122: `c.s_call`, then `Mal.AtHW`; its continuation gives p, V₂.
* the loop: `cfgAt` over the cut points 127, 196, the cases (228, 279, 318, 350, 358, 369, 380, 391, 402, 420, 435),
  288, 299, 307 and 336, with `Fin` at 240 (to `free`) and 264 (success). Invariant: rsp = S - 56, rax = p,
  rcx = cnt, rbx = data, r12 = datasize, r13 = N, r14 = sext c, rbp = r9 = zext c, r10 = 0x7804c0,
  rdx = 0x6ee9e0; memory = V₂ outside [p, p + 8N + 64); at a case cut ℓ = `ild_cases[c]`; at 288 cnt ≤ lim c; at
  336 the type is 5. Measure 10(N - cnt) plus 9 (127), 8 (196), 7 (cases), 6 (288), 5 (336), 4 (299), 3 (307).
* 240: `(c_240 prof fb).run`, `c.s_call` to `free`, then `kf`, whose continuation is `from248`.
-/
