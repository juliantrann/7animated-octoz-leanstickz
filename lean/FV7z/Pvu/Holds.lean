import FV7z.Pvu.Cuts
/-!
# `CPropVariant::operator=(UInt32)` (PLAN.md §M, M1): design notes, no proof yet

7-Zip 26.06's `NWindows::NCOM::CPropVariant::operator=(UInt32)` at `0x457430` in `7zzs`, `p` = `rdi`, `u` = `esi`:
`push r12; mov r12, rdi; push rbx; mov ebx, esi; sub rsp, 8; cmp word [rdi], 19; je 37`; at 22 `call 0x457130`
(`InternalClear`, `FV7z/Pic`); at 27 `mov edx, 19; mov [r12], dx`; at 37 `xor eax, eax; mov [r12 + 8], ebx;
mov [r12 + 2], ax; add rsp, 8; mov rax, r12; pop rbx; pop r12; ret` (60). Blocks and cuts (0, 27, 37) are generated
and build (kt632).

The wpx goals (kt632 probe, `wpx [W_0, o0]`, `[W_27, o1]`, `[W_37, o2]`):
- `W_0`: `Foot Wl` of `rsp - 8` and `rsp - 8 - 8` (8 bytes), `Foot F.data` of `rdi` (2 bytes); then
  `decide (rdw(Vp, rdi) = 19#16) = true → Q 37 …` and `= false → Q 22 …`, both with
  `{ g with rbx := sw64 (sw32 rsi), rsp := rsp - 8 - 8 - 8#64, r12 := rdi }` and
  `Vp = Vst (Vst V (rsp - 8) (toBytesLE r12 8)) (rsp - 8 - 8) (toBytesLE rbx 8)`.
- `W_27`: `Foot Wl` of `r12` (2 bytes) ∧ `Q 37 { g with rdx := sw64 19#32 } (rfz f)
  (Vst V r12 (toBytesLE (sw16 19#32) 2))`.
- `W_37`: `∀ af,` `Foot Wl ((r12 + 8#64).add i)` (4), `Foot Wl ((r12 + 2#64).add i)` (2), `Foot F.data` of
  `rsp + 8#64` and `rsp + 8#64 + 8` (8) ∧ `Q 60` with `rax := r12`, `rbx`/`r12` the loads at `rsp + 8#64` and
  `rsp + 8#64 + 8` of `Vs = Vst (Vst V (r12 + 8#64) (toBytesLE (sw32 rbx) 4)) (r12 + 2#64)
  (toBytesLE (sw16 (sw32 rax ^^^ sw32 rax)) 2)`, `rsp := rsp + 8#64 + 8 + 8`.

Plan (next step: write it, triage on tri8 with `-- FV7z.Pvu.pvu_ok`):
- `vc_0`, `vc_27`, `vc_37` with an opaque `Q` and hypotheses `h37`/`h22` (as `Caa.vc_0`), not a lambda post: wpx's
  simp would rewrite an `x = x` post away. Close `vc_0` by `⟨w1, w2, r0, fun h => h37 (of_decide_eq_true h) _,
  fun _ => h22 _⟩`.
- No `cfgAt`: chain by hand. `(c_0 prof).run`, then for 37 a local `have k37` (both ways meet there); the call by
  `(SpAt.callK c hin (lt_len _) (cl22 _) hinC (Pic.lt_len _) tg22 hFn).run (Q27 …)` with `Q27` a `def` (keeps
  `dsimp only [CallK]` off it), closed by `And.intro rfl hR`; `rel` = 18446744073709550821, `call` bytes
  `e8 e5 fc ff ff`.
- Callee `FnK … Pic.pic_at T (RK A)`, `RK A g W g' W' := Fkp g W W' ∧ Rpl.Cso g g' ∧ A W'`, `Fkp`: the 32 bytes
  above the return address's slot (`[s - 24, s + 8)`, not Rpl's 64). `hT : ∀ g W, g.rsp = s - 8 - 8 - 8#64 - 8 →
  g.rdi = p → (W = V outside [s - 32, s)) → T g W`.
- `AIns A s p`: `A` ignores the frame `[s - 32, s)` and the variant `[p, p + 12)`; `p` apart from `[s - 32, s + 8)`.
- At 37: `Sh` (registers, existential `rax`…`r11`) and `M37` (`rdq` at `s - 8`, `s - 8 - 8`, `s` as after the
  `push`es, `rdw(V', p) = 19#16`, `A V'`). Frame reads through a callee: agreement on `[s - 16, s + 8)` then
  `rd_eq` (`fr3`). `(Gc X).rsp + 8 = s - 8 - 8 - 8#64` is `BitVec.sub_add_cancel`; pops' addresses by
  `simp only [BitVec.sub_add_cancel]`.
- Post `k`: `A V'`, `rdw(V', p) = 19#16`, `rdw(V', p + 2#64) = 0#16` (`BitVec.xor_self`, then `decide`),
  `rdd(V', p + 8#64) = sw32 u` (`sw_64_32`), `Z.gpr = { X.gpr with rax := p, rcx…r11 := ∃, rsp := s + 8 }`.
- `rdw` is not in `Tun.Inv`: a `local notation`.
-/
