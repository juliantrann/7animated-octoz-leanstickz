import FV7z.U16.Vc
/-!
# `Utf8_To_Utf16`: the contract (PLAN.md §M, M1) — design notes, not yet written

Status: `Cnt`, `Adr`, `Spec`, `Vc`, `Cuts` build (kt943, fk 1334f52). This module still has to get `u16_ok`; the
design below was checked by hand on every edge (registers, counts, measures) but not yet built.

## The contract

`u16_ok` mirrors `U8w.u8w_ok`: `Seg.cfg` with `spAll`, the invariant `Inv`, the exit `Fx`, `vcAll`, start measure
`30 * n + 40`, then `Seg.s_ret` with `ret_335`, `pr.fra` and `rdM` (the return address is not written). The
continuation gets `FinM X.cpu.gpr V W V'`, `rdq(V', rsi) = ofNat 64 (NN …)` (`*destLen`), `KeptW`, `Agree`, the rip,
and `∃ c d s i x y u v, Z.cpu.gpr = ({X.cpu.gpr with rax := w64(1#32), rcx := c, rdx := d, rsi := s, rdi := i,
r8 := x, r9 := y, r10 := u, r11 := v} : Gprs).set 4 (rsp + 8)`.

- `FinM g₀ V₀ W V`: `V x = V₀ x` for every `x` outside the 60 bytes below `rsp`, the `W` bytes from `rdi` (`dest`)
  and the 8 bytes at `rsi` (`destLen`).
- `structure Pr F Wl g₀ n W : Prop` (all bounds on `toNat`): `lim : rcx = rdx + ofNat 64 n`, `pn : rdx + n < 2^64`,
  `sp : 64 ≤ rsp`, `spT : rsp + 8 ≤ 2^64`, `dT : rdi + W ≤ 2^64`, `pT : rsi + 8 ≤ 2^64`,
  `sDS : rdi + W + 60 ≤ rsp ∨ rsp + 8 ≤ rdi`, `sDp : rdi + W ≤ rdx ∨ rdx + n ≤ rdi`,
  `spS : rdx + n + 60 ≤ rsp ∨ rsp ≤ rdx`, `sPS : rsi + 56 ≤ rsp ∨ rsp + 8 ≤ rsi`,
  `fa : ∀ k < n, ∀ i < 1, Foot F.data (Addr.add (rdx + ofNat 64 k) i)`,
  `fw : ∀ j < W, ∀ i < 1, Foot Wl (Addr.add (rdi + ofNat 64 j) i)`,
  `fst`/`fsr : ∀ x, rsp ≤ x + 60 → x < rsp → Foot Wl x` / `Foot F.data x`, `fra : ∀ i < 8, Foot F.data (rsp + i)`,
  `fP : ∀ i < 8, Foot Wl (rsi + i)`.
- `Bud g₀ V₀ n W := g₀.rdi ≠ 0 → 4 * NN g₀ V₀ n ≤ W` (the characters fit in `dest`).

## Definitions

`Fl g₀ := w32(g₀.r8)`; `Uf := !zr (Fl &&& 1#32)`, `Z2 := zr (Fl &&& 2#32)`, `Z4 := zr (Fl &&& 4#32)` (abbrevs);
`Ct g₀ V₀ n k := cnt V₀ g₀.rdx n (Uf g₀) (Z2 g₀) (Z4 g₀) k`, `NN := Ct … 0`, `Rm … k r := rem …` (defs, atoms for
omega); `Ib g₀ V₀ n k j m e d := inn V₀ g₀.rdx n k (Uf g₀) (128#32 >>> j) m e d` (abbrev);
`FR g₀ V₀ W V := Fr (Vs1 g₀ V₀) g₀.rdi W V`;
`Gu g₀ a c d bp s i r8 r9 r11 := ⟨a, c, d, g₀.rdi, S6 g₀.rsp, bp, s, i, r8, r9, g₀.rcx, r11, w64(Fl &&& 2#32),
w64(128#32), w64(65533#32), w64(Fl &&& 1#32)⟩` (abbrev). `p := g₀.rdx`; `r11 = ofNat 64 c`, `c` the count so far.

`Inv g₀ V₀ n W ℓ μ g V`, 11 disjuncts (`D1` = `Or.inl`, `Dk` = `Or.inr`^(k-1) `Or.inl`, `D11` = `Or.inr`^10):
1. `ℓ = 0 ∧ μ = 30n+40 ∧ g = g₀ ∧ V = V₀`.
2. 116 (`o = 30`, `k ≤ n`), 125 (`o = 29`, `k < n`): `μ = 30(n-k)+o`, `c + Ct k = NN`, `FR`,
   `g = Gu a cx (p+k) bp s i r8 r9 c`.
3. 109 (`o = 2`), 141 (`o = 3`, `rdi ≠ 0`): `k < n`, `c + 1 + Ct (k+1) = NN`, `g = Gu a cx d bp s i r8 (p+(k+1)) c`.
4. 174: `k < n`, `1 ≤ j ≤ 3`, `μ = 30(n-k)+28`, `c + Rm k (Ib k j (j-1) 0 (d0 (by8 V₀ p k) j)) = NN`,
   `g = Gu a (w64(ofNat 32 j)) (w64(d0 (by8 V₀ p k) j)) bp s i r8 (p+(k+1)) c`.
5. 209: `ms + e + 1 = j ≤ 3`, `k+1+e ≤ n`, `μ = 30(n-k)+24-5e`, `c + Rm k (Ib k j ms e dd) = NN`,
   `g = Gu a (w64(128#32>>>j)) (w64 dd) bp (w64(ofNat 32 e)) (p+(k+1+e)) (w64(ofNat 32 ms)) (p+(k+1)) c`.
6. 192 (`o = 22`), 201 (`o = 21`, `ms ≠ 0`): as 5 but `k+1+e < n`, `μ = 30(n-k)+o-5e`, `rsi = w64(ofNat 32 (e+1))`,
   count `c + Rm k (if ms = 0 then .ok dd (e+1) else Ib k j (ms-1) (e+1) dd) = NN` (`inn_go`'s right side).
7. 272: `e ≤ 3`, `k+1+e ≤ n`, `μ = 30(n-k)+8`, `c + Rm k (.err e) = NN`, `w32(s) = ofNat 32 e`,
   `g = Gu a cx d bp s i r8 (p+(k+1)) c`.
8. 295 (`o = 33`, `rdi ≠ 0`), 299 (`o = 32`): `k ≤ n`, `c + 1 + Ct k = NN`, `g = Gu a cx (p+k) bp s i r8 r9 c`.
9. 392: `(big dd ∧ q = 2) ∨ (¬big dd ∧ q = 1)`, `1 ≤ e ≤ 3`, `k+1+e ≤ n`, `μ = 30(n-k)+8`,
   `c + q + Ct (k+1+e) = NN`, `g = Gu a cx (w64 dd) bp (w64(ofNat 32 e)) i r8 (p+(k+1)) c`.
10. 492 (`o = 7`, `q = 2`), 409 (`o = 7`, `q = 1`), 413 (`o = 6`, `q = 0`): `1 ≤ e ≤ 3`, `k+1+e ≤ n`,
   `c + q + Ct (k+1+e) = NN`, `g = Gu a cx d bp (w64(ofNat 32 e)) i r8 (p+(k+1)) c`.
11. 312: `μ = 0`, `g.rsp = S6 g₀.rsp`, `g.r11 = ofNat 64 NN`, `Fr (Vs0 g₀ V₀) g₀.rdi W V ∨ FR`.

`Fx … j g V := j = 335 ∧ FinM ∧ rdq(V, g₀.rsi) = ofNat 64 NN ∧ ∃ c d s i x y u v, g = {g₀ with rax := w64(1#32), …}`;
`Nx … μ : Post := fun j g _ V => (∃ μ' < μ, Inv … j μ' g V) ∨ Fx … j g V`. Every edge lowers `μ` (checked).

## Lemmas to write (grep first; `o1` and `b8` are taken in this namespace)

- Intro lemmas `i2`–`i11`: each concludes `Nx … μ ℓ (Gu g₀ …) fl V` from `hl`, `hμ`, `hc`, `hF` (registers by
  unification); `i11` takes a generic `g` with `hs`, `hr`. `i9` cases `big dd` itself (`rm_ok1`/`rm_ok2`).
- Counts: `ct_ge`, `ct_a`, `ct_b`, `ct_c` (`unfold Ct Rm; rw [cnt_lt hk, step_c h1 h2, hj] <;> rfl`);
  `rm_fin (h : fin k (Z2 g₀) (Z4 g₀) r = (a, b)) : Rm … k r = a + Ct … b` (`show` the unfolded sum, `rw [h] <;> rfl`),
  then `rm_e1`/`rm_e2`/`rm_esc`/`rm_ok1`/`rm_ok2` as `rm_fin (by show <fin's branch> = _; rw [h, cond_true…])`
  (never `simp [h]` with `h : Z2 g₀ = true`: it also rewrites `cnt`'s argument and `rfl` then fails).
- `ib_end`, `ib_bad`, `ib_ovl`, `ib_sur`, `ib_hi`, `ib_go` (`e ≠ 0`), `ib_g0` (`e = 0`) from `inn_*`; pass `(m := …)`
  to `ib_g0`, its `hs`/`hl` lambdas do not fix `m`.
- Decisions by `rcases (by omega : x = 0 ∨ … ∨ x = 3) with rfl | … <;> revert h <;> decide`: `e0t`/`e0f`
  (`ofNat 32 e + 1#32 = 1#32`), `m1t`/`m1f`, `m3t`/`m3f` (`w32(w64(ofNat 32 ms) + 1#64) = 3#32`), `z0t`/`z0f`,
  `c174`, `fm1`, `msub` (post-`sw_64_32` forms); `and1`, `xz`, `xz32`, `wo`, `oc`, `ske`, `ske'`, `adv1'`, `a0`.
- Memory: `pk`/`pk'` (`pinj1`, `pr.lim`), `rdS` (the byte: `rdF` with `sDp`, then `vs1_out` with `spS`), `rdFl`
  (`k60`, `rdF`, `vs1_fl`), `tsA`, `rdD`, `rdP`, `rdM`; footprints `fS`, `fR`, `fDj`, `fD` (`m4`), `fD8` (`m4`, `ad4`);
  frame `frM`, `frM8` (`frS pr.dT`).
- Per cut `v0`…`v492`: `refine vc_ℓ (g := Gu …) ?_ …`, `all_goals dsimp only [Gu]`, per branch: intro, `pk'`, `rw [rdS
  …]`, `try simp only [sw_64_32] at … ⊢`, `obtain rfl := e0f …`, `have hne : ¬ k+1+e = n := by omega` (never `by
  omega` as a `rw` argument with implicits open), rewrite `hc`, rewrite the goal's register forms, `exact iX …`.
  `v312` generic in `Vb` (`hbo`, `hb`); `vcAll` instantiates it with `vs0_out`/`rfl` or `vs1_out`/`vs1_rd`.
- `attribute [local irreducible]` on all 17 `W_*` before `vcAll`.

## Next step

Write the above here, triage `FV7z.U16.Holds -- FV7z.U16.u16_ok` on a lane, then import `Cnt`, `Adr`, `Spec`, `Vc`,
`Holds` from `FV7z.lean`.
-/
