import FV7z.U16.Ex4
/-!
# `Utf8_To_Utf16`: the contract (PLAN.md §M, M1)

`vcAll` (each cut point's `W_ℓ` from `Inv`, by `v0`…`v492` in `Ex1`–`Ex4`) and `u16_ok`. The invariant and its
lemmas are in `Inv`; the design, as built:

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
-/

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

variable {F : Footprint} {Wl : List Rgn}

/-- The return address: at the end as at the entry (`FinM`, apart from `dest`, `destLen` and the 60 bytes). -/
theorem u4rM {g₀ : Gprs} {V₀ V : Addr → Byte} {n W : Nat} (pr : Pr F Wl g₀ n W) (hM : FinM g₀ V₀ W V) :
    rdq(V, g₀.rsp) = rdq(V₀, g₀.rsp) := by
  refine congrArg (ofBytesLE 64) (List.map_congr_left fun x hx => ?_)
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have e : (Addr.add g₀.rsp i).toNat = g₀.rsp.toNat + i := tA (by have := pr.spT; omega)
  have := pr.sDS; have := pr.sPS
  exact hM _ (by omega) (by omega) (by omega)

/-! ## The cut points' conditions -/

theorem vcAll {g₀ : Gprs} {V₀ : Addr → Byte} {n W : Nat} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W) (ℓ m : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ n W ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ n W m) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨o, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, k, hk, h5, rfl, c, hc, hF, a, cx, bp, s, i, x, y, rfl⟩ |
    ⟨o, ⟨rfl, rfl⟩ | ⟨rfl, rfl, h0⟩, k, hk, rfl, c, hc, hF, a, cx, d, bp, s, i, x, rfl⟩ |
    ⟨rfl, k, hk, j, hj1, hj3, rfl, c, hc, hF, a, bp, s, i, x, rfl⟩ |
    ⟨rfl, k, j, ms, e, hj, hj3, hk, rfl, c, dd, hc, hF, a, bp, rfl⟩ |
    ⟨o, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, k, j, ms, e, hj, hj3, hk, h5, rfl, c, dd, hc, hF, a, bp, rfl⟩ |
    ⟨rfl, k, e, he, hk, rfl, c, hc, hF, a, cx, d, bp, s, i, x, hs, rfl⟩ |
    ⟨o, ⟨rfl, rfl, h0⟩ | ⟨rfl, rfl⟩, k, hk, rfl, c, hc, hF, a, cx, bp, s, i, x, y, rfl⟩ |
    ⟨rfl, k, e, q, dd, hq, he1, he3, hk, rfl, c, hc, hF, a, cx, bp, i, x, rfl⟩ |
    ⟨o, q, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩, k, e, he1, he3, hk, rfl, c, hc, hF, a, cx, d, bp, i,
      x, rfl⟩ |
    ⟨rfl, rfl, hs, hr, hF | hF⟩
  · exact v0 pr
  · exact v116 pr hk hc hF
  · exact v125 pr hB (h5 rfl) hc hF
  · exact v109 hk hc hF
  · exact v141 pr hB h0 hk hc hF
  · exact v174 hk hj1 hj3 hc hF
  · exact v209 pr hj hj3 hk hc hF
  · exact v192 pr hB hj hj3 hk hc hF
  · exact v201 hj hj3 hk (h5 rfl) hc hF
  · exact v272 pr hB he hk hc hF hs
  · exact v295 pr hB h0 hk hc hF
  · exact v299 pr hk hc hF
  · exact v392 pr hB hq he1 he3 hk hc hF
  · exact v492 he1 he3 hk hc hF
  · exact v409 he1 he3 hk hc hF
  · exact v413 he1 he3 hk hc hF
  · exact v312 pr (fun _ _ => rfl) (fun x hx => vs0_out pr.sp hx) hs hr hF
  · exact v312 pr (fun _ hc => vs1_rd pr.sp hc) (fun x hx => vs1_out pr.sp hx) hs hr hF

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {n W : Nat}

/-- `Utf8_To_Utf16 (dest, destLen, src, srcLim, flags)` from its entry, with what the caller gives (`Pr`) and the
characters fitting in `dest` (`Bud`): at the return address, the return address popped, the memory as it was but at
the 60 bytes below `rsp`, the `W` bytes from `dest` and `*destLen`, `*destLen` the count `NN`, `eax = 1`, the
callee-saved registers back, `rcx`, `rdx`, `rsi`, `rdi`, `r8`–`r11` some values. -/
theorem u16_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L u16_at u16) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u16_at) (pr : Pr F Wl X.cpu.gpr n W)
    (hB : Bud X.cpu.gpr V n W)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), FinM X.cpu.gpr V W V' →
      rdq(V', X.cpu.gpr.rsi) = BitVec.ofNat 64 (NN X.cpu.gpr V n) → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∃ c d s i x y u v, Z.cpu.gpr = ({ X.cpu.gpr with
          rax := w64(1#32), rcx := c, rdx := d, rsi := s, rdi := i, r8 := x, r9 := y, r10 := u,
          r11 := v } : Gprs).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V n W ℓ m g V')
    (fun j g _ V' => Fx X.cpu.gpr V n W j g V') (fun ℓ m g f V' h => vcAll pr hB ℓ m g f V' h) ?_
    (30 * n + 40) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨rfl, hM, hD, c', d', s', i, x, y, u, v, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hra' : rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ := by rw [u4rM pr hM]; exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_335 _) (by rw [hsY]; exact pr.fra) hin₂ h₂
    (by rw [hsY]; exact hra') ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hM hD hKZ hAZ hrZ ⟨c', d', s', i, x, y, u, v, by rw [hgZ, hsY, hgY]⟩

end FV7z.U16
