import FV7z.Dr2.Cuts
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.BlkOps12
import FV7z.Tun.Inv
import FV7z.Raf.Holds
/-!
# `LzmaDec_DecodeReal2` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_DecodeReal2 (p, limit, bufLimit)` at `0x42b5b0` in `7zzs` (`C/LzmaDec.c`; `objdump -d`),
for the decoder at `p` = `rdi`: `push rbx`; with `checkDicSize` (the 4 bytes at `p + 68`) 0, `limit` (`rsi`) cut to
`dicPos + (dicSize - processedPos)` (`p + 40`, `p + 4`, `p + 64`) when it is past it (`cmova`); `rdi = p`;
`call LZMA_DECODE_REAL` (40, to `0x6d4040`, `LzmaDec_DecodeReal_3`); then, `checkDicSize` still 0 and
`processedPos ≥ dicSize`, `checkDicSize = dicSize`; `pop rbx; ret` (64).

The callee's contract (`Lzma.dr3_holds`) wants `LzmaDec.Pre` at the call, which only the caller can show: `dr2_ok`
takes the callee as a hypothesis (`kf`), as `Lap.lap_ok` does, for the caller to discharge (`Seg.enterK`).

- `lim`: the cut limit; `Rd`: the decoder's bytes the code reads, in `F.data`.
- `vc_0`, `vc_37`, `vc_45`, `vc_63`: the cut points' conditions.
- `dr2_ok`: from the entry, through the callee (`kf`), to the return address (`kr`): the registers as after the
  callee but `rdx`, `rbx` (back to the entry's) and `rsp`; the bytes as after the callee but `[p + 68, p + 72)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dr2
set_option maxRecDepth 100000

/-- The `call` to `LZMA_DECODE_REAL`. -/
def pcall : List Byte := [0xe8, 0x63, 0x8a, 0x2a, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 2787939] 5) := by dec_rfl
theorem wc_40 : pcall <+: dr2.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat dr2 40 (FV7z.mk .call 64 [.rel 2787939] 5) :=
  Dec.shift (j := 40) (k := 0) (pcall_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : dr2_at.add (40 + 5) + BitVec.ofNat 64 2787939 = (0x6d4040#64 : Addr) := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_64 : pret <+: dr2.drop 64 := by decide +kernel
theorem ret_64 (feat : Features) : Dec feat dr2 64 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 64) (k := 0) (pret_0 feat) w_64 (Nat.zero_le _)

/-- `dicPos + (dicSize - processedPos)` of the decoder at `p`: the limit the code passes when `checkDicSize` is 0
and the given one is past it. -/
def lim (V : Addr → Byte) (p : Addr) : BitVec 64 :=
  rdq(V, p + 40#64) + (rdd(V, p + 4#64) - rdd(V, p + 64#64)).setWidth 64

/-- The decoder's bytes the code reads: `checkDicSize`, `dicPos`, `dicSize`, `processedPos`. -/
def Rd (F : Footprint) (p : Addr) : Prop :=
  (∀ i < 4, Foot F.data (Addr.add (p + 68#64) i)) ∧ (∀ i < 8, Foot F.data (Addr.add (p + 40#64) i)) ∧
  (∀ i < 4, Foot F.data (Addr.add (p + 4#64) i)) ∧ (∀ i < 4, Foot F.data (Addr.add (p + 64#64) i))

variable {F : Footprint} {Wl : List Rgn}

/-- The entry to the `mov rdi, rbx` (37): `rbx` pushed, `rbx = p`, the limit `rsi` the given one or `lim`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hr : Rd F g.rdi)
    (hs : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hQ : ∀ (a c si di : BitVec 64) fl,
      (si = g.rsi ∨ si = lim (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi) →
      Q 37 { g with rax := a, rcx := c, rsi := si, rdi := di, rbx := g.rdi, rsp := g.rsp - 8 } fl
        (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h68, h40, h4, h64⟩ := hr
  dsimp only at h68 h40 h4 h64 hs hQ ⊢
  wpx [W_0, W_11, o0, o1]
  repeat' (first
    | exact hs | exact h68 | exact h40 | exact h4 | exact h64 | exact trivial
    | exact hQ _ _ _ _ _ (.inl rfl) | exact hQ _ _ _ _ _ (.inr rfl) | (with_reducible apply And.intro) | intro _
    | split)

/-- `mov rdi, rbx`. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hQ : ∀ fl, Q 40 { g with rdi := g.rbx } fl V) : W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hQ ⊢
  wpx [W_37, o2]
  repeat' (first | exact hQ _ | (with_reducible apply And.intro) | intro _)

/-- After the `call` (45) to the `pop rbx` (63): `checkDicSize = dicSize` or the bytes kept; `rdx` changed. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hr : Rd F g.rbx)
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 68#64) i)) (hQ : ∀ d fl, Q 63 { g with rdx := d } fl V)
    (hQ' : ∀ d fl, Q 63 { g with rdx := d } fl (Vst V (g.rbx + 68#64) (toBytesLE rdd(V, g.rbx + 4#64) 4))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h68, -, h4, h64⟩ := hr
  dsimp only at h68 h4 h64 hw hQ hQ' ⊢
  wpx [W_45, W_52, W_60, o3, o4, o5, Op.cmpmr]
  repeat' (first
    | exact hQ _ _ | exact hQ' _ _ | exact h68 | exact h4 | exact h64 | exact hw | exact trivial
    | (with_reducible apply And.intro) | intro _)

/-- `pop rbx`. -/
theorem vc_63 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (hQ : ∀ fl, Q 64 { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) : W_63 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hQ ⊢
  wpx [W_63, o6]
  repeat' (first | exact hQ _ | exact hl | (with_reducible apply And.intro) | intro _)

/-! ## The run -/

/-- The store into `checkDicSize` changes only its 4 bytes. -/
theorem ost68 {V : Addr → Byte} {b : Addr} {bs : List Byte} (hn : bs.length = 4) (hb : b.toNat + 72 ≤ 2 ^ 64) :
    Raf.Out (b.toNat + 68) (b.toNat + 72) V (Vst V (b + 68#64) bs) := by
  have ht : (b + 68#64).toNat = b.toNat + 68 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have h := Raf.Out.vst (V := V) (a := b + 68#64) hn (by omega)
  rw [ht] at h
  exact h.mono (Nat.le_refl _) (by omega)

theorem sb8 (S : Addr) (h : 8 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega
theorem su8 (S : Addr) : S - 8 + 8 = S := by bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- `LzmaDec_DecodeReal2`: see the module doc. The callee `LZMA_DECODE_REAL` (at `eT.add tT` = `0x6d4040`) is the
hypothesis `kf`: entered with `rdi = p`, `rsi` the limit (the given one or `lim`), the frame `[rsp - 16, rsp)` the
saved `rbx` and the return address; back at 45 with `rsp`, `rbx` as at its entry, the saved `rbx` and the return
address kept, and `Pc`. -/
theorem dr2_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dr2_at dr2)
    {eT : Addr} {codeT : List Byte} {tT : Nat} (hinT : CodeIn L eT codeT) (hT : tT < codeT.length)
    (htT : eT.add tT = 0x6d4040#64)
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = dr2_at) (hr : Rd F X.cpu.gpr.rdi)
    (hw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 68#64) i)) (hp : X.cpu.gpr.rdi.toNat + 72 ≤ 2 ^ 64)
    (hs8 : 8 ≤ X.cpu.gpr.rsp.toNat) (hsS : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsep : X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 68 ∨
      X.cpu.gpr.rdi.toNat + 72 ≤ X.cpu.gpr.rsp.toNat - 8)
    (hw1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hw2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    {Pc : State → (Addr → Byte) → Prop}
    (kf : ∀ (Y : State) (t' : Nat) (a c si : BitVec 64),
      (si = X.cpu.gpr.rsi ∨ si = lim (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi) →
      KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE (dr2_at.add (40 + 5)) 8)) →
      Y.cpu.rip = eT.add tT →
      Y.cpu.gpr = ({ X.cpu.gpr with
          rax := a, rcx := c, rsi := si, rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8 } : Gprs).set 4
        (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = dr2_at.add 45 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = rdq(V, X.cpu.gpr.rsp) → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (V'' : Addr → Byte) (t' : Nat) (d : BitVec 64), Pc Z V' →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' →
      Raf.Out (X.cpu.gpr.rdi.toNat + 68) (X.cpu.gpr.rdi.toNat + 72) V' V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rdx := d, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have e8 := sb8 X.cpu.gpr.rsp hs8
  -- to the `mov rdi, rbx`
  refine (c_0 prof).run c hin (fun j g _ V' => j = 37 ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) ∧ ∃ a c si di : BitVec 64,
        (si = X.cpu.gpr.rsi ∨ si = lim (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi) ∧
        g = { X.cpu.gpr with
          rax := a, rcx := c, rsi := si, rdi := di, rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8 })
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hr hw1 fun a cc si di _ hsi => ⟨rfl, rfl, a, cc, si, di, hsi, rfl⟩) ?_
  rintro j g fl V₁ ⟨rfl, rfl, a, cc, si, di, hsi, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine (c_37 prof).run c hin (fun j g' _ V' => j = 40 ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) ∧ g' = { Y.cpu.gpr with rdi := Y.cpu.gpr.rbx })
    hKY hAY hrY (vc_37 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j g fl V₂ ⟨rfl, rfl, rfl⟩ Y2 t₂ hK2 hA2 hr2 hg2 -
  have hs2 : Y2.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg2, hgY]; try rfl
  -- `call LZMA_DECODE_REAL`
  refine c.s_call_x hK2 hA2 hin (lt_len (by decide)) hr2 (call_40 _) hinT hT (by rw [htT]; exact tgt_40)
    (by rw [hs2]; exact hw2) ?_
  rintro Y3 t₃ hK3 hA3 ⟨hr3, hg3⟩
  rw [hs2] at hA3
  refine kf Y3 t₃ a cc si hsi hK3 hA3 hr3 (by rw [hg3, hs2, hg2, hgY]; try rfl) ?_
  intro Z V' t₄ hKZ hAZ hrZ hzs hzb hsb hsr hPc
  -- after the `call`: `checkDicSize`
  refine (c_45 prof).run c hin (fun j g _ V'' => j = 63 ∧
      Raf.Out (X.cpu.gpr.rdi.toNat + 68) (X.cpu.gpr.rdi.toNat + 72) V' V'' ∧ ∃ d, g = { Z.cpu.gpr with rdx := d })
    hKZ hAZ hrZ (vc_45 (by rw [hzb]; exact hr) (by rw [hzb]; exact hw) (fun d _ => ⟨rfl, fun _ _ => rfl, d, rfl⟩)
      fun d _ => ⟨rfl, by rw [hzb]; exact ost68 (toBytesLE_length _ _) hp, d, rfl⟩) ?_
  rintro j g fl V₃ ⟨rfl, hO, d, rfl⟩ Y4 t₅ hK4 hA4 hr4 hg4 -
  have hs4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg4]; exact hzs
  -- `pop rbx`
  refine (c_63 prof).run c hin (fun j g _ V'' => j = 64 ∧ V'' = V₃ ∧
      g = { Y4.cpu.gpr with rbx := rdq(V₃, Y4.cpu.gpr.rsp), rsp := Y4.cpu.gpr.rsp + 8 })
    hK4 hA4 hr4 (vc_63 (by rw [hs4]; exact hl1) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j g fl V₄ ⟨rfl, rfl, rfl⟩ Y5 t₆ hK5 hA5 hr5 hg5 -
  have hs5 : Y5.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg5]; show Y4.cpu.gpr.rsp + 8 = _; rw [hs4]; exact su8 _
  have hrd0 : rdq(V₃, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hO.rd (x := X.cpu.gpr.rsp) (n := 8) hsS (by omega), hsr, hra]
  have hrb : rdq(V₃, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [hO.rd (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [e8]; omega) (by rw [e8]; omega), hsb]
  -- `ret`
  refine c.s_ret hK5 hA5 hin (lt_len (by decide)) hr5 (ret_64 _) (by rw [hs5]; exact hl0) hin₂ h₂
    (by rw [hs5]; exact hrd0) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' V₃ t₇ d hPc hKZ' hAZ' hO hrZ' ?_
  rw [hgZ', hs5, hg5, hs4, hrb, hg4]
  try rfl

end FV7z.Dr2
