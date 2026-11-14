import FV7z.Hwc.Tail
/-!
# `_dl_important_hwcaps`: the `call` of `malloc` (1111) and on to the `ret` (PLAN.md G3, startup)

- `Mal.At`: what a `call` of `malloc` (`0x633160`) does, **assumed** here (like `Gor.PcpyAt` for `mempcpy`). This is
  the second `malloc` of the process (the first is `_dl_get_origin`'s, proven: `Mal.RunN.mal_firstn`); from the top
  chunk the first one left (`mp_.top_pad` = 0x20000 above it), so no `brk`, no events. `Pm` stands for the state of
  the heap (`main_arena`, `mp_`, the top chunk, the `tcache`) that the call needs: to be discharged with the general
  proof of `malloc` (PLAN.md, item `malloc`). The bytes it stores are its own frame (below `rsp`) and the allocator's
  (at or above `0x792980`: `main_arena` `0x792a40`, `mp_` `0x7929f0`, `global_max_fast`, the heap); it returns
  `p ≠ 0` with `[p, p + n)` in the heap, below the stack.
- `from1111`: the `call` at 1111 with `rdi = s`, then `from1116` (`Tail`): to the `ret` (1681).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Mal

/-- What a `call` of `malloc` at `e` does (assumed; see the module doc): called with a return address in code, `Pm`
and `rdi = n ≤ 1024`, the run gets back to the return address with `rsp + 8`, the registers a call keeps kept,
`rax = p` with `0x792980 ≤ p`, `p + n ≤ rsp`, the `n` bytes at `p` in the footprint, the bytes below `0x792980`
and from the caller's `rsp` up as they were, and `Pm` again for the bytes that keep the ones from `0x792980` to the
slot of the return address apart from the block (the state of the heap for the next call). -/
def At (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) : Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    X.cpu.gpr.rdi.toNat ≤ 1024 → CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ Z t' V₂ (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      7940480 ≤ p.toNat → p.toNat + X.cpu.gpr.rdi.toNat ≤ X.cpu.gpr.rsp.toNat →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + X.cpu.gpr.rdi.toNat → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940480 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ a.toNat → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat →
        (a.toNat < p.toNat ∨ p.toNat + X.cpu.gpr.rdi.toNat ≤ a.toNat) → W a = V₂ a) → Pm W) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

end FV7z.Mal

namespace FV7z.Hwc

set_option maxRecDepth 100000

def pc1111 : List Byte := [0xe8, 0xc4, 0x5b, 0xf8, 0xff]
theorem pc1111_0 : ∀ feat, Dec feat pc1111 0 (FV7z.mk .call 64 [.rel 18446744073709050820] 5) := by dec_rfl
theorem w_1111 : pc1111 <+: hwc.drop 1111 := by decide +kernel
theorem call_1111 (feat : Features) : Dec feat hwc 1111 (FV7z.mk .call 64 [.rel 18446744073709050820] 5) :=
  Dec.shift (j := 1111) (k := 0) (pc1111_0 feat) w_1111 (Nat.zero_le _)

theorem tgt_1111 : hwc_at.add (1111 + 5) + BitVec.ofNat 64 18446744073709050820 = 6500704#64 := by decide

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy mlc : List Byte} {Pm Pa : (Addr → Byte) → Prop}

set_option maxHeartbeats 4000000 in
/-- The `call` of `malloc (s)` at 1111 (`s` at least the table and the strings: `16 E + rem`), then `from1116`: to the
`ret` (1681) with `rax = P` the block `malloc` gave. The strings are below `0x792980` or in the stack (from `sp`
up), out of the reach of `malloc`. -/
theorem from1111 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    {V : Addr → Byte} {cnt E H s : Nat} {R bp sp Q : Addr} {ln st : Nat → Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 8 → W a = V a) → Pa W)
    (hn : cnt = 3 ∧ E = 8 ∧ H = 4 ∨ cnt = 4 ∧ E = 16 ∧ H = 8)
    (hsz : 16 * E + rem cnt ln H ≤ s) (hs : s ≤ 1024) (hsp8 : 8 ≤ sp.toNat)
    (hRs : sp.toNat ≤ R.toNat) (hRF : R.toNat + 16 * cnt ≤ (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hFr : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hT : ∀ m < cnt, rdq(V, R + BitVec.ofNat 64 (16 * m)) = st m ∧ rdq(V, R + BitVec.ofNat 64 (16 * m + 8)) = ln m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 7940480 ∨ sp.toNat ≤ (st m).toNat)
    (hN : rdd(V, bp + 18446744073709551520#64) = BitVec.ofNat 32 cnt)
    (hD : rdq(V, bp + 18446744073709551512#64) = R + BitVec.ofNat 64 (16 * (cnt - 1)))
    (hR8 : rdq(V, bp + 18446744073709551480#64) = BitVec.ofNat 64 E)
    (hD8 : rdq(V, bp + 18446744073709551464#64) = BitVec.ofNat 64 (16 * cnt))
    (hE4 : rdd(V, bp + 18446744073709551476#64) = BitVec.ofNat 32 E)
    (hL : rdq(V, bp + 18446744073709551536#64) = ln (cnt - 1))
    (hl : rdq(V, bp + 18446744073709551544#64) = ln 0)
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (tlen V R) cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ sp.toNat - 8 →
      (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
      Y.cpu.gpr.rsp = bp + 8#64 →
      Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
      Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
      Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
      Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (tlen V R) cnt (fun _ => 0#64)) H (ln (cnt - 1)))
        (caps E (tlen V R) cnt (fun _ => 0#64)) →
      Same V W 0 7940480 → Same V W sp.toNat (bp + 18446744073709551448#64).toNat →
      Same V W ((bp + 18446744073709551448#64).toNat + 88) (2 ^ 64) →
      (∀ W' : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < sp.toNat - 8 →
        (a.toNat < P.toNat ∨ P.toNat + s ≤ a.toNat) → W' a = W a) → Pa W') → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1111 →
      X.cpu.gpr.rdi = BitVec.ofNat 64 s → X.cpu.gpr.r12 = BitVec.ofNat 64 cnt →
      X.cpu.gpr.r13 = BitVec.ofNat 64 (16 * E) → X.cpu.gpr.rbx = R → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = sp →
      GoG prof L o gev gP gE X t := by
  intro X t hK hA hrip hdi h12 h13 hbx hbp hsp
  have hsl := sp.isLt
  have hb8 := sub8 hsp8
  have es : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  refine c.s_call hK hA hin (lt_len (by omega)) hrip (call_1111 _) hinm hm0 tgt_1111
    (fun i hi => by rw [hsp]; exact hst i hi) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hsp] at hA₁ hg₁
  have hdi₁ : Y.cpu.gpr.rdi = BitVec.ofNat 64 s := by rw [hg₁]; exact hdi
  have hsp₁ : Y.cpu.gpr.rsp = sp - 8 := by rw [hg₁]; rfl
  refine hmal c hK₁ hA₁ hr₁ (hPa _ fun a ha => ?_) (by rw [hdi₁, es]; exact hs) hin (j := 1116)
    (lt_len (by omega)) ?_ (fun i hi => ?_) ?_
  · exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (.inl (by rw [hb8]; omega))
  · rw [hsp₁, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hb8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₁]
    exact c.hws _ (hst i hi)
  intro Z t₂ V₂ p hK₂ hA₂ hr₂ hsp₂ hax₂ hbx₂ hbp₂ h12₂ h13₂ _ _ hlo hpe hWP hV₂ hPa₂
  rw [hdi₁, es, hsp₁, hb8] at hPa₂
  rw [hdi₁, es] at hpe hWP
  rw [hsp₁, hb8] at hpe
  rw [hsp₁, hb8] at hV₂
  have hV : ∀ a : Addr, a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat → V₂ a = V a := fun a ha => by
    rw [hV₂ a (by omega)]
    exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (by rw [toBytesLE_length, hb8]; omega)
  have hS : Same V V₂ sp.toNat (2 ^ 64) := fun a h1 _ => hV a (.inr h1)
  have hFs : sp.toNat ≤ (bp + 18446744073709551448#64).toNat := by omega
  have htl : ∀ j < cnt, tlen V₂ R j = tlen V R j := fun j hj => by
    have e : (R + BitVec.ofNat 64 (16 * j + 8)).toNat = R.toNat + (16 * j + 8) := addO (by omega)
    exact hS.rdq (by omega) (by omega) (by omega)
  have hcp : caps E (tlen V₂ R) cnt (fun _ => 0#64) = caps E (tlen V R) cnt (fun _ => 0#64) :=
    caps_congr cnt _ htl
  refine from1116 c hfs hin hinc hc0 hcpy (V := V₂) (P := p)
    (fun W hW => hPm W fun a ha => (hW a ha).trans (hV a (.inl ha))) hn hlo (by omega) hsp8 hRs hRF hfb
    (fun a h1 h2 => hWP a h1 (by omega)) hst hFr hFT (fun m hm => ?_) hsrc hs64
    (fun m hm => (hsd m hm).elim (fun h => .inl (by omega)) (fun h => .inr (by omega)))
    (by rw [hS.rd (n := 4) (by fomega) (by fomega) (by fomega)]; exact hN)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hD)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hR8)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hD8)
    (by rw [hS.rd (n := 4) (by fomega) (by fomega) (by fomega)]; exact hE4)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hL)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hl)
    (by rw [hS.rdq (by fomega) (by fomega) (by fomega)]; exact hQ) hsQ hQ64 hQd ?_ Z t₂ hK₂ hA₂ hr₂ hax₂
    (by rw [h12₂, hg₁]; exact h12) (by rw [h13₂, hg₁]; exact h13) (by rw [hbx₂, hg₁]; exact hbx)
    (by rw [hbp₂, hg₁]; exact hbp) (by rw [hsp₂, hsp₁]; exact sub8_add sp)
  · have e1 : (R + BitVec.ofNat 64 (16 * m)).toNat = R.toNat + 16 * m := addO (by omega)
    have e2 : (R + BitVec.ofNat 64 (16 * m + 8)).toNat = R.toNat + (16 * m + 8) := addO (by omega)
    rw [hS.rdq (by omega) (by omega) (by omega), hS.rdq (by omega) (by omega) (by omega)]
    exact hT m hm
  intro Y t' W hKY hAY hrY haxY hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 hS1 hS2 hS3
  rw [hcp] at hAY hTab
  rw [hS.rdq (by fomega) (by fomega) (by fomega)] at hbxY h12Y h13Y h14Y h15Y
  rw [hS.rdq (by fomega) (by fomega) (by fomega)] at hbpY
  exact k Y t' W p hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab
    (fun a h1 h2 => (hS0 a h1 (by omega)).trans (hV a (.inl h2)))
    (fun a h1 h2 => (hS1 a h1 h2).trans (hV a (.inr h1)))
    (fun a h1 h2 => (hS2 a h1 h2).trans (hV a (.inr (by omega))))
    (fun W' hW' => hPa₂ W' fun a h1 h2 h3 => (hW' a h1 h2 h3).trans (h3.elim (fun h => hS0 a (Nat.zero_le _) h)
      (fun h => hS3 a (by omega) h2)))

end FV7z.Hwc
