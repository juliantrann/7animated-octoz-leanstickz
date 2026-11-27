import FV7z.Stl.Loop
/-!
# `____strtoul_l_internal`: from the entry to the digit loop (PLAN.md §M, M1)

The pieces before the digit loop (296, `Stl/Loop.lean`) and the theorem `stl_ok`, in the style of `Ild/Main.lean`.

- `agF`: a store in the frame `[S - 88, S - 48)` keeps the `Ag` invariant.
- `Sb`: the base tables (cut value at 7353760, digit at 7353696, the base-16 and base-8 entries), what the pieces
  before the loop read.
- `t223` (to `lpAll`), `t216` (`r10 := CU`), `t745` (no byte: to `t748`), `t171` (the base's table entries).

Each piece carries `rbx = p + k` and, for the loop's `rcx`, `p[k] = 0 → rcx = 0`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Mcn (fr6 rds rdo fr_e6 fr6_rd)
open FV7z.Nlc (Ag)
namespace FV7z.Stl

/-- A store in the frame below the pushes keeps the bytes of `Kr`. -/
theorem agF {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} {a : Addr} {w m : Nat} {v : BitVec w}
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (h1 : g0.rsp.toNat - 88 ≤ a.toNat)
    (h2 : a.toNat + m ≤ g0.rsp.toNat - 48) :
    Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vst V a (toBytesLE v m)) := by
  have hl := g0.rsp.isLt
  refine hag.st (by rw [toBytesLE_length]; omega) fun y hy => ?_
  rw [toBytesLE_length]
  unfold Kr at hy
  rcases hy with ⟨h3, h4⟩ | ⟨-, h3 | h3⟩ <;> omega

/-- The base tables: for an index `x ≤ 34` (or `base - 2`), the cut value (8 bytes at `7353760 + 8 x`) and the
digit (at `7353696 + x`); the base-16 entries (7353702, 7353808) and the base-8 ones (7353704, 7353824). -/
structure Sb (F : Footprint) (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) : Prop where
  fT : ∀ x : BitVec 32, (x.toNat ≤ 34 ∨ x = BitVec.setWidth 32 (g0.rdx + 18446744073709551614#64)) →
    (∀ i < 8, Foot F.data (Addr.add (7353760#64 + BitVec.signExtend 64 x * 8#64) i)) ∧
    (∀ i < 1, Foot F.data (Addr.add (7353696#64 + BitVec.signExtend 64 x) i))
  fA6 : ∀ i < 1, Foot F.data (Addr.add 7353702#64 i)
  fB6 : ∀ i < 8, Foot F.data (Addr.add 7353808#64 i)
  fA8 : ∀ i < 1, Foot F.data (Addr.add 7353704#64 i)
  fB8 : ∀ i < 8, Foot F.data (Addr.add 7353824#64 i)

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-! ## Into the digit loop -/

set_option maxHeartbeats 4000000 in
/-- From 223 (`rbx = p + k`, `rbp = 0`, `r10 = CU`): `rdi := rbx`, `[rsp + 24] = -1`, `r11 = CB`; the loop. -/
theorem t223 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 223) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hbp : Y.cpu.gpr.rbp = 0#64)
    (h10 : Y.cpu.gpr.r10 = Cu V0) (h13 : Y.cpu.gpr.r13 = g0.rdi) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : rb V0 (Addr.add g0.rdi k) = 0#8 → Y.cpu.gpr.rcx = 0#64)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  have hS : 80 ≤ g0.rsp.toNat := by omega
  obtain ⟨e8, -, -, e24⟩ := slots hS96
  have w24 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by
    rw [hsp]
    exact stk E.wf (by omega) (by omega) (by omega)
  refine (c_223 prof fb).run c hfs E.hin _ hK hA hr (vc_223 St.fB w24) ?_
  rintro j' g fl V' ⟨rfl, hV, hdi, h11, hsp', hbx', hcx', hbp', h10', h13', -⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  rw [hsp] at hAZ
  have hag' := agF (a := S88 g0.rsp + 24#64) (m := 8) (v := Y.cpu.gpr.rbp + 18446744073709551615#64) hag
    (by rw [e24]; omega) (by rw [e24]; omega)
  have hEs' : rdq(Vst V (S88 g0.rsp + 24#64) (toBytesLE (Y.cpu.gpr.rbp + 18446744073709551615#64) 8),
      S88 g0.rsp + 8#64) = g0.rsi :=
    (rdo (by rw [e24]; omega) (by rw [e8]; omega) (by rw [e24, e8]; omega)).trans hEs
  have hCb : Cb V = Cb V0 := congrArg (ofBytesLE 64) (rdK hS hag St.kB)
  exact lpAll c hfs E Sw St kr (n - k) k rfl hk Z t₁ _ hKZ hAZ hrZ
    (by rw [hgZ]; exact ⟨hsp'.trans hsp, hbp'.trans hbp, h10'.trans h10, h11.trans hCb, h13'.trans h13,
      hdi.trans hbx⟩)
    (fun h0 => by rw [hgZ, hcx']; exact hcx ((rbS hS Sw hag' hk).symm.trans h0)) hag' hEs'

set_option maxHeartbeats 4000000 in
/-- From 216: `r10 := CU`; to 223. -/
theorem t216 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 216) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hbp : Y.cpu.gpr.rbp = 0#64)
    (h13 : Y.cpu.gpr.r13 = g0.rdi) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : rb V0 (Addr.add g0.rdi k) = 0#8 → Y.cpu.gpr.rcx = 0#64)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS : 80 ≤ g0.rsp.toNat := by omega
  refine (c_216 prof fb).run c hfs E.hin _ hK hA hr (vc_216 Sw.fU) ?_
  rintro j' g fl V' ⟨rfl, hV, h10', hsp', hbx', hcx', hbp', h13', -⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  have hU : Cu V = Cu V0 := congrArg (ofBytesLE 64) (rdK hS hag Sw.kU)
  exact t223 c hfs E Sw St hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp', hbp])
    (by rw [hgZ, h10', hU]) (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx])
    (fun h0 => by rw [hgZ, hcx']; exact hcx h0) hag hEs kr

set_option maxHeartbeats 4000000 in
/-- From 745 (no byte after the prefix): `rdi := rbx`; to 748. -/
theorem t745 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 745) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_745 prof fb).run c hfs E.hin _ hK hA hr vc_745 ?_
  rintro j' g fl V' ⟨rfl, hV, hdi, hsp', h13'⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  exact t748 c hfs E Sw hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) hag hEs (by rw [hgZ, h13', h13])
    (by rw [hgZ, hdi, hbx]) kr

set_option maxHeartbeats 4000000 in
/-- From 171 (`eax` the base's index): the cut value and digit, `[rsp + 18]`; no byte to 745, else 216. -/
theorem t171 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 171) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hbp : Y.cpu.gpr.rbp = 0#64)
    (h13 : Y.cpu.gpr.r13 = g0.rdi) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : rb V0 (Addr.add g0.rdi k) = 0#8 → Y.cpu.gpr.rcx = 0#64)
    (hax : (BitVec.setWidth 32 Y.cpu.gpr.rax).toNat ≤ 34 ∨
      BitVec.setWidth 32 Y.cpu.gpr.rax = BitVec.setWidth 32 (g0.rdx + 18446744073709551614#64))
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨e8, e18, -, -⟩ := slots hS96
  obtain ⟨fT1, fT2⟩ := Sc.fT _ hax
  have w18 : ∀ i < 1, Foot Wl (Addr.add (Y.cpu.gpr.rsp + 18#64) i) := by
    rw [hsp]
    exact stk E.wf (by omega) (by omega) (by omega)
  refine (c_171 prof fb).run c hfs E.hin _ hK hA hr (vc_171 fT1 fT2 w18) ?_
  rintro j' g fl V' ⟨hV, hsp', hbx', hcx', hbp', h13', -, rfl | ⟨rfl, -⟩⟩ Z t₁ hKZ hAZ hrZ hgZ -
  · subst hV
    rw [hsp] at hAZ
    exact t745 c hfs E Sw hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, h13', h13])
      (by rw [hgZ, hbx', hbx]) (agF hag (by rw [e18]; omega) (by rw [e18]; omega))
      ((rdo (by rw [e18]; omega) (by rw [e8]; omega) (by rw [e18, e8]; omega)).trans hEs) kr
  · subst hV
    rw [hsp] at hAZ
    exact t216 c hfs E Sw St hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp', hbp])
      (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx]) (fun h0 => by rw [hgZ, hcx']; exact hcx h0)
      (agF hag (by rw [e18]; omega) (by rw [e18]; omega))
      ((rdo (by rw [e18]; omega) (by rw [e8]; omega) (by rw [e18, e8]; omega)).trans hEs) kr

end

end FV7z.Stl
