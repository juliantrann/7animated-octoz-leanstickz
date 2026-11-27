import FV7z.Stl.Loop
/-!
# `____strtoul_l_internal`: from the entry to the digit loop (PLAN.md §M, M1)

The pieces before the digit loop (296, `Stl/Loop.lean`) and the theorem `stl_ok`, in the style of `Ild/Main.lean`.

- `agF`: a store in the frame `[S - 88, S - 48)` keeps the `Ag` invariant. `Cx x b`: `rcx` after reading the
  byte `b` (`cxS`, `cxZ` for the sign and zero extensions). `klt`: a byte that is not 0 is before the NUL.
- `Sb`: the base tables (cut value at 7353760, digit at 7353696, the base-16 and base-8 entries), `CU[0] ≠ 'X'`
  (`u0`), the locale's ctype table `B` (`r8 + 104`, its entries, `B[0]` not a space: `b0`), what the pieces before
  the loop read.
- `t223` (to `lpAll`), `t216` (`r10 := CU`), `t745` (no byte: to `t748`), `t171` (the base's table entries),
  `t150` (base 10), `t604` (`0` without `x`), `t133` (base and prefix; the `0x` case needs `k + 2 ≤ n`, by `u0`),
  `t99` (the sign), `t80` (the spaces, by induction on `n - k`; a space is not the NUL by `b0`), `t0`, `stl_ok`.

Each piece carries `rbx = p + k` and, for the loop's `rcx`, `p[k] = 0 → rcx = 0` (from 99 on, `Cx rcx p[k]`).
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

theorem ap2 (p : Addr) (k : Nat) : Addr.add p k + 2#64 = Addr.add p (k + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `rcx` after reading the byte `b`: its low byte is `b`, and `b = 0` gives `rcx = 0`. -/
abbrev Cx (x : BitVec 64) (b : BitVec 8) : Prop := BitVec.setWidth 8 x = b ∧ (b = 0#8 → x = 0#64)

theorem sx8 (b : BitVec 8) : BitVec.setWidth 8 (BitVec.signExtend 64 b) = b := by
  have h : ∀ m < 256, BitVec.setWidth 8 (BitVec.signExtend 64 (BitVec.ofNat 8 m)) = BitVec.ofNat 8 m := by
    decide +kernel
  have := h b.toNat b.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem cxS (b : BitVec 8) : Cx (BitVec.signExtend 64 b) b :=
  ⟨sx8 b, fun h => by subst h; decide⟩

theorem cxZ (b : BitVec 8) : Cx (BitVec.setWidth 64 (BitVec.setWidth 32 b)) b :=
  ⟨by bv_omega, fun h => by subst h; decide⟩

/-- The `wp`'s test of a byte. -/
theorem nz8 {x : BitVec 8} (h : (x &&& x == 0) = false) : x ≠ 0#8 := by
  rw [BitVec.and_self] at h
  intro hx
  rw [hx] at h
  exact absurd h (by decide)

/-- A byte of the string that is not 0 is before the NUL. -/
theorem klt {F : Footprint} {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {n k : Nat}
    (Sw : Sv F Kk V0 g0 n) (hk : k ≤ n) (hb : rb V0 (Addr.add g0.rdi k) ≠ 0#8) : k < n :=
  Nat.lt_of_le_of_ne hk fun h => hb (by rw [h]; exact Sw.z)

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
  u0 : rdd(V0, Cu V0 + BitVec.signExtend 64 0#8 * 4#64) ≠ 88#32
  ku0 : ∀ i < 4, Kk (Addr.add (Cu V0 + BitVec.signExtend 64 0#8 * 4#64) i) ∧
    ((Addr.add (Cu V0 + BitVec.signExtend 64 0#8 * 4#64) i).toNat < g0.rsp.toNat - 88 ∨
      g0.rsp.toNat ≤ (Addr.add (Cu V0 + BitVec.signExtend 64 0#8 * 4#64) i).toNat)
  f104 : ∀ i < 8, Foot F.data (Addr.add (g0.r8 + 104#64) i)
  k104 : ∀ i < 8, Kk (Addr.add (g0.r8 + 104#64) i) ∧
    ((Addr.add (g0.r8 + 104#64) i).toNat < g0.rsp.toNat - 88 ∨ g0.rsp.toNat ≤ (Addr.add (g0.r8 + 104#64) i).toNat)
  fBe : ∀ w : BitVec 8, ∀ i < 1, Foot F.data (Addr.add (Bt V0 g0 + BitVec.signExtend 64 w * 2#64 + 1#64) i)
  kB0 : ∀ i < 1, Kk (Addr.add (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) i) ∧
    ((Addr.add (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) i).toNat < g0.rsp.toNat - 88 ∨
      g0.rsp.toNat ≤ (Addr.add (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) i).toNat)
  b0 : (rb V0 (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) &&& 32#8 == 0) = true

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
  rw [hV] at hAZ
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
  rw [hV] at hAZ
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

/-! ## The base and the prefix -/

set_option maxHeartbeats 4000000 in
/-- From 150 (base 10): `eax = 8`; to 171. -/
theorem t150 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 150) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (h14 : Y.cpu.gpr.r14 = 0#64) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : rb V0 (Addr.add g0.rdi k) = 0#8 → Y.cpu.gpr.rcx = 0#64)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_150 prof fb).run c hfs E.hin _ hK hA hr (vc_150 h14) ?_
  rintro j' g fl V' ⟨rfl, hV, hax, -, hbp', hsp', hbx', hcx', h13', -⟩ Z t₁ hKZ hAZ hrZ hgZ -
  rw [hV] at hAZ
  exact t171 c hfs E Sw St Sc hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
    (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx]) (fun h0 => by rw [hgZ, hcx']; exact hcx h0)
    (Or.inl (by rw [hgZ, hax]; decide)) hag hEs kr

set_option maxHeartbeats 4000000 in
/-- From 604 (`p[k] = '0'`, no `x`): `[rsp + 18]`, `ecx = '0'`; to 216 or 223. -/
theorem t604 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 604) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (h14 : Y.cpu.gpr.r14 = 0#64) (hdx : Y.cpu.gpr.rdx = g0.rdx) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hp0 : rb V0 (Addr.add g0.rdi k) = 48#8)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  have hS : 80 ≤ g0.rsp.toNat := by omega
  obtain ⟨e8, e18, -, -⟩ := slots hS96
  have w18 : ∀ i < 1, Foot Wl (Addr.add (Y.cpu.gpr.rsp + 18#64) i) := by
    rw [hsp]
    exact stk E.wf (by omega) (by omega) (by omega)
  obtain ⟨fT1, fT2⟩ := Sc.fT _ (Or.inr rfl)
  have fT1' : ∀ i < 8, Foot F.data (Addr.add
      (7353760#64 + BitVec.signExtend 64 (BitVec.setWidth 32 (Y.cpu.gpr.rdx + 18446744073709551614#64)) * 8#64) i) := by
    rw [hdx]
    exact fT1
  have fT2' : ∀ i < 1, Foot F.data (Addr.add
      (7353696#64 + BitVec.signExtend 64 (BitVec.setWidth 32 (Y.cpu.gpr.rdx + 18446744073709551614#64))) i) := by
    rw [hdx]
    exact fT2
  have hc0 : rb V0 (Addr.add g0.rdi k) = 0#8 → 48#64 = 0#64 := fun h0 => absurd (hp0.symm.trans h0) (by decide)
  have hU : Cu V = Cu V0 := congrArg (ofBytesLE 64) (rdK hS hag Sw.kU)
  refine (c_604 prof fb).run c hfs E.hin _ hK hA hr (vc_604 h14 Sc.fA8 Sc.fB8 w18 Sw.fU fT1' fT2') ?_
  rintro j' g fl V' ⟨hsp', hbx', h13', -, hbp', hcx', ⟨rfl, hV⟩ | ⟨rfl, hV, h10'⟩⟩ Z t₁ hKZ hAZ hrZ hgZ -
  · subst hV
    rw [hsp] at hAZ
    exact t216 c hfs E Sw St hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
      (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx]) (fun h0 => by rw [hgZ, hcx']; exact hc0 h0)
      (agF hag (by rw [e18]; omega) (by rw [e18]; omega))
      ((rdo (by rw [e18]; omega) (by rw [e8]; omega) (by rw [e18, e8]; omega)).trans hEs) kr
  · subst hV
    rw [hsp] at hAZ
    exact t223 c hfs E Sw St hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
      (by rw [hgZ, h10', hU]) (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx])
      (fun h0 => by rw [hgZ, hcx']; exact hc0 h0)
      (agF hag (by rw [e18]; omega) (by rw [e18]; omega))
      ((rdo (by rw [e18]; omega) (by rw [e8]; omega) (by rw [e18, e8]; omega)).trans hEs) kr

set_option maxHeartbeats 4000000 in
/-- From 133 (after the sign, `rcx` the byte `p[k]`): the base and the `0x` prefix, five ways. -/
theorem t133 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 133) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (h14 : Y.cpu.gpr.r14 = 0#64) (hdx : Y.cpu.gpr.rdx = g0.rdx) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : Cx Y.cpu.gpr.rcx (rb V0 (Addr.add g0.rdi k)))
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  have hS : 80 ≤ g0.rsp.toNat := by omega
  obtain ⟨e8, e18, -, -⟩ := slots hS96
  obtain ⟨hc8, hc0⟩ := hcx
  have w18 : ∀ i < 1, Foot Wl (Addr.add (Y.cpu.gpr.rsp + 18#64) i) := by
    rw [hsp]
    exact stk E.wf (by omega) (by omega) (by omega)
  have hU : Cu V = Cu V0 := congrArg (ofBytesLE 64) (rdK hS hag Sw.kU)
  have k48 : BitVec.setWidth 8 Y.cpu.gpr.rcx = 48#8 → k < n := fun h =>
    klt Sw hk (by rw [← hc8, h]; decide)
  have hb1 : k < n → rb V (Y.cpu.gpr.rbx + 1#64) = rb V0 (Addr.add g0.rdi (k + 1)) := fun h => by
    rw [hbx, ap1]
    exact rbS hS Sw hag (by omega)
  have k88 : BitVec.setWidth 8 Y.cpu.gpr.rcx = 48#8 →
      rdd(V, Cu V + BitVec.signExtend 64 (rb V (Y.cpu.gpr.rbx + 1#64)) * 4#64) = 88#32 → k + 1 < n := by
    intro h h88
    have hkn := k48 h
    refine Nat.lt_of_le_of_ne (by omega) fun he => Sc.u0 ?_
    rw [hU, hb1 hkn, he, Sw.z] at h88
    exact (congrArg (ofBytesLE 32) (rdK hS hag Sc.ku0)).symm.trans h88
  have f1 : BitVec.setWidth 8 Y.cpu.gpr.rcx = 48#8 → ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 1#64) i) :=
    fun h i hi => by
      have := k48 h
      rw [show i = 0 by omega, a0, hbx, ap1]
      exact Sw.fp _ (by omega)
  have fUe : ∀ i < 4,
      Foot F.data (Addr.add (Cu V + BitVec.signExtend 64 (rb V (Y.cpu.gpr.rbx + 1#64)) * 4#64) i) := by
    rw [hU]
    exact Sw.fUe _
  have f2 : BitVec.setWidth 8 Y.cpu.gpr.rcx = 48#8 →
      rdd(V, Cu V + BitVec.signExtend 64 (rb V (Y.cpu.gpr.rbx + 1#64)) * 4#64) = 88#32 →
      ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 2#64) i) := fun h h88 i hi => by
    have := k88 h h88
    rw [show i = 0 by omega, a0, hbx, ap2]
    exact Sw.fp _ (by omega)
  refine (c_133 prof fb).run c hfs E.hin _ hK hA hr (vc_133 h14 f1 Sw.fU fUe f2 Sc.fA6 Sc.fB6 w18) ?_
  rintro j' g fl V' ⟨hsp', h13', h14', ⟨rfl, hV, hax, hbx', hcx', hbp', h48, h88⟩ |
    ⟨rfl, hV, hbx', hdx', h48⟩ |
    ⟨rfl, hV, hbx', hcx', hbp', h10', h48⟩ | ⟨rfl, hV, hg⟩ | ⟨rfl, hV, hax, hbx', hcx', hbp'⟩⟩
    Z t₁ hKZ hAZ hrZ hgZ -
  · rw [hV] at hAZ
    have k1 := k88 h48 h88
    exact t171 c hfs E Sw St Sc (k := k + 2) (by omega) hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
      (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx, ap2])
      (fun h0 => by rw [hgZ, hcx', hbx, ap2, rbS (k := k + 2) hS Sw hag (by omega), h0] <;> decide)
      (Or.inl (by rw [hgZ, hax]; decide)) hag hEs kr
  · rw [hV] at hAZ
    exact t604 c hfs E Sw St Sc hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, h13', h13])
      (by rw [hgZ, h14']) (by rw [hgZ, hdx', hdx]) (by rw [hgZ, hbx', hbx]) (hc8.symm.trans h48) hag hEs kr
  · subst hV
    rw [hsp] at hAZ
    exact t223 c hfs E Sw St hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
      (by rw [hgZ, h10', hU]) (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx])
      (fun h0 => absurd ((hc8.symm.trans h48).symm.trans h0) (by decide))
      (agF hag (by rw [e18]; omega) (by rw [e18]; omega))
      ((rdo (by rw [e18]; omega) (by rw [e8]; omega) (by rw [e18, e8]; omega)).trans hEs) kr
  · rw [hV] at hAZ
    exact t150 c hfs E Sw St Sc hk hKZ hAZ hrZ (by rw [hgZ, hg, hsp]) (by rw [hgZ, hg, h13])
      (by rw [hgZ, hg, h14]) (by rw [hgZ, hg, hbx]) (fun h0 => by rw [hgZ, hg]; exact hc0 h0) hag hEs kr
  · rw [hV] at hAZ
    exact t171 c hfs E Sw St Sc hk hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, hbp'])
      (by rw [hgZ, h13', h13]) (by rw [hgZ, hbx', hbx]) (fun h0 => by rw [hgZ, hcx']; exact hc0 h0)
      (Or.inr (by rw [hgZ, hax, hdx] <;> bv_omega)) hag hEs kr

set_option maxHeartbeats 4000000 in
/-- From 99 (`rcx` the byte `p[k]`): no byte to 448 (`E = 0`) or 790; the sign at `[rsp + 20]`; to 133. -/
theorem t99 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 99) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (h14 : Y.cpu.gpr.r14 = 0#64) (hdx : Y.cpu.gpr.rdx = g0.rdx) (hbx : Y.cpu.gpr.rbx = Addr.add g0.rdi k)
    (hcx : Cx Y.cpu.gpr.rcx (rb V0 (Addr.add g0.rdi k)))
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  have hS : 80 ≤ g0.rsp.toNat := by omega
  obtain ⟨e8, -, e20, -⟩ := slots hS96
  have fE : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8#64) i) := by
    rw [hsp]
    exact fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  have w20 : ∀ i < 4, Foot Wl (Addr.add (Y.cpu.gpr.rsp + 20#64) i) := by
    rw [hsp]
    exact stk E.wf (by omega) (by omega) (by omega)
  have knz : BitVec.setWidth 8 Y.cpu.gpr.rcx ≠ 0#8 → k < n := fun h => klt Sw hk (by rw [← And.left hcx]; exact h)
  have f1 : ∀ c8 : BitVec 8, c8 ≠ 0#8 → BitVec.setWidth 8 Y.cpu.gpr.rcx = c8 →
      ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 1#64) i) := fun c8 hc8 h i hi => by
    have := knz (by rw [h]; exact hc8)
    rw [show i = 0 by omega, a0, hbx, ap1]
    exact Sw.fp _ (by omega)
  have hEv : rdq(V, Y.cpu.gpr.rsp + 8#64) = g0.rsi := by rw [hsp, hEs]
  have go : ∀ (g : Gprs) (V' : Addr → Byte) (Z : State) (t₁ : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = stl_at.add 133 → Z.cpu.gpr = g → g.rsp = Y.cpu.gpr.rsp → g.r13 = Y.cpu.gpr.r13 →
      g.r14 = Y.cpu.gpr.r14 → g.rdx = Y.cpu.gpr.rdx →
      (BitVec.setWidth 8 Y.cpu.gpr.rcx &&& BitVec.setWidth 8 Y.cpu.gpr.rcx == 0) = false →
      P133 V Y.cpu.gpr g V' → GoG prof L o gev gP gE Z t₁ := by
    intro g V' Z t₁ hKZ hAZ hrZ hgZ hsp' h13' h14' hdx' hnz hP
    have hkn := knz (nz8 hnz)
    have hag2 := agF (a := S88 g0.rsp + 20#64) (m := 4) (v := 0#32) hag (by rw [e20]; omega) (by rw [e20]; omega)
    have hEs2 : rdq(Vst V (S88 g0.rsp + 20#64) (toBytesLE (0#32) 4), S88 g0.rsp + 8#64) = g0.rsi :=
      (rdo (by rw [e20]; omega) (by rw [e8]; omega) (by rw [e20, e8]; omega)).trans hEs
    rcases hP with ⟨hV, hbx', hcx'⟩ | ⟨hV, hbx', hcx'⟩ | ⟨hV, hg⟩
    · subst hV
      rw [hsp] at hAZ
      exact t133 c hfs E Sw St Sc (k := k + 1) (by omega) hKZ hAZ hrZ (by rw [hgZ, hsp', hsp])
        (by rw [hgZ, h13', h13]) (by rw [hgZ, h14', h14]) (by rw [hgZ, hdx', hdx]) (by rw [hgZ, hbx', hbx, ap1])
        (by rw [hgZ, hcx', hbx, ap1, rbS (k := k + 1) hS Sw hag (by omega)]; exact cxZ _)
        (agF hag (by rw [e20]; omega) (by rw [e20]; omega))
        ((rdo (by rw [e20]; omega) (by rw [e8]; omega) (by rw [e20, e8]; omega)).trans hEs) kr
    · subst hV
      rw [hsp] at hAZ hcx'
      exact t133 c hfs E Sw St Sc (k := k + 1) (by omega) hKZ hAZ hrZ (by rw [hgZ, hsp', hsp])
        (by rw [hgZ, h13', h13]) (by rw [hgZ, h14', h14]) (by rw [hgZ, hdx', hdx]) (by rw [hgZ, hbx', hbx, ap1])
        (by rw [hgZ, hcx', hbx, ap1, rbS (k := k + 1) hS Sw hag2 (by omega)]; exact cxZ _) hag2 hEs2 kr
    · subst hV
      rw [hsp] at hAZ
      exact t133 c hfs E Sw St Sc hk hKZ hAZ hrZ (by rw [hgZ, hg, hsp]) (by rw [hgZ, hg, h13])
        (by rw [hgZ, hg, h14]) (by rw [hgZ, hg, hdx]) (by rw [hgZ, hg, hbx]) (by rw [hgZ, hg]; exact hcx) hag2 hEs2
        kr
  by_cases hz : g0.rsi = 0#64
  · refine (c_99 prof fb).run c hfs E.hin _ hK hA hr
      (vc_99z (by rw [hEv, hz]) fE (f1 45#8 (by decide)) (f1 43#8 (by decide)) w20) ?_
    rintro j' g fl V' ⟨hsp', h13', h14', hdx', ⟨rfl, hV⟩ | ⟨rfl, hnz, hP⟩⟩ Z t₁ hKZ hAZ hrZ hgZ -
    · rw [hV] at hAZ
      exact t448 c hfs E hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) hag kr
    · exact go g V' Z t₁ hKZ hAZ hrZ hgZ hsp' h13' h14' hdx' hnz hP
  · refine (c_99 prof fb).run c hfs E.hin _ hK hA hr
      (vc_99n (by rw [hEv]; exact hz) fE (f1 45#8 (by decide)) (f1 43#8 (by decide)) w20) ?_
    rintro j' g fl V' ⟨hsp', h13', h14', hdx', ⟨rfl, hV, -⟩ | ⟨rfl, hnz, hP⟩⟩ Z t₁ hKZ hAZ hrZ hgZ -
    · rw [hV] at hAZ
      exact t790 c hfs E hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) hag hz hEs kr
    · exact go g V' Z t₁ hKZ hAZ hrZ hgZ hsp' h13' h14' hdx' hnz hP

/-! ## The spaces and the entry -/

set_option maxHeartbeats 4000000 in
/-- From 80 (`p[k]` a space, `rsi = B`): the next byte; a space again (80, by induction on `n - k`) or 99. -/
theorem t80 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    ∀ m k, n - k = m → k < n → ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = stl_at.add 80 → Y.cpu.gpr.rsp = S88 g0.rsp →
      Y.cpu.gpr.r13 = g0.rdi → Y.cpu.gpr.r14 = 0#64 → Y.cpu.gpr.rdx = g0.rdx →
      Y.cpu.gpr.rbx = Addr.add g0.rdi k → Y.cpu.gpr.rsi = Bt V0 g0 → Ag (Kr Kk g0.rsp) (Vf V0 g0) V →
      rdq(V, S88 g0.rsp + 8#64) = g0.rsi → GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS : 80 ≤ g0.rsp.toNat := by omega
  intro m
  induction m with
  | zero => intro k hm hk; exact absurd hm (by omega)
  | succ m ih =>
    intro k hm hk Y t V hK hA hr hsp h13 h14 hdx hbx hsi hag hEs
    have hb1 : rb V (Y.cpu.gpr.rbx + 1#64) = rb V0 (Addr.add g0.rdi (k + 1)) := by
      rw [hbx, ap1]
      exact rbS hS Sw hag (by omega)
    have f1 : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 1#64) i) := fun i hi => by
      rw [show i = 0 by omega, a0, hbx, ap1]
      exact Sw.fp _ (by omega)
    have f2 : ∀ i < 1, Foot F.data
        (Addr.add (Y.cpu.gpr.rsi + BitVec.signExtend 64 (rb V (Y.cpu.gpr.rbx + 1#64)) * 2#64 + 1#64) i) := by
      rw [hsi]
      exact Sc.fBe _
    refine (c_80 prof fb).run c hfs E.hin _ hK hA hr (vc_80 f1 f2) ?_
    rintro j' g fl V' ⟨hV, hsp', hbx', hsi', h13', h14', hdx', hcx', rfl | ⟨rfl, hsp8⟩⟩ Z t₁ hKZ hAZ hrZ hgZ -
    · rw [hV] at hAZ
      exact t99 c hfs E Sw St Sc (k := k + 1) (by omega) hKZ hAZ hrZ (by rw [hgZ, hsp', hsp])
        (by rw [hgZ, h13', h13]) (by rw [hgZ, h14', h14]) (by rw [hgZ, hdx', hdx]) (by rw [hgZ, hbx', hbx, ap1])
        (by rw [hgZ, hcx', hb1]; exact cxS _) hag hEs kr
    · rw [hV] at hAZ
      have hk1 : k + 1 < n := by
        refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
        rw [hb1, he, Sw.z, hsi] at hsp8
        rw [show rb V (Bt V0 g0 + BitVec.signExtend 64 0 * 2#64 + 1#64) =
            rb V0 (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) from
          congrArg (ofBytesLE 8) (rdK hS hag Sc.kB0), Sc.b0] at hsp8
        exact absurd hsp8 (by decide)
      exact ih (k + 1) (by omega) hk1 Z t₁ V hKZ hAZ hrZ (by rw [hgZ, hsp', hsp]) (by rw [hgZ, h13', h13])
        (by rw [hgZ, h14', h14]) (by rw [hgZ, hdx', hdx]) (by rw [hgZ, hbx', hbx, ap1]) (by rw [hgZ, hsi', hsi])
        hag hEs

set_option maxHeartbeats 4000000 in
/-- From the entry: the pushes, `E` at `[rsp + 8]`, the base check (432), the first byte; to 99 or the spaces. -/
theorem t0 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0)
    {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V0) (hr : Y.cpu.rip = stl_at.add 0)
    (hg : Y.cpu.gpr = g0) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hl := g0.rsp.isLt
  have hS : 80 ≤ g0.rsp.toNat := by omega
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  obtain ⟨e8, -, -, -⟩ := slots hS96
  have w : ∀ b : Addr, g0.rsp.toNat - 88 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot Wl (Addr.add b i) := fun b h1 h2 => stk E.wf (by omega) h2 (by omega)
  have w1 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w2 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w3 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w4 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w5 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w6 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w7 : ∀ i < 8, Foot Wl (Addr.add (S88 Y.cpu.gpr.rsp + 8#64) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have fp : ∀ i < 1, Foot F.data (Addr.add Y.cpu.gpr.rdi i) := fun i hi => by
    rw [hg, show i = 0 by omega]
    exact Sw.fp 0 (Nat.zero_le _)
  have f104 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.r8 + 104#64) i) := by
    rw [hg]
    exact Sc.f104
  have hag1 : Ag (Kr Kk g0.rsp) (Vf V0 g0) (V1 V0 g0) :=
    agF (V := Vf V0 g0) (fun _ _ => rfl) (by rw [e8]; omega) (by rw [e8]; omega)
  have hEs1 : rdq(V1 V0 g0, S88 g0.rsp + 8#64) = g0.rsi := rds (by rw [e8]; omega)
  have hBt : Bt (V1 V0 g0) g0 = Bt V0 g0 := congrArg (ofBytesLE 64) (rdK hS hag1 Sc.k104)
  have hp := rbS (k := 0) hS Sw hag1 (Nat.zero_le _)
  rw [a0] at hp
  have fB : ∀ i < 1, Foot F.data (Addr.add (Bt (V1 V0 Y.cpu.gpr) Y.cpu.gpr +
      BitVec.signExtend 64 (rb (V1 V0 Y.cpu.gpr) Y.cpu.gpr.rdi) * 2#64 + 1#64) i) := by
    rw [hg, hBt]
    exact Sc.fBe _
  refine (c_0 prof fb).run c hfs E.hin _ hK hA hr
    (vc_0 (by rw [hg]; exact E.hc) w1 w2 w3 w4 w5 w6 w7 fp f104 fB) ?_
  rintro j' g fl V' ⟨hV, hsp', h13', h14', hdx', rfl | ⟨hbx', hsi', hcx', rfl | ⟨rfl, hsp8⟩⟩⟩
    Z t₁ hKZ hAZ hrZ hgZ -
  · rw [hV, hg] at hAZ
    exact t432 c hfs E hKZ hAZ hrZ (by rw [hgZ, hsp', hg]) hag1 kr
  · rw [hV, hg] at hAZ
    exact t99 c hfs E Sw St Sc (k := 0) (Nat.zero_le _) hKZ hAZ hrZ (by rw [hgZ, hsp', hg])
      (by rw [hgZ, h13', hg]) (by rw [hgZ, h14']) (by rw [hgZ, hdx', hg]) (by rw [hgZ, hbx', hg, a0])
      (by rw [hgZ, hcx', hg, hp, a0]; exact cxS _) hag1 hEs1 kr
  · rw [hV, hg] at hAZ
    have hk0 : 0 < n := by
      refine Nat.pos_of_ne_zero fun hn0 => ?_
      have hz : rb V0 g0.rdi = 0 := by
        have := Sw.z
        rw [hn0, a0] at this
        exact this
      rw [hg, hp, hBt, hz] at hsp8
      rw [show rb (V1 V0 g0) (Bt V0 g0 + BitVec.signExtend 64 0 * 2#64 + 1#64) =
          rb V0 (Bt V0 g0 + BitVec.signExtend 64 0#8 * 2#64 + 1#64) from
        congrArg (ofBytesLE 8) (rdK hS hag1 Sc.kB0), Sc.b0] at hsp8
      exact absurd hsp8 (by decide)
    exact t80 c hfs E Sw St Sc kr (n - 0) 0 rfl hk0 Z t₁ _ hKZ hAZ hrZ (by rw [hgZ, hsp', hg])
      (by rw [hgZ, h13', hg]) (by rw [hgZ, h14']) (by rw [hgZ, hdx', hg]) (by rw [hgZ, hbx', hg, a0])
      (by rw [hgZ, hsi', hg, hBt]) hag1 hEs1

/-- `____strtoul_l_internal` from its entry, under the string, table and frame conditions: every way out. -/
theorem stl_ok (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (Sc : Sb F Kk V0 g0)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V0) (hr : X.cpu.rip = stl_at)
    (hg : X.cpu.gpr = g0) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE X t :=
  t0 c hfs E Sw St Sc hK hA (hr.trans (by decide : stl_at = stl_at.add 0)) hg kr

end

end FV7z.Stl
