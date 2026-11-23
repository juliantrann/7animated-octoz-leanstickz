import FV7z.Lif.Holds
import FV7z.Ims.Holds
/-!
# `__libc_init_first` after `_dl_non_dynamic_init` (PLAN.md G3, startup)

`lif_b`, `Ims.init_misc_ok` and `lif_c` joined: from the return of `_dl_non_dynamic_init` (`lif_at + 70`), by
`__init_misc (argc, argv, envp)` and `__ctype_init`, to the return address of `__libc_init_first`.

- `bcV`: the bytes when `__init_misc` returns (the return address at `rsp - 8`, its frame, its two variables).
- `BcAp sp x m`: `m` bytes at `x` apart from the 40 bytes below `sp` and from the two variables; `bc_rd`: such bytes
  are unchanged.
- `lif_bc`: the join. The saved `rbp`, `r12`, `r13` come back from the stack, `rbx`, `r14`, `r15` are kept, and the
  bytes are `Cti.CtMem (bcV …)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Lif

/-- The bytes after `__init_misc` returns to `lif_at + 83`, from the bytes `V` and registers `g` at `lif_at + 70`. -/
def bcV (V : Addr → Byte) (g : Gprs) (a0 s : Addr) : Addr → Byte :=
  Ims.imV (Vst V (g.rsp - 8) (toBytesLE (lif_at.add 83) 8)) ((lifB g).set 4 (g.rsp - 8)) a0 s

/-- `m` bytes at `x`, apart from the 40 bytes below `sp` and from `__init_misc`'s two variables. -/
def BcAp (sp x : Addr) (m : Nat) : Prop :=
  x.toNat + m ≤ 2 ^ 64 ∧ (x.toNat + m ≤ sp.toNat - 40 ∨ sp.toNat ≤ x.toNat) ∧
    (x.toNat + m ≤ 7942968 ∨ 7942984 ≤ x.toNat)

theorem BcAp.mono {sp x y : Addr} {m k : Nat} (h : BcAp sp x m) (hy : x.toNat ≤ y.toNat)
    (hk : y.toNat + k ≤ x.toNat + m) : BcAp sp y k := by
  unfold BcAp at *
  omega

theorem bcV_out {V : Addr → Byte} {g : Gprs} {a0 s a : Addr} (hsp : 40 ≤ g.rsp.toNat)
    (ha : a.toNat < g.rsp.toNat - 40 ∨ g.rsp.toNat ≤ a.toNat) (hg : a.toNat < 7942968 ∨ 7942984 ≤ a.toNat) :
    bcV V g a0 s a = V a := by
  have := g.rsp.isLt
  have e : ((lifB g).set 4 (g.rsp - 8)).rsp = g.rsp - 8 := rfl
  have n8 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bv_omega
  unfold bcV Ims.imV
  rw [vo (a := 7942976#64) (x := a) (toBytesLE_length _ _) (by decide) (by bv_omega),
    vo (a := 7942968#64) (x := a) (toBytesLE_length _ _) (by decide) (by bv_omega),
    Ims.cV_out (g := (lifB g).set 4 (g.rsp - 8)) (a := a) (by rw [e, n8]; omega)
      (by unfold Ims.InFr; rw [e, n8]; omega),
    vo (a := g.rsp - 8) (x := a) (toBytesLE_length _ _) (by rw [n8]; omega) (by rw [n8]; omega)]

theorem bc_rd {V : Addr → Byte} {g : Gprs} {a0 s x : Addr} {m : Nat} (hsp : 40 ≤ g.rsp.toNat)
    (h : BcAp g.rsp x m) : List.map (bcV V g a0 s) (byteAddrs x m) = List.map V (byteAddrs x m) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits hj h.1
  have h2 := h.2.1
  have h3 := h.2.2
  exact bcV_out hsp (by omega) (by omega)

theorem short_congr {V V' : Addr → Byte} {a s : Addr} {n : Nat}
    (h : ∀ k ≤ n, V' (Addr.add a k) = V (Addr.add a k)) (hs : Ims.Short V' a n s) : Ims.Short V a n s := by
  rcases hs with ⟨h1, h2⟩ | ⟨m, hm, h2, h3, h4⟩
  · exact .inl ⟨fun k hk => by rw [← h k (by omega)]; exact h1 k hk, h2⟩
  · refine .inr ⟨m, hm, by rw [← h m (by omega)]; exact h2, fun k h5 h6 => ?_, h4⟩
    rw [← h k (by omega)]
    exact h3 k h5 h6

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 1600000 in
/-- From the return of `_dl_non_dynamic_init` in `__libc_init_first` to the function's return address: `__init_misc`
with `argv[0]` a string of `n` characters (`strrchr` by its contract), then `__ctype_init`. -/
theorem lif_bc {fb lp ct a0 : Addr} {a b cc : BitVec 64} {n : Nat} {pr : List Byte} {Pm : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L lif_at lif) (hinI : CodeIn L Ims.ims_at Ims.ims) (hci : CodeIn L Cti.cti_at Cti.cti)
    (hir : CodeIn L 4198480#64 pr) (hr0 : 0 < pr.length) (hrchr : Str.RchrAt prof L o 4198480#64 Pm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lif_at.add 70)
    (hsp : 40 ≤ X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat + 32 ≤ 2 ^ 64)
    (hst : ∀ i < 40, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64) i))
    (hl : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hgl : ∀ i < 16, Foot Wl (Addr.add 7942968#64 i))
    (hgs : 7942984 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat + 32 ≤ 7942968)
    -- `argv[0]`, a string of `n` characters
    (hsi : X.cpu.gpr.r12 ≠ 0) (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.r12 i))
    (ha0 : rdq(V, X.cpu.gpr.r12) = a0) (hnz : a0 ≠ 0) (hap0 : BcAp X.cpu.gpr.rsp X.cpu.gpr.r12 8)
    (nfit : a0.toNat + n < 2 ^ 64) (nnz : ∀ k < n, V (Addr.add a0 k) ≠ 0) (nz : V (Addr.add a0 n) = 0)
    (npg : ∀ x : Addr, a0.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (a0.toNat + n) / 4096 → Foot F.data x)
    (nout : ∀ k ≤ n, (Addr.add a0 k).toNat < X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ (Addr.add a0 k).toNat)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ a.toNat) →
      W a = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lif_at.add 83) 8) a) → Pm W)
    -- `__ctype_init`
    (hlp : rdq(V, fb - 112#64) = lp) (hct : rdq(V, lp) = ct) (ha : rdq(V, ct + 64#64) = a)
    (hb : rdq(V, ct + 72#64) = b) (hc : rdq(V, ct + 88#64) = cc)
    (p1 : BcAp X.cpu.gpr.rsp (fb - 112#64) 8) (p2 : BcAp X.cpu.gpr.rsp lp 8)
    (p3 : BcAp X.cpu.gpr.rsp (ct + 64#64) 32)
    (f1 : ∀ i < 8, Foot F.data ((fb - 112#64).add i)) (f2 : ∀ i < 8, Foot F.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot F.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl ((fb - 64#64).add i))
    (hfb : 64 ≤ fb.toNat) (hcn : ct.toNat + 96 ≤ 2 ^ 64)
    (hap : ct.toNat + 96 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ ct.toNat + 64)
    (hsa : X.cpu.gpr.rsp.toNat + 32 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ X.cpu.gpr.rsp.toNat + 24)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 24#64) = e₂.add j₂)
    (k : ∀ Z t' s, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cti.CtMem (bcV V X.cpu.gpr a0 s) fb a b cc) →
      Ims.Short V a0 n s → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 32#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp) →
      Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8#64) → Z.cpu.gpr.r13 = rdq(V, X.cpu.gpr.rsp + 16#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have n8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have v1o : ∀ x : Addr, (x.toNat < X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lif_at.add 83) 8) x = V x := fun x hx =>
    vo (a := X.cpu.gpr.rsp - 8) (x := x) (toBytesLE_length _ _) (by rw [n8]; omega) (by rw [n8]; omega)
  refine lif_b c hin hinI (by rw [Ims.ims_length]; omega) (by decide) hK hA hrip (fun i hi => ?_) ?_
  · have := hst (32 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 40#64) (32 + i) = Addr.add (X.cpu.gpr.rsp - 8) i by
      simp only [Addr.add]; bv_omega] at this
  intro Y t₁ hKY hAY hrY hgY
  have eY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]; rfl
  have nY : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [eY, n8]
  have eYsi : Y.cpu.gpr.rsi = X.cpu.gpr.r12 := by rw [hgY]; rfl
  have e40 : X.cpu.gpr.rsp - 8 - 32#64 = X.cpu.gpr.rsp - 40#64 := by bv_omega
  refine Ims.init_misc_ok (a0 := a0) (n := n) (j₂ := 83) c hinI hir hr0 hrchr hKY hAY hrY (by rw [nY]; omega)
    (by rw [nY]; omega) (fun i hi => ?_) (fun i hi => ?_) hin (by rw [lif_length]; omega) ?_
    (by rw [eYsi]; exact hsi) (fun i hi => by rw [eYsi]; exact fa i hi) ?_ hnz (by rw [eYsi]; exact hap0.1)
    (by rw [nY, eYsi]; have := hap0.2.1; omega) (by rw [eYsi]; have := hap0.2.2; omega) hgl
    (by rw [nY]; omega) nfit (fun j hj => by rw [v1o _ (nout j (by omega))]; exact nnz j hj)
    (by rw [v1o _ (nout n (Nat.le_refl _))]; exact nz) npg
    (fun j hj => by unfold Ims.InFr; rw [nY]; have := nout j hj; omega)
    (fun W hW => hPm W fun a ha => hW a (by unfold Ims.InFr; rw [nY]; omega)) ?_
  · rw [eY, e40]
    exact hst i (by omega)
  · rw [eY]
    have := hst (32 + i) (by omega)
    rw [show Addr.add (X.cpu.gpr.rsp - 40#64) (32 + i) = Addr.add (X.cpu.gpr.rsp - 8) i by
      simp only [Addr.add]; bv_omega] at this
    exact c.hws _ this
  · rw [eY, vs (a := X.cpu.gpr.rsp - 8) (toBytesLE_length _ _) (by rw [n8]; omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [eYsi, vr (a := X.cpu.gpr.rsp - 8) (x := X.cpu.gpr.r12) (toBytesLE_length _ _) (by rw [n8]; omega)
      hap0.1 (by have := hap0.2.1; rw [n8]; omega)]
    exact ha0
  intro Z t' s hKZ hAZ hS hrZ hB
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hB
  rw [hgY] at hAZ
  have hAZ' : Agree F Z.proc.mm.mem (bcV V X.cpu.gpr a0 s) := hAZ
  have eZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [b1, eY]; bv_omega
  have s8 : (X.cpu.gpr.rsp + 8#64).toNat = X.cpu.gpr.rsp.toNat + 8 := by bv_omega
  have s16 : (X.cpu.gpr.rsp + 16#64).toNat = X.cpu.gpr.rsp.toNat + 16 := by bv_omega
  have s24 : (X.cpu.gpr.rsp + 24#64).toNat = X.cpu.gpr.rsp.toNat + 24 := by bv_omega
  have q0 : BcAp X.cpu.gpr.rsp X.cpu.gpr.rsp 8 := ⟨by omega, .inr (Nat.le_refl _), by omega⟩
  have q8 : BcAp X.cpu.gpr.rsp (X.cpu.gpr.rsp + 8#64) 8 := ⟨by omega, .inr (by omega), by omega⟩
  have q16 : BcAp X.cpu.gpr.rsp (X.cpu.gpr.rsp + 16#64) 8 := ⟨by omega, .inr (by omega), by omega⟩
  have q24 : BcAp X.cpu.gpr.rsp (X.cpu.gpr.rsp + 24#64) 8 := ⟨by omega, .inr (by omega), by omega⟩
  have c64 : (ct + 64#64).toNat = ct.toNat + 64 := by bv_omega
  have c72 : (ct + 72#64).toNat = ct.toNat + 72 := by bv_omega
  have c88 : (ct + 88#64).toNat = ct.toNat + 88 := by bv_omega
  refine lif_c c hfs hin hci hKZ hAZ' hrZ (by rw [bc_rd hsp p1]; exact hlp) (by rw [bc_rd hsp p2]; exact hct)
    (by rw [bc_rd (x := ct + 64#64) (m := 8) hsp (p3.mono (by omega) (by omega))]; exact ha)
    (by rw [bc_rd (x := ct + 72#64) (m := 8) hsp (p3.mono (by omega) (by omega))]; exact hb)
    (by rw [bc_rd (x := ct + 88#64) (m := 8) hsp (p3.mono (by omega) (by omega))]; exact hc) f1 f2 f3 fw hfb hcn hap
    (fun i hi => by rw [eZ]; exact hl i hi) (by rw [eZ]; exact htop) (by rw [eZ]; exact hsa) hin₂ h₂
    (by rw [eZ, bc_rd hsp q24]; exact hra) ?_
  intro Z₂ t₂ hK₂ hA₂ hr₂ hg₂
  refine k Z₂ t₂ s hK₂ hA₂ (short_congr (fun j hj => v1o _ (nout j hj)) hS) hr₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hg₂, eZ]
    rfl
  · rw [hg₂]
    show Z.cpu.gpr.rbx = _
    rw [b2, hgY]
    rfl
  · rw [hg₂]
    show rdq(bcV V X.cpu.gpr a0 s, Z.cpu.gpr.rsp) = _
    rw [eZ, bc_rd hsp q0]
  · rw [hg₂]
    show rdq(bcV V X.cpu.gpr a0 s, Z.cpu.gpr.rsp + 8#64) = _
    rw [eZ, bc_rd hsp q8]
  · rw [hg₂]
    show rdq(bcV V X.cpu.gpr a0 s, Z.cpu.gpr.rsp + 16#64) = _
    rw [eZ, bc_rd hsp q16]
  · rw [hg₂]
    show Z.cpu.gpr.r14 = _
    rw [b6, hgY]
    rfl
  · rw [hg₂]
    show Z.cpu.gpr.r15 = _
    rw [b7, hgY]
    rfl

end FV7z.Lif
