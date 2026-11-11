import FV7z.Start.Holds
import FV7z.CpuFeat.Irel
/-!
# `__libc_start_main` from its entry to `0x6133bb`, past `init_cpu_features` and `apply_irel` (PLAN.md G3, startup)

`start_cfg` ends at offset 211 (`0x613113`), where `CpuFeat.initCpuFeatures_applyIrel` begins. That theorem is about
a run and what it may store into (`Seg … Wl …`), and says of the footprint's bytes outside `Wl` that they are as at
its start. For `__libc_start_main` `Wl` is all its run stores into, the frame's slots of `argc`, `argv` and `main`
among it, so the theorem is used here for the run seen from the state at offset 211 (`Seg.rebase`) with
`cpuW q = icfW q ++ irelW q`, `q` the slot of the return addresses of the calls (`bp + 104`), as what may be stored
into (`initCpuFeatures_applyIrel_in`): the bytes outside `cpuW q` are then those at offset 211, which `FinP`
describes, and the slots of `argc`, `argv` and `main` are outside `cpuW q` (`Fr.after`).

`start_cpu`: from the entry (`Ctx.Ok`, `Env`, `I0`) to `0x6133bb`, with `CpuOk` and `GotOk` there, one system call
(`arch_prctl (ARCH_CET_STATUS, …)`), `rsp`, `rbp`, `r12`, `r13` as `FinP` has them, and the footprint's bytes outside
`cpuW (bp + 104)` those of `FinP`. What `init_cpu_features` reads of the image (the tunables' `initialized` bytes,
its jump table, the `rela` entries, `_dl_x86_cpu_features` at the entry) is asked of the bytes at the entry (`K.V0`).
-/

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}

/-- The run seen from a state it keeps, with less to store into. -/
theorem rebase (c : Seg prof F Wl L s₀ o) {X : State} (hK : KeptW Wl s₀ X) {Wl' : List Rgn}
    (hsub : ∀ y, Foot Wl' y → Foot Wl y) : Seg prof F Wl' L X o where
  foot := c.foot.keptW c.ready.rseq c.hws hK c.sub_self
  ready := c.ready.keptW c.foot c.hws hK
  env := c.env
  code := c.code
  own := c.own
  hww y hy := c.hww y (hsub y hy)

end FV7z.Fn.Seg

namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V₀ : Addr → Byte} {q : Addr}

/-- What `init_cpu_features` and `apply_irel` may store into. -/
abbrev cpuW (q : Addr) : List Rgn := icfW q ++ irelW q

/-- `initCpuFeatures_applyIrel` inside a run that may store into more (`Wl`): the footprint's bytes outside `cpuW q`
are as at `0x613113`. -/
theorem initCpuFeatures_applyIrel_in (c : Seg prof F Wl L s₀ o) (hw : ∀ y, Foot (cpuW q) y → Foot Wl y)
    (hE : IE F (cpuW q) L V₀ q) (hJ : JT F (cpuW q) V₀) (hR : RE F (cpuW q) L q)
    (hT : ∀ j < 744, ¬ Foot (cpuW q) ((0x400248 : Addr).add j) ∧ V₀ ((0x400248 : Addr).add j) = rela.getD j 0)
    (hpc : prof.Consistent) (hch : Chain prof) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V₀) (hok : CInv prof V₀)
    (hr : X.cpu.rip = 0x613113) (hsp : X.cpu.gpr.rsp = q.add 8)
    (post : ∀ (g : Gprs) (Y : State) (t' : Nat), g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
      KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem → V2606.GotOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot (cpuW q) y → Y.proc.mm.mem.readByte y = V₀ y) →
      Y.cpu.rip = 0x6133bb → TKi X.cpu.gpr Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  initCpuFeatures_applyIrel (c.rebase hK hw) hE hJ hR hT hpc hch (by rw [hK.df]; exact hdf)
    (by rw [hK.x87]; exact hx87) (KeptW.refl _ X) hA hok hr hsp
    fun g Y t' hax hdi hKY hc hg hoff hrY hTY => post g Y t' hax hdi (hK.trans hKY hw) hc hg hoff hrY hTY

end FV7z.CpuFeat

namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc
open FV7z.AuxInit (globals)
open FV7z.CpuFeat (cpuW icfW irelW IE JT RE TKi CInv rela tgvInit)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {K : Ctx}
  {V V' : Addr → Byte}

/-- Where `cpuW (bp + 104)` lies: the stack from `bp - 152` to `bp + 112` and from `bp + 156` to `bp + 232`, and
variables of the image. -/
theorem cpuW_bd (hK : K.Ok) (hlo : 152 ≤ K.bp.toNat) {a : Addr} (h : Foot (cpuW (K.bp + 104#64)) a) :
    (K.bp.toNat ≤ a.toNat + 152 ∧ a.toNat < K.bp.toNat + 112) ∨
      (K.bp.toNat + 156 ≤ a.toNat ∧ a.toNat < K.bp.toNat + 232) ∨ (0x792018 ≤ a.toNat ∧ a.toNat < 0x7a8550) := by
  have := hK.hbp
  obtain ⟨r, hr, h1, h2⟩ := h
  simp only [cpuW, icfW, irelW, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Addr.add, BitVec.reduceToNat] at h1 h2 <;> bv_omega

/-- `_dl_x86_cpu_features` is none of the variables `FinP` describes. -/
theorem cpu_not_dg {a : Addr} (h1 : 0x7a4ae0 ≤ a.toNat) (h2 : a.toNat < 0x7a4b88) : ¬ Foot (d3 ++ globals) a := by
  rintro ⟨r, hr, h1', h2'⟩
  simp only [d3, globals, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BitVec.reduceToNat] at h1' h2' <;> omega

/-- A byte of the image below the variables is as at the entry. -/
theorem Same.img (hS : Same K (d3 ++ globals) V) (hK : K.Ok) {a : Addr} (h1 : 0x400000 ≤ a.toNat)
    (h2 : a.toNat < 0x791ca0) : V a = K.V0 a :=
  hS.at1 bd_dg (clean_img hK h1 (by omega))

/-- The tunables `init_cpu_features` reads: where their `initialized` bytes lie. -/
theorem tgvInit_bd : ∀ n ∈ [16, 9, 20, 3, 15, 10], 0x791660 ≤ (tgvInit (BitVec.ofNat 64 n)).toNat ∧
    (tgvInit (BitVec.ofNat 64 n)).toNat < 0x791c10 := by decide

/-- The frame's slots of `argv`, `main` and `argc` after `init_cpu_features` and `apply_irel`. -/
theorem Fr.after (hF : Fr K V) (hK : K.Ok) (hE : Env K F Wl) (hlo : 152 ≤ K.bp.toNat) {m : Memory}
    (hoff : ∀ y, Foot F.data y → ¬ Foot (cpuW (K.bp + 104#64)) y → m.readByte y = V y) :
    Fr K fun y => m.readByte y := by
  have hbp := hK.hbp
  have himg := hK.himg
  have e : ∀ c n : Nat, 124 ≤ c → c + n ≤ 144 → List.map (fun y => m.readByte y) (byteAddrs (K.bp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.bp + BitVec.ofNat 64 c) n) := fun c n h1 h2 => by
    refine rd_congr fun i hi => ?_
    have ht := tn hK (c := c) hi (by omega)
    refine hoff _ (hE.ws _ (hE.stk _ (by omega) (by omega))) fun hf => ?_
    rcases cpuW_bd hK hlo hf with h | h | h <;> omega
  exact ⟨by rw [e 128 8 (by decide) (by decide)]; exact hF.argv,
    by rw [e 136 8 (by decide) (by decide)]; exact hF.main,
    by rw [e 124 4 (by decide) (by decide)]; exact hF.argc⟩

/-- From the entry of `__libc_start_main` to `0x6133bb`: `init_cpu_features` and `apply_irel` done. -/
theorem start_cpu (c : Seg prof F Wl L s₀ o) (hl : CodeIn L lsm_at lsm) (hp : CodeIn L Pie.pie_at Pie.pie)
    (ha : CodeIn L Auxv.aux_at Auxv.aux) (hs : CodeIn L Sec.sec_at Sec.sec) (ht : CodeIn L Tun.tin_at Tun.tin)
    (hK : K.Ok) (hE : Env K F Wl)
    (hw : ∀ y, Foot (cpuW (K.bp + 104#64)) y → Foot Wl y)
    (hIE : IE F (cpuW (K.bp + 104#64)) L K.V0 (K.bp + 104#64)) (hJ : JT F (cpuW (K.bp + 104#64)) K.V0)
    (hR : RE F (cpuW (K.bp + 104#64)) L (K.bp + 104#64))
    (hT : ∀ j < 744, ¬ Foot (cpuW (K.bp + 104#64)) ((0x400248 : Addr).add j) ∧
      K.V0 ((0x400248 : Addr).add j) = rela.getD j 0)
    (hok : CInv prof K.V0) (hpc : prof.Consistent) (hch : Chain prof) (hdf : s₀.cpu.rflags.df = false)
    (hx87 : s₀.cpu.x87.full = 0)
    (hfin : ∀ (g g' : Gprs) (V' : Addr → Byte), FinP K g' V' → ∀ (Y : State) (t' : Nat),
      g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 → KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem →
      V2606.GotOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot (cpuW (K.bp + 104#64)) y → Y.proc.mm.mem.readByte y = V' y) →
      Y.cpu.rip = 0x6133bb → TKi g' Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t')
    {X : State} {t : Nat} (hX : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at) (hI : I0 K (K.N + 20) X.cpu.gpr V) : GoG prof L o gev gP gE X t := by
  refine start_cfg c hl hp ha hs ht hK hE (fun g' fl V' hF Y t' hKY hAY hrY hgY _ => ?_) hX hA hrip hI
  subst hgY
  have hS := hF.2.2.same
  have himg := hK.himg
  have hbp := hK.hbp
  -- what `init_cpu_features` reads of the image is as at the entry
  have hIE' : IE F (cpuW (K.bp + 104#64)) L V' (K.bp + 104#64) :=
    ⟨hIE.code, hIE.codek, hIE.codet, hIE.codeg, hIE.codea, hIE.codeh, hIE.codei, hIE.w, hIE.fit, hIE.apart, hIE.lo,
      hIE.al, fun n hn => ⟨(hIE.tun n hn).ty, (hIE.tun n hn).val, (hIE.tun n hn).init, (hIE.tun n hn).nw, by
        have hb := tgvInit_bd n hn
        rw [hS.img hK (by omega) (by omega)]; exact (hIE.tun n hn).z⟩⟩
  have hJ' : JT F (cpuW (K.bp + 104#64)) V' := ⟨hJ.data, hJ.nw, fun i hi => by
    have e : ((0x6ee6d0 : Addr).add i).toNat = 0x6ee6d0 + i := tg (b := 0x6ee6d0) hi (by decide)
    rw [hS.img hK (by rw [e]; omega) (by rw [e]; omega)]; exact hJ.val i hi⟩
  have hT' : ∀ j < 744, ¬ Foot (cpuW (K.bp + 104#64)) ((0x400248 : Addr).add j) ∧
      V' ((0x400248 : Addr).add j) = rela.getD j 0 := fun j hj => ⟨(hT j hj).1, by
    have e : ((0x400248 : Addr).add j).toNat = 0x400248 + j := tg (b := 0x400248) hj (by decide)
    rw [hS.img hK (by rw [e]; omega) (by rw [e]; omega)]; exact (hT j hj).2⟩
  have hok' : CInv prof V' := hok.congr fun a i hw hi => by
    have e : ((0x7a4ae0 : Addr).add (a + i / 8)).toNat = 0x7a4ae0 + (a + i / 8) :=
      CpuFeat.tn (by rw [CpuFeat.base_toNat]; simp only [CpuFeat.Watched] at hw; omega)
    have ha : a ≤ 100 := by simp only [CpuFeat.Watched] at hw; omega
    unfold CpuFeat.bitV
    rw [show V' (cpuRgn.base.add (a + i / 8)) = K.V0 (cpuRgn.base.add (a + i / 8)) from
      hS _ (by simp only [InStk]; rw [show (cpuRgn.base.add (a + i / 8)).toNat = _ from e]; omega)
        (cpu_not_dg (by rw [show (cpuRgn.base.add (a + i / 8)).toNat = _ from e]; omega)
          (by rw [show (cpuRgn.base.add (a + i / 8)).toNat = _ from e]; omega))]
  have hsp : Y.cpu.gpr.rsp = (K.bp + 104#64).add 8 := by
    rw [hF.1.1]; simp only [Addr.add]; bv_omega
  exact CpuFeat.initCpuFeatures_applyIrel_in c hw hIE' hJ' hR hT' hpc hch hdf hx87 hKY hAY hok' (by rw [hrY]; rfl)
    hsp fun g Y' t'' hax hdi hKY' hc hg hoff hrY' hTY => hfin g Y.cpu.gpr V' hF Y' t'' hax hdi hKY' hc hg hoff hrY' hTY

end FV7z.Start
