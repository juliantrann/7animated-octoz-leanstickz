import FV7z.CpuFeat.Tgv
import FV7z.CpuFeat.Gci
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.FnSys
/-!
# `init_cpu_features` after the vendor's part (PLAN.md G2, "Dispatch theo CPUID", glibc `init_cpu_features`)

glibc 2.31's `init_cpu_features (&_dl_x86_cpu_features)`, inlined in `__libc_start_main` of `7zzs` 26.06, from
`0x61316b`, where every vendor's part joins: the `rep movsb` thresholds' bits of `feature[1]` (bits 0 and 1, which
`CpuOk` does not watch), the kind and the family, model and stepping saved, the tunables `hwcaps` (16),
`x86_ibt` and `x86_shstk` (9, 20), `x86_non_temporal_threshold` (3) and, for Intel's kind, the TSX and `Prefer_No_AVX512`
choice (`0x613592`), then `x86_data_cache_size` and `x86_shared_cache_size` (15, 10) read by `__tunable_get_val` (not
set: `Tgv.lean`), and `arch_prctl (ARCH_CET_STATUS, …)`, which the model answers `EINVAL`, to `0x613278`.

The frame: `rsp` is `q + 8`; `icfW q` what the run may store into (the frame from the return addresses of the calls
it makes to the tunables' values, `_dl_x86_cpu_features` to `0x7a4b88`, `__x86_shared_non_temporal_threshold`'s
neighbour at `0x7a4ac8`, the `memcpy` choice at `0x7a8548`). The footprint's bytes keep `CInv` and, off what the run
may store into, their values at the start (`IV`).
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

set_option linter.deprecated false

/-- What the run may store into: of the frame `[q, q + 0x80)`, the slot of the return addresses and the locals from
`q + 52` (`rsp + 0x2c`), and the stack below the frame that callees use. -/
def icfW (q : Addr) : List Rgn := [⟨q, 8⟩, ⟨q.add 52, 76⟩, ⟨0x7a4ac8, 8⟩, ⟨0x7a4ae0, 0xa8⟩, ⟨0x7a8548, 8⟩, ⟨q - 256, 256⟩]

/-- Tunable `d` can be read and is not set. -/
structure TunOk (F : Footprint) (Wl : List Rgn) (V₀ : Addr → Byte) (d : Addr) : Prop where
  ty : ∀ i < 4, Foot F.data (Addr.add (tgvEnt d + BitVec.ofNat 64 8) i)
  val : ∀ i < 8, Foot F.data (Addr.add (tgvEnt d + BitVec.ofNat 64 32) i)
  init : Foot F.data (tgvInit d)
  nw : ¬ Foot Wl (tgvInit d)
  z : V₀ (tgvInit d) = 0

/-- The setting of the run. -/
structure IE (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V₀ : Addr → Byte) (q : Addr) :
    Prop where
  code : CodeIn L 0x613113 icf
  codek : CodeIn L 0x613592 icfk
  codet : CodeIn L 0x66f3a0 tgv
  codeg : CodeIn L 0x612cc0 gci
  codea : CodeIn L 0x6132ad icfa
  codeh : CodeIn L 0x613803 icfh
  codei : CodeIn L 0x613676 icfi
  w : ∀ y, Foot (icfW q) y → Foot Wl y
  fit : q.toNat + 0x80 ≤ 2 ^ 64
  apart : 0x7a4c70 ≤ q.toNat ∨ q.toNat + 0x80 ≤ 0x7a4ae0
  lo : 256 ≤ q.toNat
  al : (q.toNat + 8) % 16 = 0
  tun : ∀ n ∈ [16, 9, 20, 3, 15, 10], TunOk F Wl V₀ (BitVec.ofNat 64 n)

/-- The footprint's bytes: `CInv`, and off what the run may store into, as at the start. -/
structure IV (prof : Profile) (Wl : List Rgn) (V₀ V : Addr → Byte) : Prop where
  inv : CInv prof V
  off : ∀ y, ¬ Foot Wl y → V y = V₀ y

theorem IV.st {prof : Profile} {Wl : List Rgn} {V₀ V : Addr → Byte} (h : IV prof Wl V₀ V) {g : Addr}
    {bs : List Byte} (hw : ∀ i < bs.length, Foot Wl (g.add i)) (hc : CInv prof (Vst V g bs)) :
    IV prof Wl V₀ (Vst V g bs) :=
  ⟨hc, fun y hy => by rw [Vst_apart bs V g y fun i hi he => hy (he ▸ hw i hi)]; exact h.off y hy⟩

theorem TK.trans {a b c : Gprs} (h : TK a b) (k : TK b c) : TK a c :=
  ⟨k.sp.trans h.sp, k.rbx.trans h.rbx, k.rbp.trans h.rbp, k.r12.trans h.r12, k.r13.trans h.r13, k.r14.trans h.r14,
    k.r15.trans h.r15⟩

/-- `TK` after a write to a register other than `rsp`, `rbx`, `rbp`, `r12`–`r15`. -/
theorem TK.set {g₀ g : Gprs} (h : TK g₀ g) {r : Nat}
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 11) (v : BitVec 64) : TK g₀ (g.set (regOf r) v) := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨h.sp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The callee-saved registers and `rsp` after a call's return. -/
theorem TK.ret {X Y Z : State} {ra : Addr} (hg : Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8))
    (h : Returns sysv Y ra Z) : TK X.cpu.gpr Z.cpu.gpr := by
  obtain ⟨-, hp, hsp, -⟩ := h
  have e : ∀ r : Reg, RegName.gpr r ∈ sysv.preserved → Z.cpu.gpr.get r = Y.cpu.gpr.get r := fun r hr => hp _ hr
  refine ⟨?_, (e 3 (by simp [sysv])).trans (by rw [hg]; rfl), (e 5 (by simp [sysv])).trans (by rw [hg]; rfl),
    (e 12 (by simp [sysv])).trans (by rw [hg]; rfl), (e 13 (by simp [sysv])).trans (by rw [hg]; rfl),
    (e 14 (by simp [sysv])).trans (by rw [hg]; rfl), (e 15 (by simp [sysv])).trans (by rw [hg]; rfl)⟩
  rw [hsp, hg]
  exact BitVec.sub_add_cancel _ _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem IE.tn {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {n : Nat} (h : n < 0x80) :
    (q.add n).toNat = q.toNat + n :=
  toNat_addn h hE.fit

/-- The frame's bytes are the run's to store into. -/
theorem IE.fr {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {n : Nat} (h : n < 8 ∨ 52 ≤ n ∧ n < 0x80) :
    Foot Wl (q.add n) := by
  have hf := hE.fit
  rcases h with h | h
  · exact hE.w _ ⟨⟨q, 8⟩, by simp [icfW], mem_add_of_fits h (by omega)⟩
  · refine hE.w _ ⟨⟨q.add 52, 76⟩, by simp [icfW], ?_⟩
    simp only [Rgn.Mem, hE.tn (n := n) (by omega), hE.tn (n := 52) (by omega)]; omega

theorem sub8 (q : Addr) : q.add 8 - 8 = q := by
  show q + BitVec.ofNat 64 8 - 8 = q
  exact BitVec.add_sub_cancel q _

/-- A store into the frame keeps `IV`. -/
theorem IV.fr {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) {n : Nat}
    {bs : List Byte} (hn : n + bs.length ≤ 0x80) (hn' : n + bs.length ≤ 8 ∨ 52 ≤ n ∧ n < 0x80) :
    IV prof Wl V₀ (Vst V (q.add n) bs) := by
  have e := hE.tn (n := n) (by omega)
  have hf := hE.fit
  have ha := hE.apart
  refine hV.st (fun i hi => by rw [addr_add_add]; exact hE.fr (by omega))
    (hV.inv.st_apart _ _ (by rw [e]; omega) fun a hw => ?_)
  rw [e]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `call __tunable_get_val` for tunable `n`, `*valp` at `q + m` in the frame. -/
theorem callT (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {Z : State} {t j : Nat}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hV : IV prof Wl V₀ V)
    (hr : Z.cpu.rip = (0x613113 : Addr).add j) {rel : Nat} (hd : Dec prof.feat icf j (FV7z.mk .call 64 [.rel rel] 5))
    (hjl : j + 5 < 357) (htgt : (0x613113 : Addr).add (j + 5) + BitVec.ofNat 64 rel = 0x66f3a0)
    (hsp : Z.cpu.gpr.rsp = q.add 8) {m : Nat} (hm : 52 ≤ m) (hm2 : m + 8 ≤ 0x80) (hsi : Z.cpu.gpr.rsi = q.add m)
    {n : Nat} (hn : n ∈ [16, 9, 20, 3, 15, 10]) (hdi : (rv Z 32 7).setWidth 64 = BitVec.ofNat 64 n)
    (k' : ∀ V', IV prof Wl V₀ V' →
      ContG prof F Wl L s₀ o gev gP gE V' fun Y => Y.cpu.rip = (0x613113 : Addr).add (j + 5) ∧ TK Z.cpu.gpr Y.cpu.gpr) :
    GoG prof L o gev gP gE Z t := by
  have hl : icf.length = 357 := icf_length
  have e8 : Z.cpu.gpr.rsp - 8 = q := by rw [hsp, sub8]
  have hf := hE.fit
  have tu := hE.tun n hn
  refine c.s_tgv hE.codet hK hA hE.code (by omega) hr hd (by omega) htgt
    (fun i hi => by rw [e8]; exact hE.fr (by omega)) (by rw [e8]; omega)
    (fun i hi => by rw [hsi, addr_add_add]; exact hE.fr (by omega))
    (fun i hi k hk h => by
      rw [e8, hsi, addr_add_add] at h
      have := congrArg BitVec.toNat h
      rw [hE.tn (by omega), hE.tn (by omega)] at this; omega)
    hdi tu.ty tu.val tu.init tu.nw (by rw [hV.off _ tu.nw]; exact tu.z) fun bs hb => ?_
  rw [e8, hsi]
  have h1 := hV.fr hE (n := 0) (bs := toBytesLE ((0x613113 : Addr).add (j + 5)) 8) (by rw [toBytesLE_length]; omega)
    (by rw [toBytesLE_length]; omega)
  rw [addr_add_zero] at h1
  exact k' _ (h1.fr hE (by omega) (by omega))

/-- The rest of the run from `0x613278`, after `arch_prctl` with the registers `g`. -/
abbrev IK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) : Prop :=
  ∀ (g : Gprs) (V : Addr → Byte) (Y : State) (t : Nat), g.rax = BitVec.ofNat 64 158 →
    g.rdi = BitVec.ofNat 64 0x3001 → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → IV prof Wl V₀ V →
    Y.cpu.rip = (0x613113 : Addr).add 357 → TK g₀ Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t

/-- From `lea rsi, [rsp + 0x70]` (`331`): `arch_prctl (ARCH_CET_STATUS, …)`, `EINVAL`, to `0x613278`. -/
theorem iSys (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
    (k : IK prof F Wl L s₀ o gev gP gE V₀ g₀) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hV : IV prof Wl V₀ V)
    (hr : X.cpu.rip = (0x613113 : Addr).add 331) (hT : TK g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  have hl : icf.length = 357 := icf_length
  refine c.s_lea_bd hK hA hE.code (by omega) hr (icf_331 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_ri32 hK1 hA1 hE.code (by omega) hr1 (icf_336 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_mov_ri32 hK2 hA2 hE.code (by omega) hr2 (icf_341 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hT3 : TK g₀ Y3.cpu.gpr := by
    rw [hg3, hg2, hg1]; exact ((hT.set (by omega) _).set (by omega) _).set (by omega) _
  have hax : Y3.cpu.gpr.rax = BitVec.ofNat 64 158 := by rw [hg3]; rfl
  have hdi : Y3.cpu.gpr.rdi = BitVec.ofNat 64 0x3001 := by rw [hg3, hg2]; rfl
  refine c.s_cet hK3 hA3 hE.code (by omega) hr3 (icf_346 _) (by rw [hax]; rfl) (by rw [hdi]; rfl) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hT4 : TK g₀ Y4.cpu.gpr := by
    rw [hg4]; exact ((hT3.set (r := 1) (by omega) _).set (r := 11) (by omega) _).set (r := 0) (by omega) _
  refine c.s_test_rr64 hK4 hA4 hE.code (by omega) hr4 (icf_348 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hz5⟩
  refine c.s_jcc_f hK5 hA5 hE.code (by omega) hr5 (icf_351 _) (by
    rw [Rflags.cond, hz5]; simp only [rv, hg4]
    rw [show ((sysGpr Y3 2).set 0 (errRet EINVAL)).get (regOf 0) = errRet EINVAL from rfl]; decide) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  exact k _ _ Y6 t6 hax hdi hK6 hA6 hV hr6 (by rw [hg6, hg5]; exact hT4)

theorem eaD_sp {Y : State} {q : Addr} (h : Y.cpu.gpr.rsp = q.add 8) (d : Nat) : eaD Y 4 d = q.add (8 + d) := by
  simp only [eaD, get_regOf_4, h]; exact add_addn q 8 d

theorem rv_mov {Y : State} {g : Gprs} {v : BitVec 64} (h : Y.cpu.gpr = g.set (regOf 7) v) :
    rv Y 32 7 = v.setWidth 32 := by
  simp only [rv, h]; rfl

/-- From `lea rsi, [rsp + 0x60]` (`287`, where Intel's kind's part joins): tunables 15 and 10, then `iSys`. -/
theorem iT2 (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
    (hsp0 : g₀.rsp = q.add 8) (k : IK prof F Wl L s₀ o gev gP gE V₀ g₀) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hV : IV prof Wl V₀ V)
    (hr : X.cpu.rip = (0x613113 : Addr).add 287) (hT : TK g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  have hl : icf.length = 357 := icf_length
  refine c.s_lea_bd hK hA hE.code (by omega) hr (icf_287 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_lea_rip hK1 hA1 hE.code (by omega) hr1 (icf_292 _) (v := 0x671c10) (by decide) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, -⟩
  refine c.s_mov_ri32 hK2 hA2 hE.code (by omega) hr2 (icf_299 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hT3 : TK g₀ Y3.cpu.gpr := by
    rw [hg3, hg2, hg1]; exact ((hT.set (by omega) _).set (by omega) _).set (by omega) _
  refine callT c hE hK3 hA3 hV hr3 (icf_304 _) (by omega) (by decide) (hT3.sp.trans hsp0) (m := 104) (by omega)
    (by omega) (by rw [hg3, hg2, hg1]; exact eaD_sp (hT.sp.trans hsp0) 96) (n := 15) (by simp)
    (by rw [rv_mov hg3]; rfl) fun V4 hV4 => ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hT4'⟩
  have hT4 := hT3.trans hT4'
  refine c.s_lea_bd hK4 hA4 hE.code (by omega) hr4 (icf_309 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_mov_ri32 hK5 hA5 hE.code (by omega) hr5 (icf_314 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_lea_rip hK6 hA6 hE.code (by omega) hr6 (icf_319 _) (v := 0x671cb0) (by decide) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, -⟩
  have hT7 : TK g₀ Y7.cpu.gpr := by
    rw [hg7, hg6, hg5]; exact ((hT4.set (by omega) _).set (by omega) _).set (by omega) _
  refine callT c hE hK7 hA7 hV4 hr7 (icf_326 _) (by omega) (by decide) (hT7.sp.trans hsp0) (m := 112) (by omega)
    (by omega) (by rw [hg7, hg6, hg5]; exact eaD_sp (hT4.sp.trans hsp0) 104) (n := 10) (by simp)
    (by simp only [rv, hg7, hg6]; rfl) fun V8 hV8 => ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hT8'⟩
  exact iSys c hE k hK8 hA8 hV8 hr8 (hT7.trans hT8')

/-- From the `j`-th byte of the code at `e`, the run goes on (with `TK g₀`, `IV`) to the goal. -/
def AtK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (e : Addr) (j : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → IV prof Wl V₀ V →
    X.cpu.rip = e.add j → TK g₀ X.cpu.gpr → GoG prof L o gev gP gE X t

/-- `_dl_x86_cpu_features`' bytes are the run's to store into. -/
theorem IE.cf {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {a i : Nat} (h : a + i < 0xa8) :
    Foot Wl (((0x7a4ae0 : Addr).add a).add i) := by
  rw [addr_add_add]
  exact hE.w _ ⟨_, by simp [icfW], mem_add_of_fits h (by decide)⟩

/-- A word of `_dl_x86_cpu_features` can be read. -/
theorem IE.cfd (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {a n : Nat}
    (h : a + n ≤ 0xa8) : ∀ i < n, Foot F.data (((0x7a4ae0 : Addr).add a).add i) :=
  fun _ hi => c.hws _ (hE.cf (by omega))

/-- A store apart from the watched words keeps `IV`. -/
theorem IV.stx {V₀ V : Addr → Byte} (hV : IV prof Wl V₀ V) {g : Addr} {bs : List Byte}
    (hw : ∀ i < bs.length, Foot Wl (g.add i)) (hf : g.toNat + bs.length ≤ 2 ^ 64)
    (hap : 0x7a4b48 ≤ g.toNat ∨ g.toNat + bs.length ≤ 0x7a4ae0) : IV prof Wl V₀ (Vst V g bs) :=
  hV.st hw (hV.inv.st_apart _ _ hf fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)

/-- Into `0x7a8548` (8 bytes). -/
theorem IV.st548 {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) (v : BitVec 64) :
    IV prof Wl V₀ (Vst V 0x7a8548 (toBytesLE v 8)) :=
  hV.stx (fun i hi => hE.w _ ⟨_, by simp [icfW], mem_add_of_fits (n := 8) (by simpa using hi) (by decide)⟩)
    (by simp) (by simp)

/-- Into `0x7a4ac8` (8 bytes). -/
theorem IV.stac8 {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) (v : BitVec 64) :
    IV prof Wl V₀ (Vst V 0x7a4ac8 (toBytesLE v 8)) :=
  hV.stx (fun i hi => hE.w _ ⟨_, by simp [icfW], mem_add_of_fits (n := 8) (by simpa using hi) (by decide)⟩)
    (by simp) (by simp)

/-- `or [feature[1]], imm` without bit 8 (`AVX_Fast_Unaligned_Load`), the one `CpuOk` watches. -/
theorem CInv.or_f1 {V : Addr → Byte} (h : CInv prof V) (imm : Nat) (h8 : (BitVec.ofNat 32 imm).getLsbD 8 = false) :
    CInv prof (Vst V (cpuRgn.base.add 100) (toBytesLE (rdw V 100 ||| BitVec.ofNat 32 imm) 4)) := by
  refine h.st_f1 _ ⟨h.f.avx, h.f.avx2, h.f.avx512f, h.f.avx512vl, h.f.avx512dq, h.f.avx512bw, h.f.fma, h.f.vaes,
    fun hb => h.f.fastAvx ?_⟩
  rw [getLsbD_rd_or imm (by omega), h8, Bool.or_false] at hb
  exact hb

theorem IV.or_f1 {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) (imm : Nat)
    (h8 : (BitVec.ofNat 32 imm).getLsbD 8 = false) :
    IV prof Wl V₀ (Vst V (cpuRgn.base.add 100) (toBytesLE (rdw V 100 ||| BitVec.ofNat 32 imm) 4)) :=
  hV.st (fun i hi => hE.cf (by simp at hi; omega)) (hV.inv.or_f1 imm h8)

/-- A store into `_dl_x86_cpu_features` past the watched words. -/
theorem IV.stcf {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) {a : Nat}
    (ha : 104 ≤ a) {bs : List Byte} (hb : a + bs.length ≤ 0xa8) (hb' : a < 0xa8) :
    IV prof Wl V₀ (Vst V ((0x7a4ae0 : Addr).add a) bs) := by
  have e : ((0x7a4ae0 : Addr).add a).toNat = 0x7a4ae0 + a := CpuFeat.tn (by rw [base_toNat]; omega)
  exact hV.stx (fun i hi => hE.cf (by omega)) (by rw [e]; omega) (Or.inl (by rw [e]; omega))

/-- A pointer `get_common_indices` stores into: 4 bytes of the frame's locals, from `q + 52`. -/
def PI (q p : Addr) : Prop := ∃ m, 52 ≤ m ∧ m + 4 ≤ 0x80 ∧ p = q.add m

theorem gW_mem {q : Addr} {Y : State}
    (hptr : Y.cpu.gpr.rdi ≠ 0 → PI q Y.cpu.gpr.rdi ∧ PI q Y.cpu.gpr.rsi ∧ PI q Y.cpu.gpr.rdx ∧ PI q Y.cpu.gpr.rcx)
    {r : Rgn} (hr : r ∈ gW Y) : r = cfR ∨ ∃ m, 52 ≤ m ∧ m + 4 ≤ 0x80 ∧ r = ⟨q.add m, 4⟩ := by
  simp only [gW, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact Or.inl rfl
  split at hr
  · simp at hr
  obtain ⟨a, b, c, d⟩ := hptr ‹_›
  simp only [gPtrs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨m, h1, h2, h3⟩ := a; exact Or.inr ⟨m, h1, h2, by rw [h3]⟩
  · obtain ⟨m, h1, h2, h3⟩ := b; exact Or.inr ⟨m, h1, h2, by rw [h3]⟩
  · obtain ⟨m, h1, h2, h3⟩ := c; exact Or.inr ⟨m, h1, h2, by rw [h3]⟩
  · obtain ⟨m, h1, h2, h3⟩ := d; exact Or.inr ⟨m, h1, h2, by rw [h3]⟩

/-- `call get_common_indices` with `rsp = q + 8`, its pointers, if any, in the frame: the run goes on after it, with
`IV` of the bytes after the return. -/
theorem callG (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q)
    (hpc : prof.Consistent) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    {Z : State} {t j : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V)
    (hV : IV prof Wl V₀ V) {e : Addr} {code : List Byte} (hin : CodeIn L e code) (hj : j < code.length)
    (hr : Z.cpu.rip = e.add j) {rel : Nat} (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] 5))
    (hjl : j + 5 < code.length) (htgt : e.add (j + 5) + BitVec.ofNat 64 rel = 0x612cc0)
    (hcan : (e.add (j + 5)).canonical prof.feat.la57 = true) (hsp : Z.cpu.gpr.rsp = q.add 8)
    (hptr : Z.cpu.gpr.rdi ≠ 0 → PI q Z.cpu.gpr.rdi ∧ PI q Z.cpu.gpr.rsi ∧ PI q Z.cpu.gpr.rdx ∧ PI q Z.cpu.gpr.rcx)
    (k' : ∀ V', IV prof Wl V₀ V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e.add (j + 5) →
      TK Z.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE Z t := by
  have hf := hE.fit
  have hlo := hE.lo
  have hap := hE.apart
  have hq8 : (q.add 8).toNat = q.toNat + 8 := hE.tn (by omega)
  have hq : Z.cpu.gpr.rsp - 8 = q := by rw [hsp, sub8]
  have hqs : (q - BitVec.ofNat 64 256).toNat = q.toNat - 256 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hqs' : (q - 256).toNat = q.toNat - 256 := hqs
  have h1 : ∀ r : Addr, IV prof Wl V₀ (Vst V q (toBytesLE r 8)) := fun r => by
    have := hV.fr hE (n := 0) (bs := toBytesLE r 8) (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega)
    rwa [addr_add_zero] at this
  -- the regions `gW` names, in what the run may store into
  have hgw : ∀ Y : State, Y.cpu.gpr = Z.cpu.gpr.set 4 (Z.cpu.gpr.rsp - 8) → ∀ y, Foot (gW Y) y →
      Rgn.Mem ⟨0x7a4ae0, 0x90⟩ y ∨ ∃ m, 52 ≤ m ∧ m + 4 ≤ 0x80 ∧ q.toNat + m ≤ y.toNat ∧ y.toNat < q.toNat + m + 4 := by
    rintro Y hgY y ⟨r, hr, hm⟩
    rcases gW_mem (q := q) (Y := Y) (by rw [hgY]; exact hptr) hr with rfl | ⟨m, h1, h2, rfl⟩
    · exact Or.inl hm
    · simp only [Rgn.Mem, hE.tn (n := m) (by omega)] at hm
      exact Or.inr ⟨m, h1, h2, hm⟩
  have hws : ∀ Y : State, Y.cpu.gpr = Z.cpu.gpr.set 4 (Z.cpu.gpr.rsp - 8) → ∀ y, Foot (ws 256 gW Y) y →
      Foot Wl y := by
    rintro Y hgY y ⟨r, hr, hm⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · refine hE.w _ ⟨⟨q - 256, 256⟩, by simp [icfW], ?_⟩
      have hYs : Y.cpu.gpr.rsp = q := by rw [hgY]; exact hq
      simp only [below, hYs, Rgn.Mem] at hm ⊢; exact hm
    · rcases hgw Y hgY y ⟨r, hr, hm⟩ with hm | ⟨m, h1, h2, h3, h4⟩
      · exact hE.w _ ⟨⟨0x7a4ae0, 0xa8⟩, by simp [icfW], by simp only [Rgn.Mem] at hm ⊢; omega⟩
      · exact hE.w _ ⟨⟨q.add 52, 76⟩, by simp [icfW], by simp only [Rgn.Mem, hE.tn (n := 52) (by omega)]; omega⟩
  have hl := hE.codeg
  refine c.s_callK hK hA hin hj hr hd hE.codeg (by rw [gci_length]; omega) htgt
    (fun i hi => by rw [hq]; exact hE.fr (by omega)) (by rw [hq]; omega) (getCommonIndicesK prof hpc hE.codeg)
    hdf hx87 hcan (by rw [hsp, hq8]; exact hE.al) ?_ ?_
  · intro Y hKY hAY hrY hgY
    have hYs : Y.cpu.gpr.rsp = q := by rw [hgY]; exact hq
    have hpY : Y.cpu.gpr.rdi ≠ 0 → PI q Y.cpu.gpr.rdi ∧ PI q Y.cpu.gpr.rsi ∧ PI q Y.cpu.gpr.rdx ∧
        PI q Y.cpu.gpr.rcx := by rw [hgY]; exact hptr
    refine ⟨⟨?_, ?_, fun _ h => by simp [Contract.footprint, fnK, fn, gR, Foot] at h, c.code.symm ▸ rfl, rfl, c.own⟩,
      fun y hy => hws Y hgY y hy, ⟨?_, ?_, fun h => ?_⟩, ?_⟩
    · intro r hr
      simp only [Contract.footprint, fnK, fn, gR, List.append_nil, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp only [Rgn.Fits, frame, hYs, hqs]; omega
      · rcases gW_mem hpY hr with rfl | ⟨m, h1, h2, rfl⟩
        · simp [Rgn.Fits, cfR]
        · simp only [Rgn.Fits, hE.tn (n := m) (by omega)]; omega
    · rintro y ⟨r, hr, hm⟩
      simp only [Contract.footprint, fnK, fn, List.mem_cons] at hr
      obtain ⟨r', hr', hm'⟩ := c.hww y (by
        rcases hr with rfl | hr
        · simp only [frame, hYs, Rgn.Mem, hqs] at hm
          by_cases hy : y.toNat < q.toNat
          · exact hE.w _ ⟨⟨q - 256, 256⟩, by simp [icfW], by simp only [Rgn.Mem, hqs']; omega⟩
          · exact hE.w _ ⟨⟨q, 8⟩, by simp [icfW], by simp only [Rgn.Mem]; omega⟩
        · exact hws Y hgY y ⟨r, List.mem_cons_of_mem _ hr, hm⟩)
      exact ⟨r', hr', hm'⟩
    · rw [hq] at hAY
      exact (h1 _).inv.mem fun j hj => hAY _ (c.hws _ (by
        have := hE.cf (a := j) (i := 0) (by omega); rwa [addr_add_zero] at this))
    · rw [hYs]; omega
    · obtain ⟨a, b, c', d⟩ := hpY h
      have pk : ∀ p, PI q p → PtrOk Y p := by
        rintro p ⟨m, h1, h2, rfl⟩
        rw [PtrOk, hYs, hE.tn (n := m) (by omega)]; omega
      exact ⟨pk _ a, pk _ b, pk _ c', pk _ d⟩
    · intro i hi hm
      rw [hYs] at hm
      rcases hgw Y hgY _ hm with hm | ⟨m, h1, h2, h3, h4⟩
      · simp only [Rgn.Mem, hE.tn (n := i) (by omega), base_toNat] at hm; omega
      · rw [hE.tn (n := i) (by omega)] at h3; omega
  · intro Y Z' t' hKY hgY hKZ hmem hret hpost
    have hYs : Y.cpu.gpr.rsp = q := by rw [hgY]; exact hq
    rw [hq] at hmem
    let V' : Addr → Byte := fun y => if Foot (ws 256 gW Y) y then Z'.proc.mm.mem.readByte y
      else Vst V q (toBytesLE (e.add (j + 5)) 8) y
    have hAZ : Agree F Z'.proc.mm.mem V' := fun y hy => by
      by_cases h : Foot (ws 256 gW Y) y
      · show _ = ite _ _ _; rw [if_pos h]
      · show _ = ite _ _ _; rw [if_neg h]; exact hmem y hy h
    have hVZ : IV prof Wl V₀ V' := by
      refine ⟨(CInv.of_cpuOk hpost).congr fun a i ha hi => ?_, fun y hy => ?_⟩
      · unfold bitV
        have hm : Foot (ws 256 gW Y) (cpuRgn.base.add (a + i / 8)) := ⟨cfR, by simp [ws, gW],
          show Rgn.Mem ⟨0x7a4ae0, 0x90⟩ ((0x7a4ae0 : Addr).add _) from
            mem_add_of_fits (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega) (by decide)⟩
        rw [show V' (cpuRgn.base.add (a + i / 8)) = Z'.proc.mm.mem.readByte _ from if_pos hm]
      · show ite _ _ _ = _
        rw [if_neg fun h => hy (hws Y hgY y h)]
        exact (h1 _).off y hy
    exact k' V' hVZ Z' t' hKZ hAZ hret.1 (TK.ret hgY hret)

section K
variable (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
  (hsp0 : g₀.rsp = q.add 8) (k : IK prof F Wl L s₀ o gev gP gE V₀ g₀)
include c hE hsp0 k

theorem iT2' : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 287 :=
  fun _ _ _ hK hA hV hr hT => iT2 c hE hsp0 k hK hA hV hr hT

/-- Intel's kind, from `mov [rip], rax` (`0x6135bf`): the `memcpy` choice, back to `287`. -/
theorem iK45 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613592 45 := by
  intro X t V hK hA hV hr hT
  have hl : icfk.length = 172 := icfk_length
  refine c.s_mov_rip_r64 hK hA hE.codek (by omega) hr (icfk_45 _) (g := 0x7a8548) (by decide)
    (fun i hi => hE.w _ ⟨_, by simp [icfW], mem_add_of_fits hi (by decide)⟩) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jmp_x hK1 hA1 hE.codek (by omega) hr1 (icfk_52 _) hE.code (tgt := 287) (by rw [icf_length]; omega)
    (by decide) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact iT2' c hE hsp0 k Y2 t2 _ hK2 hA2 (hV.st548 hE _) hr2 (by rw [hg2, hg1]; exact hT)

/-- Intel's kind, from `and edx, 0x20002` (`0x6135ea`): `Prefer_No_AVX512` or not. -/
theorem iK88 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613592 88 := by
  intro X t V hK hA hV hr hT
  have hl : icfk.length = 172 := icfk_length
  have hl' : icf.length = 357 := icf_length
  refine c.s_and_ri32 hK hA hE.codek (by omega) hr (icfk_88 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT.set (by omega) _
  refine c.s_cmp_ri32 hK1 hA1 hE.codek (by omega) hr1 (icfk_94 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, -⟩
  refine c.s_jcc_x hK2 hA2 hE.codek (by omega) hr2 (icfk_100 _) hE.code (tgt := 287) (by omega) (by decide)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iT2' c hE hsp0 k Y t' _ hKY hAY hV hrY (by rw [hgY, hg2]; exact hT1))
    fun _ => ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_r32_rip hK3 hA3 hE.codek (by omega) hr3 (icfk_106 _) (g := (0x7a4ae0 : Addr).add 20) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  refine c.s_and_ri32 hK4 hA4 hE.codek (by omega) hr4 (icfk_112 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, -⟩
  have hT5 : TK g₀ Y5.cpu.gpr := by rw [hg5, hg4, hg3, hg2]; exact (hT1.set (by omega) _).set (by omega) _
  refine c.s_cmp_ri32 hK5 hA5 hE.codek (by omega) hr5 (icfk_117 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, -⟩
  refine c.s_jcc_x hK6 hA6 hE.codek (by omega) hr6 (icfk_122 _) hE.code (tgt := 287) (by omega) (by decide)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iT2' c hE hsp0 k Y t' _ hKY hAY hV hrY (by rw [hgY, hg6]; exact hT5))
    fun _ => ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_test_m8i_rip hK7 hA7 hE.codek (by omega) hr7 (icfk_128 _) (g := ((0x7a4ae0 : Addr).add 40).add 0)
    (by decide) (hE.cfd c (n := 1) (by omega) 0 (by omega)) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, -⟩
  have hT8 : TK g₀ Y8.cpu.gpr := by rw [hg8, hg7, hg6]; exact hT5
  refine c.s_jcc_x hK8 hA8 hE.codek (by omega) hr8 (icfk_135 _) hE.code (tgt := 287) (by omega) (by decide)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iT2' c hE hsp0 k Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT8))
    fun _ => ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  refine c.s_mov_r32_rip hK9 hA9 hE.codek (by omega) hr9 (icfk_141 _) (g := (0x7a4ae0 : Addr).add 8) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  refine c.s_and_ri32 hK10 hA10 hE.codek (by omega) hr10 (icfk_147 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
  have hT11 : TK g₀ Y11.cpu.gpr := by rw [hg11, hg10, hg9]; exact (hT8.set (by omega) _).set (by omega) _
  refine c.s_cmp_ri32 hK11 hA11 hE.codek (by omega) hr11 (icfk_152 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
  refine c.s_jcc_x hK12 hA12 hE.codek (by omega) hr12 (icfk_157 _) hE.code (tgt := 287) (by omega) (by decide)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iT2' c hE hsp0 k Y t' _ hKY hAY hV hrY (by rw [hgY, hg12]; exact hT11))
    fun _ => ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  refine c.s_lea_rip hK13 hA13 hE.codek (by omega) hr13 (icfk_163 _) (v := 0x6ee611) (by decide) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, -⟩
  refine c.s_jmp hK14 hA14 hE.codek (by omega) hr14 (icfk_170 _) (tgt := 45) (by decide) (by omega) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  exact iK45 c hE hsp0 k Y15 t15 _ hK15 hA15 hV hr15
    (by rw [hg15, hg14, hg13, hg12]; exact hT11.set (by omega) _)

/-- Intel's kind, from `0x613592`: the TSX choice (`RTM`), then `iK88`. -/
theorem iK0 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613592 0 := by
  intro X t V hK hA hV hr hT
  have hl : icfk.length = 172 := icfk_length
  have k88 := iK88 c hE hsp0 k
  refine c.s_mov_r32_rip hK hA hE.codek (by omega) hr (icfk_0 _) (g := (0x7a4ae0 : Addr).add 96) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT.set (by omega) _
  refine c.s_fl hK1 hA1 hE.codek (by omega) hr1 fl_test_r8i (icfk_6 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  replace hr2 : Y2.cpu.rip = (0x613592 : Addr).add 9 := hr2
  rw [← hg2] at hT1
  refine c.s_jcc hK2 hA2 hE.codek (by omega) hr2 (icfk_9 _) (tgt := 88) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => k88 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT1)) fun _ => ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  rw [← hg3] at hT1
  refine c.s_mov_r32_rip hK3 hA3 hE.codek (by omega) hr3 (icfk_11 _) (g := (0x7a4ae0 : Addr).add 20) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hT4 : TK g₀ Y4.cpu.gpr := by rw [hg4]; exact hT1.set (by omega) _
  refine c.s_fl hK4 hA4 hE.codek (by omega) hr4 fl_test_ri32 (icfk_17 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  replace hr5 : Y5.cpu.rip = (0x613592 : Addr).add 22 := hr5
  rw [← hg5] at hT4
  refine c.s_jcc hK5 hA5 hE.codek (by omega) hr5 (icfk_22 _) (tgt := 88) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => k88 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT4)) fun _ => ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  rw [← hg6] at hT4
  refine c.s_fl hK6 hA6 hE.codek (by omega) hr6 fl_test_ri32 (icfk_24 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  replace hr7 : Y7.cpu.rip = (0x613592 : Addr).add 29 := hr7
  rw [← hg7] at hT4
  refine c.s_jcc hK7 hA7 hE.codek (by omega) hr7 (icfk_29 _) (tgt := 57) (by decide) (by omega) ?_ fun _ => ?_
  · -- `57`: `HLE`/`RTM_ALWAYS_ABORT` and the errata check
    intro _
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    rw [← hg8] at hT4
    refine c.s_mov_rr32 hK8 hA8 hE.codek (by omega) hr8 (icfk_57 _) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_and_ri32 hK9 hA9 hE.codek (by omega) hr9 (icfk_59 _) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10, -⟩
    have hT10 : TK g₀ Y10.cpu.gpr := by rw [hg10, hg9]; exact (hT4.set (by omega) _).set (by omega) _
    refine c.s_cmp_ri32 hK10 hA10 hE.codek (by omega) hr10 (icfk_65 _) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
    rw [← hg11] at hT10
    refine c.s_jcc hK11 hA11 hE.codek (by omega) hr11 (icfk_71 _) (tgt := 88) (by decide) (by omega)
      (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => k88 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT10)) fun _ => ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
    rw [← hg12] at hT10
    refine c.s_fl hK12 hA12 hE.codek (by omega) hr12 fl_test_rr32 (icfk_73 _) ?_
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    replace hr13 : Y13.cpu.rip = (0x613592 : Addr).add 75 := hr13
    rw [← hg13] at hT10
    refine c.s_jcc hK13 hA13 hE.codek (by omega) hr13 (icfk_75 _) (tgt := 88) (by decide) (by omega)
      (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => k88 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT10)) fun _ => ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    rw [← hg14] at hT10
    refine c.s_mov_rip_i64 hK14 hA14 hE.codek (by omega) hr14 (icfk_77 _) (g := 0x7a4ac8) (by decide)
      (fun i hi => hE.w _ ⟨_, by simp [icfW], mem_add_of_fits hi (by decide)⟩) ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    exact k88 Y15 t15 _ hK15 hA15 (hV.stac8 hE _) hr15 (by rw [hg15]; exact hT10)
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  rw [← hg8] at hT4
  refine c.s_fl hK8 hA8 hE.codek (by omega) hr8 fl_test_ri32 (icfk_31 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  replace hr9 : Y9.cpu.rip = (0x613592 : Addr).add 36 := hr9
  rw [← hg9] at hT4
  refine c.s_jcc hK9 hA9 hE.codek (by omega) hr9 (icfk_36 _) (tgt := 88) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => k88 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT4)) fun _ => ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  rw [← hg10] at hT4
  refine c.s_lea_rip hK10 hA10 hE.codek (by omega) hr10 (icfk_38 _) (v := 0x6ee608) (by decide) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
  exact iK45 c hE hsp0 k Y11 t11 _ hK11 hA11 hV hr11 (by rw [hg11]; exact hT4.set (by omega) _)

/-- From `mov edx, [cpuid[1].edx]` (`0x61316b`, where every vendor's part joins), to `iK0` or `iT2`. -/
theorem iT1 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 88 := by
  intro X t V hK hA hV hr hT
  have hl : icf.length = 357 := icf_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := hT.sp.trans hsp0
  -- from `0x613189`: the kind and the family, model, stepping; four tunables
  have rest : ∀ (Y : State) (t' : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      IV prof Wl V₀ V → Y.cpu.rip = (0x613113 : Addr).add 118 → TK g₀ Y.cpu.gpr →
      GoG prof L o gev gP gE Y t' := by
    intro Y0 t0 V hK0 hA0 hV hr0 hT0
    have hs0 : Y0.cpu.gpr.rsp = q.add 8 := hT0.sp.trans hsp0
    refine c.s_mov_rip_r32 hK0 hA0 hE.code (by omega) hr0 (icf_118 _) (g := (0x7a4ae0 : Addr).add 104) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hV1 := hV.stcf hE (a := 104) (by omega) (bs := toBytesLE (rv Y0 32 0) 4) (by simp) (by omega)
    have hs1 : Y1.cpu.gpr.rsp = q.add 8 := by rw [hg1]; exact hs0
    refine c.s_mov_rm hK1 hA1 hE.code (by omega) hr1 (Or.inl rfl) (icf_124 _)
      (fun i hi => by rw [eaD_sp hs1, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    have hs2 : Y2.cpu.gpr.rsp = q.add 8 := by rw [hg2]; exact hs1
    refine c.s_lea_bd hK2 hA2 hE.code (by omega) hr2 (icf_128 _) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    refine c.s_lea_rip hK3 hA3 hE.code (by omega) hr3 (icf_133 _) (v := 0x671020) (by decide) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, -⟩
    refine c.s_mov_ri32 hK4 hA4 hE.code (by omega) hr4 (icf_140 _) ?_
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    refine c.s_mov_rip_r32 hK5 hA5 hE.code (by omega) hr5 (icf_145 _) (g := (0x7a4ae0 : Addr).add 112) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have hV6 := (hV1.stcf hE (a := 112) (by omega) (bs := toBytesLE (rv Y5 32 0) 4) (by simp) (by omega))
    have hs6 : Y6.cpu.gpr.rsp = q.add 8 := by simp only [hg6, hg5, hg4, hg3, set_rdi, set_rdx, set_rsi]; exact hs2
    refine c.s_mov_rm hK6 hA6 hE.code (by omega) hr6 (Or.inl rfl) (icf_151 _)
      (fun i hi => by rw [eaD_sp hs6, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    refine c.s_mov_rip_r32 hK7 hA7 hE.code (by omega) hr7 (icf_155 _) (g := (0x7a4ae0 : Addr).add 116) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    have hV8 := (hV6.stcf hE (a := 116) (by omega) (bs := toBytesLE (rv Y7 32 0) 4) (by simp) (by omega))
    have hs8 : Y8.cpu.gpr.rsp = q.add 8 := by simp only [hg8, hg7, set_rax]; exact hs6
    refine c.s_mov_rm hK8 hA8 hE.code (by omega) hr8 (Or.inl rfl) (icf_161 _)
      (fun i hi => by rw [eaD_sp hs8, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_mov_rip_r32 hK9 hA9 hE.code (by omega) hr9 (icf_165 _) (g := (0x7a4ae0 : Addr).add 120) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    have hV10 := (hV8.stcf hE (a := 120) (by omega) (bs := toBytesLE (rv Y9 32 0) 4) (by simp) (by omega))
    have hT10 : TK g₀ Y10.cpu.gpr := by
      rw [hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]
      exact (((((hT0.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set
        (by omega) _
    refine callT c hE hK10 hA10 hV10 hr10 (icf_171 _) (by omega) (by decide) (hT10.sp.trans hsp0) (m := 72)
      (by omega) (by omega)
      (by simp only [hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, set_rax, set_rdi, set_rdx, set_rsi]; exact eaD_sp hs2 64)
      (n := 16) (by simp) (by simp only [rv, hg10, hg9, hg8, hg7, hg6, hg5]; rfl) fun W1 hW1 => ?_
    rintro Z1 u1 hL1 hB1 ⟨hq1, hU1⟩
    have hT11 := hT10.trans hU1
    refine c.s_xor_rr32 hL1 hB1 hE.code (by omega) hq1 (icf_176 _) ?_
    rintro Z2 u2 hL2 hB2 ⟨hq2, hh2⟩
    refine c.s_lea_bd hL2 hB2 hE.code (by omega) hq2 (icf_178 _) ?_
    rintro Z3 u3 hL3 hB3 ⟨hq3, hh3⟩
    refine c.s_mov_ri32 hL3 hB3 hE.code (by omega) hq3 (icf_183 _) ?_
    rintro Z4 u4 hL4 hB4 ⟨hq4, hh4⟩
    have hU4 : TK g₀ Z4.cpu.gpr := by
      rw [hh4, hh3, hh2]; exact ((hT11.set (by omega) _).set (by omega) _).set (by omega) _
    refine callT c hE hL4 hB4 hW1 hq4 (icf_188 _) (by omega) (by decide) (hU4.sp.trans hsp0) (m := 80)
      (by omega) (by omega)
      (by simp only [hh4, hh3, set_rdi, set_rsi]; exact eaD_sp (by rw [hh2]; exact hT11.sp.trans hsp0) 72)
      (n := 9) (by simp) (by simp only [rv, hh4]; rfl) fun W2 hW2 => ?_
    rintro Z5 u5 hL5 hB5 ⟨hq5, hU5⟩
    have hT12 := hU4.trans hU5
    have hs12 : Z5.cpu.gpr.rsp = q.add 8 := hT12.sp.trans hsp0
    refine c.s_mov_rm hL5 hB5 hE.code (by omega) hq5 (Or.inr rfl) (icf_193 _)
      (fun i hi => by rw [eaD_sp hs12, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Z6 u6 hL6 hB6 ⟨hq6, hh6⟩
    refine c.s_xor_rr32 hL6 hB6 hE.code (by omega) hq6 (icf_198 _) ?_
    rintro Z7 u7 hL7 hB7 ⟨hq7, hh7⟩
    refine c.s_lea_bd hL7 hB7 hE.code (by omega) hq7 (icf_200 _) ?_
    rintro Z8 u8 hL8 hB8 ⟨hq8, hh8⟩
    refine c.s_mov_ri32 hL8 hB8 hE.code (by omega) hq8 (icf_205 _) ?_
    rintro Z9 u9 hL9 hB9 ⟨hq9, hh9⟩
    refine c.s_mov_rip_r64 hL9 hB9 hE.code (by omega) hq9 (icf_210 _) (g := (0x7a4ae0 : Addr).add 160) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Z10 u10 hL10 hB10 ⟨hq10, hh10⟩
    have hW3 := hW2.stcf hE (a := 160) (by omega) (bs := toBytesLE (Z9.cpu.gpr.get (regOf 0)) 8) (by simp) (by omega)
    have hU10 : TK g₀ Z10.cpu.gpr := by
      rw [hh10, hh9, hh8, hh7, hh6]
      exact (((hT12.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _
    refine callT c hE hL10 hB10 hW3 hq10 (icf_217 _) (by omega) (by decide) (hU10.sp.trans hsp0) (m := 88)
      (by omega) (by omega)
      (by simp only [hh10, hh9, hh8, set_rdi, set_rsi]; exact eaD_sp (by rw [hh7, hh6]; exact hs12) 80)
      (n := 20) (by simp) (by simp only [rv, hh10, hh9]; rfl) fun W4 hW4 => ?_
    rintro Z11 u11 hL11 hB11 ⟨hq11, hU11⟩
    have hT13 := hU10.trans hU11
    have hs13 : Z11.cpu.gpr.rsp = q.add 8 := hT13.sp.trans hsp0
    refine c.s_mov_rm hL11 hB11 hE.code (by omega) hq11 (Or.inr rfl) (icf_222 _)
      (fun i hi => by rw [eaD_sp hs13, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Z12 u12 hL12 hB12 ⟨hq12, hh12⟩
    refine c.s_xor_rr32 hL12 hB12 hE.code (by omega) hq12 (icf_227 _) ?_
    rintro Z13 u13 hL13 hB13 ⟨hq13, hh13⟩
    refine c.s_lea_bd hL13 hB13 hE.code (by omega) hq13 (icf_229 _) ?_
    rintro Z14 u14 hL14 hB14 ⟨hq14, hh14⟩
    refine c.s_mov_ri32 hL14 hB14 hE.code (by omega) hq14 (icf_234 _) ?_
    rintro Z15 u15 hL15 hB15 ⟨hq15, hh15⟩
    refine c.s_mov_rip_r64 hL15 hB15 hE.code (by omega) hq15 (icf_239 _) (g := (0x7a4ae0 : Addr).add 144) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Z16 u16 hL16 hB16 ⟨hq16, hh16⟩
    have hW5 := hW4.stcf hE (a := 144) (by omega) (bs := toBytesLE (Z15.cpu.gpr.get (regOf 0)) 8) (by simp) (by omega)
    have hU16 : TK g₀ Z16.cpu.gpr := by
      rw [hh16, hh15, hh14, hh13, hh12]
      exact (((hT13.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _
    refine callT c hE hL16 hB16 hW5 hq16 (icf_246 _) (by omega) (by decide) (hU16.sp.trans hsp0) (m := 96)
      (by omega) (by omega)
      (by simp only [hh16, hh15, hh14, set_rdi, set_rsi]; exact eaD_sp (by rw [hh13, hh12]; exact hs13) 88)
      (n := 3) (by simp) (by simp only [rv, hh16, hh15]; rfl) fun W6 hW6 => ?_
    rintro Z17 u17 hL17 hB17 ⟨hq17, hU17⟩
    have hT14 := hU16.trans hU17
    have hs14 : Z17.cpu.gpr.rsp = q.add 8 := hT14.sp.trans hsp0
    refine c.s_mov_rm hL17 hB17 hE.code (by omega) hq17 (Or.inr rfl) (icf_251 _)
      (fun i hi => by rw [eaD_sp hs14, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Z18 u18 hL18 hB18 ⟨hq18, hh18⟩
    refine c.s_cmp_m32i_rip hL18 hB18 hE.code (by omega) hq18 (icf_256 _) (g := (0x7a4ae0 : Addr).add 104) (by decide)
      (fun i hi => c.hws _ (hE.cf (by omega))) ?_
    rintro Z19 u19 hL19 hB19 ⟨hq19, hh19⟩
    refine c.s_mov_rip_i64 hL19 hB19 hE.code (by omega) hq19 (icf_263 _) (g := 0x7a4ac8) (by decide)
      (fun i hi => hE.w _ ⟨_, by simp [icfW], mem_add_of_fits hi (by decide)⟩) ?_
    rintro Z20 u20 hL20 hB20 ⟨hq20, hh20⟩
    refine c.s_mov_rip_r64 hL20 hB20 hE.code (by omega) hq20 (icf_274 _) (g := (0x7a4ae0 : Addr).add 152) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Z21 u21 hL21 hB21 ⟨hq21, hh21⟩
    have hW7 := (hW6.stac8 hE (BitVec.ofNat 64 2)).stcf hE (a := 152) (by omega) (bs := toBytesLE (Z20.cpu.gpr.get (regOf 0)) 8)
      (by simp) (by omega)
    have hU21 : TK g₀ Z21.cpu.gpr := by
      rw [hh21, hh20, hh19, hh18]; exact hT14.set (by omega) _
    refine c.s_jcc_x hL21 hB21 hE.code (by omega) hq21 (icf_281 _) hE.codek (tgt := 0) (by rw [icfk_length]; omega)
      (by decide)
      (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iK0 c hE hsp0 k Y t' _ hKY hAY hW7 hrY (by rw [hgY]; exact hU21))
      fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iT2' c hE hsp0 k Y t' _ hKY hAY hW7 hrY (by rw [hgY]; exact hU21)
  -- `0x61317d`: `ERMS`'s bit of `edx`, `Fast_Rep_String`? (`feature[1]` bit 1)
  have a106 : ∀ (Y : State) (t' : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      IV prof Wl V₀ V → Y.cpu.rip = (0x613113 : Addr).add 106 → TK g₀ Y.cpu.gpr →
      GoG prof L o gev gP gE Y t' := by
    intro Y0 t0 V hK0 hA0 hV hr0 hT0
    refine c.s_wr hK0 hA0 hE.code (by omega) hr0 wr_and_h8i (icf_106 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, v, hg1⟩
    replace hr1 : Y1.cpu.rip = (0x613113 : Addr).add 109 := hr1
    have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT0.set (by omega) _
    refine c.s_jcc hK1 hA1 hE.code (by omega) hr1 (icf_109 _) (tgt := 118) (by decide) (by omega)
      (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => rest Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT1)) fun _ => ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hE.code (by omega) hr2 (icf_111 _) (g := cpuRgn.base.add 100) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact rest Y3 t3 _ hK3 hA3 (hV.or_f1 hE 2 (by decide)) hr3 (by rw [hg3, hg2]; exact hT1)
  refine c.s_mov_r32_rip hK hA hE.code (by omega) hr (icf_88 _) (g := (0x7a4ae0 : Addr).add 12) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT.set (by omega) _
  refine c.s_test_h8i hK1 hA1 hE.code (by omega) hr1 (icf_94 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, -⟩
  rw [← hg2] at hT1
  refine c.s_jcc hK2 hA2 hE.code (by omega) hr2 (icf_97 _) (tgt := 106) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a106 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT1)) fun _ => ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_or_rip_i32 hK3 hA3 hE.code (by omega) hr3 (icf_99 _) (g := cpuRgn.base.add 100) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  exact a106 Y4 t4 _ hK4 hA4 (hV.or_f1 hE 1 (by decide)) hr4 (by rw [hg4, hg3]; exact hT1)

/-- A vendor `get_common_indices` knows nothing more of (`0x613159`): `get_common_indices (cpu_features, NULL, …)`,
`eax = 3`, to `88`. -/
theorem iO (hpc : prof.Consistent) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) :
    AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 70 := by
  intro X t V hK hA hV hr hT
  have hl : icf.length = 357 := icf_length
  refine c.s_xor_rr32 hK hA hE.code (by omega) hr (icf_70 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_xor_rr32 hK1 hA1 hE.code (by omega) hr1 (icf_72 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_xor_rr32 hK2 hA2 hE.code (by omega) hr2 (icf_74 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_xor_rr32 hK3 hA3 hE.code (by omega) hr3 (icf_76 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hT4 : TK g₀ Y4.cpu.gpr := by
    rw [hg4]; refine TK.set ?_ (by omega) _
    rw [hg3]; refine TK.set ?_ (by omega) _
    rw [hg2]; refine TK.set ?_ (by omega) _
    rw [hg1]; exact TK.set hT (by omega) _
  have hdi : Y4.cpu.gpr.rdi = 0 := by rw [hg4]; simp
  refine callG c hE hpc hdf hx87 hK4 hA4 hV hE.code (by omega) hr4 (icf_78 _) (by omega) (by decide)
    (by cases prof.feat.la57 <;> decide) (by rw [hT4.sp, hsp0]) (fun h => absurd hdi h) fun V' hV' Z t' hKZ hAZ hrZ hTZ => ?_
  refine c.s_mov_ri32 hKZ hAZ hE.code (by omega) hrZ (icf_83 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  exact iT1 c hE hsp0 k Y5 t5 _ hK5 hA5 hV' hr5 (by rw [hg5]; exact (hT4.trans hTZ).set (by omega) _)

end K

end FV7z.CpuFeat
