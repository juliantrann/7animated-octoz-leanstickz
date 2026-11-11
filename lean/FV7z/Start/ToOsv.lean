import FV7z.Start.Guard
/-!
# From the launch of `7zzs` to the call of `_dl_discover_osversion` (PLAN.md G3, startup)

`launch_to_tls` takes the run to `0x6133c0` in `__libc_start_main`; `StartB.lsb_guard` is the stretch from there to
the call at `0x61363e`. Here the two are joined.

- `auxv_rnd`, `auxv_idx25`, `ctxOf_random`: the vector has an `AT_RANDOM`, with the address of the 16 bytes `execve`
  puts above the words of the new stack; so `_dl_random` after `_dl_aux_init` is that address.
- `launch_to_osv`: for a launch as in `launch_to_tls`, the run from the first instruction goes on as the run from
  `0x61363e` does: the bytes outside `Junk` are `GuardMem (TlsMem V' brk) (brk + 2176)`, the thread control block
  with `feature_1` (0: `_dl_x86_feature_1` is as in the file) and the stack guard. What the launch gives of the
  context is part of the statement (`Ctx.Ok`, `Img`, `Bss`), for what comes after.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (cpuW icfW irelW TKi CInv)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.Tls (TlsMem TlsVar TlsMem_out TlsMem_congr Vst_congr)
open FV7z.StartB (GuardMem lsb_guard)

/-! ## `AT_RANDOM` -/

theorem auxv_rnd (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ (∀ e ∈ pre, e.1 ≠ 0 ∧ e.1 < 64) ∧
      (∀ e ∈ pre, e.1 = 25 → e.2 = l.platform - platformString.length - 16) ∧
      (25, l.platform - platformString.length - 16) ∈ pre := by
  refine ⟨(if prof.linux.vdso then [(33, c.vdsoText)] else []) ++
    [(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_, ?_, ?_⟩ <;>
    cases hv : prof.linux.vdso <;> simp [auxv, hv]

/-- The vector by index: there is an `AT_RANDOM`, and each has the address of the 16 bytes. -/
theorem auxv_idx25 (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice) (l : StackLayout) :
    (∃ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 25) ∧
    (∀ n < auxCount prof.linux - 1, BitVec.ofNat 64 ((auxv prof hdr pa a c l).getD n (0, 0)).1 = 25 →
      ((auxv prof hdr pa a c l).getD n (0, 0)).2 = l.platform - platformString.length - 16) := by
  obtain ⟨pre, hA, hnz, h5, m5⟩ := auxv_rnd prof hdr pa a c l
  have hlen : pre.length = auxCount prof.linux - 1 := by
    have := auxv_length prof hdr pa a c l
    rw [hA] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  rw [hA, ← hlen]
  have hin : ∀ n, n < pre.length → (pre ++ [(0, 0)]).getD n (0, 0) ∈ pre := by
    intro n hn
    rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn, e⟩ := List.mem_iff_getElem.1 m5
    exact ⟨n, hn, by
      rw [getD_in _ _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, e]; rfl⟩
  · intro n hn h
    refine h5 _ (hin n hn) ?_
    have h' : BitVec.ofNat 64 ((pre ++ [(0, 0)]).getD n (0, 0)).1 = BitVec.ofNat 64 25 := h
    have := congrArg BitVec.toNat h'
    have b := (hnz _ (hin n hn)).2
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem step_random (v : Vars) (e : BitVec 64 × BitVec 64) :
    (AuxInit.step v e).random = if e.1 = 25 then e.2 else v.random := by
  by_cases h : e.1 = 25
  · simp [AuxInit.step, h]
  · simp only [AuxInit.step, apply_ite Vars.random, h, ↓reduceIte]
    repeat' split
    all_goals rfl

/-- `_dl_random` after a vector with an `AT_RANDOM`, each with the value `x`. -/
theorem vsOf_random {ty val : Nat → BitVec 64} {w : Vars} {x : BitVec 64} :
    ∀ M, (∃ n < M, ty n = 25) → (∀ n < M, ty n = 25 → val n = x) → (vsOf ty val w M).random = x
  | 0, ⟨_, hn, _⟩, _ => absurd hn (Nat.not_lt_zero _)
  | M + 1, ⟨n, hn, h3⟩, hall => by
    show (AuxInit.step (vsOf ty val w M) (ty M, val M)).random = x
    rw [step_random]
    split
    · next hM => exact hall M (Nat.lt_succ_self _) hM
    · next hM =>
      have hlt : n < M := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
        · exact h
        · exact absurd (h ▸ h3) hM
      exact vsOf_random M ⟨n, hlt, h3⟩ fun k hk => hall k (Nat.lt_succ_of_lt hk)

/-- After `_dl_aux_init`, in a run of `7zzs`: `_dl_random` is the address of `AT_RANDOM`'s 16 bytes. -/
theorem ctxOf_random (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    ((ctxOf prof s a c).vs (ctxOf prof s a c).M).random =
      BitVec.ofNat 64 ((stackLayout a prof.linux c).platform - platformString.length - 16) := by
  obtain ⟨e5, h5⟩ := auxv_idx25 prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  refine vsOf_random _ e5 fun n hn h => ?_
  show BitVec.ofNat 64 _ = _
  rw [h5 n hn h]

/-! ## To the call -/

/-- From the launch of `7zzs` to the call of `_dl_discover_osversion` at `0x61363e` in `__libc_start_main`. -/
theorem launch_to_osv {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {t : Nat}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 656 ≤ n)
    (hs : l.args.secure = false) (hq : l.args.threadPending = [] ∧ l.args.signal.pending = [])
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L)
    (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none)
    (hcpy : Tls.CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      ((∀ (s₂ Z : State) (t' : Nat) (W V' : Addr → Byte) (g : Gprs) (x1 x2 x3 d r10 r8 r9 : BitVec 64),
        g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
        Seg l.prof
          (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L) [⟨l.s₀.proc.mm.brk, 8192⟩])
          ([⟨l.s₀.proc.mm.brk, 8192⟩] ++ (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).writes)
          L s₂ o →
        Base s₂ (pageUp (l.s₀.proc.mm.brk.toNat + 2 ^ 41) / 4096) (l.s₀.proc.mm.brk + 4544#64)
          (l.s₀.proc.mm.brk + 2176#64) ⟨l.s₀.thread.tid⟩ →
        KeptW ([⟨l.s₀.proc.mm.brk, 8192⟩] ++
          (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).writes) s₂ Z →
        Agree
          (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L) [⟨l.s₀.proc.mm.brk, 8192⟩])
          Z.proc.mm.mem W →
        Z.cpu.rip = 0x61363e → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → MB (ctxOf l.prof l.s₀ l.args c) V' →
        (∀ a : Addr, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data a ∨
            (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
          ¬ Junk (ctxOf l.prof l.s₀ l.args c) a →
          W a = GuardMem (TlsMem V' l.s₀.proc.mm.brk) (l.s₀.proc.mm.brk + 2176#64) a) →
        rdd(TlsMem V' l.s₀.proc.mm.brk, 8029624#64) = 0 →
        GoG l.prof L o (gev ++ [Seg.cetEv g,
          ⟨12, [0, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk, [], []⟩,
          ⟨12, [l.s₀.proc.mm.brk + 4544#64, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk + 4544#64, [], []⟩,
          ⟨158#64, [4098#64, l.s₀.proc.mm.brk + 2176#64, d, r10, r8, r9], 0, [], []⟩]) gP gE Z t') →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hto⟩ := launch_to_tls (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom hn hs hq noG noA hpc
    hch ho hL hC hT hM hmg hcpy
  obtain ⟨h16, hn', hst', hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  obtain ⟨kbp, kmain, kargc, kargv, kinit, kfini, krtld, kV0, kq, kz, kln⟩ := ctxOf_entry l.prof l.s₀ l.args c
  have himg : l.s₀.cpu.gpr.rsp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ l.s₀.cpu.gpr.rsp.toNat := .inr (by omega)
  have hI0 : Img (ctxOf l.prof l.s₀ l.args c).V0 := kV0 ▸ Entry.V1_img (launch_img h) (by omega) himg
  have hB0 : Bss (ctxOf l.prof l.s₀ l.args c).V0 := kV0 ▸ Entry.V1_bss (launch_bss h) (by omega) himg
  have hK : (ctxOf l.prof l.s₀ l.args c).Ok := Ctx.ok (hst.lch (by omega) hs noG noA) hI0 kq kz kln
  clear kbp kmain kargc kargv kinit kfini krtld kV0 kq kz kln himg
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z t₂ W V' g x1 x2 x3 d r10 r8 r9 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hcpu hgot hMB hW
  obtain ⟨hb0, hb1, hb2⟩ := launch_brk h
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := l.prof) (hdr := ElfHeader.read V2606.zzs.blob.bytes)
    (phs := zzsPhdrs) hst.top.1 hst.align hst.limits
  have hl23 : (toBytesLE c.random 16 ++ platformString).length = 23 := by
    simp [toBytesLE_length, platformString]
  rw [hl23] at h23
  have hrnd := ctxOf_random l.prof l.s₀ l.args c
  generalize hrp : (stackLayout l.args l.prof.linux c).platform - platformString.length - 16 = rp at h12 h23 hrnd
  have tfb : (l.s₀.proc.mm.brk + 2176#64).toNat = l.s₀.proc.mm.brk.toNat + 2176 := by bv_omega
  -- the bytes at `0x6133c0`
  have hWs : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → ¬ CpuVar a →
      W a = TlsMem V' l.s₀.proc.mm.brk a := fun a h1 h2 hc =>
    hW a (.inl (foot_writes (zzsFoot_var h1 h2))) fun hj => by
      rcases hj with hj | hj | hj
      · omega
      · omega
      · exact hc hj
  have hWr : ∀ i < 16, W (Addr.add (BitVec.ofNat 64 rp) i) =
      TlsMem V' l.s₀.proc.mm.brk (Addr.add (BitVec.ofNat 64 rp) i) := by
    intro i hi
    have e := tg hi (b := rp) (by omega)
    refine hW _ (.inl (foot_writes (zzsFoot_stack htop (by omega) (by omega)))) fun hj => ?_
    rcases hj with hj | hj | hj
    · omega
    · omega
    · unfold CpuVar at hj
      omega
  have hTo : ∀ a : Addr, ¬ TlsVar a → ¬ (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
      TlsMem V' l.s₀.proc.mm.brk a = V' a := fun a h1 h2 => TlsMem_out _ hb1 (by omega) h1 h2
  have hT1 : rdq(TlsMem V' l.s₀.proc.mm.brk, 7937184#64) = BitVec.ofNat 64 rp := by
    rw [← hrnd, ← hMB.gl.random]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := tg hi (b := 7937184) (by decide)
    exact hTo _ (by unfold TlsVar; omega) (by omega)
  have hT2 : rdd(TlsMem V' l.s₀.proc.mm.brk, 7944640#64) = 0 := by
    rw [← hMB.mlibs]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := tg hi (b := 7944640) (by decide)
    exact hTo _ (by unfold TlsVar; omega) (by omega)
  have hT3 : rdd(TlsMem V' l.s₀.proc.mm.brk, 8029624#64) = 0 := by
    have : List.map (TlsMem V' l.s₀.proc.mm.brk) (byteAddrs 8029624#64 4) = [0, 0, 0, 0] := by
      apply List.ext_getElem
      · simp [byteAddrs]
      · intro i h1 h2
        simp only [List.length_map, byteAddrs, List.length_range] at h1
        have e := tg h1 (b := 8029624) (by decide)
        simp only [List.getElem_map, byteAddrs, List.getElem_range]
        rw [hTo _ (by unfold TlsVar; omega) (by omega),
          hMB.same _ (by simp only [InStk]; omega) (not_dg (lo := 8029624) (hi := 8029628) (by decide)
            (by omega) (by omega)), hB0 _ (by omega) (by omega)]
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> rfl
    rw [this]
    rfl
  have hW1 : rdq(W, 7937184#64) = rdq(TlsMem V' l.s₀.proc.mm.brk, 7937184#64) :=
    congrArg _ (rd_congr fun i hi => by
      have e := tg hi (b := 7937184) (by decide)
      exact hWs _ (by omega) (by omega) (by unfold CpuVar; omega))
  have hW2 : rdd(W, 7944640#64) = rdd(TlsMem V' l.s₀.proc.mm.brk, 7944640#64) :=
    congrArg _ (rd_congr fun i hi => by
      have e := tg hi (b := 7944640) (by decide)
      exact hWs _ (by omega) (by omega) (by unfold CpuVar; omega))
  have hW3 : rdd(W, 8029624#64) = rdd(TlsMem V' l.s₀.proc.mm.brk, 8029624#64) :=
    congrArg _ (rd_congr fun i hi => by
      have e := tg hi (b := 8029624) (by decide)
      exact hWs _ (by omega) (by omega) (by unfold CpuVar; omega))
  have hW4 : StartB.guard W = StartB.guard (TlsMem V' l.s₀.proc.mm.brk) := by
    unfold StartB.guard
    rw [hW1, hT1]
    exact congrArg (· &&& _) (congrArg _ (rd_congr fun i hi => hWr i (by omega)))
  have hfw : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Foot (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
        [⟨l.s₀.proc.mm.brk, 8192⟩]).data a := fun a h1 h2 => zzs_new (foot_writes (zzsFoot_var h1 h2))
  refine lsb_guard (fb := l.s₀.proc.mm.brk + 2176#64) (rp := BitVec.ofNat 64 rp) c₂ hB₂.fsb hC.lsm hK₂ hA₂
    (hr₂.trans (by decide)) (by omega) (by omega)
    (fun i hi => by have e := tg hi (b := 8029624) (by decide); exact hfw _ (by omega) (by omega))
    (fun i hi => by have e := tg hi (b := 7937184) (by decide); exact hfw _ (by omega) (by omega))
    (fun i hi => by have e := tg hi (b := 7944640) (by decide); exact hfw _ (by omega) (by omega))
    (fun i hi => foot_append_iff.2 (.inl ⟨⟨l.s₀.proc.mm.brk, 8192⟩, List.mem_singleton.2 rfl, by
      simp only [Addr.add]; bv_omega, by simp only [Addr.add]; bv_omega⟩))
    (hW1.trans hT1)
    (fun i hi => by
      have e := tg (show i < 16 by omega) (b := rp) (by omega)
      exact zzs_new (foot_writes (zzsFoot_stack htop (by omega) (by omega))))
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    (.inr (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)) (hW2.trans hT2) ?_
  intro Y t' hKY hAY hrY hgY
  have hYZ : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Y.proc.mm.mem.readByte a = Z.proc.mm.mem.readByte a := by
    intro a h1 h2
    rw [hAY a (hfw a h1 h2), hA₂ a (hfw a h1 h2)]
    unfold GuardMem
    rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (.inl (by bv_omega)),
      Vst_out _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (.inl (by bv_omega))]
  refine hfin s₂ Y t' _ V' g x1 x2 x3 d r10 r8 r9 hax hdi c₂ hB₂ hKY hAY (hrY.trans (by decide))
    (show _ ∧ _ ∧ _ ∧ _ from ⟨by rw [hgY]; exact hRg.1, by rw [hgY]; exact hRg.2.1, by rw [hgY]; exact hRg.2.2.1,
      by rw [hgY]; exact hRg.2.2.2⟩)
    ((CInv.of_cpuOk hcpu).mem fun j hj => ?_)
    (GotOkB.to_mem ((GotOkB.of_mem hgot).congr fun a h1 h2 => hYZ a (by omega) (by omega))) hMB
    (fun a ha hj => ?_) hT3
  · have e : (cpuRgn.base.add j).toNat = 0x7a4ae0 + j := tg (b := 0x7a4ae0) hj (by decide)
    exact hYZ _ (by omega) (by omega)
  · unfold GuardMem
    rw [hW3, hW4]
    exact Vst_congr _ _ _ _ _ (Vst_congr _ _ _ _ _ (hW a ha hj))

end FV7z.Start
