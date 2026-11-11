import FV7z.Start.ToPim
import FV7z.Start.PtrGuard
/-!
# From the launch of `7zzs` to the call of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_pim` takes the run to `0x6133ff` in `__libc_start_main`; `StartB.lsb_ptr` is the stretch from there to
`0x613434`, the call of `__libc_init_first`. Here the two are joined.

- `launch_rdx`: `rdx` is 0 at the first instruction (`execve` clears the registers), so `rtld_fini` is 0 and
  `__cxa_atexit` is not called for it.
- `launch_to_ptr`: for a launch as in `launch_to_pim`, the run from the first instruction goes on as the run from
  `0x613434` does: the pointer guard is in the thread control block (`PtrMem`), and `rdx`, `rsi`, `edi` are
  `__environ`, `argv` and `argc`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (CInv)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.Tls (TlsMem TlsVar TlsMem_out Vst_congr)
open FV7z.StartB (GuardMem PimCode PtrMem ptrGuard lsb_ptr)

/-- `execve` leaves `rdx` 0. -/
theorem launch_rdx {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    l.s₀.cpu.gpr.rdx = 0 := by
  obtain ⟨hdr, c, -, -, hc, -⟩ := launch_full h
  rw [hc]
  rfl

set_option maxHeartbeats 1600000 in
/-- From the launch of `7zzs` to the call of `__libc_init_first` at `0x613434` in `__libc_start_main`. -/
theorem launch_to_ptr {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {t : Nat}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 848 ≤ n)
    (hs : l.args.secure = false) (hq : l.args.threadPending = [] ∧ l.args.signal.pending = [])
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L) (hO : OsvCode L)
    (hP : PimCode L) (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none)
    (hcpy : Tls.CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) (hun : ∀ t, KernelNew (o t .uname).val) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      ((∀ (s₂ Z : State) (t' : Nat) (W V' : Addr → Byte) (g : Gprs) (x1 x2 x3 d r10 r8 r9 : BitVec 64)
          (u : List Byte) (y1 y2 y3 y4 y5 q1 q2 q3 : BitVec 64),
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
        Z.cpu.rip = 0x613434 → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        Z.cpu.gpr.rdx = (ctxOf l.prof l.s₀ l.args c).envp → Z.cpu.gpr.rsi = (ctxOf l.prof l.s₀ l.args c).argv →
        Z.cpu.gpr.rdi = BitVec.setWidth 64 (ctxOf l.prof l.s₀ l.args c).argc →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → MB (ctxOf l.prof l.s₀ l.args c) V' →
        UtsnameOk u → KernelNew u →
        (∀ a : Addr, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data a ∨
            (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
          ¬ Junk3 (ctxOf l.prof l.s₀ l.args c) a → ¬ Pim.PimVar (l.s₀.proc.mm.brk + 2176#64) a →
          W a = PtrMem (VerMem (GuardMem (TlsMem V' l.s₀.proc.mm.brk) (l.s₀.proc.mm.brk + 2176#64)) (osVersion u))
            (l.s₀.proc.mm.brk + 2176#64) a) →
        rdd(TlsMem V' l.s₀.proc.mm.brk, 8029624#64) = 0 →
        GoG l.prof L o (gev ++ [Seg.cetEv g,
          ⟨12, [0, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk, [], []⟩,
          ⟨12, [l.s₀.proc.mm.brk + 4544#64, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk + 4544#64, [], []⟩,
          ⟨158#64, [4098#64, l.s₀.proc.mm.brk + 2176#64, d, r10, r8, r9], 0, [], []⟩,
          ⟨63, [(ctxOf l.prof l.s₀ l.args c).bp - 320#64, y1, y2, y3, y4, y5], 0, [], u⟩,
          ⟨218#64, [l.s₀.proc.mm.brk + 2176#64 + 720#64, q1, l.s₀.proc.mm.brk + 2176#64, q2, 7991568#64, q3],
            BitVec.ofNat 64 l.s₀.thread.tid, [], []⟩,
          ⟨273#64, [l.s₀.proc.mm.brk + 2176#64 + 736#64, 24#64, l.s₀.proc.mm.brk + 2176#64, q2, 7991568#64, q3],
            0, [], []⟩,
          Pim.sgEv 32#64 q3 ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
          Pim.sgEv 33#64 0 ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
          Pim.mskEv ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
          Pim.rlEv ((ctxOf l.prof l.s₀ l.args c).bp + 104#64) 0 0
            (s₂.proc.signal.rlimits ⟨3, by decide⟩).bytes]) gP gE Z t') →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_pim (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom
    hn hs hq noG noA hpc hch ho hL hC hT hO hP hM hmg hcpy hun
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z t₂ W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hcpu hgot hMB hu
    hnew hW hT3
  obtain ⟨h16, hn', hst', hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  obtain ⟨hb0, hb1, hb2⟩ := launch_brk h
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := l.prof) (hdr := ElfHeader.read V2606.zzs.blob.bytes)
    (phs := zzsPhdrs) hst.top.1 hst.align hst.limits
  have hl23 : (toBytesLE c.random 16 ++ platformString).length = 23 := by
    simp [toBytesLE_length, platformString]
  rw [hl23] at h23
  have hrnd := ctxOf_random l.prof l.s₀ l.args c
  generalize hrp : (stackLayout l.args l.prof.linux c).platform - platformString.length - 16 = rp at h12 h23 hrnd
  have h13 : Z.cpu.gpr.r13 = 0 :=
    hRg.2.2.2.trans ((ctxOf_entry l.prof l.s₀ l.args c).2.2.2.2.2.2.1.trans (launch_rdx h))
  have tfb : (l.s₀.proc.mm.brk + 2176#64).toNat = l.s₀.proc.mm.brk.toNat + 2176 := by bv_omega
  have hzr : Z.cpu.gpr.rsp.toNat = (ctxOf l.prof l.s₀ l.args c).bp.toNat + 112 := by
    rw [hRg.1]
    bv_omega
  have hfw : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Foot (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
        [⟨l.s₀.proc.mm.brk, 8192⟩]).data a := fun a h1 h2 => zzs_new (foot_writes (zzsFoot_var h1 h2))
  have hfk : ∀ a : Addr, (stackLayout l.args l.prof.linux c).sp - n ≤ a.toNat → a.toNat < c.stackTop →
      Foot (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
        [⟨l.s₀.proc.mm.brk, 8192⟩]).data a := fun a h1 h2 => zzs_new (foot_writes (zzsFoot_stack htop h1 h2))
  -- the bytes at `0x6133ff`: `M`, and what of them is `V'`
  generalize hMd : VerMem (GuardMem (TlsMem V' l.s₀.proc.mm.brk) (l.s₀.proc.mm.brk + 2176#64)) (osVersion u) = M
    at hW
  have hMV : ∀ a : Addr, ¬ TlsVar a →
      ¬ (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
      ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476) → M a = V' a := fun a h1 h2 h3 => by
    rw [← hMd]
    exact (ver_tls _ _ (by omega) h3 (by omega) (by omega)).trans (TlsMem_out _ hb1 (by omega) h1 h2)
  have hWi : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → ¬ CpuVar a →
      ¬ Pim.PimVar (l.s₀.proc.mm.brk + 2176#64) a → W a = M a := fun a h1 h2 h3 h4 =>
    hW a (.inl (foot_writes (zzsFoot_var h1 h2))) (fun hj => by
      rcases hj with hj | hj
      · omega
      · exact not_junk2 (by omega) h3 hj) h4
  have hWk : ∀ a : Addr, (ctxOf l.prof l.s₀ l.args c).bp.toNat + 112 ≤ a.toNat →
      ¬ ((ctxOf l.prof l.s₀ l.args c).bp.toNat + 156 ≤ a.toNat ∧
        a.toNat < (ctxOf l.prof l.s₀ l.args c).bp.toNat + 232) → a.toNat < c.stackTop → W a = M a :=
    fun a h1 h2 h3 => hW a (.inl (foot_writes (zzsFoot_stack htop (by omega) h3))) (fun hj => by
      unfold Junk3 Junk2 Junk CpuVar at hj
      omega) (by unfold Pim.PimVar; omega)
  have eM1 : rdq(M, 7937184#64) = BitVec.ofNat 64 rp := by
    rw [← hrnd, ← hMB.gl.random]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := tg hi (b := 7937184) (by decide)
    exact hMV _ (by unfold TlsVar; omega) (by omega) (by omega)
  have eW1 : rdq(W, 7937184#64) = BitVec.ofNat 64 rp := by
    rw [← eM1]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := tg hi (b := 7937184) (by decide)
    exact hWi _ (by omega) (by omega) (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)
  have trp : ∀ i < 8, (Addr.add (BitVec.ofNat 64 rp + 8#64) i).toNat = rp + 8 + i := fun i hi => by
    simp only [Addr.add]
    bv_omega
  have hpg' : ptrGuard W = ptrGuard M := by
    unfold ptrGuard
    rw [eW1, eM1]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := trp i hi
    exact hWk _ (by omega) (by omega) (by omega)
  have hbp' := hK.hbp
  have e128 : Z.cpu.gpr.rsp + 16#64 = (ctxOf l.prof l.s₀ l.args c).bp + 128#64 := by
    rw [hRg.1]
    bv_omega
  have e124 : Z.cpu.gpr.rsp + 12#64 = (ctxOf l.prof l.s₀ l.args c).bp + 124#64 := by
    rw [hRg.1]
    bv_omega
  have t128 : ∀ i < 8, (Addr.add ((ctxOf l.prof l.s₀ l.args c).bp + 128#64) i).toNat =
      (ctxOf l.prof l.s₀ l.args c).bp.toNat + 128 + i := fun i hi => by
    simp only [Addr.add]
    bv_omega
  have t124 : ∀ i < 4, (Addr.add ((ctxOf l.prof l.s₀ l.args c).bp + 124#64) i).toNat =
      (ctxOf l.prof l.s₀ l.args c).bp.toNat + 124 + i := fun i hi => by
    simp only [Addr.add]
    bv_omega
  have hstk : ∀ a : Addr, (ctxOf l.prof l.s₀ l.args c).bp.toNat + 112 ≤ a.toNat →
      a.toNat < (ctxOf l.prof l.s₀ l.args c).bp.toNat + 156 → W a = V' a := fun a h1 h2 =>
    (hWk a h1 (by omega) (by omega)).trans (hMV a (by unfold TlsVar; omega) (by omega) (by omega))
  have he : rdq(W, 8013720#64) = (ctxOf l.prof l.s₀ l.args c).envp := by
    rw [← hMB.env]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := tg hi (b := 8013720) (by decide)
    exact (hWi _ (by omega) (by omega) (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)).trans
      (hMV _ (by unfold TlsVar; omega) (by omega) (by omega))
  have ha : rdq(W, Z.cpu.gpr.rsp + 16#64) = (ctxOf l.prof l.s₀ l.args c).argv := by
    rw [e128, ← hMB.fr.argv]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := t128 i hi
    exact hstk _ (by omega) (by omega)
  have hc : rdd(W, Z.cpu.gpr.rsp + 12#64) = (ctxOf l.prof l.s₀ l.args c).argc := by
    rw [e124, ← hMB.fr.argc]
    refine congrArg _ (rd_congr fun i hi => ?_)
    have e := t124 i hi
    exact hstk _ (by omega) (by omega)
  refine lsb_ptr (fb := l.s₀.proc.mm.brk + 2176#64) (rp := BitVec.ofNat 64 rp) c₂ hB₂.fsb hC.lsm hK₂ hA₂
    (hr₂.trans (by decide)) (by omega) (by omega)
    (fun i hi => by have e := tg hi (b := 7937184) (by decide); exact hfw _ (by omega) (by omega))
    (fun i hi => foot_append_iff.2 (.inl ⟨⟨l.s₀.proc.mm.brk, 8192⟩, List.mem_singleton.2 rfl, by
      simp only [Addr.add]; bv_omega, by simp only [Addr.add]; bv_omega⟩))
    eW1 (fun i hi => by have e := trp i hi; exact hfk _ (by omega) (by omega)) h13
    (fun i hi => by have e := tg hi (b := 8013720) (by decide); exact hfw _ (by omega) (by omega))
    (fun i hi => by rw [e128]; have e := t128 i hi; exact hfk _ (by omega) (by omega))
    (fun i hi => by rw [e124]; have e := t124 i hi; exact hfk _ (by omega) (by omega))
    (by omega) (.inr (by omega)) he ha hc ?_
  intro Y t' hKY hAY hrY hgY
  have hYZ : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Y.proc.mm.mem.readByte a = Z.proc.mm.mem.readByte a := by
    intro a h1 h2
    rw [hAY a (hfw a h1 h2), hA₂ a (hfw a h1 h2)]
    unfold PtrMem
    rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (.inl (by bv_omega))]
  subst hMd
  refine hfin s₂ Y t' _ V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hKY hAY
    (hrY.trans (by decide))
    (show _ ∧ _ ∧ _ ∧ _ from ⟨by rw [hgY]; exact hRg.1, by rw [hgY]; exact hRg.2.1, by rw [hgY]; exact hRg.2.2.1,
      by rw [hgY]; exact hRg.2.2.2⟩)
    (by rw [hgY]; rfl) (by rw [hgY]; rfl) (by rw [hgY]; rfl)
    ((CInv.of_cpuOk hcpu).mem fun j hj => ?_)
    (GotOkB.to_mem ((GotOkB.of_mem hgot).congr fun a h1 h2 => hYZ a (by omega) (by omega))) hMB hu hnew
    (fun a ha hj hp => ?_) hT3
  · have e : (cpuRgn.base.add j).toNat = 0x7a4ae0 + j := tg (b := 0x7a4ae0) hj (by decide)
    exact hYZ _ (by omega) (by omega)
  · unfold PtrMem
    rw [hpg']
    exact Vst_congr _ _ _ _ _ (hW a ha hj hp)

end FV7z.Start
