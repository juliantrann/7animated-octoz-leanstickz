import FV7z.Start.ToOsv
import FV7z.Start.OsvCall
/-!
# From the launch of `7zzs` to after the check of the kernel's version (PLAN.md G3, startup)

`launch_to_osv` takes the run to the call of `_dl_discover_osversion` at `0x61363e` in `__libc_start_main`;
`StartB.lsb_osv` is the stretch from there to `0x6133f0`. Here the two are joined.

The run asks the kernel for its release (`uname`). The model's kernel answers with any `struct new_utsname` of the
stream; glibc 2.31 stops (`FATAL: kernel too old`) when the release's number is below 3.2.0. So the theorem has the
assumption `hun`: every answer of the stream to `uname` has `KernelNew` (`Spec/OsVersion.lean`).

- `OsvCode L`: the code of `_dl_discover_osversion` and `__uname` is in `L`.
- `Junk2 K a`: `Junk`, with the frame of `_dl_discover_osversion` (504 bytes below the stack pointer).
- `VerMem V ver`: `V` with `ver` in `_dl_osversion`.
- `launch_to_ver`: for a launch as in `launch_to_osv`, with 792 bytes of stack below the first stack pointer, the
  run from the first instruction goes on as the run from `0x6133f0` does: the bytes outside `Junk2` are
  `VerMem (GuardMem (TlsMem V' brk) (brk + 2176)) (osVersion u)`, `u` the kernel's answer.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (CInv)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.Tls (TlsMem TlsVar TlsMem_out Vst_congr)
open FV7z.StartB (GuardMem lsb_osv OsvMem OsvMem_out frame_out callG)

/-- The code of `_dl_discover_osversion` and of `__uname` is in the run's code. -/
structure OsvCode (L : List (Addr × List Byte)) : Prop where
  osv : CodeIn L Osv.osv_at Osv.osv
  unm : CodeIn L Uname.unm_at Uname.unm

/-- `Junk`, and the frame of `_dl_discover_osversion` with the return address of its call. -/
def Junk2 (K : Ctx) (a : Addr) : Prop := (K.bp.toNat ≤ a.toNat + 392 ∧ a.toNat < K.bp.toNat + 112) ∨ Junk K a

/-- `V` with the version `ver` in `_dl_osversion` (`0x7a8520`). -/
def VerMem (V : Addr → Byte) (ver : BitVec 32) : Addr → Byte := Vst V 8029472#64 (toBytesLE ver 4)

theorem userPtrMax_ge (feat : Features) : 2 ^ 47 - 4096 ≤ userPtrMax feat := by
  unfold userPtrMax
  split <;> decide

/-- From the launch of `7zzs` to `0x6133f0` in `__libc_start_main`, after the check of the kernel's version. -/
theorem launch_to_ver {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {t : Nat}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 792 ≤ n)
    (hs : l.args.secure = false) (hq : l.args.threadPending = [] ∧ l.args.signal.pending = [])
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L) (hO : OsvCode L)
    (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none)
    (hcpy : Tls.CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) (hun : ∀ t, KernelNew (o t .uname).val) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      ((∀ (s₂ Z : State) (t' : Nat) (W V' : Addr → Byte) (g : Gprs) (x1 x2 x3 d r10 r8 r9 : BitVec 64)
          (u : List Byte) (y1 y2 y3 y4 y5 : BitVec 64),
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
        Z.cpu.rip = 0x6133f0 → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → MB (ctxOf l.prof l.s₀ l.args c) V' →
        UtsnameOk u → KernelNew u →
        (∀ a : Addr, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data a ∨
            (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
          ¬ Junk2 (ctxOf l.prof l.s₀ l.args c) a →
          W a = VerMem (GuardMem (TlsMem V' l.s₀.proc.mm.brk) (l.s₀.proc.mm.brk + 2176#64)) (osVersion u) a) →
        rdd(TlsMem V' l.s₀.proc.mm.brk, 8029624#64) = 0 →
        GoG l.prof L o (gev ++ [Seg.cetEv g,
          ⟨12, [0, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk, [], []⟩,
          ⟨12, [l.s₀.proc.mm.brk + 4544#64, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk + 4544#64, [], []⟩,
          ⟨158#64, [4098#64, l.s₀.proc.mm.brk + 2176#64, d, r10, r8, r9], 0, [], []⟩,
          ⟨63, [(ctxOf l.prof l.s₀ l.args c).bp - 320#64, y1, y2, y3, y4, y5], 0, [], u⟩]) gP gE Z t') →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_osv (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom
    (by omega) hs hq noG noA hpc hch ho hL hC hT hM hmg hcpy
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z t₂ W V' g x1 x2 x3 d r10 r8 r9 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hcpu hgot hMB hW hT3
  obtain ⟨h16, hn', hst', hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have htm : c.stackTop ≤ 2 ^ 47 - 4096 := hv.stackTop.2.2
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  obtain ⟨hb0, hb1, hb2⟩ := launch_brk h
  have tfb : (l.s₀.proc.mm.brk + 2176#64).toNat = l.s₀.proc.mm.brk.toNat + 2176 := by bv_omega
  have hzr : Z.cpu.gpr.rsp.toNat = (ctxOf l.prof l.s₀ l.args c).bp.toNat + 112 := by
    rw [hRg.1]
    bv_omega
  have hfw : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Foot (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
        [⟨l.s₀.proc.mm.brk, 8192⟩]).data a := fun a h1 h2 => zzs_new (foot_writes (zzsFoot_var h1 h2))
  -- `_dl_osversion` is 0 at the call
  have hW0 : ∀ a : Addr, 8029472 ≤ a.toNat → a.toNat < 8029476 → W a = 0 := by
    intro a h1 h2
    rw [hW a (.inl (foot_writes (zzsFoot_var (by omega) (by omega)))) fun hj => by
      rcases hj with hj | hj | hj
      · omega
      · omega
      · unfold CpuVar at hj
        omega]
    unfold GuardMem
    rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (.inl (by bv_omega)),
      Vst_out _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (.inl (by bv_omega)),
      TlsMem_out _ hb1 (by omega) (by unfold TlsVar; omega) (by omega),
      hMB.same _ (by simp only [InStk]; omega) (not_dg (lo := 8029472) (hi := 8029476) (by decide) h1 h2)]
    exact hB0 _ (by omega) (by omega)
  have h0 : rdd(W, 8029472#64) = 0 := by
    have : List.map W (byteAddrs 8029472#64 4) = [0, 0, 0, 0] := by
      apply List.ext_getElem
      · simp [byteAddrs]
      · intro i h1 h2
        simp only [List.length_map, byteAddrs, List.length_range] at h1
        have e := tg h1 (b := 8029472) (by decide)
        simp only [List.getElem_map, byteAddrs, List.getElem_range]
        rw [hW0 _ (by omega) (by omega)]
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> rfl
    rw [this]
    rfl
  have t504 : (Z.cpu.gpr.rsp - 504#64).toNat = Z.cpu.gpr.rsp.toNat - 504 := by bv_omega
  refine lsb_osv (fb := l.s₀.proc.mm.brk + 2176#64) c₂ hB₂.fsb hC.lsm hO.osv hO.unm hK₂ hA₂
    (hr₂.trans (by decide)) (by omega) (Nat.le_trans (by omega) (userPtrMax_ge _)) (fun i hi => ?_)
    (fun i hi => ?_) (.inr (by omega)) h0 hun ?_
  · have e : (Addr.add (Z.cpu.gpr.rsp - 504#64) i).toNat = Z.cpu.gpr.rsp.toNat - 504 + i := by
      simp only [Addr.add]
      bv_omega
    exact foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega)))
  · have e := tg hi (b := 8029472) (by decide)
    exact foot_append_iff.2 (.inr (zzsFoot_var (by omega) (by omega)))
  intro u Y t' hu hnew hKY hAY hrY hsv
  have hYZ : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476) →
      Y.proc.mm.mem.readByte a = Z.proc.mm.mem.readByte a := by
    intro a h1 h2 h3
    rw [hAY a (hfw a h1 h2), hA₂ a (hfw a h1 h2)]
    exact OsvMem_out (by omega) hu.1 (fun hh => by omega) h3
  have e320 : (callG Z.cpu.gpr).rsp - 424#64 = (ctxOf l.prof l.s₀ l.args c).bp - 320#64 := by
    show Z.cpu.gpr.rsp - 8 - 424#64 = _
    rw [hRg.1]
    bv_omega
  have eev : Osv.osvEv (callG Z.cpu.gpr) u = ⟨63, [(ctxOf l.prof l.s₀ l.args c).bp - 320#64, Z.cpu.gpr.rsi,
      Z.cpu.gpr.rdx, Z.cpu.gpr.r10, Z.cpu.gpr.r8, Z.cpu.gpr.r9], 0, [], u⟩ := by
    rw [← e320]
    rfl
  rw [eev, List.append_assoc]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsv
  refine hfin s₂ Y t' _ V' g x1 x2 x3 d r10 r8 r9 u _ _ _ _ _ hax hdi c₂ hB₂ hKY hAY (hrY.trans (by decide))
    ⟨s1.trans hRg.1, s3.trans hRg.2.1, s4.trans hRg.2.2.1, s5.trans hRg.2.2.2⟩
    ((CInv.of_cpuOk hcpu).mem fun j hj => ?_)
    (GotOkB.to_mem ((GotOkB.of_mem hgot).congr fun a h1 h2 => hYZ a (by omega) (by omega) (by omega))) hMB hu hnew
    (fun a ha hj => ?_) hT3
  · have e : (cpuRgn.base.add j).toNat = 0x7a4ae0 + j := tg (b := 0x7a4ae0) hj (by decide)
    exact hYZ _ (by omega) (by omega) (by omega)
  · unfold OsvMem VerMem
    refine Vst_congr _ _ _ _ _ ((frame_out (by omega) hu.1 fun hh => hj (.inl (by omega))).trans
      (hW a ha fun hk => hj (.inr hk)))

end FV7z.Start
