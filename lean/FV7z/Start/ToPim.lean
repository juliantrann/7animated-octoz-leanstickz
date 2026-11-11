import FV7z.Start.ToVer
import FV7z.Start.PimCall
/-!
# From the launch of `7zzs` to after `__pthread_initialize_minimal` (PLAN.md G3, startup)

`launch_to_ver` takes the run to `0x6133f0` in `__libc_start_main`; `StartB.lsb_pim` is the stretch from there to
`0x6133ff`, the call of `__pthread_initialize_minimal` (`0x6000b0`). Here the two are joined.

- `PimCode L` (`Start/PimCall.lean`): the code of the function and of its callees is in `L`.
- `slot_pin`: the weak reference at `0x791fb0` is `0x6000b0` in the file.
- `TlsMem_self`, `TlsMem_zero`: the thread control block's pointer to itself, and the zeros after its first three
  words, in the bytes `__libc_setup_tls` leaves.
- `ver_tls`, `ver_img`: the bytes at `0x6133f0` that are `TlsMem`'s, and those that are the file's.
- `Junk3 K a`: `Junk2`, with the frame of the function and of its callees (560 bytes below the stack pointer).
- `launch_to_pim`: for a launch as in `launch_to_ver`, with 848 bytes of stack below the first stack pointer, the
  run from the first instruction goes on as the run from `0x6133ff` does: six more system calls
  (`set_tid_address`, `set_robust_list`, `rt_sigaction` twice, `rt_sigprocmask`, `prlimit64`), and the bytes
  outside `Junk3` and `Pim.PimVar` are as at `0x6133f0`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)

namespace FV7z.Tls

/-- The thread control block's pointer to itself (`header.self`). -/
theorem TlsMem_self (V : Addr → Byte) {b : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) :
    rdq(TlsMem V b, b + 2176#64 + 16#64) = b + 2176#64 := by
  unfold TlsMem WD WC
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst,
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega)]
  · exact ofBytesLE_toBytesLE (n := 8) rfl _
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- After the thread control block's first three words the two new pages are 0. -/
theorem TlsMem_zero (V : Addr → Byte) {b a : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (h1 : b.toNat + 2200 ≤ a.toNat) (h2 : a.toNat < b.toNat + 8192) : TlsMem V b a = 0 := by
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  unfold TlsMem WD WC T4 T3 T2
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
    Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vz_in (by omega) h2]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega

end FV7z.Tls

namespace FV7z.Start
open FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (CInv)
open FV7z.Tun (gz)
open FV7z.Tls (TlsMem TlsVar TlsMem_out TlsMem_self TlsMem_zero rd_ext)
open FV7z.StartB (GuardMem lsb_pim PimCode callG)

/-- The weak reference to `__pthread_initialize_minimal` in the file: `0x6000b0`. -/
theorem slot_pin : Exe.bytesAt V2606.zzs.blob 0x791fb0 8 = some [0xb0, 0x00, 0x60, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Bytes that are 0. -/
theorem rd_zero {V : Addr → Byte} {x : Addr} {n : Nat} (h : ∀ i < n, V (x.add i) = 0) :
    List.map V (byteAddrs x n) = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [byteAddrs]
  · intro i h1 h2
    simp only [List.length_map, byteAddrs, List.length_range] at h1
    simp only [List.getElem_map, byteAddrs, List.getElem_range, List.getElem_replicate]
    exact h i h1

/-- A byte at `0x6133f0` that the stores of the stack guard, of `feature_1` and of `_dl_osversion` leave. -/
theorem ver_tls (V : Addr → Byte) {b a : Addr} (ver : BitVec 32) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (h1 : ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476))
    (h2 : ¬ (b.toNat + 2216 ≤ a.toNat ∧ a.toNat < b.toNat + 2224))
    (h3 : ¬ (b.toNat + 2248 ≤ a.toNat ∧ a.toNat < b.toNat + 2252)) :
    VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver a = TlsMem V b a := by
  unfold VerMem GuardMem
  rw [Vst_out, Vst_out, Vst_out]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- A byte of the image at `0x6133f0`, not stored to since the first instruction. -/
theorem ver_img {K : Ctx} {V : Addr → Byte} {b a : Addr} (ver : BitVec 32) (hK : K.Ok)
    (hS : Same K (d3 ++ globals) V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (h1 : 0x400000 ≤ a.toNat) (h2 : a.toNat < 0x7a9000) (hT : ¬ TlsVar a)
    (hv : ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476)) (hd : ¬ Foot (d3 ++ globals) a) :
    VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver a = K.V0 a := by
  have := hK.himg
  rw [ver_tls V ver hb' hv (by omega) (by omega), TlsMem_out _ hb hb' hT (by omega)]
  exact hS _ (by simp only [InStk]; omega) hd

/-- `Junk2`, and the frame of `__pthread_initialize_minimal` with the return address of its call. -/
def Junk3 (K : Ctx) (a : Addr) : Prop := (K.bp.toNat ≤ a.toNat + 448 ∧ a.toNat < K.bp.toNat + 112) ∨ Junk2 K a

/-- A byte below the stack is not in `Junk2` but for `CpuVar`. -/
theorem not_junk2 {K : Ctx} {a : Addr} (h2 : a.toNat + 448 < K.bp.toNat) (hc : ¬ CpuVar a) : ¬ Junk2 K a := by
  unfold Junk2 Junk
  rintro (h | h | h | h)
  · omega
  · omega
  · omega
  · exact hc h

set_option maxHeartbeats 1600000 in
/-- From the launch of `7zzs` to `0x6133ff` in `__libc_start_main`, after `__pthread_initialize_minimal`. -/
theorem launch_to_pim {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
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
        Z.cpu.rip = 0x6133ff → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → MB (ctxOf l.prof l.s₀ l.args c) V' →
        UtsnameOk u → KernelNew u →
        (∀ a : Addr, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data a ∨
            (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
          ¬ Junk3 (ctxOf l.prof l.s₀ l.args c) a → ¬ Pim.PimVar (l.s₀.proc.mm.brk + 2176#64) a →
          W a = VerMem (GuardMem (TlsMem V' l.s₀.proc.mm.brk) (l.s₀.proc.mm.brk + 2176#64)) (osVersion u) a) →
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
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_ver (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom
    (by omega) hs hq noG noA hpc hch ho hL hC hT hO hM hmg hcpy hun
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z t₂ W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hcpu hgot hMB hu hnew
    hW hT3
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
  have e8 : (Z.cpu.gpr.rsp - 8).toNat = Z.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have e560 : (Z.cpu.gpr.rsp - 8 - 552#64).toNat = Z.cpu.gpr.rsp.toNat - 560 := by bv_omega
  have hfw : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Foot (withNew (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
        [⟨l.s₀.proc.mm.brk, 8192⟩]).data a := fun a h1 h2 => zzs_new (foot_writes (zzsFoot_var h1 h2))
  -- the bytes of the image at `0x6133f0`
  have him : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → ¬ TlsVar a →
      ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476) → ¬ Foot (d3 ++ globals) a → ¬ CpuVar a →
      W a = (ctxOf l.prof l.s₀ l.args c).V0 a := fun a h1 h2 h3 h4 h5 h6 =>
    (hW a (.inl (foot_writes (zzsFoot_var h1 h2))) (not_junk2 (by omega) h6)).trans
      (ver_img _ hK hMB.same hb1 (by omega) (by omega) h2 h3 h4 h5)
  -- the bytes of the two new pages
  have hnw : ∀ a : Addr, l.s₀.proc.mm.brk.toNat + 2192 ≤ a.toNat → a.toNat < l.s₀.proc.mm.brk.toNat + 2208 →
      W a = TlsMem V' l.s₀.proc.mm.brk a := fun a h1 h2 =>
    (hW a (.inr ⟨by omega, by omega⟩) (not_junk2 (by omega) (by unfold CpuVar; omega))).trans
      (ver_tls _ _ (by omega) (by omega) (by omega) (by omega))
  have hslot : rdq(W, 7937968#64) ≠ 0 := by
    have e : List.map W (byteAddrs 7937968#64 8) = [0xb0, 0x00, 0x60, 0, 0, 0, 0, 0] := by
      rw [rd_ext 7937968#64 8 fun i hi => by
        have e := tg hi (b := 0x791fb0) (by decide)
        exact him _ (by omega) (by omega) (by unfold TlsVar; omega) (by omega)
          (not_dg (lo := 0x791fb0) (hi := 0x791fb8) (by decide) (by omega) (by omega)) (by unfold CpuVar; omega)]
      exact hI0.map slot_pin rfl (by decide) (by decide) (off := 0) (m := 8) (by decide)
    rw [e]
    decide
  have hz : ∀ x n : Nat, 0x7945d0 ≤ x → x + n ≤ 0x7a4000 →
      (∀ y : Addr, x ≤ y.toNat → y.toNat < x + n → ¬ TlsVar y) →
      (∀ r ∈ d3 ++ globals, r.base.toNat + r.len ≤ x ∨ x + n ≤ r.base.toNat) →
      List.map W (byteAddrs (BitVec.ofNat 64 x) n) = List.replicate n 0 := by
    intro x n h1 h2 h3 h4
    refine rd_zero fun i hi => ?_
    have e := tg hi (b := x) (by omega)
    rw [him _ (by omega) (by omega) (h3 _ (by omega) (by omega)) (by omega)
      (not_dg h4 (by omega) (by omega)) (by unfold CpuVar; omega)]
    exact hB0 _ (by omega) (by omega)
  have hlk : rdd(W, 8008032#64) = 0 := by
    rw [hz 8008032 4 (by decide) (by decide) (fun y h1 h2 => by unfold TlsVar; omega) (by decide)]
    rfl
  have hfl : rdd(W, 8011552#64) = 0 := by
    rw [hz 8011552 4 (by decide) (by decide) (fun y h1 h2 => by unfold TlsVar; omega) (by decide)]
    rfl
  have hfg : rdb(W, 8011556#64) = 0 := by
    rw [hz 8011556 1 (by decide) (by decide) (fun y h1 h2 => by unfold TlsVar; omega) (by decide)]
    rfl
  -- the tunable of the stack's size in the file
  have htn : ∀ off m : Nat, 1296 ≤ off → off + m ≤ 1456 →
      List.map W (byteAddrs (BitVec.ofNat 64 (0x791660 + off)) m) = (tl.drop off).take m := by
    intro off m h1 h2
    rw [rd_ext (BitVec.ofNat 64 (0x791660 + off)) m fun i hi => by
      have e := tg hi (b := 0x791660 + off) (by omega)
      exact him _ (by omega) (by omega) (by unfold TlsVar; omega) (by omega)
        (not_dg (lo := 0x791b70) (hi := 0x791c10) (by decide) (by omega) (by omega)) (by unfold CpuVar; omega)]
    exact hI0.map tl_pin tl_length (by decide) (by decide) (by omega)
  have ht0 : rdd(W, 7936880#64) = 0 :=
    (congrArg (ofBytesLE 32) (htn 1296 4 (by decide) (by decide))).trans (by decide +kernel)
  have htz : rdb(W, 7936912#64) = 0 :=
    (congrArg (ofBytesLE 8) (htn 1328 1 (by decide) (by decide))).trans (by decide +kernel)
  -- the thread control block
  have hself : rdq(W, l.s₀.proc.mm.brk + 2176#64 + 16#64) = l.s₀.proc.mm.brk + 2176#64 := by
    rw [rd_ext (l.s₀.proc.mm.brk + 2176#64 + 16#64) 8 fun i hi => by
      have e : (Addr.add (l.s₀.proc.mm.brk + 2176#64 + 16#64) i).toNat = l.s₀.proc.mm.brk.toNat + 2192 + i := by
        simp only [Addr.add]
        bv_omega
      exact hnw _ (by omega) (by omega)]
    exact TlsMem_self V' hb1 (by omega)
  have hmt : rdd(W, l.s₀.proc.mm.brk + 2176#64 + 24#64) = 0 := by
    rw [rd_zero fun i hi => by
      have e : (Addr.add (l.s₀.proc.mm.brk + 2176#64 + 24#64) i).toNat = l.s₀.proc.mm.brk.toNat + 2200 + i := by
        simp only [Addr.add]
        bv_omega
      rw [hnw _ (by omega) (by omega)]
      exact TlsMem_zero V' hb1 (by omega) (by omega) (by omega)]
    rfl
  refine lsb_pim (fb := l.s₀.proc.mm.brk + 2176#64) c₂ hB₂ hC.lsm hP hK₂ hA₂ (hr₂.trans (by decide))
    (fun i hi => hfw _ (by rw [tg hi (b := 0x791fb0) (by decide)]; omega)
      (by rw [tg hi (b := 0x791fb0) (by decide)]; omega))
    hslot ⟨by omega, fun i hi => ?_, fun i hi => ?_, fun a h1 h2 => foot_append_iff.2 (.inr (zzsFoot_var h1 h2)),
      c₂.hws, by omega, by omega⟩
    (fun i hi => ?_) (by omega) (Nat.le_trans (by omega) (userPtrMax_ge _))
    (fun i hi => zzs_new (foot_reads (zzsFoot_ro (by rw [tg hi (b := 7273168) (by decide)]; omega)
      (by rw [tg hi (b := 7273168) (by decide)]; omega))))
    hself hlk hmt hfl hfg ht0 htz ?_
  · have e : (Addr.add (Z.cpu.gpr.rsp - 8 - 552#64) i).toNat = Z.cpu.gpr.rsp.toNat - 560 + i := by
      simp only [Addr.add]
      bv_omega
    exact foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega)))
  · have e : (Addr.add (l.s₀.proc.mm.brk + 2176#64) i).toNat = l.s₀.proc.mm.brk.toNat + 2176 + i := by
      simp only [Addr.add]
      bv_omega
    refine foot_append_iff.2 (.inl ⟨⟨l.s₀.proc.mm.brk, 8192⟩, List.mem_cons_self, ?_⟩)
    show l.s₀.proc.mm.brk.toNat ≤ _ ∧ _ < l.s₀.proc.mm.brk.toNat + 8192
    omega
  · have e : (Addr.add (Z.cpu.gpr.rsp - 8) i).toNat = Z.cpu.gpr.rsp.toNat - 8 + i := by
      simp only [Addr.add]
      bv_omega
    exact foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega)))
  intro s₁ Y t' V'' c₁ hB₁ hKY hAY hV hrY hsv
  have hYZ : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      ¬ Pim.PimVar (l.s₀.proc.mm.brk + 2176#64) a → Y.proc.mm.mem.readByte a = Z.proc.mm.mem.readByte a := by
    intro a h1 h2 h3
    rw [hAY a (hfw a h1 h2), hA₂ a (hfw a h1 h2)]
    exact hV a (by omega) h3
  have e104 : Z.cpu.gpr.rsp - 8 = (ctxOf l.prof l.s₀ l.args c).bp + 104#64 := by
    rw [hRg.1]
    bv_omega
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsv
  rw [e104]
  simp only [List.append_assoc]
  refine hfin s₁ Y t' V'' V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 Z.cpu.gpr.rsi Z.cpu.gpr.r10 Z.cpu.gpr.r9
    hax hdi c₁ hB₁ hKY hAY (hrY.trans (by decide))
    ⟨s1.trans hRg.1, s3.trans hRg.2.1, s4.trans hRg.2.2.1, s5.trans hRg.2.2.2⟩
    ((CInv.of_cpuOk hcpu).mem fun j hj => ?_)
    (GotOkB.to_mem ((GotOkB.of_mem hgot).congr fun a h1 h2 =>
      hYZ a (by omega) (by omega) (by unfold Pim.PimVar; omega))) hMB hu hnew
    (fun a ha hj hp => ?_) hT3
  · have e : (cpuRgn.base.add j).toNat = 0x7a4ae0 + j := tg (b := 0x7a4ae0) hj (by decide)
    exact hYZ _ (by omega) (by omega) (by unfold Pim.PimVar; omega)
  · exact (hV a (fun hh => hj (.inl (by omega))) hp).trans (hW a ha fun hk => hj (.inr hk))

end FV7z.Start
