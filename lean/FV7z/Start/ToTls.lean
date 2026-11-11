import FV7z.Start.TlsIn
/-!
# From the launch of `7zzs` to `0x6133c0` in `__libc_start_main` (PLAN.md G3, startup)

`launch_to_cpu` takes the run to the `call` of `__libc_setup_tls` at `0x6133bb`, and `Tls.setup_tls` is about that
function from its entry to its `ret`. Here the two are joined: the `call`, the function, the `ret`.

- `TlsCode L`: the code `__libc_setup_tls` runs is in the code segments `L`.
- `GotOkB`: `GotOk` of bytes; what the `memcpy` called through the PLT asks of the bytes at the call.
- `launch_brk`: where the break of `7zzs` is at its first instruction.
- `lsm_tls`: the `call` at `0x6133bb`, `__libc_setup_tls` and its `ret`, for a run with `Base`.
- `Junk K`: the bytes nothing is said of at `0x6133c0`: stack that `init_cpu_features`, `apply_irel` and
  `__libc_setup_tls` used, and the variables the first two store to (`CpuVar`; of them `CpuOk` and `GotOk` say
  what is needed).
- `launch_to_tls`: for a launch as in `launch_to_cpu`, on a kernel `Modest` that does not refuse memory, the
  `memcpy` of the PLT with its contract (`Tls.CpyAt`): the run from the first instruction goes on as the run from
  `0x6133c0` does, from a new start with the two pages at the first break in its footprint, the break 4544 bytes
  further and the `fs` base at the thread control block; there the registers are as after the prologue (`Rg`),
  `CpuOk` and `GotOk` hold, and the bytes outside `Junk` are `TlsMem V' brk` for bytes `V'` with `MB`. Four system
  calls were made: `arch_prctl (ARCH_CET_STATUS)`, two `brk`, `arch_prctl (ARCH_SET_FS)`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.CpuFeat (cpuW icfW irelW TKi CInv)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.Tls (TlsMem TlsVar TlsMem_out TlsMem_congr Eo Scr t3_low rd_ext CpyAt)

/-- The code `__libc_setup_tls` runs is in the code segments `L`. -/
structure TlsCode (L : List (Addr × List Byte)) : Prop where
  tls : CodeIn L Tls.tls_at Tls.tls
  sbk : CodeIn L Sbrk.sbk_at Sbrk.sbk
  brk : CodeIn L Brk.brk_at Brk.brk
  cpy : ∃ cpy, CodeIn L 4198512#64 cpy ∧ 0 < cpy.length

/-! ## The GOT, as bytes -/

/-- `GotOk` of bytes. -/
def GotOkB (prof : Profile) (W : Addr → Byte) : Prop :=
  ∀ p ∈ V2606.irel, ∀ r ∈ V2606.resolvers, r.1 = p.2 →
    Returns prof r.2.2 (ofBytesLE 64 ((byteAddrs (BitVec.ofNat 64 p.1) 8).map W))

theorem irel_bd : ∀ p ∈ V2606.irel, 0x792018 ≤ p.1 ∧ p.1 + 8 ≤ 0x792110 := by decide

variable {prof : Profile}

/-- `GotOkB` of bytes that are the same in the GOT. -/
theorem GotOkB.congr {W W' : Addr → Byte} (h : GotOkB prof W)
    (he : ∀ a : Addr, 0x792018 ≤ a.toNat → a.toNat < 0x792110 → W' a = W a) : GotOkB prof W' := by
  intro p hp r hr e
  obtain ⟨b1, b2⟩ := irel_bd p hp
  rw [rd_ext (BitVec.ofNat 64 p.1) 8 fun i hi => he _ (by rw [tg hi (by omega)]; omega)
    (by rw [tg hi (by omega)]; omega)]
  exact h p hp r hr e

theorem GotOkB.of_mem {m : Memory} (h : V2606.GotOk prof m) : GotOkB prof fun a => m.readByte a :=
  fun p hp r hr e => h p hp r hr e

theorem GotOkB.to_mem {m : Memory} (h : GotOkB prof fun a => m.readByte a) : V2606.GotOk prof m :=
  fun p hp r hr e => h p hp r hr e

/-! ## The break at the first instruction -/

/-- The break of `7zzs` at its first instruction: a multiple of 4096 from `0x7a9000`, less than `2 ^ 30` and a
page further. -/
theorem launch_brk {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    l.s₀.proc.mm.brk.toNat % 4096 = 0 ∧ 0x7a9000 ≤ l.s₀.proc.mm.brk.toNat ∧
      l.s₀.proc.mm.brk.toNat < 0x7a9000 + 4096 + 2 ^ 30 := by
  obtain ⟨hdr, c, hr, hv, hc, hm, hbm, hbk, -⟩ := launch_full h
  obtain ⟨eD, eB⟩ := zzs_brk
  obtain ⟨k0, k1, k2⟩ := hv.brk
  rw [eB] at k1 k2
  have eb : (BitVec.ofNat 64 c.brk).toNat = c.brk := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hbk, eb]
  omega

/-! ## The `call` at `0x6133bb` -/

def pc891 : List Byte := [0xe8, 0x50, 0x06, 0x00, 0x00]
theorem pc891_0 : ∀ feat, Dec feat pc891 0 (FV7z.mk .call 64 [.rel 1616] 5) := by dec_rfl
theorem w_891 : pc891 <+: lsm.drop 891 := by decide +kernel
theorem call_891 (feat : Features) : Dec feat lsm 891 (FV7z.mk .call 64 [.rel 1616] 5) :=
  Dec.shift (j := 891) (k := 0) (pc891_0 feat) w_891 (Nat.zero_le _)

macro "sd" : tactic =>
  `(tactic| first | (simp only [toBytesLE_length]; done) | (simp only [toBytesLE_length]; bv_omega) | bv_omega | decide)

variable {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {Y : State} {t : Nat}
  {V : Addr → Byte}

/-- The `call` of `__libc_setup_tls` at `0x6133bb`, the function, and its `ret` to `0x6133c0`: for a run with
`Base` and the break `b` as `Tls.setup_tls` asks, the bytes at the call with what the function reads (`hI`) and the
GOT's slots good (`hG`). The run goes on from `0x6133c0`, from a new start with the two new pages; the registers a
call keeps are kept, and outside the 136 bytes below the stack pointer the bytes are `TlsMem V b`. -/
theorem lsm_tls {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hl : CodeIn L lsm_at lsm) (hT : TlsCode L) (hcpy : CpyAt prof L o 4198512#64 (GotOkB prof))
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = lsm_at.add 891)
    (hI : ∀ V₁ : Addr → Byte, (∀ a : Addr, a.toNat < 0x7a9000 → V₁ a = V a) → Tls.In V₁) (hG : GotOkB prof V)
    (hst : ∀ i < 136, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 136) i))
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hhd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x401000 → Foot F.data a)
    (hbl : 0x7a9000 ≤ b.toNat) (hbp : b.toNat % 4096 = 0) (hsp : b.toNat + 8192 + 136 ≤ Y.cpu.gpr.rsp.toNat)
    (hmg : ∀ t p, o t (.memFail p) = none) (hlim : b.toNat / 4096 + 2 ≤ lim)
    (k : ∀ s₂ Z t' W (d r10 r8 r9 : BitVec 64), Seg prof (withNew F [⟨b, 8192⟩]) ([⟨b, 8192⟩] ++ Wl) L s₂ o →
      Base s₂ lim (b + 4544#64) (b + 2176#64) ks → KeptW ([⟨b, 8192⟩] ++ Wl) s₂ Z →
      Agree (withNew F [⟨b, 8192⟩]) Z.proc.mm.mem W → Z.cpu.rip = lsm_at.add 896 → Saved Y.cpu.gpr Z.cpu.gpr →
      (∀ a : Addr, ¬ (Y.cpu.gpr.rsp.toNat - 136 ≤ a.toNat ∧ a.toNat < Y.cpu.gpr.rsp.toNat) → W a = TlsMem V b a) →
      GoG prof L o (gev ++ [⟨12, [0, Y.cpu.gpr.rsi, 63#64, Y.cpu.gpr.r10, 7829360#64, Y.cpu.gpr.r9], b, [], []⟩,
        ⟨12, [b + 4544#64, Y.cpu.gpr.rsi, 63#64, Y.cpu.gpr.r10, 7829360#64, Y.cpu.gpr.r9], b + 4544#64, [], []⟩,
        ⟨158#64, [4098#64, b + 2176#64, d, r10, r8, r9], 0, [], []⟩]) gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hb47 := hB.brk_lt
  have e8 : (Y.cpu.gpr.rsp - 8#64).toNat = Y.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have slot : ∀ a : Addr, ∀ j < 136, a = Addr.add (Y.cpu.gpr.rsp - 136) j → Foot Wl a :=
    fun a j hj ha => ha ▸ hst j hj
  refine c.s_call hK hA hl (lt_len (by decide)) hrip (call_891 _) hT.tls (Tls.lt_len (by decide)) (by decide)
    (fun i hi => slot _ (128 + i) (by omega) (by simp only [Addr.add]; bv_omega)) ?_
  rintro X t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  have hsp₁ : X.cpu.gpr.rsp = Y.cpu.gpr.rsp - 8 := by rw [hg₁]; rfl
  have hsi₁ : X.cpu.gpr.rsi = Y.cpu.gpr.rsi := by rw [hg₁]; rfl
  have h10 : X.cpu.gpr.r10 = Y.cpu.gpr.r10 := by rw [hg₁]; rfl
  have h9 : X.cpu.gpr.r9 = Y.cpu.gpr.r9 := by rw [hg₁]; rfl
  obtain ⟨cpy, hc1, hc2⟩ := hT.cpy
  have hV₁ : ∀ a : Addr, ¬ (Y.cpu.gpr.rsp.toNat - 8 ≤ a.toNat ∧ a.toNat < Y.cpu.gpr.rsp.toNat) →
      Vst V (Y.cpu.gpr.rsp - 8) (toBytesLE (lsm_at.add (891 + 5)) 8) a = V a := by
    intro a ha
    rw [Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]
  refine Tls.setup_tls c hB hT.tls hT.sbk hT.brk hc1 hc2 hcpy hK₁ hA₁ hr₁ (hI _ fun a ha => hV₁ a (by omega))
    (fun i hi => ?_) hgl hhd hbl hbp (by rw [hsp₁]; bv_omega) hmg hlim (fun W hW => ?_) ?_
  · rw [hsp₁]
    exact slot _ i (by omega) (by simp only [Addr.add]; bv_omega)
  · refine hG.congr fun a h1 h2 => ?_
    rw [hW a (by unfold Scr; rw [hsp₁]; bv_omega), t3_low _ hbl (by omega), hV₁ a (by omega)]
  rw [hsi₁, h10, h9]
  intro s₂ Z t₂ W d r10 r8 r9 c₂ hB₂ hK₂ hA₂ hr₂ hax₂ hsv₂ hW₂
  obtain ⟨hs_sp, hs_bx, hs_bp, hs_12, hs_13, hs_14, hs_15⟩ := hsv₂
  rw [hsp₁] at hW₂ hs_sp
  have hra : rdq(W, Z.cpu.gpr.rsp) = lsm_at.add 896 := by
    rw [hs_sp, hW₂.rd _ 8 fun i hi => by unfold Scr; simp only [Addr.add]; bv_omega,
      rd_ext _ 8 fun i hi => TlsMem_out _ hbl (by omega) (by unfold TlsVar; simp only [Addr.add]; bv_omega)
        (by simp only [Addr.add]; bv_omega), rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  refine c₂.s_ret hK₂ hA₂ hT.tls (Tls.lt_len (by decide)) hr₂ (Tls.ret_523 _) (fun i hi => ?_) hl (j₂ := 896)
    (lt_len (by decide)) hra ?_
  · rw [hs_sp]
    exact c₂.hws _ (foot_append_iff.2 (.inr (slot _ (128 + i) (by omega) (by simp only [Addr.add]; bv_omega))))
  rintro Z₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  refine k s₂ Z₃ t₃ W d r10 r8 r9 c₂ hB₂ hK₃ hA₃ hr₃ ?_ fun a ha => ?_
  · rw [hg₃]
    refine ⟨?_, hs_bx.trans (by rw [hg₁]; rfl), hs_bp.trans (by rw [hg₁]; rfl), hs_12.trans (by rw [hg₁]; rfl),
      hs_13.trans (by rw [hg₁]; rfl), hs_14.trans (by rw [hg₁]; rfl), hs_15.trans (by rw [hg₁]; rfl)⟩
    show Z.cpu.gpr.rsp + 8 = Y.cpu.gpr.rsp
    rw [hs_sp]
    bv_omega
  · rw [hW₂ a (by unfold Scr; bv_omega)]
    exact TlsMem_congr (fun i hi => hV₁ _ (by simp only [Addr.add]; bv_omega)) fun _ => hV₁ a (by omega)

/-! ## From the launch -/

/-- The bytes nothing is said of at `0x6133c0`: the stack from 152 bytes below `K.bp` to the stack pointer
(`K.bp + 112`) and 76 bytes from `K.bp + 156`, which `init_cpu_features`, `apply_irel` and `__libc_setup_tls` used,
and the variables the first two store to. -/
def Junk (K : Ctx) (a : Addr) : Prop :=
  (K.bp.toNat ≤ a.toNat + 152 ∧ a.toNat < K.bp.toNat + 112) ∨
    (K.bp.toNat + 156 ≤ a.toNat ∧ a.toNat < K.bp.toNat + 232) ∨ CpuVar a

/-- The data of `zzsFoot` is data of the footprint with new pages. -/
theorem zzs_new {lo top : Nat} {N : List Rgn} {a : Addr} (h : Foot (zzsFoot lo top L).data a) :
    Foot (withNew (zzsFoot lo top L) N).data a := by
  rcases foot_append_iff.1 h with h | h
  · rcases foot_append_iff.1 h with h | h
    · exact foot_writes (foot_append_iff.2 (.inr h))
    · obtain ⟨r, hr, -⟩ := h
      cases hr
  · exact foot_reads h

/-- From the launch of `7zzs` to `0x6133c0` in `__libc_start_main`, after `__libc_setup_tls`. -/
theorem launch_to_tls {l : Launch} {n : Nat}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 656 ≤ n)
    (hs : l.args.secure = false) (hnp : l.args.threadPending = [] ∧ l.args.signal.pending = [])
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L)
    (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none)
    (hcpy : CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
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
        Z.cpu.rip = 0x6133c0 → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → MB (ctxOf l.prof l.s₀ l.args c) V' →
        (∀ a : Addr, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data a ∨
            (l.s₀.proc.mm.brk.toNat ≤ a.toNat ∧ a.toNat < l.s₀.proc.mm.brk.toNat + 8192) →
          ¬ Junk (ctxOf l.prof l.s₀ l.args c) a → W a = TlsMem V' l.s₀.proc.mm.brk a) →
        GoG l.prof L o (gev ++ [Seg.cetEv g,
          ⟨12, [0, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk, [], []⟩,
          ⟨12, [l.s₀.proc.mm.brk + 4544#64, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk + 4544#64, [], []⟩,
          ⟨158#64, [4098#64, l.s₀.proc.mm.brk + 2176#64, d, r10, r8, r9], 0, [], []⟩]) gP gE Z t') →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hto⟩ := launch_to_cpu (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom hn hs noG noA hpc
    hch ho hL hC
  refine ⟨c, hv, hst, fun hfin => hto ?_⟩
  obtain ⟨h16, hn', hst', hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  have hq : ((ctxOf l.prof l.s₀ l.args c).bp + 104#64).toNat = (stackLayout l.args l.prof.linux c).sp - 296 := by
    show (l.s₀.cpu.gpr.rsp - 400#64 + 104#64).toNat = _
    bv_omega
  have hq2 : ((ctxOf l.prof l.s₀ l.args c).bp + 112#64).toNat = (stackLayout l.args l.prof.linux c).sp - 288 := by
    show (l.s₀.cpu.gpr.rsp - 400#64 + 112#64).toNat = _
    bv_omega
  obtain ⟨kbp, kmain, kargc, kargv, kinit, kfini, krtld, kV0, kq, kz, kln⟩ := ctxOf_entry l.prof l.s₀ l.args c
  have himg : l.s₀.cpu.gpr.rsp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ l.s₀.cpu.gpr.rsp.toNat := .inr (by omega)
  have hI0 : Img (ctxOf l.prof l.s₀ l.args c).V0 := kV0 ▸ Entry.V1_img (launch_img h) (by omega) himg
  have hB0 : Bss (ctxOf l.prof l.s₀ l.args c).V0 := kV0 ▸ Entry.V1_bss (launch_bss h) (by omega) himg
  have hK : (ctxOf l.prof l.s₀ l.args c).Ok := Ctx.ok (hst.lch (by omega) hs noG noA) hI0 kq kz kln
  have hsg := launch_segOf (lo := (stackLayout l.args l.prof.linux c).sp - n) (L := L) (o := o) h hroom hst
    (by omega) (by omega) (by omega) hL ho
  obtain ⟨hb0, hb1, hb2⟩ := launch_brk h
  obtain ⟨hph, hpn⟩ := ctxOf_ph l.prof l.s₀ l.args c
  clear kbp kmain kargc kargv kinit kfini krtld kV0 kq kz kln hto himg
  intro g g' V' hF Y t' hax hdi hKY hcpu hgot hmem hripY hTK
  obtain ⟨⟨r_sp, r_bp, r_12, r_13⟩, -, hMB⟩ := hF
  have hspY : Y.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp - 288 := by rw [hTK.sp, r_sp, hq2]
  have hcj : ∀ a, Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) a → Junk (ctxOf l.prof l.s₀ l.args c) a := by
    intro a hf
    rcases cpuW_bd hK (by omega) hf with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · rcases cpuW_fine (by omega) (by omega) hf with h2 | h2
      · omega
      · exact .inr (.inr h2)
  have hcn : ∀ a : Addr, a.toNat < 0x7a9000 → ¬ CpuVar a →
      ¬ Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) a := by
    intro a ha hc hf
    rcases cpuW_fine (by omega) (by omega) hf with h2 | h2
    · omega
    · exact hc h2
  refine lsm_tls hsg (launch_base h hroom hM hnp) hC.lsm hT hcpy hKY (V := fun a => Y.proc.mm.mem.readByte a)
    (fun _ _ => rfl) (hripY.trans (by decide)) (fun V₁ hV₁ => ?_) (GotOkB.of_mem hgot) (fun i hi => ?_)
    (fun a h1 h2 => zzsFoot_var h1 h2) (fun a h1 h2 => foot_reads (zzsFoot_hdr h1 h2)) hb1 hb0 (by omega) hmg
    (by unfold pageUp; omega) ?_
  · refine tls_in hK hI0 hB0 hMB hph hpn fun a ha hc => ?_
    rw [hV₁ a (by omega)]
    refine hmem a ?_ (hcn a (by omega) hc)
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact foot_reads (zzsFoot_hdr h1 h2)
    · exact foot_writes (zzsFoot_var h1 h2)
  · exact zzsFoot_stack htop (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  intro s₂ Z t₂ W d r10 r8 r9 c₂ hB₂ hK₂ hA₂ hr₂ hsv hW
  obtain ⟨s_sp, s_bx, s_bp, s_12, s_13, s_14, s_15⟩ := hsv
  have hZ : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → ¬ TlsVar a →
      Z.proc.mm.mem.readByte a = Y.proc.mm.mem.readByte a := by
    intro a h1 h2 h3
    rw [hA₂ a (zzs_new (foot_writes (zzsFoot_var h1 h2))), hW a (by omega),
      TlsMem_out _ hb1 (by omega) h3 (by omega)]
  rw [List.append_assoc]
  refine hfin s₂ Z t₂ W V' g _ _ _ d r10 r8 r9 hax hdi c₂ hB₂ hK₂ hA₂ (hr₂.trans (by decide))
    (show _ ∧ _ ∧ _ ∧ _ from ⟨s_sp.trans (hTK.sp.trans r_sp), s_bp.trans (hTK.rbp.trans r_bp),
      s_12.trans (hTK.r12.trans r_12), s_13.trans (hTK.r13.trans r_13)⟩)
    ((CInv.of_cpuOk hcpu).mem fun j hj => ?_)
    (GotOkB.to_mem ((GotOkB.of_mem hgot).congr fun a h1 h2 =>
      hZ a (by omega) (by omega) (by unfold TlsVar; omega))) hMB fun a ha hj => ?_
  · have e : (cpuRgn.base.add j).toNat = 0x7a4ae0 + j := tg (b := 0x7a4ae0) hj (by decide)
    exact hZ _ (by omega) (by omega) (by unfold TlsVar; omega)
  · rw [hW a fun hh => hj (.inl (by omega))]
    refine TlsMem_congr (fun i hi => ?_) fun hnb => ?_
    · have e : (Addr.add 7829360#64 i).toNat = 7829360 + i := tg (b := 7829360) hi (by decide)
      exact hmem _ (foot_writes (zzsFoot_var (by omega) (by omega)))
        (hcn _ (by omega) fun hc => by unfold CpuVar at hc; omega)
    · exact hmem a (ha.resolve_right hnb) fun hf => hj (hcj a hf)

end FV7z.Start
