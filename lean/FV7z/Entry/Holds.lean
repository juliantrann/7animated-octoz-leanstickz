import FV7z.Entry.Cuts
import FV7z.Start.Image
/-!
# From the file's entry to `__libc_start_main` (PLAN.md G3, startup)

`_start` (`0x41d350`, the ELF header's entry): with `rsp` at `argc`, a multiple of 16, as the launch gives it, the run
goes through `_start`'s one block (`vc_0`) and its `call` (`Seg.s_call`) to `__libc_start_main`'s first byte, with
`main` (`0x41cd90`), `argc`, `argv` (`rsp + 8`), `__libc_csu_init` (`0x613ca0`), `__libc_csu_fini` (`0x613d40`) and
`rdx` (the dynamic linker's function to run at exit: none here) in the registers, and three words stored below the
launch's stack: `rax`, the stack's end (`rsp - 8`), and the return address (`V1`). `entry_lsm`: so for a `Ctx` with
these values, the run from the entry goes on as from `I0`, what `start_cfg` and `start_cpu` begin with.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Entry
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Start (Ctx I0 lsm lsm_at)
namespace FV7z.Entry

/-- The `call` of `__libc_start_main` (with an address-size prefix, which does nothing to it). -/
def pcall : List Byte := [0x67, 0xe8, 0xc2, 0x5c, 0x1f, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 0x1f5cc2] 6) := by dec_rfl
theorem w_40 : pcall <+: ent.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat ent 40 (FV7z.mk .call 64 [.rel 0x1f5cc2] 6) :=
  Dec.shift (j := 40) (k := 0) (pcall_0 feat) w_40 (Nat.zero_le _)

/-- `and rsp, -16` rounds down to 16 bytes. -/
theorem and16 (x : BitVec 64) : x &&& 18446744073709551600#64 = (x >>> 4) <<< 4 := by
  have m : ∀ i, i < 64 → (18446744073709551600#64).getLsbD i = decide (4 ≤ i) := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, m i hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 4
  · simp [h, show ¬ 4 ≤ i by omega]
  · have e : 4 + (i - 4) = i := by omega
    simp [h, hi, e, show 4 ≤ i by omega]

/-- With `rsp` a multiple of 16 at the entry, as the launch gives it. -/
theorem and16_sp (x : BitVec 64) (hal : x.toNat % 16 = 0) :
    (x + 8#64) &&& 18446744073709551600#64 = x := by
  rw [and16]
  bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- The registers and the bytes at the `call`. -/
def P (g : Gprs) (V : Addr → Byte) (g' : Gprs) (V' : Addr → Byte) : Prop :=
  g'.rsp = g.rsp - 16#64 ∧ g'.rdi = 0x41cd90#64 ∧ g'.rsi = rdq(V, g.rsp) ∧ g'.rdx = g.rsp + 8#64 ∧
    g'.rcx = 0x613ca0#64 ∧ g'.r8 = 0x613d40#64 ∧ g'.r9 = g.rdx ∧
    V' = Vst (Vst V (g.rsp - 8#64) (toBytesLE g.rax 8)) (g.rsp - 16#64) (toBytesLE (g.rsp - 8#64) 8)

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hal : g.rsp.toNat % 16 = 0) (hlo : 24 ≤ g.rsp.toNat)
    (hr : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (hw : ∀ a : Addr, g.rsp.toNat ≤ a.toNat + 24 → a.toNat < g.rsp.toNat → Foot Wl a) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ P g V g' V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  have hal' : rsp.toNat % 16 = 0 := hal
  have hlo' : 24 ≤ rsp.toNat := hlo
  have e : (rsp + 8 &&& 18446744073709551600#64) = rsp := and16_sp rsp hal'
  have e2 : rsp - 8 - 8 = rsp - 16#64 := by bv_omega
  rw [e, e2]
  refine ⟨hr, fun i hi => hw _ ?_ ?_, fun i hi => hw _ ?_ ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  all_goals
    simp only [Addr.add]
    bv_omega

/-- The bytes at `__libc_start_main`'s entry: `_start`'s three words below the launch's stack. -/
def V1 (V : Addr → Byte) (sp rax : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (sp - 8#64) (toBytesLE rax 8)) (sp - 16#64) (toBytesLE (sp - 8#64) 8)) (sp - 24#64)
    (toBytesLE (ent_at.add 46) 8)

/-- The launch's stack is as it was. -/
theorem V1_out (V : Addr → Byte) (sp rax : BitVec 64) (hlo : 24 ≤ sp.toNat) (a : Addr)
    (h : a.toNat + 24 < sp.toNat ∨ sp.toNat ≤ a.toNat) : V1 V sp rax a = V a := by
  unfold V1
  rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]

/-- `__libc_start_main`'s argument on the stack: the stack's end. -/
theorem V1_end (V : Addr → Byte) (sp rax : BitVec 64) (hlo : 24 ≤ sp.toNat) :
    rdq(V1 V sp rax, sp - 16#64) = sp - 8#64 := by
  unfold V1
  rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by bv_omega)
      (by simp only [toBytesLE_length]; bv_omega),
    rd_Vst_self _ _ _ (by simp only [toBytesLE_length]) (by bv_omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From the entry to `__libc_start_main`'s first byte. -/
theorem entry_start (c : Seg prof F Wl L s₀ o) (he : CodeIn L ent_at ent) (hl : CodeIn L lsm_at lsm)
    {X : State} {t : Nat} {V : Addr → Byte} (hX : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = ent_at) (hal : X.cpu.gpr.rsp.toNat % 16 = 0) (hlo : 24 ≤ X.cpu.gpr.rsp.toNat)
    (hr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat + 24 → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hnext : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V1 V X.cpu.gpr.rsp X.cpu.gpr.rax) →
      Y.cpu.rip = lsm_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 → Y.cpu.gpr.rdi = 0x41cd90#64 →
      Y.cpu.gpr.rsi = rdq(V, X.cpu.gpr.rsp) → Y.cpu.gpr.rdx = X.cpu.gpr.rsp + 8#64 →
      Y.cpu.gpr.rcx = 0x613ca0#64 → Y.cpu.gpr.r8 = 0x613d40#64 → Y.cpu.gpr.r9 = X.cpu.gpr.rdx →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine ((c_0 prof).at c he).run (fun j' g' _ V' => j' = 40 ∧ P X.cpu.gpr V g' V') hX hA
    (by rw [hrip, addr_add_zero]) (vc_0 hal hlo hr hw) ?_
  rintro j' g fl V' ⟨rfl, hsp, hdi, hsi, hdx, hcx, h8, h9, rfl⟩ Y t' hKY hAY hrY rfl rfl
  refine c.s_call hKY hAY he (by rw [ent_length]; decide) hrY (call_40 prof.feat) hl
    (by rw [Start.lsm_length]; decide) (by decide) (fun i hi => hw _ ?_ ?_) ?_
  · rw [hsp]; simp only [Addr.add]; bv_omega
  · rw [hsp]; simp only [Addr.add]; bv_omega
  · rintro Z t₁ hKZ hAZ ⟨hrZ, hgZ⟩
    have e3 : X.cpu.gpr.rsp - 16#64 - 8 = X.cpu.gpr.rsp - 24#64 := by bv_omega
    rw [hsp, e3] at hAZ hgZ
    refine hnext Z t₁ hKZ hAZ hrZ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hgZ]; rfl
    · rw [hgZ]; exact hdi
    · rw [hgZ]; exact hsi
    · rw [hgZ]; exact hdx
    · rw [hgZ]; exact hcx
    · rw [hgZ]; exact h8
    · rw [hgZ]; exact h9

/-- From the entry to `__libc_start_main`, in the terms of its proof: for a `Ctx` with the launch's values, the
run from the entry goes on as from `I0`. -/
theorem entry_lsm (c : Seg prof F Wl L s₀ o) (he : CodeIn L ent_at ent) (hl : CodeIn L lsm_at lsm)
    {X : State} {t : Nat} {V : Addr → Byte} (hX : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = ent_at) (hal : X.cpu.gpr.rsp.toNat % 16 = 0) (hlo : 24 ≤ X.cpu.gpr.rsp.toNat)
    (hr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat + 24 → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (K : Ctx) (hbp : K.bp + 376#64 = X.cpu.gpr.rsp - 24#64) (hmain : K.main = 0x41cd90#64)
    (hargc : K.argc = (rdq(V, X.cpu.gpr.rsp)).setWidth 32) (hargv : K.argv = X.cpu.gpr.rsp + 8#64)
    (hinit : K.init = 0x613ca0#64) (hfini : K.fini = 0x613d40#64) (hrtld : K.rtld = X.cpu.gpr.rdx)
    (hV0 : K.V0 = V1 V X.cpu.gpr.rsp X.cpu.gpr.rax)
    (hnext : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem K.V0 → Y.cpu.rip = lsm_at →
      I0 K (K.N + 20) Y.cpu.gpr K.V0 → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  entry_start c he hl hX hA hrip hal hlo hr hw fun Y t' hKY hAY hrY hsp hdi hsi hdx hcx h8 h9 =>
    hnext Y t' hKY (hV0 ▸ hAY) hrY
      ⟨hsp.trans hbp.symm, hdi.trans hmain.symm, by rw [hsi, hargc], hdx.trans hargv.symm, hcx.trans hinit.symm,
        h8.trans hfini.symm, h9.trans hrtld.symm, rfl, rfl⟩

/-- The image is as it was: `_start`'s words are apart from it. -/
theorem V1_img {V : Addr → Byte} {sp rax : BitVec 64} (h : Start.Img V) (hlo : 24 ≤ sp.toNat)
    (himg : sp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ sp.toNat) : Start.Img (V1 V sp rax) := by
  intro a n bs hp h1 h2 i hi
  have e : (BitVec.ofNat 64 (a + i)).toNat = a + i := by simp only [BitVec.toNat_ofNat]; omega
  rw [V1_out V sp rax hlo _ (by omega)]
  exact h a n bs hp h1 h2 i hi

theorem V1_bss {V : Addr → Byte} {sp rax : BitVec 64} (h : Start.Bss V) (hlo : 24 ≤ sp.toNat)
    (himg : sp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ sp.toNat) : Start.Bss (V1 V sp rax) := by
  intro a h1 h2
  rw [V1_out V sp rax hlo _ (by omega)]
  exact h a h1 h2

open FV7z.Glibc in
open FV7z.CpuFeat (cpuW IE JT RE TKi rela) in
/-- From the file's entry to `0x6133bb` in `__libc_start_main`, past `_dl_relocate_static_pie`, `_dl_aux_init`,
`__libc_init_secure`, `__tunables_init`, `init_cpu_features` and `apply_irel`: there the processor's features are
recorded as it reports them (`CpuOk`) and every slot of the GOT holds a variant the processor has (`GotOk`). The
image's bytes are the file's at the entry (`Img`, `Bss`). -/
theorem entry_cpu (c : Seg prof F Wl L s₀ o) (he : CodeIn L ent_at ent) (hl : CodeIn L lsm_at lsm)
    (hp : CodeIn L Pie.pie_at Pie.pie) (ha : CodeIn L Auxv.aux_at Auxv.aux) (hs : CodeIn L Sec.sec_at Sec.sec)
    (ht : CodeIn L Tun.tin_at Tun.tin)
    {X : State} {t : Nat} {V : Addr → Byte} (hX : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = ent_at) (hal : X.cpu.gpr.rsp.toNat % 16 = 0) (hlo : 24 ≤ X.cpu.gpr.rsp.toNat)
    (hr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat + 24 → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hI : Start.Img V) (hB : Start.Bss V) (himg : X.cpu.gpr.rsp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ X.cpu.gpr.rsp.toNat)
    (K : Ctx) (hbp : K.bp + 376#64 = X.cpu.gpr.rsp - 24#64) (hmain : K.main = 0x41cd90#64)
    (hargc : K.argc = (rdq(V, X.cpu.gpr.rsp)).setWidth 32) (hargv : K.argv = X.cpu.gpr.rsp + 8#64)
    (hinit : K.init = 0x613ca0#64) (hfini : K.fini = 0x613d40#64) (hrtld : K.rtld = X.cpu.gpr.rdx)
    (hV0 : K.V0 = V1 V X.cpu.gpr.rsp X.cpu.gpr.rax)
    (hL : K.Lch) (hq : K.aq = Start.aqI) (hz : K.az = Start.azI) (hln : K.alen = Start.alenI)
    (hE : Start.Env K F Wl) (hcw : ∀ y, Foot (cpuW (K.bp + 104#64)) y → Foot Wl y)
    (hIE : IE F (cpuW (K.bp + 104#64)) L K.V0 (K.bp + 104#64))
    (hJd : ∀ i < 280, Foot F.data ((0x6ee6d0 : Addr).add i))
    (hJn : ∀ i < 280, ¬ Foot (cpuW (K.bp + 104#64)) ((0x6ee6d0 : Addr).add i))
    (hR : RE F (cpuW (K.bp + 104#64)) L (K.bp + 104#64))
    (hTn : ∀ j < 744, ¬ Foot (cpuW (K.bp + 104#64)) ((0x400248 : Addr).add j))
    (hpc : prof.Consistent) (hch : Chain prof) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hfin : ∀ (g g' : Gprs) (V' : Addr → Byte), Start.FinP K g' V' → ∀ (Y : State) (t' : Nat),
      g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 → KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem →
      V2606.GotOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot (cpuW (K.bp + 104#64)) y → Y.proc.mm.mem.readByte y = V' y) →
      Y.cpu.rip = 0x6133bb → TKi g' Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hI0 : Start.Img K.V0 := hV0 ▸ V1_img hI hlo himg
  have hB0 : Start.Bss K.V0 := hV0 ▸ V1_bss hB hlo himg
  exact entry_lsm c he hl hX hA hrip hal hlo hr hw K hbp hmain hargc hargv hinit hfini hrtld hV0
    fun Y t' hKY hAY hrY hIY =>
      Start.start_cpu c hl hp ha hs ht (Start.Ctx.ok hL hI0 hq hz hln) hE hcw hIE ⟨hJd, hJn, hI0.jtab⟩ hR
        (fun j hj => ⟨hTn j hj, hI0.rela j hj⟩) hB0.cinv hpc hch hdf hx87 hfin hKY hAY hrY hIY

end FV7z.Entry
