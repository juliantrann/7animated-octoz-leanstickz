import FV7z.Pim.D
/-!
# `__pthread_initialize_minimal_internal` at the level of the function (PLAN.md G3, startup)

`pim_ok`: the function at `0x6000b0` entered with one thread, its descriptor at the `fs` base, the lock of
`__default_pthread_attr` free, the fork handlers' lock free and their list not set up, and the tunable of the stack's
size not set. The run makes six system calls (`set_tid_address`, `set_robust_list`, `rt_sigaction` for the signals 32
and 33, `rt_sigprocmask`, `prlimit64`) and reaches the return address with the registers a function keeps. It is
`pim_a`, `pim_b`, `pim_c` and `pim_d` one after the other.

- `MemCA_rd`: bytes the stores of the first three stretches leave.
- `PimVar`, `MemE_keep`: the bytes the function stores to outside its frame; the others are as before.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- Bytes the stores of `MemA` and `MemC` leave: outside `__stack_user`, the two variables of the static TLS block
and the thread's block from offset 704. -/
theorem MemCA_rd {V : Addr → Byte} {fb : Addr} {tid : Nat} {am tv : BitVec 64} {x : Addr} {n : Nat}
    (hfb : fb.toNat + 1704 ≤ 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ 7991568 ∨ 7991584 ≤ x.toNat) (h2 : x.toNat + n ≤ 8027696 ∨ 8027720 ≤ x.toNat)
    (h3 : x.toNat + n ≤ fb.toNat + 704 ∨ fb.toNat + 1704 ≤ x.toNat) :
    List.map (MemC (MemA V fb tid) am tv) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  unfold MemC MemA
  repeat rw [vr (by ln) (by bv_omega) hx (by bv_omega)]

/-- The bytes the function stores to outside its frame: `_dl_init_static_tls`, `__stack_user`, the lock of
`__default_pthread_attr`, the fork handlers' lock and list, `__static_tls_size` and `__static_tls_align_m1` with
`__libc_multiple_threads_ptr`, `__is_smp`, the default attributes' two sizes, `__libc_pthread_init`'s pointer,
`_dl_wait_lookup_done`, and the thread's descriptor from offset 704. -/
def PimVar (fb : Addr) (a : Addr) : Prop :=
  (0x793400 ≤ a.toNat ∧ a.toNat < 0x793408) ∨ (0x79f110 ≤ a.toNat ∧ a.toNat < 0x79f120) ∨
    (0x7a3160 ≤ a.toNat ∧ a.toNat < 0x7a3164) ∨ (0x7a3f20 ≤ a.toNat ∧ a.toNat < 0x7a3f78) ∨
    (0x7a7e30 ≤ a.toNat ∧ a.toNat < 0x7a7e48) ∨ (0x7a7e64 ≤ a.toNat ∧ a.toNat < 0x7a7e68) ∨
    (0x7a7e90 ≤ a.toNat ∧ a.toNat < 0x7a7ea8) ∨ (0x7a8410 ≤ a.toNat ∧ a.toNat < 0x7a8418) ∨
    (0x7a8578 ≤ a.toNat ∧ a.toNat < 0x7a8580) ∨ (fb.toNat + 704 ≤ a.toNat ∧ a.toNat < fb.toNat + 1704)

/-- A byte the function does not store to outside its frame. -/
theorem MemE_keep {V W : Addr → Byte} {fb : Addr} {tid : Nat} {am tv sz : BitVec 64}
    (hfb : fb.toNat + 1704 ≤ 2 ^ 64)
    (hW : ∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
      W a = MemD (MemC (MemA V fb tid) am tv) sz a) (a : Addr) (h : ¬ PimVar fb a) : MemE W a = V a := by
  unfold PimVar at h
  unfold MemE
  rw [vo (by ln) (by decide) (by bv_omega), vo (by ln) (by decide) (by bv_omega), hW a (by omega) (by omega)]
  unfold MemD MemD1 MemC MemA
  repeat rw [vo (by ln) (by bv_omega) (by bv_omega)]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__pthread_initialize_minimal_internal`: six system calls, then the return address, with the registers a
function keeps. Outside the 552 bytes below the entry's stack pointer the bytes are `MemE W`: the stores of the
function over the bytes `V` of the entry, apart from what `__libc_pthread_init` set up. -/
theorem pim_ok {lim : Nat} {b fb : Addr} {kst : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fb kst)
    (hin : CodeIn L pim_at pim) (hinS : CodeIn L Sga.sga_at Sga.sga) (hinG : CodeIn L Gts.gts_at Gts.gts)
    (hinR : CodeIn L Grl.grl_at Grl.grl) (hinL : CodeIn L Lpi.lpi_at Lpi.lpi)
    (hinRf : CodeIn L Raf.raf_at Raf.raf) (hinP : CodeIn L Pti.pti_at Pti.pti)
    (hinT : CodeIn L Tgv.tgv_at Tgv.tgv) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pim_at) (hL : Lay F Wl X.cpu.gpr.rsp fb)
    (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat) (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i))
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hself : rdq(V, fb + 16#64) = fb) (hlk : rdd(V, 8008032#64) = 0) (hmt : rdd(V, fb + 24#64) = 0)
    (hfl : rdd(V, 8011552#64) = 0) (hfg : rdb(V, 8011556#64) = 0) (ht0 : rdd(V, 7936880#64) = 0)
    (htz : rdb(V, 7936912#64) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ s₁ V' g' Z t' (W : Addr → Byte) (am tv sz : BitVec 64), Seg prof F Wl L s₁ o →
      Base s₁ lim b fb kst → KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
        W a = MemD (MemC (MemA V fb kst.tid) am tv) sz a) → rdq(W, 8029200#64) = 8027680#64 →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = MemE W a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → Osv.Back X.cpu.gpr g' →
      GoG prof L o (gev ++ [tidEv X.cpu.gpr fb kst.tid] ++ [robEv X.cpu.gpr fb] ++
        [sgEv (BitVec.setWidth 64 32#32) X.cpu.gpr.r9 X.cpu.gpr.rsp] ++
        [sgEv (BitVec.setWidth 64 33#32) 0 X.cpu.gpr.rsp] ++ [mskEv X.cpu.gpr.rsp] ++
        [rlEv X.cpu.gpr.rsp 0 0 (s₁.proc.signal.rlimits ⟨3, by decide⟩).bytes]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := X.cpu.gpr.rsp.isLt
  have hf : fb.toNat + 1704 ≤ 2 ^ 64 := by omega
  refine pim_a c hB hin hK hA hrip hL hself ?_
  intro s₁ V₁ g₁ Z₁ t₁ c₁ hB₁ hK₁ hA₁ hF₁ hr₁ hg₁ hR₁ hdx₁ h9₁
  subst hg₁
  refine pim_b c₁ hB₁ hin hinS hK₁ hA₁ hr₁ hL htop hF₁ hR₁ hdx₁ ?_
  intro s₂ V₂ g₂ Z₂ t₂ c₂ hB₂ hK₂ hA₂ hF₂ hr₂ hg₂ hR₂ h8₂ h9₂
  subst hg₂
  rw [h9₁]
  refine pim_c c₂ hB₂.fsb hin hinG hinR hK₂ hA₂ hr₂ hL htop hF₂ hR₂ ?_
  intro V₃ g₃ Z₃ t₃ am tv sz hK₃ hA₃ hF₃ hsz hr₃ hg₃ hR₃ hax₃ hdx₃
  subst hg₃
  rw [h8₂, h9₂]
  refine pim_d c₂ hB₂.fsb hin hinL hinRf hinP hinT hK₃ hA₃ hr₃ hL hro hs8 hl hF₃ hsz hR₃ hax₃ hdx₃
    (congrArg (ofBytesLE 64) (MemCA_rd hf (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)))
    ((congrArg (ofBytesLE 32) (MemCA_rd hf (by decide) (by decide) (by decide) (by bv_omega))).trans hlk)
    ((congrArg (ofBytesLE 32) (MemCA_rd hf (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega))).trans hmt)
    ((congrArg (ofBytesLE 32) (MemCA_rd hf (by decide) (by decide) (by decide) (by bv_omega))).trans hfl)
    ((congrArg (ofBytesLE 8) (MemCA_rd hf (by decide) (by decide) (by decide) (by bv_omega))).trans hfg)
    ((congrArg (ofBytesLE 32) (MemCA_rd hf (by decide) (by decide) (by decide) (by bv_omega))).trans ht0)
    ((congrArg (ofBytesLE 8) (MemCA_rd hf (by decide) (by decide) (by decide) (by bv_omega))).trans htz)
    hin₂ h₂ ((congrArg (ofBytesLE 64) (MemCA_rd hf hs8 (by bv_omega) (by bv_omega) (by bv_omega))).trans hra) ?_
  intro V₄ g₄ Z₄ t₄ W hK₄ hA₄ hW hpW ho hr₄ hg₄ hb
  exact k s₂ V₄ g₄ Z₄ t₄ W am tv sz c₂ hB₂ hK₄ hA₄ hW hpW ho hr₄ hg₄ hb

end FV7z.Pim
