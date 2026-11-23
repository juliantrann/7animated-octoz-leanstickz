import FV7z.Start.LifCode
import FV7z.Start.LifFoot
/-!
# What the first `malloc` needs, at `__libc_init_first` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `Gor.MCx`: the code of `malloc` and the functions it calls, the root `Base`, footprints of
the globals `malloc` stores to and of the words near the thread pointer, the bounds, and the new pages `N` that the
first `MORECORE` maps. At the call of `__libc_init_first` the break is `B + 4544` (`B` the launch's break, the
static TLS block below it) and the thread pointer `B + 2176` (`launch_to_ptr`); `mp_.top_pad` is `0x20000`, so the
first request grows the heap by `size 0x20000 656 = 0x21000` bytes, the pages `[B + 8192, B + 0x23000)`.

- `MalCode`: the code of `malloc` and its callees in `L`.
- `brkN`: those new pages.
- `ent_mcx`: `MCx` for the footprint of `launch_to_ptr`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Smm (corr size corr_toNat)

/-- The code of `malloc` and of the functions its first call runs through is in `L`. -/
structure MalCode (L : List (Addr × List Byte)) : Prop where
  mal : CodeIn L Mal.mal_at Mal.mal
  mhi : CodeIn L Mhi.mhi_at Mhi.mhi
  pmi : CodeIn L Pmi.pmi_at Pmi.pmi
  tgv : CodeIn L Tgv.tgv_at Tgv.tgv
  tci : CodeIn L Tci.tci_at Tci.tci
  imm : CodeIn L Imm.imm_at Imm.imm
  smm : CodeIn L Smm.smm_at Smm.smm
  dmc : CodeIn L Dmc.dmc_at Dmc.dmc
  sbk : CodeIn L Sbrk.sbk_at Sbrk.sbk
  brk : CodeIn L Brk.brk_at Brk.brk

/-- The pages the first `MORECORE` maps, above the two pages of the launch's break `B`. -/
abbrev brkN (B : Addr) : List Rgn := [⟨B + 8192#64, 0x21000⟩]

theorem foot_one {base a : Addr} {len : Nat} (h1 : base.toNat ≤ a.toNat) (h2 : a.toNat < base.toNat + len) :
    Foot [⟨base, len⟩] a :=
  ⟨⟨base, len⟩, List.mem_cons_self, show _ ∧ _ from ⟨h1, h2⟩⟩

theorem size_mp : size 0x20000#64 656#64 = 0x21000#64 := by decide

/-- A byte of the launch's break pages is stored into. -/
theorem lw_brk {lo top : Nat} {L : List (Addr × List Byte)} {B a : Addr} (h1 : B.toNat ≤ a.toNat)
    (h2 : a.toNat < B.toNat + 8192) : Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) a :=
  foot_append_iff.2 (.inl (foot_one h1 h2))

/-- A byte of the launch's break pages is data. -/
theorem lf_brk {lo top : Nat} {L : List (Addr × List Byte)} {B a : Addr} (h1 : B.toNat ≤ a.toNat)
    (h2 : a.toNat < B.toNat + 8192) : Foot (withNew (zzsFoot lo top L) [⟨B, 8192⟩]).data a :=
  Gor.foot_wnN (foot_one h1 h2)

/-- A byte from the break `B + 4544` to the end of the first `MORECORE` is in the new pages or stored into. -/
theorem lw_heap {lo top : Nat} {L : List (Addr × List Byte)} {B a : Addr} (h1 : B.toNat + 4544 ≤ a.toNat)
    (h2 : a.toNat < B.toNat + 0x23000) (hB : B.toNat + 0x23000 < 2 ^ 64) :
    Foot (brkN B ++ ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)) a := by
  by_cases h : a.toNat < B.toNat + 8192
  · exact foot_append_iff.2 (.inr (lw_brk (by omega) h))
  · have t : (B + 8192#64).toNat = B.toNat + 8192 := by bv_omega
    exact foot_append_iff.2 (.inl (foot_one (by rw [t]; omega) (by rw [t]; omega)))

/-- `MCx` at the call of `__libc_init_first`, for the footprint `launch_to_ptr` hands on: the break `B + 4544`,
the thread pointer `B + 2176`, `mp_.top_pad = 0x20000`, `mp_.sbrk_base` and `mp_.max_sbrked_mem` 0, the new pages
`brkN B`. -/
theorem ent_mcx {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {lim : Nat} {ks : Kst}
    {lo top : Nat} {B : Addr} (hB : Base s₀ lim (B + 4544#64) (B + 2176#64) ks) (hC : MalCode L)
    (hal : B.toNat % 4096 = 0) (hbl : 0x7a9000 ≤ B.toNat) (hlim : B.toNat + 0x23000 ≤ 4096 * lim)
    (hmg : ∀ t p, o t (.memFail p) = none) :
    Gor.MCx prof (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (brkN B) L
      s₀ o lim (B + 4544#64) (B + 2176#64) ks 0x20000#64 0#64 0#64 := by
  have htop := hB.top
  have hB8 : B.toNat + 0x23000 < 2 ^ 47 := by omega
  have tb : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  have tf : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have tc : (corr (B + 4544#64)).toNat = 0 := by rw [corr_toNat, tb]; omega
  have tbc : (B + 4544#64 + corr (B + 4544#64)).toNat = B.toNat + 4544 := by bv_omega
  have ts : (B + 4544#64 + size 0x20000#64 656#64).toNat = B.toNat + 4544 + 0x21000 := by
    rw [size_mp]
    bv_omega
  have wv : ∀ {x n : Nat}, 0x777000 ≤ x → x + n ≤ 0x7a9000 →
      ∀ i < n, Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (Addr.add (BitVec.ofNat 64 x) i) :=
    fun h1 h2 => lw_varN h1 h2
  refine ⟨hB, hC.mal, hC.mhi, hC.pmi, hC.tgv, hC.tci, hC.imm, hC.smm, hC.dmc, hC.sbk, hC.brk,
    fun a h1 h2 => lw_var (by omega) (by omega), wv (x := 8013152) (by omega) (by omega),
    wv (x := 8014904) (by omega) (by omega), wv (x := 7944640) (by omega) (by omega),
    wv (x := 8013220) (by omega) (by omega), wv (x := 8013224) (by omega) (by omega),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    by omega, by omega, by decide, by decide, Nat.le_refl _, by decide, hmg, ?_, by omega, ?_,
    fun a h1 h2 => ?_, rfl, by omega, fun a h1 h2 => ?_⟩
  all_goals first
    | (apply lw_brk <;> simp only [Addr.add] <;> bv_omega)
    | (apply lf_brk <;> simp only [Addr.add] <;> bv_omega)
    | skip
  · rw [ts]
    unfold pageUp
    omega
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [ts, tb]
    have t : (B + 8192#64).toNat = B.toNat + 8192 := by bv_omega
    dsimp only [Rgn.In]
    rw [t]
    unfold pageUp
    omega
  · rw [tbc] at h1 h2
    exact lw_heap h1 (by omega) (by omega)
  · rw [tbc] at h1
    rw [ts] at h2
    exact lw_heap h1 (by omega) (by omega)

end FV7z.Start
