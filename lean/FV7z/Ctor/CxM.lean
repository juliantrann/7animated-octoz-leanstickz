import FV7z.Ctor.Mix
import FV7z.Mxi.Holds
import FV7z.Cxa.Holds
/-!
# Constructors that set up a mutex and register its destructor (PLAN.md §M, constructors)

`csuTg 100` (`0x41cd50`) and `csuTg 101` (`0x41ce30`) are `endbr64; sub rsp, 8; lea rdi, [rip + d]; call
CriticalSection_Init; mov rdi, 0x59a620; add rsp, 8; lea rdx, [rip + __dso_handle]; lea rsi, [rip + d]; jmp
__cxa_atexit`: `pthread_mutex_init (M, NULL)` (`Mxi.mx_ok`), then `__cxa_atexit (0x59a620, M, __dso_handle)`
(`Cxa.cxa_ok`), which returns to `__libc_csu_init`.

- `Jc_sh`, `jg_sh`: `Jg` from `m` to `m + 1` when the constructor also stores to the words `Sh` it shares with the
  others that call `__cxa_atexit` (the list's count, the lock and the counter of `__new_exitfn`), which lie in the
  spec of the first of them.
- `CxPre`: what `__cxa_atexit` needs of the bytes, kept by stores apart from the bytes it reads (`CxR`).
- `mc_runs`: such a constructor is a function as `Csu.csu_ok` asks.
- the bytes and blocks of `csuTg 100` and `csuTg 101`.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)

/-! ## Stores to shared words -/

/-- `Jc` from `m` to `m + 1` for a constructor that stores to `spec m`'s intervals, the stack's window, and the
words `Sh` inside the intervals of the constructor `k₀` before, whose `post` holds of any bytes, apart from the
other constructors' intervals. -/
theorem Jc_sh {V W W' : Addr → Byte} {sp m k₀ : Nat} {spec : Nat → CSpec} {Sh : List (Nat × Nat)} (hm : 3 ≤ m)
    (hc : calls m = []) (hS : 7991300 + 1024 ≤ sp) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hX : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ (spec m).wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ n, InR Sh n → InR (spec k₀).wr n) (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ n, InR (spec k).wr n → ¬ InR Sh n)
    (hJ : Jc V sp spec m W)
    (hW : ∀ a : Addr, ¬ InR (spec m).wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) →
      ¬ InR Sh a.toNat → W' a = W a)
    (hp : (spec m).post W') : Jc V sp spec (m + 1) W' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact hR.far_t fun a ha => hW a (fun hw => InR_sep hw (hT m) ha)
      (by have := InR_lt (b := 7991300) (by decide) ha; omega) (fun hs => InR_sep (hSh _ hs) (hT k₀) ha)
  · rw [hW a (h4 m hm (by omega)) h1 (fun hs => h4 k₀ hk₀ (by omega) (hSh _ hs))]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · by_cases hk0 : k = k₀
      · rw [hk0]
        exact hP₀ W'
      · exact hD k W W' (fun a ha => hW a (InR_sep ha (hX k hk hlt)) (by have := InR_lt (hB k) ha; omega)
          (hShD k hk hlt hk0 _ ha)) (hP k hk hlt)
    · obtain rfl : k = m := by omega
      exact hp

/-- `Jg` from `m` to `m + 1` for `spec m = wrSpec wr`, the constructor storing to `wr`, the stack's window and the
shared words `Sh` (`Jc_sh`). -/
theorem jg_sh {V W W' : Addr → Byte} {sp m k₀ : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {Sh wr : List (Nat × Nat)} (hm : 3 ≤ m) (hc : calls m = []) (hS : 7991300 + 1024 ≤ sp)
    (hspec : spec m = wrSpec wr) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ n, InR Sh n → InR (spec k₀).wr n) (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ n, InR (spec k).wr n → ¬ InR Sh n)
    (hout : ∀ a : Addr, ¬ InR wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → ¬ InR Sh a.toNat →
      W' a = W a)
    (hG : G m W → G (m + 1) W') (hJ : Jg V sp spec G m W) : Jg V sp spec G (m + 1) W' := by
  obtain ⟨hJc, hG'⟩ := hJ
  refine ⟨Jc_sh hm hc hS hD hT hB (fun k hk hkm => ?_) hk₀ hk₀m hSh hP₀ hShD hJc
    (fun a ha => hout a (by rw [hspec] at ha; exact ha)) ?_, hG hG'⟩
  · rw [hspec]
    exact hXw k hk hkm
  · rw [hspec]
    trivial

/-! ## What `__cxa_atexit` reads -/

/-- What `__cxa_atexit` needs of the bytes, for the list `l` with `n` places taken and the thread's block `fb`: one
thread, no exit function run, the list in `__exit_funcs`, the lock free, the count, no list after it when `n = 0`, the
last place taken not free again. -/
structure CxPre (fb l : Addr) (n : Nat) (V : Addr → Byte) : Prop where
  mt : rdd(V, fb + 24#64) = 0
  flag : rdb(V, 8010388#64) = 0
  ptr : rdq(V, 7938992#64) = l
  lock : rdd(V, 8029184#64) = 0
  idx : rdq(V, l + 8#64) = BitVec.ofNat 64 n
  next : n = 0 → rdq(V, l) = 0
  prev : 0 < n → rdq(V, l + BitVec.ofNat 64 (16 + 32 * n) - 32#64) ≠ 0

/-- The bytes `CxPre` reads: the thread's block, `__exit_funcs`, the flag, the lock with the counter, the list. -/
def CxR (fb l : Addr) (a : Nat) : Prop :=
  fb.toNat ≤ a ∧ a < fb.toNat + 56 ∨ 7938992 ≤ a ∧ a < 7939000 ∨ a = 8010388 ∨ 8029184 ≤ a ∧ a < 8029200 ∨
    l.toNat ≤ a ∧ a < l.toNat + 1040

theorem CxPre.kept {fb l : Addr} {n : Nat} {V V' : Addr → Byte} (h : CxPre fb l n V) (hn : n < 32)
    (hfn : fb.toNat + 56 ≤ 2 ^ 64) (hl : l.toNat + 1040 ≤ 2 ^ 64)
    (hk : ∀ a : Addr, CxR fb l a.toNat → V' a = V a) : CxPre fb l n V' := by
  obtain ⟨f24, -⟩ := Cxa.f_c fb hfn
  obtain ⟨t8, -, -, -, -, hpos⟩ := Nef.l_n l n hn hl
  refine ⟨?_, ?_, ?_, ?_, ?_, fun h0 => ?_, fun h0 => ?_⟩
  · exact (rdd_eq (x := fb + 24#64) (by rw [f24]; omega) fun a h1 h2 => hk a
      (by rw [f24] at h1 h2; unfold CxR; omega)).trans h.mt
  · exact (congrArg (ofBytesLE 8) (Csu.rd_in (lo := 8010388) (hi := 8010389) (x := 8010388#64) (n := 1)
      (fun a ha => hk a (by unfold CxR; omega)) (by decide) (by decide) (by decide))).trans h.flag
  · exact (rdq_eq (x := 7938992#64) (by decide) fun a h1 h2 => hk a (by
      simp only [show (7938992#64 : Addr).toNat = 7938992 from rfl] at h1 h2; unfold CxR; omega)).trans h.ptr
  · exact (rdd_eq (x := 8029184#64) (by decide) fun a h1 h2 => hk a (by
      simp only [show (8029184#64 : Addr).toNat = 8029184 from rfl] at h1 h2; unfold CxR; omega)).trans h.lock
  · exact (rdq_eq (x := l + 8#64) (by rw [t8]; omega) fun a h1 h2 => hk a
      (by rw [t8] at h1 h2; unfold CxR; omega)).trans h.idx
  · exact (rdq_eq (x := l) (by omega) fun a h1 h2 => hk a (by unfold CxR; omega)).trans (h.next h0)
  · have e := (hpos h0).2.2
    rw [rdq_eq (x := l + BitVec.ofNat 64 (16 + 32 * n) - 32#64) (by rw [e]; omega) fun a h1 h2 => hk a
      (by rw [e] at h1 h2; unfold CxR; omega)]
    exact h.prev h0

/-! ## The constructor's run -/

theorem e80 (sp : Addr) : sp - 64#64 - 8 - 8 = sp - 80#64 := by bv_omega
theorem e80n (sp : Addr) (h : 80 ≤ sp.toNat) : (sp - 80#64).toNat = sp.toNat - 80 := by bv_omega
theorem e136 (sp : Addr) : sp - 80#64 = sp - 136#64 + BitVec.ofNat 64 56 := by bv_omega
theorem e136' (sp : Addr) : sp - 80#64 - 56#64 = sp - 136#64 + BitVec.ofNat 64 0 := by bv_omega
theorem e120 (sp : Addr) : sp - 64#64 - 56#64 = sp - 136#64 + BitVec.ofNat 64 16 := by bv_omega
theorem e64 (sp : Addr) : sp - 80#64 + 8#64 + 8 = sp - 64#64 := by bv_omega
theorem f40 (fb : Addr) (h : fb.toNat + 56 ≤ 2 ^ 64) : (fb + 40#64).toNat = fb.toNat + 40 := by bv_omega

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- A constructor at offset `j` of `sti`, `endbr64; sub rsp, 8; lea rdi, M; call CriticalSection_Init; mov rdi, D;
add rsp, 8; lea rdx, __dso_handle; lea rsi, M; jmp __cxa_atexit`, the `m`-th function `__libc_csu_init` calls, is a
function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs (`hpre`), and `J (m + 1)` holds of the bytes after
`pthread_mutex_init`'s stores (below the frame and to `M`) and `__cxa_atexit`'s (`Cxa.Reg`, the list's place `n`). -/
theorem mc_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j r₁ r₂ M D n : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (htg : csuTg m = sti_at.add j) (hpro : BlkA prof sti sti_at j (j + 8) [Op.nop, Op.sub 64 4 (.i 8)])
    (hlea : BlkA prof sti sti_at (j + 8) (j + 15) [Op.mov 64 7 (.i M)])
    (hcd : Dec prof.feat sti (j + 15) (FV7z.mk .call 64 [.rel r₁] 5))
    (htc : sti_at.add (j + 15 + 5) + BitVec.ofNat 64 r₁ = Mxs.mxs_at)
    (htl : BlkA prof sti sti_at (j + 20) (j + 45)
      [Op.mov 64 7 (.i D), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i M)])
    (hjd : Dec prof.feat sti (j + 45) (FV7z.mk .jmp 64 [.rel r₂] 5))
    (htj : sti_at.add (j + 45 + 5) + BitVec.ofNat 64 r₂ = Cxa.cxa_at.add 0) (hj : j + 45 < sti.length)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hM0 : 0 < M) (hMg : 7939000 ≤ M ∧ M + 40 ≤ 8010388) (hMl : M + 40 ≤ l.toNat)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 M) i)) (hD0 : BitVec.ofNat 64 D ≠ 0)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat) (hfM : fb.toNat + 56 ≤ M ∨ M + 40 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : l ≠ 0) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat)
    (hpre : ∀ W, J m W → CxPre fb l n W)
    (hJ : ∀ W V₁ V', J m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → ¬ (M ≤ a.toNat ∧ a.toNat < M + 40) →
        V₁ a = W a) →
      Cxa.Reg V₁ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 D ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 M) 7938344#64 →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs8 := hC.s8
  have hsl := sp.isLt
  have n64 := Csu.sp_n hC.s0
  have n80 := e80n sp (by omega)
  have eM : (BitVec.ofNat 64 M).toNat = M := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e40 := f40 fb hfn
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  -- `endbr64; sub rsp, 8`
  refine pro hpro c hin hK hA (hr.trans htg) fun Y t₀ hKY hAY hrY hsY hcY => ?_
  rw [hsp] at hsY
  -- `lea rdi, M`
  refine (Sp.blkA hlea).run c hin (fun j' g' _ V' => j' = j + 15 ∧ g' = wr Y.cpu.gpr 7 (BitVec.ofNat 64 M) ∧
    V = V') hKY hAY hrY ?_ ?_
  · intro fl _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y' t₁ hKY' hAY' hrY' hgY' -
  have hsY' : Y'.cpu.gpr.rsp = sp - 64#64 - 8 := by rw [hgY']; exact hsY
  -- `call CriticalSection_Init`
  refine c.s_call hKY' hAY' hin (by omega) hrY' hcd hinM (Mxs.lt_len (j := 0) (by decide)) htc
    (by rw [hsY', e80]; exact off_ft hst 56 (e136 sp) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY', e80] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = sp - 80#64 := by rw [hg₂]; show Y'.cpu.gpr.rsp - 8 = _; rw [hsY', e80]
  have hdi₂ : Y₂.cpu.gpr.rdi = BitVec.ofNat 64 M := by rw [hg₂, hgY']; exact sw_64_64 _
  have hc₂ : Cs Y.cpu.gpr Y₂.cpu.gpr := by rw [hg₂, hgY']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hV₀ : ∀ a : Addr, ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 72) →
      Vst V (sp - 80#64) (toBytesLE (sti_at.add (j + 15 + 5)) 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n80]; omega) (by rw [n80]; omega)
  -- `pthread_mutex_init (M, NULL)`
  refine Mxi.mx_ok c hfs hinM hinI hK₂ hA₂ hr₂ (fun h => by
      have := congrArg BitVec.toNat (hdi₂.symm.trans h)
      rw [eM] at this
      simp at this
      omega)
    (by rw [hsp₂, n80]; omega) (by rw [hsp₂, n80]; omega) (by rw [hsp₂]; exact off_ft hst 0 (e136' sp) (by omega))
    (by rw [hsp₂]; exact fun i hi => c.hws _ (off_ft hst 56 (e136 sp) (by omega) i hi))
    (off_ft hft 40 rfl (by decide)) (by rw [e40]; omega) (by rw [hsp₂, n80, e40]; omega)
    (by rw [hdi₂, eM, e40]; omega) (by rw [hdi₂]; exact hmw) (by rw [hdi₂, eM]; omega)
    (by rw [hdi₂, eM, hsp₂, n80]; omega) (j₂ := j + 15 + 5) hin (by omega)
    (by rw [hsp₂, Sga.vs (a := sp - 80#64) (n := 8) (toBytesLE_length _ _) (by rw [n80]; omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro V₁ Z₁ t₃ hKZ hAZ hout hrZ hB
  rw [hsp₂, hdi₂, n80, eM] at hout
  have hmo : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (M ≤ a.toNat ∧ a.toNat < M + 40) → V₁ a = V a := fun a h1 h2 =>
    (hout a (by omega) h2).trans (hV₀ a (by omega))
  have hX : CxPre fb l n V₁ := (hpre V hI).kept hn hfn (by omega) fun a ha => hmo a
    (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)
  have hsZ : Z₁.cpu.gpr.rsp = sp - 80#64 + 8#64 := by rw [hB.1, hsp₂]
  have hcZ : Cs Y₂.cpu.gpr Z₁.cpu.gpr := hB.2
  -- `mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M`
  have e20 : j + 15 + 5 = j + 20 := by omega
  rw [e20] at hrZ
  refine (Sp.blkA htl).run c hin (fun j' g' _ V' => j' = j + 45 ∧
    g' = wr (wr (wr (wr Z₁.cpu.gpr 7 (BitVec.ofNat 64 D)) 4
      (addR (gv (wr Z₁.cpu.gpr 7 (BitVec.ofNat 64 D)) 64 4) (BitVec.ofNat 64 8))) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 M) ∧ V₁ = V') hKZ hAZ hrZ ?_ ?_
  · intro _ _ _ _ _ _ _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  have hsp₃ : Y₃.cpu.gpr.rsp = sp - 64#64 := by
    rw [← e64 sp, ← hsZ, hg₃]
    exact rsp_add8 _
  have hdi₃ : Y₃.cpu.gpr.rdi = BitVec.ofNat 64 D := by rw [hg₃]; exact sw_64_64 _
  have hsi₃ : Y₃.cpu.gpr.rsi = BitVec.ofNat 64 M := by rw [hg₃]; exact sw_64_64 _
  have hdx₃ : Y₃.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₃]; exact sw_64_64 _
  have hc₃ : Cs Z₁.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `jmp __cxa_atexit`
  refine c.s_jmp_x hK₃ hA₃ hin hj hr₃ hjd hinC (Cxa.lt_len (j := 0) (by decide)) htj ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  refine Cxa.cxa_ok (sp := sp - 64#64) (l := l) (p := l + BitVec.ofNat 64 (16 + 32 * n)) (n := n)
    (fn := BitVec.ofNat 64 D) (arg := BitVec.ofNat 64 M) (dso := 7938344#64) c hfs hinC hinN hK₄ hA₄
    (by rw [hr₄, addr_add_zero]) (by rw [hg₄]; exact hsp₃) (by rw [hg₄]; exact hdi₃) (by rw [hg₄]; exact hsi₃)
    (by rw [hg₄]; exact hdx₃) (off_ft hst 16 (e120 sp) (by omega)) (fun i hi => c.hws _ (hC.st i (by omega)))
    hC.code hj₂ ?_ (by rw [n64]; omega) hD0 hft hfn (by rw [n64]; omega) hfld hfcd hX.mt hfl hX.flag hp hX.ptr hl0
    hn rfl hlw (by rw [n64]; omega) hkw (by rw [n64]; omega) hlc hX.lock hX.idx hX.next hX.prev ?_
  · exact (rdq_eq (V := V) (x := sp - 64#64) (by rw [n64]; omega) fun a h1 h2 => hmo a
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)).trans hra
  intro V' g' Z t' hKZ' hAZ' hR hrZ' hgZ _ hBk
  have hcs : Cs X.cpu.gpr Z.cpu.gpr := Cs.trans hcY (Cs.trans hc₂ (Cs.trans hcZ (Cs.trans hc₃
    (by rw [hgZ]; rw [hg₄] at hBk; exact hBk.2))))
  refine k Z t' V' hKZ' hAZ' (hJ V V₁ V' hI hmo hR) (fun a ha => ?_) (fun a ha => ?_) hrZ' ⟨?_, hcs⟩
  · rw [hR.out a (by rw [n64]; omega) (by omega) (by rw [ep]; omega) (by omega)]
    exact hmo a (by omega) (by omega)
  · rw [hR.out a (by rw [n64]; omega) (by omega) (by rw [ep]; omega) (by omega)]
    exact hmo a (by omega) (by omega)
  · rw [hgZ, hBk.1, hg₄, hsp₃, hsp]

/-- The words the constructors that call `__cxa_atexit` share: the list's count, the lock and `__new_exitfn`'s
counter. -/
def cxSh (l : Addr) : List (Nat × Nat) := [(l.toNat + 8, l.toNat + 16), (8029184, 8029200)]

/-- The intervals of such a constructor: its mutex and the list's place `n`. -/
def mcWr (l : Addr) (M n : Nat) : List (Nat × Nat) := [(M, M + 40), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 32)]

/-- `mc_runs` for `Jg`, the spec `wrSpec (mcWr l M n)`, the shared words `cxSh l` in the spec of `k₀`: `G m` gives
what `__cxa_atexit` needs, and `G` goes from `m` to `m + 1` by the stores (`hG`). -/
theorem mc_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m j r₁ r₂ M D n k₀ : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (htg : csuTg m = sti_at.add j) (hpro : BlkA prof sti sti_at j (j + 8) [Op.nop, Op.sub 64 4 (.i 8)])
    (hlea : BlkA prof sti sti_at (j + 8) (j + 15) [Op.mov 64 7 (.i M)])
    (hcd : Dec prof.feat sti (j + 15) (FV7z.mk .call 64 [.rel r₁] 5))
    (htc : sti_at.add (j + 15 + 5) + BitVec.ofNat 64 r₁ = Mxs.mxs_at)
    (htl : BlkA prof sti sti_at (j + 20) (j + 45)
      [Op.mov 64 7 (.i D), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i M)])
    (hjd : Dec prof.feat sti (j + 45) (FV7z.mk .jmp 64 [.rel r₂] 5))
    (htj : sti_at.add (j + 45 + 5) + BitVec.ofNat 64 r₂ = Cxa.cxa_at.add 0) (hj : j + 45 < sti.length)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hM0 : 0 < M) (hMg : 7939000 ≤ M ∧ M + 40 ≤ 8010388) (hMl : M + 40 ≤ l.toNat)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 M) i)) (hD0 : BitVec.ofNat 64 D ≠ 0)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat) (hfM : fb.toNat + 56 ≤ M ∨ M + 40 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : l ≠ 0) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat)
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (mcWr l M n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ mcWr l M n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (cxSh l) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (cxSh l) x)
    (hGx : ∀ W, G m W → CxPre fb l n W)
    (hG : ∀ W V₁ V', G m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → ¬ (M ≤ a.toNat ∧ a.toNat < M + 40) →
        V₁ a = W a) →
      Cxa.Reg V₁ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 D ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 M) 7938344#64 →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n64 := Csu.sp_n hC.s0
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  refine mc_runs c hC hin hfs hinM hinI hinC hinN htg hpro hlea hcd htc htl hjd htj hj hst hS hM0 hMg hMl hmw hD0
    hft hfn hfsd hfM hfld hfcd hfl hp hl0 hn hlw hld hkw hlc (fun W hJ => hGx W hJ.2)
    fun W V₁ V' hJ hmo hR => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m hSh hP₀ hShD
      (fun a h1 h2 h3 => ?_) (hG W V₁ V' · hmo hR) hJ
  rw [hR.out a (by rw [n64]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
    (fun h => h1 (by rw [ep] at h; simp only [mcWr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega))]
  exact hmo a (by omega) fun h => h1 (by simp only [mcWr, InR]; omega)

/-- `csuTg 100`, at `0x41cd50`: the mutex `0x79f0a0`. -/
def c3088 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0x41, 0x23, 0x38, 0x00, 0xe8,
  0xdc, 0xbd, 0x02, 0x00, 0x48, 0xc7, 0xc7, 0x20, 0xa6, 0x59, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x48,
  0x8d, 0x15, 0xb2, 0x53, 0x37, 0x00, 0x48, 0x8d, 0x35, 0x23, 0x23, 0x38, 0x00, 0xe9, 0x0e, 0x69,
  0x20, 0x00]
theorem c3088_0 : ∀ feat, Dec feat c3088 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c3088_4 : ∀ feat, Dec feat c3088 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3088_8 : ∀ feat, Dec feat c3088 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3679041 0)] 7) := by dec_rfl
theorem c3088_15 : ∀ feat, Dec feat c3088 15 (FV7z.mk .call 64 [.rel 179676] 5) := by dec_rfl
theorem c3088_20 : ∀ feat, Dec feat c3088 20 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c3088_27 : ∀ feat, Dec feat c3088 27 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3088_31 : ∀ feat, Dec feat c3088 31 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3625906 0)] 7) := by dec_rfl
theorem c3088_38 : ∀ feat, Dec feat c3088 38 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3679011 0)] 7) := by dec_rfl
theorem c3088_45 : ∀ feat, Dec feat c3088 45 (FV7z.mk .jmp 64 [.rel 2124046] 5) := by dec_rfl
theorem v3088 : c3088 <+: sti.drop 3088 := by decide +kernel
theorem tg100 : csuTg 100 = sti_at.add 3088 := by decide +kernel
theorem pq3088 (prof : Profile) : BlkA prof c3088 (0x41cd50 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c3088_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c3088_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb3088 (prof : Profile) : BlkA prof sti sti_at 3088 3096 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq3088 prof).shift (by decide) v3088
theorem lq3088 (prof : Profile) : BlkA prof c3088 (0x41cd50 : Addr) 8 15 [Op.mov 64 7 (.i 7991456)] :=
  .cons (c3088_8 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 15
theorem lb3088 (prof : Profile) : BlkA prof sti sti_at 3096 3103 [Op.mov 64 7 (.i 7991456)] :=
  (lq3088 prof).shift (by decide) v3088
theorem cd3088 (feat : Features) : Dec feat sti 3103 (FV7z.mk .call 64 [.rel 179676] 5) :=
  Dec.shift (j := 3088) (k := 15) (c3088_15 feat) v3088 (by decide)
theorem tq3088 (prof : Profile) : BlkA prof c3088 (0x41cd50 : Addr) 20 45
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991456)] :=
  .cons (c3088_20 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c3088_27 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (c3088_31 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c3088_38 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 45
theorem tb3088 (prof : Profile) : BlkA prof sti sti_at 3108 3133
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991456)] :=
  (tq3088 prof).shift (by decide) v3088
theorem jd3088 (feat : Features) : Dec feat sti 3133 (FV7z.mk .jmp 64 [.rel 2124046] 5) :=
  Dec.shift (j := 3088) (k := 45) (c3088_45 feat) v3088 (by decide)

/-- `csuTg 101`, at `0x41ce30`: the mutex `0x79f0e0`. -/
def c3312 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0xa1, 0x22, 0x38, 0x00, 0xe8,
  0xfc, 0xbc, 0x02, 0x00, 0x48, 0xc7, 0xc7, 0x20, 0xa6, 0x59, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x48,
  0x8d, 0x15, 0xd2, 0x52, 0x37, 0x00, 0x48, 0x8d, 0x35, 0x83, 0x22, 0x38, 0x00, 0xe9, 0x2e, 0x68,
  0x20, 0x00]
theorem c3312_0 : ∀ feat, Dec feat c3312 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c3312_4 : ∀ feat, Dec feat c3312 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3312_8 : ∀ feat, Dec feat c3312 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678881 0)] 7) := by dec_rfl
theorem c3312_15 : ∀ feat, Dec feat c3312 15 (FV7z.mk .call 64 [.rel 179452] 5) := by dec_rfl
theorem c3312_20 : ∀ feat, Dec feat c3312 20 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c3312_27 : ∀ feat, Dec feat c3312 27 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3312_31 : ∀ feat, Dec feat c3312 31 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3625682 0)] 7) := by dec_rfl
theorem c3312_38 : ∀ feat, Dec feat c3312 38 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678851 0)] 7) := by dec_rfl
theorem c3312_45 : ∀ feat, Dec feat c3312 45 (FV7z.mk .jmp 64 [.rel 2123822] 5) := by dec_rfl
theorem v3312 : c3312 <+: sti.drop 3312 := by decide +kernel
theorem tg101 : csuTg 101 = sti_at.add 3312 := by decide +kernel
theorem pq3312 (prof : Profile) : BlkA prof c3312 (0x41ce30 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c3312_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c3312_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb3312 (prof : Profile) : BlkA prof sti sti_at 3312 3320 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq3312 prof).shift (by decide) v3312
theorem lq3312 (prof : Profile) : BlkA prof c3312 (0x41ce30 : Addr) 8 15 [Op.mov 64 7 (.i 7991520)] :=
  .cons (c3312_8 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 15
theorem lb3312 (prof : Profile) : BlkA prof sti sti_at 3320 3327 [Op.mov 64 7 (.i 7991520)] :=
  (lq3312 prof).shift (by decide) v3312
theorem cd3312 (feat : Features) : Dec feat sti 3327 (FV7z.mk .call 64 [.rel 179452] 5) :=
  Dec.shift (j := 3312) (k := 15) (c3312_15 feat) v3312 (by decide)
theorem tq3312 (prof : Profile) : BlkA prof c3312 (0x41ce30 : Addr) 20 45
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991520)] :=
  .cons (c3312_20 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c3312_27 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (c3312_31 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c3312_38 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 45
theorem tb3312 (prof : Profile) : BlkA prof sti sti_at 3332 3357
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991520)] :=
  (tq3312 prof).shift (by decide) v3312
theorem jd3312 (feat : Features) : Dec feat sti 3357 (FV7z.mk .jmp 64 [.rel 2123822] 5) :=
  Dec.shift (j := 3312) (k := 45) (c3312_45 feat) v3312 (by decide)


end FV7z.Ctor
