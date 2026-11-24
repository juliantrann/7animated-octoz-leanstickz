import FV7z.Oin
/-!
# Constructor 95: an object's constructor, `__cxa_atexit`, then a mutex (PLAN.md §M, constructors)

`csuTg 95` (`0x41cbd0`): `endbr64; sub rsp, 8; lea rdi, O; call 0x59ea30; mov rdi, 0x59eac0; lea rdx,
__dso_handle; lea rsi, O; call __cxa_atexit`, then the tail of `mc_tail` for the mutex `M = 0x79eca0`, with the object
`O = 0x79ece0` (the function at `0x59ea30`: `Oin.oin_ok`).

- `oi_mid`: `call 0x59ea30` inside a constructor, with `rdi = O`.
- `c95_runs`, `c95_jg`: `csuTg 95` as `Csu.csu_ok` asks, and for `Jg` (its spec `wrSpec (c95Wr l n)`, the shared
  words in the spec of `k₀`, as `c94_jg`).
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The call of `0x59ea30` -/

/-- `call 0x59ea30` at offset `q` of `sti` with `rdi = O` and the stack pointer `R`: back at `q + 5` with `rsp = R`,
the registers a call keeps, the bytes apart from the 64 below `R` and the 40 from `O + 0x48` as before. -/
theorem oi_mid {R : Addr} {q r : Nat} {X : State} {t : Nat} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L sti_at sti) (hinO : CodeIn L Oin.oin_at Oin.oin) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add q)
    (hcd : Dec prof.feat sti q (FV7z.mk .call 64 [.rel r] 5))
    (htc : sti_at.add (q + 5) + BitVec.ofNat 64 r = Oin.oin_at) (hq : q + 5 < sti.length)
    (hsp : X.cpu.gpr.rsp = R) (hdi : X.cpu.gpr.rdi = 7990496#64) (hR : 7990608 + 64 ≤ R.toNat)
    (hst : ∀ i < 64, Foot Wl (Addr.add (R - 64#64) i)) (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i))
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (R.toNat - 64 ≤ a.toNat ∧ a.toNat < R.toNat) → ¬ (7990568 ≤ a.toNat ∧ a.toNat < 7990608) →
        V' a = V a) →
      Z.cpu.rip = sti_at.add (q + 5) → Z.cpu.gpr.rsp = R → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := R.isLt
  have n8 := m8n R (by omega)
  refine c.s_call hK hA hin (by omega) hrip hcd hinO (Oin.lt_len (j := 0) (by decide)) htc
    (by rw [hsp]; exact off_ft hst 56 (m8s R) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = R - 8 := by rw [hg₂]; show X.cpu.gpr.rsp - 8 = _; rw [hsp]
  have hdi₂ : Y₂.cpu.gpr.rdi = 7990496#64 := by rw [hg₂]; exact hdi
  have hc₂ : Cs X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hV₀ : ∀ a : Addr, ¬ (R.toNat - 8 ≤ a.toNat ∧ a.toNat < R.toNat) →
      Vst V (R - 8) (toBytesLE (sti_at.add (q + 5)) 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n8]; omega) (by rw [n8]; omega)
  refine Oin.oin_ok c hinO hK₂ hA₂ hr₂ hdi₂ hw
    (by rw [hsp₂]; exact fun i hi => c.hws _ (off_ft hst 56 (m8s R) (by omega) i hi))
    (by rw [hsp₂, n8]; omega) (by rw [hsp₂, n8]; omega) (j₂ := q + 5) hin hq
    (by rw [hsp₂, Sga.vs (a := R - 8) (n := 8) (toBytesLE_length _ _) (by rw [n8]; omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro V₁ Z₁ t₃ hKZ hAZ hout hrZ hB
  exact k V₁ Z₁ t₃ hKZ hAZ (fun a h1 h2 => (hout a (by omega)).trans (hV₀ a (by omega))) hrZ
    (by rw [hB.1, hsp₂, m8b]) (Cs.trans hc₂ hB.2)

/-! ## `csuTg 95` -/

/-- `csuTg 95`, at `0x41cbd0`: the object `0x79ece0` and the mutex `0x79eca0`. -/
def c2704 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0x01, 0x21, 0x38, 0x00, 0xe8,
  0x4c, 0x1e, 0x18, 0x00, 0x48, 0xc7, 0xc7, 0xc0, 0xea, 0x59, 0x00, 0x48, 0x8d, 0x15, 0x36, 0x55,
  0x37, 0x00, 0x48, 0x8d, 0x35, 0xe7, 0x20, 0x38, 0x00, 0xe8, 0x92, 0x6a, 0x20, 0x00, 0x48, 0x8d,
  0x3d, 0x9b, 0x20, 0x38, 0x00, 0xe8, 0x36, 0xbf, 0x02, 0x00, 0x48, 0xc7, 0xc7, 0x20, 0xa6, 0x59,
  0x00, 0x48, 0x83, 0xc4, 0x08, 0x48, 0x8d, 0x15, 0x0c, 0x55, 0x37, 0x00, 0x48, 0x8d, 0x35, 0x7d,
  0x20, 0x38, 0x00, 0xe9, 0x68, 0x6a, 0x20, 0x00]
theorem c2704_0 : ∀ feat, Dec feat c2704 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c2704_4 : ∀ feat, Dec feat c2704 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2704_8 : ∀ feat, Dec feat c2704 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678465 0)] 7) := by dec_rfl
theorem c2704_15 : ∀ feat, Dec feat c2704 15 (FV7z.mk .call 64 [.rel 1580620] 5) := by dec_rfl
theorem c2704_20 : ∀ feat, Dec feat c2704 20 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5892800)] 7) := by dec_rfl
theorem c2704_27 : ∀ feat, Dec feat c2704 27 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626294 0)] 7) := by dec_rfl
theorem c2704_34 : ∀ feat, Dec feat c2704 34 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678439 0)] 7) := by dec_rfl
theorem c2704_41 : ∀ feat, Dec feat c2704 41 (FV7z.mk .call 64 [.rel 2124434] 5) := by dec_rfl
theorem c2704_46 : ∀ feat, Dec feat c2704 46 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678363 0)] 7) := by dec_rfl
theorem c2704_53 : ∀ feat, Dec feat c2704 53 (FV7z.mk .call 64 [.rel 180022] 5) := by dec_rfl
theorem c2704_58 : ∀ feat, Dec feat c2704 58 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c2704_65 : ∀ feat, Dec feat c2704 65 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2704_69 : ∀ feat, Dec feat c2704 69 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626252 0)] 7) := by dec_rfl
theorem c2704_76 : ∀ feat, Dec feat c2704 76 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678333 0)] 7) := by dec_rfl
theorem c2704_83 : ∀ feat, Dec feat c2704 83 (FV7z.mk .jmp 64 [.rel 2124392] 5) := by dec_rfl
theorem v2704 : c2704 <+: sti.drop 2704 := by decide +kernel
theorem tg95 : csuTg 95 = sti_at.add 2704 := by decide +kernel

theorem pq2704 (prof : Profile) : BlkA prof c2704 (0x41cbd0 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c2704_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c2704_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb2704 (prof : Profile) : BlkA prof sti sti_at 2704 2712 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq2704 prof).shift (by decide) v2704
theorem lq2704 (prof : Profile) : BlkA prof c2704 (0x41cbd0 : Addr) 8 15 [Op.mov 64 7 (.i 7990496)] :=
  .cons (c2704_8 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 15
theorem lb2704 (prof : Profile) : BlkA prof sti sti_at 2712 2719 [Op.mov 64 7 (.i 7990496)] :=
  (lq2704 prof).shift (by decide) v2704
theorem cd2719 (feat : Features) : Dec feat sti 2719 (FV7z.mk .call 64 [.rel 1580620] 5) :=
  Dec.shift (j := 2704) (k := 15) (c2704_15 feat) v2704 (by decide)
theorem bq2724 (prof : Profile) : BlkA prof c2704 (0x41cbd0 : Addr) 20 41
    [Op.mov 64 7 (.i 5892800), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990496)] :=
  .cons (c2704_20 _) ((OpI.mov (.i 5892800) (.inr rfl)).at _) (by decide) <|
  .cons (c2704_27 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2704_34 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 41
theorem b2724 (prof : Profile) : BlkA prof sti sti_at 2724 2745
    [Op.mov 64 7 (.i 5892800), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990496)] :=
  (bq2724 prof).shift (by decide) v2704
theorem cd2745 (feat : Features) : Dec feat sti 2745 (FV7z.mk .call 64 [.rel 2124434] 5) :=
  Dec.shift (j := 2704) (k := 41) (c2704_41 feat) v2704 (by decide)
theorem lq2750 (prof : Profile) : BlkA prof c2704 (0x41cbd0 : Addr) 46 53 [Op.mov 64 7 (.i 7990432)] :=
  .cons (c2704_46 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 53
theorem lb2750 (prof : Profile) : BlkA prof sti sti_at 2750 2757 [Op.mov 64 7 (.i 7990432)] :=
  (lq2750 prof).shift (by decide) v2704
theorem cd2757 (feat : Features) : Dec feat sti 2757 (FV7z.mk .call 64 [.rel 180022] 5) :=
  Dec.shift (j := 2704) (k := 53) (c2704_53 feat) v2704 (by decide)
theorem tq2762 (prof : Profile) : BlkA prof c2704 (0x41cbd0 : Addr) 58 83
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990432)] :=
  .cons (c2704_58 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c2704_65 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (c2704_69 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2704_76 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 83
theorem tb2762 (prof : Profile) : BlkA prof sti sti_at 2762 2787
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990432)] :=
  (tq2762 prof).shift (by decide) v2704
theorem jd2787 (feat : Features) : Dec feat sti 2787 (FV7z.mk .jmp 64 [.rel 2124392] 5) :=
  Dec.shift (j := 2704) (k := 83) (c2704_83 feat) v2704 (by decide)
theorem tc2719 : sti_at.add (2719 + 5) + BitVec.ofNat 64 1580620 = Oin.oin_at := by decide +kernel
theorem tc2745 : sti_at.add (2745 + 5) + BitVec.ofNat 64 2124434 = Cxa.cxa_at := by decide +kernel
theorem tc2757 : sti_at.add (2742 + 15 + 5) + BitVec.ofNat 64 180022 = Mxs.mxs_at := by decide +kernel
theorem tj2787 : sti_at.add (2742 + 45 + 5) + BitVec.ofNat 64 2124392 = Cxa.cxa_at.add 0 := by decide +kernel

/-- `csuTg 95` is a function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs (`hpre`), and `J (m + 1)`
holds of the bytes after the object's constructor (`V₁`, below the frame and in the 40 from `O + 0x48`),
`__cxa_atexit`'s stores for it (place `n`), the mutex's set-up (`V₃`) and `__cxa_atexit`'s stores for it
(place `n + 1`). -/
theorem c95_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m n : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (hinO : CodeIn L Oin.oin_at Oin.oin) (htg : csuTg m = sti_at.add 2704)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfO : fb.toNat + 56 ≤ 7990432 ∨ 7990608 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990432) i))
    (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i))
    (hpre : ∀ W, J m W → CxPre fb l n W)
    (hJ : ∀ W V₁ V₂ V₃ V', J m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990568 ≤ a.toNat ∧ a.toNat < 7990608) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5892800 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990496) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990432 ≤ a.toNat ∧ a.toNat < 7990472) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990432) 7938344#64 →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs8 := hC.s8
  have hsl := sp.isLt
  have n64 := Csu.sp_n hC.s0
  have n72 := e72n sp (by omega)
  have n80 := e80n sp (by omega)
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) (by omega)
  obtain ⟨-, -, ep', -, -, -⟩ := Nef.l_n l (n + 1) hn (by omega)
  have hl0' : l ≠ 0 := by rintro rfl; simp at hl0
  -- `endbr64; sub rsp, 8`
  refine pro (pb2704 prof) c hin hK hA (hr.trans htg) fun Y₀ t₀ hK₀ hA₀ hr₀ hs₀ hc₀ => ?_
  rw [hsp, e72] at hs₀
  -- `lea rdi, O`
  refine (Sp.blkA (lb2704 prof)).run c hin (fun j' g' _ V' => j' = 2719 ∧
    g' = wr Y₀.cpu.gpr 7 (BitVec.ofNat 64 7990496) ∧ V = V') hK₀ hA₀ hr₀ ?_ ?_
  · intro _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = sp - 72#64 := by rw [hg₁]; exact hs₀
  have hd₁ : Y₁.cpu.gpr.rdi = 7990496#64 := by rw [hg₁]; exact sw_64_64 _
  have hc₁ : Cs Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `call 0x59ea30`
  refine oi_mid (R := sp - 72#64) c hin hinO hK₁ hA₁ hr₁ (cd2719 _) tc2719 (sti_lt (by decide)) hs₁ hd₁
    (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) hw ?_
  intro V₀ Y₂ t₂ hK₂ hA₂ ho₀ hr₂ hs₂ hc₂
  rw [n72] at ho₀
  -- `mov rdi, 0x59eac0; lea rdx, __dso_handle; lea rsi, O`
  refine (Sp.blkA (b2724 prof)).run c hin (fun j' g' _ V' => j' = 2745 ∧
    g' = wr (wr (wr Y₂.cpu.gpr 7 (BitVec.ofNat 64 5892800)) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 7990496) ∧ V₀ = V') hK₂ hA₂ hr₂ ?_ ?_
  · intro _ _ _ _ _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hs₃ : Y₃.cpu.gpr.rsp = sp - 72#64 := by rw [hg₃]; exact hs₂
  have hd₃ : Y₃.cpu.gpr.rdi = BitVec.ofNat 64 5892800 := by rw [hg₃]; exact sw_64_64 _
  have hx₃ : Y₃.cpu.gpr.rsi = BitVec.ofNat 64 7990496 := by rw [hg₃]; exact sw_64_64 _
  have hdx₃ : Y₃.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₃]; exact sw_64_64 _
  have hc₃ : Cs Y₂.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hX₀ : CxPre fb l n V₀ := (hpre V hI).kept (by omega) hfn (by omega) fun a ha =>
    ho₀ a (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)
  -- `call __cxa_atexit (0x59eac0, O, __dso_handle)`
  refine cx_mid (R := sp - 72#64) c hin hfs hinC hinN hK₃ hA₃ hr₃ (cd2745 _) tc2745 (sti_lt (by decide)) hs₃ hd₃
    hx₃ hdx₃ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) hX₀ hft hfn
    (by rw [n72]; omega) hfld hfcd hfl hp hl0' (by omega) hlw (by rw [n72]; omega) hkw (by rw [n72]; omega)
    (by omega) ?_
  intro V₁ V₂ Y₄ t₄ hK₄ hA₄ hv₁ hR₁ hr₄ hs₄ hc₄
  rw [n72] at hv₁
  rw [e72b] at hR₁
  have hX₂ : CxPre fb l (n + 1) V₂ := (hX₀.kept (by omega) hfn (by omega) fun a ha =>
    hv₁ a (by unfold CxR at ha; omega)).reg hR₁ hn hfn (by omega) (by rw [n80]; omega) (by rw [n80]; omega) hfld
    hfcd (by rw [n80]; omega) (by rw [n80]; omega) (by omega)
  have hkp : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990568 ≤ a.toNat ∧ a.toNat < 7990608) → ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) →
      ¬ (l.toNat + 16 + 32 * n ≤ a.toNat ∧ a.toNat < l.toNat + 48 + 32 * n) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₂ a = V a := fun a h1 h2 h3 h4 h5 => by
    rw [hR₁.out a (by rw [n80]; omega) h3 (by rw [ep]; omega) h5, hv₁ a (by omega)]
    exact ho₀ a (by omega) h2
  -- the tail: `lea rdi, M; call CriticalSection_Init; mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M;
  -- jmp __cxa_atexit`
  refine mc_tail (j := 2742) (M := 7990432) (D := 5875232) c hin hfs hinM hinI hinC hinN hK₄ hA₄ hr₄
    (hs₄.trans (e72 sp).symm) (lb2750 prof) (cd2757 _) tc2757 (tb2762 prof) (jd2787 _) tj2787 (sti_lt (by decide))
    hst (fun i hi => c.hws _ (hC.st i (by omega))) hC.s0 hC.s8 hS (by decide) (by decide) (by omega) hmw
    (by decide) hft hfn (by omega) (by omega) hfld hfcd hfl hp hl0' hn hlw hld hkw (.inl hlc) hX₂ hC.code hj₂
    ((rdq_eq (V := V) (x := sp - 64#64) (by rw [n64]; omega) fun a h1 h2 => hkp a
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)).trans hra) ?_
  intro V₃ V' Z t' hKZ hAZ hmo hR₂ hrZ hsZ hcs
  refine k Z t' V' hKZ hAZ (hJ V V₁ V₂ V₃ V' hI (fun a h1 h2 => (hv₁ a (by omega)).trans (ho₀ a (by omega) h2))
    hR₁ (fun a h1 h2 => hmo a h1 (by omega)) hR₂) (fun a ha => ?_) (fun a ha => ?_) hrZ
    ⟨by rw [hsZ, hsp], Cs.trans hc₀ (Cs.trans hc₁ (Cs.trans hc₂ (Cs.trans hc₃ (Cs.trans hc₄ hcs))))⟩
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega), hmo a (by omega) (by omega)]
    exact hkp a (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega), hmo a (by omega) (by omega)]
    exact hkp a (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The intervals of `csuTg 95`: the mutex, the 40 bytes of the object it stores and the list's places `n`,
`n + 1`. -/
def c95Wr (l : Addr) (n : Nat) : List (Nat × Nat) :=
  [(7990432, 7990472), (7990568, 7990608), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 64)]

/-- `c95_runs` for `Jg`, the spec `wrSpec (c95Wr l n)`, the shared words `cxSh l` in the spec of `k₀`. -/
theorem c95_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m n k₀ : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (hinO : CodeIn L Oin.oin_at Oin.oin) (htg : csuTg m = sti_at.add 2704)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfO : fb.toNat + 56 ≤ 7990432 ∨ 7990608 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990432) i))
    (hw : ∀ i < 40, Foot Wl (Addr.add 7990568#64 i))
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (c95Wr l n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c95Wr l n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (cxSh l) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (cxSh l) x)
    (hGx : ∀ W, G m W → CxPre fb l n W)
    (hG : ∀ W V₁ V₂ V₃ V', G m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990568 ≤ a.toNat ∧ a.toNat < 7990608) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5892800 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990496) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990432 ≤ a.toNat ∧ a.toNat < 7990472) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990432) 7938344#64 →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n64 := Csu.sp_n hC.s0
  have n80 := e80n sp (by omega)
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) (by omega)
  obtain ⟨-, -, ep', -, -, -⟩ := Nef.l_n l (n + 1) hn (by omega)
  refine c95_runs c hC hin hfs hinM hinI hinC hinN hinO htg hst hS hft hfn hfsd hfO hfld hfcd hfl hp hl0 hn hlw
    hld hkw hlc hmw hw (fun W hJ => hGx W hJ.2)
    fun W V₁ V₂ V₃ V' hJ hv hR₁ hmo hR₂ => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m hSh hP₀ hShD
      (fun a h1 h2 h3 => ?_) (hG W V₁ V₂ V₃ V' · hv hR₁ hmo hR₂) hJ
  rw [hR₂.out a (by rw [n64]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
      (fun h => h1 (by rw [ep'] at h; simp only [c95Wr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega)),
    hmo a (by omega) (fun h => h1 (by simp only [c95Wr, InR]; omega)),
    hR₁.out a (by rw [n80]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
      (fun h => h1 (by rw [ep] at h; simp only [c95Wr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega))]
  exact hv a (by omega) fun h => h1 (by simp only [c95Wr, InR]; omega)

end FV7z.Ctor
