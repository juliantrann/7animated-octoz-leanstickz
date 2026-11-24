import FV7z.Ctor.Cx95
import FV7z.Nst
/-!
# Constructor 98: an empty string on the heap, `__cxa_atexit` (PLAN.md §M, constructors)

`csuTg 98` (`0x41ccb0`): `endbr64; sub rsp, 8; lea rdi, O; call 0x44c360; mov rdi, 0x5a9fd0; add rsp, 8; lea rdx,
__dso_handle; lea rsi, O; jmp __cxa_atexit`, with the string `O = 0x79ed90` (the function at `0x44c360`:
`Nst.nst_ok`, the first constructor to call `malloc`).

- `cx_tail`: the tail `mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M; jmp __cxa_atexit` after a
  constructor's `call`, back at the return address (`mc_tail` is this after `pthread_mutex_init`).
- `c98_runs`, `c98_jg`: `csuTg 98` as `Csu.csu_ok` asks, and for `Jg` (its spec `wrSpec (c98Wr l n)`, the shared words
  `c98Sh l hi`: those of `__cxa_atexit` and the heap's, in the spec of `k₀`).
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem e136n (sp : Addr) (h : 136 ≤ sp.toNat) : (sp - 136#64).toNat = sp.toNat - 136 := by bv_omega

/-! ## The tail to `__cxa_atexit` -/

/-- The tail `mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M; jmp __cxa_atexit` at offset `j + 20` of
`sti`, with `rsp = sp - 72` and the return address at `sp - 64`: the run reaches the return address with
`rsp = sp - 56`, the registers a call keeps and `__cxa_atexit`'s stores (`Cxa.Reg`, the list's place `n`). -/
theorem cx_tail {sp fb l : Addr} {j r₂ M D n : Nat} {Z₁ : State} {t : Nat} {V₁ : Addr → Byte} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (hKZ : KeptW Wl s₀ Z₁) (hAZ : Agree F Z₁.proc.mm.mem V₁) (hrZ : Z₁.cpu.rip = sti_at.add (j + 20))
    (hsZ : Z₁.cpu.gpr.rsp = sp - 80#64 + 8#64)
    (htl : BlkA prof sti sti_at (j + 20) (j + 45)
      [Op.mov 64 7 (.i D), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i M)])
    (hjd : Dec prof.feat sti (j + 45) (FV7z.mk .jmp 64 [.rel r₂] 5))
    (htj : sti_at.add (j + 45 + 5) + BitVec.ofNat 64 r₂ = Cxa.cxa_at.add 0) (hj : j + 45 < sti.length)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hlr : ∀ i < 8, Foot F.data (Addr.add (sp - 64#64) i))
    (h64 : 64 ≤ sp.toNat) (hs8 : sp.toNat + 8 ≤ 2 ^ 64) (hS : 8029400 ≤ sp.toNat) (hD0 : BitVec.ofNat 64 D ≠ 0)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : l ≠ 0) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat) (hX : CxPre fb l n V₁)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₁, sp - 64#64) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Cxa.Reg V₁ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 D ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 M) 7938344#64 →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp - 64#64 + 8#64 → Cs Z₁.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Z₁ t := by
  have hsl := sp.isLt
  have n64 := Csu.sp_n h64
  -- `mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M`
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
    (by rw [hg₄]; exact hdx₃) (off_ft hst 16 (e120 sp) (by omega)) hlr
    hin₂ h₂ hra (by rw [n64]; omega) hD0 hft hfn (by rw [n64]; omega) hfld hfcd hX.mt hfl hX.flag hp hX.ptr hl0
    hn rfl hlw (by rw [n64]; omega) hkw (by rw [n64]; omega) hlc hX.lock hX.idx hX.next hX.prev ?_
  intro V' g' Z t' hKZ' hAZ' hR hrZ' hgZ _ hBk
  exact k V' Z t' hKZ' hAZ' hR hrZ' (by rw [hgZ, hBk.1, hg₄, hsp₃])
    (Cs.trans hc₃ (by rw [hgZ]; rw [hg₄] at hBk; exact hBk.2))

/-! ## `csuTg 98` -/

/-- `csuTg 98`, at `0x41ccb0`: the string `0x79ed90`. -/
def c2928 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0xd1, 0x20, 0x38, 0x00, 0xe8,
  0x9c, 0xf6, 0x02, 0x00, 0x48, 0xc7, 0xc7, 0xd0, 0x9f, 0x5a, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x48,
  0x8d, 0x15, 0x52, 0x54, 0x37, 0x00, 0x48, 0x8d, 0x35, 0xb3, 0x20, 0x38, 0x00, 0xe9, 0xae, 0x69,
  0x20, 0x00]
theorem c2928_0 : ∀ feat, Dec feat c2928 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c2928_4 : ∀ feat, Dec feat c2928 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2928_8 : ∀ feat, Dec feat c2928 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678417 0)] 7) := by dec_rfl
theorem c2928_15 : ∀ feat, Dec feat c2928 15 (FV7z.mk .call 64 [.rel 194204] 5) := by dec_rfl
theorem c2928_20 : ∀ feat, Dec feat c2928 20 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5939152)] 7) := by dec_rfl
theorem c2928_27 : ∀ feat, Dec feat c2928 27 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2928_31 : ∀ feat, Dec feat c2928 31 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626066 0)] 7) := by dec_rfl
theorem c2928_38 : ∀ feat, Dec feat c2928 38 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678387 0)] 7) := by dec_rfl
theorem c2928_45 : ∀ feat, Dec feat c2928 45 (FV7z.mk .jmp 64 [.rel 2124206] 5) := by dec_rfl
theorem v2928 : c2928 <+: sti.drop 2928 := by decide +kernel
theorem tg98 : csuTg 98 = sti_at.add 2928 := by decide +kernel

theorem pq2928 (prof : Profile) : BlkA prof c2928 (0x41ccb0 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c2928_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c2928_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb2928 (prof : Profile) : BlkA prof sti sti_at 2928 2936 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq2928 prof).shift (by decide) v2928
theorem lq2928 (prof : Profile) : BlkA prof c2928 (0x41ccb0 : Addr) 8 15 [Op.mov 64 7 (.i 7990672)] :=
  .cons (c2928_8 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 15
theorem lb2928 (prof : Profile) : BlkA prof sti sti_at 2936 2943 [Op.mov 64 7 (.i 7990672)] :=
  (lq2928 prof).shift (by decide) v2928
theorem cd2943 (feat : Features) : Dec feat sti 2943 (FV7z.mk .call 64 [.rel 194204] 5) :=
  Dec.shift (j := 2928) (k := 15) (c2928_15 feat) v2928 (by decide)
theorem tq2928 (prof : Profile) : BlkA prof c2928 (0x41ccb0 : Addr) 20 45
    [Op.mov 64 7 (.i 5939152), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990672)] :=
  .cons (c2928_20 _) ((OpI.mov (.i 5939152) (.inr rfl)).at _) (by decide) <|
  .cons (c2928_27 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (c2928_31 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2928_38 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 45
theorem tb2928 (prof : Profile) : BlkA prof sti sti_at 2948 2973
    [Op.mov 64 7 (.i 5939152), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990672)] :=
  (tq2928 prof).shift (by decide) v2928
theorem jd2928 (feat : Features) : Dec feat sti 2973 (FV7z.mk .jmp 64 [.rel 2124206] 5) :=
  Dec.shift (j := 2928) (k := 45) (c2928_45 feat) v2928 (by decide)
theorem tc2943 : sti_at.add (2943 + 5) + BitVec.ofNat 64 194204 = Nst.nst_at := by decide +kernel
theorem tj2973 : sti_at.add (2928 + 45 + 5) + BitVec.ofNat 64 2124206 = Cxa.cxa_at.add 0 := by decide +kernel

theorem eO98 : (7990672#64 : Addr).toNat = 7990672 := rfl

set_option maxHeartbeats 1600000 in
/-- `csuTg 98` is a function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs and the heap (`hpre`), and
`J (m + 1)` holds of the bytes after the string's set-up (`V₂`: `[O] = p`, `[O + 8] = 0x300000000`, `[p] = 0`, the
bytes outside `O`'s 16, the heap's top word, `[p - 8, hi)` and the frame as before, the heap for every byte map that
agrees on `GlR` but for `[p, p + 4)`) and `__cxa_atexit`'s stores for it (place `n`). -/
theorem c98_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m n hi k : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinS : CodeIn L Nst.nst_at Nst.nst) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hinM : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2928)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < sp.toNat - 64 → Foot Wl a) (hhs : hi + 1024 ≤ sp.toNat)
    (hS : 8029400 ≤ sp.toNat) (hk : 16 ≤ k) (hOw : ∀ a : Addr, 7990672 ≤ a.toNat → a.toNat < 7990688 → Foot Wl a)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hf7 : fb.toNat + 56 ≤ 7940768 ∨ 7940776 ≤ fb.toNat) (hfO : fb.toNat + 56 ≤ 7990672 ∨ 7990688 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hpre : ∀ W, J m W → CxPre fb l n W ∧ Mal.Hp F Wl fb hi (k + 1072) W)
    (hJ : ∀ W V₂ V' (p : Addr), J m W →
      (∀ a : Addr, ¬ (7990672 ≤ a.toNat ∧ a.toNat < 7990688) →
        (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
          hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V₂ a = W a) →
      rdq(V₂, 7990672#64) = p → rdq(V₂, 7990672#64 + 8#64) = 12884901888#64 →
      (byteAddrs p 1).map V₂ = toBytesLE 0#8 1 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 4 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 4 → Foot Wl a ∧ Foot F.data a) →
      (∀ U : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 4 ≤ a.toNat) → U a = V₂ a) →
        Mal.Hp F Wl fb hi k U) →
      Cxa.Reg V₂ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5939152 ^^^ rdq(V₂, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990672) 7938344#64 →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra kk
  have hsl := sp.isLt
  have n64 := Csu.sp_n hC.s0
  have n80 := e80n sp (by omega)
  have n136 := e136n sp (by omega)
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  have hl0' : l ≠ 0 := by rintro rfl; simp at hl0
  obtain ⟨hX, hH⟩ := hpre V hI
  have hhl := hH.hi_ge
  have hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i) := fun i hi' =>
    Nst.fw hsw (by omega) hi' (by rw [n136]; omega) (by rw [n136]; omega)
  -- `endbr64; sub rsp, 8`
  refine pro (pb2928 prof) c hin hK hA (hr.trans htg) fun Y₀ t₀ hK₀ hA₀ hr₀ hs₀ hc₀ => ?_
  rw [hsp, e72] at hs₀
  -- `lea rdi, O`
  refine (Sp.blkA (lb2928 prof)).run c hin (fun j' g' _ V' => j' = 2943 ∧
    g' = wr Y₀.cpu.gpr 7 (BitVec.ofNat 64 7990672) ∧ V = V') hK₀ hA₀ hr₀ ?_ ?_
  · intro _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = sp - 72#64 := by rw [hg₁]; exact hs₀
  have hd₁ : Y₁.cpu.gpr.rdi = 7990672#64 := by rw [hg₁]; exact sw_64_64 _
  have hc₁ : Cs Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `call 0x44c360`
  refine c.s_call hK₁ hA₁ hin (sti_lt (by decide)) hr₁ (cd2943 _) hinS (Nst.lt_len (j := 0) (by decide)) tc2943
    (fun i hi' => by rw [hs₁, e72b]; exact Nst.fw hsw (by omega) hi' (by rw [n80]; omega) (by rw [n80]; omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hs₁, e72b] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = sp - 80#64 := by rw [hg₂]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hs₁, e72b]
  have hdi₂ : Y₂.cpu.gpr.rdi = 7990672#64 := by rw [hg₂]; exact hd₁
  have hc₂ : Cs Y₁.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hV₀ : ∀ a : Addr, ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 72) →
      Vst V (sp - 80#64) (toBytesLE (sti_at.add (2943 + 5)) 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n80]; omega) (by rw [n80]; omega)
  have hH₀ := Mal.Hp.mvR hH (by omega) fun a ha => hV₀ a (by unfold Mal.GlR at ha; omega)
  -- the string's set-up
  refine Nst.nst_ok c hfs hinS hinW hinM hinI hK₂ hA₂ hr₂ hH₀ hk hdi₂
    (fun a h1 h2 => by rw [eO98] at h1 h2; unfold Mal.GlR; omega) (by rw [eO98]; omega) (by rw [eO98]; omega)
    (fun a h1 h2 => hOw a (by rw [eO98] at h1; exact h1) (by rw [eO98] at h2; omega))
    (by rw [hsp₂, n80]; omega) (by rw [hsp₂, n80]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hsp₂, n80] at h2; omega)) (j := 2943 + 5) hin (sti_lt (by decide))
    (by rw [hsp₂, Sga.vs (a := sp - 80#64) (n := 8) (toBytesLE_length _ _) (by rw [n80]; omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro Z t₃ V₂ p hKZ hAZ hrZ hsZ hbx hbp h12 h13 h14 h15 hp1 hp2 hpn hpF hO1 hO2 hp0 hfr hHp
  rw [hsp₂, n80, eO98] at hfr
  have hsZ' : Z.cpu.gpr.rsp = sp - 80#64 + 8#64 := by rw [hsZ, hsp₂]; try rfl
  have hcN : Cs Y₂.cpu.gpr Z.cpu.gpr := ⟨hbx, hbp, h12, h13, h14, h15⟩
  have hv : ∀ a : Addr, ¬ (7990672 ≤ a.toNat ∧ a.toNat < 7990688) →
      (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V₂ a = V a := fun a h1 h2 =>
    (hfr a (by omega) (by omega)).trans (hV₀ a (by omega))
  have hX₂ : CxPre fb l n V₂ := hX.kept hn hfn (by omega) fun a ha =>
    hv a (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)
  -- `mov rdi, 0x5a9fd0; add rsp, 8; lea rdx, __dso_handle; lea rsi, O; jmp __cxa_atexit`
  refine cx_tail (j := 2928) (M := 7990672) (D := 5939152) c hin hfs hinC hinN hKZ hAZ hrZ hsZ' (tb2928 prof)
    (jd2928 _) tj2973 (sti_lt (by decide)) hst (fun i hi => c.hws _ (hC.st i (by omega))) hC.s0 hC.s8 hS
    (by decide) hft hfn hfsd hfld hfcd hfl hp hl0' hn hlw hld hkw (.inl hlc) hX₂ hC.code hj₂
    ((rdq_eq (V := V) (x := sp - 64#64) (by rw [n64]; omega) fun a h1 h2 => hv a
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)).trans hra) ?_
  intro V' Z' t' hKZ' hAZ' hR hrZ' hsZ'' hcs
  refine kk Z' t' V' hKZ' hAZ' (hJ V V₂ V' p hI hv hO1 hO2 hp0 hp1 hp2 hpn hpF hHp hR) (fun a ha => ?_)
    (fun a ha => ?_) hrZ' ⟨by rw [hsZ'', hsp], Cs.trans hc₀ (Cs.trans hc₁ (Cs.trans hc₂ (Cs.trans hcN hcs)))⟩
  · rw [hR.out a (by rw [n64]; omega) (by omega) (by rw [ep]; omega) (by omega)]
    exact hv a (by omega) (.inr (.inr ⟨by omega, .inr (by omega)⟩))
  · rw [hR.out a (by rw [n64]; omega) (by omega) (by rw [ep]; omega) (by omega)]
    exact hv a (by omega) (.inl (by omega))

/-- The intervals of `csuTg 98`: the string and the list's place `n`. -/
def c98Wr (l : Addr) (n : Nat) : List (Nat × Nat) :=
  [(7990672, 7990688), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 32)]

/-- The words `csuTg 98` shares with the constructors before and after it: `__cxa_atexit`'s (`cxSh l`) and those
`malloc` reads (`Mal.GlR hi`). -/
def c98Sh (l : Addr) (hi : Nat) : List (Nat × Nat) :=
  [(l.toNat + 8, l.toNat + 16), (8029184, 8029200), (7940480, 7943136), (8013220, 8013232), (8029888, hi)]

/-- `c98_runs` for `Jg`, the spec `wrSpec (c98Wr l n)`, the shared words `c98Sh l hi` in the spec of `k₀`. -/
theorem c98_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m n k₀ hi k : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinS : CodeIn L Nst.nst_at Nst.nst) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hinM : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2928)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < sp.toNat - 64 → Foot Wl a) (hhs : hi + 1024 ≤ sp.toNat)
    (hS : 8029400 ≤ sp.toNat) (hk : 16 ≤ k) (hOw : ∀ a : Addr, 7990672 ≤ a.toNat → a.toNat < 7990688 → Foot Wl a)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hf7 : fb.toNat + 56 ≤ 7940768 ∨ 7940776 ≤ fb.toNat) (hfO : fb.toNat + 56 ≤ 7990672 ∨ 7990688 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (c98Wr l n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c98Wr l n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (c98Sh l hi) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (c98Sh l hi) x)
    (hGx : ∀ W, G m W → CxPre fb l n W ∧ Mal.Hp F Wl fb hi (k + 1072) W)
    (hG : ∀ W V₂ V' (p : Addr), G m W →
      (∀ a : Addr, ¬ (7990672 ≤ a.toNat ∧ a.toNat < 7990688) →
        (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
          hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V₂ a = W a) →
      rdq(V₂, 7990672#64) = p → rdq(V₂, 7990672#64 + 8#64) = 12884901888#64 →
      (byteAddrs p 1).map V₂ = toBytesLE 0#8 1 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 4 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 4 → Foot Wl a ∧ Foot F.data a) →
      (∀ U : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 4 ≤ a.toNat) → U a = V₂ a) →
        Mal.Hp F Wl fb hi k U) →
      Cxa.Reg V₂ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5939152 ^^^ rdq(V₂, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990672) 7938344#64 →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n64 := Csu.sp_n hC.s0
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  refine c98_runs c hC hin hfs hinS hinW hinM hinI hinC hinN htg hsw hhs hS hk hOw hft hfn hfsd hf7 hfO hfld hfcd
    hfl hp hl0 hn hlw hld hkw hlc (fun W hJ => hGx W hJ.2)
    fun W V₂ V' p hJ hv hO1 hO2 hp0 hp1 hp2 hpn hpF hHp hR => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m
      hSh hP₀ hShD (fun a h1 h2 h3 => ?_) (hG W V₂ V' p · hv hO1 hO2 hp0 hp1 hp2 hpn hpF hHp hR) hJ
  simp only [c98Wr, c98Sh, InR] at h1 h3
  rw [hR.out a (by rw [n64]; omega) (by omega) (by rw [ep]; omega) (by omega)]
  exact hv a (by omega) (by omega)

end FV7z.Ctor
