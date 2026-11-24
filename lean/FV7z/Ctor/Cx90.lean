import FV7z.Ctor.Cx99
/-!
# Constructors 94 and 90: `__cxa_atexit` with a `ret` after it, and the first of them (PLAN.md §M, constructors)

- `csuTg 94` (`0x41cb90`): `endbr64; sub rsp, 8; lea rdi, M; call CriticalSection_Init; mov rdi, D; lea rdx,
  __dso_handle; lea rsi, M; call __cxa_atexit; mov rax, 0x79ec20; mov byte [rax + 0x20], 1; add rsp, 8; ret` with the
  mutex `M = 0x79ec60`: `c94_runs`, `c94_jg`.
- `csuTg 90` (`0x41caf0`): `endbr64; sub rsp, 8; mov rdi, 0x59a640; lea rdx, __dso_handle; lea rsi, O; mov dword [O],
  32; mov qword [O + 8], 0; mov qword [O + 16], 0; call __cxa_atexit`, then the tail of `mc_tail` for the mutex
  `M = 0x79ebc0`, with the object `O = 0x79ebf0`: `c90_runs`, `c90_jg`. It is the first constructor to call
  `__cxa_atexit`, so its spec holds the words they share (`cxSh`).
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## `csuTg 94` -/

/-- `csuTg 94`, at `0x41cb90`: the mutex `0x79ec60` and the byte `0x79ec40`. -/
def c2640 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0xc1, 0x20, 0x38, 0x00, 0xe8,
  0x9c, 0xbf, 0x02, 0x00, 0x48, 0xc7, 0xc7, 0x20, 0xa6, 0x59, 0x00, 0x48, 0x8d, 0x15, 0x76, 0x55,
  0x37, 0x00, 0x48, 0x8d, 0x35, 0xa7, 0x20, 0x38, 0x00, 0xe8, 0xd2, 0x6a, 0x20, 0x00, 0x48, 0xc7,
  0xc0, 0x20, 0xec, 0x79, 0x00, 0xc6, 0x40, 0x20, 0x01, 0x48, 0x83, 0xc4, 0x08, 0xc3]
theorem c2640_0 : ∀ feat, Dec feat c2640 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c2640_4 : ∀ feat, Dec feat c2640 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2640_8 : ∀ feat, Dec feat c2640 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678401 0)] 7) := by dec_rfl
theorem c2640_15 : ∀ feat, Dec feat c2640 15 (FV7z.mk .call 64 [.rel 180124] 5) := by dec_rfl
theorem c2640_20 : ∀ feat, Dec feat c2640 20 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c2640_27 : ∀ feat, Dec feat c2640 27 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626358 0)] 7) := by dec_rfl
theorem c2640_34 : ∀ feat, Dec feat c2640 34 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678375 0)] 7) := by dec_rfl
theorem c2640_41 : ∀ feat, Dec feat c2640 41 (FV7z.mk .call 64 [.rel 2124498] 5) := by dec_rfl
theorem c2640_46 : ∀ feat, Dec feat c2640 46 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7990304)] 7) := by dec_rfl
theorem c2640_53 : ∀ feat, Dec feat c2640 53 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 32 8), .imm 8 1] 4) := by
  dec_rfl
theorem c2640_57 : ∀ feat, Dec feat c2640 57 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2640_61 : ∀ feat, Dec feat c2640 61 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v2640 : c2640 <+: sti.drop 2640 := by decide +kernel
theorem tg94 : csuTg 94 = sti_at.add 2640 := by decide +kernel

theorem pq2640 (prof : Profile) : BlkA prof c2640 (0x41cb90 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c2640_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c2640_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb2640 (prof : Profile) : BlkA prof sti sti_at 2640 2648 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq2640 prof).shift (by decide) v2640
theorem lq2640 (prof : Profile) : BlkA prof c2640 (0x41cb90 : Addr) 8 15 [Op.mov 64 7 (.i 7990368)] :=
  .cons (c2640_8 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 15
theorem lb2640 (prof : Profile) : BlkA prof sti sti_at 2648 2655 [Op.mov 64 7 (.i 7990368)] :=
  (lq2640 prof).shift (by decide) v2640
theorem cd2655 (feat : Features) : Dec feat sti 2655 (FV7z.mk .call 64 [.rel 180124] 5) :=
  Dec.shift (j := 2640) (k := 15) (c2640_15 feat) v2640 (by decide)
theorem bq2660 (prof : Profile) : BlkA prof c2640 (0x41cb90 : Addr) 20 41
    [Op.mov 64 7 (.i 5875232), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990368)] :=
  .cons (c2640_20 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c2640_27 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2640_34 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 41
theorem b2660 (prof : Profile) : BlkA prof sti sti_at 2660 2681
    [Op.mov 64 7 (.i 5875232), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990368)] :=
  (bq2660 prof).shift (by decide) v2640
theorem cd2681 (feat : Features) : Dec feat sti 2681 (FV7z.mk .call 64 [.rel 2124498] 5) :=
  Dec.shift (j := 2640) (k := 41) (c2640_41 feat) v2640 (by decide)
theorem bq2686 (prof : Profile) : BlkA prof c2640 (0x41cb90 : Addr) 46 61
    [Op.mov 64 0 (.i 7990304), Op.sti 8 (some 0) none 1 32 1, Op.add 64 4 (.i 8)] :=
  .cons (c2640_46 _) ((OpI.mov (.i 7990304) (.inr rfl)).at _) (by decide) <|
  .cons (c2640_53 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (c2640_57 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <| .nil 61
theorem b2686 (prof : Profile) : BlkA prof sti sti_at 2686 2701
    [Op.mov 64 0 (.i 7990304), Op.sti 8 (some 0) none 1 32 1, Op.add 64 4 (.i 8)] :=
  (bq2686 prof).shift (by decide) v2640
theorem rd2701 (feat : Features) : Dec feat sti 2701 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 2640) (k := 61) (c2640_61 feat) v2640 (by decide)
theorem tc2655 : sti_at.add (2655 + 5) + BitVec.ofNat 64 180124 = Mxs.mxs_at := by decide +kernel
theorem tc2681 : sti_at.add (2681 + 5) + BitVec.ofNat 64 2124498 = Cxa.cxa_at := by decide +kernel

theorem ea94 (g : Gprs) : eaG (wr g 0 (BitVec.ofNat 64 7990304)) (some 0) none 1 32 = 7990336#64 := by
  cases g
  rfl

/-- `csuTg 94` is a function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs (`hpre`), and `J (m + 1)`
holds of the bytes after the mutex's set-up (`V₁`, below the frame and to `M`), `__cxa_atexit`'s stores (place `n`)
and the byte `1` at `0x79ec40`. -/
theorem c94_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m n : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2640)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfM : fb.toNat + 56 ≤ 7990368 ∨ 7990408 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hm1 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990368) i))
    (hb : ∀ i < 1, Foot Wl (Addr.add 7990336#64 i))
    (hpre : ∀ W, J m W → CxPre fb l n W)
    (hJ : ∀ W V₁ V₂, J m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990368 ≤ a.toNat ∧ a.toNat < 7990408) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990368) 7938344#64 →
      J (m + 1) (Vst V₂ 7990336#64 (toBytesLE (BitVec.ofNat 8 1) 1))) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs8 := hC.s8
  have hsl := sp.isLt
  have n72 := e72n sp (by omega)
  have n80 := e80n sp (by omega)
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  have hl0' : l ≠ 0 := by rintro rfl; simp at hl0
  -- `endbr64; sub rsp, 8`
  refine pro (pb2640 prof) c hin hK hA (hr.trans htg) fun Y₀ t₀ hK₀ hA₀ hr₀ hs₀ hc₀ => ?_
  rw [hsp, e72] at hs₀
  -- `lea rdi, M`
  refine (Sp.blkA (lb2640 prof)).run c hin (fun j' g' _ V' => j' = 2655 ∧
    g' = wr Y₀.cpu.gpr 7 (BitVec.ofNat 64 7990368) ∧ V = V') hK₀ hA₀ hr₀ ?_ ?_
  · intro _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = sp - 72#64 := by rw [hg₁]; exact hs₀
  have hd₁ : Y₁.cpu.gpr.rdi = BitVec.ofNat 64 7990368 := by rw [hg₁]; exact sw_64_64 _
  have hc₁ : Cs Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `call CriticalSection_Init`
  refine mx_mid (R := sp - 72#64) (M := 7990368) c hin hfs hinM hinI hK₁ hA₁ hr₁ (cd2655 _) tc2655
    (sti_lt (by decide)) hs₁ hd₁ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) (by decide)
    hm1 hft hfn (by rw [n72]; omega) (by omega) (by rw [n72]; omega) ?_
  intro V₁ Y₂ t₂ hK₂ hA₂ ho₁ hr₂ hs₂ hc₂
  rw [n72] at ho₁
  -- `mov rdi, D; lea rdx, __dso_handle; lea rsi, M`
  refine (Sp.blkA (b2660 prof)).run c hin (fun j' g' _ V' => j' = 2681 ∧
    g' = wr (wr (wr Y₂.cpu.gpr 7 (BitVec.ofNat 64 5875232)) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 7990368) ∧ V₁ = V') hK₂ hA₂ hr₂ ?_ ?_
  · intro _ _ _ _ _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hs₃ : Y₃.cpu.gpr.rsp = sp - 72#64 := by rw [hg₃]; exact hs₂
  have hd₃ : Y₃.cpu.gpr.rdi = BitVec.ofNat 64 5875232 := by rw [hg₃]; exact sw_64_64 _
  have hx₃ : Y₃.cpu.gpr.rsi = BitVec.ofNat 64 7990368 := by rw [hg₃]; exact sw_64_64 _
  have hdx₃ : Y₃.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₃]; exact sw_64_64 _
  have hc₃ : Cs Y₂.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hX₁ : CxPre fb l n V₁ := (hpre V hI).kept hn hfn (by omega) fun a ha =>
    ho₁ a (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)
  -- `call __cxa_atexit (D, M, __dso_handle)`
  refine cx_mid (R := sp - 72#64) c hin hfs hinC hinN hK₃ hA₃ hr₃ (cd2681 _) tc2681 (sti_lt (by decide)) hs₃ hd₃
    hx₃ hdx₃ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) hX₁ hft hfn
    (by rw [n72]; omega) hfld hfcd hfl hp hl0' hn hlw (by rw [n72]; omega) hkw (by rw [n72]; omega)
    (by omega) ?_
  intro V₁' V₂ Y₄ t₄ hK₄ hA₄ hv₁ hR₁ hr₄ hs₄ hc₄
  rw [n72] at hv₁
  rw [e72b] at hR₁
  -- `mov rax, 0x79ec20; mov byte [rax + 0x20], 1; add rsp, 8`
  have hb' : ∀ i < 8 / 8, Foot Wl (Addr.add (eaG (wr Y₄.cpu.gpr 0 (BitVec.ofNat 64 7990304)) (some 0) none 1 32) i) :=
    by rw [ea94]; exact hb
  refine (Sp.blkA (b2686 prof)).run c hin (fun j' g' _ V' => j' = 2701 ∧
    g' = wr (wr Y₄.cpu.gpr 0 (BitVec.ofNat 64 7990304)) 4
      (addR (gv (wr Y₄.cpu.gpr 0 (BitVec.ofNat 64 7990304)) 64 4) (BitVec.ofNat 64 8)) ∧
    V' = Vst V₂ (eaG (wr Y₄.cpu.gpr 0 (BitVec.ofNat 64 7990304)) (some 0) none 1 32)
      (toBytesLE (BitVec.ofNat 8 1) (8 / 8))) hK₄ hA₄ hr₄ ?_ ?_
  · intro _ _
    exact ⟨toBytesLE_length _ _, hb', fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  rw [ea94] at hA₅
  have hs₅ : Y₅.cpu.gpr.rsp = sp - 64#64 := by
    rw [hg₅, rsp_add8]
    show Y₄.cpu.gpr.rsp + 8 = _
    rw [hs₄, e72a]
  have hc₅ : Cs Y₄.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcs : Cs X.cpu.gpr Y₅.cpu.gpr :=
    Cs.trans hc₀ (Cs.trans hc₁ (Cs.trans hc₂ (Cs.trans hc₃ (Cs.trans hc₄ hc₅))))
  have hv : ∀ a : Addr, a.toNat < 7990336 ∨ 7990337 ≤ a.toNat →
      Vst V₂ 7990336#64 (toBytesLE (BitVec.ofNat 8 1) (8 / 8)) a = V₂ a := fun a h => vo (by omega) (by omega)
  -- `ret`
  refine ret_tail c hC hin (rd2701 _) (sti_lt (by decide)) hsp hj₂ hra hK₅ hA₅ hr₅
    ⟨hs₅.trans hsp.symm, hcs.1, hcs.2.1, hcs.2.2.1, hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2⟩
    (hJ V V₁' V₂ hI (fun a h1 h2 => (hv₁ a (by omega)).trans (ho₁ a (by omega) (by omega))) hR₁)
    (fun a ha => ?_) k
  rw [hv a (by omega), hR₁.out a (by rw [n80]; omega) (by omega) (by rw [ep]; omega) (by omega), hv₁ a (by omega)]
  exact ho₁ a (by omega) (by omega)

/-- The intervals of `csuTg 94`: the byte, the mutex and the list's place `n`. -/
def c94Wr (l : Addr) (n : Nat) : List (Nat × Nat) :=
  [(7990336, 7990337), (7990368, 7990408), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 32)]

/-- `c94_runs` for `Jg`, the spec `wrSpec (c94Wr l n)`, the shared words `cxSh l` in the spec of `k₀`. -/
theorem c94_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m n k₀ : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2640)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfM : fb.toNat + 56 ≤ 7990368 ∨ 7990408 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hm1 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990368) i))
    (hb : ∀ i < 1, Foot Wl (Addr.add 7990336#64 i))
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (c94Wr l n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c94Wr l n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (cxSh l) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (cxSh l) x)
    (hGx : ∀ W, G m W → CxPre fb l n W)
    (hG : ∀ W V₁ V₂, G m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990368 ≤ a.toNat ∧ a.toNat < 7990408) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990368) 7938344#64 →
      G (m + 1) (Vst V₂ 7990336#64 (toBytesLE (BitVec.ofNat 8 1) 1))) :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n80 := e80n sp (by omega)
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n hn (by omega)
  refine c94_runs c hC hin hfs hinM hinI hinC hinN htg hst hS hft hfn hfsd hfM hfld hfcd hfl hp hl0 hn hlw hld hkw
    hlc hm1 hb (fun W hJ => hGx W hJ.2)
    fun W V₁ V₂ hJ hmo hR₁ => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m hSh hP₀ hShD
      (fun a h1 h2 h3 => ?_) (hG W V₁ V₂ · hmo hR₁) hJ
  have h0 : ¬ (7990336 ≤ a.toNat ∧ a.toNat < 7990337) := fun h => h1 (by simp only [c94Wr, InR]; omega)
  rw [vo (x := 7990336) (n := 1) (a := a) (by decide) (by omega),
    hR₁.out a (by rw [n80]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
      (fun h => h1 (by rw [ep] at h; simp only [c94Wr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega))]
  exact hmo a (by omega) fun h => h1 (by simp only [c94Wr, InR]; omega)

/-! ## `csuTg 90` -/

/-- `csuTg 90`, at `0x41caf0`: the object `0x79ebf0` and the mutex `0x79ebc0`. -/
def c2480 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0xc7, 0x40, 0xa6, 0x59, 0x00, 0x48,
  0x8d, 0x15, 0x22, 0x56, 0x37, 0x00, 0x48, 0x8d, 0x35, 0xe3, 0x20, 0x38, 0x00, 0xc7, 0x05, 0xd9,
  0x20, 0x38, 0x00, 0x20, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x05, 0xd6, 0x20, 0x38, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x05, 0xd3, 0x20, 0x38, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x5e, 0x6b,
  0x20, 0x00, 0x48, 0x8d, 0x3d, 0x87, 0x20, 0x38, 0x00, 0xe8, 0x02, 0xc0, 0x02, 0x00, 0x48, 0xc7,
  0xc7, 0x20, 0xa6, 0x59, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x48, 0x8d, 0x15, 0xd8, 0x55, 0x37, 0x00,
  0x48, 0x8d, 0x35, 0x69, 0x20, 0x38, 0x00, 0xe9, 0x34, 0x6b, 0x20, 0x00]
theorem c2480_0 : ∀ feat, Dec feat c2480 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c2480_4 : ∀ feat, Dec feat c2480 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2480_8 : ∀ feat, Dec feat c2480 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875264)] 7) := by dec_rfl
theorem c2480_15 : ∀ feat, Dec feat c2480 15 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626530 0)] 7) := by dec_rfl
theorem c2480_22 : ∀ feat, Dec feat c2480 22 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678435 0)] 7) := by dec_rfl
theorem c2480_29 : ∀ feat, Dec feat c2480 29 (FV7z.mk .mov 32 [.mem (mrip 3678425 32), .imm 32 32] 10) := by dec_rfl
theorem c2480_39 : ∀ feat, Dec feat c2480 39 (FV7z.mk .mov 64 [.mem (mrip 3678422 64), .imm 64 0] 11) := by dec_rfl
theorem c2480_50 : ∀ feat, Dec feat c2480 50 (FV7z.mk .mov 64 [.mem (mrip 3678419 64), .imm 64 0] 11) := by dec_rfl
theorem c2480_61 : ∀ feat, Dec feat c2480 61 (FV7z.mk .call 64 [.rel 2124638] 5) := by dec_rfl
theorem c2480_66 : ∀ feat, Dec feat c2480 66 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678343 0)] 7) := by dec_rfl
theorem c2480_73 : ∀ feat, Dec feat c2480 73 (FV7z.mk .call 64 [.rel 180226] 5) := by dec_rfl
theorem c2480_78 : ∀ feat, Dec feat c2480 78 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c2480_85 : ∀ feat, Dec feat c2480 85 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c2480_89 : ∀ feat, Dec feat c2480 89 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626456 0)] 7) := by dec_rfl
theorem c2480_96 : ∀ feat, Dec feat c2480 96 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678313 0)] 7) := by dec_rfl
theorem c2480_103 : ∀ feat, Dec feat c2480 103 (FV7z.mk .jmp 64 [.rel 2124596] 5) := by dec_rfl
theorem v2480 : c2480 <+: sti.drop 2480 := by decide +kernel
theorem tg90 : csuTg 90 = sti_at.add 2480 := by decide +kernel

theorem pq2480 (prof : Profile) : BlkA prof c2480 (0x41caf0 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c2480_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c2480_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb2480 (prof : Profile) : BlkA prof sti sti_at 2480 2488 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq2480 prof).shift (by decide) v2480
/-- The effects of `mov rdi, 0x59a640; lea rdx, __dso_handle; lea rsi, O` and the object's three stores. -/
def o2488 : List Op :=
  [Op.mov 64 7 (.i 5875264), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990256), Op.stia 32 7990256 32,
    Op.stia 64 7990264 0, Op.stia 64 7990272 0]
theorem bq2488 (prof : Profile) : BlkA prof c2480 (0x41caf0 : Addr) 8 61 o2488 :=
  .cons (c2480_8 _) ((OpI.mov (.i 5875264) (.inr rfl)).at _) (by decide) <|
  .cons (c2480_15 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2480_22 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2480_29 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (c2480_39 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (c2480_50 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <| .nil 61
theorem b2488 (prof : Profile) : BlkA prof sti sti_at 2488 2541 o2488 :=
  (bq2488 prof).shift (by decide) v2480
theorem cd2541 (feat : Features) : Dec feat sti 2541 (FV7z.mk .call 64 [.rel 2124638] 5) :=
  Dec.shift (j := 2480) (k := 61) (c2480_61 feat) v2480 (by decide)
theorem lq2546 (prof : Profile) : BlkA prof c2480 (0x41caf0 : Addr) 66 73 [Op.mov 64 7 (.i 7990208)] :=
  .cons (c2480_66 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 73
theorem lb2546 (prof : Profile) : BlkA prof sti sti_at 2546 2553 [Op.mov 64 7 (.i 7990208)] :=
  (lq2546 prof).shift (by decide) v2480
theorem cd2553 (feat : Features) : Dec feat sti 2553 (FV7z.mk .call 64 [.rel 180226] 5) :=
  Dec.shift (j := 2480) (k := 73) (c2480_73 feat) v2480 (by decide)
theorem tq2558 (prof : Profile) : BlkA prof c2480 (0x41caf0 : Addr) 78 103
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990208)] :=
  .cons (c2480_78 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c2480_85 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (c2480_89 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2480_96 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 103
theorem tb2558 (prof : Profile) : BlkA prof sti sti_at 2558 2583
    [Op.mov 64 7 (.i 5875232), Op.add 64 4 (.i 8), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7990208)] :=
  (tq2558 prof).shift (by decide) v2480
theorem jd2583 (feat : Features) : Dec feat sti 2583 (FV7z.mk .jmp 64 [.rel 2124596] 5) :=
  Dec.shift (j := 2480) (k := 103) (c2480_103 feat) v2480 (by decide)
theorem tc2541 : sti_at.add (2541 + 5) + BitVec.ofNat 64 2124638 = Cxa.cxa_at := by decide +kernel
theorem tc2553 : sti_at.add (2538 + 15 + 5) + BitVec.ofNat 64 180226 = Mxs.mxs_at := by decide +kernel
theorem tj2583 : sti_at.add (2538 + 45 + 5) + BitVec.ofNat 64 2124596 = Cxa.cxa_at.add 0 := by decide +kernel

/-- The bytes after the object's three stores: `32` at `O`, `0` at `O + 8` and `O + 16`. -/
def ob90 (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (BitVec.ofNat 64 7990256) (toBytesLE (BitVec.ofNat 32 32) 4)) (BitVec.ofNat 64 7990264)
    (toBytesLE (BitVec.ofNat 64 0) 8)) (BitVec.ofNat 64 7990272) (toBytesLE (BitVec.ofNat 64 0) 8)

theorem ob90_out (V : Addr → Byte) (a : Addr) (h : a.toNat < 7990256 ∨ 7990280 ≤ a.toNat) : ob90 V a = V a := by
  unfold ob90
  rw [vo, vo, vo] <;> omega

/-- `csuTg 90` is a function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs (`hpre`), and `J (m + 1)`
holds of the bytes after the object's stores (`ob90`), `__cxa_atexit`'s stores for it (place `n`), the mutex's
set-up (`V₃`) and `__cxa_atexit`'s stores for it (place `n + 1`). -/
theorem c90_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m n : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2480)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfO : fb.toNat + 56 ≤ 7990208 ∨ 7990280 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990208) i))
    (hob : ∀ i < 24, Foot Wl (Addr.add (BitVec.ofNat 64 7990256) i))
    (hpre : ∀ W, J m W → CxPre fb l n W)
    (hJ : ∀ W V₁ V₂ V₃ V', J m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → V₁ a = ob90 W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875264 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990256) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990208 ≤ a.toNat ∧ a.toNat < 7990248) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990208) 7938344#64 →
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
  refine pro (pb2480 prof) c hin hK hA (hr.trans htg) fun Y₀ t₀ hK₀ hA₀ hr₀ hs₀ hc₀ => ?_
  rw [hsp, e72] at hs₀
  -- `mov rdi, 0x59a640; lea rdx, __dso_handle; lea rsi, O` and the object's stores
  refine (Sp.blkA (b2488 prof)).run c hin (fun j' g' _ V' => j' = 2541 ∧
    g' = wr (wr (wr Y₀.cpu.gpr 7 (BitVec.ofNat 64 5875264)) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 7990256) ∧ V' = ob90 V) hK₀ hA₀ hr₀ ?_ ?_
  · intro _ _ _ _ _ _
    exact ⟨toBytesLE_length _ _, ft_in hob (by omega) (by omega) (by omega), toBytesLE_length _ _,
      ft_in hob (by omega) (by omega) (by omega), toBytesLE_length _ _, ft_in hob (by omega) (by omega) (by omega),
      rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = sp - 72#64 := by rw [hg₁]; exact hs₀
  have hd₁ : Y₁.cpu.gpr.rdi = BitVec.ofNat 64 5875264 := by rw [hg₁]; exact sw_64_64 _
  have hx₁ : Y₁.cpu.gpr.rsi = BitVec.ofNat 64 7990256 := by rw [hg₁]; exact sw_64_64 _
  have hdx₁ : Y₁.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₁]; exact sw_64_64 _
  have hc₁ : Cs Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hX₀ : CxPre fb l n (ob90 V) := (hpre V hI).kept (by omega) hfn (by omega) fun a ha =>
    ob90_out V a (by unfold CxR at ha; omega)
  -- `call __cxa_atexit (0x59a640, O, __dso_handle)`
  refine cx_mid (R := sp - 72#64) c hin hfs hinC hinN hK₁ hA₁ hr₁ (cd2541 _) tc2541 (sti_lt (by decide)) hs₁ hd₁
    hx₁ hdx₁ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) hX₀ hft hfn
    (by rw [n72]; omega) hfld hfcd hfl hp hl0' (by omega) hlw (by rw [n72]; omega) hkw (by rw [n72]; omega)
    (by omega) ?_
  intro V₁ V₂ Y₂ t₂ hK₂ hA₂ hv₁ hR₁ hr₂ hs₂ hc₂
  rw [n72] at hv₁
  rw [e72b] at hR₁
  have hX₂ : CxPre fb l (n + 1) V₂ := (hX₀.kept (by omega) hfn (by omega) fun a ha =>
    hv₁ a (by unfold CxR at ha; omega)).reg hR₁ hn hfn (by omega) (by rw [n80]; omega) (by rw [n80]; omega) hfld
    hfcd (by rw [n80]; omega) (by rw [n80]; omega) (by omega)
  have hkp : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990256 ≤ a.toNat ∧ a.toNat < 7990280) → ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) →
      ¬ (l.toNat + 16 + 32 * n ≤ a.toNat ∧ a.toNat < l.toNat + 48 + 32 * n) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₂ a = V a := fun a h1 h2 h3 h4 h5 => by
    rw [hR₁.out a (by rw [n80]; omega) h3 (by rw [ep]; omega) h5, hv₁ a (by omega)]
    exact ob90_out V a (by omega)
  -- the tail: `lea rdi, M; call CriticalSection_Init; mov rdi, D; add rsp, 8; lea rdx, __dso_handle; lea rsi, M;
  -- jmp __cxa_atexit`
  refine mc_tail (j := 2538) (M := 7990208) (D := 5875232) c hin hfs hinM hinI hinC hinN hK₂ hA₂ hr₂
    (hs₂.trans (e72 sp).symm) (lb2546 prof) (cd2553 _) tc2553 (tb2558 prof) (jd2583 _) tj2583 (sti_lt (by decide))
    hst (fun i hi => c.hws _ (hC.st i (by omega))) hC.s0 hC.s8 hS (by decide) (by decide) (by omega) hmw
    (by decide) hft hfn (by omega) (by omega) hfld hfcd hfl hp hl0' hn hlw hld hkw (.inl hlc) hX₂ hC.code hj₂
    ((rdq_eq (V := V) (x := sp - 64#64) (by rw [n64]; omega) fun a h1 h2 => hkp a
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)).trans hra) ?_
  intro V₃ V' Z t' hKZ hAZ hmo hR₂ hrZ hsZ hcs
  refine k Z t' V' hKZ hAZ (hJ V V₁ V₂ V₃ V' hI (fun a h => hv₁ a (by omega)) hR₁
    (fun a h1 h2 => hmo a h1 (by omega)) hR₂) (fun a ha => ?_) (fun a ha => ?_) hrZ
    ⟨by rw [hsZ, hsp], Cs.trans hc₀ (Cs.trans hc₁ (Cs.trans hc₂ hcs))⟩
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega), hmo a (by omega) (by omega)]
    exact hkp a (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega), hmo a (by omega) (by omega)]
    exact hkp a (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The intervals of `csuTg 90`: the mutex, the object, the list's places `n`, `n + 1` and the words the
constructors that call `__cxa_atexit` share (`cxSh`). -/
def c90Wr (l : Addr) (n : Nat) : List (Nat × Nat) :=
  [(7990208, 7990248), (7990256, 7990280), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 64),
    (l.toNat + 8, l.toNat + 16), (8029184, 8029200)]

/-- `c90_runs` for `Jg`, the spec `wrSpec (c90Wr l n)`, which holds the shared words (`jg_wrk`). -/
theorem c90_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m n : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2480)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfO : fb.toNat + 56 ≤ 7990208 ∨ 7990280 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7990208) i))
    (hob : ∀ i < 24, Foot Wl (Addr.add (BitVec.ofNat 64 7990256) i))
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (c90Wr l n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c90Wr l n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hGx : ∀ W, G m W → CxPre fb l n W)
    (hG : ∀ W V₁ V₂ V₃ V', G m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → V₁ a = ob90 W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875264 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990256) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7990208 ≤ a.toNat ∧ a.toNat < 7990248) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7990208) 7938344#64 →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n64 := Csu.sp_n hC.s0
  have n80 := e80n sp (by omega)
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) (by omega)
  obtain ⟨-, -, ep', -, -, -⟩ := Nef.l_n l (n + 1) hn (by omega)
  refine c90_runs c hC hin hfs hinM hinI hinC hinN htg hst hS hft hfn hfsd hfO hfld hfcd hfl hp hl0 hn hlw hld hkw
    hlc hmw hob (fun W hJ => hGx W hJ.2)
    fun W V₁ V₂ V₃ V' hJ hv hR₁ hmo hR₂ => jg_wrk hm hc (by omega) hspec hD
      (fun x hx => hT m x (by rw [hspec]; exact hx)) hB hXw (fun a h1 h2 => ?_) (hG W V₁ V₂ V₃ V' · hv hR₁ hmo hR₂) hJ
  rw [hR₂.out a (by rw [n64]; omega) (fun h => h1 (by simp only [c90Wr, InR]; omega))
      (fun h => h1 (by rw [ep'] at h; simp only [c90Wr, InR]; omega)) (fun h => h1 (by simp only [c90Wr, InR]; omega)),
    hmo a (by omega) (fun h => h1 (by simp only [c90Wr, InR]; omega)),
    hR₁.out a (by rw [n80]; omega) (fun h => h1 (by simp only [c90Wr, InR]; omega))
      (fun h => h1 (by rw [ep] at h; simp only [c90Wr, InR]; omega)) (fun h => h1 (by simp only [c90Wr, InR]; omega)),
    hv a (by omega)]
  have h0 : ¬ (7990256 ≤ a.toNat ∧ a.toNat < 7990280) := fun h => h1 (by simp only [c90Wr, InR]; omega)
  exact ob90_out W a (by omega)

end FV7z.Ctor
