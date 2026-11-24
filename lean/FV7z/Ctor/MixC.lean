import FV7z.Ctor.Mix
import FV7z.Ctor.PrepC
/-!
# `csuTg 67`: registrar calls, then `jmp z7_Black2sp_Prepare` (PLAN.md §M, constructors)

`csuTg 67` (offset 1360 of `sti`, `0x41c690`) is `endbr64; sub rsp, 8; lea rdi, [rip + d₁]; call RegisterArc;
lea rdi, [rip + d₂]; call RegisterHasher; add rsp, 8; jmp 0x422a20`: `callsK_runs` of `prepK_core` with
`z7_Black2sp_Prepare`'s contract by `fnK` (`Prepare/K.lean`). Its bytes, decodings and stretches follow the pattern
of `Chains.lean` (`tools/ctor_gen.py`); its spec is `wrSpec` of the globals the function writes.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Prepare

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 67`, at `0x41c690`: `RegisterArc (0x77d700)`, `RegisterHasher (0x77d6e0)`, `jmp 0x422a20`. -/
def c1360 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0x61, 0x10, 0x36, 0x00, 0xe8,
  0x7c, 0x24, 0x1b, 0x00, 0x48, 0x8d, 0x3d, 0x35, 0x10, 0x36, 0x00, 0xe8, 0xe0, 0xc7, 0x03, 0x00,
  0x48, 0x83, 0xc4, 0x08, 0xe9, 0x67, 0x63, 0x00, 0x00]
theorem c1360_0 : ∀ feat, Dec feat c1360 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c1360_4 : ∀ feat, Dec feat c1360 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c1360_8 : ∀ feat, Dec feat c1360 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3543137 0)] 7) :=
  by dec_rfl
theorem c1360_15 : ∀ feat, Dec feat c1360 15 (FV7z.mk .call 64 [.rel 1778812] 5) :=
  by dec_rfl
theorem c1360_20 : ∀ feat, Dec feat c1360 20 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3543093 0)] 7) :=
  by dec_rfl
theorem c1360_27 : ∀ feat, Dec feat c1360 27 (FV7z.mk .call 64 [.rel 247776] 5) :=
  by dec_rfl
theorem c1360_32 : ∀ feat, Dec feat c1360 32 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c1360_36 : ∀ feat, Dec feat c1360 36 (FV7z.mk .jmp 64 [.rel 25447] 5) :=
  by dec_rfl
theorem v1360 : c1360 <+: sti.drop 1360 := by decide +kernel
theorem tg67 : csuTg 67 = sti_at.add 1360 := by decide +kernel
theorem pq1360 (prof : Profile) : BlkA prof c1360 (0x41c690 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c1360_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c1360_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 8
theorem pb1360 (prof : Profile) : BlkA prof sti sti_at 1360 1368 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq1360 prof).shift (by decide) v1360
theorem lq1360_8 (prof : Profile) : BlkA prof c1360 (0x41c690 : Addr) 8 15 [Op.mov 64 7 (.i 7853824)] :=
  .cons (c1360_8 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 15
theorem lb1360_8 (prof : Profile) : BlkA prof sti sti_at 1368 1375 [Op.mov 64 7 (.i 7853824)] :=
  (lq1360_8 prof).shift (by decide) v1360
theorem ld1360_8 (feat : Features) : Dec feat sti 1375 (FV7z.mk .call 64 [.rel 1778812] 5) :=
  Dec.shift (j := 1360) (k := 15) (c1360_15 feat) v1360 (by decide)
theorem lq1360_20 (prof : Profile) : BlkA prof c1360 (0x41c690 : Addr) 20 27 [Op.mov 64 7 (.i 7853792)] :=
  .cons (c1360_20 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 27
theorem lb1360_20 (prof : Profile) : BlkA prof sti sti_at 1380 1387 [Op.mov 64 7 (.i 7853792)] :=
  (lq1360_20 prof).shift (by decide) v1360
theorem ld1360_20 (feat : Features) : Dec feat sti 1387 (FV7z.mk .call 64 [.rel 247776] 5) :=
  Dec.shift (j := 1360) (k := 27) (c1360_27 feat) v1360 (by decide)
theorem aq1360 (prof : Profile) : BlkA prof c1360 (0x41c690 : Addr) 32 36 [Op.add 64 4 (.i 8)] :=
  .cons (c1360_32 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 36
theorem ab1360 (prof : Profile) : BlkA prof sti sti_at 1392 1396 [Op.add 64 4 (.i 8)] :=
  (aq1360 prof).shift (by decide) v1360
theorem jd1360 (feat : Features) : Dec feat sti 1396 (FV7z.mk .jmp 64 [.rel 25447] 5) :=
  Dec.shift (j := 1360) (k := 36) (c1360_36 feat) v1360 (by decide)
theorem cs1360 (prof : Profile) : CallsMid prof 1368 [(0, 7853824), (2, 7853792)] 1392 :=
  CallsMid.mid (lb1360_8 prof) (ld1360_8 _) (sti_lt (by decide)) (by decide) <|
  CallsMid.mid (lb1360_20 prof) (ld1360_20 _) (sti_lt (by decide)) (by decide) CallsMid.nil

theorem calls67 : calls 67 = [(0, 7853824), (2, 7853792)] := by decide +kernel

/-- The two registrars' tables have room for the calls. -/
theorem fits67 : Fits (regsAt 67) [(0, 7853824), (2, 7853792)] := by
  have h := fits_all 67 (by decide)
  rw [calls67] at h
  exact fits_of h

/-- What `z7_Black2sp_Prepare` writes: its function pointers and flags. -/
def w67 : List Rgn := [⟨0x792148, 8⟩, ⟨0x792140, 8⟩, ⟨0x796798, 8⟩, ⟨0x796790, 8⟩, ⟨0x796788, 4⟩]

theorem wrA67 : ∀ x ∈ wrOf w67, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel

/-- `csuTg 67` for `Jg`, its spec `wrSpec (wrOf w67)`: `G` goes from `67` to `68` by the calls and what
`z7_Black2sp_Prepare` leaves (`hG`). -/
theorem runs67_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) (hinE : CodeIn L 0x422a20 b2s)
    (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8 - 8) i)) (hWl : ∀ y, Foot w67 y → Foot Wl y)
    (hspec : spec 67 = wrSpec (wrOf w67)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 67 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w67, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W U U' : Addr → Byte), CallOut (sp - 64#64) [(0, 7853824), (2, 7853792)] W U →
      b2Ok prof Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w67 y → U' y = U y) →
      Agree F Z.proc.mm.mem U' → G 67 W → G 68 U') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 67 (csuTg 67) := by
  have hS := hP.hi
  have n := Csu.sp_n (show 64 ≤ sp.toNat by omega)
  refine callsK_runs c hC hin tg67 (pb1360 prof) (cs1360 prof) (ab1360 prof) (jd1360 _) (sti_lt (by decide))
    (by decide) hinE (by decide +kernel) hR hinR hst (by omega) fun _ _ _ => ?_
  refine prepK_core (k := 120) (Wc := w67) (Rc := []) c hC
    (black2spPrepareK prof hP.pc hinE hinS hinA2 hinA hinM hinC) hP.df hP.x87 hP.al (by decide) hS hP.stk hWl
    (lo_canary hP.can) hP.rf1 (fun Y hs hr => ?_) (lo_wrOf (by have h := hB 67; rw [hspec] at h; exact h)) wrA67
    fun _ Z U U' hpost hU' hAZ hI => ?_
  · obtain ⟨h1, h2⟩ := hP.can' hs hr
    unfold b2Pre
    omega
  · rcases hI with ⟨-, W, hW, hO⟩ | ⟨h, -⟩
    · exact Or.inr ⟨by omega, jg_callsK (by decide) (by rw [n]; omega) hS calls67 fits67 hspec hD hT hB hXw hO
        (fun a ha hw => hU' a hw fun hy => ha (foot_wrOf hy)) (hG Z W U U' hO hpost hU' hAZ) hW⟩
    · exact absurd rfl h

end FV7z.Ctor
