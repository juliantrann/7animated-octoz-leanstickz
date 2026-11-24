import FV7z.Ctor.Mix
import FV7z.Ctor.PrepC
/-!
# `csuTg 67` and `csuTg 77`: registrar calls and a `*Prepare` function (PLAN.md §M, constructors)

`csuTg 67` (offset 1360 of `sti`, `0x41c690`) is `endbr64; sub rsp, 8; lea rdi, [rip + d₁]; call RegisterArc;
lea rdi, [rip + d₂]; call RegisterHasher; add rsp, 8; jmp 0x422a20`: `callsK_runs` of `prepK_core` with
`z7_Black2sp_Prepare`'s contract by `fnK` (`Prepare/K.lean`). Its bytes, decodings and stretches follow the pattern
of `Chains.lean` (`tools/ctor_gen.py`); its spec is `wrSpec` of the globals the function writes.

`csuTg 77` (offset 1776, `0x41c830`) is `endbr64; sub rsp, 8; call z7_SwapBytesPrepare; lea rdi, [rip + d₁];
call RegisterCodec; lea rdi, [rip + d₂]; add rsp, 8; jmp RegisterCodec`: `callK_chain_runs` with the function's
contract (`prepK_sub`), `Jg` by `jg_kchain`.
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

/-! ## `csuTg 77`: `call z7_SwapBytesPrepare`, then two `RegisterCodec` calls -/

/-- `csuTg 77`, at `0x41c830`: `call 0x43d3d0`, `RegisterCodec (0x77e000)`, `RegisterCodec (0x77e028)`. -/
def c1776 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0xe8, 0x93, 0x0b, 0x02, 0x00, 0x48, 0x8d, 0x3d,
  0xbc, 0x17, 0x36, 0x00, 0xe8, 0x17, 0xc6, 0x03, 0x00, 0x48, 0x8d, 0x3d, 0xd8, 0x17, 0x36, 0x00,
  0x48, 0x83, 0xc4, 0x08, 0xe9, 0x07, 0xc6, 0x03, 0x00]
theorem c1776_0 : ∀ feat, Dec feat c1776 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c1776_4 : ∀ feat, Dec feat c1776 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c1776_8 : ∀ feat, Dec feat c1776 8 (FV7z.mk .call 64 [.rel 134035] 5) :=
  by dec_rfl
theorem c1776_13 : ∀ feat, Dec feat c1776 13 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3545020 0)] 7) :=
  by dec_rfl
theorem c1776_20 : ∀ feat, Dec feat c1776 20 (FV7z.mk .call 64 [.rel 247319] 5) :=
  by dec_rfl
theorem c1776_25 : ∀ feat, Dec feat c1776 25 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3545048 0)] 7) :=
  by dec_rfl
theorem c1776_32 : ∀ feat, Dec feat c1776 32 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c1776_36 : ∀ feat, Dec feat c1776 36 (FV7z.mk .jmp 64 [.rel 247303] 5) :=
  by dec_rfl
theorem v1776 : c1776 <+: sti.drop 1776 := by decide +kernel
theorem tg77 : csuTg 77 = sti_at.add 1776 := by decide +kernel
theorem pq1776 (prof : Profile) : BlkA prof c1776 (0x41c830 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c1776_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c1776_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 8
theorem pb1776 (prof : Profile) : BlkA prof sti sti_at 1776 1784 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq1776 prof).shift (by decide) v1776
theorem cd1776 (feat : Features) : Dec feat sti 1784 (FV7z.mk .call 64 [.rel 134035] 5) :=
  Dec.shift (j := 1776) (k := 8) (c1776_8 feat) v1776 (by decide)
theorem lq1776_13 (prof : Profile) : BlkA prof c1776 (0x41c830 : Addr) 13 20 [Op.mov 64 7 (.i 7856128)] :=
  .cons (c1776_13 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 20
theorem lb1776_13 (prof : Profile) : BlkA prof sti sti_at 1789 1796 [Op.mov 64 7 (.i 7856128)] :=
  (lq1776_13 prof).shift (by decide) v1776
theorem ld1776_13 (feat : Features) : Dec feat sti 1796 (FV7z.mk .call 64 [.rel 247319] 5) :=
  Dec.shift (j := 1776) (k := 20) (c1776_20 feat) v1776 (by decide)
theorem lq1776_25 (prof : Profile) :
    BlkA prof c1776 (0x41c830 : Addr) 25 36 [Op.mov 64 7 (.i 7856168), Op.add 64 4 (.i 8)] :=
  .cons (c1776_25 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c1776_32 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 36
theorem lb1776_25 (prof : Profile) :
    BlkA prof sti sti_at 1801 1812 [Op.mov 64 7 (.i 7856168), Op.add 64 4 (.i 8)] :=
  (lq1776_25 prof).shift (by decide) v1776
theorem ld1776_25 (feat : Features) : Dec feat sti 1812 (FV7z.mk .jmp 64 [.rel 247303] 5) :=
  Dec.shift (j := 1776) (k := 36) (c1776_36 feat) v1776 (by decide)
theorem cs1776 (prof : Profile) : CallsAt prof 1789 [(1, 7856128), (1, 7856168)] :=
  CallsAt.mid (lb1776_13 prof) (ld1776_13 _) (sti_lt (by decide)) (by decide) <|
  CallsAt.last (lb1776_25 prof) (ld1776_25 _) (sti_lt (by decide)) (by decide)
theorem calls77 : calls 77 = [(1, 7856128), (1, 7856168)] := by decide +kernel
/-- `RegisterCodec`'s table has room for the two calls. -/
theorem fits77 : Fits (regsAt 77) [(1, 7856128), (1, 7856168)] := by
  have h := fits_all 77 (by decide)
  rw [calls77] at h
  exact fits_of h
/-- What `z7_SwapBytesPrepare` writes: `g_SwapBytes_Mode`. -/
def w77 : List Rgn := [⟨0x7967b8, 4⟩]
theorem wrA77 : ∀ x ∈ wrOf w77, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel

/-- `csuTg 77` for `Jg`, its spec `wrSpec (wrOf w77)`: `G` goes from `77` to `78` by what `z7_SwapBytesPrepare`
leaves and then the calls (`hG`). -/
theorem runs77_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) (hinE : CodeIn L 0x43d3d0 swap)
    (hinS : CodeIn L 0x424340 ssse3) (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8 - 8) i)) (hWl : ∀ y, Foot w77 y → Foot Wl y)
    (hspec : spec 77 = wrSpec (wrOf w77)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 77 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w77, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W U U' : Addr → Byte), swOk prof Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w77 y → U y = W y) →
      Agree F Z.proc.mm.mem U → ChainOut (sp - 64#64) [(1, 7856128), (1, 7856168)] U U' → G 77 W → G 78 U') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 77 (csuTg 77) := by
  have hS := hP.hi
  have n := Csu.sp_n (show 64 ≤ sp.toNat by omega)
  have e80 : (sp - 64#64 - 8 - 8).toNat = sp.toNat - 80 := by rw [sub16 _ (by rw [n]; omega), n]; omega
  have hlo : Lo (sp.toNat - 1024) w77 := lo_wrOf (by have h := hB 77; rw [hspec] at h; exact h)
  have hws : ∀ Y : State, Y.cpu.gpr.rsp = sp - 64#64 - 8 - 8 → ∀ y, Foot (ws 120 swW Y) y →
      (sp.toNat - 200 ≤ y.toNat ∧ y.toNat < sp.toNat - 80) ∨ Foot w77 y := fun Y hYs y hy => by
    rcases prepK_ws (Wc := w77) hYs (by rw [e80]; omega) hy with h | h
    · rw [e80] at h
      exact .inl (by omega)
    · exact .inr h
  refine callK_chain_runs (k := 120) c hC hin tg77 (pb1776 prof) (cd1776 _) (sti_lt (by decide)) (by decide)
    hinE (by decide +kernel) (swapBytesPrepareK prof hP.pc hinE hinS hinA2 hinA hinM hinC) hP.df hP.x87 hP.al
    (cs1776 prof) hR hinR hst (by omega) (fun Y hK hYs => ?_) fun Y Z U U₁ U' hYs hI hpost hU hAZ hO => ?_
  · obtain ⟨hsub, hwl, hap⟩ := prepK_sub (D := sp - 64#64 - 8 - 8) (k := 120) (Wc := w77) (Rc := []) (pre := swPre)
      (post := fun _ Y => swOk prof Y) c (by rw [e80]; omega) (by rw [e80]; omega) hP.stk hWl (lo_canary hP.can)
      hP.rf1 hlo hK hYs
    refine ⟨hsub, hwl, ?_, fun i hi hm => ?_, hap, fun y hy => ?_⟩
    · have hc := hP.can
      unfold swPre
      rw [hYs, e80, hK.seg]
      omega
    · have h1 := hlo.foot hm
      have e := toNat_add_of_fits (a := sp - 64#64 - 8 - 8) hi (by rw [e80]; omega)
      rw [hYs, e, e80] at h1
      omega
    · rcases hws Y hYs y hy with h | h
      · exact ⟨by omega, by omega⟩
      · have h1 := hlo.foot h
        have h2 := InR_apart wrA77 (foot_wrOf h)
        exact ⟨by omega, by omega⟩
  · have hw : ∀ a : Addr, ¬ (sp.toNat - 1024 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) → ¬ Foot w77 a → U₁ a = U a :=
      fun a h2 h1 => hU a (fun hy => by
        rcases hws Y hYs a hy with h | h
        · exact h2 ⟨by omega, by omega⟩
        · exact h1 h) fun h => h2 ⟨by omega, by omega⟩
    exact jg_kchain (by decide) (by rw [n]; omega) hS calls77 fits77 hspec hD hT hB hXw
      (fun a ha hw' => hw a hw' fun hy => ha (foot_wrOf hy)) hO (hG Z U U₁ U' hpost hw hAZ hO) hI

end FV7z.Ctor
