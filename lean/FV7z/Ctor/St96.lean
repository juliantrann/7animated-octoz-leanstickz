import FV7z.Ctor.AtCtor
import FV7z.Ctor.BlkRet
/-!
# A constructor that copies a global into a static object (PLAN.md §M, constructors)

`csuTg 96`, at `0x41cc30` (offset 2800 of `sti`), stores the word at `0x792978` to `0x79ed50` and `-1` to the
dword at `0x79ed58`, then returns:

```
endbr64; mov rax, 0x792978; mov rdx, [rax]; mov rax, 0x79ed50; mov [rax], rdx; mov dword [rax + 8], -1; ret
```

- `st96 V`: the bytes after; `st96_out`: the same as `V` apart from `[0x79ed50, 0x79ed5c)`.
- `runs96`: `csuTg 96` is a function as `Csu.csu_ok` asks, for an invariant the step from `96` to `97` takes
  through `st96`.
- `spec96 V`: what it stores (`[0x79ed50, 0x79ed5c)`) and leaves there (`post96`: the word of `V` at `0x792978`,
  then `-1`); `jg96`: `Jg` goes from `96` to `97` through `st96`; `runs96_jg`: `runs96` for `Jg`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 96`. -/
def c96 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x78, 0x29, 0x79, 0x00, 0x48, 0x8b, 0x10, 0x48, 0xc7,
  0xc0, 0x50, 0xed, 0x79, 0x00, 0x48, 0x89, 0x10, 0xc7, 0x40, 0x08, 0xff, 0xff, 0xff, 0xff, 0xc3]
theorem c96_0 : ∀ feat, Dec feat c96 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c96_4 : ∀ feat, Dec feat c96 4 (FV7z.mk .mov 64 [gr 64 0, .imm 64 7940472] 7) := by dec_rfl
theorem c96_11 : ∀ feat, Dec feat c96 11 (FV7z.mk .mov 64 [gr 64 2, .mem (mbd 0 0 64)] 3) := by dec_rfl
theorem c96_14 : ∀ feat, Dec feat c96 14 (FV7z.mk .mov 64 [gr 64 0, .imm 64 7990608] 7) := by dec_rfl
theorem c96_21 : ∀ feat, Dec feat c96 21 (FV7z.mk .mov 64 [.mem (mbd 0 0 64), gr 64 2] 3) := by dec_rfl
theorem c96_24 : ∀ feat, Dec feat c96 24 (FV7z.mk .mov 32 [.mem (mbd 0 8 32), .imm 32 4294967295] 7) := by
  dec_rfl
theorem c96_31 : ∀ feat, Dec feat c96 31 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v96 : c96 <+: sti.drop 2800 := by decide +kernel
theorem tg96 : csuTg 96 = sti_at.add 2800 := by decide +kernel

/-- The bytes after `csuTg 96`. -/
def st96 (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst V 7990608#64 (toBytesLE rdq(V, 7940472#64) 8)) 7990616#64 (toBytesLE (BitVec.ofNat 32 4294967295) 4)

theorem st96_out (V : Addr → Byte) (a : Addr) (h : a.toNat < 7990608 ∨ 7990620 ≤ a.toNat) : st96 V a = V a := by
  have e1 : (7990608#64 : Addr).toNat = 7990608 := rfl
  have e2 : (7990616#64 : Addr).toNat = 7990616 := rfl
  unfold st96
  rw [Tun.Vst_out _ _ _ a (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ a (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- `csuTg 96` is a function as `Csu.csu_ok` asks, for an invariant the step from `96` to `97` takes through
`st96`, with the word it reads in the data footprint and the twelve bytes it writes in `Wl`. -/
theorem runs96 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hl : ∀ i < 8, Foot F.data (Addr.add 7940472#64 i)) (hw8 : ∀ i < 8, Foot Wl (Addr.add 7990608#64 i))
    (hw4 : ∀ i < 4, Foot Wl (Addr.add 7990616#64 i)) (hsp : 7990620 + 64 ≤ sp.toNat)
    (hJ : ∀ V, J 96 V → J 97 (st96 V)) : Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 96 (csuTg 96) := by
  intro X t V j₂ hK hA hI hr hsp' _ hj₂ hra k
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  refine c.s_endbr hK hA hin (sti_lt (by decide)) (hr.trans tg96)
    (Dec.shift (j := 2800) (k := 0) (c96_0 _) v96 (by decide)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_ri64 hK1 hA1 hin (sti_lt (by decide)) hr1
    (Dec.shift (j := 2800) (k := 4) (c96_4 _) v96 (by decide)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have e2 : eaD Y2 0 0 = 7940472#64 := by
    show Y2.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 0 = _
    rw [hg2]
    rfl
  refine c.s_mov_rm hK2 hA2 hin (sti_lt (by decide)) hr2 (.inr rfl)
    (Dec.shift (j := 2800) (k := 11) (c96_11 _) v96 (by decide)) (fun i hi => by rw [e2]; exact hl i hi) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_ri64 hK3 hA3 hin (sti_lt (by decide)) hr3
    (Dec.shift (j := 2800) (k := 14) (c96_14 _) v96 (by decide)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have e4 : eaD Y4 0 0 = 7990608#64 := by
    show Y4.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 0 = _
    rw [hg4]
    rfl
  have v4 : rv Y4 64 2 = rdq(V, 7940472#64) := by
    show (Y4.cpu.gpr.get (regOf 2)).setWidth 64 = _
    rw [hg4, hg3]
    show ((ofBytesLE 64 (List.map V (byteAddrs (eaD Y2 0 0) 8))).setWidth 64).setWidth 64 = _
    rw [e2, BitVec.setWidth_eq, BitVec.setWidth_eq]
  refine c.s_mov_mr hK4 hA4 hin (sti_lt (by decide)) hr4 (.inr rfl)
    (Dec.shift (j := 2800) (k := 21) (c96_21 _) v96 (by decide)) (fun i hi => by rw [e4]; exact hw8 i hi) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have e5 : eaD Y5 0 8 = 7990616#64 := by
    show Y5.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
    rw [hg5, hg4]
    rfl
  refine c.s_mov_mi32 hK5 hA5 hin (sti_lt (by decide)) hr5
    (Dec.shift (j := 2800) (k := 24) (c96_24 _) v96 (by decide)) (fun i hi => by rw [e5]; exact hw4 i hi) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  rw [e5, e4, v4] at hA6
  change Agree F Y6.proc.mm.mem (st96 V) at hA6
  have hs6 : Y6.cpu.gpr.rsp = sp - 64#64 := by
    rw [hg6, hg5, hg4, hg3, hg2, hg1]
    exact hsp'
  have hl6 : ∀ i < 8, Foot F.data (Addr.add Y6.cpu.gpr.rsp i) := fun i hi => by
    rw [hs6]
    exact c.hws _ (hC.st i (by omega))
  have hra6 : rdq(st96 V, Y6.cpu.gpr.rsp) = Csu.csu_at.add j₂ := by
    rw [hs6, ← hra]
    exact rdq_eq (by omega) fun a h1 h2 => st96_out V a (by omega)
  refine c.s_ret hK6 hA6 hin (sti_lt (by decide)) hr6 (Dec.shift (j := 2800) (k := 31) (c96_31 _) v96 (by decide))
    hl6 hC.code hj₂ hra6 ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' (st96 V) hKZ hAZ (hJ V hI) (fun a ha => st96_out V a (by omega))
    (fun a ha => st96_out V a (by omega)) hrZ ?_
  rw [hgZ, hg6, hg5, hg4, hg3, hg2, hg1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What `csuTg 96` leaves: the word of `V` at `0x792978` at `0x79ed50`, `-1` at `0x79ed58`. -/
def post96 (V W : Addr → Byte) : Prop :=
  rdq(W, 7990608#64) = rdq(V, 7940472#64) ∧ rdd(W, 7990616#64) = BitVec.ofNat 32 4294967295

/-- What `csuTg 96` stores and leaves. -/
def spec96 (V : Addr → Byte) : CSpec := ⟨[(7990608, 7990620)], post96 V⟩

theorem calls96 : calls 96 = [] := by decide +kernel

theorem wr96 : ∀ x ∈ [((7990608 : Nat), (7990620 : Nat))], ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

theorem dep96 (V : Addr → Byte) : (spec96 V).Dep := by
  rintro W W' h ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · exact (rdq_at (by decide) fun a _h4 _h5 => h a (by simp only [spec96, InR]; omega)).trans h1
  · exact (rdd_at (by decide) fun a _h4 _h5 => h a (by simp only [spec96, InR]; omega)).trans h2

theorem post96_st {V W : Addr → Byte} (hW : rdq(W, 7940472#64) = rdq(V, 7940472#64)) : post96 V (st96 W) := by
  have h1 : rdq(st96 W, 7990608#64) = rdq(Vst W 7990608#64 (toBytesLE rdq(W, 7940472#64) 8), 7990608#64) :=
    rdq_at (by decide) fun a _ h => vo (by decide) (Or.inl (by omega))
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (rd_st (w := 64) (n := 8) rfl _ (by decide)).trans hW
  · unfold st96
    exact rd_st (w := 32) (n := 4) rfl _ (by decide)

/-- `Jg` from `96` to `97` through `st96`, for `spec 96 = spec96 V`, the stores of the constructors before apart
from the word `csuTg 96` reads and from what it writes, and `G` taken along. -/
theorem jg96 {V W : Addr → Byte} {sp : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    (hspec : spec 96 = spec96 V) (hD : ∀ k, (spec k).Dep)
    (hX : ∀ k, 3 ≤ k → k < 96 → ∀ x ∈ (spec k).wr, ∀ y ∈ [(7940472, 7940480), (7990608, 7990620)],
      x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hsp : 7990620 + 136 ≤ sp) (hG : G 96 W → G 97 (st96 W)) (hJ : Jg V sp spec G 96 W) :
    Jg V sp spec G 97 (st96 W) := by
  obtain ⟨hJc, hG'⟩ := hJ
  have hrd : rdq(W, 7940472#64) = rdq(V, 7940472#64) :=
    rdq_at (by decide) fun a _h4 _h5 => hJc.2.1 a (by omega) (by unfold Pre; omega) (by omega)
      fun k hk hkm hin => InR_sep hin (hX k hk hkm) (by simp only [InR]; omega)
  refine ⟨Jc_st (by decide) calls96 hD (by rw [hspec]; exact wr96) (fun k hk hkm x hx y hy => ?_) hJc
    (fun a ha => st96_out W a ?_) (by rw [hspec]; exact post96_st hrd), hG hG'⟩
  · rw [hspec] at hy
    exact hX k hk hkm x hx y (List.mem_cons_of_mem _ hy)
  · rw [hspec] at ha
    simp only [spec96, InR] at ha
    omega

/-- `runs96` for `Jg`. -/
theorem runs96_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hl : ∀ i < 8, Foot F.data (Addr.add 7940472#64 i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add 7990608#64 i)) (hw4 : ∀ i < 4, Foot Wl (Addr.add 7990616#64 i))
    (hsp : 7990620 + 136 ≤ sp.toNat) (hspec : spec 96 = spec96 V) (hD : ∀ k, (spec k).Dep)
    (hX : ∀ k, 3 ≤ k → k < 96 → ∀ x ∈ (spec k).wr, ∀ y ∈ [(7940472, 7940480), (7990608, 7990620)],
      x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W, G 96 W → G 97 (st96 W)) :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 96 (csuTg 96) :=
  runs96 c hC hin hl hw8 hw4 (by omega) fun W hJ => jg96 hspec hD hX (by omega) (hG W) hJ

end FV7z.Ctor
