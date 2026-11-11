import FV7z.Spec.Glibc
import FV7z.Lemmas.FnSteps
/-!
# What `init_cpu_features` keeps true of `_dl_x86_cpu_features` (PLAN.md G2, "Dispatch theo CPUID", glibc)

`Glibc.CpuOk`, on the bytes of the footprint (`V`, `Agree`) instead of memory: `CInv prof V`. Every word of
`_dl_x86_cpu_features` starts at 0 (`.bss`), where it holds, and each store of `init_cpu_features` keeps it: a
`CPUID` word some CPU answered (`st_ecx1`, …), or a `feature` word whose bits meet `F`, or a word elsewhere
(`st_apart`). At the end, `Agree` turns it into `CpuOk` of memory (`CInv.cpuOk`).
-/
namespace FV7z.CpuFeat
open ZellicX86 Glibc

variable {prof : Profile}
set_option linter.deprecated false

theorem tn {a : Addr} {i : Nat} (h : a.toNat + i < 2 ^ 64) : (a.add i).toNat = a.toNat + i :=
  toNat_add_of_fits (n := i + 1) (by omega) (by omega)

theorem base_toNat : (0x7a4ae0 : Addr).toNat = 0x7a4ae0 := rfl

/-- Bit `i` of the little-endian word at offset `a` of `cpuRgn`, in the footprint's bytes `V` (`Glibc.bit`). -/
def bitV (V : Addr → Byte) (a i : Nat) : Bool := (V (cpuRgn.base.add (a + i / 8))).getLsbD (i % 8)

/-- What `CpuOk` asks of the two `feature` words, `f0` (`feature[0]`) and `f1` (`feature[1]`), as bits. -/
structure F (prof : Profile) (f0 f1 : Nat → Bool) : Prop where
  avx : f0 0 = true → prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx
  avx2 : f0 1 = true → f0 0 = true ∧ prof.reports 7 0 (·.ebx) 5
  avx512f : f0 2 = true → prof.reports 7 0 (·.ebx) 16 ∧ prof.enabled xcr0Avx512
  avx512vl : f0 6 = true → f0 2 = true ∧ prof.reports 7 0 (·.ebx) 31
  avx512dq : f0 7 = true → f0 2 = true ∧ prof.reports 7 0 (·.ebx) 17
  avx512bw : f0 8 = true → f0 2 = true ∧ prof.reports 7 0 (·.ebx) 30
  fma : f0 17 = true → f0 0 = true ∧ prof.reports 1 0 (·.ecx) 12
  vaes : f0 19 = true → f0 0 = true ∧ prof.reports 7 0 (·.ecx) 9
  fastAvx : f1 8 = true → f0 1 = true

/-- `CpuOk` of the bytes `V`. -/
structure CInv (prof : Profile) (V : Addr → Byte) : Prop where
  ecx1 : ∀ i < 32, bitV V 8 i = true → prof.reports 1 0 (·.ecx) i
  edx1 : ∀ i < 32, bitV V 12 i = true → prof.reports 1 0 (·.edx) i
  ebx7 : ∀ i < 32, bitV V 20 i = true → prof.reports 7 0 (·.ebx) i
  ecx7 : ∀ i < 32, bitV V 24 i = true → prof.reports 7 0 (·.ecx) i
  f : F prof (bitV V 96) (bitV V 100)

theorem CInv.cpuOk {m : Memory} (h : CInv prof fun a => m.readByte a) : CpuOk prof m :=
  ⟨h.ecx1, h.edx1, h.ebx7, h.ecx7, h.f.avx, h.f.avx2, h.f.avx512f, h.f.avx512vl, h.f.avx512dq, h.f.avx512bw,
    h.f.fma, h.f.vaes, h.f.fastAvx⟩

/-- The words `CInv` reads: offsets 8, 12, 20, 24, 96, 100. -/
def Watched (a : Nat) : Prop := a = 8 ∨ a = 12 ∨ a = 20 ∨ a = 24 ∨ a = 96 ∨ a = 100

/-- `CInv` of other bytes with the same watched bits. -/
theorem CInv.congr {V V' : Addr → Byte} (h : CInv prof V)
    (he : ∀ a i, Watched a → i < 32 → bitV V' a i = bitV V a i) : CInv prof V' := by
  have e := fun a i (ha : Watched a) (hi : i < 32) => he a i ha hi
  refine ⟨fun i hi => by rw [e 8 i (by simp [Watched]) hi]; exact h.ecx1 i hi,
    fun i hi => by rw [e 12 i (by simp [Watched]) hi]; exact h.edx1 i hi,
    fun i hi => by rw [e 20 i (by simp [Watched]) hi]; exact h.ebx7 i hi,
    fun i hi => by rw [e 24 i (by simp [Watched]) hi]; exact h.ecx7 i hi, ?_⟩
  have e0 := fun i (hi : i < 32) => e 96 i (by simp [Watched]) hi
  have e1 := fun i (hi : i < 32) => e 100 i (by simp [Watched]) hi
  have := h.f.avx; have := h.f.avx2; have := h.f.avx512f; have := h.f.avx512vl; have := h.f.avx512dq
  have := h.f.avx512bw; have := h.f.fma; have := h.f.vaes; have := h.f.fastAvx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e0 0 (by omega), e0 1 (by omega), e0 2 (by omega), e0 6 (by omega), e0 7 (by omega),
      e0 8 (by omega), e0 17 (by omega), e0 19 (by omega), e1 8 (by omega)] <;> assumption

/-- `CpuOk` of memory from `CInv` of bytes it agrees with on `cpuRgn`. -/
theorem CInv.mem {V : Addr → Byte} {m : Memory} (h : CInv prof V)
    (hm : ∀ j < 104, m.readByte (cpuRgn.base.add j) = V (cpuRgn.base.add j)) : CpuOk prof m :=
  CInv.cpuOk (h.congr fun a i ha hi => by
    unfold bitV; dsimp only; rw [hm _ (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)])

/-! ## Stores -/

theorem Vst_at (bs : List Byte) (V : Addr → Byte) (g : Addr) {j : Nat} (hj : j < bs.length)
    (hf : g.toNat + bs.length ≤ 2 ^ 64) : Vst V g bs (g.add j) = bs[j] := by
  have h := congrArg (fun l => l[j]?) (Vst_self bs V g hf)
  simp only [byteAddrs, List.map_map, List.getElem?_map, List.getElem?_range hj] at h
  simpa [List.getElem?_eq_getElem hj] using h

theorem cpuRgn_base : cpuRgn.base = 0x7a4ae0 := rfl

/-- A word stored at offset `a`: its bits. -/
theorem bitV_st_self {V : Addr → Byte} {a i : Nat} (w : BitVec 32) (ha : a + 4 ≤ 104) (hi : i < 32) :
    bitV (Vst V (cpuRgn.base.add a) (toBytesLE w 4)) a i = w.getLsbD i := by
  have h4 : i / 8 < 4 := by omega
  unfold bitV
  rw [← addr_add_add, Vst_at _ _ _ (by simpa using h4)
    (by rw [toBytesLE_length, cpuRgn_base, tn (by rw [base_toNat]; omega), base_toNat]; omega)]
  simp only [toBytesLE, List.getElem_map, List.getElem_range, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have h2 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  rw [show 8 * (i / 8) + i % 8 = i by omega]
  simp [h2]

/-- A store of `n` bytes at `g`, apart from the word at offset `a`, keeps its bits. -/
theorem bitV_st_apart {V : Addr → Byte} {a i : Nat} (bs : List Byte) (g : Addr) (hi : i < 32) (ha : a + 4 ≤ 104)
    (hg : g.toNat + bs.length ≤ 2 ^ 64)
    (hap : 0x7a4ae0 + a + 4 ≤ g.toNat ∨ g.toNat + bs.length ≤ 0x7a4ae0 + a) :
    bitV (Vst V g bs) a i = bitV V a i := by
  unfold bitV
  rw [Vst_apart _ _ _ _ fun j hj he => ?_]
  have h1 := congrArg BitVec.toNat he
  rw [cpuRgn_base, tn (by rw [base_toNat]; omega), base_toNat, tn (by omega)] at h1
  omega

/-- The bits of the word at offset `a` as a load reads it. -/
theorem getLsbD_rd {V : Addr → Byte} {a i : Nat} (hi : i < 32) :
    (ofBytesLE 32 ((byteAddrs (cpuRgn.base.add a) 4).map V)).getLsbD i = bitV V a i := by
  have h4 : i / 8 < 4 := by omega
  rw [getLsbD_ofBytesLE]
  simp only [hi, decide_true, List.length_map, byteAddrs, List.length_range, h4, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range h4]
  simp [bitV, addr_add_add]

/-- A store apart from the watched words keeps `CInv`. -/
theorem CInv.st_apart {V : Addr → Byte} (h : CInv prof V) (bs : List Byte) (g : Addr)
    (hg : g.toNat + bs.length ≤ 2 ^ 64)
    (hap : ∀ a, Watched a → 0x7a4ae0 + a + 4 ≤ g.toNat ∨ g.toNat + bs.length ≤ 0x7a4ae0 + a) :
    CInv prof (Vst V g bs) :=
  h.congr fun a i ha hi => bitV_st_apart bs g hi (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega) hg
    (hap a ha)

theorem watched_apart {a b : Nat} (ha : Watched a) (hb : Watched b) (h : a ≠ b) :
    0x7a4ae0 + a + 4 ≤ (cpuRgn.base.add b).toNat ∨ (cpuRgn.base.add b).toNat + 4 ≤ 0x7a4ae0 + a := by
  rw [cpuRgn_base, tn (by rw [base_toNat]; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), base_toNat]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem fits_w {b : Nat} (w : BitVec 32) (hb : Watched b) : (cpuRgn.base.add b).toNat + (toBytesLE w 4).length ≤ 2 ^ 64 := by
  rw [toBytesLE_length, cpuRgn_base, tn (by rw [base_toNat]; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> omega),
    base_toNat]
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The bits of watched word `a` after a store of `w` at watched word `b`. -/
theorem bitV_st_w {V : Addr → Byte} {a b i : Nat} (ha : Watched a) (hb : Watched b) (hi : i < 32) (w : BitVec 32) :
    bitV (Vst V (cpuRgn.base.add b) (toBytesLE w 4)) a i = if a = b then w.getLsbD i else bitV V a i := by
  split
  · subst a; exact bitV_st_self w (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega) hi
  · exact bitV_st_apart _ _ hi (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega) (fits_w w hb)
      (watched_apart ha hb (by assumption))

theorem w8 : Watched 8 := by simp [Watched]
theorem w12 : Watched 12 := by simp [Watched]
theorem w20 : Watched 20 := by simp [Watched]
theorem w24 : Watched 24 := by simp [Watched]
theorem w96 : Watched 96 := by simp [Watched]
theorem w100 : Watched 100 := by simp [Watched]

theorem F.congr {f0 f1 g0 g1 : Nat → Bool} (hF : F prof f0 f1) (h0 : ∀ i < 32, g0 i = f0 i)
    (h1 : ∀ i < 32, g1 i = f1 i) : F prof g0 g1 := by
  have := hF.avx; have := hF.avx2; have := hF.avx512f; have := hF.avx512vl; have := hF.avx512dq
  have := hF.avx512bw; have := hF.fma; have := hF.vaes; have := hF.fastAvx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h0 0 (by omega), h0 1 (by omega), h0 2 (by omega), h0 6 (by omega), h0 7 (by omega),
      h0 8 (by omega), h0 17 (by omega), h0 19 (by omega), h1 8 (by omega)] <;> assumption

/-- Storing a `CPUID` word at a watched offset other than the `feature` words: each bit set, `Reported`. -/
theorem CInv.st_cpuid {V : Addr → Byte} (h : CInv prof V) {b : Nat} (w : BitVec 32)
    (hb : b = 8 ∨ b = 12 ∨ b = 20 ∨ b = 24)
    (hw : ∀ i < 32, w.getLsbD i = true → (b = 8 → prof.reports 1 0 (·.ecx) i) ∧ (b = 12 → prof.reports 1 0 (·.edx) i)
      ∧ (b = 20 → prof.reports 7 0 (·.ebx) i) ∧ (b = 24 → prof.reports 7 0 (·.ecx) i)) :
    CInv prof (Vst V (cpuRgn.base.add b) (toBytesLE w 4)) := by
  have hb' : Watched b := by rcases hb with rfl | rfl | rfl | rfl <;> simp [Watched]
  have e := fun a i (ha : Watched a) (hi : i < 32) => bitV_st_w (V := V) ha hb' hi w
  refine ⟨fun i hi hx => ?_, fun i hi hx => ?_, fun i hi hx => ?_, fun i hi hx => ?_,
    h.f.congr (fun i hi => by rw [e 96 i w96 hi, if_neg (by omega)])
      (fun i hi => by rw [e 100 i w100 hi, if_neg (by omega)])⟩
  · rw [e 8 i w8 hi] at hx; split at hx
    · exact (hw i hi hx).1 (by omega)
    · exact h.ecx1 i hi hx
  · rw [e 12 i w12 hi] at hx; split at hx
    · exact (hw i hi hx).2.1 (by omega)
    · exact h.edx1 i hi hx
  · rw [e 20 i w20 hi] at hx; split at hx
    · exact (hw i hi hx).2.2.1 (by omega)
    · exact h.ebx7 i hi hx
  · rw [e 24 i w24 hi] at hx; split at hx
    · exact (hw i hi hx).2.2.2 (by omega)
    · exact h.ecx7 i hi hx

/-- Storing `feature[0]` (offset 96): its bits must meet `F` with `feature[1]`. -/
theorem CInv.st_f0 {V : Addr → Byte} (h : CInv prof V) (w : BitVec 32) (hw : F prof w.getLsbD (bitV V 100)) :
    CInv prof (Vst V (cpuRgn.base.add 96) (toBytesLE w 4)) := by
  have e := fun a i (ha : Watched a) (hi : i < 32) => bitV_st_w (V := V) ha w96 hi w
  exact ⟨fun i hi hx => h.ecx1 i hi (by rwa [e 8 i w8 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.edx1 i hi (by rwa [e 12 i w12 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ebx7 i hi (by rwa [e 20 i w20 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ecx7 i hi (by rwa [e 24 i w24 hi, if_neg (by omega)] at hx),
    hw.congr (fun i hi => by rw [e 96 i w96 hi, if_pos rfl]) (fun i hi => by rw [e 100 i w100 hi, if_neg (by omega)])⟩

/-- Storing `feature[1]` (offset 100). -/
theorem CInv.st_f1 {V : Addr → Byte} (h : CInv prof V) (w : BitVec 32) (hw : F prof (bitV V 96) w.getLsbD) :
    CInv prof (Vst V (cpuRgn.base.add 100) (toBytesLE w 4)) := by
  have e := fun a i (ha : Watched a) (hi : i < 32) => bitV_st_w (V := V) ha w100 hi w
  exact ⟨fun i hi hx => h.ecx1 i hi (by rwa [e 8 i w8 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.edx1 i hi (by rwa [e 12 i w12 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ebx7 i hi (by rwa [e 20 i w20 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ecx7 i hi (by rwa [e 24 i w24 hi, if_neg (by omega)] at hx),
    hw.congr (fun i hi => by rw [e 96 i w96 hi, if_neg (by omega)]) (fun i hi => by rw [e 100 i w100 hi, if_pos rfl])⟩

/-- `feature[1]`, then `feature[0]` (`update_usable` sets `AVX_Fast_Unaligned_Load` just before `AVX2_Usable`). -/
theorem CInv.st_f1_f0 {V : Addr → Byte} (h : CInv prof V) (w1 w0 : BitVec 32) (hw : F prof w0.getLsbD w1.getLsbD) :
    CInv prof (Vst (Vst V (cpuRgn.base.add 100) (toBytesLE w1 4)) (cpuRgn.base.add 96) (toBytesLE w0 4)) := by
  have e1 := fun a i (ha : Watched a) (hi : i < 32) => bitV_st_w (V := V) ha w100 hi w1
  have e0 := fun a i (ha : Watched a) (hi : i < 32) =>
    bitV_st_w (V := Vst V (cpuRgn.base.add 100) (toBytesLE w1 4)) ha w96 hi w0
  exact ⟨fun i hi hx => h.ecx1 i hi (by rwa [e0 8 i w8 hi, if_neg (by omega), e1 8 i w8 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.edx1 i hi (by rwa [e0 12 i w12 hi, if_neg (by omega), e1 12 i w12 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ebx7 i hi (by rwa [e0 20 i w20 hi, if_neg (by omega), e1 20 i w20 hi, if_neg (by omega)] at hx),
    fun i hi hx => h.ecx7 i hi (by rwa [e0 24 i w24 hi, if_neg (by omega), e1 24 i w24 hi, if_neg (by omega)] at hx),
    hw.congr (fun i hi => by rw [e0 96 i w96 hi, if_pos rfl])
      (fun i hi => by rw [e0 100 i w100 hi, if_neg (by omega), e1 100 i w100 hi, if_pos rfl])⟩

/-- `F` after setting bits `m0` of `feature[0]` and `m1` of `feature[1]`, each with its condition. -/
theorem F.or {f0 f1 g0 g1 m0 m1 : Nat → Bool} (hF : F prof f0 f1)
    (h0 : ∀ i, g0 i = (f0 i || m0 i)) (h1 : ∀ i, g1 i = (f1 i || m1 i))
    (a0 : m0 0 = true → prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx)
    (a1 : m0 1 = true → g0 0 = true ∧ prof.reports 7 0 (·.ebx) 5)
    (a2 : m0 2 = true → prof.reports 7 0 (·.ebx) 16 ∧ prof.enabled xcr0Avx512)
    (a6 : m0 6 = true → g0 2 = true ∧ prof.reports 7 0 (·.ebx) 31)
    (a7 : m0 7 = true → g0 2 = true ∧ prof.reports 7 0 (·.ebx) 17)
    (a8 : m0 8 = true → g0 2 = true ∧ prof.reports 7 0 (·.ebx) 30)
    (a17 : m0 17 = true → g0 0 = true ∧ prof.reports 1 0 (·.ecx) 12)
    (a19 : m0 19 = true → g0 0 = true ∧ prof.reports 7 0 (·.ecx) 9)
    (b8 : m1 8 = true → g0 1 = true) : F prof g0 g1 := by
  have lift : ∀ i, f0 i = true → g0 i = true := fun i h => by rw [h0, h, Bool.true_or]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hF.avx h
    · exact a0 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.avx2 h).1, (hF.avx2 h).2⟩
    · exact a1 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hF.avx512f h
    · exact a2 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.avx512vl h).1, (hF.avx512vl h).2⟩
    · exact a6 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.avx512dq h).1, (hF.avx512dq h).2⟩
    · exact a7 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.avx512bw h).1, (hF.avx512bw h).2⟩
    · exact a8 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.fma h).1, (hF.fma h).2⟩
    · exact a17 h
  · rw [h0, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lift _ (hF.vaes h).1, (hF.vaes h).2⟩
    · exact a19 h
  · rw [h1, Bool.or_eq_true] at h
    rcases h with h | h
    · exact lift _ (hF.fastAvx h)
    · exact b8 h

/-- Storing `feature[0]` with the bits `m` set beside the old ones, each with its condition. -/
theorem CInv.st_f0_or {V : Addr → Byte} (h : CInv prof V) (w : BitVec 32) (m : Nat → Bool)
    (hw : ∀ i < 32, w.getLsbD i = (bitV V 96 i || m i))
    (a0 : m 0 = true → prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx)
    (a1 : m 1 = true → (bitV V 96 0 || m 0) = true ∧ prof.reports 7 0 (·.ebx) 5)
    (a2 : m 2 = true → prof.reports 7 0 (·.ebx) 16 ∧ prof.enabled xcr0Avx512)
    (a6 : m 6 = true → (bitV V 96 2 || m 2) = true ∧ prof.reports 7 0 (·.ebx) 31)
    (a7 : m 7 = true → (bitV V 96 2 || m 2) = true ∧ prof.reports 7 0 (·.ebx) 17)
    (a8 : m 8 = true → (bitV V 96 2 || m 2) = true ∧ prof.reports 7 0 (·.ebx) 30)
    (a17 : m 17 = true → (bitV V 96 0 || m 0) = true ∧ prof.reports 1 0 (·.ecx) 12)
    (a19 : m 19 = true → (bitV V 96 0 || m 0) = true ∧ prof.reports 7 0 (·.ecx) 9) :
    CInv prof (Vst V (cpuRgn.base.add 96) (toBytesLE w 4)) :=
  h.st_f0 w ((F.or (g0 := fun i => bitV V 96 i || m i) (g1 := bitV V 100) (m1 := fun _ => false) h.f
    (fun _ => rfl) (fun _ => (Bool.or_false _).symm) a0 a1 a2 a6 a7 a8 a17 a19 (fun h => absurd h (by simp))).congr
    hw (fun _ _ => rfl))

/-- The bits of `feature[0]` after that store. -/
theorem bitV_f0_or {V : Addr → Byte} (w : BitVec 32) {m : Nat → Bool} (hw : ∀ i < 32, w.getLsbD i = (bitV V 96 i || m i))
    {i : Nat} (hi : i < 32) : bitV (Vst V (cpuRgn.base.add 96) (toBytesLE w 4)) 96 i = (bitV V 96 i || m i) := by
  rw [bitV_st_self w (by omega) hi, hw i hi]

/-- The bits of the `or` of the word at offset `a` and an immediate. -/
theorem getLsbD_rd_or {V : Addr → Byte} {a i : Nat} (imm : Nat) (hi : i < 32) :
    (ofBytesLE 32 ((byteAddrs (cpuRgn.base.add a) 4).map V) ||| BitVec.ofNat 32 imm).getLsbD i =
      (bitV V a i || (BitVec.ofNat 32 imm).getLsbD i) := by
  rw [BitVec.getLsbD_or, getLsbD_rd hi]

/-! ## Bits a branch tests -/

/-- `ZF` of `x & 2^k`. -/
theorem zf_bit {w : Nat} (x : BitVec w) {k m : Nat} (hm : m = 2 ^ k) (hk : k < w) :
    (x &&& BitVec.ofNat w m == 0) = !x.getLsbD k := by
  subst hm
  have hb : ∀ i, (BitVec.ofNat w (2 ^ k)).getLsbD i = decide (i = k) := by
    intro i
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases h : i = k
    · subst h; simp [hk]
    · simp only [h, decide_false]; simp [Ne.symm h]
  cases hx : x.getLsbD k
  · simp only [Bool.not_false, beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, hb]
    by_cases h : i = k
    · subst h; simp [hx]
    · simp [h]
  · simp only [Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h0
    have := congrArg (fun z => z.getLsbD k) h0
    simp only [BitVec.getLsbD_and, hb, hx, decide_true, Bool.and_true] at this
    simp at this

theorem bit_of_zf {w : Nat} {x : BitVec w} {k m : Nat} (hm : m = 2 ^ k) (hk : k < w)
    (h : (x &&& BitVec.ofNat w m == 0) = false) : x.getLsbD k = true := by
  rw [zf_bit x hm hk] at h; simpa using h

/-- The bits of a loaded word, zero-extended to 64. -/
theorem getLsbD_sw {x : BitVec 32} {i : Nat} (hi : i < 32) : (x.setWidth 64).getLsbD i = x.getLsbD i := by
  have : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth, this, decide_true, Bool.true_and]

/-- The byte at `g`, as a 1-byte load reads it. -/
theorem rd1 {V : Addr → Byte} {g : Addr} : ofBytesLE 8 ((byteAddrs g 1).map V) = V g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBytesLE]
  simp [byteAddrs, hi, addr_add_zero, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

/-- `XCR0` enables `m`, from its low half. -/
theorem enabled_of_low {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 32)
    (h : x.setWidth 32 &&& BitVec.ofNat 32 m = BitVec.ofNat 32 m) : x &&& BitVec.ofNat 64 m = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases h32 : i < 32
  · have := congrArg (fun z => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, h32, decide_true, Bool.true_and,
      BitVec.getLsbD_ofNat] at this
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simpa [h32] using this
  · have : m.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [BitVec.getLsbD_ofNat, this]

theorem enabled_e6 {y : BitVec 64} (h6 : y &&& BitVec.ofNat 64 6 = BitVec.ofNat 64 6)
    (he : y &&& BitVec.ofNat 64 224 = BitVec.ofNat 64 224) : y &&& BitVec.ofNat 64 230 = BitVec.ofNat 64 230 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have a := congrArg (fun z => z.getLsbD i) h6
  have b := congrArg (fun z => z.getLsbD i) he
  have e : (BitVec.ofNat 64 230).getLsbD i = ((BitVec.ofNat 64 6).getLsbD i || (BitVec.ofNat 64 224).getLsbD i) := by
    rw [show BitVec.ofNat 64 230 = BitVec.ofNat 64 6 ||| BitVec.ofNat 64 224 from by decide, BitVec.getLsbD_or]
  simp only [BitVec.getLsbD_and] at a b
  rw [BitVec.getLsbD_and, e]
  revert a b
  generalize y.getLsbD i = u
  generalize (BitVec.ofNat 64 6).getLsbD i = v
  generalize (BitVec.ofNat 64 224).getLsbD i = z
  cases u <;> cases v <;> cases z <;> simp

end FV7z.CpuFeat
