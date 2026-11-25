import FV7z.Onw
/-!
# `Gl` and `Hp` for bytes that agree on less of `main_arena`'s neighbourhood (PLAN.md §M, assembly of `at_ctor`)

`init_cacheinfo` (constructor 103) stores to the `__x86_*` words at `[0x7932e0, 0x793320)`: inside the first interval
`[0x792980, 0x7933e0)` of `GlR`, but above all that `Gl` and `Hp` read (`Gl` up to `0x7932b0`, `mp_.system_mem` at
`0x7932c8`).

- `GlS E`: `GlR E` with the first interval ending at `0x7932e0`.
- `Gl.mvS`, `Hp.mvS`: `Gl.mvR`, `Hp.mvR` for bytes that agree on `GlS`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sbrk (rd_eq)
namespace FV7z.Mal

/-- `GlR E` with the first interval ending at `0x7932e0`, below the `__x86_*` words. -/
abbrev GlS (E : Nat) (a : Addr) : Prop :=
  7940480 ≤ a.toNat ∧ a.toNat < 7942880 ∨ 8013220 ≤ a.toNat ∧ a.toNat < 8013232 ∨ 8029888 ≤ a.toNat ∧ a.toNat < E

/-- `Gl` for bytes that agree on `GlS E` but for the word `main_arena.top`. -/
theorem Gl.mvS {F : Footprint} {Wl : List Rgn} {fb C : Addr} {E : Nat} {V W : Addr → Byte} (h : Gl F Wl fb C V)
    (hf1 : 8029928 ≤ fb.toNat) (hf2 : fb.toNat + 48 ≤ E) (hc1 : 8029888 ≤ C.toNat) (hc2 : C.toNat + 128 ≤ E)
    (hE : E < 2 ^ 64) (hW : ∀ a : Addr, GlS E a → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → W a = V a) :
    Gl F Wl fb C W := by
  obtain ⟨f24, -, f40⟩ := fofs fb (by omega) (by omega)
  have R : ∀ (x : Addr) (n : Nat), (7940480 ≤ x.toNat ∧ x.toNat + n ≤ 7942880 ∨
      8013220 ≤ x.toNat ∧ x.toNat + n ≤ 8013232 ∨ 8029888 ≤ x.toNat ∧ x.toNat + n ≤ E) →
      x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h1 h3 => rd_eq (by omega) fun a a1 a2 => hW a (by unfold GlS; omega) (by omega)
  have Rc : ∀ (x n : Nat), (7940480 ≤ x ∧ x + n ≤ 7942880 ∨ 8013220 ≤ x ∧ x + n ≤ 8013232) →
      x + n ≤ 7940768 ∨ 7940776 ≤ x →
      List.map W (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h1 h3 => R _ n (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
  exact
    { h with
      hk := by rw [Rc 7940656 8 (by omega) (by omega)]; exact h.hk
      tc := by rw [R _ 8 (by rw [f40]; omega) (by rw [f40]; omega)]; exact h.tc
      cn := fun i hi => by
        have e : (C + BitVec.ofNat 64 (2 * i)).toNat = C.toNat + 2 * i := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [R _ 2 (by rw [e]; omega) (by rw [e]; omega)]
        exact h.cn i hi
      t1 := by rw [R _ 4 (by rw [f24]; omega) (by rw [f24]; omega)]; exact h.t1
      gm := by rw [Rc 8013224 8 (by omega) (by omega)]; exact h.gm
      fc := by rw [Rc 7940680 4 (by omega) (by omega)]; exact h.fc
      fz := fun k hk => by rw [Rc (7940688 + 8 * k) 8 (by omega) (by omega)]; exact h.fz k hk
      bk := fun i i1 i2 => by rw [Rc (7940776 + 16 * i) 8 (by omega) (by omega)]; exact h.bk i i1 i2
      lb := fun i i1 i2 => by rw [Rc (7940768 + 16 * i) 8 (by omega) (by omega)]; exact h.lb i i1 i2
      tb := by rw [Rc 7940592 8 (by omega) (by omega)]; exact h.tb
      un := by rw [Rc 7940792 8 (by omega) (by omega)]; exact h.un
      m0 := by rw [Rc 7942816 4 (by omega) (by omega)]; exact h.m0
      m1 := by rw [Rc 7942820 4 (by omega) (by omega)]; exact h.m1
      m2 := by rw [Rc 7942824 4 (by omega) (by omega)]; exact h.m2
      m3 := by rw [Rc 7942828 4 (by omega) (by omega)]; exact h.m3
      p0 := by rw [Rc 8013220 4 (by omega) (by omega)]; exact h.p0 }

/-- `Hp` (a top of at least 16 bytes) for bytes that agree on `GlS hi`. -/
theorem Hp.mvS {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V W : Addr → Byte}
    (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) (hW : ∀ a : Addr, GlS hi a → W a = V a) : Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, G.mvS (E := T.toNat) hf1 hf2 hc1 hc2 (by omega) fun a ha _ => hW a (by
      unfold GlS at ha ⊢; omega), hf1, hf2, hc1, hc2, hT, hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
  · rw [rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by unfold GlS; rw [et] at a1 a2; omega)]
    exact htop
  · rw [rd_eq (V := V) (x := T + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by unfold GlS; rw [e8] at a1 a2; omega)]
    exact hsz
  · rw [rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by unfold GlS; rw [es] at a1 a2; omega)]
    exact hsm

/-- The `fs` base and the budget's end that `Hp` gives. -/
theorem Hp.bnd {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V : Addr → Byte}
    (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) : 8029928 ≤ fb.toNat ∧ fb.toNat + 64 ≤ hi ∧ hi < 2 ^ 64 := by
  obtain ⟨_, _, _, _, -, hf1, hf2, -, -, -, hTh, hhi, -⟩ := h
  omega

end FV7z.Mal
