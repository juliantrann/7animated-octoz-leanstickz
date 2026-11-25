import FV7z.Mal.HeapS
/-!
# `Hp` for bytes that agree only on what it reads (PLAN.md §M, `Hp` after `_dl_non_dynamic_init`)

Between the last `malloc` of the start and `__libc_csu_init` there are stores to the blocks `malloc` gave (below
the top `T`) and to the TLS words `fs:-0x40..-0x30`: inside `GlR`/`GlS`, which take all of `[0x7a86c0, hi)`, but
apart from what `Gl` and `Hp` read.

- `GlF fb C`: `main_arena` and `mp_` (as `GlS`), `perturb_byte` and `global_max_fast`, the words `fs:-0x28`,
  `fs:0x18` and the tcache's counts `[C, C + 128)`; `HpF fb C T`: with the top's size word `[T + 8, T + 16)`.
- `Gl.mvF`: `Gl` for bytes that agree on `GlF` but for `main_arena.top`; `Hp.cut`: `Hp` names its tcache `C` and
  top `T` (with their bounds), and holds for every byte map that agrees on `HpF fb C T`.
- `Hp.mono`: a smaller budget, a larger `hi`; `Gl.foot`, `Hp.foot`: larger footprints.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sbrk (rd_eq)
namespace FV7z.Mal

/-- What `Gl` reads: `main_arena` and `mp_`, `perturb_byte` and `global_max_fast`, `fs:-0x28`, `fs:0x18`, the
tcache's counts. -/
def GlF (fb C : Addr) (a : Nat) : Prop :=
  7940480 ≤ a ∧ a < 7942880 ∨ 8013220 ≤ a ∧ a < 8013232 ∨ fb.toNat - 40 ≤ a ∧ a < fb.toNat - 32 ∨
    fb.toNat + 24 ≤ a ∧ a < fb.toNat + 28 ∨ C.toNat ≤ a ∧ a < C.toNat + 128

/-- What `Hp` reads: `GlF` and the top's size word. -/
def HpF (fb C T : Addr) (a : Nat) : Prop :=
  GlF fb C a ∨ T.toNat + 8 ≤ a ∧ a < T.toNat + 16

variable {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V W : Addr → Byte}

/-- `Gl` for bytes that agree on `GlF` but for the word `main_arena.top`. -/
theorem Gl.mvF {C : Addr} (h : Gl F Wl fb C V) (hf1 : 8029928 ≤ fb.toNat) (hf2 : fb.toNat + 48 < 2 ^ 64)
    (hc1 : 8029888 ≤ C.toNat) (hc : C.toNat + 128 < 2 ^ 64)
    (hW : ∀ a : Addr, GlF fb C a.toNat → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → W a = V a) :
    Gl F Wl fb C W := by
  obtain ⟨f24, -, f40⟩ := fofs fb (by omega) hf2
  have R : ∀ (x : Addr) (n : Nat), (7940480 ≤ x.toNat ∧ x.toNat + n ≤ 7942880 ∨
      8013220 ≤ x.toNat ∧ x.toNat + n ≤ 8013232 ∨ fb.toNat - 40 ≤ x.toNat ∧ x.toNat + n ≤ fb.toNat - 32 ∨
      fb.toNat + 24 ≤ x.toNat ∧ x.toNat + n ≤ fb.toNat + 28 ∨ C.toNat ≤ x.toNat ∧ x.toNat + n ≤ C.toNat + 128) →
      x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h1 h3 => rd_eq (by omega) fun a a1 a2 => hW a (by unfold GlF; omega) (by omega)
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

/-- `Hp` (a budget of at least 16) names its tcache `C` and top `T`, with their bounds, and holds of every byte map that agrees on
`HpF fb C T`. -/
theorem Hp.cut (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) : ∃ C T : Addr, 8029928 ≤ fb.toNat ∧ fb.toNat + 48 ≤ T.toNat ∧
    8029888 ≤ C.toNat ∧ C.toNat + 128 ≤ T.toNat ∧ 8032256 ≤ T.toNat ∧ T.toNat + m ≤ hi ∧ hi < 2 ^ 64 ∧
    rdq(V, 7940768#64) = T ∧ ∀ W : Addr → Byte, (∀ a : Addr, HpF fb C T a.toNat → W a = V a) →
      Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  refine ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, fun W hW => ?_⟩
  have hTl := T.isLt
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, G.mvF hf1 (by omega) hc1 (by omega) fun a ha _ => hW a (Or.inl ha), hf1, hf2, hc1, hc2, hT,
    hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
  · rw [rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by unfold HpF GlF; rw [et] at a1 a2; omega)]
    exact htop
  · rw [rd_eq (V := V) (x := T + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by unfold HpF GlF; rw [e8] at a1 a2; omega)]
    exact hsz
  · rw [rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by unfold HpF GlF; rw [es] at a1 a2; omega)]
    exact hsm

/-- `Hp` with a smaller budget and a larger `hi`. -/
theorem Hp.mono {hi' m' : Nat} (h : Hp F Wl fb hi m V) (hm : m' ≤ m) (hh : hi ≤ hi') (hh' : hi' < 2 ^ 64) :
    Hp F Wl fb hi' m' V := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  exact ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, by omega, hh', htop, hsz, hsm, hle, by omega,
    fun a a1 a2 => hTF a a1 (by omega)⟩

/-- `Gl` for larger footprints. -/
theorem Gl.foot {F' : Footprint} {Wl' : List Rgn} {C : Addr} (h : Gl F Wl fb C V)
    (hF : ∀ a, Foot F.data a → Foot F'.data a) (hW : ∀ a, Foot Wl a → Foot Wl' a) : Gl F' Wl' fb C V :=
  { h with
    fh := fun i hi => hF _ (h.fh i hi)
    fn := fun i hi j hj => hF _ (h.fn i hi j hj)
    f1 := fun i hi => hF _ (h.f1 i hi)
    W := fun a a1 a2 => hW _ (h.W a a1 a2)
    gf := fun i hi => hF _ (h.gf i hi)
    tf := fun i hi => hF _ (h.tf i hi)
    pb := fun i hi => hF _ (h.pb i hi) }

/-- `Hp` for larger footprints. -/
theorem Hp.foot {F' : Footprint} {Wl' : List Rgn} (h : Hp F Wl fb hi m V)
    (hF : ∀ a, Foot F.data a → Foot F'.data a) (hW : ∀ a, Foot Wl a → Foot Wl' a) : Hp F' Wl' fb hi m V := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  exact ⟨C, T, szw, sm, G.foot hF hW, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge,
    fun a a1 a2 => ⟨hW _ (hTF a a1 a2).1, hF _ (hTF a a1 a2).2⟩⟩

end FV7z.Mal
