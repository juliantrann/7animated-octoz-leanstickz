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
- `HpR R`: `Hp`, with the bytes `R` (the blocks `malloc` gave, words of `ld.so` in `.bss`) apart from what `Gl` reads
  and below the top's size word; `HpR.keep`: stores to `R` keep it; `HpR.mal`: after a `malloc` (the facts of
  `Mal.At` on the top), with the new block added to `R`; `HpR.addLo`: words of `.bss` added to `R`.
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

/-- `Hp` (a budget of at least 16) names its tcache `C` and top `T`, with their bounds, and holds of every byte map
that agrees on `HpF fb C T`. -/
theorem Hp.cut (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) : ∃ C T : Addr, 8029928 ≤ fb.toNat ∧ fb.toNat + 48 ≤ T.toNat ∧
    fb.toNat + 64 ≤ C.toNat ∧ C.toNat + 128 ≤ T.toNat ∧ 8032256 ≤ T.toNat ∧ T.toNat + m ≤ hi ∧ hi < 2 ^ 64 ∧
    rdq(V, 7940768#64) = T ∧ rdq(V, fb + 18446744073709551576#64) = C ∧
    ∀ W : Addr → Byte, (∀ a : Addr, HpF fb C T a.toNat → W a = V a) → Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  refine ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, G.tc, fun W hW => ?_⟩
  have hTl := T.isLt
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, G.mvF hf1 (by omega) (by omega) (by omega) fun a ha _ => hW a (Or.inl ha), hf1, hf2, hc1,
    hc2, hT, hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
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

/-- `Hp` for footprints that are larger from `0x792980` (`main_arena`) up: all the bytes whose footprint `Hp` states
lie there. -/
theorem Hp.footHi {F' : Footprint} {Wl' : List Rgn} (h : Hp F Wl fb hi m V)
    (hF : ∀ a : Addr, 7940480 ≤ a.toNat → Foot F.data a → Foot F'.data a)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → Foot Wl a → Foot Wl' a) : Hp F' Wl' fb hi m V := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  have hTl := T.isLt
  have e24 : (fb + 24#64).toNat = fb.toNat + 24 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e40 : (fb + 18446744073709551576#64).toNat = fb.toNat - 40 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eC : ∀ i < 64, (C + BitVec.ofNat 64 (2 * i)).toNat = C.toNat + 2 * i := fun i hi => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t1 : (7940656#64 : Addr).toNat = 7940656 := rfl
  have t2 : (8013224#64 : Addr).toNat = 8013224 := rfl
  have t3 : (8013220#64 : Addr).toNat = 8013220 := rfl
  refine ⟨C, T, szw, sm, { G with
    fh := fun i hi => hF _ (by rw [toNat_add_of_fits (n := 8) hi (by rw [t1]; omega), t1]; omega) (G.fh i hi)
    fn := fun i hi j hj => hF _ (by rw [toNat_add_of_fits (n := 2) hj (by rw [eC i hi]; omega), eC i hi]; omega)
      (G.fn i hi j hj)
    f1 := fun i hi => hF _ (by rw [toNat_add_of_fits (n := 4) hi (by rw [e24]; omega), e24]; omega) (G.f1 i hi)
    W := fun a a1 a2 => hW _ (by omega) (G.W a a1 a2)
    gf := fun i hi => hF _ (by rw [toNat_add_of_fits (n := 8) hi (by rw [t2]; omega), t2]; omega) (G.gf i hi)
    tf := fun i hi => hF _ (by rw [toNat_add_of_fits (n := 8) hi (by rw [e40]; omega), e40]; omega) (G.tf i hi)
    pb := fun i hi => hF _ (by rw [toNat_add_of_fits (n := 4) hi (by rw [t3]; omega), t3]; omega) (G.pb i hi) },
    hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge,
    fun a a1 a2 => ⟨hW _ (by omega) (hTF a a1 a2).1, hF _ (by omega) (hTF a a1 a2).2⟩⟩

/-- `Hp`, and the bytes `R` apart from what `Gl` reads (its tcache the word at `fs:-0x28`) and below the top's size
word. -/
def HpR (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (R : Nat → Prop) (V : Addr → Byte) : Prop :=
  Hp F Wl fb hi m V ∧
    ∀ a, R a → ¬ GlF fb (rdq(V, fb + 18446744073709551576#64)) a ∧ a < (rdq(V, 7940768#64)).toNat + 8

/-- Stores to `R` (and outside `[0x792980, hi)`) keep `HpR R`. -/
theorem HpR.keep {R : Nat → Prop} (h : HpR F Wl fb hi m R V) (hm : 16 ≤ m)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi → ¬ R a.toNat → W a = V a) : HpR F Wl fb hi m R W := by
  obtain ⟨hp, hR⟩ := h
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, htc, hcut⟩ := hp.cut hm
  have hTl := T.isLt
  have hF : ∀ a : Addr, HpF fb C T a.toNat → W a = V a := fun a ha => by
    apply hW a
    · unfold HpF GlF at ha; omega
    · unfold HpF GlF at ha; omega
    · intro hr
      have := hR _ hr
      rw [htc, htop] at this
      unfold HpF at ha
      rcases ha with ha | ha
      · exact this.1 ha
      · omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  obtain ⟨-, -, f40⟩ := fofs fb (by omega) (by omega)
  have etop : rdq(W, 7940768#64) = rdq(V, 7940768#64) := by
    rw [rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hF a (by unfold HpF GlF; rw [et] at a1 a2; omega)]
  have etc : rdq(W, fb + 18446744073709551576#64) = rdq(V, fb + 18446744073709551576#64) := by
    rw [rd_eq (V := V) (x := fb + 18446744073709551576#64) (n := 8) (by rw [f40]; omega) fun a a1 a2 =>
      hF a (by unfold HpF GlF; rw [f40] at a1 a2; omega)]
  exact ⟨hcut W hF, fun a ha => by rw [etop, etc]; exact hR a ha⟩

/-- After a `malloc` (the top `T` before, the block `[p, p + n)` above `T + 16` and below the new top's size word,
the bytes below `T + 8` but `main_arena.top` kept): `HpR` with the block added. -/
theorem HpR.mal {R : Nat → Prop} {V₂ : Addr → Byte} {m₀ : Nat} {p : Addr} {n : Nat}
    (h : HpR F Wl fb hi m₀ R V) (hm₀ : 16 ≤ m₀) (h₂ : Hp F Wl fb hi m V₂)
    (hp1 : rdq(V, 7940768#64).toNat + 16 ≤ p.toNat) (hp2 : p.toNat + n ≤ rdq(V₂, 7940768#64).toNat + 8)
    (hp3 : ∀ a : Addr, a.toNat < rdq(V, 7940768#64).toNat + 8 → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) →
      V₂ a = V a) :
    HpR F Wl fb hi m (fun a => R a ∨ p.toNat ≤ a ∧ a < p.toNat + n) V₂ := by
  obtain ⟨hp, hR⟩ := h
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, htc, -⟩ := hp.cut hm₀
  obtain ⟨-, -, f40⟩ := fofs fb (by omega) (by omega)
  rw [htop] at hp1 hp3
  have etc : rdq(V₂, fb + 18446744073709551576#64) = C := by
    rw [rd_eq (V := V) (x := fb + 18446744073709551576#64) (n := 8) (by rw [f40]; omega) fun a a1 a2 =>
      hp3 a (by rw [f40] at a1 a2; omega) (by rw [f40] at a1 a2; omega)]
    exact htc
  refine ⟨h₂, fun a ha => ?_⟩
  rw [etc]
  rcases ha with ha | ⟨h1, h2⟩
  · have := hR a ha
    rw [htc, htop] at this
    exact ⟨this.1, by omega⟩
  · exact ⟨by unfold GlF; omega, by omega⟩

/-- Words of `.bss` past `main_arena` and `mp_` (but `perturb_byte`, `global_max_fast`) added to `R`. -/
theorem HpR.addLo {R S : Nat → Prop} (h : HpR F Wl fb hi m R V) (hm : 16 ≤ m)
    (hS : ∀ a, S a → 7942880 ≤ a ∧ a < 8013220 ∨ 8013232 ≤ a ∧ a < 8029888) :
    HpR F Wl fb hi m (fun a => R a ∨ S a) V := by
  obtain ⟨hp, hR⟩ := h
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, htc, -⟩ := hp.cut hm
  refine ⟨hp, fun a ha => ?_⟩
  rcases ha with ha | ha
  · exact hR a ha
  · have := hS a ha
    rw [htc, htop]
    exact ⟨by unfold GlF; omega, by omega⟩

/-- `HpR` for more bytes in the TLS block below the tcache word, `[fs:-0x40, fs:-0x28)`. -/
theorem HpR.addTls {R S : Nat → Prop} (h : HpR F Wl fb hi m R V) (hm : 16 ≤ m)
    (hS : ∀ a, S a → fb.toNat - 64 ≤ a ∧ a < fb.toNat - 40) : HpR F Wl fb hi m (fun a => R a ∨ S a) V := by
  obtain ⟨hp, hR⟩ := h
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, htc, -⟩ := hp.cut hm
  refine ⟨hp, fun a ha => ?_⟩
  rcases ha with ha | ha
  · exact hR a ha
  · have := hS a ha
    rw [htc, htop]
    exact ⟨by unfold GlF; omega, by omega⟩

/-- `HpR` for fewer bytes. -/
theorem HpR.sub {R R' : Nat → Prop} (h : HpR F Wl fb hi m R V) (hR : ∀ a, R' a → R a) :
    HpR F Wl fb hi m R' V :=
  ⟨h.1, fun a ha => h.2 a (hR a ha)⟩

end FV7z.Mal
