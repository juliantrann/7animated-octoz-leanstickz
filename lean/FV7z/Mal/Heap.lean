import FV7z.Mnx.Run
import FV7z.Im6.Run
import FV7z.Im7.Run
import FV7z.Gor.Run
/-!
# The heap after the first `malloc`, kept by the next ones (PLAN.md G3, `malloc`)

- `Gl F Wl fb C V`: what `Mnx.mal_next` reads apart from the top and the stack: `__malloc_hook` null, the tcache `C`
  (`fs:-0x28`) with its 64 counts 0, one thread (`fs:0x18`), `global_max_fast`, the fastbins, the small and large
  bins and the unsorted bin empty, the binmap 0, `perturb_byte` 0; with the footprint those reads need.
- `Gl.mvR`: the same for bytes that agree on what `Gl` reads below `E` (`GlR E`: `main_arena`, `mp_`,
  `perturb_byte`, `global_max_fast`, the TLS words and the tcache) but for the word `main_arena.top`; `Gl.mv`: for those
  that agree on `[0x792980, E)`.
- `Hp F Wl fb hi k V`: `Gl` and the top `T` (`main_arena.top`) with its size at least `k`, not above `system_mem`,
  `[T, T + k)` in the footprint and below `hi` (the budget, not the whole top).
- `nb_le`: the chunk size of `malloc (n)`, `n ≤ 1024`: `n + 8 ≤ nb ≤ 1040`, a multiple of 16; `nb_ex`: a chunk size
  of class `Im5.ClsN` with `n + 8 ≤ nb ≤ B - 32` for `n ≤ 1024` (`B` = 1072) or `n` = 72704 (`B` = 72752, ctor 102).
- `MalB n B`: `n ≤ 2 ^ 32` and `B` at least 64 and 32 above `n + 23` rounded down to 16; `nb_exW`: a chunk size of
  class `Im7.ClsW` with `n + 8 ≤ nb ≤ B - 32`; `secW`: `Im5.SecA` for `ClsW` (`Im6.secN`, `Im7.secC`).
- `mal_hpW`: `malloc (n)` for `MalB n B`, from `Hp … (k + B)` (the stack from `hi + 216` below `rsp`):
  the chunk `p = T + 16` split off the top, the bytes as before but for the top word, the two size words (below `p`
  and in `[p + n, hi)`) and the frame; and `Hp … k` again for every byte map that agrees with the one at the return from
  `0x792980` to `hi` but for `[p, p + n)`. This is the form `Mal.At` is to take: `Pm` there is a predicate of bytes
  only, for every footprint, so the top's footprint can not be part of it. `mal_hp`: the same for `n ≤ 1024`
  (`B` = 1072) or `n` = 72704 (`B` = 72752).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at)
open FV7z.Im2 (VspN)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Mal

/-- What `malloc` after the first call reads apart from the top and the stack, and the footprint of those reads. -/
structure Gl (F : Footprint) (Wl : List Rgn) (fb C : Addr) (V : Addr → Byte) : Prop where
  hk : rdq(V, 7940656#64) = 0#64
  tc : rdq(V, fb + 18446744073709551576#64) = C
  cn : ∀ i < 64, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16
  t1 : rdd(V, fb + 24#64) = 0#32
  gm : rdq(V, 8013224#64) = 128#64
  fc : rdd(V, 7940680#64) = 0
  fz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64
  bk : ∀ i, 2 ≤ i → i ≤ 63 →
    rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i)
  lb : ∀ i, 64 ≤ i → i ≤ 126 →
    rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i)
  tb : rdq(V, 7940592#64) = 64#64
  un : rdq(V, 7940792#64) = 7940768#64
  m0 : rdd(V, 7942816#64) = 0
  m1 : rdd(V, 7942820#64) = 0
  m2 : rdd(V, 7942824#64) = 0
  m3 : rdd(V, 7942828#64) = 0
  p0 : rdd(V, 8013220#64) = 0
  fh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)
  fn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)
  f1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)
  W : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a
  gf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i)
  tf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)
  pb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)

/-- The bytes `Gl` reads below `E`: `main_arena` and `mp_`, `perturb_byte` and `global_max_fast`, from `0x7a86c0`
(the TLS words, the tcache) up to `E`. -/
abbrev GlR (E : Nat) (a : Addr) : Prop :=
  7940480 ≤ a.toNat ∧ a.toNat < 7943136 ∨ 8013220 ≤ a.toNat ∧ a.toNat < 8013232 ∨ 8029888 ≤ a.toNat ∧ a.toNat < E

/-- `Gl` for bytes that agree on `GlR E` but for the word `main_arena.top`. -/
theorem Gl.mvR {F : Footprint} {Wl : List Rgn} {fb C : Addr} {E : Nat} {V W : Addr → Byte} (h : Gl F Wl fb C V)
    (hf1 : 8029928 ≤ fb.toNat) (hf2 : fb.toNat + 48 ≤ E) (hc1 : 8029888 ≤ C.toNat) (hc2 : C.toNat + 128 ≤ E)
    (hE : E < 2 ^ 64) (hW : ∀ a : Addr, GlR E a → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → W a = V a) :
    Gl F Wl fb C W := by
  obtain ⟨f24, -, f40⟩ := fofs fb (by omega) (by omega)
  have R : ∀ (x : Addr) (n : Nat), (7940480 ≤ x.toNat ∧ x.toNat + n ≤ 7943136 ∨
      8013220 ≤ x.toNat ∧ x.toNat + n ≤ 8013232 ∨ 8029888 ≤ x.toNat ∧ x.toNat + n ≤ E) →
      x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h1 h3 => rd_eq (by omega) fun a a1 a2 => hW a (by unfold GlR; omega) (by omega)
  have Rc : ∀ (x n : Nat), (7940480 ≤ x ∧ x + n ≤ 7943136 ∨ 8013220 ≤ x ∧ x + n ≤ 8013232) →
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

/-- `Gl` for bytes that agree from `0x792980` up to `E` but for the word `main_arena.top`. -/
theorem Gl.mv {F : Footprint} {Wl : List Rgn} {fb C : Addr} {E : Nat} {V W : Addr → Byte} (h : Gl F Wl fb C V)
    (hf1 : 8029928 ≤ fb.toNat) (hf2 : fb.toNat + 48 ≤ E) (hc1 : 8029888 ≤ C.toNat) (hc2 : C.toNat + 128 ≤ E)
    (hE : E < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < E → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → W a = V a) :
    Gl F Wl fb C W :=
  h.mvR hf1 hf2 hc1 hc2 hE fun a ha ht => hW a (by unfold GlR at ha; omega) (by unfold GlR at ha; omega) ht

/-- The heap for the next `malloc`: `Gl`, the tcache `C` and the TLS words below the top `T`, the top's size (without
the in-use bit) at least `k` and not above `system_mem`, `[T, T + k)` in the footprint and below `hi`. -/
def Hp (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi k : Nat) (V : Addr → Byte) : Prop :=
  ∃ C T szw sm : Addr, Gl F Wl fb C V ∧ 8029928 ≤ fb.toNat ∧ fb.toNat + 48 ≤ T.toNat ∧ fb.toNat + 64 ≤ C.toNat ∧
    C.toNat + 128 ≤ T.toNat ∧ 8032256 ≤ T.toNat ∧ T.toNat + k ≤ hi ∧
    hi < 2 ^ 64 ∧ rdq(V, 7940768#64) = T ∧ rdq(V, T + 8#64) = szw ∧ rdq(V, 7942856#64) = sm ∧
    (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat ∧ k ≤ (szw &&& 18446744073709551608#64).toNat ∧
    ∀ a : Addr, T.toNat ≤ a.toNat → a.toNat < T.toNat + k → Foot Wl a ∧ Foot F.data a

/-- The chunk size of `malloc (n)`, `n ≤ 1024`. -/
theorem nb_le {n : Nat} (h : n ≤ 1024) :
    n + 8 ≤ (Gor.nbOf n).toNat ∧ (Gor.nbOf n).toNat ≤ 1040 ∧ (Gor.nbOf n).toNat % 16 = 0 := by
  unfold Gor.nbOf
  split
  · show n + 8 ≤ 32 ∧ 32 ≤ 1040 ∧ 32 % 16 = 0
    omega
  · rw [Im2.and_m16, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- A chunk size for `malloc (n)`: `Im5.ClsN`, `n + 8 ≤ nb`, `nb + 32 ≤ B`, `16 ∣ nb`, for `n ≤ 1024` with `B` = 1072 or
`n` = 72704 with `B` = 72752. -/
theorem nb_ex {n : Addr} {B : Nat} (h : n.toNat ≤ 1024 ∧ B = 1072 ∨ n = 72704#64 ∧ B = 72752) :
    ∃ nb : Addr, Im5.ClsN n nb ∧ n.toNat + 8 ≤ nb.toNat ∧ nb.toNat + 32 ≤ B ∧ nb.toNat % 16 = 0 := by
  rcases h with ⟨hn, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hb1, hb2, hb3⟩ := nb_le hn
    have hcls := Gor.clsA_of (n := n.toNat) (by omega)
    have en : BitVec.ofNat 64 n.toNat = n := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
    rw [en] at hcls
    exact ⟨_, .inl hcls, hb1, by omega, hb3⟩
  · exact ⟨72720#64, .inr ⟨rfl, rfl⟩, by decide, by decide, by decide⟩

/-- What `mal_hpW` takes of the request `n` and the top's budget `B`: `n ≤ 2 ^ 32`, `B` at least 64 and 32 above
`n + 23` rounded down to 16 (the chunk size for `n ≥ 9`). -/
def MalB (n : Addr) (B : Nat) : Prop := n.toNat ≤ 2 ^ 32 ∧ (n.toNat + 23) / 16 * 16 + 32 ≤ B ∧ 64 ≤ B

theorem MalB.old {n : Addr} {B : Nat} (h : n.toNat ≤ 1024 ∧ B = 1072 ∨ n = 72704#64 ∧ B = 72752) : MalB n B := by
  rcases h with ⟨hn, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by decide, by decide, by decide⟩

/-- A chunk size for `malloc (n)`, `MalB n B`: `Im7.ClsW`, `n + 8 ≤ nb`, `nb + 32 ≤ B`, `16 ∣ nb`. -/
theorem nb_exW {n : Addr} {B : Nat} (h : MalB n B) :
    ∃ nb : Addr, Im7.ClsW n nb ∧ n.toNat + 8 ≤ nb.toNat ∧ nb.toNat + 32 ≤ B ∧ nb.toNat % 16 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge n.toNat 4105 with hn | hn
  · have hcls := Gor.clsA_of (n := n.toNat) (by omega)
    have en : BitVec.ofNat 64 n.toNat = n := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
    rw [en] at hcls
    refine ⟨_, .inl (.inl hcls), ?_⟩
    unfold Gor.nbOf
    split
    · show n.toNat + 8 ≤ 32 ∧ 32 + 32 ≤ B ∧ 32 % 16 = 0
      omega
    · rw [Im2.and_m16, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
  · have hg : Im7.ClsG n (n + 23#64 &&& 18446744073709551600#64) := ⟨hn, h1, rfl⟩
    have e := hg.nb
    exact ⟨_, .inr hg, by omega, by omega, by omega⟩

/-- `_int_malloc` on the second call for every request of `Im7.ClsW`. -/
theorem secW {n nb : Addr} (h : Im7.ClsW n nb) : Im5.SecA n nb := by
  rcases h with h | h
  · exact Im6.secN h
  · exact Im7.secC h

/-- `main_arena.top` after the split. -/
theorem VspN_top {T szw nb : Addr} (V : Addr → Byte) (h1 : 7940776 ≤ T.toNat) (hT : T.toNat + nb.toNat + 16 < 2 ^ 64) :
    rdq(VspN T szw nb V, 7940768#64) = T + nb := by
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold VspN
  rw [rd_Vst _ _ _ _ _ (by rw [l, e72]; omega) (by rw [et]; omega) (by rw [l, e72, et]; omega),
    rd_Vst _ _ _ _ _ (by rw [l, e8]; omega) (by rw [et]; omega) (by rw [l, e8, et]; omega),
    rd_Vst_self _ _ _ (l _) (by rw [et]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The rest's size word after the split. -/
theorem VspN_rest {T szw nb : Addr} (V : Addr → Byte) (hT : T.toNat + nb.toNat + 16 < 2 ^ 64) :
    rdq(VspN T szw nb V, T + nb + 8#64) = (szw &&& 18446744073709551608#64) - nb ||| 1#64 := by
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold VspN
  rw [rd_Vst_self _ _ _ (l _) (by rw [e72]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- A byte the split does not store to. -/
theorem VspN_out {T szw nb : Addr} (V : Addr → Byte) (hT : T.toNat + nb.toNat + 16 < 2 ^ 64) {a : Addr}
    (h1 : ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776)) (h2 : ¬ (T.toNat + 8 ≤ a.toNat ∧ a.toNat < T.toNat + 16))
    (h3 : ¬ (T.toNat + nb.toNat + 8 ≤ a.toNat ∧ a.toNat < T.toNat + nb.toNat + 16)) : VspN T szw nb V a = V a := by
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold VspN
  rw [Vst_out _ _ _ _ (by rw [l, e72]; omega) (by rw [l, e72]; omega),
    Vst_out _ _ _ _ (by rw [l, e8]; omega) (by rw [l, e8]; omega),
    Vst_out _ _ _ _ (by rw [l, et]; omega) (by rw [l, et]; omega)]

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle}
  {t : Nat} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- `malloc (n)` for `MalB n B` (`n ≤ 2 ^ 32`), after the first call (`Hp` with a top of at least `n`'s chunk and 32
bytes more): from the entry to the return address with `p = T + 16` in `rax`; `Hp` again, for a top smaller by at
most `B - 32`. -/
theorem mal_hpW {fb : Addr} {hi m B : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mnx_at) (hH : Hp F Wl fb hi (m + B) V)
    (hn : MalB X.cpu.gpr.rdi B)
    (hhi : hi + 216 ≤ X.cpu.gpr.rsp.toNat) (hR : X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ i < 224, Foot Wl (Addr.add (X.cpu.gpr.rsp - 216#64) i))
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (kc : ∀ Z t' (V₂ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat →
      p.toNat + X.cpu.gpr.rdi.toNat ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + X.cpu.gpr.rdi.toNat → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 208 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < p.toNat ∨ p.toNat + X.cpu.gpr.rdi.toNat ≤ a.toNat) → W a = V₂ a) → Hp F Wl fb hi m W) →
      rdq(V, 7940768#64).toNat + 16 ≤ p.toNat → p.toNat + X.cpu.gpr.rdi.toNat ≤ rdq(V₂, 7940768#64).toNat + 8 →
      (∀ a : Addr, a.toNat < rdq(V, 7940768#64).toNat + 8 → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi', htop, hsz, hsm, hle, hge, hTF⟩ := hH
  have hrs := X.cpu.gpr.rsp.isLt
  have hdl := X.cpu.gpr.rdi.isLt
  have ha8 := Smm.and_m8 szw
  obtain ⟨nb, hcls, hb1, hb2, hb3⟩ := nb_exW hn
  obtain ⟨f24, -, f40⟩ := fofs fb (by omega) (by omega)
  have eS : (X.cpu.gpr.rsp - 216#64).toNat = X.cpu.gpr.rsp.toNat - 216 := by bvg
  have eS' : X.cpu.gpr.rsp - 216#64 + 216#64 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have eS8 : X.cpu.gpr.rsp - 216#64 + 224#64 = X.cpu.gpr.rsp + 8 := by bvg
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e16 : (T + 16#64).toNat = T.toNat + 16 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eTn : (T + nb).toNat = T.toNat + nb.toNat := by rw [BitVec.toNat_add]; omega
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hTF' : ∀ x : Addr, ∀ i < 8, T.toNat + 8 ≤ x.toNat → x.toNat + 8 ≤ T.toNat + B →
      Foot Wl (Addr.add x i) := fun x i hi8 h1 h2 => by
    have e : (Addr.add x i).toNat = x.toNat + i := by
      simp only [Addr.add]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact (hTF (Addr.add x i) (by omega) (by omega)).1
  refine Mnx.mal_next (S := X.cpu.gpr.rsp - 216#64) (T := T) (szw := szw) (sm := sm) (C := C)
    (n := X.cpu.gpr.rdi) (nb := nb) c hfs hin hinI hK hA hcls (secW hcls) hrip rfl eS'.symm (by omega)
    (by omega) (by rw [f40, eS]; omega) (by rw [f24, eS]; omega) G.hk G.fh G.tc
    (fun h0 => by rw [h0] at hc1; simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hc1; omega)
    (by rw [eS]; omega) G.cn G.fn G.t1 G.f1 G.gm G.fc G.fz G.bk G.lb G.tb G.un G.m0 G.m1 G.m2 G.m3 G.W G.gf G.tf
    hsw (by omega) (by rw [eS]; omega) (fun i hi8 => hTF' (T + 8#64) i hi8 (by omega) (by omega))
    (fun i hi8 => hTF' (T + nb + 8#64) i hi8 (by rw [e72]; omega) (by rw [e72]; omega))
    G.pb G.p0 htop hsz hsm hle (by omega)
    hin₂ hj (by rw [eS']; exact hra) ?_
  intro M Z t' hKZ hAZ hMV hrZ hax hspZ hbx hbp h12 h13 h14 h15
  have hT16 : T.toNat + nb.toNat + 16 < 2 ^ 64 := by omega
  -- the bytes at the return: as before but for the three words of the split and the frame
  have MV : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 208 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → ¬ (T.toNat + 8 ≤ a.toNat ∧ a.toNat < T.toNat + 16) →
      ¬ (T.toNat + nb.toNat + 8 ≤ a.toNat ∧ a.toNat < T.toNat + nb.toNat + 16) → M a = V a :=
    fun a h0 h1 h2 h3 => (hMV a (by rw [eS]; omega)).trans (VspN_out V hT16 h1 h2 h3)
  have MS : ∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 208 → M a = VspN T szw nb V a :=
    fun a h0 => hMV a (by rw [eS]; omega)
  -- the top at the return
  have hMt : rdq(M, 7940768#64) = T + nb := by
    have et : (7940768#64 : Addr).toNat = 7940768 := rfl
    rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN T szw nb V) (x := 7940768#64) (n := 8) (by rw [et]; omega)
      fun a a1 a2 => MS a (by rw [et] at a2; omega))]
    exact VspN_top V (by omega) hT16
  refine kc Z t' M (T + 16#64) hKZ hAZ hrZ (by rw [hspZ, eS8]) hax hbx hbp h12 h13 h14 h15 (by rw [e16]; omega)
    (by rw [e16]; omega) (by rw [e16]; omega)
    (fun a a1 a2 => hTF a (by rw [e16] at a1; omega) (by rw [e16] at a2; omega))
    (fun a ha => MV a (by omega) (by omega) (by rw [e16] at ha; omega) (by rw [e16] at ha; omega)) ?_
    (by rw [htop]; omega) (by rw [hMt]; rw [eTn]; omega)
    (fun a h1 h2 => by rw [htop] at h1; exact MV a (by omega) h2 (by omega) (by omega))
  intro W hW
  -- below the top, `W` is `V` but for the top word
  have WV : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < T.toNat → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) →
      W a = V a := fun a a1 a2 a3 =>
    (hW a a1 (by omega) (.inl (by rw [e16]; omega))).trans (MV a (by omega) a3 (by omega) (by omega))
  have hx : ((szw &&& 18446744073709551608#64) - nb).toNat = (szw &&& 18446744073709551608#64).toNat - nb.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hs' : (((szw &&& 18446744073709551608#64) - nb ||| 1#64) &&& 18446744073709551608#64).toNat =
      (szw &&& 18446744073709551608#64).toNat - nb.toNat := by
    rw [Mhi.or1_m8, hx]; omega
  refine ⟨C, T + nb, (szw &&& 18446744073709551608#64) - nb ||| 1#64, sm,
    G.mv (E := T.toNat) hf1 hf2 (by omega) hc2 (by omega) WV, hf1, by rw [eTn]; omega, hc1, by rw [eTn]; omega,
    by rw [eTn]; omega, by rw [eTn]; omega, hhi', ?_, ?_, ?_, by rw [hs']; omega, by rw [hs']; omega, ?_⟩
  · -- the top word
    have et : (7940768#64 : Addr).toNat = 7940768 := rfl
    rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN T szw nb V) (x := 7940768#64) (n := 8) (by rw [et]; omega)
      fun a a1 a2 =>
      (hW a (by rw [et] at a1; omega) (by rw [et] at a2; omega) (.inl (by rw [et] at a2; rw [e16]; omega))).trans
        (MS a (by rw [et] at a2; omega)))]
    exact VspN_top V (by omega) hT16
  · -- the rest's size word
    rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN T szw nb V) (x := T + nb + 8#64) (n := 8) (by rw [e72]; omega)
      fun a a1 a2 =>
      (hW a (by rw [e72] at a1; omega) (by rw [e72] at a2; omega) (.inr (by rw [e72] at a1; rw [e16]; omega))).trans
        (MS a (by rw [e72] at a2; omega)))]
    exact VspN_rest V hT16
  · -- `system_mem`
    have et : (7942856#64 : Addr).toNat = 7942856 := rfl
    rw [congrArg (ofBytesLE 64) (rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      WV a (by rw [et] at a1; omega) (by rw [et] at a2; omega) (by rw [et] at a1; omega))]
    exact hsm
  · intro a a1 a2
    rw [eTn] at a1
    rw [eTn] at a2
    exact hTF a (by omega) (by omega)

/-- `mal_hpW` for `n ≤ 1024` (`B` = 1072) or `n` = 72704 (`B` = 72752). -/
theorem mal_hp {fb : Addr} {hi m B : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mnx_at) (hH : Hp F Wl fb hi (m + B) V)
    (hn : X.cpu.gpr.rdi.toNat ≤ 1024 ∧ B = 1072 ∨ X.cpu.gpr.rdi = 72704#64 ∧ B = 72752)
    (hhi : hi + 216 ≤ X.cpu.gpr.rsp.toNat) (hR : X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ i < 224, Foot Wl (Addr.add (X.cpu.gpr.rsp - 216#64) i))
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (kc : ∀ Z t' (V₂ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat →
      p.toNat + X.cpu.gpr.rdi.toNat ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + X.cpu.gpr.rdi.toNat → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 208 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < p.toNat ∨ p.toNat + X.cpu.gpr.rdi.toNat ≤ a.toNat) → W a = V₂ a) → Hp F Wl fb hi m W) →
      rdq(V, 7940768#64).toNat + 16 ≤ p.toNat → p.toNat + X.cpu.gpr.rdi.toNat ≤ rdq(V₂, 7940768#64).toNat + 8 →
      (∀ a : Addr, a.toNat < rdq(V, 7940768#64).toNat + 8 → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  mal_hpW c hfs hin hinI hK hA hrip hH (MalB.old hn) hhi hR hsw hin₂ hj hra kc

end FV7z.Mal
