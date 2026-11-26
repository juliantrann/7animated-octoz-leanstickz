import FV7z.Ifr.Holds
import FV7z.Mal.Tc
/-!
# The tcache after `tcache_put` (PLAN.md G3, `free`)

The four stores of `_int_free`'s tcache put (`Vput`, `Ifr.Frame`) on a heap with `GlB` and `TcSt V C bins`, for a
chunk `p` that is allocated (`Alloc`: its words `[p + 16, p + 32)` apart from every entry's `next` word and from the
tcache): `GlB` still holds and the bins are `bput bins i (p + 16)`, `i` the chunk's bin.

- `rd4`: a read apart from each of the four stores.
- `a2`, `a8`: `Mal`'s count and entry addresses as `_int_free` computes them.
- `GlB.congr`: `GlB` from the bytes it reads, `[0x792a80, 0x793660)`, `[0x7a4564, 0x7a4570)`, `fs:-0x28`, `fs:24`.
- `TcSt.congr`: `TcSt` from the bytes of the tcache and of the entries' `next` words.
- `tc_put`: `TcSt V C bins` and `Alloc` give `TcSt (Vput …) C (bput bins i (p + 16))`.
- `put_inv`: `GlB ∧ TcSt bins ∧ Alloc p` before, `GlB ∧ TcSt (bput bins i (p + 16))` after,
  for any `W` equal to the four stores outside the frame.
- `ifr_put_inv`: the free contract on the put path, from `ifr_put_ok`. Open gaps (the branches `PutOk` leaves out):
  the `key = tcache` scan, the full bin (and the tcache not made, `tc_idx` too big), the non-tcache path.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Mal (GlB TcSt tcnt tent bput)
namespace FV7z.Ifr

/-- The chunk `p` is not in the tcache: its `next` and `key` words apart from every entry's `next` word and from the
tcache `C`, the entries' words inside memory. -/
def Alloc (C : Addr) (bins : Nat → List Addr) (p : Addr) : Prop :=
  ∀ i < 64, ∀ e ∈ bins i, e.toNat + 8 ≤ 2 ^ 64 ∧
    (e.toNat + 8 ≤ p.toNat + 16 ∨ p.toNat + 32 ≤ e.toNat) ∧
    (e.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat)

/-- A read apart from each of the four stores. -/
theorem rd4 (U : Addr → Byte) (p C ix E : Addr) (c : BitVec 16) (hp : p.toNat + 32 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ p.toNat + 24 ∨ p.toNat + 32 ≤ x.toNat)
    (h2 : x.toNat + n ≤ p.toNat + 16 ∨ p.toNat + 24 ≤ x.toNat)
    (h3 : x.toNat + n ≤ C.toNat + ix.toNat * 8 + 128 ∨ C.toNat + ix.toNat * 8 + 136 ≤ x.toNat)
    (h4 : x.toNat + n ≤ C.toNat + ix.toNat * 2 ∨ C.toNat + ix.toNat * 2 + 2 ≤ x.toNat) :
    List.map (Vput U p C ix E c) (byteAddrs x n) = List.map U (byteAddrs x n) := by
  have e24 : (p + 24#64).toNat = p.toNat + 24 := tAdd p 24 (by omega)
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  dsimp only [Vput]
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  all_goals (try simp only [toBytesLE_length, e24, e16, e8, e2])
  all_goals omega

theorem a2 {C ix : Addr} (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) :
    C + BitVec.ofNat 64 (2 * ix.toNat) = C + ix * 2#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [ix2 hc hk, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem a8 {C ix : Addr} (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) :
    C + BitVec.ofNat 64 (128 + 8 * ix.toNat) = C + ix * 8#64 + 128#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [ix8 hc hk, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_C {C : Addr} {k : Nat} (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : k < 640) :
    (C + BitVec.ofNat 64 k).toNat = C.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The bytes `GlB` reads: `main_arena`'s, `mp_`'s, `fs:-0x28` and `fs:24`. -/
abbrev Gr (fb a : Addr) : Prop :=
  (7940480 ≤ a.toNat ∧ a.toNat < 7943136) ∨ (8013220 ≤ a.toNat ∧ a.toNat < 8013232) ∨
    (fb.toNat - 40 ≤ a.toNat ∧ a.toNat < fb.toNat - 32) ∨ (fb.toNat + 24 ≤ a.toNat ∧ a.toNat < fb.toNat + 28)

/-- A byte apart from the four stores. -/
theorem Vput_out (U : Addr → Byte) (p C ix E : Addr) (c : BitVec 16) (hp : p.toNat + 32 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) (a : Addr)
    (h1 : a.toNat < p.toNat + 16 ∨ p.toNat + 32 ≤ a.toNat) (h2 : a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) :
    Vput U p C ix E c a = U a := by
  have e24 : (p + 24#64).toNat = p.toNat + 24 := tAdd p 24 (by omega)
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  dsimp only [Vput]
  rw [Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length, e24, e16, e8, e2])
  all_goals omega

/-- `GlB` from the bytes it reads. -/
theorem GlB.congr {F : Footprint} {Wl : List Rgn} {fb C : Addr} {V W : Addr → Byte} (h : GlB F Wl fb C V)
    (f0 : 40 ≤ fb.toNat) (f1 : fb.toNat + 28 ≤ 2 ^ 64)
    (hW : ∀ a : Addr, Gr fb a → W a = V a) :
    GlB F Wl fb C W := by
  have hm : (fb + 18446744073709551576#64).toNat = fb.toNat - 40 := by
    rw [BitVec.toNat_add, show (18446744073709551576#64 : BitVec 64).toNat = 18446744073709551576 from rfl]
    omega
  have h24 : (fb + 24#64).toNat = fb.toNat + 24 := tAdd fb 24 (by omega)
  have g : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → W a = V a) →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) := fun _ _ hx hy => Sbrk.rd_eq hx hy
  have gl : ∀ (k n : Nat), 7940480 ≤ k → k + n ≤ 7943136 →
      List.map W (byteAddrs (BitVec.ofNat 64 k) n) = List.map V (byteAddrs (BitVec.ofNat 64 k) n) :=
    fun k n h1 h2 => g _ n (by rw [BitVec.toNat_ofNat]; omega) fun a b1 b2 => by
      rw [BitVec.toNat_ofNat] at b1 b2
      exact hW a (.inl ⟨by omega, by omega⟩)
  have gp : ∀ (k n : Nat), 8013220 ≤ k → k + n ≤ 8013232 →
      List.map W (byteAddrs (BitVec.ofNat 64 k) n) = List.map V (byteAddrs (BitVec.ofNat 64 k) n) :=
    fun k n h1 h2 => g _ n (by rw [BitVec.toNat_ofNat]; omega) fun a b1 b2 => by
      rw [BitVec.toNat_ofNat] at b1 b2
      exact hW a (.inr (.inl ⟨by omega, by omega⟩))
  exact
    { hk := (congrArg (ofBytesLE 64) (gl 7940656 8 (by omega) (by omega))).trans h.hk
      tc := (congrArg (ofBytesLE 64) (g _ 8 (by omega) fun a b1 b2 =>
        hW a (.inr (.inr (.inl ⟨by omega, by omega⟩))))).trans h.tc
      t1 := (congrArg (ofBytesLE 32) (g _ 4 (by omega) fun a b1 b2 =>
        hW a (.inr (.inr (.inr ⟨by omega, by omega⟩))))).trans h.t1
      gm := (congrArg (ofBytesLE 64) (gp 8013224 8 (by omega) (by omega))).trans h.gm
      fc := (congrArg (ofBytesLE 32) (gl 7940680 4 (by omega) (by omega))).trans h.fc
      fz := fun k hk => (congrArg (ofBytesLE 64) (gl _ 8 (by omega) (by omega))).trans (h.fz k hk)
      bk := fun i h2 h63 => (congrArg (ofBytesLE 64) (gl _ 8 (by omega) (by omega))).trans (h.bk i h2 h63)
      lb := fun i h64 h126 => (congrArg (ofBytesLE 64) (gl _ 8 (by omega) (by omega))).trans (h.lb i h64 h126)
      tb := (congrArg (ofBytesLE 64) (gl 7940592 8 (by omega) (by omega))).trans h.tb
      un := (congrArg (ofBytesLE 64) (gl 7940792 8 (by omega) (by omega))).trans h.un
      m0 := (congrArg (ofBytesLE 32) (gl 7942816 4 (by omega) (by omega))).trans h.m0
      m1 := (congrArg (ofBytesLE 32) (gl 7942820 4 (by omega) (by omega))).trans h.m1
      m2 := (congrArg (ofBytesLE 32) (gl 7942824 4 (by omega) (by omega))).trans h.m2
      m3 := (congrArg (ofBytesLE 32) (gl 7942828 4 (by omega) (by omega))).trans h.m3
      p0 := (congrArg (ofBytesLE 32) (gp 8013220 4 (by omega) (by omega))).trans h.p0
      fh := h.fh, fn := h.fn, f1 := h.f1, W := h.W, gf := h.gf, tf := h.tf, pb := h.pb }

/-- `TcSt` from the bytes of the tcache and of the entries' `next` words. -/
theorem TcSt.congr {V W : Addr → Byte} {C : Addr} {bins : Nat → List Addr} (h : TcSt V C bins)
    (hc : C.toNat + 640 ≤ 2 ^ 64)
    (he : ∀ i < 64, ∀ e ∈ bins i, e.toNat + 8 ≤ 2 ^ 64 ∧
      ∀ a : Addr, e.toNat ≤ a.toNat → a.toNat < e.toNat + 8 → W a = V a)
    (hW : ∀ a : Addr, C.toNat ≤ a.toNat → a.toNat < C.toNat + 640 → W a = V a) :
    TcSt W C bins := by
  intro i hi
  obtain ⟨h1, h2, h3⟩ := h i hi
  have ec := toNat_C (k := 2 * i) hc (by omega)
  have ee := toNat_C (k := 128 + 8 * i) hc (by omega)
  refine ⟨?_, fun e he' => ?_, fun k hk => ?_⟩
  · rw [← h1]
    exact congrArg (ofBytesLE 16) (Sbrk.rd_eq (by omega) fun a b1 b2 => hW a (by omega) (by omega))
  · rw [← h2 e he']
    exact congrArg (ofBytesLE 64) (Sbrk.rd_eq (by omega) fun a b1 b2 => hW a (by omega) (by omega))
  · rw [← h3 k hk]
    obtain ⟨x8, hx⟩ := he i hi _ (List.getElem_mem (by omega : k < (bins i).length))
    exact congrArg (ofBytesLE 64) (Sbrk.rd_eq x8 hx)

/-- The tcache after the put of the chunk `p` in bin `i = ix`: its count plus one, its head `p + 16`, `p`'s `next` the
old head. -/
theorem tc_put {V : Addr → Byte} {C p ix : Addr} {bins : Nat → List Addr} (h : TcSt V C bins)
    (ha : Alloc C bins p) (hp : p.toNat + 32 ≤ 2 ^ 64) (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64)
    (cp : p.toNat + 32 ≤ C.toNat ∨ C.toNat + 640 ≤ p.toNat + 16) :
    TcSt (Vput V p C ix (tent V C ix.toNat) (tcnt V C ix.toNat + 1#16)) C (bput bins ix.toNat (p + 16#64)) := by
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h j hj
  have ec := toNat_C (k := 2 * j) hc (by omega)
  have ee := toNat_C (k := 128 + 8 * j) hc (by omega)
  by_cases hji : j = ix.toNat
  · subst hji
    simp only [bput, eq_self_iff_true, if_true, ↓reduceIte]
    refine ⟨?_, fun e he' => ?_, fun k hk' => ?_⟩
    · -- the count
      dsimp only [tcnt]
      rw [a2 hc hk]
      dsimp only [Vput]
      rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 2) rfl]
      dsimp only [tcnt] at h1
      rw [a2 hc hk] at h1
      rw [h1, List.length_cons]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · -- the head
      simp only [List.head?_cons, Option.some.injEq] at he'
      subst he'
      dsimp only [tent]
      rw [a8 hc hk]
      dsimp only [Vput]
      rw [rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
      all_goals (try simp only [toBytesLE_length, e8, e2])
      all_goals omega
    · cases k with
      | zero =>
        -- `p`'s `next`: the old head
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        have hne : 0 < (bins ix.toNat).length := by simp only [List.length_cons] at hk'; omega
        have hd : ∀ l : List Addr, 0 < l.length → l.head? = some l[0] := by
          intro l hl
          cases l with
          | nil => simp at hl
          | cons a t => simp only [List.head?_cons, List.getElem_cons_zero]
        have hh := h2 _ (hd _ hne)
        rw [← hh]
        dsimp only [Vput]
        rw [rd_Vst, rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega),
          ofBytesLE_toBytesLE (n := 8) rfl]
        all_goals (try simp only [toBytesLE_length, e16, e8, e2])
        all_goals omega
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk2 : k + 1 < (bins ix.toNat).length := by simp only [List.length_cons] at hk'; omega
        obtain ⟨x8, d1, d2⟩ := ha _ hk _ (List.getElem_mem (by omega : k < (bins ix.toNat).length))
        rw [← h3 k hk2]
        exact congrArg (ofBytesLE 64) (rd4 V p C ix _ _ hp hc hk x8 (by omega) (by omega) (by omega) (by omega))
  · simp only [bput, hji, if_false, ↓reduceIte]
    refine ⟨?_, fun e he' => ?_, fun k hk' => ?_⟩
    · rw [← h1]
      exact congrArg (ofBytesLE 16) (rd4 V p C ix _ _ hp hc hk (by omega) (by omega) (by omega) (by omega)
        (by omega))
    · rw [← h2 e he']
      exact congrArg (ofBytesLE 64) (rd4 V p C ix _ _ hp hc hk (by omega) (by omega) (by omega) (by omega)
        (by omega))
    · obtain ⟨x8, d1, d2⟩ := ha _ hj _ (List.getElem_mem (by omega : k < (bins j).length))
      rw [← h3 k hk']
      exact congrArg (ofBytesLE 64) (rd4 V p C ix _ _ hp hc hk x8 (by omega) (by omega) (by omega) (by omega))

/-- The heap after the put: `GlB` kept, the chunk's `p + 16` in front of bin `ix`, from `W` equal to the four stores
outside the frame `[S - 64, S)`, the frame apart from the tcache, from `p`'s words and from the entries' `next` words,
and the bytes `GlB` reads apart from the frame, from `p`'s words and from the tcache. -/
theorem put_inv {F : Footprint} {Wl : List Rgn} {fb C p ix S : Addr} {V W : Addr → Byte} {bins : Nat → List Addr}
    (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (ha : Alloc C bins p) (hp : p.toNat + 32 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64)
    (cp : p.toNat + 32 ≤ C.toNat ∨ C.toNat + 640 ≤ p.toNat + 16) (f0 : 40 ≤ fb.toNat)
    (f1 : fb.toNat + 28 ≤ 2 ^ 64)
    (hW : ∀ a : Addr, a.toNat < S.toNat - 64 ∨ S.toNat ≤ a.toNat →
      W a = Vput V p C ix (tent V C ix.toNat) (tcnt V C ix.toNat + 1#16) a)
    (sC : C.toNat + 640 ≤ S.toNat - 64 ∨ S.toNat ≤ C.toNat)
    (sp : p.toNat + 32 ≤ S.toNat - 64 ∨ S.toNat ≤ p.toNat + 16)
    (se : ∀ i < 64, ∀ e ∈ bins i, e.toNat + 8 ≤ S.toNat - 64 ∨ S.toNat ≤ e.toNat)
    (hG : ∀ a : Addr, Gr fb a → (a.toNat < S.toNat - 64 ∨ S.toNat ≤ a.toNat) ∧
      (a.toNat < p.toNat + 16 ∨ p.toNat + 32 ≤ a.toNat) ∧ (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat)) :
    GlB F Wl fb C W ∧ TcSt W C (bput bins ix.toNat (p + 16#64)) := by
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have hV : ∀ a : Addr, Gr fb a → W a = V a := fun a hga => by
    obtain ⟨g1, g2, g3⟩ := hG a hga
    rw [hW a g1, Vput_out V p C ix _ _ hp hc hk a g2 g3]
  refine ⟨GlB.congr hg f0 f1 hV, TcSt.congr (tc_put ht ha hp hc hk cp) hc (fun i hi e he => ?_)
    (fun a b1 b2 => hW a (by omega))⟩
  by_cases hi' : i = ix.toNat
  · subst hi'
    simp only [bput, eq_self_iff_true, if_true, ↓reduceIte, List.mem_cons] at he
    rcases he with rfl | hm
    · exact ⟨by omega, fun a b1 b2 => hW a (by omega)⟩
    · obtain ⟨x8, -, -⟩ := ha _ hk e hm
      have := se _ hk e hm
      exact ⟨x8, fun a b1 b2 => hW a (by omega)⟩
  · simp only [bput, hi', if_false, ↓reduceIte] at he
    obtain ⟨x8, -, -⟩ := ha i hi e he
    have := se i hi e he
    exact ⟨x8, fun a b1 b2 => hW a (by omega)⟩

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- The free contract on the put path: `_int_free (av, p, _)` with `PutOk`, `GlB`, `TcSt V C bins` and `p` not in
the tcache (`Alloc`) returns with `GlB` and `TcSt W C (bput bins ix (p + 16))`, `ix` the chunk's bin. The branches
`PutOk` leaves out stay open gaps (`ifr_put_ok`): the `key = tcache` scan, the full bin, the non-tcache path. -/
theorem ifr_put_inv {fb C : Addr} {bins : Nat → List Addr} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L ifr_at ifr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifr_at) (h : PutOk F Wl V fb X.cpu.gpr.rsp X.cpu.gpr.rsi)
    (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (ha : Alloc C bins X.cpu.gpr.rsi)
    (se : ∀ i < 64, ∀ e ∈ bins i, e.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat ≤ e.toNat)
    (hG : ∀ a : Addr, Gr fb a → (a.toNat < X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) ∧
      (a.toNat < X.cpu.gpr.rsi.toNat + 16 ∨ X.cpu.gpr.rsi.toNat + 32 ≤ a.toNat) ∧
      (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      GlB F Wl fb C W → TcSt W C (bput bins (tix V X.cpu.gpr.rsi).toNat (X.cpu.gpr.rsi + 16#64)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hC : tcp V fb = C := hg.tc
  have hk := h.k64
  have hc : C.toNat + 640 ≤ 2 ^ 64 := by rw [← hC]; exact h.c0
  have cs := h.cs
  have cp := h.cp
  rw [hC] at cs cp
  have hE : ent V fb X.cpu.gpr.rsi = tent V C (tix V X.cpu.gpr.rsi).toNat := by
    show rdq(V, tcp V fb + tix V X.cpu.gpr.rsi * 8#64 + 128#64) =
      rdq(V, C + BitVec.ofNat 64 (128 + 8 * (tix V X.cpu.gpr.rsi).toNat))
    rw [hC, a8 hc hk]
  have hN : tcn V fb X.cpu.gpr.rsi = tcnt V C (tix V X.cpu.gpr.rsi).toNat := by
    show ofBytesLE 16 (List.map V (byteAddrs (tcp V fb + tix V X.cpu.gpr.rsi * 2#64) 2)) =
      ofBytesLE 16 (List.map V (byteAddrs (C + BitVec.ofNat 64 (2 * (tix V X.cpu.gpr.rsi).toNat)) 2))
    rw [hC, a2 hc hk]
  refine ifr_put_ok c hfs hin hK hA hrip h hin₂ h₂ hra fun Z t' W hK' hA' hW r1 r2 r3 r4 r5 r6 r7 r8 => ?_
  have hW' : ∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat →
      W a = Vput V X.cpu.gpr.rsi C (tix V X.cpu.gpr.rsi) (tent V C (tix V X.cpu.gpr.rsi).toNat)
        (tcnt V C (tix V X.cpu.gpr.rsi).toNat + 1#16) a := fun a ha' => by
    rw [hW a ha', hE, hN, hC]
  have hp := h.p0
  have ps := h.ps
  have f0 := h.f0
  have f1 := h.f1
  obtain ⟨g1, g2⟩ := put_inv hg ht ha hp hc hk (by omega) f0 (by omega) hW' (by omega) (by omega) se hG
  exact k Z t' W hK' hA' g1 g2 r1 r2 r3 r4 r5 r6 r7 r8

end FV7z.Ifr
