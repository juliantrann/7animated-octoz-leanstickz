import FV7z.Mal.Heap
/-!
# The heap after the first `malloc`: `Gl` and the top from `Mal.After` (PLAN.md G3, `malloc`)

- `Lay`: the layout `After.near` asks for, with the tcache's chunk below the end of the new pages and the stack a
  page above the break.
- `After.gl`: `Gl` of the bytes `Mal.After` gives, the tcache `C = b + corr b + 16` (`tcache_init`'s chunk, in the
  zero bytes of the new pages or of the break's page): `__malloc_hook` cleared by `malloc_hook_ini`, the bins,
  `global_max_fast` and the arena's flags from `ptmalloc_init` (`Pmi.Dat`), the other words as at the call
  (`MPre`).
- `After.top`: `main_arena.top = Tp b + nb`, its size word `(Sz b pad & -8) - nb | 1`, `system_mem` grown by the two
  `MORECORE`s.
- `After.hp`: `Hp` (a budget `m` of the top) for the bytes that agree with `After`'s on what it reads but for the
  first block.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr size)
open FV7z.Mhi (Tp C2 Sz Vh mhi_at)
open FV7z.Im2 (VspN)
namespace FV7z.Mal

set_option maxRecDepth 8192

/-- The layout of the first `malloc`'s frame (`S`), the break `b` and the TLS block `fsb`. -/
structure Lay (fsb S b pad nb : Addr) (g : Gprs) : Prop where
  sp : g.rsp = S + 232#64
  hS : S.toNat + 512 < 2 ^ 64
  sl : 8029888 + 168 ≤ S.toNat
  bs : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat
  bS : b.toNat + 8192 ≤ S.toNat
  fs : 8029888 + 40 ≤ fsb.toNat
  fb : fsb.toNat + 48 ≤ b.toNat
  T0 : (b + corr b).toNat + 656 + nb.toNat + 16 ≤ S.toNat
  T1 : (Tp b).toNat = (b + corr b).toNat + 656
  bc : b.toNat ≤ (b + corr b).toNat
  ly : (b + corr b).toNat + 656 ≤ pageUp (b + size pad 656#64).toNat / 4096 * 4096
  n8 : 8 ≤ nb.toNat

/-- `Gl` after the first `malloc` (`MPre` at its call). -/
theorem After.gl {F F' : Footprint} {Wl : List Rgn} {fsb S b pad sm mx nb : Addr} {g : Gprs} {V M : Addr → Byte}
    (h : After fsb S b pad sm nb g V M) (hL : Lay fsb S b pad nb g) (hpre : MPre F' V b fsb pad sm mx)
    (fh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (fn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)) j))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (fsb + 24#64) i))
    (fW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (gf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (tf : ∀ i < 8, Foot F.data (Addr.add (fsb + 18446744073709551576#64) i))
    (pb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) :
    Gl F Wl fsb (b + corr b + 16#64) M := by
  have hnear := fun {a : Addr} => h.near (a := a) hL.sp hL.hS hL.sl hL.bs hL.fs hL.fb hL.T0 hL.T1 hL.bc
  obtain ⟨Vd, V₁, hD, hO, hM⟩ := h
  obtain ⟨hsp, hS, hsl, hbs, hbS, hfs, hfb, hT0, hT1, hbc, hly, hn8⟩ := hL
  obtain ⟨f24, -, f40⟩ := fofs fsb (by omega) (by omega)
  have a200 : (S + 200#64).toNat = S.toNat + 200 := by bv_omega
  have a232 : (S + 232#64).toNat = S.toNat + 232 := by bv_omega
  have e1 : (Tp b + 8#64).toNat = (Tp b).toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (Tp b + nb + 8#64).toNat = (Tp b).toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hbt := (b + corr b).isLt
  -- the bytes `M` from those after `ptmalloc_init` (`Vd`): `_int_malloc`'s words, the tcache pointer, the split
  have MD : ∀ a : Addr, a.toNat < b.toNat → ¬ (7940584 ≤ a.toNat ∧ a.toNat < 7940592) →
      ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → ¬ (7942856 ≤ a.toNat ∧ a.toNat < 7942872) →
      ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → ¬ (fsb.toNat - 40 ≤ a.toNat ∧ a.toNat < fsb.toNat - 32) →
      M a = Vd a := fun a ha h1 h2 h3 h4 h5 => by
    rw [hM a (.inl (by omega))]
    unfold VspN
    rw [Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_,
      hO.same a ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, Vst_out _ _ _ _ ?_ ?_]
    all_goals (try simp only [toBytesLE_length, e1, e2, f40, a200, pageUp, BitVec.toNat_ofNat, Nat.reduceMod])
    all_goals omega
  -- the bytes `Vd` from those at the call: `ptmalloc_init`'s words, the hook, the pushes
  have DV : ∀ a : Addr, a.toNat < S.toNat → ¬ Pmi.Wr fsb a.toNat → ¬ (7940656 ≤ a.toNat ∧ a.toNat < 7940664) →
      Vd a = V a := fun a ha h1 h2 => by
    rw [hD.out a ?_ h1, Mhi.Vh_out _ _ _ ?_ ?_ ?_, Vm_out _ _ ?_ ?_]
    all_goals (try simp only [a200, a232, hsp])
    all_goals omega
  -- the tcache's chunk: zero bytes but its size word
  have ZC : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 →
      ¬ ((b + corr b).toNat + 8 ≤ a.toNat ∧ a.toNat < (b + corr b).toNat + 16) → M a = 0 := fun a a1 a2 a3 => by
    have e : M a = V₁ a := by
      rw [hM a (.inl (by omega))]
      unfold VspN
      rw [Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_, Vst_out _ _ _ _ ?_ ?_]
      all_goals (try simp only [toBytesLE_length, e1, e2, f40, BitVec.toNat_ofNat, Nat.reduceMod])
      all_goals omega
    rw [e]
    by_cases hlo : pageUp b.toNat / 4096 * 4096 ≤ a.toNat
    · exact hO.zero a hlo (by omega) a3 (by simp only [BitVec.toNat_ofNat, Nat.reduceMod]; omega)
    · have hz : pageUp b.toNat / 4096 * 4096 ≤ b.toNat + 4095 := by unfold pageUp; omega
      rw [hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a3
        (by simp only [BitVec.toNat_ofNat, Nat.reduceMod]; omega),
        Vst_out _ _ _ _ (by simp only [toBytesLE_length, a200]; omega) (by simp only [toBytesLE_length, a200]; omega),
        DV a (by omega) (by unfold Pmi.Wr; omega) (by omega)]
      exact hpre.z a a1 (by omega)
  have Rd : ∀ (x n : Nat), 7940480 ≤ x → x + n ≤ 8029888 → x + n ≤ 7940584 ∨ 7940592 ≤ x →
      x + n ≤ 7940768 ∨ 7940776 ≤ x → x + n ≤ 7942856 ∨ 7942872 ≤ x → x + n ≤ 0x7a4c38 ∨ 0x7a4c40 ≤ x →
      List.map M (byteAddrs (BitVec.ofNat 64 x) n) = List.map Vd (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h0 h1 h2 h3 h4 h5 => rd_eq (by rw [BitVec.toNat_ofNat]; omega) fun a a1 a2 => by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at a1 a2
      exact MD a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have Rv : ∀ (x n : Nat), 7940480 ≤ x → x + n ≤ 8029888 → x + n ≤ 7940584 ∨ 7940592 ≤ x →
      x + n ≤ 7940768 ∨ 7940776 ≤ x → x + n ≤ 7942856 ∨ 7942872 ≤ x → x + n ≤ 0x7a4c38 ∨ 0x7a4c40 ≤ x →
      (∀ y, x ≤ y → y < x + n → ¬ Pmi.Wr fsb y) → x + n ≤ 7940656 ∨ 7940664 ≤ x →
      List.map M (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h0 h1 h2 h3 h4 h5 h6 h7 => (Rd x n h0 h1 h2 h3 h4 h5).trans
      (rd_eq (by rw [BitVec.toNat_ofNat]; omega) fun a a1 a2 => by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at a1 a2
        exact DV a (by omega) (h6 _ a1 a2) (by omega))
  have nW : ∀ (x n : Nat), x + n ≤ 8013224 → (x + n ≤ 7940784 ∨ 7942816 ≤ x) →
      (x + n ≤ 7940768 ∨ 7940776 ≤ x) → (x + n ≤ 7940680 ∨ 7940684 ≤ x) → (x + n ≤ 7940484 ∨ 7940488 ≤ x) →
      ∀ y, x ≤ y → y < x + n → ¬ Pmi.Wr fsb y := fun x n h1 h2 h3 h4 h5 y y1 y2 => by
    unfold Pmi.Wr; omega
  refine ⟨?_, ?_, fun i hi => ?_, ?_, ?_, ?_, fun k hk => ?_, fun i i1 i2 => ?_, fun i i1 i2 => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fh, fn, f1, fW, gf, tf, pb⟩
  · -- the hook, cleared by `malloc_hook_ini`
    have e0 : (7940656#64 : Addr).toNat = 7940656 := rfl
    obtain ⟨r1, r2, r3, r4⟩ := Mhi.r4 (S + 232#64) (by omega)
    have l8 : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
    rw [(Rd 7940656 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)),
      congrArg (ofBytesLE 64) (rd_eq (V := Vh (S + 232#64) g (Vm g V)) (x := 7940656#64) (n := 8) (by rw [e0]; omega)
        fun a a1 a2 => hD.out a (by rw [a200]; rw [e0] at a1 a2; omega) (by unfold Pmi.Wr; rw [e0] at a1 a2; omega))]
    unfold Vh
    rw [rd_Vst _ _ _ _ _ (by rw [l8, r4]; omega) (by rw [e0]; omega) (.inr (by rw [r4, e0]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l8, r3]; omega) (by rw [e0]; omega) (.inr (by rw [r3, e0]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l8, r2]; omega) (by rw [e0]; omega) (.inr (by rw [r2, e0]; omega)),
      rd_Vst_self _ _ _ (l8 _) (by rw [e0]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · -- the tcache pointer
    have l8 : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
    rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN (Tp b) (Sz b pad) nb
        (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)))
        (x := fsb + 18446744073709551576#64) (n := 8) (by rw [f40]; omega)
        fun a a1 a2 => hM a (.inl (by rw [f40] at a2; omega))),
      Im2.VspN_rd _ (by omega) (by rw [f40]; omega) (.inr (by rw [f40]; omega)) (.inl (by rw [f40]; omega)) hn8,
      rd_Vst_self _ _ _ (l8 _) (by rw [f40]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · -- the tcache's counts: zero bytes
    have eC : ∀ j < 2, (Addr.add (b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)) j).toNat =
        (b + corr b).toNat + 16 + 2 * i + j := fun j hj => by
      simp only [Addr.add]
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat]
      omega
    exact Mhi.z16 fun j hj => ZC _ (by rw [eC j hj]; omega) (by rw [eC j hj]; omega) (by rw [eC j hj]; omega)
  · -- one thread
    rw [rd_eq (V := V) (x := fsb + 24#64) (n := 4) (by rw [f24]; omega) fun a a1 a2 => hnear (by rw [f24] at a2; omega)
      (by rw [f24] at a1; omega) (by rw [f24] at a1; omega) (by rw [f24] at a1; omega)
      (by rw [f24] at a1; omega)]
    exact hpre.mt
  · rw [(Rd 8013224 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact hD.gmf
  · rw [(Rd 7940680 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact hD.flg
  · rw [(Rv (7940688 + 8 * k) 8 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.fz k hk
  · rw [(Rd (7940776 + 16 * i) 8 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))]
    have e : 7940776 + 16 * i = 7940792 + 16 * (i - 1) := by omega
    have e' : 7940752 + 16 * i = 7940768 + 16 * (i - 1) := by omega
    rw [e, e']
    exact (hD.bins (i - 1) (by omega)).2
  · rw [(Rd (7940768 + 16 * i) 8 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))]
    have e : 7940768 + 16 * i = 7940784 + 16 * (i - 1) := by omega
    have e' : 7940752 + 16 * i = 7940768 + 16 * (i - 1) := by omega
    rw [e, e']
    exact (hD.bins (i - 1) (by omega)).1
  · rw [(Rv 7940592 8 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.tb
  · rw [(Rd 7940792 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact (hD.bins 0 (by omega)).2
  · rw [(Rv 7942816 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.m0
  · rw [(Rv 7942820 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.m1
  · rw [(Rv 7942824 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.m2
  · rw [(Rv 7942828 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (nW _ _ (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega))]
    exact hpre.m3
  · have e0 : (8013220#64 : Addr).toNat = 8013220 := rfl
    rw [rd_eq (V := V) (x := 8013220#64) (n := 4) (by rw [e0]; omega) fun a a1 a2 => hnear (by rw [e0] at a2; omega)
      (by rw [e0] at a1 a2; omega) (by rw [e0] at a1 a2; omega) (by rw [e0] at a1 a2; omega)
      (by rw [e0] at a1 a2; omega)]
    exact hpre.p0

/-- The top after the first `malloc`: `Tp b + nb`, its size word, `system_mem`. -/
theorem After.top {fsb S b pad sm nb : Addr} {g : Gprs} {V M : Addr → Byte}
    (h : After fsb S b pad sm nb g V M) (hL : Lay fsb S b pad nb g) :
    rdq(M, 7940768#64) = Tp b + nb ∧
      rdq(M, Tp b + nb + 8#64) = (Sz b pad &&& 18446744073709551608#64) - nb ||| 1#64 ∧
      rdq(M, 7942856#64) = sm + size pad 656#64 + C2 b pad := by
  obtain ⟨Vd, V₁, hD, hO, hM⟩ := h
  obtain ⟨hsp, hS, hsl, hbs, hbS, hfs, hfb, hT0, hT1, hbc, hly, hn8⟩ := hL
  obtain ⟨-, -, f40⟩ := fofs fsb (by omega) (by omega)
  have e2 : (Tp b + nb + 8#64).toNat = (Tp b).toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  have l8 : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN (Tp b) (Sz b pad) nb
        (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)))
        (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 => hM a (.inl (by rw [et] at a2; omega)))]
    exact VspN_top _ (by omega) (by omega)
  · rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN (Tp b) (Sz b pad) nb
        (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)))
        (x := Tp b + nb + 8#64) (n := 8) (by rw [e2]; omega) fun a a1 a2 => hM a (.inl (by rw [e2] at a2; omega)))]
    exact VspN_rest _ (by omega)
  · rw [congrArg (ofBytesLE 64) (rd_eq (V := VspN (Tp b) (Sz b pad) nb
        (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)))
        (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 => hM a (.inl (by rw [es] at a2; omega))),
      Im2.VspN_rd _ (by omega) (by rw [es]; omega) (.inr (by rw [es]; omega)) (.inl (by rw [es]; omega)) hn8,
      rd_Vst _ _ _ _ _ (by rw [l8, f40]; omega) (by rw [es]; omega) (.inr (by rw [f40, es]; omega))]
    exact hO.sys

/-- `Hp` after the first `malloc` (`After`; the tcache at `b + corr b + 16`, the top at `Tp b + nb`) for bytes `W`
that agree with `M` on what `Hp` reads (`GlR` up to the top's size word) but for `[Tp b + 16, Tp b + 16 + s)` (in
the first block): a budget `m`
of the rest of the top in the footprint and below `hi`, the brk above `0x7a9000` (`Kn`). -/
theorem After.hp {F F' : Footprint} {Wl : List Rgn} {fsb S b pad sm mx nb : Addr} {g : Gprs} {V M W : Addr → Byte}
    {hi m s : Nat} (h : After fsb S b pad sm nb g V M) (hL : Lay fsb S b pad nb g) (hpre : MPre F' V b fsb pad sm mx)
    (fh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (fn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)) j))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (fsb + 24#64) i))
    (fW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (gf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (tf : ∀ i < 8, Foot F.data (Addr.add (fsb + 18446744073709551576#64) i))
    (pb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i))
    (hbk : 8032256 ≤ b.toNat) (hs : s + 8 ≤ nb.toNat) (hn8 : nb.toNat % 8 = 0)
    (hnb : nb.toNat ≤ (Sz b pad &&& 18446744073709551608#64).toNat)
    (hm : m ≤ (Sz b pad &&& 18446744073709551608#64).toNat - nb.toNat) (hm16 : 16 ≤ m)
    (hsm : (Sz b pad &&& 18446744073709551608#64).toNat - nb.toNat ≤ (sm + size pad 656#64 + C2 b pad).toNat)
    (hhi : (Tp b).toNat + nb.toNat + m ≤ hi) (hhi2 : hi < 2 ^ 64)
    (hTF : ∀ a : Addr, (Tp b).toNat + nb.toNat ≤ a.toNat → a.toNat < (Tp b).toNat + nb.toNat + m →
      Foot Wl a ∧ Foot F.data a)
    (hW : ∀ a : Addr, GlR ((Tp b).toNat + nb.toNat + 16) a →
      (a.toNat < (Tp b).toNat + 16 ∨ (Tp b).toNat + 16 + s ≤ a.toNat) → W a = M a) :
    Hp F Wl fsb hi m W := by
  have G := After.gl h hL hpre fh fn f1 fW gf tf pb
  obtain ⟨t1, t2, t3⟩ := After.top h hL
  obtain ⟨-, -, -, -, -, hfs, hfb, hT0, hT1, hbc, -, -⟩ := hL
  have ha8 := Smm.and_m8 (Sz b pad)
  have eC : (b + corr b + 16#64).toNat = (b + corr b).toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eT : (Tp b + nb).toNat = (Tp b).toNat + nb.toNat := by rw [BitVec.toNat_add]; omega
  have e8 : (Tp b + nb + 8#64).toNat = (Tp b).toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx : ((Sz b pad &&& 18446744073709551608#64) - nb).toNat =
      (Sz b pad &&& 18446744073709551608#64).toNat - nb.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hs' : (((Sz b pad &&& 18446744073709551608#64) - nb ||| 1#64) &&& 18446744073709551608#64).toNat =
      (Sz b pad &&& 18446744073709551608#64).toNat - nb.toNat := by
    rw [Mhi.or1_m8, hx]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨b + corr b + 16#64, Tp b + nb, (Sz b pad &&& 18446744073709551608#64) - nb ||| 1#64,
    sm + size pad 656#64 + C2 b pad,
    G.mvR (E := (Tp b).toNat + 16) (by omega) (by omega) (by rw [eC]; omega) (by rw [eC]; omega) (by omega)
      fun a ha _ => hW a (by unfold GlR at ha ⊢; omega) (.inl (by unfold GlR at ha; omega)),
    by omega, by rw [eT]; omega, by rw [eC]; omega, by rw [eC, eT]; omega, by rw [eT]; omega, by rw [eT]; omega,
    hhi2, ?_, ?_, ?_, by rw [hs']; exact hsm, by rw [hs']; exact hm,
    fun a a1 a2 => hTF a (by rw [eT] at a1; omega) (by rw [eT] at a2; omega)⟩
  · rw [rd_eq (V := M) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [et] at a1 a2; omega) (.inl (by rw [et] at a2; omega))]
    exact t1
  · rw [rd_eq (V := M) (x := Tp b + nb + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [e8] at a1 a2; omega) (.inr (by rw [e8] at a1; omega))]
    exact t2
  · rw [rd_eq (V := M) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [es] at a1 a2; omega) (.inl (by rw [es] at a2; omega))]
    exact t3

end FV7z.Mal
