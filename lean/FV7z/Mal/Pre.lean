import FV7z.Mal.RunN
/-!
# What the first `malloc` reads below the break, as one hypothesis (PLAN.md G3, `malloc`)

- `MPre F V b fsb pad sm mx`: the conditions of `mal_firstn` on the bytes `V` below `b + 4096` (`b` the break): the
  hook, `mp_`, `main_arena`, the TLS words at `fsb`, the words of `tunables`, `__curbrk`, the zero bytes up to the
  page of `b`.
- `MPre.lo`: the same for bytes `W` that agree with `V` below `b + 4096` (a caller's stack writes, say).
- `far`: after `mal_firstn`, the bytes of the caller's stack above the frame of `malloc` (`S + 240` on) as at the call.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr size)
open FV7z.Mhi (Tp C2 Sz Vh mhi_at)
open FV7z.Im2 (VspN)
namespace FV7z.Mal

/-- The conditions of `mal_firstn` on the bytes below `b + 4096`. -/
structure MPre (F : Footprint) (V : Addr → Byte) (b fsb pad sm mx : Addr) : Prop where
  hook : rdq(V, 7940656#64) = Mhi.mhi_at
  mi : (rdd(V, 7940484#64)).msb = true
  u32 : ∀ d ∈ Pmi.t32, Tgv.Unset F V d
  u64 : ∀ d ∈ Pmi.t64, Tgv.UnsetW F V d
  sd : ofBytesLE 8 ((byteAddrs (fsb + 18446744073709551584#64) 1).map V) = 0#8
  mt : rdd(V, fsb + 24#64) = 0
  lk : rdd(V, 7940672#64) = 0
  tc : rdq(V, fsb + 18446744073709551576#64) = 0#64
  fz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64
  tb : rdq(V, 7940592#64) = 64#64
  m0 : rdd(V, 7942816#64) = 0
  m1 : rdd(V, 7942820#64) = 0
  m2 : rdd(V, 7942824#64) = 0
  m3 : rdd(V, 7942828#64) = 0
  ps : rdq(V, 7943128#64) = 4096#64
  thr : 656 < (rdq(V, 7940528#64)).toNat
  sz : rdq(V, 7940776#64) = 0#64
  hpad : rdq(V, 7940520#64) = pad
  fl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8
  mc : rdq(V, 7942872#64) = Dmc.dmc_at
  cb : rdq(V, curbrk) = b
  ml0 : rdd(V, 7944640#64) = 0
  k0 : rdq(V, 8013152#64) = 0#64
  hsm : rdq(V, 7942856#64) = sm
  sb : rdq(V, 7940584#64) = 0#64
  hmx : rdq(V, 7942864#64) = mx
  p0 : rdd(V, 8013220#64) = 0
  z : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → V a = 0

theorem g32 : ∀ d ∈ Pmi.t32, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
  simp only [Pmi.t32, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

theorem g64 : ∀ d ∈ Pmi.t64, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
  simp only [Pmi.t64, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `MPre` for bytes that agree below `b + 4096`. -/
theorem MPre.lo {F : Footprint} {V W : Addr → Byte} {b fsb pad sm mx : Addr} (h : MPre F V b fsb pad sm mx)
    (hfs : 8029888 + 40 ≤ fsb.toNat) (hfb : fsb.toNat + 48 ≤ b.toNat)
    (hW : ∀ a : Addr, a.toNat < b.toNat + 4096 → W a = V a) : MPre F W b fsb pad sm mx := by
  have hbt := b.isLt
  obtain ⟨f24, f32, f40⟩ := fofs fsb (by omega) (by omega)
  have R : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ b.toNat →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n hx => rd_eq (by omega) fun a _ h2 => hW a (by omega)
  have Rc : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 8029888 →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) := fun x n hx => R x n (by omega)
  have hlo : ∀ a : Addr, ¬ (b.toNat ≤ a.toNat ∧ a.toNat < 2 ^ 64) → W a = V a := fun a ha => by
    have := a.isLt
    exact hW a (by omega)
  refine
    { hook := by rw [Rc (7940656#64) 8 (by decide)]; exact h.hook
      mi := by rw [Rc (7940484#64) 4 (by decide)]; exact h.mi
      u32 := fun d hd => (h.u32 d hd).out (lo := b.toNat) (hi := 2 ^ 64) (by have := g32 d hd; omega) (by omega) hlo
      u64 := fun d hd => (h.u64 d hd).out (lo := b.toNat) (hi := 2 ^ 64) (by have := g64 d hd; omega) (by omega) hlo
      sd := by rw [R _ 1 (by rw [f32]; omega)]; exact h.sd
      mt := by rw [R _ 4 (by rw [f24]; omega)]; exact h.mt
      lk := by rw [Rc (7940672#64) 4 (by decide)]; exact h.lk
      tc := by rw [R _ 8 (by rw [f40]; omega)]; exact h.tc
      fz := fun k hk => by
        rw [Rc (BitVec.ofNat 64 (7940688 + 8 * k)) 8 (by rw [BitVec.toNat_ofNat]; omega)]
        exact h.fz k hk
      tb := by rw [Rc (7940592#64) 8 (by decide)]; exact h.tb
      m0 := by rw [Rc (7942816#64) 4 (by decide)]; exact h.m0
      m1 := by rw [Rc (7942820#64) 4 (by decide)]; exact h.m1
      m2 := by rw [Rc (7942824#64) 4 (by decide)]; exact h.m2
      m3 := by rw [Rc (7942828#64) 4 (by decide)]; exact h.m3
      ps := by rw [Rc (7943128#64) 8 (by decide)]; exact h.ps
      thr := by rw [Rc (7940528#64) 8 (by decide)]; exact h.thr
      sz := by rw [Rc (7940776#64) 8 (by decide)]; exact h.sz
      hpad := by rw [Rc (7940520#64) 8 (by decide)]; exact h.hpad
      fl := by rw [Rc (7940676#64) 1 (by decide)]; exact h.fl
      mc := by rw [Rc (7942872#64) 8 (by decide)]; exact h.mc
      cb := by rw [Rc (curbrk) 8 (by decide)]; exact h.cb
      ml0 := by rw [Rc (7944640#64) 4 (by decide)]; exact h.ml0
      k0 := by rw [Rc (8013152#64) 8 (by decide)]; exact h.k0
      hsm := by rw [Rc (7942856#64) 8 (by decide)]; exact h.hsm
      sb := by rw [Rc (7940584#64) 8 (by decide)]; exact h.sb
      hmx := by rw [Rc (7942864#64) 8 (by decide)]; exact h.hmx
      p0 := by rw [Rc (8013220#64) 4 (by decide)]; exact h.p0
      z := fun a h1 h2 => by
        have : pageUp b.toNat / 4096 * 4096 ≤ b.toNat + 4095 := by unfold pageUp; omega
        rw [hW a (by omega)]
        exact h.z a h1 h2 }

/-- The bytes after `mal_firstn` (`hD`, `hO`, `hM` of its continuation, `g` the registers at the call) at `S + 240`
and above, the heap below `S`: as at the call. -/
theorem far {b fsb pad sm nb S : Addr} {g : Gprs} {V Vd V₁ M : Addr → Byte}
    (hD : Pmi.Dat fsb (S + 200#64) 1 (Vh (S + 232#64) g (Vm g V)) Vd)
    (hO : Imm.Out (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) V₁ b 656#64 (size pad 656#64) (C2 b pad)
      sm (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
      (S.toNat - 168) (S.toNat + 200))
    (hM : ∀ a : Addr, a.toNat < S.toNat + 24 ∨ S.toNat + 208 ≤ a.toNat →
      M a = VspN (Tp b) (Sz b pad) nb (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) a)
    (hsp : g.rsp = S + 232#64) (hS : S.toNat + 512 < 2 ^ 64) (hsl : 8029888 + 168 ≤ S.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat)
    (hfs : 8029888 + 40 ≤ fsb.toNat) (hfb : fsb.toNat + 48 ≤ b.toNat)
    (hT0 : (b + corr b).toNat + 656 + nb.toNat + 16 ≤ S.toNat) (hT1 : (Tp b).toNat = (b + corr b).toNat + 656)
    {a : Addr} (ha : S.toNat + 240 ≤ a.toNat) : M a = V a := by
  have hat := a.isLt
  obtain ⟨-, -, f40⟩ := fofs fsb (by omega) (by omega)
  have a200 : (S + 200#64).toNat = S.toNat + 200 := by bv_omega
  have a232 : (S + 232#64).toNat = S.toNat + 232 := by bv_omega
  have e1 : (Tp b + 8#64).toNat = (Tp b).toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (Tp b + nb + 8#64).toNat = (Tp b).toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hM a (.inr (by omega))]
  unfold VspN
  rw [Tun.Vst_out _ _ _ _ ?_ ?_, Tun.Vst_out _ _ _ _ ?_ ?_, Tun.Vst_out _ _ _ _ ?_ ?_, Tun.Vst_out _ _ _ _ ?_ ?_,
    hO.same a ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, Tun.Vst_out _ _ _ _ ?_ ?_, hD.out a ?_ ?_, Mhi.Vh_hi _ _ _ ?_ ?_,
    Vm_out _ _ ?_ ?_]
  all_goals (try simp only [toBytesLE_length, e1, e2, f40, a200, a232, hsp, pageUp, Pmi.Wr, BitVec.toNat_ofNat,
    Nat.reduceMod])
  all_goals omega

end FV7z.Mal
