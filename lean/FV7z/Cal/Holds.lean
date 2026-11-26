import FV7z.Cal.Vc
import FV7z.Ipa.Set
/-!
# `__libc_calloc`: `_int_malloc`, then `memset` or the inline stores (PLAN.md §M, M1)

glibc 2.31's `__libc_calloc (n, m)` at `0x634a60` in `7zzs`, on the way of one thread, the hook null and the
`tcache` made: `r13`, `r12`, `rbp`, `rbx` saved, `n * m` (no overflow), `main_arena`'s top chunk `T` and its size
`O` kept, `_int_malloc (&main_arena, n * m)` (`ImAt`, assumed), the chunk `p` not mmapped and of the main arena,
`perturb_byte` 0, then `csz - 8` bytes from `p` cleared (`csz`: the chunk's size `C`, or `O` when `p` was cut from
the old top and `O` is smaller, as glibc relies on fresh memory being 0): more than 79 bytes by `memset` through
the PLT (`Ipa.SetAt`), else by the inline stores of `xmm0` (24, 40, 56 or 72 bytes: `cln`).

- `ImAt`: what a `call` of `_int_malloc` at `e` does (assumed; like `Mal.At`).
- `fr4_out`, `fr_out`, `rd_eq`, `rd_out`, `slot`, `tm8`: the frame and reads where memories agree.
- `inl`: from 252 (the inline stores) to 196, the bytes from `p` cleared.
- `cal_ok`: the run from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Cal
set_option maxRecDepth 100000

/-- What a `call` of `_int_malloc` at `e` does (assumed here), for the footprint `F`, `Wl` and the TLS block `fb`:
called with `rdi = &main_arena`, `rsi ≤ 1024`, a return address in code and `Pm (k + 1)`, the stack from `hi` to the
slot of the return address in `Wl` and `hi + 216 ≤ rsp`, the run gets back to the return address with `rsp + 8`,
the registers a call keeps kept, `rax = p` with `0x792980 ≤ p`, the chunk's size word `Zs` at `p - 8` (bits 1 and
2 clear: not mmapped, of the main arena), its size `C = Zs & ~7` at least 32 and `rsi + 8`, `p + C ≤ rsp`, the
bytes from `p - 8` to `p + C - 8` in the footprint, the bytes below `0x792980` and from the caller's `rsp` up as
they were, `fs:0x18` and `perturb_byte` as they were, and `Pm k` for the bytes that keep the ones from `0x792980`
to the slot of the return address apart from the chunk. -/
def ImAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle) (fb : Addr)
    (hi : Nat) (e : Addr) (Pm : Nat → (Addr → Byte) → Prop) : Prop :=
  ∀ {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte} {j k : Nat},
    Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm (k + 1) V →
    X.cpu.gpr.rdi = 7940672#64 → X.cpu.gpr.rsi.toNat ≤ 1024 → s₀.cpu.seg.fsBase = fb →
    hi + 216 ≤ X.cpu.gpr.rsp.toNat → X.cpu.gpr.rsp.toNat + 48 < 2 ^ 64 →
    (∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot Wl a) →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ Z t' V₂ (p Zs : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      7940480 ≤ p.toNat → rdq(V₂, p + 18446744073709551608#64) = Zs →
      Zs.setWidth 8 &&& 2#8 = 0#8 → Zs.setWidth 8 &&& 4#8 = 0#8 →
      X.cpu.gpr.rsi.toNat + 8 ≤ (Zs &&& 18446744073709551608#64).toNat →
      32 ≤ (Zs &&& 18446744073709551608#64).toNat →
      p.toNat + (Zs &&& 18446744073709551608#64).toNat ≤ X.cpu.gpr.rsp.toNat →
      (∀ a : Addr, p.toNat ≤ a.toNat + 8 → a.toNat + 8 < p.toNat + (Zs &&& 18446744073709551608#64).toNat →
        Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940480 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ a.toNat → V₂ a = V a) →
      rdd(V₂, fb + 24#64) = rdd(V, fb + 24#64) → rdd(V₂, 8013220#64) = rdd(V, 8013220#64) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat →
        (a.toNat < p.toNat ∨ p.toNat + (Zs &&& 18446744073709551608#64).toNat ≤ a.toNat + 8) → W a = V₂ a) →
        Pm k W) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-! ## The frame, reads -/

/-- The four pushes and the return address of the `call` under `S`. -/
abbrev fr5 (V : Addr → Byte) (S : Addr) (a b c d r : BitVec 64) : Addr → Byte :=
  Vst (fr4 V S a b c d) (S - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE r 8)

theorem fr4_out (V : Addr → Byte) (S : Addr) (a b c d : BitVec 64) (hS : 32 ≤ S.toNat) (x : Addr)
    (hx : ¬ (S.toNat - 32 ≤ x.toNat ∧ x.toNat < S.toNat)) : fr4 V S a b c d x = V x := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, e4⟩ := fr_e hS
  unfold fr4
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

theorem e5s {S : Addr} (hS : 48 ≤ S.toNat) : (S - 8 - 8 - 8 - 8 - 8#64).toNat = S.toNat - 40 := by
  obtain ⟨-, -, -, e4⟩ := fr_e (S := S) (by omega)
  rw [t8 (by rw [e4]; omega), e4]; omega

theorem e6s {S : Addr} (hS : 48 ≤ S.toNat) : (S - 8 - 8 - 8 - 8 - 8#64 - 8).toNat = S.toNat - 48 := by
  have e5 := e5s hS
  rw [Prepare.toNat_sub8 (by rw [e5]; omega), e5]; omega

theorem fr_out (V : Addr → Byte) (S : Addr) (a b c d r : BitVec 64) (hS : 48 ≤ S.toNat) (x : Addr)
    (hx : ¬ (S.toNat - 48 ≤ x.toNat ∧ x.toNat < S.toNat)) : fr5 V S a b c d r x = V x := by
  have hl := S.isLt
  have e6 := e6s hS
  unfold fr5
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega)]
  exact fr4_out V S a b c d (by omega) x (by omega)

theorem a5s (S : Addr) : S - 8 - 8 - 8 - 8 - 8#64 + 8#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a4s (S : Addr) : S - 8 - 8 - 8 - 8 + 8 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem a1s (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- Bytes read where two memories agree. -/
theorem rd_eq {V V' : Addr → Byte} {P : Addr → Prop} (h : ∀ a, P a → V' a = V a) {x : Addr} {n : Nat}
    (hP : ∀ i < n, P (Addr.add x i)) : List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  exact h _ (hP i hi)

/-- Bytes outside `[lo, up)`, read where two memories agree outside it. -/
theorem rd_out {V V' : Addr → Byte} {lo up : Nat} (h : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < up) → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ lo ∨ up ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_eq h fun i hi => by rw [toNat_add_of_fits hi hx]; omega

/-- Eight bytes from `b` in the stack below `s`. -/
theorem slot {Wl : List Rgn} {hi : Nat} {s : Addr} (hstk : ∀ a : Addr, hi ≤ a.toNat → a.toNat < s.toNat → Foot Wl a)
    {b : Addr} (h1 : hi ≤ b.toNat) (h2 : b.toNat + 8 ≤ s.toNat) : ∀ i < 8, Foot Wl (Addr.add b i) := fun i hi' => by
  have hl := s.isLt
  have e := toNat_add_of_fits (a := b) (n := 8) hi' (by omega)
  exact hstk _ (by rw [e]; omega) (by rw [e]; omega)

/-- `p - 8` in numbers. -/
theorem tm8 {p : Addr} (h : 8 ≤ p.toNat) : (p + 18446744073709551608#64).toNat = p.toNat - 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

/-! ## The sizes -/

theorem csz_le (p T O C : Addr) : (csz p T O C).toNat ≤ C.toNat := by
  unfold csz
  split
  · split <;> omega
  · omega

theorem csz_ge {p T O C : Addr} (hO : 32 ≤ O.toNat) (hC : 32 ≤ C.toNat) : 32 ≤ (csz p T O C).toNat := by
  unfold csz
  split
  · split <;> omega
  · omega

/-- How many of `c` bytes the stores clear: 24, 40, 56 or 72 inline, all by `memset`. -/
def cln (c : Nat) : Nat :=
  if c ≤ 39 then 24 else if c ≤ 55 then 40 else if c ≤ 71 then 56 else if c ≤ 79 then 72 else c

theorem cln_a {c : Nat} (h : c ≤ 39) : cln c = 24 := by rw [cln, if_pos h]
theorem cln_b {c : Nat} (h1 : 39 < c) (h2 : c ≤ 55) : cln c = 40 := by
  rw [cln, if_neg (by omega), if_pos h2]
theorem cln_c {c : Nat} (h1 : 55 < c) (h2 : c ≤ 71) : cln c = 56 := by
  rw [cln, if_neg (by omega), if_neg (by omega), if_pos h2]
theorem cln_d {c : Nat} (h1 : 71 < c) (h2 : c ≤ 79) : cln c = 72 := by
  rw [cln, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
theorem cln_e {c : Nat} (h : 79 < c) : cln c = c := by
  rw [cln, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem cln_le {c : Nat} (h : 24 ≤ c) : cln c ≤ c := by
  unfold cln
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split <;> omega

/-! ## The inline stores -/

theorem z_all (w : Nat) : ByteAll (0#w) 0 := fun i _ => by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat]

/-- `cmp rdx, n` then `jbe`: taken just when `rdx ≤ n`. -/
theorem jbe_cmp {g : Gprs} {f fl : Rflags} {n : Nat} (hn : n < 2 ^ 64)
    (h : fl = subF (rfz f) (gv g 64 2) (Src.val 64 g (.i n))) : fl.cond 6 = decide (g.rdx.toNat ≤ n) := by
  subst h
  rw [cond_6, subF_cf, subF_zf]
  simp only [gv, Src.val, sw_64_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact be_imm (g.get (regOf 2)) n hn

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- From 252 to 196: `cl` bytes from `p` (`r8`) to clear, `rdx = cl` from 24 to 79: the first `cln cl` of them
cleared by `pxor xmm0, xmm0`, `mov qword [r8 + 16], 0` and the `movups` of `xmm0`, the registers kept. -/
theorem inl (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cal_at cal) {X : State} {t : Nat} {V : Addr → Byte}
    {p : Addr} {cl : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cal_at.add 252)
    (hp : X.cpu.gpr.r8 = p) (hc : X.cpu.gpr.rdx.toNat = cl) (hlo : 24 ≤ cl) (hhi : cl ≤ 79)
    (hf : p.toNat + cl ≤ 2 ^ 64) (hW : ∀ i < cl, Foot Wl (p.add i))
    (k : ∀ Y t' W, KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = cal_at.add 196 →
      Y.cpu.gpr = X.cpu.gpr → FillP V W p cl 0 (fun i => i < cln cl) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hWo : ∀ a i, a + i < cl → Foot Wl ((p.add a).add i) := fun a i h => by
    rw [addr_add_add]; exact hW _ h
  have ea : ∀ {Y : State} (d : Nat), Y.cpu.gpr = X.cpu.gpr → eaD Y 8 d = p.add d := fun d h => by
    show _ + BitVec.ofNat 64 d = p + BitVec.ofNat 64 d
    rw [h]
    exact congrArg (· + BitVec.ofNat 64 d) hp
  have z16 : ∀ x ∈ toBytesLE (0#128) 16, x = 0 := (z_all 128).bytes (by decide)
  have z8 : ∀ x ∈ toBytesLE (BitVec.ofNat 64 0) (64 / 8), x = 0 := (z_all 64).bytes (by decide)
  -- `pxor xmm0, xmm0`
  refine c.s_blkV hin (bpx prof) hK hA hrip ?_
  dsimp only [wpV, VOp.pxor]
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun h => absurd h Bool.false_ne_true, ?_⟩
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx1
  have hz1 : xlo Y1 0 = 0#128 := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 0) = 0#128
    rw [hx1, xset_same, BitVec.xor_self]
  -- `mov qword [r8 + 16], 0`
  have e16 : eaG Y1.cpu.gpr (some 8) none 1 16 = p.add 16 := by
    show Y1.cpu.gpr.get (regOf 8) + 0 * BitVec.ofNat 64 1 + BitVec.ofNat 64 16 = p + BitVec.ofNat 64 16
    rw [hg1, z_mul64, add_z64]
    exact congrArg (· + BitVec.ofNat 64 16) hp
  refine c.s_blkA_v hin ((blk_256 prof).at cal_at) Y1.cpu.vec hK1 hA1 hr1 rfl rfl ?_
  dsimp only [o17, wp, Op.sti]
  rw [e16]
  refine ⟨toBytesLE_length _ _, fun i hi => hWo 16 i (by omega), ?_⟩
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hv2
  have hF2 := (FillP.start V p cl 0).st hf (toBytesLE_length _ _) (by omega) z8 (o := 16)
  have hg2' : Y2.cpu.gpr = X.cpu.gpr := hg2.trans hg1
  have hz2 : xlo Y2 0 = 0#128 := by
    show (Y2.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv2]; exact hz1
  -- `movups [r8], xmm0`
  refine c.s_movups_stv hK2 hA2 hin (lt_len (by decide)) hr2 (mv_264 _) (fun i hi => ?_) ?_
  · rw [ea 0 hg2']; exact hWo 0 i (by omega)
  intro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  rw [ea 0 hg2', hz2] at hA3
  have hF3 := hF2.st hf (toBytesLE_length _ _) (by omega) z16 (o := 0)
  have hg3' : Y3.cpu.gpr = X.cpu.gpr := hg3.trans hg2'
  have hz3 : xlo Y3 0 = 0#128 := by
    show (Y3.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv3]; exact hz2
  -- `cmp rdx, 39`, `jbe 196`
  refine c.s_blkA_v hin ((blk_268 prof).at cal_at) Y3.cpu.vec hK3 hA3 hr3 rfl rfl ?_
  dsimp only [o18, wp, Op.cmp]
  intro fl hfl Y4 t4 hK4 hA4 hr4 hg4 hf4 hv4
  have hg4' : Y4.cpu.gpr = X.cpu.gpr := hg4.trans hg3'
  have hb4 := jbe_cmp (by decide) hfl
  rw [hg3', hc] at hb4
  refine c.s_jccV hK4 hA4 hin (lt_len (by decide)) hr4 (jb_272 _) (tgt := 196) (by decide) (lt_len (by decide))
    (fun h6 => ?_) (fun h6 => ?_)
  · rw [hf4, hb4] at h6
    have h39 := of_decide_eq_true h6
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, -⟩
    exact k Y5 t5 _ hK5 hA5 hr5 (hg5.trans hg4') (hF3.mono fun i hi hc' => by
      rw [cln_a h39] at hc'; try dsimp only at hc' ⊢
      omega)
  rw [hf4, hb4] at h6
  have h39 := of_decide_eq_false h6
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have hg5' : Y5.cpu.gpr = X.cpu.gpr := hg5.trans hg4'
  have hz5 : xlo Y5 0 = 0#128 := by
    show (Y5.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv5, hv4]; exact hz3
  -- `movups [r8 + 24], xmm0`
  refine c.s_movups_stv hK5 hA5 hin (lt_len (by decide)) hr5 (mv_274 _) (fun i hi => ?_) ?_
  · rw [ea 24 hg5']; exact hWo 24 i (by omega)
  intro Y6 t6 hK6 hA6 ⟨hr6, hg6, hv6⟩
  rw [ea 24 hg5', hz5] at hA6
  have hF6 := hF3.st hf (toBytesLE_length _ _) (by omega) z16 (o := 24)
  have hg6' : Y6.cpu.gpr = X.cpu.gpr := hg6.trans hg5'
  have hz6 : xlo Y6 0 = 0#128 := by
    show (Y6.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv6]; exact hz5
  -- `cmp rdx, 55`, `jbe 196`
  refine c.s_blkA_v hin ((blk_279 prof).at cal_at) Y6.cpu.vec hK6 hA6 hr6 rfl rfl ?_
  dsimp only [o19, wp, Op.cmp]
  intro fl hfl Y7 t7 hK7 hA7 hr7 hg7 hf7 hv7
  have hg7' : Y7.cpu.gpr = X.cpu.gpr := hg7.trans hg6'
  have hb7 := jbe_cmp (by decide) hfl
  rw [hg6', hc] at hb7
  refine c.s_jccV hK7 hA7 hin (lt_len (by decide)) hr7 (jb_283 _) (tgt := 196) (by decide) (lt_len (by decide))
    (fun h6 => ?_) (fun h6 => ?_)
  · rw [hf7, hb7] at h6
    have h55 := of_decide_eq_true h6
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, -⟩
    exact k Y8 t8 _ hK8 hA8 hr8 (hg8.trans hg7')
      (hF6.mono fun i hi hc' => by
        rw [cln_b (by omega) h55] at hc'; try dsimp only at hc' ⊢
        omega)
  rw [hf7, hb7] at h6
  have h55 := of_decide_eq_false h6
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hv8⟩
  have hg8' : Y8.cpu.gpr = X.cpu.gpr := hg8.trans hg7'
  have hz8 : xlo Y8 0 = 0#128 := by
    show (Y8.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv8, hv7]; exact hz6
  -- `movups [r8 + 40], xmm0`
  refine c.s_movups_stv hK8 hA8 hin (lt_len (by decide)) hr8 (mv_285 _) (fun i hi => ?_) ?_
  · rw [ea 40 hg8']; exact hWo 40 i (by omega)
  intro Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
  rw [ea 40 hg8', hz8] at hA9
  have hF9 := hF6.st hf (toBytesLE_length _ _) (by omega) z16 (o := 40)
  have hg9' : Y9.cpu.gpr = X.cpu.gpr := hg9.trans hg8'
  have hz9 : xlo Y9 0 = 0#128 := by
    show (Y9.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv9]; exact hz8
  -- `cmp rdx, 71`, `jbe 196`
  refine c.s_blkA_v hin ((blk_290 prof).at cal_at) Y9.cpu.vec hK9 hA9 hr9 rfl rfl ?_
  dsimp only [o20, wp, Op.cmp]
  intro fl hfl Y10 t10 hK10 hA10 hr10 hg10 hf10 hv10
  have hg10' : Y10.cpu.gpr = X.cpu.gpr := hg10.trans hg9'
  have hb10 := jbe_cmp (by decide) hfl
  rw [hg9', hc] at hb10
  refine c.s_jccV hK10 hA10 hin (lt_len (by decide)) hr10 (jb_294 _) (tgt := 196) (by decide)
    (lt_len (by decide)) (fun h6 => ?_) (fun h6 => ?_)
  · rw [hf10, hb10] at h6
    have h71 := of_decide_eq_true h6
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
    exact k Y11 t11 _ hK11 hA11 hr11 (hg11.trans hg10')
      (hF9.mono fun i hi hc' => by
        rw [cln_c (by omega) h71] at hc'; try dsimp only at hc' ⊢
        omega)
  rw [hf10, hb10] at h6
  have h71 := of_decide_eq_false h6
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, hv11⟩
  have hg11' : Y11.cpu.gpr = X.cpu.gpr := hg11.trans hg10'
  have hz11 : xlo Y11 0 = 0#128 := by
    show (Y11.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv11, hv10]; exact hz9
  -- `movups [r8 + 56], xmm0`, `jmp 196`
  refine c.s_movups_stv hK11 hA11 hin (lt_len (by decide)) hr11 (mv_296 _) (fun i hi => ?_) ?_
  · rw [ea 56 hg11']; exact hWo 56 i (by omega)
  intro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
  rw [ea 56 hg11', hz11] at hA12
  have hF12 := hF9.st hf (toBytesLE_length _ _) (by omega) z16 (o := 56)
  refine c.s_jmpV hK12 hA12 hin (lt_len (by decide)) hr12 (Dec.shift (j17_0 _) wj_301 (by decide)) (tgt := 196)
    (by decide) (lt_len (by decide)) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13, -⟩
  exact k Y13 t13 _ hK13 hA13 hr13 (hg13.trans (hg12.trans hg11'))
    (hF12.mono fun i hi hc' => by
      rw [cln_d (by omega) hhi] at hc'; try dsimp only at hc' ⊢
      omega)

end FV7z.Cal
