import FV7z.Cal.Vc
import FV7z.Ipa.Set
import FV7z.Lemmas.CmpImm
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

/-- The bytes `__libc_calloc` is to clear from the chunk `p` with size word `Zs`: its `csz` less 8 (`T` the old top
chunk, `V` the memory at the entry, the old top's size word at `T + 8`). -/
def clr (V : Addr → Byte) (T p Zs : Addr) : Nat :=
  (csz p T (rdq(V, T + 8#64) &&& 18446744073709551608#64) (Zs &&& 18446744073709551608#64)).toNat - 8

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
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
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
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hv6⟩
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
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
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
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
  rw [ea 56 hg11', hz11] at hA12
  have hF12 := hF9.st hf (toBytesLE_length _ _) (by omega) z16 (o := 56)
  refine c.s_jmpV (j := 301) hK12 hA12 hin (lt_len (by decide)) hr12 (Dec.shift (j17_0 _) wj_301 (by decide))
    (tgt := 196) (by decide) (lt_len (by decide)) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13, -⟩
  exact k Y13 t13 _ hK13 hA13 hr13 (hg13.trans (hg12.trans hg11'))
    (hF12.mono fun i hi hc' => by
      rw [cln_d (by omega) hhi] at hc'; try dsimp only at hc' ⊢
      omega)

set_option maxHeartbeats 8000000 in
/-- `__libc_calloc (n, m)` with `n * m ≤ 1024`, on the way of one thread, the hook null, the `tcache` made and
`perturb_byte` 0: `_int_malloc` (`ImAt`, at `0x630be0`) and `memset` (`Ipa.SetAt`, the PLT's at `0x401080`) by their
contracts, the run reaches the return address with `rax` the chunk `p` `_int_malloc` gave, the registers a call keeps
as at the entry, the first `cln (clr V T p Zs)` bytes at `p` 0 (`Zs` the chunk's size word; all the `clr` bytes but
for a size the inline stores round down), the other bytes as `_int_malloc` left them (`V₂`) apart from the stack
frame, and `Pm k` for what follows. -/
theorem cal_ok {fb T : Addr} {hi k : Nat} {pm ps : List Byte} {Ps : (Addr → Byte) → Prop}
    {Pm : Nat → (Addr → Byte) → Prop} {X : State} {t : Nat} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hgf : GotF F) (hin : CodeIn L cal_at cal)
    (him : CodeIn L 6491104#64 pm) (hm0 : 0 < pm.length) (himal : ImAt prof F Wl L o fb hi 6491104#64 Pm)
    (his : CodeIn L 4198528#64 ps) (hs0 : 0 < ps.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cal_at)
    (hdf : X.cpu.rflags.df = false) (hhi : hi + 264 ≤ X.cpu.gpr.rsp.toNat)
    (hs8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64) (hlo : 8013272 ≤ X.cpu.gpr.rsp.toNat)
    (hstk : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hm : X.cpu.gpr.rdi.toNat * X.cpu.gpr.rsi.toNat ≤ 1024)
    (hhk : rdq(V, 7940656#64) = 0#64) (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64)
    (hmt : rdd(V, fb + 24#64) = 0) (hpt : rdd(V, 8013220#64) = 0) (hT : rdq(V, 7940768#64) = T)
    (hO : 32 ≤ (rdq(V, T + 8#64) &&& 18446744073709551608#64).toNat)
    (d2 : (fb + 18446744073709551576#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 48)
    (d3 : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 48)
    (d5 : (T + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 48)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940656#64 i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i)) (f6 : ∀ i < 4, Foot F.data (Addr.add 8013220#64 i))
    (hPm : ∀ W : Addr → Byte,
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → W a = V a) →
        Pm (k + 1) W)
    (hPs : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Ps W)
    (kk : ∀ (Z : State) (t' : Nat) (W V₂ : Addr → Byte) (p Zs : Addr), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      7940480 ≤ p.toNat → rdq(V₂, p + 18446744073709551608#64) = Zs →
      X.cpu.gpr.rdi.toNat * X.cpu.gpr.rsi.toNat + 8 ≤ (Zs &&& 18446744073709551608#64).toNat →
      p.toNat + (Zs &&& 18446744073709551608#64).toNat ≤ X.cpu.gpr.rsp.toNat - 48 →
      (∀ i < cln (clr V T p Zs), W (p.add i) = 0) →
      (∀ a : Addr, ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + clr V T p Zs) →
        ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → W a = V₂ a) →
      (∀ a : Addr, a.toNat < 7940480 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat → V₂ a = V a) →
      Pm k W → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := X.cpu.gpr.rsp.isLt
  have hS48 : 48 ≤ X.cpu.gpr.rsp.toNat := by omega
  obtain ⟨e1, e2, e3, e4⟩ := fr_e (S := X.cpu.gpr.rsp) (by omega)
  have e6 := e6s hS48
  have hlt : X.cpu.gpr.rdi.toNat * X.cpu.gpr.rsi.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hm (by decide)
  have hmul : (X.cpu.gpr.rdi * X.cpu.gpr.rsi).toNat = X.cpu.gpr.rdi.toNat * X.cpu.gpr.rsi.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hlt]
  -- the prologue, to the call of `_int_malloc`
  refine (c_0' prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hm (by omega) hhk htc hmt hT (by omega) (by omega) (by omega) (by omega) (by omega)
      (slot hstk (by rw [e1]; omega) (by rw [e1]; omega)) (slot hstk (by rw [e2]; omega) (by rw [e2]; omega))
      (slot hstk (by rw [e3]; omega) (by rw [e3]; omega)) (slot hstk (by rw [e4]; omega) (by rw [e4]; omega))
      f1 f2 f3 f4 f5) ?_
  rintro j' g₁ fl V₁ ⟨rfl, rfl, hsp, hdi, hsi, hbp, h12, h13, hbx, h14, h15⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by rw [hg₁]; exact hsp
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_123 _) him hm0 tgt_123 (fun i hi => ?_) ?_
  · rw [hsp₁]; exact slot hstk (by rw [e6]; omega) (by rw [e6]; omega) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8 := by rw [hg₂]; rfl
  have hrsi : Y₂.cpu.gpr.rsi = X.cpu.gpr.rdi * X.cpu.gpr.rsi := by rw [hg₂, hg₁]; exact hsi
  have hVc : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      fr5 V X.cpu.gpr.rsp X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx (cal_at.add (123 + 5)) a = V a :=
    fun a ha => fr_out V _ _ _ _ _ _ hS48 a ha
  -- `_int_malloc (&main_arena, n * m)`
  refine himal c hK₂ hA₂ hr₂ (hPm _ hVc) (by rw [hg₂, hg₁]; exact hdi) (by rw [hrsi, hmul]; exact hm) hfs
    (by rw [hsp₂, e6]; omega) (by rw [hsp₂, e6]; omega) (fun a h1 h2 => hstk a h1 (by rw [hsp₂, e6] at h2; omega))
    hin (j := 128) (lt_len (by decide)) ?_ (fun i hi => ?_) ?_
  · rw [hsp₂, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e6]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₂]; exact c.hws _ (slot hstk (by rw [e6]; omega) (by rw [e6]; omega) i hi)
  intro Zm tm V₂ p Zs hKm hAm hrm hspm haxm hbxm hbpm h12m h13m h14m h15m hp7 hZs hb2 hb4 hcs hc32 hpC hfoot hV₂
    hdd hdp hPk
  rw [hsp₂, e6] at hpC hPk hV₂
  rw [hrsi, hmul] at hcs
  have h8p : 8 ≤ p.toNat := by omega
  have hp0 : p ≠ 0#64 := fun h => by rw [h] at hp7; exact absurd hp7 (by decide)
  have hfz : ∀ i < 8, Foot F.data (Addr.add (p + 18446744073709551608#64) i) := fun i hi => by
    have e := toNat_add_of_fits (a := p + 18446744073709551608#64) (n := 8) hi (by rw [tm8 h8p]; omega)
    exact (hfoot _ (by rw [e, tm8 h8p]; omega) (by rw [e, tm8 h8p]; omega)).2
  have hmt₂ : rdd(V₂, fb + 24#64) = 0 := by
    rw [hdd, rd_out (x := fb + 24#64) (n := 4) hVc (by omega) (.inl d3)]; exact hmt
  have hpt₂ : rdd(V₂, 8013220#64) = 0 := by
    rw [hdp, rd_out (x := 8013220#64) (n := 4) hVc (by simp only [BitVec.toNat_ofNat]; omega)
      (.inl (by simp only [BitVec.toNat_ofNat]; omega))]
    exact hpt
  -- to 148
  refine (c_128 prof fb).run c hfs hin _ hKm hAm hrm
    (vc_128 (by rw [haxm]; exact hp0) (by rw [haxm]; exact hZs) hb2 hb4 (by rw [hbpm, hg₂, hg₁]; exact hbp)
      (by rw [haxm]; exact hfz)) ?_
  rintro j' g₂ fl V' ⟨rfl, rfl, hVV⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V'
  have r8₃ : Y₃.cpu.gpr.r8 = p := by rw [hg₃]; exact haxm
  -- to 228
  refine (c_148 prof fb).run c hfs hin _ hK₃ hA₃ hr₃
    (vc_148 (by rw [r8₃]; exact hp0) hmt₂ (by rw [r8₃]; exact hZs) hb2 hpt₂ f3 (by rw [r8₃]; exact hfz) f6) ?_
  rintro j' g₄ fl V' ⟨rfl, hVV, hdx4, hsp4, hr84, -, -, -, -, h144, h154⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst V'
  have r13₃ : Y₃.cpu.gpr.r13 = T := by rw [hg₃]; show Zm.cpu.gpr.r13 = T; rw [h13m, hg₂, hg₁]; exact h13
  have rbx₃ : Y₃.cpu.gpr.rbx = rdq(V, T + 8#64) &&& 18446744073709551608#64 := by
    rw [hg₃]; show Zm.cpu.gpr.rbx = _; rw [hbxm, hg₂, hg₁]; exact hbx
  have hdx : Y₄.cpu.gpr.rdx = csz p T (rdq(V, T + 8#64) &&& 18446744073709551608#64)
      (Zs &&& 18446744073709551608#64) := by rw [hg₄, hdx4, r8₃, r13₃, rbx₃]
  have hc1 := csz_ge (p := p) (T := T) hO hc32
  have hc2 := csz_le p T (rdq(V, T + 8#64) &&& 18446744073709551608#64) (Zs &&& 18446744073709551608#64)
  have hcl : (Y₄.cpu.gpr.rdx - 8#64).toNat = clr V T p Zs := by rw [hdx, t8 (by omega)]; rfl
  have hcl1 : 24 ≤ clr V T p Zs := by unfold clr; omega
  have hcl2 : clr V T p Zs + 8 ≤ (Zs &&& 18446744073709551608#64).toNat := by unfold clr; omega
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by
    rw [hg₃]; show Zm.cpu.gpr.rsp = _; rw [hspm, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by rw [hg₄, hsp4, hsp₃]
  have r8₄ : Y₄.cpu.gpr.r8 = p := by rw [hg₄, hr84, r8₃]
  have r14₄ : Y₄.cpu.gpr.r14 = X.cpu.gpr.r14 := by
    rw [hg₄, h144, hg₃]; show Zm.cpu.gpr.r14 = _; rw [h14m, hg₂, hg₁]; exact h14
  have r15₄ : Y₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₄, h154, hg₃]; show Zm.cpu.gpr.r15 = _; rw [h15m, hg₂, hg₁]; exact h15
  have hdst : ∀ i < clr V T p Zs, Foot Wl (p.add i) := fun i hi => by
    have e := toNat_add_of_fits (a := p) (n := clr V T p Zs) hi (by omega)
    exact (hfoot _ (by rw [e]; omega) (by rw [e]; omega)).1
  -- the frame from `S - 40` up, through what `_int_malloc` and the clearing leave
  have hup : ∀ W : Addr → Byte, (∀ a : Addr, ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + clr V T p Zs) →
      ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 40) → W a = V₂ a) →
      ∀ a : Addr, X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat →
        W a = fr4 V X.cpu.gpr.rsp X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx a := fun W hout a ha => by
    rw [hout a (by omega) (by omega), hV₂ a (.inr (by omega))]
    exact Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (.inr (by rw [toBytesLE_length, e6]; omega))
  -- from 196 to the return address
  have k196 : ∀ (Y : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = cal_at.add 196 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 → Y.cpu.gpr.r8 = p →
      Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < cln (clr V T p Zs), W (p.add i) = 0) →
      (∀ a : Addr, ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + clr V T p Zs) →
        ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 40) → W a = V₂ a) →
      GoG prof L o gev gP gE Y t' := by
    intro Y t' W hKY hAY hrY hspY hr8Y h14Y h15Y hz hout
    have hu := hup W hout
    refine (c_196 prof fb).run c hfs hin _ hKY hAY hrY (vc_196 (fun i hi => ?_) (fun i hi => ?_)
      (fun i hi => ?_) (fun i hi => ?_)) ?_
    · rw [hspY, a5s]; exact c.hws _ (slot hstk (by rw [e4]; omega) (by rw [e4]; omega) i hi)
    · rw [hspY, a5s, a4s]; exact c.hws _ (slot hstk (by rw [e3]; omega) (by rw [e3]; omega) i hi)
    · rw [hspY, a5s, a4s, a3s]; exact c.hws _ (slot hstk (by rw [e2]; omega) (by rw [e2]; omega) i hi)
    · rw [hspY, a5s, a4s, a3s, a2s]; exact c.hws _ (slot hstk (by rw [e1]; omega) (by rw [e1]; omega) i hi)
    rintro j' g₉ fl V' ⟨rfl, hVV, hax9, hsp9, hbx9, hbp9, h129, h139, h149, h159⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
    subst V'
    have hsp₉ : Y₉.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₉, hsp9, hspY, a5s, a4s, a3s, a2s, a1s]
    have rdS : ∀ x : Addr, X.cpu.gpr.rsp.toNat - 40 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
        rdq(W, x) = rdq(fr4 V X.cpu.gpr.rsp X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx, x) :=
      fun x h1 h2 => congrArg (ofBytesLE 64) (rd_eq (P := fun a => X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat)
        (fun a ha => hu a ha) fun i hi => by rw [toNat_add_of_fits (n := 8) hi h2]; omega)
    obtain ⟨s1, s2, s3, s4⟩ := fr_slots V X.cpu.gpr.rsp X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx
      (by omega)
    refine c.s_ret hK₉ hA₉ hin (lt_len (by decide)) hr₉ (ret_209 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
    · rw [hsp₉]; exact hl i hi
    · rw [hsp₉]
      refine (congrArg (ofBytesLE 64) (rd_eq (P := fun a => X.cpu.gpr.rsp.toNat ≤ a.toNat)
        (fun a ha => (hu a (by omega)).trans (fr4_out _ _ _ _ _ _ (by omega) a (by omega)))
        fun i hi => ?_)).trans hra
      rw [toNat_add_of_fits (n := 8) hi (by omega)]
      omega
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    refine kk Z t' W V₂ p Zs hKZ hAZ hrZ (by rw [hgZ]; show Y₉.cpu.gpr.rsp + 8 = _; rw [hsp₉])
      (by rw [hgZ]; show Y₉.cpu.gpr.rax = p; rw [hg₉, hax9, hr8Y]) ?_ ?_ ?_ ?_
      (by rw [hgZ]; show Y₉.cpu.gpr.r14 = _; rw [hg₉, h149, h14Y])
      (by rw [hgZ]; show Y₉.cpu.gpr.r15 = _; rw [hg₉, h159, h15Y])
      hp7 hZs hcs hpC hz (fun a h1 _ => hout a h1 (by omega))
      (fun a ha => (hV₂ a (by omega)).trans (hVc a (by omega)))
      (hPk W fun a h1 h2 h3 => hout a (by omega) (by omega))
    · rw [hgZ]; show Y₉.cpu.gpr.rbx = _
      rw [hg₉, hbx9, hspY, a5s, rdS (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (by rw [e4]; omega) (by rw [e4]; omega)]
      exact s1
    · rw [hgZ]; show Y₉.cpu.gpr.rbp = _
      rw [hg₉, hbp9, hspY, a5s, a4s, rdS (X.cpu.gpr.rsp - 8 - 8 - 8) (by rw [e3]; omega) (by rw [e3]; omega)]
      exact s2
    · rw [hgZ]; show Y₉.cpu.gpr.r12 = _
      rw [hg₉, h129, hspY, a5s, a4s, a3s, rdS (X.cpu.gpr.rsp - 8 - 8) (by rw [e2]; omega) (by rw [e2]; omega)]
      exact s3
    · rw [hgZ]; show Y₉.cpu.gpr.r13 = _
      rw [hg₉, h139, hspY, a5s, a4s, a3s, a2s, rdS (X.cpu.gpr.rsp - 8) (by rw [e1]; omega) (by rw [e1]; omega)]
      exact s4
  by_cases hbig : 79 < clr V T p Zs
  · -- more than 79 bytes: `memset (p, 0, clr)`
    refine (c_228 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
      (vc_228m (by rw [hdx]; omega) (by rw [hdx]; unfold clr at hbig; omega)) ?_
    rintro j' g₅ fl V' ⟨rfl, hVV, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V'
    have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by rw [hg₅]; exact hsp₄
    refine c.s_call hK₅ hA₅ hin (lt_len (by decide)) hr₅ (call_717 _) his hs0 tgt_717 (fun i hi => ?_) ?_
    · rw [hsp₅]; exact slot hstk (by rw [e6]; omega) (by rw [e6]; omega) i hi
    rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
    rw [hsp₅] at hA₆ hg₆
    have hsp₆ : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8 := by rw [hg₆]; rfl
    have rdi₆ : Y₆.cpu.gpr.rdi = p := by rw [hg₆, hg₅]; exact r8₄
    have rsi₆ : Y₆.cpu.gpr.rsi = 0#64 := by rw [hg₆, hg₅]; rfl
    have rdx₆ : Y₆.cpu.gpr.rdx.toNat = clr V T p Zs := by rw [hg₆, hg₅]; exact hcl
    have hVm : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 40) →
        Vst V₂ (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE (cal_at.add (717 + 5)) 8) a = V₂ a :=
      fun a ha => Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega)
    refine hset c hgf hK₆ hA₆ hr₆ (hPs _ fun a ha => ?_) hin (j := 722) (lt_len (by decide)) ?_
      (fun i hi => ?_) (fun i hi => ?_) (by rw [rdi₆, rdx₆]; omega) (.inl (by rw [rdi₆, rdx₆, hsp₆, e6]; omega))
      (hK₆.df.trans (hK.df.symm.trans hdf)) (by rw [hsp₆, e6]; omega) ?_
    · rw [hVm a (by omega), hV₂ a (.inl ha)]; exact hVc a (by omega)
    · rw [hsp₆, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e6]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
      try rfl
    · rw [hsp₆]; exact c.hws _ (slot hstk (by rw [e6]; omega) (by rw [e6]; omega) i hi)
    · rw [rdx₆] at hi
      rw [rdi₆]
      exact hdst i hi
    rintro Z₇ t₇ V₃ hK₇ hA₇ hr₇ hsp₇ hax₇ - - - - h14₇ h15₇ hset₇ hout₇
    refine (c_722 prof fb).run c hfs hin _ hK₇ hA₇ hr₇ vc_722 ?_
    rintro j' g₈ fl V' ⟨rfl, hVV, rfl⟩ Y₈ t₈ hK₈ hA₈ hr₈ hg₈ -
    subst V'
    refine k196 Y₈ t₈ V₃ hK₈ hA₈ hr₈ ?_ ?_ ?_ ?_ (fun i hi => ?_) (fun a h1 h2 => ?_)
    · rw [hg₈]; show Z₇.cpu.gpr.rsp = _; rw [hsp₇, hsp₆]; exact BitVec.sub_add_cancel _ _
    · rw [hg₈]; show Z₇.cpu.gpr.rax = p; rw [hax₇, rdi₆]
    · rw [hg₈]; show Z₇.cpu.gpr.r14 = _; rw [h14₇, hg₆, hg₅]; exact r14₄
    · rw [hg₈]; show Z₇.cpu.gpr.r15 = _; rw [h15₇, hg₆, hg₅]; exact r15₄
    · rw [cln_e hbig] at hi
      have h := hset₇ i (by rw [rdx₆]; exact hi)
      rw [rdi₆, rsi₆] at h
      exact h.trans (by decide)
    · rw [hout₇ a (by rw [rdi₆, rdx₆]; exact h1)]
      exact hVm a h2
  · -- from 24 to 79 bytes: the inline stores
    refine (c_228 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
      (vc_228i (by rw [hdx]; omega) (by rw [hdx]; unfold clr at hcl1; omega)
        (by rw [hdx]; unfold clr at hbig; omega)) ?_
    rintro j' g₅ fl V' ⟨rfl, hVV, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V'
    refine inl c hin hK₅ hA₅ hr₅ (p := p) (by rw [hg₅]; exact r8₄) (by rw [hg₅]; exact hcl) hcl1 (by omega)
      (by omega) hdst ?_
    intro Y₆ t₆ W hK₆ hA₆ hr₆ hg₆ hF
    exact k196 Y₆ t₆ W hK₆ hA₆ hr₆ (by rw [hg₆, hg₅]; exact hsp₄) (by rw [hg₆, hg₅]; exact r8₄)
      (by rw [hg₆, hg₅]; exact r14₄) (by rw [hg₆, hg₅]; exact r15₄)
      (fun i hi => hF.1 i (Nat.lt_of_lt_of_le hi (cln_le hcl1)) hi) (fun a h1 _ => hF.2 a h1)

end FV7z.Cal
