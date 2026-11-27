import FV7z.Fmi.Vc
import FV7z.Hsh.Holds
import FV7z.Mga.Holds
/-!
# `find_module_idx` (PLAN.md §M, M1)

glibc 2.31's `find_module_idx (str, idxp)` (`iconv/gconv_cache.c`) at `0x67ce30` in `7zzs`, one thread: the hash of
`str` (`__hash_string`, by its proof `Hsh.hsh_ok`), then the probe of the cache's hash table. An empty slot gives -1;
a name in bounds is compared with `str` by `strcmp` (through the PLT): a continuation hypothesis `Cmp`, with `eax` 0
just when `Same k`, as `Ffp.Cmp`. Equal: `*idxp` is the slot's module index and the result 0.

- `Of`, `FrO`: bytes outside the frame `[S - 96, S)`, and bytes that are those of the entry there.
- `cc`, `so`, `ho`, `hs`, `lim`: the cache and its header; `hv`, `i0`, `stp`, `idx`, `slot`, `nmk`, `nma`: the hash,
  the probe sequence, the `k`-th slot, its name's offset and the name. `Stop k`: the slot empty, or its name in bounds
  and `Same k`.
- `Env`: what the function is given. `Fm`, `Lp`: the bytes and the registers at the probe (147). `Kret`: what the
  caller asks at the return address.
- `lpE`: from the entry to the first probe. `t127`: to the next probe. `lpHead`: one probe. `lpAll`: the probes left.
- `fmi_ok`: the function, for a first `N` with `Stop N`: at the first slot `k` with `Stop k`, `kE` (empty, `rax` -1)
  or `kF` (found, `eax` 0, `*idxp` stored).
-/
/-! ## Fixes after triage kt788 (run 45838289885)
- `m2w`: the kernel ran out of memory on `omega` over `18446744073709551614#64`; now `m2`, `bv_omega` on the 32-bit
  form (as `Ugr.m1`).
- `t127`, `lpHead` (empty slot): the `rfl` in `rintro … ⟨rfl, rfl, …⟩` substituted `V`; the bytes are `_` there.
- `lpE`: `congrArg Gprs.rdi hg₁` elaborated against `(Y₁.cpu.gpr.set 4 _).rdi` assigned the wrong argument; the
  projections of `hg₁` are named first (`edi₁`, `e14₁`, `e12₁`).
- `lpHead`: no `swap`; `by_cases hc : ¬ …` takes the out-of-bounds case first, then `Decidable.of_not_not`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6 fr_e6 rdo rds)
open FV7z.Stm (Km stk)
open FV7z.Mga (Fr Oa Fr_st Fr_fr6)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Fmi

/-! ## The frame -/

/-- `n` bytes from `a`, not wrapping, outside the frame `[S - 96, S)`. -/
abbrev Of (S a : Addr) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ (a.toNat + n ≤ S.toNat - 96 ∨ S.toNat ≤ a.toNat)

/-- `V'` is `V` outside the frame `[S - 96, S)`. -/
def FrO (S : Addr) (V V' : Addr → Byte) : Prop :=
  ∀ y : Addr, (y.toNat < S.toNat - 96 ∨ S.toNat ≤ y.toNat) → V' y = V y

theorem FrO.refl (S : Addr) (V : Addr → Byte) : FrO S V V := fun _ _ => rfl

theorem FrO.st {S a : Addr} {V V' : Addr → Byte} {bs : List Byte} (h : FrO S V V')
    (h1 : S.toNat - 96 ≤ a.toNat) (h2 : a.toNat + bs.length ≤ S.toNat) : FrO S V (Vst V' a bs) := by
  intro y hy
  have := S.isLt
  exact (Vst_out V' a bs y (by omega) (by omega)).trans (h y hy)

theorem FrO.stb {S a : Addr} {V V' : Addr → Byte} {w n : Nat} {v : BitVec w} (h : FrO S V V')
    (h1 : S.toNat - 96 ≤ a.toNat) (h2 : a.toNat + n ≤ S.toNat) : FrO S V (Vst V' a (toBytesLE v n)) :=
  h.st h1 (by rw [toBytesLE_length]; exact h2)

theorem FrO.rd {S a : Addr} {n : Nat} {V V' : Addr → Byte} (h : FrO S V V') (ho : Of S a n) :
    List.map V' (byteAddrs a n) = List.map V (byteAddrs a n) := by
  obtain ⟨o1, o2⟩ := ho
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have e := toNat_add_of_fits hi o1
  exact h _ (by omega)

theorem FrO.w16 {S a : Addr} {V V' : Addr → Byte} (h : FrO S V V') (ho : Of S a 2) : rw16 V' a = rw16 V a :=
  congrArg (ofBytesLE 16) (h.rd ho)

theorem FrO.rb {S a : Addr} {V V' : Addr → Byte} (h : FrO S V V') (ho : Of S a 1) : Hsh.rb V' a = Hsh.rb V a :=
  congrArg (ofBytesLE 8) (h.rd ho)

/-- Stores keep bytes that agree where `P` holds. -/
theorem Vst_pt {P : Addr → Prop} : ∀ (bs : List Byte) (V W : Addr → Byte) (a : Addr),
    (∀ y, P y → V y = W y) → ∀ y, P y → Vst V a bs y = Vst W a bs y
  | [], _, _, _, h => h
  | b :: bs, V, W, a, h => Vst_pt bs (upd1 V a b) (upd1 W a b) (a.add 1) fun y hy => by
      show (if y = a then b else V y) = (if y = a then b else W y)
      by_cases e : y = a
      · rw [if_pos e, if_pos e]
      · rw [if_neg e, if_neg e]
        exact h y hy

theorem FrO.vst {S a : Addr} {V V' : Addr → Byte} {bs : List Byte} (h : FrO S V V') :
    FrO S (Vst V a bs) (Vst V' a bs) :=
  Vst_pt (P := fun y : Addr => y.toNat < S.toNat - 96 ∨ S.toNat ≤ y.toNat) bs V' V a h

theorem FrO.fr6 {S : Addr} (V : Addr → Byte) (a b c d e f : BitVec 64) (hS : 96 ≤ S.toNat) :
    FrO S V (fr6 V S a b c d e f) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 (S := S) (by omega)
  exact ((((((FrO.refl S V).stb (by omega) (by omega)).stb (by omega) (by omega)).stb (by omega) (by omega)).stb
    (by omega) (by omega)).stb (by omega) (by omega)).stb (by omega) (by omega)

/-- The hash reads only the string's bytes. -/
theorem hashN_fo {S a : Addr} {V V' : Addr → Byte} (h : FrO S V V') :
    ∀ n, (∀ i < n, Of S (a + BitVec.ofNat 64 i) 1) → Hsh.hashN V' a n = Hsh.hashN V a n
  | 0, _ => rfl
  | n + 1, ho => by
    simp only [Hsh.hashN]
    rw [hashN_fo h n (fun i hi => ho i (by omega)), h.rb (ho n (by omega))]

/-! ## Arithmetic -/

theorem tsub {a : Addr} {k : Nat} (hk : k ≤ a.toNat) : (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem tadd {a : Addr} {k : Nat} (hk : a.toNat + k < 2 ^ 64) : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The body's stack pointer and its slots. -/
theorem bt {S : Addr} (hS : 96 ≤ S.toNat) : (bR S).toNat = S.toNat - 88 ∧ (bR S - 8).toNat = S.toNat - 96 ∧
    (bR S + 4#64).toNat = S.toNat - 84 ∧ (bR S + 8#64).toNat = S.toNat - 80 ∧
    (bR S + 16#64).toNat = S.toNat - 72 ∧ (bR S + 24#64).toNat = S.toNat - 64 := by
  have hl := S.isLt
  obtain ⟨-, -, -, -, -, s6⟩ := fr_e6 (S := S) (by omega)
  have e : (bR S).toNat = S.toNat - 88 := by
    show (S - 8 - 8 - 8 - 8 - 8 - 8 - BitVec.ofNat 64 40).toNat = _
    rw [tsub (a := S - 8 - 8 - 8 - 8 - 8 - 8) (k := 40) (by omega)]
    omega
  have e1 := Prepare.toNat_sub8 (a := bR S) (by omega)
  have e2 := tadd (a := bR S) (k := 4) (by omega)
  have e3 := tadd (a := bR S) (k := 8) (by omega)
  have e4 := tadd (a := bR S) (k := 16) (by omega)
  have e5 := tadd (a := bR S) (k := 24) (by omega)
  exact ⟨e, by omega, by omega, by omega, by omega, by omega⟩

/-- The slots the epilogue pops, from the body's stack pointer. -/
theorem up_r {S : Addr} (hS : 96 ≤ S.toNat) :
    bR S + 40#64 = S - 8 - 8 - 8 - 8 - 8 - 8 ∧ bR S + 40#64 + 8 = S - 8 - 8 - 8 - 8 - 8 ∧
    bR S + 40#64 + 8 + 8 = S - 8 - 8 - 8 - 8 ∧ bR S + 40#64 + 8 + 8 + 8 = S - 8 - 8 - 8 ∧
    bR S + 40#64 + 8 + 8 + 8 + 8 = S - 8 - 8 ∧ bR S + 40#64 + 8 + 8 + 8 + 8 + 8 = S - 8 ∧
    bR S + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 (S := S) (by omega)
  have eb := (bt hS).1
  have u0 := tadd (a := bR S) (k := 40) (by omega)
  have u1 := Stm.ta8 (a := bR S + 40#64) (by omega)
  have u2 := Stm.ta8 (a := bR S + 40#64 + 8) (by omega)
  have u3 := Stm.ta8 (a := bR S + 40#64 + 8 + 8) (by omega)
  have u4 := Stm.ta8 (a := bR S + 40#64 + 8 + 8 + 8) (by omega)
  have u5 := Stm.ta8 (a := bR S + 40#64 + 8 + 8 + 8 + 8) (by omega)
  have u6 := Stm.ta8 (a := bR S + 40#64 + 8 + 8 + 8 + 8 + 8) (by omega)
  exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega),
    BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega),
    BitVec.eq_of_toNat_eq (by omega)⟩

/-- `y - 2` in 32 bits through 64. -/
theorem m2 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y + 18446744073709551614#64) = y - 2#32 := by
  bv_omega

/-- `ebx - 2` in 32 bits, `ebx` a word zero-extended (as `Ugr.m1`: `bv_omega` on the 32-bit form). -/
theorem m2w (x : BitVec 16) : (zw x + 18446744073709551614#64).setWidth 32 = x.setWidth 32 - 2#32 :=
  m2 (x.setWidth 32)

/-- `edx + 1` in 32 bits. -/
theorem p1w (x : BitVec 32) : (x.setWidth 64 + 1#64).setWidth 32 = x + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sw16_ne {x : BitVec 16} (h : x ≠ 0) : x.setWidth 32 ≠ 0 := by
  intro e
  apply h
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat e
  rw [BitVec.toNat_setWidth] at h1
  have h2 : (0 : BitVec 32).toNat = 0 := rfl
  have h3 : (0 : BitVec 16).toNat = 0 := rfl
  have := x.isLt
  omega

theorem sw16_ne2 {x : BitVec 16} (h : x ≠ 2) : x.setWidth 32 - 2#32 ≠ 0 := by
  intro e
  apply h
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat e
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth] at h1
  have h2 : (0 : BitVec 32).toNat = 0 := rfl
  have h3 : (2 : BitVec 16).toNat = 2 := rfl
  have h4 : (2#32).toNat = 2 := rfl
  have := x.isLt
  omega

/-- A read of bytes apart from a store. -/
theorem rdg {V : Addr → Byte} {a x : Addr} {w n m u : Nat} {v : BitVec w} (ha : a.toNat + n ≤ 2 ^ 64)
    (hx : x.toNat + m ≤ 2 ^ 64) (h : a.toNat + n ≤ x.toNat ∨ x.toNat + m ≤ a.toNat) :
    ofBytesLE u (List.map (Vst V a (toBytesLE v n)) (byteAddrs x m)) = ofBytesLE u (List.map V (byteAddrs x m)) :=
  congrArg (ofBytesLE u) (rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))

/-- A doubleword read where it was stored. -/
theorem rds4 {V : Addr → Byte} {a : Addr} {v : BitVec 32} (ha : a.toNat + 4 ≤ 2 ^ 64) :
    rdd(Vst V a (toBytesLE v 4), a) = v := by
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) ha]
  exact ofBytesLE_toBytesLE (n := 4) rfl _

/-! ## The cache and the probe -/

/-- The cache (`gconv_cache`) and its header's `string_offset`, `hash_offset`, `hash_size`. -/
abbrev cc (V : Addr → Byte) : Addr := rdq(V, 8014768#64)
abbrev so (V : Addr → Byte) : BitVec 16 := rw16 V (cc V + 4#64)
abbrev ho (V : Addr → Byte) : BitVec 16 := rw16 V (cc V + 6#64)
abbrev hs (V : Addr → Byte) : BitVec 16 := rw16 V (cc V + 8#64)
/-- The bound on the names' offsets: `cache_size - string_offset`. -/
abbrev lim (V : Addr → Byte) : BitVec 32 := rdd(V, 8014760#64) - (so V).setWidth 32
/-- The hash of the `n` bytes of `str` at `a`, 32 bits of it. -/
abbrev hv (V : Addr → Byte) (a : Addr) (n : Nat) : BitVec 32 := (Hsh.hashN V a n).setWidth 32
/-- The first index, `hval % hash_size`. -/
def i0 (V : Addr → Byte) (a : Addr) (n : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((hv V a n).toNat % ((hs V).setWidth 32).toNat)
/-- The step, `1 + hval % (hash_size - 2)`. -/
def stp (V : Addr → Byte) (a : Addr) (n : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((hv V a n).toNat % ((hs V).setWidth 32 - 2#32).toNat) + 1#32
/-- The `k`-th index. -/
def idx (V : Addr → Byte) (a : Addr) (n : Nat) : Nat → BitVec 32
  | 0 => i0 V a n
  | k + 1 => nxt (idx V a n k) (stp V a n) ((hs V).setWidth 32)
/-- The `k`-th slot, its name's offset, the name. -/
abbrev slot (V : Addr → Byte) (a : Addr) (n k : Nat) : Addr := cc V + (zw (ho V) + (idx V a n k).setWidth 64 * 4#64)
abbrev nmk (V : Addr → Byte) (a : Addr) (n k : Nat) : BitVec 16 := rw16 V (slot V a n k)
abbrev nma (V : Addr → Byte) (a : Addr) (n k : Nat) : Addr := zw (nmk V a n k) + zw (so V) + cc V

/-- The probe stops at the `k`-th slot: empty, or the name in bounds and `Same k`. -/
def Stop (V : Addr → Byte) (a : Addr) (n : Nat) (Same : Nat → Prop) (k : Nat) : Prop :=
  nmk V a n k = 0 ∨ (((nmk V a n k).setWidth 32).toNat < (lim V).toNat ∧ Same k)

/-- What the function is given: `V0` the bytes and `g0` the registers at the entry (`S = rsp`, `rdi = str` of `n`
bytes and a 0, `rsi = idxp`), the code, the frame `[S - 96, S)` writable, the return address `e₂ + j₂`, the cache's
words and the slots up to `N` readable and outside the frame, `hash_size` neither 0 nor 2, `*idxp` writable and
apart from the saved registers. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V0 : Addr → Byte) (g0 : Gprs)
    (n N : Nat) (e₂ : Addr) (j₂ : Nat) : Prop where
  hin : CodeIn L fmi_at fmi
  hinH : CodeIn L Hsh.hsh_at Hsh.hsh
  plt : ∃ code, CodeIn L 0x401110 code ∧ 0 < code.length
  rc : ∃ code, CodeIn L e₂ code ∧ j₂ < code.length
  s96 : 96 ≤ g0.rsp.toNat
  s8 : g0.rsp.toNat + 8 ≤ 2 ^ 64
  wf : ∀ a : Addr, g0.rsp.toNat - 96 ≤ a.toNat → a.toNat < g0.rsp.toNat → Foot Wl a
  fra : ∀ i < 8, Foot F.data (Addr.add g0.rsp i)
  hra : rdq(V0, g0.rsp) = e₂.add j₂
  fA : ∀ i < 8, Foot F.data (Addr.add 8014768#64 i)
  oA : Of g0.rsp 8014768#64 8
  fZ : ∀ i < 4, Foot F.data (Addr.add 8014760#64 i)
  oZ : Of g0.rsp 8014760#64 4
  f4 : ∀ i < 2, Foot F.data (Addr.add (cc V0 + 4#64) i)
  o4 : Of g0.rsp (cc V0 + 4#64) 2
  f6 : ∀ i < 2, Foot F.data (Addr.add (cc V0 + 6#64) i)
  o6 : Of g0.rsp (cc V0 + 6#64) 2
  f8 : ∀ i < 2, Foot F.data (Addr.add (cc V0 + 8#64) i)
  o8 : Of g0.rsp (cc V0 + 8#64) 2
  h0 : hs V0 ≠ 0
  h2 : hs V0 ≠ 2
  fs : ∀ i < n + 1, Foot F.data (g0.rdi + BitVec.ofNat 64 i)
  os : ∀ i < n + 1, Of g0.rsp (g0.rdi + BitVec.ofNat 64 i) 1
  snz : ∀ i < n, Hsh.rb V0 (g0.rdi + BitVec.ofNat 64 i) ≠ 0
  sz : Hsh.rb V0 (g0.rdi + BitVec.ofNat 64 n) = 0
  fN : ∀ k ≤ N, ∀ i < 2, Foot F.data (Addr.add (slot V0 g0.rdi n k) i)
  oN : ∀ k ≤ N, Of g0.rsp (slot V0 g0.rdi n k) 2
  fI : ∀ k ≤ N, ∀ i < 2, Foot F.data (Addr.add (slot V0 g0.rdi n k + 2#64) i)
  oI : ∀ k ≤ N, Of g0.rsp (slot V0 g0.rdi n k + 2#64) 2
  wI : ∀ i < 8, Foot Wl (Addr.add g0.rsi i)
  oS : Oa g0.rsp g0.rsi 8

/-- The bytes at the probe: the entry's outside the frame, the saved registers and the return address `ra`, the
bound, `string_offset`, `str` and `idxp` in the frame. -/
structure Fm (V0 : Addr → Byte) (g0 : Gprs) (ra : Addr) (V : Addr → Byte) : Prop where
  fo : FrO g0.rsp V0 V
  fr : Fr V g0.rsp g0 ra
  m4 : rdd(V, bR g0.rsp + 4#64) = lim V0
  m8 : rdq(V, bR g0.rsp + 8#64) = zw (so V0)
  m16 : rdq(V, bR g0.rsp + 16#64) = g0.rdi
  m24 : rdq(V, bR g0.rsp + 24#64) = g0.rsi

/-- The bytes and the registers at the `k`-th probe. -/
structure Lp (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (ra : Addr) (V : Addr → Byte) (g : Gprs) (k : Nat) :
    Prop where
  mem : Fm V0 g0 ra V
  sp : g.rsp = bR g0.rsp
  r12 : g.r12 = zw (ho V0)
  r13 : g.r13 = (idx V0 g0.rdi n k).setWidth 64
  r14 : g.r14 = cc V0
  rbx : g.rbx = zw (hs V0)
  rbp : g.rbp = (stp V0 g0.rdi n).setWidth 64

/-- A call's return address stored under the body's frame. -/
theorem Fm.call {V0 V : Addr → Byte} {g0 : Gprs} {ra : Addr} (h : Fm V0 g0 ra V) (hS : 96 ≤ g0.rsp.toNat)
    (hS8 : g0.rsp.toNat + 8 ≤ 2 ^ 64) {v : Addr} : Fm V0 g0 ra (Vst V (bR g0.rsp - 8) (toBytesLE v 8)) := by
  have hl := g0.rsp.isLt
  obtain ⟨e0, e8m, e4, e8, e16, e24⟩ := bt hS
  exact ⟨h.fo.stb (by omega) (by omega), Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩ h.fr,
    (rdg (by omega) (by omega) (by omega)).trans h.m4, (rdo (by omega) (by omega) (by omega)).trans h.m8,
    (rdo (by omega) (by omega) (by omega)).trans h.m16, (rdo (by omega) (by omega) (by omega)).trans h.m24⟩

theorem Lp.kp {V0 V : Addr → Byte} {g0 g g' : Gprs} {n k : Nat} {ra : Addr} (h : Lp V0 g0 n ra V g k)
    (hk : Kp g g') : Lp V0 g0 n ra V g' k :=
  ⟨h.mem, hk.1.trans h.sp, hk.2.1.trans h.r12, hk.2.2.1.trans h.r13, hk.2.2.2.1.trans h.r14,
    hk.2.2.2.2.1.trans h.rbx, hk.2.2.2.2.2.trans h.rbp⟩

/-! ## The pieces -/

/-- What the function asks of `strcmp` (its PLT entry `0x401110`) for the `k`-th slot: from its entry with
`rsp = bR S - 8`, the return address into the function there, the bytes those of the entry outside the frame, `rdi`
`str` and `rsi` the slot's name, the run goes on to the goal if it does from every state at the return address with
the same bytes, `rsp = bR S`, the registers a call keeps, and `eax` 0 just when `Same k`. -/
def Cmp (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (Same : Nat → Prop) : Prop :=
  ∀ (k : Nat) (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    FrO g0.rsp V0 V → Y.cpu.rip = 0x401110 → Y.cpu.gpr.rsp = bR g0.rsp - 8 →
    rdq(V, bR g0.rsp - 8) = fmi_at.add 123 → Y.cpu.gpr.rdi = g0.rdi → Y.cpu.gpr.rsi = nma V0 g0.rdi n k →
    (∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = fmi_at.add 123 →
      Z.cpu.gpr.rsp = bR g0.rsp → Km Y.cpu.gpr Z.cpu.gpr → (Z.cpu.gpr.rax.setWidth 32 = 0 ↔ Same k) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `W` outside the frame, `rsp = S + 8`, `rax` with `R`,
the registers a call keeps. -/
def Kret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (g0 : Gprs) (ra : Addr) (R : Addr → Prop) (W : Addr → Byte) : Prop :=
  ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → FrO g0.rsp W V' →
    Z.cpu.rip = ra → Z.cpu.gpr.rsp = g0.rsp + 8 → R Z.cpu.gpr.rax → Km g0 Z.cpu.gpr →
    GoG prof L o gev gP gE Z t'

/-- From the `k`-th probe the run goes on to the goal. -/
def LpAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (ra : Addr) (k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = fmi_at.add 147 → Lp V0 g0 n ra V Y.cpu.gpr k → GoG prof L o gev gP gE Y t

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 127 at the `k`-th probe: the next index, to the next probe. -/
theorem t127 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fmi_at fmi) {V0 : Addr → Byte} {g0 : Gprs} {n k : Nat}
    {ra : Addr} {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = fmi_at.add 127) (hL : Lp V0 g0 n ra V Y.cpu.gpr k)
    (kn : LpAt prof F Wl L s₀ o gev gP gE V0 g0 n ra (k + 1)) : GoG prof L o gev gP gE Y t := by
  refine (c_127 prof).run c hin _ hK hA hr vc_127 ?_
  rintro j' g fl V' ⟨rfl, rfl, hsp, h12, h14, hbx, hbp, h13⟩ Z t' hKZ hAZ hrZ hgZ -
  subst hgZ
  refine kn Z t' _ hKZ hAZ hrZ ⟨hL.mem, hsp.trans hL.sp, h12.trans hL.r12, ?_, h14.trans hL.r14,
    hbx.trans hL.rbx, hbp.trans hL.rbp⟩
  rw [h13, hL.r13, hL.rbp, hL.rbx]
  simp only [zw, sw_64_32]
  rfl

set_option maxHeartbeats 4000000 in
/-- From the entry: the pushes, the hash of `str`, `hash_size`, the first index and the step, to the first probe. -/
theorem lpE (c : Seg prof F Wl L s₀ o) {V0 : Addr → Byte} {X : State} {t n N : Nat} {e₂ : Addr} {j₂ : Nat}
    (E : Env F Wl L V0 X.cpu.gpr n N e₂ j₂) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V0)
    (hrip : X.cpu.rip = fmi_at) (k0 : LpAt prof F Wl L s₀ o gev gP gE V0 X.cpu.gpr n (e₂.add j₂) 0) :
    GoG prof L o gev gP gE X t := by
  have hS := E.s96
  have hS8 := E.s8
  have hl := X.cpu.gpr.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 (S := X.cpu.gpr.rsp) (by omega)
  obtain ⟨e0, e8m, e4, e8, e16, e24⟩ := bt hS
  have wfr : ∀ b : Addr, X.cpu.gpr.rsp.toNat - 96 ≤ b.toNat → ∀ m, b.toNat + m ≤ X.cpu.gpr.rsp.toNat →
      ∀ i < m, Foot Wl (Addr.add b i) := fun b h1 m h2 => stk E.wf h1 h2 (by omega)
  have fo1 : FrO X.cpu.gpr.rsp V0 (V1 V0 X.cpu.gpr) := FrO.fr6 _ _ _ _ _ _ _ hS
  have ecc : cC V0 X.cpu.gpr = cc V0 := congrArg (ofBytesLE 64) (fo1.rd E.oA)
  have fo2 : FrO X.cpu.gpr.rsp V0 (V2 V0 X.cpu.gpr) := fo1.stb (by omega) (by omega)
  have eso : so0 V0 X.cpu.gpr = so V0 := by
    show rw16 (V2 V0 X.cpu.gpr) (cC V0 X.cpu.gpr + 4#64) = _
    rw [ecc]
    exact fo2.w16 E.o4
  have eho : ho0 V0 X.cpu.gpr = ho V0 := by
    show rw16 (V2 V0 X.cpu.gpr) (cC V0 X.cpu.gpr + 6#64) = _
    rw [ecc]
    exact fo2.w16 E.o6
  have hr0 : X.cpu.rip = fmi_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the pushes, the header, `str` and `idxp` saved, to the call of `__hash_string`
  refine (c_0 prof).run c E.hin _ hK hA hr0 (vc_0 (wfr _ (by omega) 8 (by omega)) (wfr _ (by omega) 8 (by omega))
    (wfr _ (by omega) 8 (by omega)) (wfr _ (by omega) 8 (by omega)) (wfr _ (by omega) 8 (by omega))
    (wfr _ (by omega) 8 (by omega)) E.fA (wfr _ (by omega) 8 (by omega)) (wfr _ (by omega) 8 (by omega))
    (wfr _ (by omega) 8 (by omega)) (by rw [ecc]; exact E.f4) (by rw [ecc]; exact E.f6)) ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have esp₁ : Y₁.cpu.gpr.rsp = bR X.cpu.gpr.rsp := congrArg Gprs.rsp hg₁
  refine c.s_call hK₁ hA₁ E.hin (lt_len (by decide)) hr₁ (call_46 _) E.hinH (Hsh.lt_len (j := 0) (by decide))
    hs_46
    (by rw [esp₁]; exact wfr _ (by omega) 8 (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [esp₁] at hA₂
  generalize hV₂ : Vst (V4 V0 X.cpu.gpr) (bR X.cpu.gpr.rsp - 8) (toBytesLE (fmi_at.add (46 + 5)) 8) = V₂ at hA₂
  -- the bytes at the call of the hash
  have fo₂ : FrO X.cpu.gpr.rsp V0 V₂ := by
    rw [← hV₂]
    exact ((fo2.stb (by omega) (by omega)).stb (by omega) (by omega)).stb (by omega) (by omega)
  have hf1 := Fr_fr6 V0 X.cpu.gpr.rsp X.cpu.gpr (by omega) hS8
  rw [E.hra] at hf1
  have fr₂ : Fr V₂ X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) := by
    rw [← hV₂]
    exact Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩ (Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩
      (Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩
        (Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩ hf1)))
  have ra₂ : rdq(V₂, bR X.cpu.gpr.rsp - 8) = fmi_at.add 51 := by
    rw [← hV₂]
    exact rds (by omega)
  have m8₂ : rdq(V₂, bR X.cpu.gpr.rsp + 8#64) = zw (so V0) := by
    rw [← hV₂]
    exact (rdo (by omega) (by omega) (by omega)).trans ((rds (by omega)).trans (congrArg zw eso))
  have m16₂ : rdq(V₂, bR X.cpu.gpr.rsp + 16#64) = X.cpu.gpr.rdi := by
    rw [← hV₂]
    exact (rdo (by omega) (by omega) (by omega)).trans ((rdo (by omega) (by omega) (by omega)).trans
      ((rdo (by omega) (by omega) (by omega)).trans (rds (by omega))))
  have m24₂ : rdq(V₂, bR X.cpu.gpr.rsp + 24#64) = X.cpu.gpr.rsi := by
    rw [← hV₂]
    exact (rdo (by omega) (by omega) (by omega)).trans ((rdo (by omega) (by omega) (by omega)).trans
      (rds (by omega)))
  have esp₂ : Y₂.cpu.gpr.rsp = bR X.cpu.gpr.rsp - 8 := by
    rw [hg₂]
    show Y₁.cpu.gpr.rsp - 8 = _
    rw [esp₁]
  have edi₁ : Y₁.cpu.gpr.rdi = X.cpu.gpr.rdi := congrArg Gprs.rdi hg₁
  have e14₁ : Y₁.cpu.gpr.r14 = cC V0 X.cpu.gpr := congrArg Gprs.r14 hg₁
  have e12₁ : Y₁.cpu.gpr.r12 = zw (ho0 V0 X.cpu.gpr) := congrArg Gprs.r12 hg₁
  have edi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := (congrArg Gprs.rdi hg₂).trans edi₁
  have e14₂ : Y₂.cpu.gpr.r14 = cc V0 := ((congrArg Gprs.r14 hg₂).trans e14₁).trans ecc
  have e12₂ : Y₂.cpu.gpr.r12 = zw (ho V0) := ((congrArg Gprs.r12 hg₂).trans e12₁).trans (congrArg zw eho)
  -- the hash
  refine Hsh.hsh_ok c E.hinH hK₂ hA₂ hr₂ (n := n) (by rw [edi₂]; exact E.fs)
    (by rw [edi₂]; intro i hi; rw [fo₂.rb (E.os i (by omega))]; exact E.snz i hi)
    (by rw [edi₂, fo₂.rb (E.os n (by omega))]; exact E.sz)
    (by rw [esp₂]; exact fun i hi => c.hws _ (wfr _ (by omega) 8 (by omega) i hi))
    E.hin (lt_len (j := 51) (by decide)) (by rw [esp₂]; exact ra₂) ?_
  rintro Z t₃ hK₃ hA₃ hr₃ ⟨cx, dx, si, hg₃⟩
  have esp₃ : Z.cpu.gpr.rsp = bR X.cpu.gpr.rsp := by
    rw [hg₃]
    show Y₂.cpu.gpr.rsp + 8 = _
    rw [esp₂]
    exact BitVec.sub_add_cancel _ _
  have e14₃ : Z.cpu.gpr.r14 = cc V0 := (congrArg Gprs.r14 hg₃).trans e14₂
  have e12₃ : Z.cpu.gpr.r12 = zw (ho V0) := (congrArg Gprs.r12 hg₃).trans e12₂
  have eh₃ : Z.cpu.gpr.rax.setWidth 32 = hv V0 X.cpu.gpr.rdi n := by
    rw [hg₃]
    show (Hsh.hashN V₂ Y₂.cpu.gpr.rdi n).setWidth 32 = _
    rw [edi₂, hashN_fo fo₂ n (fun i hi => E.os i (by omega))]
  -- `hash_size`, `cache_size`, to the first `div`
  refine (c_51 prof).run c E.hin _ hK₃ hA₃ hr₃ (vc_51 (by rw [e14₃]; exact E.f8) E.fZ) ?_
  rintro j' g₄ fl V' ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have ehs : rw16 V₂ (cc V0 + 8#64) = hs V0 := fo₂.w16 E.o8
  have ebx₄ : Y₄.cpu.gpr.rbx = zw (hs V0) := by
    rw [hg₄]
    show zw (rw16 V₂ (Z.cpu.gpr.r14 + 8#64)) = _
    rw [e14₃, ehs]
  have esp₄ := (congrArg Gprs.rsp hg₄).trans esp₃
  have e12₄ := (congrArg Gprs.r12 hg₄).trans e12₃
  have e14₄ := (congrArg Gprs.r14 hg₄).trans e14₃
  have edi₄ : Y₄.cpu.gpr.rdi = (rdd(V₂, 8014760#64)).setWidth 64 := congrArg Gprs.rdi hg₄
  have ebp₄ : Y₄.cpu.gpr.rbp.setWidth 32 = hv V0 X.cpu.gpr.rdi n := by
    rw [hg₄]
    show ((Z.cpu.gpr.rax.setWidth 32).setWidth 64).setWidth 32 = _
    rw [sw_64_32]
    exact eh₃
  have r40 : rv Y₄ 32 0 = hv V0 X.cpu.gpr.rdi n := by
    show (Y₄.cpu.gpr.rax).setWidth 32 = _
    rw [hg₄]
    exact eh₃
  have r43 : rv Y₄ 32 3 = (hs V0).setWidth 32 := by
    show (Y₄.cpu.gpr.rbx).setWidth 32 = _
    rw [ebx₄, zw, sw_64_32]
  refine c.s_div32 hK₄ hA₄ E.hin (lt_len (by decide)) hr₄ (div_66 _) (congrArg Gprs.rdx hg₄)
    (by rw [r43]; exact sw16_ne E.h0) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  have edx₅ : Y₅.cpu.gpr.rdx = (i0 V0 X.cpu.gpr.rdi n).setWidth 64 := by
    rw [hg₅]
    show (BitVec.ofNat 32 ((rv Y₄ 32 0).toNat % (rv Y₄ 32 3).toNat)).setWidth 64 = _
    rw [r40, r43] <;> rfl
  have esp₅ := (congrArg Gprs.rsp hg₅).trans esp₄
  have e12₅ := (congrArg Gprs.r12 hg₅).trans e12₄
  have e14₅ := (congrArg Gprs.r14 hg₅).trans e14₄
  have ebx₅ := (congrArg Gprs.rbx hg₅).trans ebx₄
  have edi₅ := (congrArg Gprs.rdi hg₅).trans edi₄
  have ebp₅ := (congrArg (BitVec.setWidth 32) (congrArg Gprs.rbp hg₅)).trans ebp₄
  -- `hash_size - 2`, to the second `div`
  refine (c_68 prof).run c E.hin _ hK₅ hA₅ hr₅ vc_68 ?_
  rintro j' g₆ fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  have r60 : rv Y₆ 32 0 = hv V0 X.cpu.gpr.rdi n := by
    show (Y₆.cpu.gpr.rax).setWidth 32 = _
    rw [hg₆]
    show ((Y₅.cpu.gpr.rbp.setWidth 32).setWidth 64).setWidth 32 = _
    rw [sw_64_32]
    exact ebp₅
  have r66 : rv Y₆ 32 6 = (hs V0).setWidth 32 - 2#32 := by
    show (Y₆.cpu.gpr.rsi).setWidth 32 = _
    rw [hg₆]
    show (((Y₅.cpu.gpr.rbx + 18446744073709551614#64).setWidth 32).setWidth 64).setWidth 32 = _
    rw [sw_64_32, ebx₅, m2w]
  have esp₆ := (congrArg Gprs.rsp hg₆).trans esp₅
  have e12₆ := (congrArg Gprs.r12 hg₆).trans e12₅
  have e14₆ := (congrArg Gprs.r14 hg₆).trans e14₅
  have ebx₆ := (congrArg Gprs.rbx hg₆).trans ebx₅
  have edi₆ := (congrArg Gprs.rdi hg₆).trans edi₅
  have e13₆ : Y₆.cpu.gpr.r13 = (idx V0 X.cpu.gpr.rdi n 0).setWidth 64 := by
    rw [hg₆]
    show (Y₅.cpu.gpr.rdx.setWidth 32).setWidth 64 = _
    rw [edx₅, sw_64_32] <;> rfl
  refine c.s_div32 hK₆ hA₆ E.hin (lt_len (by decide)) hr₆ (div_78 _) (congrArg Gprs.rdx hg₆)
    (by rw [r66]; exact sw16_ne2 E.h2) ?_
  rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
  have edx₇ : Y₇.cpu.gpr.rdx = (BitVec.ofNat 32 ((hv V0 X.cpu.gpr.rdi n).toNat %
      ((hs V0).setWidth 32 - 2#32).toNat)).setWidth 64 := by
    rw [hg₇]
    show (BitVec.ofNat 32 ((rv Y₆ 32 0).toNat % (rv Y₆ 32 6).toNat)).setWidth 64 = _
    rw [r60, r66]
  have esp₇ := (congrArg Gprs.rsp hg₇).trans esp₆
  have e12₇ := (congrArg Gprs.r12 hg₇).trans e12₆
  have e13₇ := (congrArg Gprs.r13 hg₇).trans e13₆
  have e14₇ := (congrArg Gprs.r14 hg₇).trans e14₆
  have ebx₇ := (congrArg Gprs.rbx hg₇).trans ebx₆
  have edi₇ := (congrArg Gprs.rdi hg₇).trans edi₆
  -- the bound and the step, to the first probe
  refine (c_80 prof).run c E.hin _ hK₇ hA₇ hr₇ (vc_80 (by rw [e14₇]; exact E.f4)
    (by rw [esp₇]; exact wfr _ (by omega) 4 (by omega))) ?_
  rintro j' g₈ fl V' ⟨rfl, rfl, rfl⟩ Y₈ t₈ hK₈ hA₈ hr₈ hg₈ -
  rw [esp₇] at hA₈
  have rdZ : rdd(V₂, 8014760#64) = rdd(V0, 8014760#64) := congrArg (ofBytesLE 32) (fo₂.rd E.oZ)
  refine k0 Y₈ t₈ _ hK₈ hA₈ hr₈ ⟨⟨fo₂.stb (by omega) (by omega),
    Fr_st (by omega) hS8 ⟨by omega, Or.inl (by omega)⟩ fr₂, ?_,
    (rdo (by omega) (by omega) (by omega)).trans m8₂,
    (rdo (by omega) (by omega) (by omega)).trans m16₂, (rdo (by omega) (by omega) (by omega)).trans m24₂⟩,
    (congrArg Gprs.rsp hg₈).trans esp₇, (congrArg Gprs.r12 hg₈).trans e12₇,
    (congrArg Gprs.r13 hg₈).trans e13₇,
    (congrArg Gprs.r14 hg₈).trans e14₇, (congrArg Gprs.rbx hg₈).trans ebx₇, ?_⟩
  · refine (rds4 (by omega)).trans ?_
    rw [edi₇, sw_64_32, e14₇, fo₂.w16 E.o4, rdZ]
  · refine (congrArg Gprs.rbp hg₈).trans ?_
    show ((Y₇.cpu.gpr.rdx + 1#64).setWidth 32).setWidth 64 = _
    rw [edx₇, p1w] <;> rfl

set_option maxHeartbeats 4000000 in
/-- The `k`-th probe, none before it stopping: an empty slot (return -1), a name out of bounds (to the next probe),
or `strcmp`: equal (`*idxp` stored, return 0) or not (to the next probe). -/
theorem lpHead (c : Seg prof F Wl L s₀ o) {V0 : Addr → Byte} {g0 : Gprs} {n N : Nat} {e₂ : Addr} {j₂ : Nat}
    {Same : Nat → Prop} (E : Env F Wl L V0 g0 n N e₂ j₂) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V0 g0 n Same)
    (kE : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 g0.rdi n Same i) → nmk V0 g0.rdi n k = 0 →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) (fun r => r = 4294967295#64) V0)
    (kF : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 g0.rdi n Same i) → nmk V0 g0.rdi n k ≠ 0 →
      ((nmk V0 g0.rdi n k).setWidth 32).toNat < (lim V0).toNat → Same k →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) (fun r => r.setWidth 32 = 0)
        (Vst V0 g0.rsi (toBytesLE (zw (rw16 V0 (slot V0 g0.rdi n k + 2#64))) 8)))
    {k : Nat} (hk : k ≤ N) (hb : ∀ i < k, ¬ Stop V0 g0.rdi n Same i)
    (kn : (∀ i < k + 1, ¬ Stop V0 g0.rdi n Same i) →
      LpAt prof F Wl L s₀ o gev gP gE V0 g0 n (e₂.add j₂) (k + 1)) :
    LpAt prof F Wl L s₀ o gev gP gE V0 g0 n (e₂.add j₂) k := by
  intro Y t V hK hA hr hL
  have hS := E.s96
  have hl := g0.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 (S := g0.rsp) (by omega)
  obtain ⟨e0, e8m, e4, e8, e16, e24⟩ := bt hS
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := up_r hS
  obtain ⟨cR, hcR, hjR⟩ := E.rc
  have ffr : ∀ b : Addr, g0.rsp.toNat - 96 ≤ b.toNat → ∀ m, b.toNat + m ≤ g0.rsp.toNat →
      ∀ i < m, Foot F.data (Addr.add b i) := fun b h1 m h2 i hi => c.hws _ (stk E.wf h1 h2 (by omega) i hi)
  have hb1 : ¬ Stop V0 g0.rdi n Same k → ∀ i < k + 1, ¬ Stop V0 g0.rdi n Same i := fun hs i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact hb i h
    · rw [h]; exact hs
  have esp := hL.sp
  have esl : sl Y.cpu.gpr = slot V0 g0.rdi n k := by
    simp only [sl, sx, slot, hL.r12, hL.r13, hL.r14, sw_64_32]
  have eN : rw16 V (sl Y.cpu.gpr) = nmk V0 g0.rdi n k := by
    rw [esl]
    exact hL.mem.fo.w16 (E.oN k hk)
  have fN : ∀ i < 2, Foot F.data (Addr.add (sl Y.cpu.gpr) i) := by rw [esl]; exact E.fN k hk
  have fL : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 4#64) i) := by
    rw [esp]; exact ffr _ (by omega) 4 (by omega)
  have eL : rdd(V, Y.cpu.gpr.rsp + 4#64) = lim V0 := by rw [esp]; exact hL.mem.m4
  by_cases hz : nmk V0 g0.rdi n k = 0
  · -- an empty slot: return -1
    refine (c_147 prof).run c E.hin _ hK hA hr (vc_147e (beq_iff_eq.mpr (eN.trans hz)) fN
      (by rw [esp, q0]; exact ffr _ (by omega) 8 (by omega)) (by rw [esp, q1]; exact ffr _ (by omega) 8 (by omega))
      (by rw [esp, q2]; exact ffr _ (by omega) 8 (by omega)) (by rw [esp, q3]; exact ffr _ (by omega) 8 (by omega))
      (by rw [esp, q4]; exact ffr _ (by omega) 8 (by omega)) (by rw [esp, q5]; exact ffr _ (by omega) 8 (by omega)))
      ?_
    rintro j' g fl V' ⟨rfl, rfl, hsp, hax, hbx, hbp, h12, h13, h14, h15⟩ Z t' hKZ hAZ hrZ hgZ -
    subst hgZ
    rw [esp] at hsp hbx hbp h12 h13 h14 h15
    rw [q6] at hsp
    rw [q0] at hbx
    rw [q1] at hbp
    rw [q2] at h12
    rw [q3] at h13
    rw [q4] at h14
    rw [q5] at h15
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hL.mem.fr
    refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_186 _) (by rw [hsp]; exact E.fra) hcR hjR
      (by rw [hsp]; exact r7) ?_
    rintro W t'' hKW hAW ⟨hrW, hgW⟩
    exact kE k hk hb hz W t'' _ hKW hAW hL.mem.fo hrW
      (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp])
      (by show W.cpu.gpr.rax = _; rw [hgW]; exact hax)
      ⟨(congrArg Gprs.rbx hgW).trans (hbx.trans r1), (congrArg Gprs.rbp hgW).trans (hbp.trans r2),
        (congrArg Gprs.r12 hgW).trans (h12.trans r3), (congrArg Gprs.r13 hgW).trans (h13.trans r4),
        (congrArg Gprs.r14 hgW).trans (h14.trans r5), (congrArg Gprs.r15 hgW).trans (h15.trans r6)⟩
  have hz' : (rw16 V (sl Y.cpu.gpr) == 0) = false := by rw [eN]; exact beq_eq_false_iff_ne.mpr hz
  by_cases hc : ¬ ((nmk V0 g0.rdi n k).setWidth 32).toNat < (lim V0).toNat
  · -- the name out of bounds: to the next probe
    have hns : ¬ Stop V0 g0.rdi n Same k := fun h => Or.elim h hz fun h' => hc h'.1
    refine (c_147 prof).run c E.hin _ hK hA hr (vc_147s hz' (by rw [eN, eL]; exact hc) fN fL) ?_
    rintro j' g fl V' ⟨rfl, rfl, hkp⟩ Z t' hKZ hAZ hrZ hgZ -
    subst hgZ
    exact t127 c E.hin hKZ hAZ hrZ (hL.kp hkp) (kn (hb1 hns))
  replace hc := Decidable.of_not_not hc
  -- the call of `strcmp`
  have f8 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8#64) i) := by
    rw [esp]; exact ffr _ (by omega) 8 (by omega)
  have f16 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 16#64) i) := by
    rw [esp]; exact ffr _ (by omega) 8 (by omega)
  refine (c_147 prof).run c E.hin _ hK hA hr (vc_147c hz' (by rw [eN, eL]; exact hc) fN fL f8 f16) ?_
  rintro j' g fl V' ⟨rfl, rfl, hkp, hdi, hsi, h15⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  have hL₁ := hL.kp hkp
  have esp₁ := hL₁.sp
  obtain ⟨cC, hcC, hC0⟩ := E.plt
  refine c.s_call hK₁ hA₁ E.hin (lt_len (by decide)) hr₁ (call_118 _) hcC hC0 sc_118
    (by rw [esp₁]; exact stk E.wf (by omega) (by omega) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [esp₁] at hA₂
  generalize hV₂ : Vst V (bR g0.rsp - 8) (toBytesLE (fmi_at.add (118 + 5)) 8) = V₂ at hA₂
  have hM₂ : Fm V0 g0 (e₂.add j₂) V₂ := by
    rw [← hV₂]
    exact hL.mem.call hS E.s8
  have ra₂ : rdq(V₂, bR g0.rsp - 8) = fmi_at.add 123 := by
    rw [← hV₂]
    exact rds (by omega)
  have esp₂ : Y₂.cpu.gpr.rsp = bR g0.rsp - 8 := by
    rw [hg₂]
    show Y₁.cpu.gpr.rsp - 8 = _
    rw [esp₁]
  refine hcmp k Y₂ t₂ V₂ hK₂ hA₂ hM₂.fo hr₂ esp₂ ra₂
    (by rw [hg₂]; show Y₁.cpu.gpr.rdi = _; rw [hdi, esp]; exact hL.mem.m16)
    (by
      rw [hg₂]
      show Y₁.cpu.gpr.rsi = zw (nmk V0 g0.rdi n k) + zw (so V0) + cc V0
      rw [hsi, esp, eN, hL.mem.m8, hL.r14]) ?_
  intro Z t₃ hK₃ hA₃ hr₃ hsp₃ hkm hiff
  have e15 : Z.cpu.gpr.r15 = slot V0 g0.rdi n k :=
    hkm.2.2.2.2.2.trans ((congrArg Gprs.r15 hg₂).trans (h15.trans esl))
  by_cases hs : Same k
  · -- equal: `*idxp` stored, return 0
    have h0 : (Z.cpu.gpr.rax.setWidth 32 == 0) = true := beq_iff_eq.mpr (hiff.2 hs)
    have eVf : Vf V₂ Z.cpu.gpr = Vst V₂ g0.rsi (toBytesLE (zw (rw16 V0 (slot V0 g0.rdi n k + 2#64))) 8) := by
      show Vst V₂ (rdq(V₂, Z.cpu.gpr.rsp + 24#64)) (toBytesLE (zw (rw16 V₂ (Z.cpu.gpr.r15 + 2#64))) 8) = _
      rw [hsp₃, hM₂.m24, e15, hM₂.fo.w16 (E.oI k hk)]
    refine (c_123 prof).run c E.hin _ hK₃ hA₃ hr₃ (vc_123f h0 (by rw [e15]; exact E.fI k hk)
      (by rw [hsp₃]; exact ffr _ (by omega) 8 (by omega)) (by rw [hsp₃, hM₂.m24]; exact E.wI)
      (by rw [hsp₃, q0]; exact ffr _ (by omega) 8 (by omega))
      (by rw [hsp₃, q1]; exact ffr _ (by omega) 8 (by omega))
      (by rw [hsp₃, q2]; exact ffr _ (by omega) 8 (by omega))
      (by rw [hsp₃, q3]; exact ffr _ (by omega) 8 (by omega))
      (by rw [hsp₃, q4]; exact ffr _ (by omega) 8 (by omega))
      (by rw [hsp₃, q5]; exact ffr _ (by omega) 8 (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, hsp, hax, hbx, hbp, h12, h13, h14, h15'⟩ W₁ t₄ hK₄ hA₄ hr₄ hg₄ -
    subst hg₄
    rw [eVf] at hA₄ hbx hbp h12 h13 h14 h15'
    rw [hsp₃] at hsp hbx hbp h12 h13 h14 h15'
    rw [q6] at hsp
    rw [q0] at hbx
    rw [q1] at hbp
    rw [q2] at h12
    rw [q3] at h13
    rw [q4] at h14
    rw [q5] at h15'
    have hFr : Fr (Vst V₂ g0.rsi (toBytesLE (zw (rw16 V0 (slot V0 g0.rdi n k + 2#64))) 8)) g0.rsp g0
        (e₂.add j₂) := Fr_st (by omega) E.s8 E.oS hM₂.fr
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hFr
    refine c.s_ret hK₄ hA₄ E.hin (lt_len (by decide)) hr₄ (ret_219 _) (by rw [hsp]; exact E.fra) hcR hjR
      (by rw [hsp]; exact r7) ?_
    rintro W t'' hKW hAW ⟨hrW, hgW⟩
    exact kF k hk hb hz hc hs W t'' _ hKW hAW hM₂.fo.vst hrW
      (by rw [hgW]; show W₁.cpu.gpr.rsp + 8 = _; rw [hsp])
      (by
        show W.cpu.gpr.rax.setWidth 32 = 0
        rw [hgW]
        show W₁.cpu.gpr.rax.setWidth 32 = 0
        rw [hax]
        exact hiff.2 hs)
      ⟨(congrArg Gprs.rbx hgW).trans (hbx.trans r1), (congrArg Gprs.rbp hgW).trans (hbp.trans r2),
        (congrArg Gprs.r12 hgW).trans (h12.trans r3), (congrArg Gprs.r13 hgW).trans (h13.trans r4),
        (congrArg Gprs.r14 hgW).trans (h14.trans r5), (congrArg Gprs.r15 hgW).trans (h15'.trans r6)⟩
  · -- not equal: to the next probe
    have h0 : (Z.cpu.gpr.rax.setWidth 32 == 0) = false := beq_eq_false_iff_ne.mpr fun e => hs (hiff.1 e)
    have hns : ¬ Stop V0 g0.rdi n Same k := fun h => Or.elim h hz fun h' => hs h'.2
    have hL₃ : Lp V0 g0 n (e₂.add j₂) V₂ Z.cpu.gpr k :=
      ⟨hM₂, hsp₃, hkm.2.2.1.trans ((congrArg Gprs.r12 hg₂).trans hL₁.r12),
        hkm.2.2.2.1.trans ((congrArg Gprs.r13 hg₂).trans hL₁.r13),
        hkm.2.2.2.2.1.trans ((congrArg Gprs.r14 hg₂).trans hL₁.r14),
        hkm.1.trans ((congrArg Gprs.rbx hg₂).trans hL₁.rbx),
        hkm.2.1.trans ((congrArg Gprs.rbp hg₂).trans hL₁.rbp)⟩
    refine (c_123 prof).run c E.hin _ hK₃ hA₃ hr₃ (vc_123n h0) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ W₁ t₄ hK₄ hA₄ hr₄ hg₄ -
    exact t127 c E.hin hK₄ hA₄ hr₄ (by rw [hg₄]; exact hL₃) (kn (hb1 hns))

/-- The probes from the `k`-th, `m` left to `N`. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) {V0 : Addr → Byte} {g0 : Gprs} {n N : Nat} {e₂ : Addr} {j₂ : Nat}
    {Same : Nat → Prop} (E : Env F Wl L V0 g0 n N e₂ j₂) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V0 g0 n Same)
    (hN : Stop V0 g0.rdi n Same N)
    (kE : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 g0.rdi n Same i) → nmk V0 g0.rdi n k = 0 →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) (fun r => r = 4294967295#64) V0)
    (kF : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 g0.rdi n Same i) → nmk V0 g0.rdi n k ≠ 0 →
      ((nmk V0 g0.rdi n k).setWidth 32).toNat < (lim V0).toNat → Same k →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) (fun r => r.setWidth 32 = 0)
        (Vst V0 g0.rsi (toBytesLE (zw (rw16 V0 (slot V0 g0.rdi n k + 2#64))) 8))) :
    ∀ m k, k + m = N → (∀ i < k, ¬ Stop V0 g0.rdi n Same i) →
      LpAt prof F Wl L s₀ o gev gP gE V0 g0 n (e₂.add j₂) k := by
  intro m
  induction m with
  | zero =>
    intro k hk hb
    have hkN : k = N := by omega
    subst hkN
    exact lpHead c E hcmp kE kF (Nat.le_refl _) hb fun hb' => absurd hN (hb' _ (Nat.lt_succ_self _))
  | succ m ih =>
    intro k hk hb
    exact lpHead c E hcmp kE kF (by omega) hb fun hb' => ih (k + 1) (by omega) hb'

/-- `find_module_idx (str, idxp)` from its entry, for a first `N` with `Stop N`: at the first slot `k` that stops,
the return with `rax = -1` (`kE`, an empty slot) or `eax = 0` and `*idxp` the slot's module index (`kF`), the
registers a call keeps, the bytes those of the entry outside the frame (and `*idxp`). -/
theorem fmi_ok (c : Seg prof F Wl L s₀ o) {V0 : Addr → Byte} {X : State} {t n N : Nat} {e₂ : Addr} {j₂ : Nat}
    {Same : Nat → Prop} (E : Env F Wl L V0 X.cpu.gpr n N e₂ j₂) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V0) (hrip : X.cpu.rip = fmi_at)
    (hcmp : Cmp prof F Wl L s₀ o gev gP gE V0 X.cpu.gpr n Same) (hN : Stop V0 X.cpu.gpr.rdi n Same N)
    (kE : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 X.cpu.gpr.rdi n Same i) → nmk V0 X.cpu.gpr.rdi n k = 0 →
      Kret prof F Wl L s₀ o gev gP gE X.cpu.gpr (e₂.add j₂) (fun r => r = 4294967295#64) V0)
    (kF : ∀ k ≤ N, (∀ i < k, ¬ Stop V0 X.cpu.gpr.rdi n Same i) → nmk V0 X.cpu.gpr.rdi n k ≠ 0 →
      ((nmk V0 X.cpu.gpr.rdi n k).setWidth 32).toNat < (lim V0).toNat → Same k →
      Kret prof F Wl L s₀ o gev gP gE X.cpu.gpr (e₂.add j₂) (fun r => r.setWidth 32 = 0)
        (Vst V0 X.cpu.gpr.rsi (toBytesLE (zw (rw16 V0 (slot V0 X.cpu.gpr.rdi n k + 2#64))) 8))) :
    GoG prof L o gev gP gE X t :=
  lpE c E hK hA hrip (lpAll c E hcmp hN kE kF N 0 (Nat.zero_add N) fun _ h => absurd h (Nat.not_lt_zero _))

end

end FV7z.Fmi
