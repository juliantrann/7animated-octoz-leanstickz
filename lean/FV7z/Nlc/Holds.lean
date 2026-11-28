import FV7z.Nlc.Vc
import FV7z.Stm.Holds
import FV7z.Mcn.Holds
import FV7z.Cxa.Holds
import FV7z.Lemmas.RepStosb
/-!
# `_nl_normalize_codeset` (PLAN.md §M, M1)

glibc 2.31's `_nl_normalize_codeset (codeset, name_len)` (`intl/l10nflist.c`) at `0x619f30` in `7zzs`, one thread:
count the alnum bytes of the name (and whether all of them are digits), `malloc` the new name (a continuation
hypothesis `Mal`, as `Fmi.Cmp`), then copy the name's alnum bytes, letters through `tolower`, behind `"iso"` for an
all-digit name, and a 0.

- `nb`, `ta`, `tp`, `tl`, `qa`, `qp`, `dd`: the `k`-th byte, its entries in `__ctype_b` (low and high byte) and in
  `__ctype_tolower`; not alnum, not alpha, a digit. `ch`, `out`, `cnt`, `dg`: the bytes a name byte gives, those of the
  first `k` bytes, the count of the alnums, whether all the alnums are digits.
- `Kr`, `Ag`, `Rd`: the bytes kept (the frame `[S - 24, S + 8)` and, outside `[S - 32, S)`, the region `Kk` that
  `malloc` keeps), memories that agree there, and the bytes read (readable, in `Kk`, outside the frame).
- `Env`: what the function is given. `Mal`: what it asks of `malloc`. `Kret`: what the caller asks at the return.
- `Cl`: the registers of the counting loop (48, 74). `Cp`, `Pb`: those of the copy loop (140, 131, 180), and the
  facts on the new block `p` (the name's bytes go from `p + d`, `d` 0 or 3) and the bytes `Vb` under it.
- `t48`, `t74`, `lcAll`: the counting loop. `tcall`: a `call` of `malloc`. `t140`, `t131`, `cpAll`, `cpEnd`: the copy
  loop. `t180`, `t224`: the way out. `aft91`, `aft196`, `aft245`: from each `call`.
- `nlc_ok`: the function. `malloc` gave 0: `rax = 0` (`kZ`). Else `rax = p` and the bytes `Wf`: `out n` and a 0 at
  `p` (`kS`), or after `"iso"` (`kI`, all the alnums digits, an empty name too).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (fr3 Km stk)
open FV7z.Tun (Vst_out)
open FV7z.Mcn (rds)
namespace FV7z.Nlc

/-! ## The name -/

/-- The `k`-th byte of the name at `s`. -/
abbrev nb (V0 : Addr → Byte) (s : Addr) (k : Nat) : BitVec 8 := rb V0 (s + BitVec.ofNat 64 k)
/-- The tables `__ctype_b` and `__ctype_tolower`. -/
abbrev T0 (V0 : Addr → Byte) : Addr := rdq(V0, 7935176#64)
abbrev U0 (V0 : Addr → Byte) : Addr := rdq(V0, 7935184#64)
/-- The `k`-th byte's class word (its low byte), the word's high byte, its `tolower`. -/
abbrev ta (V0 : Addr → Byte) (s : Addr) (k : Nat) : Addr := T0 V0 + zb (nb V0 s k) * 2#64
abbrev tp (V0 : Addr → Byte) (s : Addr) (k : Nat) : Addr := ta V0 s k + 1#64
abbrev tl (V0 : Addr → Byte) (s : Addr) (k : Nat) : Addr := U0 V0 + zb (nb V0 s k) * 4#64
/-- The `k`-th byte is not alnum (`_ISalnum`), is not alpha (`_ISalpha`), is a digit. -/
abbrev qa (V0 : Addr → Byte) (s : Addr) (k : Nat) : Bool := rb V0 (ta V0 s k) &&& 8#8 == 0
abbrev qp (V0 : Addr → Byte) (s : Addr) (k : Nat) : Bool := rb V0 (tp V0 s k) &&& 4#8 == 0
abbrev dd (V0 : Addr → Byte) (s : Addr) (k : Nat) : Prop := (d32 (nb V0 s k)).toNat < 10

/-- The bytes the `k`-th byte gives: its `tolower` if alpha, itself if a digit, else none. -/
def ch (V0 : Addr → Byte) (s : Addr) (k : Nat) : List Byte :=
  cond (qp V0 s k) (if dd V0 s k then [nb V0 s k] else []) [(rdd(V0, tl V0 s k)).setWidth 8]

/-- The bytes the first `k` bytes give. -/
def out (V0 : Addr → Byte) (s : Addr) : Nat → List Byte
  | 0 => []
  | k + 1 => out V0 s k ++ ch V0 s k

/-- The count of the alnums among the first `k` bytes. -/
def cnt (V0 : Addr → Byte) (s : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt V0 s k + cond (qa V0 s k) 0 1

/-- All the alnums among the first `k` bytes are digits. -/
def dg (V0 : Addr → Byte) (s : Addr) : Nat → Bool
  | 0 => true
  | k + 1 => dg V0 s k && (qa V0 s k || decide (dd V0 s k))

/-- `esi`: 1 or 0. -/
abbrev bi (b : Bool) : BitVec 64 := cond b 1#64 0#64

section
variable {V0 : Addr → Byte} {s : Addr} {k : Nat}

theorem out_a (hq : qp V0 s k = false) :
    out V0 s (k + 1) = out V0 s k ++ [(rdd(V0, tl V0 s k)).setWidth 8] := by
  show out V0 s k ++ ch V0 s k = _
  rw [ch, hq] <;> rfl

theorem out_d (hq : qp V0 s k = true) (hd : dd V0 s k) : out V0 s (k + 1) = out V0 s k ++ [nb V0 s k] := by
  show out V0 s k ++ ch V0 s k = _
  rw [ch, hq, if_pos hd] <;> rfl

theorem out_s (hq : qp V0 s k = true) (hd : ¬ dd V0 s k) : out V0 s (k + 1) = out V0 s k := by
  show out V0 s k ++ ch V0 s k = _
  rw [ch, hq, if_neg hd] <;> exact List.append_nil _

theorem out_al (hq : qp V0 s k = false) : (out V0 s (k + 1)).length = (out V0 s k).length + 1 := by
  rw [out_a hq, List.length_append, List.length_singleton]

theorem out_dl (hq : qp V0 s k = true) (hd : dd V0 s k) :
    (out V0 s (k + 1)).length = (out V0 s k).length + 1 := by
  rw [out_d hq hd, List.length_append, List.length_singleton]

theorem cnt_t (hq : qa V0 s k = true) : cnt V0 s (k + 1) = cnt V0 s k := by
  show cnt V0 s k + cond (qa V0 s k) 0 1 = _
  rw [hq] <;> rfl

theorem cnt_f (hq : qa V0 s k = false) : cnt V0 s (k + 1) = cnt V0 s k + 1 := by
  show cnt V0 s k + cond (qa V0 s k) 0 1 = _
  rw [hq] <;> rfl

theorem dg_t (hq : qa V0 s k = true) : dg V0 s (k + 1) = dg V0 s k := by
  show (dg V0 s k && (qa V0 s k || decide (dd V0 s k))) = _
  rw [hq, Bool.true_or, Bool.and_true]

theorem dg_fd (hq : qa V0 s k = false) (hd : dd V0 s k) : dg V0 s (k + 1) = dg V0 s k := by
  show (dg V0 s k && (qa V0 s k || decide (dd V0 s k))) = _
  rw [hq, Bool.false_or, decide_eq_true hd, Bool.and_true]

theorem dg_fx (hq : qa V0 s k = false) (hd : ¬ dd V0 s k) : dg V0 s (k + 1) = false := by
  show (dg V0 s k && (qa V0 s k || decide (dd V0 s k))) = _
  rw [hq, Bool.false_or, decide_eq_false hd, Bool.and_false]

end

theorem chl (V0 : Addr → Byte) (s : Addr) (k : Nat) : (ch V0 s k).length ≤ 1 := by
  rw [ch]
  cases hq : qp V0 s k
  · exact Nat.le_refl 1
  · by_cases hd : dd V0 s k
    · rw [if_pos hd] <;> exact Nat.le_refl 1
    · rw [if_neg hd] <;> exact Nat.zero_le 1

/-- At most one byte for each alnum, given that alpha and digits are alnum. -/
theorem outl {V0 : Addr → Byte} {s : Addr} {n : Nat}
    (han : ∀ k < n, qa V0 s k = true → qp V0 s k = true ∧ ¬ dd V0 s k) :
    ∀ k ≤ n, (out V0 s k).length ≤ cnt V0 s k
  | 0, _ => Nat.le_refl 0
  | k + 1, hk => by
    have ih := outl han k (by omega)
    have hc : (ch V0 s k).length ≤ cond (qa V0 s k) 0 1 := by
      cases hq : qa V0 s k
      · exact chl V0 s k
      · obtain ⟨hp, hd⟩ := han k (by omega) hq
        rw [ch, hp, if_neg hd] <;> exact Nat.le_refl 0
    show (out V0 s k ++ ch V0 s k).length ≤ cnt V0 s k + cond (qa V0 s k) 0 1
    rw [List.length_append]
    omega

theorem cntm (V0 : Addr → Byte) (s : Addr) (k : Nat) : ∀ m, k ≤ m → cnt V0 s k ≤ cnt V0 s m
  | 0, h => by
    have e : k = 0 := by omega
    subst e
    exact Nat.le_refl _
  | m + 1, h => by
    by_cases e : k = m + 1
    · subst e
      exact Nat.le_refl _
    · have ih := cntm V0 s k m (by omega)
      show cnt V0 s k ≤ cnt V0 s m + cond (qa V0 s m) 0 1
      omega

/-! ## Arithmetic -/

theorem on1 (m : Nat) : BitVec.ofNat 64 m + 1#64 = BitVec.ofNat 64 (m + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem on4 (m : Nat) : BitVec.ofNat 64 m + 4#64 = BitVec.ofNat 64 (m + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sko (s : Addr) (k : Nat) : s + BitVec.ofNat 64 k + 1#64 = s + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc, on1]

theorem az (s : Addr) : s + BitVec.ofNat 64 0 = s := BitVec.add_zero s

theorem ad1 (a : Addr) (m : Nat) : Addr.add a m + 1#64 = Addr.add a (m + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The store address of `[rax - 1]` after `rax + 1`. -/
theorem pm1 (x : Addr) : x + 1#64 + 18446744073709551615#64 = x := by
  rw [BitVec.add_assoc, show (1#64 + 18446744073709551615#64 : BitVec 64) = 0#64 from by decide,
    BitVec.add_zero]

/-- The end of the name: `r8 = s + n` against `rdx + 1`. -/
theorem r8e {s : Addr} {n k : Nat} (hn : n < 2 ^ 64) (hk : k + 1 ≤ n) :
    BitVec.ofNat 64 n + s = s + BitVec.ofNat 64 (k + 1) ↔ k + 1 = n := by
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
    have := s.isLt
    omega
  · intro h
    rw [h]
    exact BitVec.add_comm _ _

/-- The copy loop's bound: `rdx + 1 < r12`. -/
theorem bl {n k : Nat} (hn : n < 2 ^ 64) (hk : k + 1 ≤ n) :
    (BitVec.ofNat 64 k + 1#64).toNat < (BitVec.ofNat 64 n).toNat ↔ k + 1 < n := by
  rw [on1]
  simp only [BitVec.toNat_ofNat]
  constructor <;> intro h <;> omega

theorem bsw (b : Bool) : ((bi b).setWidth 32).setWidth 64 = bi b := by cases b <;> decide

theorem nz {n : Nat} (hn : n < 2 ^ 64) (h0 : n ≠ 0) : (BitVec.ofNat 64 n == 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h1 := congrArg BitVec.toNat h
  have h2 : (0 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat, h2] at h1
  omega

/-- The pops' slots, from `S - 24`. -/
theorem up3 (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 ∧ S - 8 - 8 - 8 + 8 + 8 = S - 8 ∧
    S - 8 - 8 - 8 + 8 + 8 + 8 = S := by
  refine ⟨BitVec.sub_add_cancel _ _, ?_, ?_⟩
  · rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]
  · rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel, BitVec.sub_add_cancel]

/-! ## The bytes kept and read -/

/-- The bytes kept: the frame `[S - 24, S + 8)`, and `Kk` outside `[S - 32, S)`. -/
def Kr (Kk : Addr → Prop) (S y : Addr) : Prop :=
  (S.toNat - 24 ≤ y.toNat ∧ y.toNat < S.toNat + 8) ∨ (Kk y ∧ (y.toNat < S.toNat - 32 ∨ S.toNat ≤ y.toNat))

/-- `W` is `V` where `P` holds. -/
def Ag (P : Addr → Prop) (V W : Addr → Byte) : Prop := ∀ y, P y → W y = V y

/-- `m` bytes from `x` read: readable, in `Kk`, outside the frame `[S - 32, S)`. -/
def Rd (F : Footprint) (Kk : Addr → Prop) (S x : Addr) (m : Nat) : Prop :=
  ∀ j < m, Foot F.data (Addr.add x j) ∧ Kk (Addr.add x j) ∧
    ((Addr.add x j).toNat < S.toNat - 32 ∨ S.toNat ≤ (Addr.add x j).toNat)

theorem Rd.fd {F : Footprint} {Kk : Addr → Prop} {S x : Addr} {m : Nat} (h : Rd F Kk S x m) :
    ∀ i < m, Foot F.data (Addr.add x i) := fun i hi => (h i hi).1

/-- The bytes after the three pushes. -/
abbrev Vf (V0 : Addr → Byte) (g0 : Gprs) : Addr → Byte := fr3 V0 g0.rsp g0.r12 g0.rbp g0.rbx

/-- A read where the bytes agree with the pushes': the entry's. -/
theorem rdR {F : Footprint} {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} {x : Addr} {m : Nat}
    (hS : 32 ≤ g0.rsp.toNat) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hx : Rd F Kk g0.rsp x m) :
    List.map V (byteAddrs x m) = List.map V0 (byteAddrs x m) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  obtain ⟨-, hk, ho⟩ := hx i hi
  rw [hag _ (Or.inr ⟨hk, ho⟩)]
  exact Stm.fr3_out V0 g0.rsp g0.r12 g0.rbp g0.rbx hS _ (by omega)

theorem Ag.st {P : Addr → Prop} {V W : Addr → Byte} {a : Addr} {bs : List Byte} (h : Ag P V W)
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (ho : ∀ y, P y → y.toNat < a.toNat ∨ a.toNat + bs.length ≤ y.toNat) :
    Ag P V (Vst W a bs) :=
  fun y hy => (Vst_out W a bs y ha (ho y hy)).trans (h y hy)

/-- Stores in `[p, p + sz)`, apart from `Kk`, are apart from the bytes kept. -/
theorem noK {Kk : Addr → Prop} {S p a : Addr} {sz m : Nat}
    (hkf : ∀ y : Addr, S.toNat - 24 ≤ y.toNat → y.toNat < S.toNat + 8 → Kk y)
    (hp : ∀ y : Addr, p.toNat ≤ y.toNat → y.toNat < p.toNat + sz → ¬ Kk y)
    (h1 : p.toNat ≤ a.toNat) (h2 : a.toNat + m ≤ p.toNat + sz) :
    ∀ y, Kr Kk S y → y.toNat < a.toNat ∨ a.toNat + m ≤ y.toNat := by
  intro y hy
  have hk : Kk y := by
    rcases hy with ⟨h3, h4⟩ | ⟨h3, -⟩
    · exact hkf y h3 h4
    · exact h3
  by_cases e : y.toNat < a.toNat ∨ a.toNat + m ≤ y.toNat
  · exact e
  · exact absurd hk (hp y (by omega) (by omega))

/-- After `malloc`: the bytes kept on `Kk` are the pushes' where they are kept. -/
theorem agM {Kk : Addr → Prop} {V0 V' : Addr → Byte} {g0 : Gprs} {ra : Addr} (hS : 32 ≤ g0.rsp.toNat)
    (hkf : ∀ y : Addr, g0.rsp.toNat - 24 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y)
    (h : ∀ y, Kk y → V' y = Vst (Vf V0 g0) (g0.rsp - 8 - 8 - 8 - 8) (toBytesLE ra 8) y) :
    Ag (Kr Kk g0.rsp) (Vf V0 g0) V' := by
  intro y hy
  have hl := g0.rsp.isLt
  obtain ⟨-, -, -, e4⟩ := Cal.fr_e hS
  have hk : Kk y := by
    rcases hy with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact hkf y h1 h2
    · exact h1
  rw [h y hk]
  refine Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) ?_
  rw [toBytesLE_length, e4]
  rcases hy with ⟨h1, -⟩ | ⟨-, h1⟩ <;> omega

theorem wsub {Wl : List Rgn} {p : Addr} {N e m : Nat} (hw : ∀ i < N, Foot Wl (Addr.add p i)) (h : e + m ≤ N) :
    ∀ i < m, Foot Wl (Addr.add (Addr.add p e) i) := fun i hi => by
  rw [addr_add_add]
  exact hw _ (by omega)

theorem vapp (Vb : Addr → Byte) (p : Addr) (d : Nat) (xs ys : List Byte) :
    Vst (Vst Vb (Addr.add p d) xs) (Addr.add p (d + xs.length)) ys = Vst Vb (Addr.add p d) (xs ++ ys) := by
  rw [Cxa.Vst_append, addr_add_add]

theorem ol0 (V0 : Addr → Byte) (s : Addr) : (out V0 s 0).length = 0 := rfl

theorem v0 (V0 : Addr → Byte) (s : Addr) (Vb : Addr → Byte) (a : Addr) : Vst Vb a (out V0 s 0) = Vb := rfl

/-- The bytes of the new name: `out n` from `p + d` over `Vb`, then a 0. -/
def Wf (V0 : Addr → Byte) (s : Addr) (Vb : Addr → Byte) (p : Addr) (d n : Nat) : Addr → Byte :=
  Vst (Vst Vb (Addr.add p d) (out V0 s n)) (Addr.add p (d + (out V0 s n).length)) (toBytesLE 0#8 1)

theorem wf0 (V0 : Addr → Byte) (s : Addr) (Vb : Addr → Byte) (p : Addr) (d : Nat) :
    Wf V0 s Vb p d 0 = Vst Vb (Addr.add p d) (toBytesLE 0#8 1) := rfl

/-! ## What the function is given and asks -/

/-- What the function is given: `V0` the bytes and `g0` the registers at the entry (`S = rsp`, `rdi = s`,
`rsi = n`), the code (and `malloc`'s), the frame `[S - 32, S)` writable, the return address `e₂ + j₂`, the frame and
its return address in `Kk`, the name's bytes and their entries in the tables, and the tables, read; alpha and digits
alnum. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (Kk : Addr → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (e₂ : Addr) (j₂ : Nat) : Prop where
  hin : CodeIn L nlc_at nlc
  mc : ∃ code, CodeIn L 0x633160 code ∧ 0 < code.length
  rc : ∃ code, CodeIn L e₂ code ∧ j₂ < code.length
  s32 : 32 ≤ g0.rsp.toNat
  s8 : g0.rsp.toNat + 8 ≤ 2 ^ 64
  wf : ∀ a : Addr, g0.rsp.toNat - 32 ≤ a.toNat → a.toNat < g0.rsp.toNat → Foot Wl a
  fra : ∀ i < 8, Foot F.data (Addr.add g0.rsp i)
  hra : rdq(V0, g0.rsp) = e₂.add j₂
  kf : ∀ y : Addr, g0.rsp.toNat - 24 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y
  rn : g0.rsi = BitVec.ofNat 64 n
  nl : g0.rdi.toNat + n < 2 ^ 64
  d1 : 7935184 ≤ g0.rsp.toNat - 24
  fT : ∀ i < 8, Foot F.data (Addr.add 7935176#64 i)
  rU : Rd F Kk g0.rsp 7935184#64 8
  rs : ∀ k < n, Rd F Kk g0.rsp (g0.rdi + BitVec.ofNat 64 k) 1
  ra : ∀ k < n, Rd F Kk g0.rsp (ta V0 g0.rdi k) 1
  rp : ∀ k < n, Rd F Kk g0.rsp (tp V0 g0.rdi k) 1
  rl : ∀ k < n, Rd F Kk g0.rsp (tl V0 g0.rdi k) 4
  an : ∀ k < n, qa V0 g0.rdi k = true → qp V0 g0.rdi k = true ∧ ¬ dd V0 g0.rdi k

/-- What `malloc (sz)` gives: 0, or `p` with `[p, p + sz)` not wrapping, writable and apart from `Kk`. -/
def Res (Wl : List Rgn) (Kk : Addr → Prop) (sz : Nat) (p : Addr) : Prop :=
  p = 0 ∨ (p.toNat + sz ≤ 2 ^ 64 ∧ (∀ i < sz, Foot Wl (Addr.add p i)) ∧
    ∀ y : Addr, p.toNat ≤ y.toNat → y.toNat < p.toNat + sz → ¬ Kk y)

/-- What the function asks of `malloc` (`0x633160`): from its entry with `rsp = S - 32`, the return address `ra` there
and `rdi = sz`, the run goes on to the goal if it does from every state at `ra` with `rsp = S - 24`, the registers a
call keeps, the bytes kept on `Kk`, and `rax` with `Res`. -/
def Mal (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (Kk : Addr → Prop) : Prop :=
  ∀ (sz : Nat) (Y : State) (t : Nat) (V : Addr → Byte) (ra : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = 0x633160 → Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 → rdq(V, S - 8 - 8 - 8 - 8) = ra →
    Y.cpu.gpr.rdi = BitVec.ofNat 64 sz →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ y, Kk y → V' y = V y) → Z.cpu.rip = ra → Z.cpu.gpr.rsp = S - 8 - 8 - 8 → Km Y.cpu.gpr Z.cpu.gpr →
      Res Wl Kk sz Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `W`, `rsp = S + 8`, `rax = r`, the registers a call
keeps. -/
def Kret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (g0 : Gprs) (ra r : Addr) (W : Addr → Byte) : Prop :=
  ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = ra →
    Z.cpu.gpr.rsp = g0.rsp + 8 → Z.cpu.gpr.rax = r → Km g0 Z.cpu.gpr → GoG prof L o gev gP gE Z t'

/-! ## The loops' registers -/

/-- The registers both loops keep: the frame, `__ctype_b`, the name, its length, those a call keeps. -/
abbrev Rg (V0 : Addr → Byte) (g0 g : Gprs) (n : Nat) : Prop :=
  g.rsp = g0.rsp - 8 - 8 - 8 ∧ g.rbx = T0 V0 ∧ g.rbp = g0.rdi ∧ g.r12 = BitVec.ofNat 64 n ∧ g.r13 = g0.r13 ∧
    g.r14 = g0.r14 ∧ g.r15 = g0.r15

section
variable {V0 : Addr → Byte} {g0 g : Gprs} {n : Nat}
theorem Rg.sp (h : Rg V0 g0 g n) : g.rsp = g0.rsp - 8 - 8 - 8 := h.1
theorem Rg.bx (h : Rg V0 g0 g n) : g.rbx = T0 V0 := h.2.1
theorem Rg.bp (h : Rg V0 g0 g n) : g.rbp = g0.rdi := h.2.2.1
theorem Rg.r12 (h : Rg V0 g0 g n) : g.r12 = BitVec.ofNat 64 n := h.2.2.2.1
theorem Rg.r13 (h : Rg V0 g0 g n) : g.r13 = g0.r13 := h.2.2.2.2.1
theorem Rg.r14 (h : Rg V0 g0 g n) : g.r14 = g0.r14 := h.2.2.2.2.2.1
theorem Rg.r15 (h : Rg V0 g0 g n) : g.r15 = g0.r15 := h.2.2.2.2.2.2
end

/-- The counting loop at the `k`-th byte, the counts those of the first `i`. -/
structure Cl (V0 : Addr → Byte) (g0 g : Gprs) (n k i : Nat) : Prop where
  rg : Rg V0 g0 g n
  r8 : g.r8 = BitVec.ofNat 64 n + g0.rdi
  r9 : g.r9 = 0#64
  dx : g.rdx = g0.rdi + BitVec.ofNat 64 k
  di : g.rdi = BitVec.ofNat 64 (cnt V0 g0.rdi i)
  si : g.rsi = bi (dg V0 g0.rdi i)

/-- The copy loop at the `j`-th byte, the bytes of the first `k` stored from `p + d`. -/
structure Cp (V0 : Addr → Byte) (g0 g : Gprs) (n : Nat) (p : Addr) (d k j : Nat) : Prop where
  rg : Rg V0 g0 g n
  r8 : g.r8 = U0 V0
  r9 : g.r9 = p
  dx : g.rdx = BitVec.ofNat 64 j
  ax : g.rax = Addr.add p (d + (out V0 g0.rdi k).length)

/-- The new block: `[p, p + d + cnt n + 1)` not wrapping, writable, apart from `Kk`; the bytes `Vb` kept. -/
structure Pb (Wl : List Rgn) (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (p : Addr) (d : Nat)
    (Vb : Addr → Byte) : Prop where
  fit : p.toNat + (d + cnt V0 g0.rdi n + 1) ≤ 2 ^ 64
  w : ∀ i < d + cnt V0 g0.rdi n + 1, Foot Wl (Addr.add p i)
  nk : ∀ y : Addr, p.toNat ≤ y.toNat → y.toNat < p.toNat + (d + cnt V0 g0.rdi n + 1) → ¬ Kk y
  ag : Ag (Kr Kk g0.rsp) (Vf V0 g0) Vb

/-- From 48 at the `k`-th byte the run goes on to the goal. -/
def LcAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vf V0 g0) → Y.cpu.rip = nlc_at.add 48 →
    Cl V0 g0 Y.cpu.gpr n k k → GoG prof L o gev gP gE Y t

/-- From the `call` at `j` with `rdi = sz` the run goes on to the goal. -/
def Aft (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n j sz : Nat) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vf V0 g0) → Y.cpu.rip = nlc_at.add j →
    Rg V0 g0 Y.cpu.gpr n → Y.cpu.gpr.rdi = BitVec.ofNat 64 sz → GoG prof L o gev gP gE Y t

/-- From 140 at the `k`-th byte the run goes on to the goal. -/
def LpAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (p : Addr) (d : Nat) (Vb : Addr → Byte) (k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst Vb (Addr.add p d) (out V0 g0.rdi k)) →
    Y.cpu.rip = nlc_at.add 140 → Cp V0 g0 Y.cpu.gpr n p d k k → GoG prof L o gev gP gE Y t

/-- From 180 after `k` bytes the run goes on to the goal. -/
def A180 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) (p : Addr) (d : Nat) (Vb : Addr → Byte) (k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst Vb (Addr.add p d) (out V0 g0.rdi k)) →
    Y.cpu.rip = nlc_at.add 180 → Cp V0 g0 Y.cpu.gpr n p d k k → GoG prof L o gev gP gE Y t

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {n : Nat} {e₂ : Addr} {j₂ : Nat}

/-- The bytes stored so far from `p + d` keep the bytes kept. -/
theorem agk (E : Env F Wl L Kk V0 g0 n e₂ j₂) {p : Addr} {d : Nat} {Vb : Addr → Byte}
    (P : Pb Wl Kk V0 g0 n p d Vb) {k : Nat} (hk : k ≤ n) :
    Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vst Vb (Addr.add p d) (out V0 g0.rdi k)) := by
  have ho := outl E.an k hk
  have hc := cntm V0 g0.rdi k n hk
  have hf := P.fit
  have e := toNat_add_of_fits (a := p) (i := d) (n := d + cnt V0 g0.rdi n + 1) (by omega) hf
  exact P.ag.st (by rw [e]; omega) (noK E.kf P.nk (by rw [e]; omega) (by rw [e]; omega))

/-! ## The way out -/

set_option maxHeartbeats 4000000 in
/-- From 180: the 0 stored at `rax`, `rax = r9`, the pops and the `ret`. -/
theorem t180 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {Y : State} {t : Nat}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hr : Y.cpu.rip = nlc_at.add 180)
    (hsp : Y.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8) (h13 : Y.cpu.gpr.r13 = g0.r13) (h14 : Y.cpu.gpr.r14 = g0.r14)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (w : ∀ i < 1, Foot Wl (Addr.add Y.cpu.gpr.rax i))
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vst V Y.cpu.gpr.rax (toBytesLE 0#8 1)))
    (k : Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) Y.cpu.gpr.r9 (Vst V Y.cpu.gpr.rax (toBytesLE 0#8 1))) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s32
  have hl := g0.rsp.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  obtain ⟨u1, u2, u3⟩ := up3 g0.rsp
  have ffr : ∀ b : Addr, g0.rsp.toNat - 32 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot F.data (Addr.add b i) := fun b h1 h2 i hi => c.hws _ (stk E.wf h1 h2 (by omega) i hi)
  obtain ⟨r3, r2, r1, r0⟩ := Stm.frame (V := V0) (a := g0.r12) (b := g0.rbp) (c := g0.rbx) hS E.s8 E.hra
    (fun x h1 h2 => hag x (Or.inl ⟨h1, h2⟩))
  obtain ⟨cR, hcR, hjR⟩ := E.rc
  refine (c_180 prof).run c E.hin _ hK hA hr (vc_180 w (by rw [hsp]; exact ffr _ (by omega) (by omega))
    (by rw [hsp, u1]; exact ffr _ (by omega) (by omega))
    (by rw [hsp, u2]; exact ffr _ (by omega) (by omega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, hsp', hax, hbx, hbp, h12, h13', h14', h15'⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hgZ
  rw [hsp, u3] at hsp'
  rw [hsp] at hbx
  rw [hsp, u1] at hbp
  rw [hsp, u2] at h12
  refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_190 _) (by rw [hsp']; exact E.fra) hcR hjR
    (by rw [hsp']; exact r0) ?_
  rintro W t₂ hKW hAW ⟨hrW, hgW⟩
  exact k W t₂ hKW hAW hrW (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp'])
    (by rw [hgW]; show Z.cpu.gpr.rax = _; exact hax)
    ⟨(congrArg Gprs.rbx hgW).trans (hbx.trans r3), (congrArg Gprs.rbp hgW).trans (hbp.trans r2),
      (congrArg Gprs.r12 hgW).trans (h12.trans r1), (congrArg Gprs.r13 hgW).trans (h13'.trans h13),
      (congrArg Gprs.r14 hgW).trans (h14'.trans h14), (congrArg Gprs.r15 hgW).trans (h15'.trans h15)⟩

set_option maxHeartbeats 4000000 in
/-- From 224 (`malloc` gave 0): `rax = 0`, the pops and the `ret`. -/
theorem t224 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {Y : State} {t : Nat}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hr : Y.cpu.rip = nlc_at.add 224)
    (hsp : Y.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8) (h13 : Y.cpu.gpr.r13 = g0.r13) (h14 : Y.cpu.gpr.r14 = g0.r14)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) 0#64 V) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s32
  have hl := g0.rsp.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  obtain ⟨u1, u2, u3⟩ := up3 g0.rsp
  have ffr : ∀ b : Addr, g0.rsp.toNat - 32 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot F.data (Addr.add b i) := fun b h1 h2 i hi => c.hws _ (stk E.wf h1 h2 (by omega) i hi)
  obtain ⟨r3, r2, r1, r0⟩ := Stm.frame (V := V0) (a := g0.r12) (b := g0.rbp) (c := g0.rbx) hS E.s8 E.hra
    (fun x h1 h2 => hag x (Or.inl ⟨h1, h2⟩))
  obtain ⟨cR, hcR, hjR⟩ := E.rc
  refine (c_224 prof).run c E.hin _ hK hA hr (vc_224 (by rw [hsp]; exact ffr _ (by omega) (by omega))
    (by rw [hsp, u1]; exact ffr _ (by omega) (by omega))
    (by rw [hsp, u2]; exact ffr _ (by omega) (by omega))) ?_
  rintro j' g fl V ⟨rfl, rfl, hsp', hax, hbx, hbp, h12, h13', h14', h15'⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hgZ
  rw [hsp, u3] at hsp'
  rw [hsp] at hbx
  rw [hsp, u1] at hbp
  rw [hsp, u2] at h12
  refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_234 _) (by rw [hsp']; exact E.fra) hcR hjR
    (by rw [hsp']; exact r0) ?_
  rintro W t₂ hKW hAW ⟨hrW, hgW⟩
  exact k W t₂ hKW hAW hrW (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp'])
    (by rw [hgW]; show Z.cpu.gpr.rax = _; exact hax)
    ⟨(congrArg Gprs.rbx hgW).trans (hbx.trans r3), (congrArg Gprs.rbp hgW).trans (hbp.trans r2),
      (congrArg Gprs.r12 hgW).trans (h12.trans r1), (congrArg Gprs.r13 hgW).trans (h13'.trans h13),
      (congrArg Gprs.r14 hgW).trans (h14'.trans h14), (congrArg Gprs.r15 hgW).trans (h15'.trans h15)⟩

/-! ## The calls of `malloc` -/

set_option maxHeartbeats 4000000 in
/-- A `call` of `malloc` at `j` (`rsp = S - 24`, the bytes the pushes'): from every return at `j + 5`. -/
theorem tcall (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) {j rel sz : Nat} (hj : j < 271)
    (hd : Dec prof.feat nlc j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : nlc_at.add (j + 5) + BitVec.ofNat 64 rel = 0x633160) {Y : State} {t : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem (Vf V0 g0)) (hr : Y.cpu.rip = nlc_at.add j)
    (hsp : Y.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8) (hdi : Y.cpu.gpr.rdi = BitVec.ofNat 64 sz)
    (k : ∀ (Z : State) (t' : Nat) (Vm : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem Vm →
      Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm → Z.cpu.rip = nlc_at.add (j + 5) → Z.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8 →
      Km Y.cpu.gpr Z.cpu.gpr → Res Wl Kk sz Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s32
  have hl := g0.rsp.isLt
  obtain ⟨-, -, -, e4⟩ := Cal.fr_e hS
  obtain ⟨cM, hcM, hM0⟩ := E.mc
  refine c.s_call hK hA E.hin (lt_len hj) hr hd hcM hM0 htgt
    (by rw [hsp]; exact stk E.wf (by omega) (by omega) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂
  have esp₂ : Y₂.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8 - 8 := by
    rw [hg₂]
    show Y.cpu.gpr.rsp - 8 = _
    rw [hsp]
  refine hmal sz Y₂ t₂ _ _ hK₂ hA₂ hr₂ esp₂ (rds (by rw [e4]; omega)) (by rw [hg₂]; exact hdi) ?_
  intro Z t' V' hKZ hAZ hkp hrZ hspZ hkm hres
  rw [hg₂] at hkm
  exact k Z t' V' hKZ hAZ (agM hS E.kf hkp) hrZ hspZ hkm hres

/-! ## The counting loop -/

set_option maxHeartbeats 4000000 in
/-- From 48 at the `k`-th byte: its class, the counts, to 74. -/
theorem t48 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {k : Nat} (hk : k < n) {Y : State}
    {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem (Vf V0 g0)) (hr : Y.cpu.rip = nlc_at.add 48)
    (hC : Cl V0 g0 Y.cpu.gpr n k k)
    (k74 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vf V0 g0) →
      Z.cpu.rip = nlc_at.add 74 → Cl V0 g0 Z.cpu.gpr n k (k + 1) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s32
  have ag : Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vf V0 g0) := fun _ _ => rfl
  have ec : rb (Vf V0 g0) Y.cpu.gpr.rdx = nb V0 g0.rdi k := by
    rw [hC.dx]
    exact congrArg (ofBytesLE 8) (rdR hS ag (E.rs k hk))
  have et : Y.cpu.gpr.rbx + zb (rb (Vf V0 g0) Y.cpu.gpr.rdx) * 2#64 = ta V0 g0.rdi k := by
    rw [ec, hC.rg.bx] <;> rfl
  have eb : rb (Vf V0 g0) (ta V0 g0.rdi k) = rb V0 (ta V0 g0.rdi k) :=
    congrArg (ofBytesLE 8) (rdR hS ag (E.ra k hk))
  have fc : ∀ i < 1, Foot F.data (Addr.add Y.cpu.gpr.rdx i) := by
    rw [hC.dx]
    exact (E.rs k hk).fd
  have ft : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbx + zb (rb (Vf V0 g0) Y.cpu.gpr.rdx) * 2#64) i) := by
    rw [et]
    exact (E.ra k hk).fd
  cases hq : qa V0 g0.rdi k
  · by_cases hd : dd V0 g0.rdi k
    · -- alnum, a digit: `esi` kept
      refine (c_48 prof).run c E.hin _ hK hA hr
        (vc_48d (by rw [et, eb]; exact hq) (by rw [ec]; exact hd) fc ft) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      refine k74 Z t' hKZ hAZ hrZ ?_
      rw [hgZ]
      exact ⟨hC.rg, hC.r8, hC.r9, hC.dx,
        by show Y.cpu.gpr.rdi + 1#64 = _; rw [hC.di, on1, cnt_f hq],
        by show (Y.cpu.gpr.rsi.setWidth 32).setWidth 64 = _; rw [hC.si, bsw, dg_fd hq hd]⟩
    · -- alnum, not a digit: `esi = 0`
      refine (c_48 prof).run c E.hin _ hK hA hr
        (vc_48x (by rw [et, eb]; exact hq) (by rw [ec]; exact hd) fc ft) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      refine k74 Z t' hKZ hAZ hrZ ?_
      rw [hgZ]
      exact ⟨hC.rg, hC.r8, hC.r9, hC.dx,
        by show Y.cpu.gpr.rdi + 1#64 = _; rw [hC.di, on1, cnt_f hq],
        by show (Y.cpu.gpr.r9.setWidth 32).setWidth 64 = _; rw [hC.r9, dg_fx hq hd] <;> decide⟩
  · -- not alnum
    refine (c_48 prof).run c E.hin _ hK hA hr (vc_48n (by rw [et, eb]; exact hq) fc ft) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
    refine k74 Z t' hKZ hAZ hrZ ?_
    rw [hgZ]
    exact ⟨hC.rg, hC.r8, hC.r9, hC.dx, by rw [cnt_t hq]; exact hC.di, by rw [dg_t hq]; exact hC.si⟩

set_option maxHeartbeats 4000000 in
/-- From 74 after the `k`-th byte: to the next byte, or to the `call` (196 all digits, 91 not). -/
theorem t74 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {k : Nat} (hk : k < n) {Y : State}
    {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem (Vf V0 g0)) (hr : Y.cpu.rip = nlc_at.add 74)
    (hC : Cl V0 g0 Y.cpu.gpr n k (k + 1))
    (kn : k + 1 < n → LcAt prof F Wl L s₀ o gev gP gE V0 g0 n (k + 1))
    (k196 : dg V0 g0.rdi n = true → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 196 (cnt V0 g0.rdi n + 4))
    (k91 : dg V0 g0.rdi n = false → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 91 (cnt V0 g0.rdi n + 1)) :
    GoG prof L o gev gP gE Y t := by
  have hn64 : n < 2 ^ 64 := by have := E.nl; omega
  by_cases hl : k + 1 < n
  · refine (c_74 prof).run c E.hin _ hK hA hr (vc_74l ?_) ?_
    · rw [hC.r8, hC.dx, sko]
      intro h
      have := (r8e hn64 (by omega)).1 h
      omega
    · rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      refine kn hl Z t' hKZ hAZ hrZ ?_
      rw [hgZ]
      exact ⟨hC.rg, hC.r8, hC.r9, by show Y.cpu.gpr.rdx + 1#64 = _; rw [hC.dx, sko], hC.di, hC.si⟩
  · have hkn : k + 1 = n := by omega
    have he : Y.cpu.gpr.r8 = Y.cpu.gpr.rdx + 1#64 := by
      rw [hC.r8, hC.dx, sko]
      exact (r8e hn64 (by omega)).2 hkn
    cases hdg : dg V0 g0.rdi (k + 1)
    · refine (c_74 prof).run c E.hin _ hK hA hr (vc_74n he (by rw [hC.si, hdg] <;> decide)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      refine k91 (by rw [← hkn]; exact hdg) Z t' hKZ hAZ hrZ (by rw [hgZ]; exact hC.rg) ?_
      rw [hgZ]
      show Y.cpu.gpr.rdi + 1#64 = _
      rw [hC.di, on1, hkn]
    · refine (c_74 prof).run c E.hin _ hK hA hr (vc_74d he (by rw [hC.si, hdg] <;> decide)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      refine k196 (by rw [← hkn]; exact hdg) Z t' hKZ hAZ hrZ (by rw [hgZ]; exact hC.rg) ?_
      rw [hgZ]
      show Y.cpu.gpr.rdi + 4#64 = _
      rw [hC.di, on4, hkn]

/-- The counting loop from the `k`-th byte, `m + 1` bytes left. -/
theorem lcAll (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂)
    (k196 : dg V0 g0.rdi n = true → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 196 (cnt V0 g0.rdi n + 4))
    (k91 : dg V0 g0.rdi n = false → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 91 (cnt V0 g0.rdi n + 1)) :
    ∀ m k, k + m + 1 = n → LcAt prof F Wl L s₀ o gev gP gE V0 g0 n k := by
  intro m
  induction m with
  | zero =>
    intro k hk Y t hK hA hr hC
    exact t48 c E (by omega) hK hA hr hC fun Z t' hKZ hAZ hrZ hCZ =>
      t74 c E (by omega) hKZ hAZ hrZ hCZ (fun h => absurd h (by omega)) k196 k91
  | succ m ih =>
    intro k hk Y t hK hA hr hC
    exact t48 c E (by omega) hK hA hr hC fun Z t' hKZ hAZ hrZ hCZ =>
      t74 c E (by omega) hKZ hAZ hrZ hCZ (fun _ => ih (k + 1) (by omega)) k196 k91

/-! ## The copy loop -/

set_option maxHeartbeats 4000000 in
/-- From 131 after the `k`-th byte: to the next byte (140) or to the end (180). -/
theorem t131 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {p : Addr} {d : Nat}
    {Vb : Addr → Byte} {k : Nat} (hk : k + 1 ≤ n) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem (Vst Vb (Addr.add p d) (out V0 g0.rdi (k + 1))))
    (hr : Y.cpu.rip = nlc_at.add 131) (hC : Cp V0 g0 Y.cpu.gpr n p d (k + 1) k)
    (kn : k + 1 < n → LpAt prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb (k + 1))
    (ke : k + 1 = n → A180 prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb (k + 1)) :
    GoG prof L o gev gP gE Y t := by
  have hn64 : n < 2 ^ 64 := by have := E.nl; omega
  by_cases hl : k + 1 < n
  · refine (c_131 prof).run c E.hin _ hK hA hr
      (vc_131l (by rw [hC.dx, hC.rg.r12]; exact (bl hn64 hk).2 hl)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
    refine kn hl Z t' hKZ hAZ hrZ ?_
    rw [hgZ]
    exact ⟨hC.rg, hC.r8, hC.r9, by show Y.cpu.gpr.rdx + 1#64 = _; rw [hC.dx, on1], hC.ax⟩
  · refine (c_131 prof).run c E.hin _ hK hA hr
      (vc_131e (by rw [hC.dx, hC.rg.r12]; exact fun h => hl ((bl hn64 hk).1 h))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
    refine ke (by omega) Z t' hKZ hAZ hrZ ?_
    rw [hgZ]
    exact ⟨hC.rg, hC.r8, hC.r9, by show Y.cpu.gpr.rdx + 1#64 = _; rw [hC.dx, on1], hC.ax⟩

set_option maxHeartbeats 4000000 in
/-- From 140 at the `k`-th byte: alpha (its `tolower` stored), a digit (stored), or neither. -/
theorem t140 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {p : Addr} {d : Nat}
    {Vb : Addr → Byte} (P : Pb Wl Kk V0 g0 n p d Vb) {k : Nat} (hk : k < n) {Y : State} {t : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem (Vst Vb (Addr.add p d) (out V0 g0.rdi k)))
    (hr : Y.cpu.rip = nlc_at.add 140) (hC : Cp V0 g0 Y.cpu.gpr n p d k k)
    (kn : k + 1 < n → LpAt prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb (k + 1))
    (ke : k + 1 = n → A180 prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb (k + 1)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s32
  have hn64 : n < 2 ^ 64 := by have := E.nl; omega
  have ho := outl E.an k (by omega)
  have hcn := cntm V0 g0.rdi k n (by omega)
  have hag := agk E P (k := k) (by omega)
  have hax := hC.ax
  have wr : ∀ i < 1, Foot Wl (Addr.add Y.cpu.gpr.rax i) := by
    rw [hax]
    exact wsub P.w (by omega)
  generalize hV : Vst Vb (Addr.add p d) (out V0 g0.rdi k) = V at hA hag
  have ec : cn V Y.cpu.gpr = nb V0 g0.rdi k := by
    show rb V (Y.cpu.gpr.rbp + Y.cpu.gpr.rdx) = _
    rw [hC.rg.bp, hC.dx]
    exact congrArg (ofBytesLE 8) (rdR hS hag (E.rs k hk))
  have eca : ca V Y.cpu.gpr = tp V0 g0.rdi k := by
    show Y.cpu.gpr.rbx + zb (cn V Y.cpu.gpr) * 2#64 + 1#64 = _
    rw [ec, hC.rg.bx] <;> rfl
  have ecl : cl V Y.cpu.gpr = tl V0 g0.rdi k := by
    show Y.cpu.gpr.r8 + zb (cn V Y.cpu.gpr) * 4#64 = _
    rw [ec, hC.r8] <;> rfl
  have erp : rb V (tp V0 g0.rdi k) = rb V0 (tp V0 g0.rdi k) := congrArg (ofBytesLE 8) (rdR hS hag (E.rp k hk))
  have erl : rdd(V, tl V0 g0.rdi k) = rdd(V0, tl V0 g0.rdi k) :=
    congrArg (ofBytesLE 32) (rdR hS hag (E.rl k hk))
  have fc : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rbp + Y.cpu.gpr.rdx) i) := by
    rw [hC.rg.bp, hC.dx]
    exact (E.rs k hk).fd
  have fa : ∀ i < 1, Foot F.data (Addr.add (ca V Y.cpu.gpr) i) := by
    rw [eca]
    exact (E.rp k hk).fd
  cases hq : qp V0 g0.rdi k
  · -- alpha: its `tolower` stored at `rax`
    refine (c_140 prof).run c E.hin _ hK hA hr (vc_140a (by rw [eca, erp]; exact hq) fc fa
      (by rw [ecl]; exact (E.rl k hk).fd) (by rw [pm1]; exact wr)) ?_
    rintro j' g fl V' ⟨rfl, hV', rfl⟩ Z t' hKZ hAZ hrZ hgZ -
    have eW : V' = Vst Vb (Addr.add p d) (out V0 g0.rdi (k + 1)) := by
      rw [hV', pm1, ecl, erl, toBytesLE_one8, hax, ← hV, out_a hq]
      exact vapp _ _ _ _ _
    rw [eW] at hAZ
    refine t131 c E (by omega) hKZ hAZ hrZ ?_ kn ke
    rw [hgZ]
    exact ⟨hC.rg, hC.r8, hC.r9, hC.dx,
      by show Y.cpu.gpr.rax + 1#64 = _; rw [hax, ad1, out_al hq, Nat.add_assoc]⟩
  · have ha : (rb V (ca V Y.cpu.gpr) &&& 4#8 == 0) = true := by rw [eca, erp]; exact hq
    by_cases hd : dd V0 g0.rdi k
    · -- a digit, stored at `rax`
      have hdd : (d32 (cn V Y.cpu.gpr)).toNat < 10 := by rw [ec]; exact hd
      have eax : Y.cpu.gpr.rax + 1#64 = Addr.add p (d + (out V0 g0.rdi (k + 1)).length) := by
        rw [hax, ad1, out_dl hq hd, Nat.add_assoc]
      by_cases hl : k + 1 < n
      · refine (c_140 prof).run c E.hin _ hK hA hr
          (vc_140dl ha hdd (by rw [hC.dx, hC.rg.r12]; exact (bl hn64 (by omega)).2 hl) fc fa wr) ?_
        rintro j' g fl V' ⟨rfl, hV', rfl⟩ Z t' hKZ hAZ hrZ hgZ -
        have eW : V' = Vst Vb (Addr.add p d) (out V0 g0.rdi (k + 1)) := by
          rw [hV', ec, toBytesLE_one8, hax, ← hV, out_d hq hd]
          exact vapp _ _ _ _ _
        rw [eW] at hAZ
        refine kn hl Z t' hKZ hAZ hrZ ?_
        rw [hgZ]
        exact ⟨hC.rg, hC.r8, hC.r9, by show Y.cpu.gpr.rdx + 1#64 = _; rw [hC.dx, on1], eax⟩
      · refine (c_140 prof).run c E.hin _ hK hA hr
          (vc_140de ha hdd (by rw [hC.dx, hC.rg.r12]; exact fun h => hl ((bl hn64 (by omega)).1 h)) fc fa wr)
          ?_
        rintro j' g fl V' ⟨rfl, hV', rfl⟩ Z t' hKZ hAZ hrZ hgZ -
        have eW : V' = Vst Vb (Addr.add p d) (out V0 g0.rdi (k + 1)) := by
          rw [hV', ec, toBytesLE_one8, hax, ← hV, out_d hq hd]
          exact vapp _ _ _ _ _
        rw [eW] at hAZ
        refine ke (by omega) Z t' hKZ hAZ hrZ ?_
        rw [hgZ]
        exact ⟨hC.rg, hC.r8, hC.r9, by show Y.cpu.gpr.rdx + 1#64 = _; rw [hC.dx, on1], eax⟩
    · -- neither: nothing stored
      refine (c_140 prof).run c E.hin _ hK hA hr (vc_140s ha (by rw [ec]; exact hd) fc fa) ?_
      rintro j' g fl V ⟨rfl, rfl, rfl⟩ Z t' hKZ hAZ hrZ hgZ -
      have eW : V = Vst Vb (Addr.add p d) (out V0 g0.rdi (k + 1)) := by rw [out_s hq hd, hV]
      rw [eW] at hAZ
      refine t131 c E (by omega) hKZ hAZ hrZ ?_ kn ke
      rw [hgZ]
      exact ⟨hC.rg, hC.r8, hC.r9, hC.dx, by rw [out_s hq hd]; exact hax⟩

/-- The copy loop from the `k`-th byte, `m + 1` bytes left. -/
theorem cpAll (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {p : Addr} {d : Nat}
    {Vb : Addr → Byte} (P : Pb Wl Kk V0 g0 n p d Vb)
    (ke : A180 prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb n) :
    ∀ m k, k + m + 1 = n → LpAt prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb k := by
  intro m
  induction m with
  | zero =>
    intro k hk Y t hK hA hr hC
    exact t140 c E P (by omega) hK hA hr hC (fun h => absurd h (by omega)) (fun h => by rw [h]; exact ke)
  | succ m ih =>
    intro k hk Y t hK hA hr hC
    exact t140 c E P (by omega) hK hA hr hC (fun _ => ih (k + 1) (by omega)) (fun h => absurd h (by omega))

/-- From 180 after the name: the 0 stored, the return with `rax = p` and the bytes `Wf`. -/
theorem cpEnd (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂) {p : Addr} {d : Nat}
    {Vb : Addr → Byte} (P : Pb Wl Kk V0 g0 n p d Vb)
    (kr : Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) p (Wf V0 g0.rdi Vb p d n)) :
    A180 prof F Wl L s₀ o gev gP gE V0 g0 n p d Vb n := by
  intro Y t hK hA hr hC
  have ho := outl E.an n (Nat.le_refl n)
  have hf := P.fit
  have e := toNat_add_of_fits (a := p) (i := d + (out V0 g0.rdi n).length) (n := d + cnt V0 g0.rdi n + 1)
    (by omega) hf
  have hag := agk E P (Nat.le_refl n)
  refine t180 c E hK hA hr hC.rg.sp hC.rg.r13 hC.rg.r14 hC.rg.r15
    (by rw [hC.ax]; exact wsub P.w (by omega)) ?_ ?_
  · rw [hC.ax]
    exact hag.st (by rw [toBytesLE_length, e]; omega)
      (noK E.kf P.nk (by rw [e]; omega) (by rw [toBytesLE_length, e]; omega))
  · rw [hC.r9, hC.ax]
    exact kr

/-! ## From the calls -/

set_option maxHeartbeats 4000000 in
/-- From the `call` at 91 (`malloc (cnt n + 1)`): 0 (224), or the copy from `p`. -/
theorem aft91 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hn : 0 < n)
    (kZ : ∀ Vm, Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm → Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) 0#64 Vm)
    (kS : dg V0 g0.rdi n = false → ∀ (p : Addr) (Vm : Addr → Byte), p ≠ 0 →
      Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) p (Wf V0 g0.rdi Vm p 0 n)) :
    dg V0 g0.rdi n = false → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 91 (cnt V0 g0.rdi n + 1) := by
  intro hdg Y t hK hA hr hR hdi
  refine tcall c E hmal (by decide) (call_91 _) ml_91 hK hA hr hR.sp hdi ?_
  intro Z t' Vm hKZ hAZ hag hrZ hspZ hkm hres
  have hR' : Rg V0 g0 Z.cpu.gpr n := ⟨hspZ, hkm.1.trans hR.bx, hkm.2.1.trans hR.bp, hkm.2.2.1.trans hR.r12,
    hkm.2.2.2.1.trans hR.r13, hkm.2.2.2.2.1.trans hR.r14, hkm.2.2.2.2.2.trans hR.r15⟩
  by_cases h0 : Z.cpu.gpr.rax = 0
  · refine (c_96 prof).run c E.hin _ hKZ hAZ hrZ (vc_96z (beq_iff_eq.mpr h0)) ?_
    rintro j' g fl Vm ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    exact t224 c E hKW hAW hrW (by rw [hgW]; exact hR'.sp) (by rw [hgW]; exact hR'.r13)
      (by rw [hgW]; exact hR'.r14) (by rw [hgW]; exact hR'.r15) hag (kZ Vm hag)
  · obtain ⟨hfit, hw, hnk⟩ := Or.resolve_left hres h0
    generalize hp : Z.cpu.gpr.rax = p at hfit hw hnk h0
    have P : Pb Wl Kk V0 g0 n p 0 Vm :=
      ⟨by omega, fun i hi => hw i (by omega), fun y h1 h2 => hnk y h1 (by omega), hag⟩
    refine (c_96 prof).run c E.hin _ hKZ hAZ hrZ (vc_96n (by rw [hp]; exact beq_eq_false_iff_ne.mpr h0)) ?_
    rintro j' g fl Vm ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    refine (c_104 prof).run c E.hin _ hKW hAW hrW (vc_104 E.rU.fd) ?_
    rintro j' g fl Vm ⟨rfl, rfl, rfl⟩ Q t₂ hKQ hAQ hrQ hgQ -
    refine cpAll c E P (cpEnd c E P (kS hdg p Vm h0 hag)) (n - 1) 0 (by omega) Q t₂ hKQ
      (by rw [v0]; exact hAQ) hrQ ?_
    rw [hgQ]
    refine ⟨?_, congrArg (ofBytesLE 64) (rdR E.s32 hag E.rU), ?_, rfl, ?_⟩
    · rw [hgW]
      exact hR'
    · show W.cpu.gpr.r9 = p
      rw [hgW]
      exact hp
    · show W.cpu.gpr.rax = _
      rw [hgW]
      show Z.cpu.gpr.rax = _
      rw [hp, ol0, Nat.add_zero, addr_add_zero]

set_option maxHeartbeats 4000000 in
/-- From the `call` at 196 (`malloc (cnt n + 4)`, all the alnums digits): 0 (224), or `"iso"` and the copy from
`p + 3`. -/
theorem aft196 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 n e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hn : 0 < n)
    (kZ : ∀ Vm, Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm → Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) 0#64 Vm)
    (kI : dg V0 g0.rdi n = true → ∀ (p : Addr) (Vm : Addr → Byte), p ≠ 0 →
      Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) p (Wf V0 g0.rdi (Vi Vm p) p 3 n)) :
    dg V0 g0.rdi n = true → Aft prof F Wl L s₀ o gev gP gE V0 g0 n 196 (cnt V0 g0.rdi n + 4) := by
  intro hdg Y t hK hA hr hR hdi
  refine tcall c E hmal (by decide) (call_196 _) ml_196 hK hA hr hR.sp hdi ?_
  intro Z t' Vm hKZ hAZ hag hrZ hspZ hkm hres
  have hR' : Rg V0 g0 Z.cpu.gpr n := ⟨hspZ, hkm.1.trans hR.bx, hkm.2.1.trans hR.bp, hkm.2.2.1.trans hR.r12,
    hkm.2.2.2.1.trans hR.r13, hkm.2.2.2.2.1.trans hR.r14, hkm.2.2.2.2.2.trans hR.r15⟩
  by_cases h0 : Z.cpu.gpr.rax = 0
  · refine (c_201 prof).run c E.hin _ hKZ hAZ hrZ (vc_201z (beq_iff_eq.mpr h0)) ?_
    rintro j' g fl Vm ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    exact t224 c E hKW hAW hrW (by rw [hgW]; exact hR'.sp) (by rw [hgW]; exact hR'.r13)
      (by rw [hgW]; exact hR'.r14) (by rw [hgW]; exact hR'.r15) hag (kZ Vm hag)
  · obtain ⟨hfit, hw, hnk⟩ := Or.resolve_left hres h0
    generalize hp : Z.cpu.gpr.rax = p at hfit hw hnk h0
    have P : Pb Wl Kk V0 g0 n p 3 (Vi Vm p) :=
      ⟨by omega, fun i hi => hw i (by omega), fun y h1 h2 => hnk y h1 (by omega),
        hag.st (by rw [toBytesLE_length]; omega)
          (noK E.kf hnk (Nat.le_refl _) (by rw [toBytesLE_length]; omega))⟩
    refine (c_201 prof).run c E.hin _ hKZ hAZ hrZ (vc_201n (by rw [hp]; exact beq_eq_false_iff_ne.mpr h0)
      (by rw [hp]; exact fun i hi => hw i (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    rw [hp] at hAW
    refine (c_104 prof).run c E.hin _ hKW hAW hrW (vc_104 E.rU.fd) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Q t₂ hKQ hAQ hrQ hgQ -
    refine cpAll c E P (cpEnd c E P (kI hdg p Vm h0 hag)) (n - 1) 0 (by omega) Q t₂ hKQ
      (by rw [v0]; exact hAQ) hrQ ?_
    rw [hgQ]
    refine ⟨?_, congrArg (ofBytesLE 64) (rdR E.s32 P.ag E.rU), ?_, rfl, ?_⟩
    · rw [hgW]
      exact hR'
    · show W.cpu.gpr.r9 = p
      rw [hgW]
      exact hp
    · show W.cpu.gpr.rax = _
      rw [hgW]
      show Z.cpu.gpr.rax + 3#64 = _
      rw [hp, ol0, Nat.add_zero] <;> rfl

set_option maxHeartbeats 4000000 in
/-- An empty name: from the `call` at 245 (`malloc (4)`): 0 (224), or `"iso"` and the 0 at `p + 3`. -/
theorem aft245 (c : Seg prof F Wl L s₀ o) (E : Env F Wl L Kk V0 g0 0 e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem (Vf V0 g0)) (hr : Y.cpu.rip = nlc_at.add 245)
    (hsp : Y.cpu.gpr.rsp = g0.rsp - 8 - 8 - 8) (hdi : Y.cpu.gpr.rdi = 4#64) (h13 : Y.cpu.gpr.r13 = g0.r13)
    (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (kZ : ∀ Vm, Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm → Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) 0#64 Vm)
    (kI : ∀ (p : Addr) (Vm : Addr → Byte), p ≠ 0 → Ag (Kr Kk g0.rsp) (Vf V0 g0) Vm →
      Kret prof F Wl L s₀ o gev gP gE g0 (e₂.add j₂) p (Wf V0 g0.rdi (Vi Vm p) p 3 0)) :
    GoG prof L o gev gP gE Y t := by
  refine tcall c E hmal (sz := 4) (by decide) (call_245 _) ml_245 hK hA hr hsp hdi ?_
  intro Z t' Vm hKZ hAZ hag hrZ hspZ hkm hres
  have e13 : Z.cpu.gpr.r13 = g0.r13 := hkm.2.2.2.1.trans h13
  have e14 : Z.cpu.gpr.r14 = g0.r14 := hkm.2.2.2.2.1.trans h14
  have e15 : Z.cpu.gpr.r15 = g0.r15 := hkm.2.2.2.2.2.trans h15
  by_cases h0 : Z.cpu.gpr.rax = 0
  · refine (c_250 prof).run c E.hin _ hKZ hAZ hrZ (vc_250z (beq_iff_eq.mpr h0)) ?_
    rintro j' g fl Vm ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    exact t224 c E hKW hAW hrW (by rw [hgW]; exact hspZ) (by rw [hgW]; exact e13) (by rw [hgW]; exact e14)
      (by rw [hgW]; exact e15) hag (kZ Vm hag)
  · obtain ⟨hfit, hw, hnk⟩ := Or.resolve_left hres h0
    generalize hp : Z.cpu.gpr.rax = p at hfit hw hnk h0
    have ag1 : Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vi Vm p) :=
      hag.st (by rw [toBytesLE_length]; omega) (noK E.kf hnk (Nat.le_refl _) (by rw [toBytesLE_length]; omega))
    have e3 : (p + 3#64).toNat = p.toNat + 3 := toNat_add_of_fits (a := p) (i := 3) (n := 4) (by omega) hfit
    refine (c_250 prof).run c E.hin _ hKZ hAZ hrZ (vc_250n (by rw [hp]; exact beq_eq_false_iff_ne.mpr h0)
      (by rw [hp]; exact hw)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
    rw [hp] at hAW
    have hax : W.cpu.gpr.rax = p + 3#64 := by
      rw [hgW]
      show Z.cpu.gpr.rax + 3#64 = _
      rw [hp]
    have h9 : W.cpu.gpr.r9 = p := by
      rw [hgW]
      exact hp
    have kI' := kI p Vm h0 hag
    rw [wf0] at kI'
    refine t180 c E hKW hAW hrW (by rw [hgW]; exact hspZ) (by rw [hgW]; exact e13) (by rw [hgW]; exact e14)
      (by rw [hgW]; exact e15) (by rw [hax]; exact wsub (e := 3) hw (by omega)) ?_ ?_
    · rw [hax]
      exact ag1.st (by rw [toBytesLE_length, e3]; omega)
        (noK E.kf hnk (by rw [e3]; omega) (by rw [toBytesLE_length, e3]; omega))
    · rw [h9, hax]
      exact kI'

/-! ## The function -/

set_option maxHeartbeats 4000000 in
/-- `_nl_normalize_codeset (s, n)` from its entry: `malloc` gave 0, the return with `rax = 0` (`kZ`); else the
return with `rax = p` and the bytes `Wf`: `out n` and a 0 at `p` (`kS`), or after `"iso"` when all the alnums are
digits (`kI`). The registers a call keeps, `Vm` the bytes `malloc` left (kept where `Kr` holds). -/
theorem nlc_ok (c : Seg prof F Wl L s₀ o) {X : State} {t : Nat}
    (E : Env F Wl L Kk V0 X.cpu.gpr n e₂ j₂) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V0)
    (hrip : X.cpu.rip = nlc_at) (hmal : Mal prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp Kk)
    (kZ : ∀ Vm, Ag (Kr Kk X.cpu.gpr.rsp) (Vf V0 X.cpu.gpr) Vm →
      Kret prof F Wl L s₀ o gev gP gE X.cpu.gpr (e₂.add j₂) 0#64 Vm)
    (kS : dg V0 X.cpu.gpr.rdi n = false → ∀ (p : Addr) (Vm : Addr → Byte), p ≠ 0 →
      Ag (Kr Kk X.cpu.gpr.rsp) (Vf V0 X.cpu.gpr) Vm →
      Kret prof F Wl L s₀ o gev gP gE X.cpu.gpr (e₂.add j₂) p (Wf V0 X.cpu.gpr.rdi Vm p 0 n))
    (kI : dg V0 X.cpu.gpr.rdi n = true → ∀ (p : Addr) (Vm : Addr → Byte), p ≠ 0 →
      Ag (Kr Kk X.cpu.gpr.rsp) (Vf V0 X.cpu.gpr) Vm →
      Kret prof F Wl L s₀ o gev gP gE X.cpu.gpr (e₂.add j₂) p (Wf V0 X.cpu.gpr.rdi (Vi Vm p) p 3 n)) :
    GoG prof L o gev gP gE X t := by
  have hS := E.s32
  have hl := X.cpu.gpr.rsp.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  have wfr : ∀ b : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ b.toNat → b.toNat + 8 ≤ X.cpu.gpr.rsp.toNat →
      ∀ i < 8, Foot Wl (Addr.add b i) := fun b h1 h2 => stk E.wf h1 h2 (by omega)
  have hr0 : X.cpu.rip = nlc_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hn : n = 0
  · subst hn
    refine (c_0 prof).run c E.hin _ hK hA hr0 (vc_0e (by rw [E.rn] <;> decide) (wfr _ (by omega) (by omega))
      (wfr _ (by omega) (by omega)) (wfr _ (by omega) (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
    exact aft245 c E hmal hK₁ hA₁ hr₁ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl) kZ (kI rfl)
  · refine (c_0 prof).run c E.hin _ hK hA hr0 (vc_0n (T := T0 V0)
      (by rw [E.rn]; exact nz (by have := E.nl; omega) hn) hS E.d1 rfl (wfr _ (by omega) (by omega))
      (wfr _ (by omega) (by omega)) (wfr _ (by omega) (by omega)) E.fT) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
    refine lcAll c E (aft196 c E hmal (by omega) kZ kI) (aft91 c E hmal (by omega) kZ kS) (n - 1) 0 (by omega)
      Y t₁ hK₁ hA₁ hr₁ ?_
    rw [hg₁]
    exact ⟨⟨rfl, rfl, rfl, E.rn, rfl, rfl, rfl⟩, by show X.cpu.gpr.rsi + X.cpu.gpr.rdi = _; rw [E.rn], rfl,
      (az _).symm, rfl, rfl⟩

end

end FV7z.Nlc
