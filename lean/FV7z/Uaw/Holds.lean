import FV7z.Uaw.Cuts
import FV7z.Usf.Holds
/-!
# `UString::operator= (const wchar_t *s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::operator= (s)` at `0x44d670` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `s` in
`rsi`: the length `n` of `s` (`s[0]` tested at 22, then the loop at 32 from the index 1; for `n = 0` at 144
`r14 = _chars`, `r12d = 1`); if `_limit < n` (the 4 bytes at `this + 12`; `jb` at 56) `newBuf = new wchar_t[n + 1]`
(`call` at 104 to `operator new`, `Onw.onw_at + 64`), `delete [] _chars` unless null (`call` at 121 to the thunk at
`0x6014f0`), `_chars = newBuf`, `_limit = n` (126); else `r14 = _chars` (58). Then (62) `_len = n`,
`wmemcpy (_chars, s, n + 1)` (`call` at 75 to `Wmc.wmc_at`), `rax = this` and the `ret` at 91. `push r14; push r13;
push r12; push rbp; push rbx`, `r13` = `this`, `rbp` = `s`, `rbx` = `n`, `r12` = `n + 1`, `r14` = `_chars` across
the calls.

The callees are hypotheses, as in `FV7z/Usf/Holds.lean` (the same pushes: `V5`, `Sv5`): a continuation at each
entry (`kn`, `kd`; `kmA`, `km0`, `km1` for `wmemcpy` after each of the three ways to it, `Kc`), given the run from its
return and the callee's own post (`Pn`, `Pd`, `Pw`); `kr` at the return address. From the entry to 62 or to the
`call` of `operator new` a `Seg.cfg` (`FV7z/Ucw/Holds.lean`, the same count; the string is `Ucw.Wz`).

- `ln`: `n` as stored; `gJ`, `gW`: the registers at 62 without `operator new` and at its `call`.
- `I32`, `Inv`, `Fin`, `Nx`: the loop's head at the index `k` (measure `n - k + 1`), the invariant, the exits, the
  post of `Seg.cfg`.
- `vc_0`, `vc_32`, `vc_62`, `vc_80`, `vc_109`, `vc_126`: the verification conditions of the pieces.
- `uaw_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uaw
open FV7z.Uau (zl VB rq_out)
open FV7z.Usf (V5 Sv5 m5 sv5)

/-- The `call`s to `wmemcpy`, `operator new` and `operator delete []`. -/
def pcw : List Byte := [0xe8, 0x40, 0xfc, 0x20, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2161728] 5) := by dec_rfl
theorem wc_75 : pcw <+: uaw.drop 75 := by decide +kernel
theorem call_75 (feat : Features) : Dec feat uaw 75 (FV7z.mk .call 64 [.rel 2161728] 5) :=
  Dec.shift (j := 75) (k := 0) (pcw_0 feat) wc_75 (Nat.zero_le _)
theorem tgt_75 : uaw_at.add (75 + 5) + BitVec.ofNat 64 2161728 = Wmc.wmc_at.add 0 := by decide
def pcn : List Byte := [0xe8, 0xd3, 0x52, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1790675] 5) := by dec_rfl
theorem wc_104 : pcn <+: uaw.drop 104 := by decide +kernel
theorem call_104 (feat : Features) : Dec feat uaw 104 (FV7z.mk .call 64 [.rel 1790675] 5) :=
  Dec.shift (j := 104) (k := 0) (pcn_0 feat) wc_104 (Nat.zero_le _)
theorem tgt_104 : uaw_at.add (104 + 5) + BitVec.ofNat 64 1790675 = Onw.onw_at.add 64 := by decide
def pcd : List Byte := [0xe8, 0x02, 0x3e, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1785346] 5) := by dec_rfl
theorem wc_121 : pcd <+: uaw.drop 121 := by decide +kernel
theorem call_121 (feat : Features) : Dec feat uaw 121 (FV7z.mk .call 64 [.rel 1785346] 5) :=
  Dec.shift (j := 121) (k := 0) (pcd_0 feat) wc_121 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_91 : pret <+: uaw.drop 91 := by decide +kernel
theorem ret_91 (feat : Features) : Dec feat uaw 91 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 91) (k := 0) (pret_0 feat) w_91 (Nat.zero_le _)

/-! ## The invariant -/

/-- `n` as `mov [r13 + 8], ebx` and `mov [r13 + 12], ebx` store it. -/
abbrev ln (n : Nat) : BitVec 32 := BitVec.setWidth 32 (BitVec.ofNat 64 n)

/-- The registers at 62 without `operator new` (`_chars` = `p`; `rax`, `rcx`, `rdx` any): `rbx` = `n`,
`r12` = `n + 1`, `r13` = `this`, `rbp` = `s`, `r14` = `_chars`, 40 below the entry. -/
abbrev gJ (g : Gprs) (n : Nat) (p a cx d : BitVec 64) : Gprs :=
  { g with rax := a, rcx := cx, rdx := d, rbx := BitVec.ofNat 64 n, r12 := BitVec.ofNat 64 (n + 1), r13 := g.rdi,
           rbp := g.rsi, r14 := p, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The registers at the `call` of `operator new`: `rdi` = `4 n + 4`. -/
abbrev gW (g : Gprs) (n : Nat) (cx d : BitVec 64) : Gprs :=
  { g with rax := BitVec.ofNat 64 n, rcx := cx, rdx := d, rbx := BitVec.ofNat 64 n, r12 := BitVec.ofNat 64 (n + 1),
           r13 := g.rdi, rbp := g.rsi, rdi := BitVec.ofNat 64 n * 4#64 + 4#64, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The loop's head at the index `k`: `rbx` = `k`. -/
def I32 (g₀ : Gprs) (k : Nat) (g : Gprs) : Prop :=
  ∃ a cx d q, g = { g₀ with rax := a, rcx := cx, rdx := d, rbx := BitVec.ofNat 64 k, r12 := q, r13 := g₀.rdi,
                            rbp := g₀.rsi, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The invariant at the cut points (`VS` the bytes after the pushes). -/
def Inv (g₀ : Gprs) (V₀ VS : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = n + 2 ∧ g = g₀ ∧ V = V₀) ∨ (ℓ = 32 ∧ V = VS ∧ ∃ k, k < n ∧ m = n - k + 1 ∧ I32 g₀ k g)

/-- The exits: 62 without `operator new` (`n = 0`, or `_limit ≥ n`), its `call` (`_limit < n`). -/
def Fin (g₀ : Gprs) (VS : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = VS ∧ ((j = 62 ∧ (n = 0 ∨ ¬ (rdd(VS, g₀.rdi + 12#64)).toNat < n) ∧
      ∃ a cx d, g = gJ g₀ n (rdq(VS, g₀.rdi)) a cx d) ∨
    (j = 104 ∧ (rdd(VS, g₀.rdi + 12#64)).toNat < n ∧ ∃ cx d, g = gW g₀ n cx d))

/-- At an exit: a cut point's invariant with a smaller measure, or `Fin`. -/
def Nx (g₀ : Gprs) (V₀ VS : Addr → Byte) (n m : Nat) : Post :=
  fun j' g' _ V' => (∃ m' < m, Inv g₀ V₀ VS n j' m' g' V') ∨ Fin g₀ VS n j' g' V'

variable {g₀ : Gprs} {V₀ VS : Addr → Byte} {n : Nat}

theorem x32 {m k : Nat} (hk : k < n) (hm : n - k + 1 < m) {a cx d b q : BitVec 64} (hb : b = BitVec.ofNat 64 k)
    {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rbx := b, r12 := q, r13 := g₀.rdi, rbp := g₀.rsi,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 32 g fl VS := by
  subst hb hg
  exact Or.inl ⟨n - k + 1, hm, Or.inr ⟨rfl, rfl, k, hk, rfl, a, cx, d, q, rfl⟩⟩

theorem x62 {m : Nat} (hm : 0 < m) (hz : n = 0 ∨ ¬ (rdd(VS, g₀.rdi + 12#64)).toNat < n)
    {a cx d b q p : BitVec 64} (hb : b = BitVec.ofNat 64 n) (hq : q = BitVec.ofNat 64 (n + 1))
    (hp : p = rdq(VS, g₀.rdi)) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rbx := b, r12 := q, r13 := g₀.rdi, rbp := g₀.rsi, r14 := p,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 62 g fl VS := by
  subst hb hq hp hg
  exact Or.inr ⟨rfl, .inl ⟨rfl, hz, a, cx, d, rfl⟩⟩

theorem x62L {m : Nat} (hm : 0 < m) {M L : BitVec 32} (hc : decide (M.toNat < L.toNat) = false)
    (hL : L.toNat = n) (hM : M = rdd(VS, g₀.rdi + 12#64)) {a cx d b q p : BitVec 64}
    (hb : b = BitVec.ofNat 64 n) (hq : q = BitVec.ofNat 64 (n + 1)) (hp : p = rdq(VS, g₀.rdi)) {g : Gprs}
    {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rbx := b, r12 := q, r13 := g₀.rdi, rbp := g₀.rsi, r14 := p,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 62 g fl VS := by
  subst hM
  exact x62 hm (.inr (by rw [← hL]; exact of_decide_eq_false hc)) hb hq hp hg

theorem x104 {m : Nat} (hm : 0 < m) {M L : BitVec 32} (hc : decide (M.toNat < L.toNat) = true)
    (hL : L.toNat = n) (hM : M = rdd(VS, g₀.rdi + 12#64)) {a cx d b q : BitVec 64} (ha : a = BitVec.ofNat 64 n)
    (hb : b = BitVec.ofNat 64 n) (hq : q = BitVec.ofNat 64 (n + 1)) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rbx := b, r12 := q, r13 := g₀.rdi, rbp := g₀.rsi,
                        rdi := a * 4#64 + 4#64, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 104 g fl VS := by
  subst hM ha hb hq hg
  exact Or.inr ⟨rfl, .inr ⟨rfl, by rw [← hL]; exact of_decide_eq_true hc, cx, d, rfl⟩⟩

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- The pushes, `mov r13, rdi; mov rbp, rsi; mov ecx, [rsi]; xor ebx, ebx; test ecx, ecx; je`: for the length 0
`mov r14, [rdi]; mov r12d, 1` to 62, else the loop's head at the index 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (hw : Ucw.Wz F (V5 V g) g.rsi n) :
    W_0 F Wl (Nx g V (V5 V g) n (n + 2)) g f V := by
  obtain ⟨-, hz, hnz, hf⟩ := hw
  have f0 : ∀ j < 4, Foot F.data (Addr.add g.rsi j) := by
    have := hf 0 (Nat.zero_le _)
    rwa [Nat.mul_zero, addr_add_zero] at this
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · have hX : (rdd(V5 V g, g.rsi) == 0) = true := by
      rw [beq_iff_eq]
      have e := hz
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V5] at hs1 hs2 hs3 hs4 hs5 f0 fd0 hX ⊢
    wpx [W_0, W_144, W_26, o0, o1, o10, Ucw.xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | with_reducible exact fd0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x62 (by omega) (by exact Or.inl rfl) (by decide) (by decide) (by rfl) rfl
  · have hX : (rdd(V5 V g, g.rsi) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      have e := hnz 0 hp
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V5] at hs1 hs2 hs3 hs4 hs5 f0 fd0 hX ⊢
    wpx [W_0, W_144, W_26, o0, o1, o10, Ucw.xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | with_reducible exact fd0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x32 (k := 0) hp (by omega) (by rfl) rfl

set_option maxHeartbeats 2000000 in
/-- The loop's head at the index `k`: `mov edx, ebx; lea eax, [rbx + 1]; lea r12d, [rdx + 2];
mov edx, [rbp + rax * 4]; mov rbx, rax; test edx, edx; jne`: the head at `k + 1` for a character not 0, else
(`k + 1` = `n`) `cmp [r13 + 12], eax; jb`: `lea rdi, [rax * 4 + 4]` to the `call` of `operator new`, or
`mov r14, [r13]` to 62. -/
theorem vc_32 {k : Nat} {g : Gprs} {f : Rflags} (hw : Ucw.Wz F VS g₀.rsi n) (hk : k < n)
    (fd0 : ∀ i < 8, Foot F.data (Addr.add g₀.rdi i)) (fd12 : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 12#64) i))
    (h : I32 g₀ k g) : W_32 F Wl (Nx g₀ V₀ VS n (n - k + 1)) g f VS := by
  obtain ⟨hn, hz, hnz, hf⟩ := hw
  obtain ⟨a, cx, d, q, rfl⟩ := h
  have hA := Ucw.ldw g₀.rsi (k := k) (by omega)
  have fk := hf (k + 1) (by omega)
  have e1 := Ucw.sk1 (k := k) (by omega)
  by_cases hc : k + 1 = n
  · have e2 := Ucw.sk2 (k := k) (by omega)
    have hX : (rdd(VS, Addr.add g₀.rsi (4 * (k + 1))) == 0) = true := by
      rw [beq_iff_eq, hc]
      exact hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX fd0 fd12 ⊢
    wpx [W_32, W_52, W_96, W_58, o2, o3, o7, o4, Op.cmpmr, hA, hX, BitVec.and_self, eq_self_iff_true,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and,
      and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | with_reducible exact fd0
      | with_reducible exact fd12
      | apply And.intro
      | intro)
    all_goals rename_i hcf
    all_goals first
      | exact x104 (by omega) hcf
          (by simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rfl)
          (by rw [← hc]; exact e1) (by rw [← hc]; exact e1) (by rw [← hc]; exact e2) rfl
      | exact x62L (by omega) hcf
          (by simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rfl)
          (by rw [← hc]; exact e1) (by rw [← hc]; exact e2) (by rfl) rfl
  · have hX : (rdd(VS, Addr.add g₀.rsi (4 * (k + 1))) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact hnz (k + 1) (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_52, W_96, W_58, o2, o3, o7, o4, Op.cmpmr, hA, hX, BitVec.and_self, eq_self_iff_true,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and,
      and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x32 (k := k + 1) (by omega) (by omega) (by exact e1) rfl

theorem vcAll (hw : Ucw.Wz F VS g₀.rsi n) (hV : VS = V5 V₀ g₀)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add g₀.rdi i)) (fd12 : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 12#64) i))
    (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ VS n ℓ m g V) :
    Wt ℓ F Wl (Nx g₀ V₀ VS n m) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, k, hk, rfl, h⟩ := h
  · subst hV
    exact vc_0 hs1 hs2 hs3 hs4 hs5 fd0 hw
  · exact vc_32 hw hk fd0 fd12 h

/-- `mov [r13 + 8], ebx; mov rdx, r12; mov rsi, rbp; mov rdi, r14` to the `call` at 75. -/
theorem vc_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : BitVec 64} (h13 : g.r13 = p)
    (w8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    (h : ∀ fl, Q 75 { g with rdx := g.r12, rsi := g.rbp, rdi := g.r14 } fl
      (Vst V (p + 8#64) (toBytesLE (BitVec.setWidth 32 g.rbx) 4))) :
    W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h13 w8 h ⊢
  subst h13
  wpx [W_62, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- Back from `wmemcpy`: `pop rbx; mov rax, r13; pop rbp; pop r12; pop r13; pop r14` to the `ret` at 91. -/
theorem vc_80 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 91
      { g with
          rax := g.r13,
          rbx := rdq(V, g.rsp),
          rbp := rdq(V, g.rsp + 8),
          r12 := rdq(V, g.rsp + 8 + 8),
          r13 := rdq(V, g.rsp + 8 + 8 + 8),
          r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 + 8 + 8 } fl V) :
    W_80 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl0 hl1 hl2 hl3 hl4 h ⊢
  wpx [W_80, o6]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new`: `mov rdi, [r13]; mov r14, rax; test rdi, rdi; je 126`, else to the `call` at 121. -/
theorem vc_109 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (h13 : g.r13 = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h126 : rdq(V, p) = 0 → ∀ fl, Q 126 { g with rdi := rdq(V, p), r14 := g.rax } fl V)
    (h121 : rdq(V, p) ≠ 0 → ∀ fl, Q 121 { g with rdi := rdq(V, p), r14 := g.rax } fl V) :
    W_109 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h13 f0 h126 h121 ⊢
  subst h13
  by_cases h1 : rdq(V, r13) = 0
  · have hb : (rdq(V, r13) == 0) = true := beq_iff_eq.2 h1
    wpx [W_109, o8, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h126 h1 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (rdq(V, r13) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_109, o8, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h121 h1 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r13], r14; mov [r13 + 12], ebx` and the jump to 62. -/
theorem vc_126 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q b : BitVec 64}
    (h13 : g.r13 = p) (h14 : g.r14 = q) (hbx : g.rbx = b) (w0 : ∀ i < 8, Foot Wl (Addr.add p i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (p + 12#64) i)) (h : ∀ fl, Q 62 g fl (VB V p q (BitVec.setWidth 32 b))) :
    W_126 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h13 h14 hbx w0 w12 h ⊢
  subst h13 h14 hbx
  wpx [W_126, o9]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The bytes after `_len = n` for the object at `p`. -/
abbrev VL (W : Addr → Byte) (p : BitVec 64) (n : Nat) : Addr → Byte := Vst W (p + 8#64) (toBytesLE (ln n) 4)

/-- At `wmemcpy`'s entry from 62 with the registers `g` and the bytes `W` there (`x` the entry's registers, `r` the
return address): `_len = n` stored, `rdi` = `r14`, `rdx` = `r12`, `rsi` = `rbp`, `rsp` 48 below the entry's, the
return address pushed; back at `uaw_at + 80` with `rsp` 40 below the entry's, `r13` = `this`, the saved registers
and the return address (`Sv5`) and `wmemcpy`'s post `Pw`. -/
def Kc (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (x : Gprs) (r : Addr) (n : Nat) (Pw : State → State → (Addr → Byte) → Prop) (g : Gprs)
    (W : Addr → Byte) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst (VL W x.rdi n) (x.rsp - 48) (toBytesLE (uaw_at.add 80) 8)) →
    Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = { g with rdx := g.r12, rsi := g.rbp, rdi := g.r14 }.set 4 (x.rsp - 48) →
    (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
      Zw.cpu.rip = uaw_at.add 80 → Zw.cpu.gpr.rsp = x.rsp - 40 → Zw.cpu.gpr.r13 = x.rdi → Sv5 V₂ x r →
      Pw Y Zw V₂ → GoG prof L o gev gP gE Zw t'') →
    GoG prof L o gev gP gE Y t'

/-- The registers at the return address from those `z` at 80 (`x` the entry's): `rax` = `this`, the saved ones
back. -/
abbrev gR (z x : Gprs) : Gprs :=
  { z with rax := x.rdi, rbx := x.rbx, rbp := x.rbp, r12 := x.r12, r13 := x.r13, r14 := x.r14, rsp := x.rsp + 8 }

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::operator= (s)` (`this` = `rdi`, `s` = `rsi`) from its entry, `n` the length of `s` (`Wz`; its
characters clear of the pushes). If `_limit < n`, at `operator new`'s entry with the registers `gW` (`kn`), back at
`uaw_at + 109` (`Pn`), at the thunk of `operator delete []` with `rdi` = `_chars` unless null (`kd`), back at
`uaw_at + 126` (`Pd`). Then, and also without `operator new`, at `wmemcpy`'s entry (`kmA`, `km0`, `km1`: `Kc`),
back at `uaw_at + 80` (`Pw`), at the return address with `rax` = `this` and the saved registers back (`kr`). -/
theorem uaw_ok {Pn : State → (Addr → Byte) → Prop} {Pd : State → State → (Addr → Byte) → Prop}
    {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uaw_at uaw) (hinN : CodeIn L Onw.onw_at Onw.onw)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uaw_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hw : Ucw.Wz F V X.cpu.gpr.rsi n)
    (hsd : ∀ i ≤ n, (Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ 2 ^ 64 ∧
      ((Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 40 ∨
        X.cpu.gpr.rsp.toNat ≤ (Addr.add X.cpu.gpr.rsi (4 * i)).toNat))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : ∀ (Y : State) (t' : Nat) (cx d : BitVec 64), (Usf.tlm V X.cpu.gpr).toNat < n → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V5 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uaw_at.add 109) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gW X.cpu.gpr n cx d).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = uaw_at.add 109 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zn.cpu.gpr.r13 = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbx = BitVec.ofNat 64 n → Pn Zn V₁ → GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (uaw_at.add 126) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r14 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = uaw_at.add 126 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.r13 = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = BitVec.ofNat 64 n → Zd.cpu.gpr.r14 = Zn.cpu.gpr.rax → Pd Zn Zd V₃ →
        GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : (n = 0 ∨ ¬ (Usf.tlm V X.cpu.gpr).toNat < n) → ∀ a cx d : BitVec 64,
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) n Pw
        (gJ X.cpu.gpr n (rdq(V, X.cpu.gpr.rdi)) a cx d) (V5 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) n Pw
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r14 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (ln n)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) n Pw Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (ln n)))
    (kr : ∀ (Y Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Y Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR Zw.cpu.gpr X.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have a40 : X.cpu.gpr.rsp - 40 + 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have a32 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have a24 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40) i) := fun i hi => c.hws _ (hs5 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have td12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- from 80 (the pops) to the return address
  have fin : ∀ (U : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = uaw_at.add 80 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.r13 = X.cpu.gpr.rdi →
      Sv5 W X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = gR U.cpu.gpr X.cpu.gpr → GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U W t' hKU hAU hrU hs h13 hsv k
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hsv
    refine (c_80 prof).run c hin (fun j' g' _ V' => j' = 91 ∧
        g' = { U.cpu.gpr with
            rax := X.cpu.gpr.rdi, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
            r13 := X.cpu.gpr.r13, r14 := X.cpu.gpr.r14, rsp := X.cpu.gpr.rsp } ∧ V' = W) hKU hAU hrU
      (vc_80 (by rw [hs]; exact h40) (by rw [hs, a40]; exact h32) (by rw [hs, a40, a32]; exact h24)
        (by rw [hs, a40, a32, a24]; exact h16) (by rw [hs, a40, a32, a24, a16]; exact h8)
        fun _ => ⟨rfl, by rw [hs, a40, a32, a24, a16, a8, hb1, hb2, hb3, hb4, hb5, h13], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_91 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hb6) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₅ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  -- from 62: `_len = n`, `wmemcpy` (`Kc`), back at 80, then the return
  have run62 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = uaw_at.add 62 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.r13 = X.cpu.gpr.rdi → g.rbx = BitVec.ofNat 64 n →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) n Pw g W →
      GoG prof L o gev gP gE U t' := by
    intro U g W t' hKU hAU hrU hgU hs h13 hbx kc
    subst hgU
    refine (c_62 prof).run c hin (fun j' g' _ V' => j' = 75 ∧
        g' = { U.cpu.gpr with rdx := U.cpu.gpr.r12, rsi := U.cpu.gpr.rbp, rdi := U.cpu.gpr.r14 } ∧
        V' = VL W X.cpu.gpr.rdi n) hKU hAU hrU
      (vc_62 h13 fw8 fun _ => ⟨rfl, rfl, by rw [hbx]⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ Y t₄ hKY hAY hrY hgY -
    subst V₄
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact hs
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_75 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
      tgt_75 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine kc Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
    -- back from `wmemcpy`
    intro Zw V₂ t₃ hKw hAw hrw hws hw13 hsv hPw
    exact fin Zw V₂ t₃ hKw hAw hrw hws hw13 hsv
      fun Z' t₆ hKZ hAZ hrZ hgZ => kr Y₂ Zw V₂ Z' t₆ hPw hKZ hAZ hrZ hgZ
  -- from 126 (`_chars = newBuf; _limit = n`) to 62
  have run126 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (q : BitVec 64) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = uaw_at.add 126 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.r13 = X.cpu.gpr.rdi → g.rbx = BitVec.ofNat 64 n → g.r14 = q →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) n Pw g (VB W X.cpu.gpr.rdi q (ln n)) →
      GoG prof L o gev gP gE U t' := by
    intro U g W q t' hKU hAU hrU hgU hs h13 hbx h14 k
    subst hgU
    refine (c_126 prof).run c hin (fun j' g' _ V' => j' = 62 ∧ g' = U.cpu.gpr ∧
        V' = VB W X.cpu.gpr.rdi q (ln n)) hKU hAU hrU
      (vc_126 h13 h14 hbx fw0 fw12 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    exact run62 U' U.cpu.gpr _ t₄ hKU' hAU' hrU' hgU' hs h13 hbx k
  -- the loads before any store
  have hm0 : rdd(V5 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = Usf.tlm V X.cpu.gpr :=
    congrArg (ofBytesLE 32) (m5 (V := V) (g := X.cpu.gpr) (by omega) (X.cpu.gpr.rdi + 12#64) 4
      (by rw [td12]; omega) (by rw [td12]; omega))
  have hq0 : rdq(V5 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) :=
    congrArg (ofBytesLE 64) (m5 (V := V) (g := X.cpu.gpr) (by omega) X.cpu.gpr.rdi 8 (by omega) (by omega))
  -- the string as it was before the pushes
  have rd0 : ∀ i ≤ n, rdd(V5 V X.cpu.gpr, Addr.add X.cpu.gpr.rsi (4 * i)) =
      rdd(V, Addr.add X.cpu.gpr.rsi (4 * i)) := fun i hi =>
    congrArg (ofBytesLE 32) (m5 (V := V) (g := X.cpu.gpr) (by omega) _ 4 (hsd i hi).1 (hsd i hi).2)
  have hw' : Ucw.Wz F (V5 V X.cpu.gpr) X.cpu.gpr.rsi n := by
    obtain ⟨w1, w2, w3, w4⟩ := hw
    refine ⟨w1, ?_, fun i hi => ?_, w4⟩
    · rw [rd0 n (Nat.le_refl _)]
      exact w2
    · rw [rd0 i (by omega)]
      exact w3 i hi
  -- the count, to 62 or to the `call` of `operator new`
  refine c.cfg hin (fun ℓ => spAll prof ℓ)
    (fun ℓ m g _ V' => Inv X.cpu.gpr V (V5 V X.cpu.gpr) n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr (V5 V X.cpu.gpr) n j g V')
    (fun ℓ m g f V' h => vcAll hw' rfl hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)
      (by rw [e32]; exact hs4) (by rw [e40]; exact hs5) fd0 fd12 ℓ m g f V' h) ?_
    (n + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V₁ ⟨rfl, ⟨rfl, hz, a, cx, d, rfl⟩ | ⟨rfl, hc, cx, d, rfl⟩⟩ Y t₁ hKY hAY hrY hgY -
  · -- the buffer as it is
    rw [hm0] at hz
    rw [hq0] at hgY
    exact run62 Y _ (V5 V X.cpu.gpr) t₁ hKY hAY hrY hgY e40 rfl rfl (kmA hz a cx d)
  -- `new wchar_t[n + 1]`
  rw [hm0] at hc
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_104 _) hinN (tgt := 64)
    (Onw.lt_len (by decide)) tgt_104 hst ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsY, c48] at hA₄
  refine kn Y₄ t₄ cx d hc hK₄ hA₄ hr₄ (by rw [hg₄, hsY, c48, hgY]) ?_
  -- back from `operator new`
  intro Zn V₁ t₅ hKn hAn hrn hns hn13 hnbx hPn
  refine (c_109 prof).run c hin (fun j' g' _ V' => V' = V₁ ∧
      g' = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r14 := Zn.cpu.gpr.rax } ∧
      ((j' = 126 ∧ rdq(V₁, X.cpu.gpr.rdi) = 0) ∨ (j' = 121 ∧ rdq(V₁, X.cpu.gpr.rdi) ≠ 0))) hKn hAn hrn
    (vc_109 hn13 fd0 (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
  rintro j' g fl V₂ ⟨hV₂, rfl, h⟩ U t₆ hKU hAU hrU hgU -
  subst V₂
  rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · -- a null `_chars`: no `delete []`
    exact run126 U _ V₁ Zn.cpu.gpr.rax t₆ hKU hAU hrU hgU hns hn13 hnbx rfl (km0 Zn V₁ hPn h0)
  · -- `delete [] _chars`
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgU]; exact hns
    have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c48]; exact hs6
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_121 _) hinD hD (by decide) hst5 ?_
    rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
    rw [hsU, c48] at hA₅
    refine kd Zn V₁ hPn h0 Y₅ t₇ hK₅ hA₅ hr₅ (by rw [hg₅, hsU, c48, hgU]) ?_
    intro Zd V₃ t₈ hKd hAd hrd hds hd13 hdbx hd14 hPd
    exact run126 Zd Zd.cpu.gpr V₃ Zn.cpu.gpr.rax t₈ hKd hAd hrd rfl hds hd13 hdbx hd14 (km1 Zn Zd V₃ hPd)

end FV7z.Uaw
