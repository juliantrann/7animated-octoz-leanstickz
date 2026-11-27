import FV7z.Uca.Cuts
import FV7z.Usl.Blocks1
import FV7z.Ucw.Holds
import FV7z.Usf.Holds
import FV7z.Mys.Lem
/-!
# `UString::UString (const char *)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (const char *s)` at `0x44d4e0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in
`rdi`, `s` in `rsi`: `push r14; mov r14, rdi; push r13; push r12; push rbp; push rbx`, then `cmp byte [rsi], 0`. For
`s[0] = 0` (18) `xor esi, esi` and the `call` of `SetStartLen` (`Usl.usl_at`) at 130, then `mov r12, [r14]` and the
jump to 103. Else (20) `rbp` = `s`, `ebx` = 0 and the length loop at 32 (`lea r12d, [rbx + 1]; mov r13d, ebx;
cmp byte [rbp + r12], 0; mov rbx, r12; jne 32`), then (50) `esi` = `n`, `shl r12, 2` and the `call` at 60; back at
65 `rcx` = `_chars`, `eax` = 0 and the copy loop at 80 (`movzx edx, byte [rbp + rax]; mov [rcx + rax * 4], edx;
mov rdx, rax; add rax, 1; cmp r13, rdx; jne 80`), `r12` = `_chars + 4 n` (100). At 103 `mov dword [r12], 0`, the
pops and the `ret` at 119.

The callee is a hypothesis, as in `FV7z/Uaw/Holds.lean`: a continuation at its entry (`Kc`) given the run from its
return with the registers `Kp` keeps, the saved ones (`Sv5`) and its post `Pu`; `kr` at the return address. From the
entry to a `call` a `Seg.cfg` (the length loop's head at the index `k`, measure `n - k + 1`).

- `Bz`: `n` bytes not 0 and a 0 at `s`, readable; `gC`, `gZ`: the registers at the `call`s at 60 and 130.
- `I32`, `Inv`, `Fin`, `Nx`: the loop's head, the invariant, the exits, the post of `Seg.cfg`.
- `vc_0`, `vc_32`, `vc_65`, `vc_80n`, `vc_80z`, `vc_100`, `vc_103`, `vc_135`: the pieces.
- `Cw`, `Mf`: the bytes after `k` characters copied and after the final 0; `loop`: the copy loop by induction.
- `uca_ok`: from the entry, through the callee, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Uca
open FV7z.Usf (V5 Sv5 m5)

/-- The `call`s of `SetStartLen`. -/
def pc1 : List Byte := [0xe8, 0x3f, 0xfb, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709550399] 5) := by dec_rfl
theorem wc_60 : pc1 <+: uca.drop 60 := by decide +kernel
theorem call_60 (feat : Features) : Dec feat uca 60 (FV7z.mk .call 64 [.rel 18446744073709550399] 5) :=
  Dec.shift (j := 60) (k := 0) (pc1_0 feat) wc_60 (Nat.zero_le _)
theorem tgt_60 : uca_at.add (60 + 5) + BitVec.ofNat 64 18446744073709550399 = Usl.usl_at.add 0 := by decide
def pc2 : List Byte := [0xe8, 0xf9, 0xfa, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709550329] 5) := by dec_rfl
theorem wc_130 : pc2 <+: uca.drop 130 := by decide +kernel
theorem call_130 (feat : Features) : Dec feat uca 130 (FV7z.mk .call 64 [.rel 18446744073709550329] 5) :=
  Dec.shift (j := 130) (k := 0) (pc2_0 feat) wc_130 (Nat.zero_le _)
theorem tgt_130 : uca_at.add (130 + 5) + BitVec.ofNat 64 18446744073709550329 = Usl.usl_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_119 : pret <+: uca.drop 119 := by decide +kernel
theorem ret_119 (feat : Features) : Dec feat uca 119 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 119) (k := 0) (pret_0 feat) w_119 (Nat.zero_le _)

/-- An equation of 64-bit values by their numbers. -/
macro "uca_tn" : tactic => `(tactic| (apply BitVec.eq_of_toNat_eq;
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_mul, Nat.reducePow, Nat.reduceMod]; omega))

/-! ## The invariant -/

/-- `n` bytes not 0 and a 0 at `s`, readable. -/
def Bz (F : Footprint) (V : Addr → Byte) (s : Addr) (n : Nat) : Prop :=
  n < 2 ^ 32 ∧ V (Addr.add s n) = 0#8 ∧ (∀ i < n, V (Addr.add s i) ≠ 0#8) ∧ ∀ i ≤ n, Foot F.data (Addr.add s i)

/-- The registers at the `call` at 60: `rbx` = `esi` = `n`, `rbp` = `s`, `r12` = `4 n`, `r13` = `n - 1`, `r14` =
`this`, 40 below the entry. -/
abbrev gC (g : Gprs) (n : Nat) : Gprs :=
  { g with rbx := BitVec.ofNat 64 n, rbp := g.rsi, rsi := BitVec.ofNat 64 n, r12 := BitVec.ofNat 64 (4 * n),
           r13 := BitVec.ofNat 64 (n - 1), r14 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The registers at the `call` at 130: `esi` = 0, `r14` = `this`. -/
abbrev gZ (g : Gprs) : Gprs := { g with rsi := 0#64, r14 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The length loop's head at the index `k`: `rbx` = `k`. -/
def I32 (g₀ : Gprs) (k : Nat) (g : Gprs) : Prop :=
  ∃ q r, g = { g₀ with rbx := BitVec.ofNat 64 k, rbp := g₀.rsi, r12 := q, r13 := r, r14 := g₀.rdi,
                       rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The invariant at the cut points (`VS` the bytes after the pushes). -/
def Inv (g₀ : Gprs) (V₀ VS : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = n + 2 ∧ g = g₀ ∧ V = V₀) ∨ (ℓ = 32 ∧ V = VS ∧ ∃ k, k < n ∧ m = n - k + 1 ∧ I32 g₀ k g)

/-- The exits: the `call` at 60 (`n > 0`), the one at 130 (`n = 0`). -/
def Fin (g₀ : Gprs) (VS : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = VS ∧ ((j = 60 ∧ 0 < n ∧ g = gC g₀ n) ∨ (j = 130 ∧ n = 0 ∧ g = gZ g₀))

/-- At an exit: a cut point's invariant with a smaller measure, or `Fin`. -/
def Nx (g₀ : Gprs) (V₀ VS : Addr → Byte) (n m : Nat) : Post :=
  fun j' g' _ V' => (∃ m' < m, Inv g₀ V₀ VS n j' m' g' V') ∨ Fin g₀ VS n j' g' V'

section
variable {g₀ : Gprs} {V₀ VS : Addr → Byte} {n : Nat}

theorem x32 {m k : Nat} (hk : k < n) (hm : n - k + 1 < m) {b q r : BitVec 64} (hb : b = BitVec.ofNat 64 k)
    {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rbx := b, rbp := g₀.rsi, r12 := q, r13 := r, r14 := g₀.rdi,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 32 g fl VS := by
  subst hb hg
  exact Or.inl ⟨n - k + 1, hm, Or.inr ⟨rfl, rfl, k, hk, rfl, q, r, rfl⟩⟩

theorem x60 {m : Nat} (hn : 0 < n) {b si q r : BitVec 64} (hb : b = BitVec.ofNat 64 n)
    (hsi : si = BitVec.ofNat 64 n) (hq : q = BitVec.ofNat 64 (4 * n)) (hr : r = BitVec.ofNat 64 (n - 1))
    {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rbx := b, rbp := g₀.rsi, rsi := si, r12 := q, r13 := r, r14 := g₀.rdi,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 60 g fl VS := by
  subst hb hsi hq hr hg
  exact Or.inr ⟨rfl, .inl ⟨rfl, hn, rfl⟩⟩

theorem x130 {m : Nat} (hn : n = 0) {si : BitVec 64} (hsi : si = 0#64) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rsi := si, r14 := g₀.rdi, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 130 g fl VS := by
  subst hsi hg
  exact Or.inr ⟨rfl, .inr ⟨rfl, hn, rfl⟩⟩

end

/-- The address `[rbp + r12]` of the byte `k + 1`. -/
theorem lb (s : Addr) {k : Nat} (hk : k + 1 < 2 ^ 32) :
    s + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k + 1#64)) = Addr.add s (k + 1) := by
  rw [Ucw.sk1 hk]
  rfl

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

section
variable {g₀ : Gprs} {V₀ VS : Addr → Byte} {n : Nat}

set_option maxHeartbeats 1000000 in
/-- The pushes, `mov r14, rdi; cmp byte [rsi], 0; je`: for the length 0 `xor esi, esi` to the `call` at 130, else
`mov rbp, rsi; xor ebx, ebx` to the loop's head at the index 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) (hw : Bz F (V5 V g) g.rsi n) :
    W_0 F Wl (Nx g V (V5 V g) n (n + 2)) g f V := by
  obtain ⟨-, hz, hnz, hf⟩ := hw
  have f0 : ∀ j < 1, Foot F.data (Addr.add g.rsi j) := fun j hj => by
    obtain rfl : j = 0 := by omega
    exact hf 0 (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · have hX : V5 V g g.rsi = 0#8 := by
      have e := hz
      rwa [addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V5] at hs1 hs2 hs3 hs4 hs5 f0 hX ⊢
    wpx [W_0, W_128, W_20, o0, o1, o9, Op.cmpmi, Tun.rd1, BitVec.sub_zero, Ucw.xz, hX, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true, eq_self_iff_true, and_self, and_true, true_and]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x130 rfl (by rfl) rfl
  · have hX : V5 V g g.rsi ≠ 0#8 := by
      have e := hnz 0 hp
      rwa [addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V5] at hs1 hs2 hs3 hs4 hs5 f0 hX ⊢
    wpx [W_0, W_128, W_20, o0, o1, o9, Op.cmpmi, Tun.rd1, BitVec.sub_zero, Ucw.xz, hX, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true, eq_self_iff_true, and_self, and_true, true_and]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x32 (k := 0) hp (by omega) (by rfl) rfl

set_option maxHeartbeats 2000000 in
/-- The loop's head at the index `k`: `lea r12d, [rbx + 1]; mov r13d, ebx; cmp byte [rbp + r12], 0; mov rbx, r12;
jne`: the head at `k + 1` for a byte not 0, else (`k + 1` = `n`) `mov esi, r12d; mov rdi, r14; shl r12, 2` to the
`call` at 60. -/
theorem vc_32 {k : Nat} {g : Gprs} {f : Rflags} (hw : Bz F VS g₀.rsi n) (hk : k < n) (h : I32 g₀ k g) :
    W_32 F Wl (Nx g₀ V₀ VS n (n - k + 1)) g f VS := by
  obtain ⟨hn, hz, hnz, hf⟩ := hw
  obtain ⟨q, r, rfl⟩ := h
  have hA := lb g₀.rsi (k := k) (by omega)
  have fk : ∀ j < 1, Foot F.data (Addr.add (Addr.add g₀.rsi (k + 1)) j) := fun j hj => by
    obtain rfl : j = 0 := by omega
    rw [addr_add_zero]
    exact hf (k + 1) (by omega)
  have e1 := Ucw.sk1 (k := k) (by omega)
  by_cases hc : k + 1 = n
  · have hX : VS (Addr.add g₀.rsi (k + 1)) = 0#8 := by rw [hc]; exact hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_50, o2, o3, Op.cmpmi, Op.shl64, Tun.rd1, BitVec.sub_zero, hA, hX, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true, eq_self_iff_true, and_self, and_true, true_and]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x60 (by omega) (by uca_tn) (by uca_tn) (by uca_tn) (by uca_tn) rfl
  · have hX : VS (Addr.add g₀.rsi (k + 1)) ≠ 0#8 := hnz (k + 1) (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_50, o2, o3, Op.cmpmi, Op.shl64, Tun.rd1, BitVec.sub_zero, hA, hX, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
      implies_true, eq_self_iff_true, and_self, and_true, true_and]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x32 (k := k + 1) (by omega) (by omega) (by exact e1) rfl

theorem vcAll (hw : Bz F VS g₀.rsi n) (hV : VS = V5 V₀ g₀)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i))
    (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ VS n ℓ m g V) :
    Wt ℓ F Wl (Nx g₀ V₀ VS n m) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, k, hk, rfl, h⟩ := h
  · subst hV
    exact vc_0 hs1 hs2 hs3 hs4 hs5 hw
  · exact vc_32 hw hk h

end

/-- Back from `SetStartLen`: `mov rcx, [r14]; test ebx, ebx; je 100` (not taken, `n > 0`), `xor eax, eax` to 80. -/
theorem vc_65 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} {n : Nat} (h14 : g.r14 = p)
    (hb : g.rbx = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32) (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h : ∀ fl, Q 80 { g with rcx := rdq(V, p), rax := 0#64 } fl V) :
    W_65 F Wl Q g f V := by
  have hX : (BitVec.setWidth 32 g.rbx == 0) = false := by
    rw [beq_eq_false_iff_ne, hb]
    intro e
    have := congrArg BitVec.toNat e
    simp at this <;> omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h14 hX f0 h ⊢
  subst h14
  wpx [W_65, W_72, o4, o5, Ucw.xz, BitVec.and_self, hX, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- The copy loop at the index `rax` short of the last (`r13`): the byte stored as 4, `rax` one on, back to 80. -/
theorem vc_80n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hX : g.r13 ≠ g.rax)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rax) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rcx + g.rax * 4#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 80 ∧ g'.rax = g.rax + 1#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V (g.rcx + g.rax * 4#64) (toBytesLE (BitVec.setWidth 32 (V (g.rbp + g.rax))) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hX hf hw ⊢
  have hX' : rax ≠ r13 := fun e => hX e.symm
  wpx [W_80, o6, Tun.rd1, hX, hX', Kp, decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

set_option maxHeartbeats 1000000 in
/-- The copy loop at the last index (`rax` = `r13`): the byte stored as 4, on to 100. -/
theorem vc_80z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hX : g.r13 = g.rax)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rax) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rcx + g.rax * 4#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 100 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V (g.rcx + g.rax * 4#64) (toBytesLE (BitVec.setWidth 32 (V (g.rbp + g.rax))) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hX hf hw ⊢
  subst hX
  wpx [W_80, o6, Tun.rd1, Kp, decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

/-- `add r12, rcx` to 103. -/
theorem vc_100 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 103 { g with r12 := g.r12 + g.rcx } fl V) : W_100 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_100, o7]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- `mov dword [r12], 0; pop rbx; pop rbp; pop r12; pop r13; pop r14` to the `ret` at 119. -/
theorem vc_103 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (h12 : g.r12 = p)
    (hw : ∀ i < 4, Foot Wl (Addr.add p i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 119
      { g with
          rbx := rdq(Vst V p (toBytesLE 0#32 4), g.rsp),
          rbp := rdq(Vst V p (toBytesLE 0#32 4), g.rsp + 8),
          r12 := rdq(Vst V p (toBytesLE 0#32 4), g.rsp + 8 + 8),
          r13 := rdq(Vst V p (toBytesLE 0#32 4), g.rsp + 8 + 8 + 8),
          r14 := rdq(Vst V p (toBytesLE 0#32 4), g.rsp + 8 + 8 + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 + 8 + 8 } fl (Vst V p (toBytesLE 0#32 4))) :
    W_103 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 hw hl0 hl1 hl2 hl3 hl4 h ⊢
  subst h12
  wpx [W_103, o8]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `SetStartLen` for the length 0: `mov r12, [r14]` and the jump to 103. -/
theorem vc_135 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (h14 : g.r14 = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (h : ∀ fl, Q 103 { g with r12 := rdq(V, p) } fl V) :
    W_135 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h14 f0 h ⊢
  subst h14
  wpx [W_135, o10]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The copy -/

/-- The bytes after the first `k` bytes at `s` stored as 4 each at `d`. -/
def Cw (W : Addr → Byte) (s d : Addr) : Nat → Addr → Byte
  | 0 => W
  | k + 1 => Vst (Cw W s d k) (Addr.add d (4 * k)) (toBytesLE (BitVec.setWidth 32 (Cw W s d k (Addr.add s k))) 4)

theorem Cw_zero (W : Addr → Byte) (s d : Addr) : Cw W s d 0 = W := rfl

/-- A byte not among the first `4 k` at `d`: as it was. -/
theorem Cw_out (W : Addr → Byte) (s d : Addr) :
    ∀ (k : Nat) (x : Addr), (∀ i < 4 * k, x ≠ d.add i) → Cw W s d k x = W x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    show Vst (Cw W s d k) (Addr.add d (4 * k)) (toBytesLE (BitVec.setWidth 32 (Cw W s d k (Addr.add s k))) 4) x =
      W x
    rw [Vst_apart (toBytesLE (BitVec.setWidth 32 (Cw W s d k (Addr.add s k))) 4) (Cw W s d k) (Addr.add d (4 * k)) x
      fun i hi => by
        rw [addr_add_add]
        exact h (4 * k + i) (by rw [toBytesLE_length] at hi; omega)]
    exact Cw_out W s d k x fun i hi => h i (by omega)

/-- The bytes at the end: the copy and the 4 bytes 0 after it. -/
abbrev Mf (W : Addr → Byte) (s d : Addr) (n : Nat) : Addr → Byte :=
  Vst (Cw W s d n) (Addr.add d (4 * n)) (toBytesLE 0#32 4)

/-- 8 bytes apart from the `4 n + 4` at `d`: as they were. -/
theorem rdMf (W : Addr → Byte) (s d : Addr) (n : Nat) (a : Addr) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hd : d.toNat + (4 * n + 4) ≤ 2 ^ 64) (h : d.toNat + (4 * n + 4) ≤ a.toNat ∨ a.toNat + 8 ≤ d.toNat) :
    rdq(Mf W s d n, a) = rdq(W, a) := by
  have hne : ∀ b < 8, ∀ i < 4 * n + 4, a.add b ≠ d.add i := fun b hb i hi e => by
    have := congrArg BitVec.toNat e
    rw [toNat_add_of_fits hb ha, toNat_add_of_fits hi hd] at this
    omega
  show ofBytesLE 64 (List.map (Mf W s d n) (byteAddrs a 8)) = ofBytesLE 64 (List.map W (byteAddrs a 8))
  congr 1
  refine List.map_congr_left fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := mem_byteAddrs.1 hy
  show Vst (Cw W s d n) (Addr.add d (4 * n)) (toBytesLE 0#32 4) (a.add b) = W (a.add b)
  rw [Vst_apart (toBytesLE 0#32 4) (Cw W s d n) (Addr.add d (4 * n)) (a.add b) fun i hi => by
    rw [addr_add_add]
    exact hne b hb (4 * n + i) (by rw [toBytesLE_length] at hi; omega)]
  exact Cw_out W s d n _ fun i hi => hne b hb i (by omega)

/-- The `4 n + 4` bytes at `d` writable and clear of the saved registers and the return address (`x` the entry's). -/
abbrev Dst (Wl : List Rgn) (x : Gprs) (n : Nat) (d : Addr) : Prop :=
  (∀ i < 4 * n + 4, Foot Wl (Addr.add d i)) ∧ d.toNat + (4 * n + 4) ≤ 2 ^ 64 ∧
    (d.toNat + (4 * n + 4) ≤ x.rsp.toNat - 40 ∨ x.rsp.toNat + 8 ≤ d.toNat)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The copy loop from 80 at the index `j` (`j + 1 ≤ n`) of the `n` bytes at `s` (`rbp`) to `d` (`rcx`), `r13` =
`n - 1`: on to 100 with all `n` stored and the registers `Kp` keeps as at `g₀`. By induction on `n - j - 1`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uca_at uca) {W : Addr → Byte} {s d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hf : ∀ i ≤ n, Foot F.data (Addr.add s i))
    (hw : ∀ i < 4 * n + 4, Foot Wl (Addr.add d i)) (hp : g₀.rbp = s) (h13 : g₀.r13 = BitVec.ofNat 64 (n - 1))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cw W s d n) →
      Z.cpu.rip = uca_at.add 100 → Z.cpu.gpr.rcx = d → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Cw W s d j) → X.cpu.rip = uca_at.add 80 → X.cpu.gpr.rax = BitVec.ofNat 64 j →
      X.cpu.gpr.rcx = d → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hkp
    obtain rfl : n = j + 1 := by omega
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rax = Addr.add s j := by rw [hkp.2.2.1, hp, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax * 4#64 = Addr.add d (4 * j) := by
      rw [hcx, hax]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hX : X.cpu.gpr.r13 = X.cpu.gpr.rax := by
      rw [hkp.2.2.2.2.1, h13, hax]
      congr 1
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax * 4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80z hX hf1 hw4) ?_
    rintro j' g fl V₁ ⟨rfl, hcx', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    exact k Y t₁ hKY hAY hrY (by rw [hgY, hcx', hcx]) (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hkp
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rax = Addr.add s j := by rw [hkp.2.2.1, hp, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax * 4#64 = Addr.add d (4 * j) := by
      rw [hcx, hax]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hX : X.cpu.gpr.r13 ≠ X.cpu.gpr.rax := by
      rw [hkp.2.2.2.2.1, h13, hax]
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax * 4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80n hX hf1 hw4) ?_
    rintro j' g fl V₁ ⟨rfl, hax', hcx', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hcx', hcx]) (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hax', hax]
    exact (BitVec.ofNat_add j 1).symm

/-! ## From the entry to the return address -/

/-- At `SetStartLen`'s entry from the `call` with the registers `G` and the bytes `W` there (`x` the entry's
registers, `r` the return address, `ret` the `call`'s): `rsp` 48 below the entry's, `ret` pushed; back at `ret` with
the registers `Kp` keeps as in `G`, the saved ones and `r` (`Sv5`) and the callee's post `Pu`. -/
def Kc (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (x : Gprs) (r : Addr) (Pu : State → (Addr → Byte) → Prop) (G : Gprs) (W : Addr → Byte)
    (ret : Addr) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst W (x.rsp - 48) (toBytesLE ret 8)) →
    Y.cpu.rip = Usl.usl_at → Y.cpu.gpr = G.set 4 (x.rsp - 48) →
    (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
      Z.cpu.rip = ret → Kp G Z.cpu.gpr → Sv5 V₁ x r → Pu Z V₁ → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

variable {X : State} {t : Nat} {V : Addr → Byte} {n : Nat}

set_option maxHeartbeats 1000000 in
/-- `UString::UString (s)` (`this` = `rdi`, `s` = `rsi`) from its entry, `n` the length of `s` (`Bz`; its bytes
clear of the pushes): at `SetStartLen`'s entry with the registers `gC` (`n > 0`, `ku1`) or `gZ` (`n = 0`, `ku0`),
back with `_chars` (the 8 bytes at `this`) writable for `4 n + 4` bytes (`hPu`: `Dst`), at the return address with
the bytes `Mf` (the `n` bytes of `s` as 4 each and the 0 after them at `_chars`) and the registers `Str.Back` keeps
(`kr`). -/
theorem uca_ok {Pu : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uca_at uca) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uca_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hw : Bz F V X.cpu.gpr.rsi n) (hsd : X.cpu.gpr.rsi.toNat + (n + 1) ≤ 2 ^ 64)
    (hsd' : X.cpu.gpr.rsi.toNat + (n + 1) ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ku1 : 0 < n → Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) Pu (gC X.cpu.gpr n) (V5 V X.cpu.gpr)
      (uca_at.add 65))
    (ku0 : n = 0 → Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) Pu (gZ X.cpu.gpr) (V5 V X.cpu.gpr)
      (uca_at.add 135))
    (hPu : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → Dst Wl X.cpu.gpr n (rdq(V₁, X.cpu.gpr.rdi)))
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), Pu Z V₁ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Mf V₁ X.cpu.gpr.rsi (rdq(V₁, X.cpu.gpr.rdi)) n) → Z'.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
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
  -- the saved registers and the return address after the copy
  have svM : ∀ (W : Addr → Byte) (d : Addr), d.toNat + (4 * n + 4) ≤ 2 ^ 64 →
      (d.toNat + (4 * n + 4) ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ d.toNat) →
      Sv5 W X.cpu.gpr (e₂.add j₂) → Sv5 (Mf W X.cpu.gpr.rsi d n) X.cpu.gpr (e₂.add j₂) := by
    intro W d hdt hds ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (rdMf W _ d n (X.cpu.gpr.rsp - 40) (by rw [tn40]; omega) hdt (by rw [tn40]; omega)).trans b1
    · exact (rdMf W _ d n (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) hdt (by rw [tn32]; omega)).trans b2
    · exact (rdMf W _ d n (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) hdt (by rw [tn24]; omega)).trans b3
    · exact (rdMf W _ d n (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) hdt (by rw [tn16]; omega)).trans b4
    · exact (rdMf W _ d n (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) hdt (by rw [tn8]; omega)).trans b5
    · exact (rdMf W _ d n X.cpu.gpr.rsp hp8 hdt (by omega)).trans b6
  -- from 103 (the final 0, the pops) to the return address
  have fin : ∀ (U : State) (V₁ : Addr → Byte) (d : Addr) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem (Cw V₁ X.cpu.gpr.rsi d n) → U.cpu.rip = uca_at.add 103 →
      U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.r12 = Addr.add d (4 * n) → U.cpu.gpr.r15 = X.cpu.gpr.r15 →
      Dst Wl X.cpu.gpr n d → Sv5 V₁ X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Mf V₁ X.cpu.gpr.rsi d n) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U V₁ d t' hKU hAU hrU hs h12 h15 hD hsv k
    obtain ⟨hdw, hdt, hds⟩ := hD
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := svM V₁ d hdt hds hsv
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (Addr.add d (4 * n)) i) := fun i hi => by
      rw [addr_add_add]
      exact hdw _ (by omega)
    refine (c_103 prof).run c hin (fun j' g' _ V' => j' = 119 ∧
        g' = { U.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, r14 := X.cpu.gpr.r14, rsp := X.cpu.gpr.rsp } ∧ V' = Mf V₁ X.cpu.gpr.rsi d n)
      hKU hAU hrU
      (vc_103 h12 hw4 (by rw [hs]; exact h40) (by rw [hs, a40]; exact h32) (by rw [hs, a40, a32]; exact h24)
        (by rw [hs, a40, a32, a24]; exact h16) (by rw [hs, a40, a32, a24, a16]; exact h8)
        fun _ => ⟨rfl, by rw [hs, a40, a32, a24, a16, a8, hb1, hb2, hb3, hb4, hb5], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hkp : Kp X.cpu.gpr U'.cpu.gpr := by
      rw [hgU']
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h15⟩
    exact ret_back c hin (lt_len (by decide)) (ret_119 _) hKU' hAU' hrU' hkp hl hin₂ h₂ hb6
      fun Z' t'' hK' hA' hr' hB _ => k Z' t'' hK' hA' hr' hB
  -- the string as it was before the pushes
  have rd0 : ∀ i ≤ n, V5 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
    have ht : (Addr.add X.cpu.gpr.rsi i).toNat = X.cpu.gpr.rsi.toNat + i :=
      toNat_add_of_fits (n := n + 1) (by omega) hsd
    have e := congrArg (ofBytesLE 8) (m5 (V := V) (g := X.cpu.gpr) (by omega) (Addr.add X.cpu.gpr.rsi i) 1
      (by omega) (by omega))
    rwa [Tun.rd1, Tun.rd1] at e
  have hw' : Bz F (V5 V X.cpu.gpr) X.cpu.gpr.rsi n := by
    obtain ⟨w1, w2, w3, w4⟩ := hw
    refine ⟨w1, ?_, fun i hi => ?_, w4⟩
    · rw [rd0 n (Nat.le_refl _)]
      exact w2
    · rw [rd0 i (by omega)]
      exact w3 i hi
  -- the count, to a `call`
  refine c.cfg hin (fun ℓ => spAll prof ℓ)
    (fun ℓ m g _ V' => Inv X.cpu.gpr V (V5 V X.cpu.gpr) n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr (V5 V X.cpu.gpr) n j g V')
    (fun ℓ m g f V' h => vcAll hw' rfl hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)
      (by rw [e32]; exact hs4) (by rw [e40]; exact hs5) ℓ m g f V' h) ?_
    (n + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V₁ ⟨rfl, ⟨rfl, hn0, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ Y t₁ hKY hAY hrY hgY -
  · -- `SetStartLen (n)`, the copy
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_60 _) hinU (tgt := 0) (Usl.lt_len (by decide))
      tgt_60 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine ku1 hn0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
    intro Z V₂ t₃ hKZ hAZ hrZ hkZ hsv hPZ
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hkZ
    have hD := hPu Z V₂ hPZ
    refine (c_65 prof).run c hin (fun j' g' _ V' => j' = 80 ∧
        g' = { Z.cpu.gpr with rcx := rdq(V₂, X.cpu.gpr.rdi), rax := 0#64 } ∧ V' = V₂) hKZ hAZ hrZ
      (vc_65 (p := X.cpu.gpr.rdi) k6 k2 hn0 hw.1 fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ U t₄ hKU hAU hrU hgU -
    refine loop c hin (W := V₂) (s := X.cpu.gpr.rsi) (d := rdq(V₂, X.cpu.gpr.rdi)) (g₀ := Z.cpu.gpr) hw.1
      hw.2.2.2 hD.1 k3 k5 ?_ (n - 1) 0 (by omega) U t₄ hKU (by rw [Cw_zero]; exact hAU) hrU (by rw [hgU])
      (by rw [hgU]) (kp_w hgU)
    intro Z₁ t₅ hK₅ hA₅ hr₅ hcx₅ hkp₅
    refine (c_100 prof).run c hin (fun j' g' _ V' => j' = 103 ∧
        g' = { Z₁.cpu.gpr with r12 := Z₁.cpu.gpr.r12 + Z₁.cpu.gpr.rcx } ∧
        V' = Cw V₂ X.cpu.gpr.rsi (rdq(V₂, X.cpu.gpr.rdi)) n) hK₅ hA₅ hr₅ (vc_100 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
    refine fin U₂ V₂ (rdq(V₂, X.cpu.gpr.rdi)) t₆ hKU₂ hAU₂ hrU₂ ?_ ?_ ?_ hD hsv
      fun Z' t'' hK' hA' hr' hB => kr Z V₂ Z' t'' hPZ hK' hA' hr' hB
    · rw [hgU₂]
      exact hkp₅.1.trans (k1.trans e40)
    · rw [hgU₂]
      show Z₁.cpu.gpr.r12 + Z₁.cpu.gpr.rcx = _
      rw [hkp₅.2.2.2.1, k4, hcx₅, BitVec.add_comm]
      try rfl
    · rw [hgU₂]
      exact hkp₅.2.2.2.2.2.2.trans k7
  · -- `SetStartLen (0)`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_130 _) hinU (tgt := 0) (Usl.lt_len (by decide))
      tgt_130 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine ku0 rfl Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
    intro Z V₂ t₃ hKZ hAZ hrZ hkZ hsv hPZ
    obtain ⟨k1, -, -, -, -, k6, k7⟩ := hkZ
    refine (c_135 prof).run c hin (fun j' g' _ V' => j' = 103 ∧
        g' = { Z.cpu.gpr with r12 := rdq(V₂, X.cpu.gpr.rdi) } ∧ V' = V₂) hKZ hAZ hrZ
      (vc_135 (p := X.cpu.gpr.rdi) k6 fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ U t₄ hKU hAU hrU hgU -
    refine fin U V₂ (rdq(V₂, X.cpu.gpr.rdi)) t₄ hKU (by rw [Cw_zero]; exact hAU) hrU ?_ ?_ ?_ (hPu Z V₂ hPZ) hsv
      fun Z' t'' hK' hA' hr' hB => kr Z V₂ Z' t'' hPZ hK' hA' hr' hB
    · rw [hgU]
      exact k1.trans e40
    · rw [hgU, Nat.mul_zero, addr_add_zero]
    · rw [hgU]
      exact k7

end FV7z.Uca
