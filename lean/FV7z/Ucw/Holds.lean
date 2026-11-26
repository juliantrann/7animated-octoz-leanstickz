import FV7z.Ucw.Cuts
import FV7z.Usl.Code
import FV7z.Usl.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::UString (const wchar_t *s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (s)` at `0x44d480` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `s` in
`rsi`: the length `n` of `s` (the first 0 character; `s[0]` tested at 16, then the loop at 32 from the index 1),
`SetStartLen (n)` (`call` at 55 to `Usl.usl_at`), then a tail jump (73) to `wmemcpy (_chars, s, n + 1)` (`_chars`
the 8 bytes at `this`). `push r12; push rbp; push rbx`, `rbx` = `this`, `rbp` = `s`, `r12` = `n + 1` across the
call, the three popped before the jump.

The callee is a hypothesis (`ku`), as in `FV7z/Uc4/Holds.lean`: a continuation at its entry, given the run from its
return (`rsp` 24 below the entry's, `rbx`, `rbp`, `r12` as the caller left them, the saved registers as they were:
`Sv`) and the callee's own post (`Pu`). From the entry to the `call` a `Seg.cfg` (`FV7z/Utr/Holds.lean`).

- `V0`: the bytes after the pushes (`rdV0`: the same 4 bytes below them); `Wz`: the string at `s` of length `n`,
  its characters readable.
- `I32`, `I52`, `Inv`, `Fin`, `Nx`: the loop's head at the index `k` (measure `n - k + 1`), the end of the count
  (0), the invariant, the `call`, the post of `Seg.cfg`; `gC`: the registers at the `call`.
- `vc_0`, `vc_32`, `vc_52`, `vc_60`: the verification conditions of the pieces.
- `ucw_ok`: from the entry, through `SetStartLen`, to `wmemcpy`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ucw

/-- The `call` to `SetStartLen`. -/
def pcu : List Byte := [0xe8, 0xa4, 0xfb, 0xff, 0xff]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 18446744073709550500] 5) := by dec_rfl
theorem wc_55 : pcu <+: ucw.drop 55 := by decide +kernel
theorem call_55 (feat : Features) : Dec feat ucw 55 (FV7z.mk .call 64 [.rel 18446744073709550500] 5) :=
  Dec.shift (j := 55) (k := 0) (pcu_0 feat) wc_55 (Nat.zero_le _)
theorem tgt_55 : ucw_at.add (55 + 5) + BitVec.ofNat 64 18446744073709550500 = Usl.usl_at.add 0 := by decide

/-- The jump to `wmemcpy`. -/
def pjm : List Byte := [0xe9, 0x32, 0xfe, 0x20, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2162226] 5) := by dec_rfl
theorem wj_73 : pjm <+: ucw.drop 73 := by decide +kernel
theorem jmp_73 (feat : Features) : Dec feat ucw 73 (FV7z.mk .jmp 64 [.rel 2162226] 5) :=
  Dec.shift (j := 73) (k := 0) (pjm_0 feat) wj_73 (Nat.zero_le _)
theorem tgt_73 : ucw_at.add (73 + 5) + BitVec.ofNat 64 2162226 = Wmc.wmc_at.add 0 := by decide

/-! ## Arithmetic -/

/-- `xor esi, esi`. -/
theorem xz (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x) = 0#64 := by
  rw [BitVec.xor_self]
  decide

/-- `lea eax, [rsi + 1]` at the index `k`. -/
theorem sk1 {k : Nat} (hk : k + 1 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k + 1#64)) = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `mov edx, esi; lea r12d, [rdx + 2]` at the index `k`. -/
theorem sk2 {k : Nat} (hk : k + 2 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k)) + 2#64)) =
      BitVec.ofNat 64 (k + 1 + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The address `[rbp + rax * 4]` of the character `k + 1`. -/
theorem ldw (s : Addr) {k : Nat} (hk : k + 1 < 2 ^ 32) :
    s + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k + 1#64)) * 4#64 = Addr.add s (4 * (k + 1)) := by
  rw [sk1 hk]
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-! ## The bytes and the string -/

/-- The bytes after the pushes: `r12`, `rbp`, `rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- Four bytes clear of the pushes read as they were. -/
theorem rdV0 {V : Addr → Byte} {g : Gprs} {a : Addr} (hp : 24 ≤ g.rsp.toNat) (ha : a.toNat + 4 ≤ 2 ^ 64)
    (hd : a.toNat + 4 ≤ g.rsp.toNat - 24 ∨ g.rsp.toNat ≤ a.toNat) : rdd(V0 V g, a) = rdd(V, a) := by
  have hlt := g.rsp.isLt
  have t1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub, t2]; simp <;> omega
  have a1 := Tun.rd_Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) a 4 (by rw [toBytesLE_length, t3]; omega) ha
    (by rw [toBytesLE_length, t3]; omega)
  have a2 := Tun.rd_Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8) a 4
    (by rw [toBytesLE_length, t2]; omega) ha (by rw [toBytesLE_length, t2]; omega)
  have a3 := Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.r12 8) a 4 (by rw [toBytesLE_length, t1]; omega) ha
    (by rw [toBytesLE_length, t1]; omega)
  exact congrArg (ofBytesLE 32) (a1.trans (a2.trans a3))

/-- The string at `s` in the bytes `V`, of length `n`: the character `n` 0, those before it not, all readable. -/
def Wz (F : Footprint) (V : Addr → Byte) (s : Addr) (n : Nat) : Prop :=
  n + 1 < 2 ^ 32 ∧ rdd(V, Addr.add s (4 * n)) = 0 ∧ (∀ i < n, rdd(V, Addr.add s (4 * i)) ≠ 0) ∧
    ∀ i ≤ n, ∀ j < 4, Foot F.data (Addr.add (Addr.add s (4 * i)) j)

/-! ## The invariant -/

/-- The registers at the `call` for the length `n` (`rax`, `rdx` any): `esi` = `n`, `r12` = `n + 1`, `rbp` = `s`,
`rbx` = `rdi` = `this`, 24 below the entry. -/
abbrev gC (g : Gprs) (n : Nat) (a d : BitVec 64) : Gprs :=
  { g with rax := a, rdx := d, rsi := BitVec.ofNat 64 n, r12 := BitVec.ofNat 64 (n + 1), rbp := g.rsi,
           rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8 }

/-- The loop's head at the index `k`: `rsi` = `k`. -/
def I32 (g₀ : Gprs) (k : Nat) (g : Gprs) : Prop :=
  ∃ a d, g = { g₀ with rax := a, rdx := d, rsi := BitVec.ofNat 64 k, rbp := g₀.rsi, rbx := g₀.rdi,
                       rsp := g₀.rsp - 8 - 8 - 8 }

/-- The end of the count. -/
def I52 (g₀ : Gprs) (n : Nat) (g : Gprs) : Prop := ∃ a d, g = gC g₀ n a d

/-- The invariant at the cut points (`VS` the bytes after the pushes). -/
def Inv (g₀ : Gprs) (V₀ VS : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = n + 2 ∧ g = g₀ ∧ V = V₀) ∨ (ℓ = 32 ∧ V = VS ∧ ∃ k, k < n ∧ m = n - k + 1 ∧ I32 g₀ k g) ∨
    (ℓ = 52 ∧ m = 0 ∧ V = VS ∧ I52 g₀ n g)

/-- At the `call`. -/
def Fin (g₀ : Gprs) (VS : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 55 ∧ V = VS ∧ ∃ a d, g = gC g₀ n a d

/-- At an exit: a cut point's invariant with a smaller measure, or the `call`. -/
def Nx (g₀ : Gprs) (V₀ VS : Addr → Byte) (n m : Nat) : Post :=
  fun j' g' _ V' => (∃ m' < m, Inv g₀ V₀ VS n j' m' g' V') ∨ Fin g₀ VS n j' g' V'

variable {g₀ : Gprs} {V₀ VS : Addr → Byte} {n : Nat}

theorem x32 {m k : Nat} (hk : k < n) (hm : n - k + 1 < m) {a d r : BitVec 64} (hr : r = BitVec.ofNat 64 k)
    {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rdx := d, rsi := r, rbp := g₀.rsi, rbx := g₀.rdi, rsp := g₀.rsp - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 32 g fl VS := by
  subst hr hg
  exact Or.inl ⟨n - k + 1, hm, Or.inr (Or.inl ⟨rfl, rfl, k, hk, rfl, a, d, rfl⟩)⟩

theorem x52 {m : Nat} (hm : 0 < m) {a d r q : BitVec 64} (hr : r = BitVec.ofNat 64 n)
    (hq : q = BitVec.ofNat 64 (n + 1)) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rdx := d, rsi := r, r12 := q, rbp := g₀.rsi, rbx := g₀.rdi,
                        rsp := g₀.rsp - 8 - 8 - 8 }) :
    Nx g₀ V₀ VS n m 52 g fl VS := by
  subst hr hq hg
  exact Or.inl ⟨0, hm, Or.inr (Or.inr ⟨rfl, rfl, rfl, a, d, rfl⟩)⟩

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- `push r12; push rbp; mov rbp, rsi; push rbx; mov edx, [rsi]; mov rbx, rdi; test edx, edx; je`: the end of the
count for the length 0 (`mov r12d, 1; xor esi, esi`), else the loop's head at the index 0 (`xor esi, esi`). -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) (hw : Wz F (V0 V g) g.rsi n) :
    W_0 F Wl (Nx g V (V0 V g) n (n + 2)) g f V := by
  obtain ⟨-, hz, hnz, hf⟩ := hw
  have f0 : ∀ j < 4, Foot F.data (Addr.add g.rsi j) := by
    have := hf 0 (Nat.zero_le _)
    rwa [Nat.mul_zero, addr_add_zero] at this
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · have hX : (rdd(V0 V g, g.rsi) == 0) = true := by
      rw [beq_iff_eq]
      have e := hz
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V0] at hs1 hs2 hs3 f0 hX ⊢
    wpx [W_0, W_20, W_80, o0, o1, o6, xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x52 (by omega) (by decide) (by decide) rfl
  · have hX : (rdd(V0 V g, g.rsi) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      have e := hnz 0 hp
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V0] at hs1 hs2 hs3 f0 hX ⊢
    wpx [W_0, W_20, W_80, o0, o1, o6, xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x32 (k := 0) hp (by omega) (by rfl) rfl

set_option maxHeartbeats 2000000 in
/-- The loop's head at the index `k`: `lea eax, [rsi + 1]; mov edx, esi; mov rsi, rax; mov eax, [rbp + rax * 4];
test eax, eax; jne`: the head at `k + 1` for a character not 0, else (`k + 1` = `n`) `lea r12d, [rdx + 2]`. -/
theorem vc_32 {k : Nat} {g : Gprs} {f : Rflags} (hw : Wz F VS g₀.rsi n) (hk : k < n) (h : I32 g₀ k g) :
    W_32 F Wl (Nx g₀ V₀ VS n (n - k + 1)) g f VS := by
  obtain ⟨hn, hz, hnz, hf⟩ := hw
  obtain ⟨a, d, rfl⟩ := h
  have hA := ldw g₀.rsi (k := k) (by omega)
  have fk := hf (k + 1) (by omega)
  have e1 := sk1 (k := k) (by omega)
  by_cases hc : k + 1 = n
  · have e2 := sk2 (k := k) (by omega)
    have hX : (rdd(VS, Addr.add g₀.rsi (4 * (k + 1))) == 0) = true := by
      rw [beq_iff_eq, hc]
      exact hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_48, o2, o3, hA, hX, BitVec.and_self, eq_self_iff_true, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x52 (by omega) (by rw [← hc]; exact e1) (by rw [← hc]; exact e2) rfl
  · have hX : (rdd(VS, Addr.add g₀.rsi (4 * (k + 1))) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact hnz (k + 1) (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_48, o2, o3, hA, hX, BitVec.and_self, eq_self_iff_true, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x32 (k := k + 1) (by omega) (by omega) (by exact e1) rfl

/-- The end of the count: `mov rdi, rbx` to the `call`. -/
theorem vc_52 {g : Gprs} {f : Rflags} (h : I52 g₀ n g) : W_52 F Wl (Nx g₀ V₀ VS n 0) g f VS := by
  obtain ⟨a, d, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [gC]
  wpx [W_52, o4]
  exact Or.inr ⟨rfl, rfl, a, d, rfl⟩

theorem vcAll (hw : Wz F VS g₀.rsi n) (hV : VS = V0 V₀ g₀)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i)) (ℓ m : Nat) (g : Gprs) (f : Rflags)
    (V : Addr → Byte) (h : Inv g₀ V₀ VS n ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ VS n m) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, k, hk, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩ := h
  · subst hV
    exact vc_0 hs1 hs2 hs3 hw
  · exact vc_32 hw hk h
  · exact vc_52 h

/-- The saved `rbx`, `rbp`, `r12` (the entry's `x`) in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) : Prop :=
  rdq(V, x.rsp - 24) = x.rbx ∧ rdq(V, x.rsp - 16) = x.rbp ∧ rdq(V, x.rsp - 8) = x.r12

/-- Back from `SetStartLen`: `mov rdi, [rbx]; mov rdx, r12; pop rbx; mov rsi, rbp; pop rbp; pop r12` to the jump at
73. -/
theorem vc_60 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 73
      { g with
          rdi := rdq(V, p),
          rdx := g.r12,
          rbx := rdq(V, g.rsp),
          rsi := g.rbp,
          rbp := rdq(V, g.rsp + 8),
          r12 := rdq(V, g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl V) :
    W_60 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx fp hl0 hl1 hl2 h ⊢
  subst hbx
  wpx [W_60, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (s)` from its entry, `n` the length of `s` (`Wz`; its characters clear of the pushes). At
`SetStartLen`'s entry the registers are `gC` (`rax`, `rdx` any), `rsp` 32 below the entry's, the bytes `V0` with the
return address pushed (`ku`); back at `ucw_at + 60` (`Sv`, `Pu`), at `wmemcpy`'s entry with `rdi` = `_chars`,
`rsi` = `s`, `rdx` = `n + 1` and the saved registers back (`kr`). -/
theorem ucw_ok {Pu : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ucw_at ucw) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucw_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hw : Wz F V X.cpu.gpr.rsi n)
    (hsd : ∀ i ≤ n, (Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ 2 ^ 64 ∧
      ((Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨
        X.cpu.gpr.rsp.toNat ≤ (Addr.add X.cpu.gpr.rsi (4 * i)).toNat))
    (ku : ∀ (Y : State) (t' : Nat) (a d : BitVec 64), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8)) →
      Y.cpu.rip = Usl.usl_at → Y.cpu.gpr = (gC X.cpu.gpr n a d).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = ucw_at.add 60 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rsi → Z.cpu.gpr.r12 = BitVec.ofNat 64 (n + 1) → Sv V₁ X.cpu.gpr → Pu Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Y : State) (t' : Nat), Pu Z V₁ → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V₁ → Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Z.cpu.gpr with
          rdi := rdq(V₁, X.cpu.gpr.rdi), rdx := BitVec.ofNat 64 (n + 1), rbx := X.cpu.gpr.rbx,
          rsi := X.cpu.gpr.rsi, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have c32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the string as it was before the pushes
  have hw' : Wz F (V0 V X.cpu.gpr) X.cpu.gpr.rsi n := by
    obtain ⟨w1, w2, w3, w4⟩ := hw
    refine ⟨w1, ?_, fun i hi => ?_, w4⟩
    · rw [rdV0 (V := V) (g := X.cpu.gpr) (by omega) (hsd n (Nat.le_refl _)).1 (hsd n (Nat.le_refl _)).2]
      exact w2
    · rw [rdV0 (V := V) (g := X.cpu.gpr) (by omega) (hsd i (by omega)).1 (hsd i (by omega)).2]
      exact w3 i hi
  -- to the `call` of `SetStartLen`
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V (V0 V X.cpu.gpr) n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr (V0 V X.cpu.gpr) n j g V')
    (fun ℓ m g f V' h => vcAll hw' rfl hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) ℓ m g f V' h) ?_
    (n + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V₁ ⟨rfl, rfl, a, d, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_55 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_55 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr n a d).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hsY, c32, hgY]
  refine ku Y₂ t₂ a d hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `SetStartLen`
  intro Z V₂ t₃ hKZ hAZ hrZ hzs hzb hzp hz12 hsv hPu
  obtain ⟨hb1, hb2, hb3⟩ := hsv
  refine (c_60 prof).run c hin (fun j' g' _ V' => j' = 73 ∧
      g' = { Z.cpu.gpr with
          rdi := rdq(V₂, X.cpu.gpr.rdi), rdx := BitVec.ofNat 64 (n + 1), rbx := X.cpu.gpr.rbx,
          rsi := X.cpu.gpr.rsi, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp } ∧ V' = V₂)
    hKZ hAZ hrZ
    (vc_60 hzb fd0 (by rw [hzs]; exact h24) (by rw [hzs, a16]; exact h16) (by rw [hzs, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hzs, a16, a8, e8, hb1, hb2, hb3, hz12, hzp], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ U t₄ hKU hAU hrU hgU -
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_73 _) hinW (Wmc.lt_len (j := 0) (by decide))
    tgt_73 ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  exact kr Z _ Y₅ t₅ hPu hK₅ hA₅ (by rw [hr₅, addr_add_zero]) (by rw [hg₅, hgU])

end FV7z.Ucw
