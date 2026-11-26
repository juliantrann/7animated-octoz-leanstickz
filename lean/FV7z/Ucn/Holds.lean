import FV7z.Ucn.Cuts
import FV7z.Ucw.Holds
import FV7z.Uau.Holds
/-!
# `UString::UString (unsigned num, const wchar_t *s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (num, s)` at `0x44d1c0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`num` in `esi`, `s` in `rdx`: the length `n` of `s` (`s[0]` tested at 22, then the loop at 32 from the index 1),
`m = min (num, n)` (`cmova` at 48), `SetStartLen (m)` (`call` at 65 to `Usl.usl_at`), `wmemcpy (_chars, s, m)`
(`call` at 79 to `Wmc.wmc_at`), `_chars[m] = 0` (87) and the `ret` at 105. `push r13; push r12; push rbp;
push rbx; sub rsp, 8`, `rbx` = `this`, `rbp` = `s`, `r12` = `m`, `r13` = `4 m` across the calls.

The callees are hypotheses, as in `FV7z/Uau/Holds.lean`: a continuation at each entry (`ku`, `kw`), given the run
from its return and the callee's own post (`Pu`, `Pw`); `kr` at the return address. From the entry to the first
`call` a `Seg.cfg` (`FV7z/Ucw/Holds.lean`). The bytes after the pushes, `Sv` and their loads are those of
`FV7z/Uau/Holds.lean` (the same pushes); the string is `Ucw.Wz`.

- `cmv`: what `cmp esi, eax; cmova esi, eax` leaves, the smaller of `num` and `n`.
- `gJ`: the registers at 62 for `m` = `c` (`rax`, `rcx`, `rdx` any).
- `I32`, `I62`, `Inv`, `Fin`, `Nx`: the loop's head at the index `k` (measure `n - k + 1`), the join (0), the
  invariant, the `call`, the post of `Seg.cfg`.
- `vc_0`, `vc_32`, `vc_62`, `vc_70`, `vc_84`: the verification conditions of the pieces.
- `ucn_ok`: from the entry, through `SetStartLen` and `wmemcpy`, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ucn
open FV7z.Uau (V0 Sv zl m0)

/-- The `call`s to `SetStartLen` and `wmemcpy`. -/
def pcu : List Byte := [0xe8, 0x5a, 0xfe, 0xff, 0xff]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 18446744073709551194] 5) := by dec_rfl
theorem wc_65 : pcu <+: ucn.drop 65 := by decide +kernel
theorem call_65 (feat : Features) : Dec feat ucn 65 (FV7z.mk .call 64 [.rel 18446744073709551194] 5) :=
  Dec.shift (j := 65) (k := 0) (pcu_0 feat) wc_65 (Nat.zero_le _)
theorem tgt_65 : ucn_at.add (65 + 5) + BitVec.ofNat 64 18446744073709551194 = Usl.usl_at.add 0 := by decide
def pcw : List Byte := [0xe8, 0xec, 0x00, 0x21, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2162924] 5) := by dec_rfl
theorem wc_79 : pcw <+: ucn.drop 79 := by decide +kernel
theorem call_79 (feat : Features) : Dec feat ucn 79 (FV7z.mk .call 64 [.rel 2162924] 5) :=
  Dec.shift (j := 79) (k := 0) (pcw_0 feat) wc_79 (Nat.zero_le _)
theorem tgt_79 : ucn_at.add (79 + 5) + BitVec.ofNat 64 2162924 = Wmc.wmc_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_105 : pret <+: ucn.drop 105 := by decide +kernel
theorem ret_105 (feat : Features) : Dec feat ucn 105 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 105) (k := 0) (pret_0 feat) w_105 (Nat.zero_le _)

/-! ## Arithmetic and bytes -/

/-- `cmp esi, eax; cmova esi, eax` for `esi` = `a`, `eax` = `b` (= `n`): the smaller. -/
theorem cmv (A B : BitVec 32) (n : Nat) (hB : B.toNat = n) :
    (if (!(decide (A.toNat < B.toNat) || decide (A = B))) = true then B else A).toNat = min A.toNat n := by
  subst hB
  rcases Nat.lt_or_ge A.toNat B.toNat with h | h
  · simp [h] <;> omega
  · rcases Nat.lt_or_eq_of_le h with h' | h'
    · have hne : A ≠ B := fun e => by rw [e] at h'; omega
      have hn : ¬ A.toNat < B.toNat := by omega
      simp [hn, hne] <;> omega
    · have he : A = B := BitVec.eq_of_toNat_eq h'.symm
      subst he
      simp

/-- A quad word apart from a store of a double word. -/
theorem rq_out4 (W : Addr → Byte) (a x : Addr) (v : BitVec 32) (ha : a.toNat + 4 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + 4 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst W a (toBytesLE v 4), x) = rdq(W, x) :=
  congrArg (ofBytesLE 64)
    (Tun.rd_Vst W a _ x 8 (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))

/-! ## The invariant -/

/-- The registers at 62 for `m` = `c`: `esi` = `r12` = `c`, `r13` = `4 c`, `rbp` = `s`, `rbx` = `this`, 40 below
the entry. -/
abbrev gJ (g : Gprs) (c : BitVec 32) (a cx d : BitVec 64) : Gprs :=
  { g with rax := a, rcx := cx, rdx := d, rsi := zl c, r12 := zl c, r13 := zl c * 4#64, rbp := g.rdx,
           rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }

/-- `m` = `c` for `num` (the entry's `esi`) and the length `n`. -/
abbrev Mn (g : Gprs) (n : Nat) (c : BitVec 32) : Prop := c.toNat = min (BitVec.setWidth 32 g.rsi).toNat n

/-- The loop's head at the index `k`: `rax` = `k`. -/
def I32 (g₀ : Gprs) (k : Nat) (g : Gprs) : Prop :=
  ∃ cx d, g = { g₀ with rax := BitVec.ofNat 64 k, rcx := cx, rdx := d, rbp := g₀.rdx, rbx := g₀.rdi,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64 }

/-- The join. -/
def I62 (g₀ : Gprs) (n : Nat) (g : Gprs) : Prop := ∃ c a cx d, Mn g₀ n c ∧ g = gJ g₀ c a cx d

/-- The invariant at the cut points (`VS` the bytes after the pushes). -/
def Inv (g₀ : Gprs) (V₀ VS : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = n + 2 ∧ g = g₀ ∧ V = V₀) ∨ (ℓ = 32 ∧ V = VS ∧ ∃ k, k < n ∧ m = n - k + 1 ∧ I32 g₀ k g) ∨
    (ℓ = 62 ∧ m = 0 ∧ V = VS ∧ I62 g₀ n g)

/-- At the `call`. -/
def Fin (g₀ : Gprs) (VS : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 65 ∧ V = VS ∧ ∃ c a cx d, Mn g₀ n c ∧ g = gJ g₀ c a cx d

/-- At an exit: a cut point's invariant with a smaller measure, or the `call`. -/
def Nx (g₀ : Gprs) (V₀ VS : Addr → Byte) (n m : Nat) : Post :=
  fun j' g' _ V' => (∃ m' < m, Inv g₀ V₀ VS n j' m' g' V') ∨ Fin g₀ VS n j' g' V'

variable {g₀ : Gprs} {V₀ VS : Addr → Byte} {n : Nat}

theorem x32 {m k : Nat} (hk : k < n) (hm : n - k + 1 < m) {a cx d : BitVec 64} (hr : a = BitVec.ofNat 64 k)
    {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rbp := g₀.rdx, rbx := g₀.rdi,
                        rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64 }) :
    Nx g₀ V₀ VS n m 32 g fl VS := by
  subst hr hg
  exact Or.inl ⟨n - k + 1, hm, Or.inr (Or.inl ⟨rfl, rfl, k, hk, rfl, cx, d, rfl⟩)⟩

theorem x62 {m : Nat} (hm : 0 < m) {c : BitVec 32} (hc : Mn g₀ n c) {a cx d r q1 q2 : BitVec 64}
    (hr : r = zl c) (h1 : q1 = zl c) (h2 : q2 = zl c * 4#64) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := cx, rdx := d, rsi := r, r12 := q1, r13 := q2, rbp := g₀.rdx,
                        rbx := g₀.rdi, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64 }) :
    Nx g₀ V₀ VS n m 62 g fl VS := by
  subst hr h1 h2 hg
  exact Or.inl ⟨0, hm, Or.inr (Or.inr ⟨rfl, rfl, rfl, c, a, cx, d, hc, rfl⟩)⟩

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- The pushes, `mov rbp, rdx; mov rbx, rdi; sub rsp, 8; mov ecx, [rdx]; test ecx, ecx; je`: for the length 0
`xor esi, esi; xor r13d, r13d; xor r12d, r12d` to the join, else `xor eax, eax` to the loop's head at 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) (hw : Ucw.Wz F (V0 V g) g.rdx n) :
    W_0 F Wl (Nx g V (V0 V g) n (n + 2)) g f V := by
  obtain ⟨-, hz, hnz, hf⟩ := hw
  have f0 : ∀ j < 4, Foot F.data (Addr.add g.rdx j) := by
    have := hf 0 (Nat.zero_le _)
    rwa [Nat.mul_zero, addr_add_zero] at this
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · have hX : (rdd(V0 V g, g.rdx) == 0) = true := by
      rw [beq_iff_eq]
      have e := hz
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V0] at hs1 hs2 hs3 hs4 f0 hX ⊢
    wpx [W_0, W_112, W_26, o0, o1, o7, Ucw.xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x62 (c := 0#32) (by omega) (by simp [Mn]) (by first | decide | simp)
      (by first | decide | simp) (by first | decide | simp) rfl
  · have hX : (rdd(V0 V g, g.rdx) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      have e := hnz 0 hp
      rwa [Nat.mul_zero, addr_add_zero] at e
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [V0] at hs1 hs2 hs3 hs4 f0 hX ⊢
    wpx [W_0, W_112, W_26, o0, o1, o7, Ucw.xz, BitVec.and_self, hX, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact f0
      | assumption
      | apply And.intro
      | intro)
    all_goals exact x32 (k := 0) hp (by omega) (by rfl) rfl

set_option maxHeartbeats 2000000 in
/-- The loop's head at the index `k`: `lea edx, [rax + 1]; mov rax, rdx; mov edx, [rbp + rdx * 4]; test edx, edx;
jne`: the head at `k + 1` for a character not 0, else (`k + 1` = `n`) `cmp esi, eax; cmova esi, eax;
mov r12d, esi; lea r13, [r12 * 4]` to the join. -/
theorem vc_32 {k : Nat} {g : Gprs} {f : Rflags} (hw : Ucw.Wz F VS g₀.rdx n) (hk : k < n) (h : I32 g₀ k g) :
    W_32 F Wl (Nx g₀ V₀ VS n (n - k + 1)) g f VS := by
  obtain ⟨hn, hz, hnz, hf⟩ := hw
  obtain ⟨cx, d, rfl⟩ := h
  have hA := Ucw.ldw g₀.rdx (k := k) (by omega)
  have fk := hf (k + 1) (by omega)
  have e1 := Ucw.sk1 (k := k) (by omega)
  by_cases hc : k + 1 = n
  · have hX : (rdd(VS, Addr.add g₀.rdx (4 * (k + 1))) == 0) = true := by
      rw [beq_iff_eq, hc]
      exact hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_46, o2, o3, hA, hX, BitVec.and_self, eq_self_iff_true, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals refine x62 (by omega) ?_ rfl (by first | rfl | simp) (by first | rfl | simp) rfl
    all_goals first
      | exact cmv _ _ _ (by simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | (split <;> rename_i hq <;> simp at hq <;> bv_omega)
  · have hX : (rdd(VS, Addr.add g₀.rdx (4 * (k + 1))) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact hnz (k + 1) (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
    dsimp only at hA fk hX ⊢
    wpx [W_32, W_46, o2, o3, hA, hX, BitVec.and_self, eq_self_iff_true, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fk
      | apply And.intro
      | intro)
    all_goals exact x32 (k := k + 1) (by omega) (by omega) (by exact e1) rfl

/-- The join: `mov rdi, rbx` to the `call`. -/
theorem vc_62 {g : Gprs} {f : Rflags} (h : I62 g₀ n g) : W_62 F Wl (Nx g₀ V₀ VS n 0) g f VS := by
  obtain ⟨c, a, cx, d, hc, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [gJ]
  wpx [W_62, o4]
  exact Or.inr ⟨rfl, rfl, c, a, cx, d, hc, rfl⟩

theorem vcAll (hw : Ucw.Wz F VS g₀.rdx n) (hV : VS = V0 V₀ g₀)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i)) (ℓ m : Nat) (g : Gprs) (f : Rflags)
    (V : Addr → Byte) (h : Inv g₀ V₀ VS n ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ VS n m) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, k, hk, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩ := h
  · subst hV
    exact vc_0 hs1 hs2 hs3 hs4 hw
  · exact vc_32 hw hk h
  · exact vc_62 h

/-- Back from `SetStartLen`: `mov rdi, [rbx]; mov rdx, r12; mov rsi, rbp` to the `call` at 79. -/
theorem vc_70 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i))
    (h : ∀ fl, Q 79 { g with rdi := rdq(V, p), rdx := g.r12, rsi := g.rbp } fl V) :
    W_70 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx fp h ⊢
  subst hbx
  wpx [W_70, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `wmemcpy`: `mov rax, [rbx]; mov dword [rax + r13], 0; add rsp, 8; pop rbx; pop rbp; pop r12;
pop r13` to the `ret` at 105. -/
theorem vc_84 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : Addr} (hbx : g.rbx = p)
    (h13 : g.r13 = q) (fp : ∀ i < 8, Foot F.data (Addr.add p i))
    (w4 : ∀ i < 4, Foot Wl (Addr.add (rdq(V, p) + q) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 105
      { g with
          rax := rdq(V, p),
          rbx := rdq(Vst V (rdq(V, p) + q) (toBytesLE 0#32 4), g.rsp + 8#64),
          rbp := rdq(Vst V (rdq(V, p) + q) (toBytesLE 0#32 4), g.rsp + 8#64 + 8),
          r12 := rdq(Vst V (rdq(V, p) + q) (toBytesLE 0#32 4), g.rsp + 8#64 + 8 + 8),
          r13 := rdq(Vst V (rdq(V, p) + q) (toBytesLE 0#32 4), g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl (Vst V (rdq(V, p) + q) (toBytesLE 0#32 4))) :
    W_84 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h13 fp w4 hl0 hl1 hl2 hl3 h ⊢
  subst hbx h13
  wpx [W_84, o6]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (num, s)` from its entry, `n` the length of `s` (`Wz`; its characters clear of the pushes).
At `SetStartLen`'s entry for `m` = `c` (`Mn`) the registers `gJ`, `rsp` 48 below the entry's, the bytes `V0` with
the return address pushed (`ku`); back at `ucn_at + 70` (`Pu`), at `wmemcpy`'s entry with `rdi` = `_chars`,
`rsi` = `s`, `rdx` = `m` (`kw`); back at `ucn_at + 84` (`Pw`, with `_chars + 4 m` writable and clear of the saved
registers and the return address), at the return address with `_chars[m] = 0` and the saved registers back
(`kr`). -/
theorem ucn_ok {Pu : BitVec 32 → State → (Addr → Byte) → Prop} {Pw : BitVec 32 → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ucn_at ucn) (hinU : CodeIn L Usl.usl_at Usl.usl)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucn_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hw : Ucw.Wz F V X.cpu.gpr.rdx n)
    (hsd : ∀ i ≤ n, (Addr.add X.cpu.gpr.rdx (4 * i)).toNat + 4 ≤ 2 ^ 64 ∧
      ((Addr.add X.cpu.gpr.rdx (4 * i)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 32 ∨
        X.cpu.gpr.rsp.toNat ≤ (Addr.add X.cpu.gpr.rdx (4 * i)).toNat))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (ku : ∀ (Y : State) (t' : Nat) (cm : BitVec 32) (a cx d : BitVec 64), Mn X.cpu.gpr n cm → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8)) →
      Y.cpu.rip = Usl.usl_at → Y.cpu.gpr = (gJ X.cpu.gpr cm a cx d).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = ucn_at.add 70 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdx → Z.cpu.gpr.r12 = zl cm → Z.cpu.gpr.r13 = zl cm * 4#64 →
        Sv V₁ X.cpu.gpr (e₂.add j₂) → Pu cm Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (cm : BitVec 32) (Z : State) (V₁ : Addr → Byte), Pu cm Z V₁ → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 84) 8)) →
      Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), rdx := zl cm, rsi := X.cpu.gpr.rdx }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = ucn_at.add 84 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zw.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zw.cpu.gpr.r13 = zl cm * 4#64 → Sv V₂ X.cpu.gpr (e₂.add j₂) →
        (∀ i < 4, Foot Wl (Addr.add (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64) i)) →
        (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat + 4 ≤ 2 ^ 64 →
        ((rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 32 ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat) →
        Pw cm Zw V₂ → GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (cm : BitVec 32) (Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw cm Zw V₂ →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64) (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with
          rax := rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp + 8 } →
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
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have a32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have a24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
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
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the string as it was before the pushes
  have rd0 : ∀ i ≤ n, rdd(V0 V X.cpu.gpr, Addr.add X.cpu.gpr.rdx (4 * i)) =
      rdd(V, Addr.add X.cpu.gpr.rdx (4 * i)) := fun i hi =>
    congrArg (ofBytesLE 32) (m0 (V := V) (g := X.cpu.gpr) (by omega) _ 4 (hsd i hi).1 (hsd i hi).2)
  have hw' : Ucw.Wz F (V0 V X.cpu.gpr) X.cpu.gpr.rdx n := by
    obtain ⟨w1, w2, w3, w4⟩ := hw
    refine ⟨w1, ?_, fun i hi => ?_, w4⟩
    · rw [rd0 n (Nat.le_refl _)]
      exact w2
    · rw [rd0 i (by omega)]
      exact w3 i hi
  -- to the `call` of `SetStartLen`
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V (V0 V X.cpu.gpr) n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr (V0 V X.cpu.gpr) n j g V')
    (fun ℓ m g f V' h => vcAll hw' rfl hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)
      (by rw [e32]; exact hs4) ℓ m g f V' h) ?_
    (n + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V₁ ⟨rfl, rfl, cm, a, cx, d, hc, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_65 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_65 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c48] at hA₂
  refine ku Y₂ t₂ cm a cx d hc hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
  -- back from `SetStartLen`
  intro Z V₂ t₃ hKZ hAZ hrZ hzs hzb hzp hz12 hz13 _ hPu
  refine (c_70 prof).run c hin (fun j' g' _ V' => j' = 79 ∧
      g' = { Z.cpu.gpr with rdi := rdq(V₂, X.cpu.gpr.rdi), rdx := zl cm, rsi := X.cpu.gpr.rdx } ∧ V' = V₂)
    hKZ hAZ hrZ (vc_70 hzb fd0 fun _ => ⟨rfl, by rw [hz12, hzp], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₄ hKU hAU hrU hgU -
  subst V₃
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgU]; exact hzs
  have hstU : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c48]; exact hs6
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_79 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
    tgt_79 hstU ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU, c48] at hA₃
  refine kw cm Z V₂ hPu Y₃ t₅ hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (by rw [hg₃, hsU, c48, hgU]) ?_
  -- back from `wmemcpy`
  intro Zw W t₆ hKw hAw hrw hws hwb hw13 hsv hw4 hpb hpd hPw
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hsv
  have r1 : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 32 ≤ x.toNat → x.toNat ≤ X.cpu.gpr.rsp.toNat →
      rdq(Vst W (rdq(W, X.cpu.gpr.rdi) + zl cm * 4#64) (toBytesLE 0#32 4), x) = rdq(W, x) := by
    intro x hx h1 h2
    refine rq_out4 W _ x _ hpb hx ?_
    omega
  have q32 := (r1 (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (Nat.le_of_eq tn32.symm)
    (by rw [tn32]; omega)).trans hb1
  have q24 := (r1 (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega) (by rw [tn24]; omega)).trans hb2
  have q16 := (r1 (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)).trans hb3
  have q8 := (r1 (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)).trans hb4
  have q0 := (r1 X.cpu.gpr.rsp hp8 (by omega) (Nat.le_refl _)).trans hb5
  refine (c_84 prof).run c hin (fun j' g' _ V' => j' = 105 ∧
      g' = { Zw.cpu.gpr with
          rax := rdq(W, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp } ∧
      V' = Vst W (rdq(W, X.cpu.gpr.rdi) + zl cm * 4#64) (toBytesLE 0#32 4)) hKw hAw hrw
    (vc_84 hwb hw13 fd0 hw4 (by rw [hws, a32]; exact h32) (by rw [hws, a32, a24]; exact h24)
      (by rw [hws, a32, a24, a16]; exact h16) (by rw [hws, a32, a24, a16, a8]; exact h8)
      fun _ => ⟨rfl, by
        rw [hws, a32, a24, a16, a8, e8, q32, q24, q16, q8], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₇ hKU' hAU' hrU' hgU' -
  subst V₄
  have hsU' : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
  refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_105 _) (by rw [hsU']; exact hl) hin₂ h₂
    (by rw [hsU']; exact q0) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr cm Zw W Z' t₈ hPw hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU']
  try rfl

end FV7z.Ucn
