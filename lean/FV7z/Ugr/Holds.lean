import FV7z.Ugr.Cuts
import FV7z.Ura.Code
import FV7z.Ura.Blocks
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::Grow` (PLAN.md §M, M1)

7-Zip 26.06's `UString::Grow (unsigned n)` at `0x44d0e0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `n`
in `esi`: with `_len` and `_limit` the 4 bytes at `this + 8` and `this + 12`, a `ret` (88) when `n <= _limit - _len`
(`jae` at 14). Else `next = ((_len + n) + (_len + n) / 2 + 16) & ~15) - 1`, `k_Alloc_Len_Limit` (`0x3ffffffe`) instead
when below `_len` (`ja` at 39) or above it (`jbe` at 46 not taken); the throw stub at `0x401406` when `next <= _len`
(`jae` at 55) or `next - _len < n` (`jb` at 67); else `esi = next - 1`, `add rsp, 8` and a tail jump (80) to
`UString::ReAlloc (next - 1)` (`Ura.ura_at`). No byte is written.

The return, the callee and the throw stub are hypotheses (`kn`, `kf`, `kt`), as in `FV7z/Caa/Holds.lean` and
`FV7z/Ug1/Holds.lean`.

- `gU`: the registers from 48/53 on: `rax` = `next`, `rdx` = `_len`, `rsp` 8 below the entry's.
- `nlt`, `le_of_jbe`, `f55_f`, `f67_f`: what the flags of the `jae` at 14, the `jbe` at 46, the `jae` at 55 and the
  `jb` at 67 say.
- `vc_0`, `vc_48`, `vc_53`, `vc_61`, `vc_73`: the verification conditions of the pieces.
- `ugr_ok`: from the entry to the return address (`kn`), the throw stub (`kt`), or `UString::ReAlloc`'s entry with
  `_len < next <= 0x3ffffffe`, `n <= next - _len`, `esi` = `next - 1` and `rsp` as at the entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ugr

/-- The `jae` to the throw stub at 55. -/
def pja : List Byte := [0x0f, 0x83, 0xe9, 0x42, 0xfb, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709241065] 6) := by dec_rfl
theorem wa_55 : pja <+: ugr.drop 55 := by decide +kernel
theorem jae_55 (feat : Features) : Dec feat ugr 55 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709241065] 6) :=
  Dec.shift (j := 55) (k := 0) (pja_0 feat) wa_55 (Nat.zero_le _)
theorem tgt_55 : ugr_at.add (55 + 6) + BitVec.ofNat 64 18446744073709241065 = (0x401406#64).add 0 := by decide

/-- The `jb` to the throw stub at 67. -/
def pjb : List Byte := [0x0f, 0x82, 0xdd, 0x42, 0xfb, 0xff]
theorem pjb_0 : ∀ feat, Dec feat pjb 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709241053] 6) := by dec_rfl
theorem wb_67 : pjb <+: ugr.drop 67 := by decide +kernel
theorem jb_67 (feat : Features) : Dec feat ugr 67 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709241053] 6) :=
  Dec.shift (j := 67) (k := 0) (pjb_0 feat) wb_67 (Nat.zero_le _)
theorem tgt_67 : ugr_at.add (67 + 6) + BitVec.ofNat 64 18446744073709241053 = (0x401406#64).add 0 := by decide

/-- The tail jump to `UString::ReAlloc`. -/
def pjm : List Byte := [0xe9, 0x8b, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) := by dec_rfl
theorem wm_80 : pjm <+: ugr.drop 80 := by decide +kernel
theorem jmp_80 (feat : Features) : Dec feat ugr 80 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) :=
  Dec.shift (j := 80) (k := 0) (pjm_0 feat) wm_80 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_88 : pret <+: ugr.drop 88 := by decide +kernel
theorem ret_88 (feat : Features) : Dec feat ugr 88 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 88) (k := 0) (pret_0 feat) w_88 (Nat.zero_le _)

/-- The registers from 48/53 on: `rax` = `nx`, `rcx` = `c`, `rdx` = `_len`, `rsp` 8 below the entry's. -/
abbrev gU (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 nx,
    rcx := c,
    rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
    rsp := g.rsp - 8#64 }

/-- `ecx` at 67: `next - _len`. -/
abbrev cx61 (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 nx) -
    BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, g.rdi + 8#64)))

/-- `jae` taken. -/
theorem nlt {a b : Nat} (h : (!decide (a < b)) = true) : b ≤ a := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
  omega

/-- `jbe` taken: not above `0x3ffffffe`. -/
theorem le_of_jbe {s : BitVec 32} (h : (decide (s.toNat < 1073741822) || decide (s = 1073741822#32)) = true) :
    s.toNat ≤ 1073741822 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · subst h; decide

/-- 32 bits zero-extended, their low 32: the same (as `FV7z/Pos/Holds.lean`). -/
theorem sw32 (w : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 w) = w :=
  (BitVec.setWidth_setWidth_of_le w (by decide)).trans (BitVec.setWidth_eq w)

/-- `cmp edx, eax; jae` not taken: `l < n`. -/
theorem f55_f {f : Rflags} {l n : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 l)) (BitVec.setWidth 32 (BitVec.setWidth 64 n))).cond 3 =
      false) : l.toNat < n.toNat := by
  rw [sw32, sw32, cond_3, subF_cf] at h
  simp only [Bool.not_eq_false', decide_eq_true_eq] at h
  exact h

/-- `cmp ecx, esi; jb` not taken: `r <= n - l`. -/
theorem f67_f {f : Rflags} {n l r : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 n) - BitVec.setWidth 32 (BitVec.setWidth 64 l)) r).cond 2 =
      false) : r.toNat ≤ (n - l).toNat := by
  rw [sw32, sw32, cond_2, subF_cf] at h
  simp only [decide_eq_false_iff_not] at h
  omega

/-- `lea esi, [rax - 1]` of a zero-extended `eax`. -/
theorem m1 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x + 18446744073709551615#64) = x - 1#32 := by
  bv_omega

/-- `lea esi, [rax - 1]; add rsp, 8` from `gU`. -/
theorem gU_back (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) (c : BitVec 64) :
    { gU V g nx c with
      rsp := (gU V g nx c).rsp + 8#64,
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 ((gU V g nx c).rax + 18446744073709551615#64)) } =
      { g with
        rax := BitVec.setWidth 64 nx, rcx := c, rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
        rsi := BitVec.setWidth 64 (nx - 1#32) } := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e1 : rsp - 8#64 + 8#64 = rsp := BitVec.sub_add_cancel _ _
  have e2 : BitVec.setWidth 32 (BitVec.setWidth 64 nx + 18446744073709551615#64) = nx - 1#32 := m1 nx
  show Gprs.mk (BitVec.setWidth 64 nx) c (BitVec.setWidth 64 rdd(V, rdi + 8#64)) rbx (rsp - 8#64 + 8#64) rbp
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 nx + 18446744073709551615#64)))
      rdi r8 r9 r10 r11 r12 r13 r14 r15 =
    Gprs.mk (BitVec.setWidth 64 nx) c (BitVec.setWidth 64 rdd(V, rdi + 8#64)) rbx rsp rbp
      (BitVec.setWidth 64 (nx - 1#32)) rdi r8 r9 r10 r11 r12 r13 r14 r15
  rw [e1, e2]

variable {F : Footprint} {Wl : List Rgn}

/-- `mov edx, [rdi + 8]; mov eax, [rdi + 12]; sub eax, edx; cmp eax, esi; jae 88`, then `lea; sub rsp, 8; …;
cmp edx, eax; ja 48; cmp eax, 0x3ffffffe; jbe 53`: to 88 with `n <= _limit - _len`, to 48, or to 53 with `next` not
above `0x3ffffffe`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (h88 : (BitVec.setWidth 32 g.rsi).toNat ≤ (rdd(V, g.rdi + 12#64) - rdd(V, g.rdi + 8#64)).toNat → ∀ fl,
      Q 88 { g with
        rax := BitVec.setWidth 64 (rdd(V, g.rdi + 12#64) - rdd(V, g.rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64) } fl V)
    (h48 : ∀ (a c : BitVec 64) fl, Q 48
      { g with rax := a, rcx := c, rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rsp := g.rsp - 8#64 } fl V)
    (h53 : ∀ (c : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 → ∀ fl, Q 53 (gU V g nx c) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f12 h88 h48 ⊢
  wpx [W_0, W_16, W_41, o0, o1, o2]
  all_goals repeat' (first | with_reducible exact f8 | with_reducible exact f12 | apply And.intro | intro _)
  all_goals first
    | exact h88 (nlt (by assumption)) _
    | exact h48 _ _ _
    | exact h53 _ _ (le_of_jbe (by assumption)) _

/-- `mov eax, 0x3ffffffe` to 53. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 53 { g with rax := BitVec.setWidth 64 1073741822#32 } fl V) : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_48, o3]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- `cmp edx, eax` to the `jae` at 55. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : Q 55 g (subF (rfz f) (BitVec.setWidth 32 g.rdx) (BitVec.setWidth 32 g.rax)) V) : W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_53, o4]
  all_goals repeat' (first | exact h | apply And.intro | intro _)

/-- `mov ecx, eax; sub ecx, edx; cmp ecx, esi` to the `jb` at 67. -/
theorem vc_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : Q 67 { g with rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax - BitVec.setWidth 32 g.rdx) }
      (subF (rfz (subF (rfz f) (BitVec.setWidth 32 g.rax) (BitVec.setWidth 32 g.rdx)))
        (BitVec.setWidth 32 g.rax - BitVec.setWidth 32 g.rdx) (BitVec.setWidth 32 g.rsi)) V) :
    W_61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_61, o5]
  all_goals repeat' (first | exact h | apply And.intro | intro _)

/-- `lea esi, [rax - 1]; add rsp, 8` to the jump at 80. -/
theorem vc_73 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 80 { g with
      rsp := g.rsp + 8#64,
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rax + 18446744073709551615#64)) } fl V) :
    W_73 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_73, o6]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::Grow (n)` (`this` = `rdi`, `n` = `esi`) from its entry, no byte written. With `_len`, `_limit` the 4
bytes at `this + 8`, `this + 12`: at the return address when `n <= _limit - _len` (`kn`); else, with `rsp` 8 below
the entry's, at the throw stub `0x401406` (`kt`), or at `UString::ReAlloc`'s entry with `esi` = `next - 1`,
`_len < next <= 0x3ffffffe`, `n <= next - _len` and `rsp` as at the entry (`kf`). -/
theorem ugr_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ugr_at ugr) (hinR : CodeIn L Ura.ura_at Ura.ura)
    {codeT : List Byte} (hinT : CodeIn L 0x401406#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ugr_at)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤
        (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64),
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kt : ∀ (Y : State) (t' : Nat) (a cx : BitVec 64), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 0x401406#64 →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := a, rcx := cx, rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsp := X.cpu.gpr.rsp - 8#64 } →
      GoG prof L o gev gP gE Y t')
    (kf : ∀ (Y : State) (t' : Nat) (cx : BitVec 64) (nx : BitVec 32),
      (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < nx.toNat → nx.toNat ≤ 1073741822 →
      (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (nx - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Ura.ura_at →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 nx, rcx := cx, rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64),
        rsi := BitVec.setWidth 64 (nx - 1#32) } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- from 53: the `jae` and the `jb` to the throw stub, else `lea esi, [rax - 1]; add rsp, 8` and the tail jump
  have k53 : ∀ (cx : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = ugr_at.add 53 → Y.cpu.gpr = gU V X.cpu.gpr nx cx →
      GoG prof L o gev gP gE Y t' := by
    intro cx nx hn Y t₁ hKY hAY hrY hgY
    refine (c_53 prof).run c hin (fun j' g' f' V' => j' = 55 ∧ g' = gU V X.cpu.gpr nx cx ∧ V' = V ∧
        f' = subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx)))
      hKY hAY hrY (by rw [hgY]; exact vc_53 ⟨rfl, rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV, hfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂
    subst hg hfl; subst V₁
    refine c.s_jcc_x hK₂ hA₂ hin (lt_len (by decide)) hr₂ (jae_55 _) hinT (tgt := 0) hT tgt_55 ?_ ?_
    · intro _
      rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
      exact kt Y₃ t₃ (BitVec.setWidth 64 nx) cx hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (hg₃.trans hg₂)
    intro hc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hc' : (subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
        (BitVec.setWidth 32 (BitVec.setWidth 64 nx))).cond 3 = false := by
      rw [← hf₂]; exact hc
    have hlt := f55_f hc'
    refine (c_61 prof).run c hin (fun j' g' f' V' => j' = 67 ∧ g' = gU V X.cpu.gpr nx (cx61 V X.cpu.gpr nx) ∧
        V' = V ∧
        f' = subF (rfz (subF (rfz Y₃.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 nx))
            (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx) -
            BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 X.cpu.gpr.rsi))
      hK₃ hA₃ hr₃ (by rw [hg₃, hg₂]; exact vc_61 ⟨rfl, rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV, hfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄
    subst hg hfl; subst V₁
    refine c.s_jcc_x hK₄ hA₄ hin (lt_len (by decide)) hr₄ (jb_67 _) hinT (tgt := 0) hT tgt_67 ?_ ?_
    · intro _
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      exact kt Y₅ t₅ (BitVec.setWidth 64 nx) (cx61 V X.cpu.gpr nx) hK₅ hA₅ (by rw [hr₅, addr_add_zero])
        (hg₅.trans hg₄)
    intro hc
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
    have hc' : (subF (rfz (subF (rfz Y₃.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 nx))
            (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx) -
            BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 X.cpu.gpr.rsi)).cond 2 = false := by
      rw [← hf₄]; exact hc
    have hle := f67_f hc'
    refine (c_73 prof).run c hin (fun j' g' _ V' => j' = 80 ∧
        g' = { X.cpu.gpr with
          rax := BitVec.setWidth 64 nx, rcx := cx61 V X.cpu.gpr nx,
          rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsi := BitVec.setWidth 64 (nx - 1#32) } ∧
        V' = V)
      hK₅ hA₅ hr₅
      (by rw [hg₅, hg₄]; exact vc_73 fun _ => ⟨rfl, gU_back V X.cpu.gpr nx (cx61 V X.cpu.gpr nx), rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
    subst hg; subst V₁
    refine c.s_jmp_x hK₆ hA₆ hin (lt_len (by decide)) hr₆ (jmp_80 _) hinR (Ura.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
    exact kf Y₇ t₇ (cx61 V X.cpu.gpr nx) nx hlt hn hle hK₇ hA₇ (by rw [hr₇, addr_add_zero])
      (hg₇.trans hg₆)
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 88 ∧ (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤
          (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat ∧
          g' = { X.cpu.gpr with
            rax := BitVec.setWidth 64 (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)),
            rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64) }) ∨
        (j' = 48 ∧ ∃ a cx : BitVec 64, g' = { X.cpu.gpr with
          rax := a, rcx := cx, rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64),
          rsp := X.cpu.gpr.rsp - 8#64 }) ∨
        (j' = 53 ∧ ∃ (cx : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 ∧
          g' = gU V X.cpu.gpr nx cx)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f8 f12 (fun hle _ => ⟨rfl, Or.inl ⟨rfl, hle, rfl⟩⟩)
      (fun a cx _ => ⟨rfl, Or.inr (Or.inl ⟨rfl, a, cx, rfl⟩)⟩)
      (fun cx nx hn _ => ⟨rfl, Or.inr (Or.inr ⟨rfl, cx, nx, hn, rfl⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, hle, hg⟩ | ⟨rfl, a, cx, hg⟩ | ⟨rfl, cx, nx, hn, hg⟩
  · -- `ret`
    subst hg
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_88 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hle Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- `mov eax, 0x3ffffffe`
    subst hg
    refine (c_48 prof).run c hin (fun j' g' _ V' => j' = 53 ∧ g' = gU V X.cpu.gpr 1073741822#32 cx ∧ V' = V)
      hKY hAY hrY (by rw [hgY]; exact vc_48 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst hg; subst V₁
    exact k53 cx 1073741822#32 (by decide) Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  · subst hg
    exact k53 cx nx hn Y t₁ hKY hAY hrY hgY

end FV7z.Ugr
