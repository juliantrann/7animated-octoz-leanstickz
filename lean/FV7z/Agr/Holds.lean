import FV7z.Agr.Cuts
import FV7z.Arl.Code
import FV7z.Arl.Blocks
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `AString::Grow` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Grow (unsigned n)` at `0x44c0e0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`, `n`
in `esi`: with `_len` and `_limit` the 4 bytes at `this + 8` and `this + 12`, a `ret` (88) when `n <= _limit - _len`
(`jae` at 14). Else `eax = n`, `next = ((_len + n) + (_len + n) / 2 + 16) & ~15) - 1` in `esi`, `k_Alloc_Len_Limit`
(`0x3ffffffe`) instead when below `_len` (`ja` at 41) or above it (`jbe` at 49 not taken); the throw stub at
`0x401394` when `next <= _len` (`jae` at 58) or `next - _len < n` (`jb` at 70); else `add rsp, 8` and a tail jump
(80) to `AString::ReAlloc (next)` (`Arl.arl_at`). No byte is written.

The proof is `FV7z/Ugr/Holds.lean`'s (`UString::Grow`) with the registers renamed: here `n` stays in `eax` and `next`
is in `esi`, and `ReAlloc` gets `next` itself. The return, the callee and the throw stub are hypotheses (`kn`, `kf`,
`kt`).

- `gA`: the registers from 51/56 on: `rax` = `n`, `rdx` = `_len`, `rsi` = `next`, `rsp` 8 below the entry's.
- `nlt`, `le_of_jbe`, `f58_f`, `f70_f`: what the flags of the `jae` at 14, the `jbe` at 49, the `jae` at 58 and the
  `jb` at 70 say.
- `vc_0`, `vc_51`, `vc_56`, `vc_64`, `vc_76`: the verification conditions of the pieces.
- `agr_ok`: from the entry to the return address (`kn`), the throw stub (`kt`), or `AString::ReAlloc`'s entry with
  `_len < next <= 0x3ffffffe`, `n <= next - _len`, `esi` = `next` and `rsp` as at the entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Agr

/-- The `jae` to the throw stub at 58. -/
def pja : List Byte := [0x0f, 0x83, 0x74, 0x52, 0xfb, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709245044] 6) := by dec_rfl
theorem wa_58 : pja <+: agr.drop 58 := by decide +kernel
theorem jae_58 (feat : Features) : Dec feat agr 58 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709245044] 6) :=
  Dec.shift (j := 58) (k := 0) (pja_0 feat) wa_58 (Nat.zero_le _)
theorem tgt_58 : agr_at.add (58 + 6) + BitVec.ofNat 64 18446744073709245044 = (0x401394#64).add 0 := by decide

/-- The `jb` to the throw stub at 70. -/
def pjb : List Byte := [0x0f, 0x82, 0x68, 0x52, 0xfb, 0xff]
theorem pjb_0 : ∀ feat, Dec feat pjb 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709245032] 6) := by dec_rfl
theorem wb_70 : pjb <+: agr.drop 70 := by decide +kernel
theorem jb_70 (feat : Features) : Dec feat agr 70 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709245032] 6) :=
  Dec.shift (j := 70) (k := 0) (pjb_0 feat) wb_70 (Nat.zero_le _)
theorem tgt_70 : agr_at.add (70 + 6) + BitVec.ofNat 64 18446744073709245032 = (0x401394#64).add 0 := by decide

/-- The tail jump to `AString::ReAlloc`. -/
def pjm : List Byte := [0xe9, 0x8b, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) := by dec_rfl
theorem wm_80 : pjm <+: agr.drop 80 := by decide +kernel
theorem jmp_80 (feat : Features) : Dec feat agr 80 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) :=
  Dec.shift (j := 80) (k := 0) (pjm_0 feat) wm_80 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_88 : pret <+: agr.drop 88 := by decide +kernel
theorem ret_88 (feat : Features) : Dec feat agr 88 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 88) (k := 0) (pret_0 feat) w_88 (Nat.zero_le _)

/-- The registers from 51/56 on: `rax` = `n`, `rcx` = `c`, `rdx` = `_len`, `rsi` = `nx`, `rsp` 8 below the entry's. -/
abbrev gA (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
    rcx := c,
    rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
    rsp := g.rsp - 8#64,
    rsi := BitVec.setWidth 64 nx }

/-- `ecx` at 70: `next - _len`. -/
abbrev cx64 (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) : BitVec 64 :=
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

/-- `cmp edx, esi; jae` not taken: `l < n`. -/
theorem f58_f {f : Rflags} {l n : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 l)) (BitVec.setWidth 32 (BitVec.setWidth 64 n))).cond 3 =
      false) : l.toNat < n.toNat := by
  rw [sw32, sw32, cond_3, subF_cf] at h
  simp only [Bool.not_eq_false', decide_eq_true_eq] at h
  exact h

/-- `cmp ecx, eax; jb` not taken: `r <= n - l`. -/
theorem f70_f {f : Rflags} {n l r : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 n) - BitVec.setWidth 32 (BitVec.setWidth 64 l)) r).cond 2 =
      false) : r.toNat ≤ (n - l).toNat := by
  rw [sw32, sw32, cond_2, subF_cf] at h
  simp only [decide_eq_false_iff_not] at h
  omega

/-- `add rsp, 8` back from `gA`. -/
theorem gA_back (V : Addr → Byte) (g : Gprs) (nx : BitVec 32) (c : BitVec 64) :
    { gA V g nx c with rsp := (gA V g nx c).rsp + 8#64 } =
      { g with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi), rcx := c, rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
        rsi := BitVec.setWidth 64 nx } := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  show Gprs.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = Gprs.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  congr 1
  all_goals first | rfl | exact BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-- `mov edx, [rdi + 8]; mov ecx, [rdi + 12]; sub ecx, edx; cmp ecx, esi; jae 88`, then `lea; mov eax, esi;
sub rsp, 8; …; cmp edx, esi; ja 51; cmp esi, 0x3ffffffe; jbe 56`: to 88 with `n <= _limit - _len`, to 51, or to 56
with `next` not above `0x3ffffffe`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (h88 : (BitVec.setWidth 32 g.rsi).toNat ≤ (rdd(V, g.rdi + 12#64) - rdd(V, g.rdi + 8#64)).toNat → ∀ fl,
      Q 88 { g with
        rcx := BitVec.setWidth 64 (rdd(V, g.rdi + 12#64) - rdd(V, g.rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64) } fl V)
    (h51 : ∀ (c s : BitVec 64) fl, Q 51
      { g with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi), rcx := c, rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
        rsp := g.rsp - 8#64, rsi := s } fl V)
    (h56 : ∀ (c : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 → ∀ fl, Q 56 (gA V g nx c) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f12 h88 h51 ⊢
  wpx [W_0, W_16, W_43, o0, o1, o2]
  all_goals repeat' (first | with_reducible exact f8 | with_reducible exact f12 | apply And.intro | intro _)
  all_goals first
    | exact h88 (nlt (by assumption)) _
    | exact h51 _ _ _
    | exact h56 _ _ (le_of_jbe (by assumption)) _

/-- `mov esi, 0x3ffffffe` to 56. -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 56 { g with rsi := BitVec.setWidth 64 1073741822#32 } fl V) : W_51 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_51, o3]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- `cmp edx, esi` to the `jae` at 58. -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : Q 58 g (subF (rfz f) (BitVec.setWidth 32 g.rdx) (BitVec.setWidth 32 g.rsi)) V) : W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_56, o4]
  all_goals repeat' (first | exact h | apply And.intro | intro _)

/-- `mov ecx, esi; sub ecx, edx; cmp ecx, eax` to the `jb` at 70. -/
theorem vc_64 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : Q 70 { g with rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi - BitVec.setWidth 32 g.rdx) }
      (subF (rfz (subF (rfz f) (BitVec.setWidth 32 g.rsi) (BitVec.setWidth 32 g.rdx)))
        (BitVec.setWidth 32 g.rsi - BitVec.setWidth 32 g.rdx) (BitVec.setWidth 32 g.rax)) V) :
    W_64 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_64, o5]
  all_goals repeat' (first | exact h | apply And.intro | intro _)

/-- `add rsp, 8` to the jump at 80. -/
theorem vc_76 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 80 { g with rsp := g.rsp + 8#64 } fl V) : W_76 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_76, o6]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Grow (n)` (`this` = `rdi`, `n` = `esi`) from its entry, no byte written. With `_len`, `_limit` the 4
bytes at `this + 8`, `this + 12`: at the return address when `n <= _limit - _len` (`kn`); else, with `rsp` 8 below
the entry's, at the throw stub `0x401394` (`kt`), or at `AString::ReAlloc`'s entry with `esi` = `next`,
`_len < next <= 0x3ffffffe`, `n <= next - _len` and `rsp` as at the entry (`kf`). -/
theorem agr_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L agr_at agr) (hinR : CodeIn L Arl.arl_at Arl.arl)
    {codeT : List Byte} (hinT : CodeIn L 0x401394#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = agr_at)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤
        (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rcx := BitVec.setWidth 64 (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64),
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kt : ∀ (Y : State) (t' : Nat) (cx s : BitVec 64), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 0x401394#64 →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi), rcx := cx,
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsp := X.cpu.gpr.rsp - 8#64, rsi := s } →
      GoG prof L o gev gP gE Y t')
    (kf : ∀ (Y : State) (t' : Nat) (cx : BitVec 64) (nx : BitVec 32),
      (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < nx.toNat → nx.toNat ≤ 1073741822 →
      (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (nx - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Arl.arl_at →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi), rcx := cx,
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsi := BitVec.setWidth 64 nx } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- from 56: the `jae` and the `jb` to the throw stub, else `add rsp, 8` and the tail jump
  have k56 : ∀ (cx : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = agr_at.add 56 → Y.cpu.gpr = gA V X.cpu.gpr nx cx →
      GoG prof L o gev gP gE Y t' := by
    intro cx nx hn Y t₁ hKY hAY hrY hgY
    refine (c_56 prof).run c hin (fun j' g' f' V' => j' = 58 ∧ g' = gA V X.cpu.gpr nx cx ∧ V' = V ∧
        f' = subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx)))
      hKY hAY hrY (by rw [hgY]; exact vc_56 ⟨rfl, rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV, hfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂
    subst hg hfl; subst V₁
    refine c.s_jcc_x hK₂ hA₂ hin (lt_len (by decide)) hr₂ (jae_58 _) hinT (tgt := 0) hT tgt_58 ?_ ?_
    · intro _
      rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
      exact kt Y₃ t₃ cx (BitVec.setWidth 64 nx) hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (hg₃.trans hg₂)
    intro hc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hc' : (subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
        (BitVec.setWidth 32 (BitVec.setWidth 64 nx))).cond 3 = false := by
      rw [← hf₂]; exact hc
    have hlt := f58_f hc'
    refine (c_64 prof).run c hin (fun j' g' f' V' => j' = 70 ∧ g' = gA V X.cpu.gpr nx (cx64 V X.cpu.gpr nx) ∧
        V' = V ∧
        f' = subF (rfz (subF (rfz Y₃.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 nx))
            (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx) -
            BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi))))
      hK₃ hA₃ hr₃ (by rw [hg₃, hg₂]; exact vc_64 ⟨rfl, rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV, hfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄
    subst hg hfl; subst V₁
    refine c.s_jcc_x hK₄ hA₄ hin (lt_len (by decide)) hr₄ (jb_70 _) hinT (tgt := 0) hT tgt_70 ?_ ?_
    · intro _
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      exact kt Y₅ t₅ (cx64 V X.cpu.gpr nx) (BitVec.setWidth 64 nx) hK₅ hA₅ (by rw [hr₅, addr_add_zero])
        (hg₅.trans hg₄)
    intro hc
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
    have hc' : (subF (rfz (subF (rfz Y₃.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 nx))
            (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))))
          (BitVec.setWidth 32 (BitVec.setWidth 64 nx) -
            BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi)))).cond 2 = false := by
      rw [← hf₄]; exact hc
    have hle : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (nx - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat := by
      have h := f70_f hc'
      rwa [sw32] at h
    refine (c_76 prof).run c hin (fun j' g' _ V' => j' = 80 ∧
        g' = { X.cpu.gpr with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi), rcx := cx64 V X.cpu.gpr nx,
          rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsi := BitVec.setWidth 64 nx } ∧
        V' = V)
      hK₅ hA₅ hr₅
      (by rw [hg₅, hg₄]; exact vc_76 fun _ => ⟨rfl, gA_back V X.cpu.gpr nx (cx64 V X.cpu.gpr nx), rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
    subst hg; subst V₁
    refine c.s_jmp_x hK₆ hA₆ hin (lt_len (by decide)) hr₆ (jmp_80 _) hinR (Arl.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
    exact kf Y₇ t₇ (cx64 V X.cpu.gpr nx) nx hlt hn hle hK₇ hA₇ (by rw [hr₇, addr_add_zero])
      (hg₇.trans hg₆)
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 88 ∧ (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤
          (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat ∧
          g' = { X.cpu.gpr with
            rcx := BitVec.setWidth 64 (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)),
            rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64) }) ∨
        (j' = 51 ∧ ∃ cx s : BitVec 64, g' = { X.cpu.gpr with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi), rcx := cx,
          rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsp := X.cpu.gpr.rsp - 8#64, rsi := s }) ∨
        (j' = 56 ∧ ∃ (cx : BitVec 64) (nx : BitVec 32), nx.toNat ≤ 1073741822 ∧
          g' = gA V X.cpu.gpr nx cx)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f8 f12 (fun hle _ => ⟨rfl, Or.inl ⟨rfl, hle, rfl⟩⟩)
      (fun cx s _ => ⟨rfl, Or.inr (Or.inl ⟨rfl, cx, s, rfl⟩)⟩)
      (fun cx nx hn _ => ⟨rfl, Or.inr (Or.inr ⟨rfl, cx, nx, hn, rfl⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, hle, hg⟩ | ⟨rfl, cx, s, hg⟩ | ⟨rfl, cx, nx, hn, hg⟩
  · -- `ret`
    subst hg
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_88 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hle Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- `mov esi, 0x3ffffffe`
    subst hg
    refine (c_51 prof).run c hin (fun j' g' _ V' => j' = 56 ∧ g' = gA V X.cpu.gpr 1073741822#32 cx ∧ V' = V)
      hKY hAY hrY (by rw [hgY]; exact vc_51 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst hg; subst V₁
    exact k56 cx 1073741822#32 (by decide) Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  · subst hg
    exact k56 cx nx hn Y t₁ hKY hAY hrY hgY

end FV7z.Agr
