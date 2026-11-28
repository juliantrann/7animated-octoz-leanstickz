import FV7z.Ag1.Cuts
import FV7z.Arl.Code
import FV7z.Arl.Blocks
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `AString::Grow_1` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Grow_1 ()` at `0x44c0a0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`: with
`_len` the 4 bytes at `this + 8`, `next = ((_len + _len / 2 + 16) & ~15) - 1`, `k_Alloc_Len_Limit` (`0x3ffffffe`)
instead when above it (`ja` at 31) or below `_len` (`jbe` at 35 not taken), then the throw stub at `0x401372` when
`next <= _len` (`jbe` at 44), else `add rsp, 8` and a tail jump (54) to `AString::ReAlloc (next)` (`Arl.arl_at`). No
byte is written (`sub rsp, 8` only moves `rsp`).

The callee and the throw stub are hypotheses (`kf`, `kt`), as in `FV7z/Ug1/Holds.lean`, whose proof this is: the bytes
are `UString::Grow_1`'s but for the jump targets (the throw stub `0x401372`, `AString::ReAlloc` at `Arl.arl_at`).

- `gq`: the registers from 42 on: `rax` = `_len`, `rsi` = `next`, `rsp` 8 below the entry's.
- `lim_le`, `f44_t`, `f44_f`: what the flags of the `ja` at 31 and the `jbe` at 44 say.
- `vc_0`, `vc_37`, `vc_42`, `vc_50`: the verification conditions of the pieces.
- `ag1_ok`: from the entry to the throw stub with `next <= _len` (`kt`), or to `AString::ReAlloc`'s entry with
  `_len < next <= 0x3ffffffe` in `esi` and `rsp` as at the entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ag1

/-- The `jbe` to the throw stub. -/
def pjb : List Byte := [0x0f, 0x86, 0xa0, 0x52, 0xfb, 0xff]
theorem pjb_0 : ∀ feat, Dec feat pjb 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709245088] 6) := by dec_rfl
theorem wj_44 : pjb <+: ag1.drop 44 := by decide +kernel
theorem jbe_44 (feat : Features) : Dec feat ag1 44 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709245088] 6) :=
  Dec.shift (j := 44) (k := 0) (pjb_0 feat) wj_44 (Nat.zero_le _)
theorem tgt_44 : ag1_at.add (44 + 6) + BitVec.ofNat 64 18446744073709245088 = (0x401372#64).add 0 := by decide

/-- The tail jump to `AString::ReAlloc`. -/
def pjm : List Byte := [0xe9, 0xe5, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551333] 5) := by dec_rfl
theorem wm_54 : pjm <+: ag1.drop 54 := by decide +kernel
theorem jmp_54 (feat : Features) : Dec feat ag1 54 (FV7z.mk .jmp 64 [.rel 18446744073709551333] 5) :=
  Dec.shift (j := 54) (k := 0) (pjm_0 feat) wm_54 (Nat.zero_le _)

/-- The registers from 42 on: `rax` = `_len`, `rdx` = `d`, `rsi` = `n`, `rsp` 8 below the entry's. -/
abbrev gq (V : Addr → Byte) (g : Gprs) (n : BitVec 32) (d : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64),
    rdx := d,
    rsp := g.rsp - 8#64,
    rsi := BitVec.setWidth 64 n }

/-- Not above `0x3ffffffe` (the `ja` at 31 not taken). -/
theorem lim_le {s : BitVec 32}
    (h : (!(decide (s.toNat < 1073741822) || decide (s = 1073741822#32))) = false) : s.toNat ≤ 1073741822 := by
  simp only [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · subst h; decide

/-- 32 bits zero-extended, their low 32: the same (as `FV7z/Pos/Holds.lean`). -/
theorem sw32 (w : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 w) = w :=
  (BitVec.setWidth_setWidth_of_le w (by decide)).trans (BitVec.setWidth_eq w)

/-- `cmp esi, eax; jbe` taken: `n <= l`. -/
theorem f44_t {f : Rflags} {n l : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 n)) (BitVec.setWidth 32 (BitVec.setWidth 64 l))).cond 6 =
      true) : n.toNat ≤ l.toNat := by
  rw [sw32, sw32, cond_6, subF_cf, subF_zf] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · rw [h]; exact Nat.le_refl _

/-- `cmp esi, eax; jbe` not taken: `l < n`. -/
theorem f44_f {f : Rflags} {n l : BitVec 32}
    (h : (subF f (BitVec.setWidth 32 (BitVec.setWidth 64 n)) (BitVec.setWidth 32 (BitVec.setWidth 64 l))).cond 6 =
      false) : l.toNat < n.toNat := by
  rw [sw32, sw32, cond_6, subF_cf, subF_zf] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  have h2 : n.toNat ≠ l.toNat := fun e => h.2 (BitVec.eq_of_toNat_eq e)
  omega

/-- `add rsp, 8` back from `gq`. -/
theorem gq_back (V : Addr → Byte) (g : Gprs) (n : BitVec 32) (d : BitVec 64) :
    { gq V g n d with rsp := (gq V g n d).rsp + 8#64 } =
      { g with rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rdx := d, rsi := BitVec.setWidth 64 n } := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  show Gprs.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = Gprs.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  congr 1
  all_goals first | rfl | exact BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8; mov eax, [rdi + 8]; …; cmp esi, 0x3ffffffe; ja 37; cmp eax, esi; jbe 42`: to 37, or to 42 with
`next` not above `0x3ffffffe`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (h37 : ∀ (d s : BitVec 64) fl, Q 37
      { g with rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rdx := d, rsp := g.rsp - 8#64, rsi := s } fl V)
    (h42 : ∀ (d : BitVec 64) (n : BitVec 32), n.toNat ≤ 1073741822 → ∀ fl, Q 42 (gq V g n d) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 h37 ⊢
  wpx [W_0, W_33, o0, o1]
  all_goals repeat' (first | with_reducible exact f8 | apply And.intro | intro _)
  all_goals first
    | exact h37 _ _ _
    | exact h42 _ _ (lim_le (by assumption)) _

/-- `mov esi, 0x3ffffffe` to 42. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 42 { g with rsi := BitVec.setWidth 64 1073741822#32 } fl V) : W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_37, o2]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- `cmp esi, eax` to the `jbe` at 44. -/
theorem vc_42 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : Q 44 g (subF (rfz f) (BitVec.setWidth 32 g.rsi) (BitVec.setWidth 32 g.rax)) V) : W_42 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_42, o3]
  all_goals repeat' (first | exact h | apply And.intro | intro _)

/-- `add rsp, 8` to the jump at 54. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 54 { g with rsp := g.rsp + 8#64 } fl V) : W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_50, o4]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Grow_1 ()` (`this` = `rdi`) from its entry, no byte written. With `next` computed from `_len` (the 4
bytes at `this + 8`): at the throw stub `0x401372` with the registers `gq` when `next <= _len` (`kt`), else at
`AString::ReAlloc`'s entry with `esi` = `next`, `_len < next <= 0x3ffffffe`, `rsp` as at the entry (`kf`). -/
theorem ag1_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ag1_at ag1) (hinR : CodeIn L Arl.arl_at Arl.arl)
    {codeT : List Byte} (hinT : CodeIn L 0x401372#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ag1_at)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (kt : ∀ (Y : State) (t' : Nat) (d : BitVec 64) (n : BitVec 32),
      n.toNat ≤ (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 0x401372#64 → Y.cpu.gpr = gq V X.cpu.gpr n d → GoG prof L o gev gP gE Y t')
    (kf : ∀ (Y : State) (t' : Nat) (d : BitVec 64) (n : BitVec 32),
      (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat → n.toNat ≤ 1073741822 → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = Arl.arl_at →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rdx := d, rsi := BitVec.setWidth 64 n } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- from 42: the `jbe` to the throw stub, else `add rsp, 8` and the tail jump
  have k42 : ∀ (d : BitVec 64) (n : BitVec 32), n.toNat ≤ 1073741822 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = ag1_at.add 42 → Y.cpu.gpr = gq V X.cpu.gpr n d →
      GoG prof L o gev gP gE Y t' := by
    intro d n hn Y t₁ hKY hAY hrY hgY
    refine (c_42 prof).run c hin (fun j' g' f' V' => j' = 44 ∧ g' = gq V X.cpu.gpr n d ∧ V' = V ∧
        f' = subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 n))
          (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64))))
      hKY hAY hrY (by rw [hgY]; exact vc_42 ⟨rfl, rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV, hfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂
    subst hg hfl; subst V₁
    refine c.s_jcc_x hK₂ hA₂ hin (lt_len (by decide)) hr₂ (jbe_44 _) hinT (tgt := 0) hT tgt_44 ?_ ?_
    · intro hc
      rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
      have hc' : (subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 n))
          (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))).cond 6 = true := by
        rw [← hf₂]; exact hc
      exact kt Y₃ t₃ d n (f44_t hc') hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (hg₃.trans hg₂)
    · intro hc
      rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
      have hc' : (subF (rfz Y.cpu.rflags) (BitVec.setWidth 32 (BitVec.setWidth 64 n))
          (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64)))).cond 6 = false := by
        rw [← hf₂]; exact hc
      have hlt := f44_f hc'
      refine (c_50 prof).run c hin (fun j' g' _ V' => j' = 54 ∧
          g' = { X.cpu.gpr with
            rax := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rdx := d, rsi := BitVec.setWidth 64 n } ∧
          V' = V)
        hK₃ hA₃ hr₃ (by rw [hg₃, hg₂]; exact vc_50 fun _ => ⟨rfl, gq_back V X.cpu.gpr n d, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
      subst hg; subst V₁
      refine c.s_jmp_x hK₄ hA₄ hin (lt_len (by decide)) hr₄ (jmp_54 _) hinR (Arl.lt_len (j := 0) (by decide))
        (by decide) ?_
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      exact kf Y₅ t₅ d n hlt hn hK₅ hA₅ (by rw [hr₅, addr_add_zero]) (hg₅.trans hg₄)
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 37 ∧ ∃ d s : BitVec 64, g' = { X.cpu.gpr with
          rax := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rdx := d, rsp := X.cpu.gpr.rsp - 8#64,
          rsi := s }) ∨
        (j' = 42 ∧ ∃ (d : BitVec 64) (n : BitVec 32), n.toNat ≤ 1073741822 ∧ g' = gq V X.cpu.gpr n d)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f8 (fun d s _ => ⟨rfl, Or.inl ⟨rfl, d, s, rfl⟩⟩)
      (fun d n hn _ => ⟨rfl, Or.inr ⟨rfl, d, n, hn, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, d, s, hg⟩ | ⟨rfl, d, n, hn, hg⟩
  · subst hg
    refine (c_37 prof).run c hin (fun j' g' _ V' => j' = 42 ∧ g' = gq V X.cpu.gpr 1073741822#32 d ∧ V' = V)
      hKY hAY hrY (by rw [hgY]; exact vc_37 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst hg; subst V₁
    exact k42 d 1073741822#32 (by decide) Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  · subst hg
    exact k42 d n hn Y t₁ hKY hAY hrY hgY

end FV7z.Ag1
