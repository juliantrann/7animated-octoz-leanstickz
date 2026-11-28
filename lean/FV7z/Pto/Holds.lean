import FV7z.Pto.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `__pthread_once` (PLAN.md §M, M1)

glibc 2.31's `__pthread_once (once_control, init_routine)` at `0x5fefc0` in `7zzs` (`nptl/pthread_once.c`;
`objdump -d`): `mov eax, [rdi]; test al, 2; je 16`; with the word done (bit 1, `__PTHREAD_ONCE_DONE`) `xor eax, eax;
ret` (12), else a tail jump (16) to `0x5fee60` (`__pthread_once_slow`, `Pos.pos_at`, `FV7z/Pos/Holds.lean`; its code a
hypothesis, `hinT`) with `rax` the word.

- `gd`, `gs`: the registers at the `ret` and at the jump; `vc_0`: the code from the entry to either.
- `pto_ok`: from the entry: with the word done, to the return address with `rax` = 0 (`kd`); else at
  `__pthread_once_slow` with `rax` the word (`ks`); the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pto

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_12 : pret <+: pto.drop 12 := by decide +kernel
theorem ret_12 (feat : Features) : Dec feat pto 12 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 12) (k := 0) (pret_0 feat) w_12 (Nat.zero_le _)

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x8b, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) := by dec_rfl
theorem wj_16 : pjm <+: pto.drop 16 := by decide +kernel
theorem jmp_16 (feat : Features) : Dec feat pto 16 (FV7z.mk .jmp 64 [.rel 18446744073709551243] 5) :=
  Dec.shift (j := 16) (k := 0) (pjm_0 feat) wj_16 (Nat.zero_le _)

/-- `__pthread_once_slow` (`Pos.pos_at`; proved in `FV7z/Pos/Holds.lean`). -/
abbrev tgt_at : Addr := 0x5fee60
theorem tgt_16 : pto_at.add (16 + 5) + BitVec.ofNat 64 18446744073709551243 = tgt_at.add 0 := by decide

/-- The registers at the `ret`: `eax` = 0. -/
abbrev gd (g : Gprs) : Gprs := { g with rax := 0#64 }

/-- The registers at the jump: `rax` = the word `w`. -/
abbrev gs (g : Gprs) (w : BitVec 32) : Gprs := { g with rax := BitVec.setWidth 64 w }

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the word read and tested; done, `xor eax, eax` to the `ret` (12); else to the jump (16). -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h4 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (hd : (BitVec.setWidth 8 rdd(V, g.rdi) &&& 2#8 == 0) = false → ∀ fl, Q 12 (gd g) fl V)
    (hs : (BitVec.setWidth 8 rdd(V, g.rdi) &&& 2#8 == 0) = true → ∀ fl, Q 16 (gs g rdd(V, g.rdi)) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h4 hd hs
  cases hb : (BitVec.setWidth 8 rdd(V, rdi) &&& 2#8 == 0)
  · wpx [W_0, W_10, o0, o1, hb, xz, BitVec.reduceSetWidth]
    all_goals repeat' (first
      | exact hd hb _
      | with_reducible exact h4
      | (intro h; exact absurd h (by decide))
      | apply And.intro
      | intro _)
  · wpx [W_0, W_10, o0, o1, hb, xz, BitVec.reduceSetWidth]
    all_goals repeat' (first
      | exact hs hb _
      | with_reducible exact h4
      | (intro h; exact absurd h (by decide))
      | apply And.intro
      | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__pthread_once` from its entry, `w` the word at `rdi`: done (bit 1 set), to the return address with `rax` = 0
and `rsp` 8 above (`kd`); else at `__pthread_once_slow` with `rax` = `w` (`ks`). -/
theorem pto_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pto_at pto)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pto_at)
    (h4 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kd : (BitVec.setWidth 8 rdd(V, X.cpu.gpr.rdi) &&& 2#8 == 0) = false →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (gd X.cpu.gpr).set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t')
    (ks : (BitVec.setWidth 8 rdd(V, X.cpu.gpr.rdi) &&& 2#8 == 0) = true →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gs X.cpu.gpr rdd(V, X.cpu.gpr.rdi) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      (((BitVec.setWidth 8 rdd(V, X.cpu.gpr.rdi) &&& 2#8 == 0) = false ∧ j' = 12 ∧ g' = gd X.cpu.gpr) ∨
        ((BitVec.setWidth 8 rdd(V, X.cpu.gpr.rdi) &&& 2#8 == 0) = true ∧ j' = 16 ∧
          g' = gs X.cpu.gpr rdd(V, X.cpu.gpr.rdi))))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 h4 (fun hb _ => ⟨rfl, Or.inl ⟨hb, rfl, rfl⟩⟩) (fun hb _ => ⟨rfl, Or.inr ⟨hb, rfl, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases hpost with ⟨hb, rfl, hg⟩ | ⟨hb, rfl, hg⟩
  · -- done: the `ret`
    subst hg
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_12 _) (by rw [hgY]; exact hl) hin₂ h₂
      (by rw [hgY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kd hb Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  · -- not done: the tail jump
    subst hg
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_16 _) hinT (tgt := 0) hT tgt_16 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact ks hb Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Pto
