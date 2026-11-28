import FV7z.Uad.Cuts
import FV7z.Ndp.Holds
/-!
# `UString::Add_Dot` (PLAN.md §M, M1)

7-Zip 26.06's `UString::Add_Dot ()` at `0x44d9b0` in `7zzs` (`CPP/Common/MyString.cpp`), the string at `p` = `rdi`
(`Rfw.chs`, `Rfw.len`: the characters, the length): `push rbx; mov eax, [rdi + 8]; mov rbx, rdi; cmp [rdi + 0xc], eax;
je 48` (`_len` = `_limit`); at 16 the stores: `mov rcx, [rbx]; lea edx, [rax + 1]; mov dword [rcx + rax*4], '.';
mov eax, edx; mov dword [rcx + rax*4], 0; mov [rbx + 8], edx; pop rbx; ret` (42). At 48 the `call` of
`UString::Grow_1` (`Ug1.ug1_at`); at 53 `mov eax, [rbx + 8]; jmp 16` (the length read again; the characters are read
at 16).

The bytes from the `push` on are `Vb` (`rbx` saved 8 below the entry's `rsp`). The callee is a hypothesis (`k1`), as in
`FV7z/Ndp/Holds.lean`: a continuation at its entry, given the run from its return (`rsp` 8 below the entry's,
`rbx` = `p`, the other callee-saved registers as they were, `Room` for the stores, the saved `rbx` and the return
address left by the stores, and the callee's own post `P1`).

- `KS`: `rbp`, `r12`..`r15` as they were; `KSb`: and `rbx`.
- `P16`: the registers at 16 (`rax` the length zero-extended, `rbx` = `p`, `rsp` 8 below the entry's).
- `Out`: the bytes after the stores: '.' at the end, then 0, the length plus 1 (`Ndp.Room` their footprint).
- `vc_0`, `vc_16`, `vc_53`: the verification conditions of the three pieces; `tail16`: from 16 to the return.
- `uad_ok`: from the entry to the return address with `rsp` 8 above the entry's, the callee-saved registers as they
  were and the bytes `Out` of `Vb`, or `Out` of `Grow_1`'s.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len lea4)
open FV7z.Ndp (Room inc32)
namespace FV7z.Uad

/-- The `call` of `UString::Grow_1`. -/
def pc1 : List Byte := [0xe8, 0xbb, 0xf6, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709549243] 5) := by dec_rfl
theorem wc_48 : pc1 <+: uad.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat uad 48 (FV7z.mk .call 64 [.rel 18446744073709549243] 5) :=
  Dec.shift (j := 48) (k := 0) (pc1_0 feat) wc_48 (Nat.zero_le _)
theorem tgt_48 : uad_at.add (48 + 5) + BitVec.ofNat 64 18446744073709549243 = Ug1.ug1_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_42 : pret <+: uad.drop 42 := by decide +kernel
theorem ret_42 (feat : Features) : Dec feat uad 42 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 42) (k := 0) (pret_0 feat) w_42 (Nat.zero_le _)

theorem q16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega

/-! ## The pieces -/

/-- `rbp`, `r12`..`r15` as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The callee-saved registers as they were. -/
abbrev KSb (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ KS g g'

/-- The bytes after the `push`: `rbx` saved 8 below `rsp`. -/
abbrev Vb (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The registers at 16, the string at `p` in the bytes `W`, `S` the entry's `rsp`, `g₀` the entry's registers. -/
abbrev P16 (W : Addr → Byte) (p S : Addr) (g₀ g : Gprs) : Prop :=
  g.rax = BitVec.setWidth 64 (len W p) ∧ g.rbx = p ∧ g.rsp = S - 8 ∧ KS g₀ g

/-- The bytes after the stores at 16: '.' at the end, 0 after it, the length plus 1. -/
abbrev Out (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (Addr.add (chs W p) (4 * (len W p).toNat)) (toBytesLE 46#32 4))
      (Addr.add (chs W p) (4 * (len W p + 1#32).toNat)) (toBytesLE 0#32 4))
    (p + 8#64) (toBytesLE (len W p + 1#32) 4)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the `push`, the length, to the stores at 16 or the `call` at 48. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (h16 : ∀ g', P16 (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi g.rsp g g' →
      ∀ fl, Q 16 g' fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)))
    (h48 : ∀ g', g'.rsp = g.rsp - 8 → g'.rbx = g.rdi → g'.rdi = g.rdi → KS g g' →
      ∀ fl, Q 48 g' fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 f8 f12 h16 h48 ⊢
  wpx [W_0, o0, Op.cmpmr]
  all_goals repeat' (first
    | refine h16 _ ?_ _
    | refine h48 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact f8
    | with_reducible exact f12
    | apply And.intro
    | intro _)

/-- The stores at 16, then `pop rbx` to the `ret` at 42. -/
theorem vc_16 {g : Gprs} {f : Rflags} {W : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hP : P16 W p S g₀ g) (hR : Room Wl W p) (hb : rdq(Out W p, S - 8) = g₀.rbx)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (fb : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (h : ∀ g', g'.rsp = S → KSb g₀ g' → ∀ fl, Q 42 g' fl (Out W p)) :
    W_16 F Wl Q g f W := by
  obtain ⟨hax, hbx, hsp, hk⟩ := hP
  have ha : BitVec.setWidth 32 g.rax = len W p := by rw [hax]; exact sw_64_32 _
  have e2 := inc32 ha
  have e1 : rdq(W, p) + g.rax * 4#64 = Addr.add (chs W p) (4 * (len W p).toNat) := by
    rw [hax]
    exact lea4 _ _
  dsimp only [Out] at hb
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hbx hsp k1 k2 k3 k4 k5 ha e1 e2
  subst hbx hsp
  wpx [W_16, o1]
  simp only [e1, e2, lea4, hb, BitVec.sub_add_cancel]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | with_reducible exact fp
    | with_reducible exact fb
    | apply And.intro
    | intro _)

/-- Back from `Grow_1` at 53: the length again, to 16. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hS : g.rsp = S - 8) (hb : g.rbx = p) (hk : KS g₀ g) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (h : ∀ g', P16 V p S g₀ g' → ∀ fl, Q 16 g' fl V) :
    W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  dsimp only at hS hb k1 k2 k3 k4 k5
  subst hS hb
  wpx [W_53, o2]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
    | with_reducible exact f8
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 16 (the registers `P16`, the bytes `W`) to the return address with the bytes `Out`. -/
theorem tail16 {W : Addr → Byte} {p S : Addr} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L uad_at uad) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = uad_at.add 16) (hP : P16 W p S g₀ Y.cpu.gpr) (hR : Room Wl W p)
    (hb : rdq(Out W p, S - 8) = g₀.rbx) (fp : ∀ i < 8, Foot F.data (Addr.add p i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(Out W p, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Out W p) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KSb g₀ Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_16 prof).run c hin (fun j' g' _ V' => j' = 42 ∧ g'.rsp = S ∧ KSb g₀ g' ∧ V' = Out W p) hK hA hrY
    (vc_16 hP hR hb fp fb fun _ hs hk _ => ⟨rfl, hs, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, hk, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_42 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact hk

/-- `UString::Add_Dot ()` (`p` = `rdi`) from its entry. Either straight to the stores (room left) and to the return
address with `Out` of the bytes after the `push` (`Vb`), or through `Grow_1` (`k1`: at its entry with `rsp` 16 below
the entry's, `rdi` = `rbx` = `p`; from its return as above) to the return address with `Out` of the bytes `Grow_1`
left (`kr`, with `P1`). -/
theorem uad_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uad_at uad)
    (hinG : CodeIn L Ug1.ug1_at Ug1.ug1)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uad_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hR : Room Wl (Vb V X.cpu.gpr) X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hb1 : rdq(Out (Vb V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx)
    (hr1 : rdq(Out (Vb V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vb V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (uad_at.add 53) 8)) →
      Y.cpu.rip = Ug1.ug1_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 16 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rbx = X.cpu.gpr.rdi → KS X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = uad_at.add 53 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        KS X.cpu.gpr Z.cpu.gpr → Room Wl V' X.cpu.gpr.rdi →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KSb X.cpu.gpr Z'.cpu.gpr →
      (W = Out (Vb V X.cpu.gpr) X.cpu.gpr.rdi ∨ ∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧ W = Out V' X.cpu.gpr.rdi) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hb8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 16 ∧ V' = Vb V X.cpu.gpr ∧ P16 (Vb V X.cpu.gpr) X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g') ∨
      (j' = 48 ∧ V' = Vb V X.cpu.gpr ∧ g'.rsp = X.cpu.gpr.rsp - 8 ∧ g'.rbx = X.cpu.gpr.rdi ∧
        g'.rdi = X.cpu.gpr.rdi ∧ KS X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 (by exact fun i hi => c.hws _ (hR.2.2 i hi)) f12
      (fun _ hP _ => Or.inl ⟨rfl, rfl, hP⟩)
      (fun _ hs hb hd hk _ => Or.inr ⟨rfl, rfl, hs, hb, hd, hk⟩)) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hs, hb, hd, hk⟩
  · -- the stores at 16 in place
    exact tail16 c hin hKY hAY hrY hP hR hb1 fp hb8 hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs hk (Or.inl rfl)
  · -- `Grow_1`, then the stores at 16 in its buffer
    have hY16 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hs]; exact q16 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_48 _) hinG (tgt := 0) (Ug1.lt_len (by decide))
      tgt_48 (by rw [hY16]; exact hs2) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY16] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY16) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hb) (by rw [hg₂]; exact hk) ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzk hR' hb' hr' hP1
    refine (c_53 prof).run c hin
      (fun j' g' _ V'' => j' = 16 ∧ V'' = V' ∧ P16 V' X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g')
      hKZ hAZ hrZ (vc_53 hzs hzb hzk (by exact fun i hi => c.hws _ (hR'.2.2 i hi))
        fun _ hP _ => ⟨rfl, rfl, hP⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hP⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    exact tail16 c hin hKU hAU hrU hP hR' hb' fp hb8 hl hin₂ h₂ hr' fun Z' t₄ hKZ' hAZ' hrZ' hs hk =>
      kr _ Z' t₄ hKZ' hAZ' hrZ' hs hk (Or.inr ⟨Z, _, hP1, rfl⟩)

end FV7z.Uad
