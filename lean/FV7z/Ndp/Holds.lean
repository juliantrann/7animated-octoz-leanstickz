import FV7z.Ndp.Cuts
import FV7z.Ug1.Blocks
import FV7z.Rfw.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `NormalizeDirPathPrefix` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NName::NormalizeDirPathPrefix (FString &dirPath)` at `0x4568a0` in `7zzs`
(`CPP/Windows/FileName.cpp`; `FString` is `UString` here: 4-byte characters), the string at `p` = `rdi`
(`Rfw.chs`, `Rfw.len`: the characters, the length): `mov eax, [rdi + 8]; test eax, eax; je 31` (empty: the `ret` at
31); `mov rdx, [rdi]; mov ecx, eax; lea rsi, [rcx*4]; cmp dword [rdx + rcx*4 - 4], '/'; jne 32` (else the `ret` at 31);
`sub rsp, 0x18; cmp eax, [rdi + 0xc]; je 72` (`_len` = `_limit`); at 41 `Add_PathSepar`'s stores: `lea ecx, [rax + 1];
mov dword [rdx + rsi], '/'; mov dword [rdx + rcx*4], 0; mov [rdi + 8], ecx; add rsp, 0x18; ret` (65). At 72
`mov [rsp + 8], rdi`, the `call` (77) of `UString::Grow_1` (`Ug1.ug1_at`); at 82 `mov rdi, [rsp + 8]; mov esi,
[rdi + 8]; mov rdx, [rdi]; mov rax, rsi; shl rsi, 2; jmp 41` (the length and the characters read again).

The callee is a hypothesis (`k1`), as in `FV7z/Upe/Holds.lean`: a continuation at its entry, given the run from its
return (`rsp` 24 below the entry's, the callee-saved registers and the saved `p` as they were, `Room` for the
stores in the new buffer, the return address left by the stores, and the callee's own post `P1`). No flag fact is
kept: the post says which bytes the run may leave, not when.

- `KS`: the callee-saved registers as they were.
- `P41`: the registers at 41 (`rdx` the characters, `rdx + rsi` the end, `eax` the length).
- `Out`: the bytes after `Add_PathSepar`'s stores: '/' at the end, then 0, the length plus 1.
- `Room`: the footprint of those stores.
- `vc_0`, `vc_41`, `vc_82`: the verification conditions of the three pieces; `tail41`: from 41 to the return.
- `ndp_ok`: from the entry to the return address with `rsp` 8 above the entry's, the callee-saved registers as they
  were and the bytes as they were, or `Out` of them, or `Out` of `Grow_1`'s.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len lea4)
namespace FV7z.Ndp

/-- The `call` of `UString::Grow_1`. -/
def pc1 : List Byte := [0xe8, 0xae, 0x67, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709512622] 5) := by dec_rfl
theorem wc_77 : pc1 <+: ndp.drop 77 := by decide +kernel
theorem call_77 (feat : Features) : Dec feat ndp 77 (FV7z.mk .call 64 [.rel 18446744073709512622] 5) :=
  Dec.shift (j := 77) (k := 0) (pc1_0 feat) wc_77 (Nat.zero_le _)
theorem tgt_77 : ndp_at.add (77 + 5) + BitVec.ofNat 64 18446744073709512622 = Ug1.ug1_at.add 0 := by decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_31 : pret <+: ndp.drop 31 := by decide +kernel
theorem ret_31 (feat : Features) : Dec feat ndp 31 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 31) (k := 0) (pret_0 feat) w_31 (Nat.zero_le _)
theorem w_65 : pret <+: ndp.drop 65 := by decide +kernel
theorem ret_65 (feat : Features) : Dec feat ndp 65 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 65) (k := 0) (pret_0 feat) w_65 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem inc32 {r : BitVec 64} {n : BitVec 32} (h : BitVec.setWidth 32 r = n) :
    BitVec.setWidth 32 (r + 1#64) = n + 1#32 := by
  subst h
  bv_omega

theorem shl4a (s : Addr) (x : BitVec 32) : s + BitVec.setWidth 64 x <<< 2 = Addr.add s (4 * x.toNat) := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  omega

theorem sa24 (s : BitVec 64) : s - 24#64 + 24#64 = s := by bv_omega
theorem q16 (s : BitVec 64) : s - 24#64 + 8#64 = s - 16 := by bv_omega
theorem q32 (s : BitVec 64) : s - 24#64 - 8 = s - 32 := by bv_omega

/-! ## The pieces -/

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The registers at 41, the string at `p` in the bytes `W`, `S` the entry's `rsp`, `g₀` the entry's registers. -/
abbrev P41 (W : Addr → Byte) (p S : Addr) (g₀ g : Gprs) : Prop :=
  g.rdx = chs W p ∧ g.rdx + g.rsi = Addr.add (chs W p) (4 * (len W p).toNat) ∧ BitVec.setWidth 32 g.rax = len W p ∧
    g.rdi = p ∧ g.rsp = S - 24#64 ∧ KS g₀ g

/-- The bytes after the stores at 41: '/' at the end, 0 after it, the length plus 1. -/
abbrev Out (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (Addr.add (chs W p) (4 * (len W p).toNat)) (toBytesLE 47#32 4))
      (Addr.add (chs W p) (4 * (len W p + 1#32).toNat)) (toBytesLE 0#32 4))
    (p + 8#64) (toBytesLE (len W p + 1#32) 4)

/-- The footprint of the stores at 41: writable. -/
abbrev Room (Wl : List Rgn) (W : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 4, Foot Wl (Addr.add (Addr.add (chs W p) (4 * (len W p).toNat)) i)) ∧
    (∀ i < 4, Foot Wl (Addr.add (Addr.add (chs W p) (4 * (len W p + 1#32).toNat)) i)) ∧
    ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the `ret` at 31, the stores at 41, or the `call` at 77 with `p` saved at `rsp + 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fl : ∀ i < 4, Foot F.data
      (Addr.add (chs V g.rdi + BitVec.setWidth 64 (len V g.rdi) * 4#64 + 18446744073709551612#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 24#64 + 8#64) i))
    (h31 : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 31 g' fl V)
    (h41 : ∀ g', P41 V g.rdi g.rsp g g' → ∀ fl, Q 41 g' fl V)
    (h77 : ∀ g', g'.rsp = g.rsp - 24#64 → g'.rdi = g.rdi → KS g g' →
      ∀ fl, Q 77 g' fl (Vst V (g.rsp - 24#64 + 8#64) (toBytesLE g.rdi 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 fp fl f12 hs2 h31 h41 h77 ⊢
  wpx [W_0, W_11, W_32, W_72, o0, o1, o2, o4, Op.cmpmi]
  all_goals repeat' (first
    | refine h31 _ ?_ ?_ _
    | refine h41 _ ?_ _
    | refine h77 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact lea4 _ _
    | exact sw_64_32 _
    | with_reducible exact f8
    | with_reducible exact fp
    | with_reducible exact fl
    | with_reducible exact f12
    | with_reducible exact hs2
    | apply And.intro
    | intro _)

/-- The stores at 41, then `add rsp, 0x18` to the `ret` at 65. -/
theorem vc_41 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hP : P41 V p S g₀ g) (hR : Room Wl V p) (h : ∀ g', g'.rsp = S → KS g₀ g' → ∀ fl, Q 65 g' fl (Out V p)) :
    W_41 F Wl Q g f V := by
  obtain ⟨hd, hs, ha, hp, hsp, hk⟩ := hP
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hs ha hp hsp hk
  subst hp hsp hd
  have e2 := inc32 ha
  wpx [W_41, o3]
  simp only [hs, e2, lea4]
  repeat' (first
    | exact h _ (sa24 _) (by exact hk) _
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | apply And.intro
    | intro _)

/-- Back from `Grow_1` at 82: `p` from `rsp + 8`, its length and characters again, to 41. -/
theorem vc_82 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hS : g.rsp = S - 24#64) (hk : KS g₀ g) (hz : rdq(V, g.rsp + 8#64) = p)
    (fs : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (h : ∀ g', P41 V p S g₀ g' → ∀ fl, Q 41 g' fl V) :
    W_82 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  dsimp only at hS k1 k2 k3 k4 k5 k6 hz fs
  subst hS
  wpx [W_82, o5, Op.shl64]
  simp only [hz]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | exact shl4a _ _
    | exact sw_64_32 _
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact k5
    | with_reducible exact k6
    | with_reducible exact fs
    | with_reducible exact f8
    | with_reducible exact fp
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 41 (the registers `P41`, the bytes `W`) to the return address with the bytes `Out`. -/
theorem tail41 {W : Addr → Byte} {p S : Addr} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L ndp_at ndp) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = ndp_at.add 41) (hP : P41 W p S g₀ Y.cpu.gpr) (hR : Room Wl W p)
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(Out W p, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Out W p) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g₀ Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_41 prof).run c hin (fun j' g' _ V' => j' = 65 ∧ g'.rsp = S ∧ KS g₀ g' ∧ V' = Out W p) hK hA hrY
    (vc_41 hP hR fun _ hs hk _ => ⟨rfl, hs, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, hk, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_65 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact hk

/-- `NormalizeDirPathPrefix (dirPath)` (`p` = `rdi`) from its entry. Either straight to the return address with
the bytes as they were (empty, or '/' at the end) or `Out` of them (room left), or through `Grow_1` (`k1`: at its
entry with `rsp` 32 below the entry's and `p` saved at `rsp` - 16; from its return as above) to the return address
with `Out` of the bytes `Grow_1` left (`kr`, with `P1`). -/
theorem ndp_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ndp_at ndp)
    (hinG : CodeIn L Ug1.ug1_at Ug1.ug1)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ndp_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (chs V X.cpu.gpr.rdi +
      BitVec.setWidth 64 (len V X.cpu.gpr.rdi) * 4#64 + 18446744073709551612#64) i))
    (hR : Room Wl V X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hr1 : rdq(Out V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE X.cpu.gpr.rdi 8)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (ndp_at.add 82) 8)) →
      Y.cpu.rip = Ug1.ug1_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      KS X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ndp_at.add 82 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 → KS X.cpu.gpr Z.cpu.gpr →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rdi → Room Wl V' X.cpu.gpr.rdi →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (W = V ∨ W = Out V X.cpu.gpr.rdi ∨ ∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧ W = Out V' X.cpu.gpr.rdi) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 31 ∧ V' = V ∧ g'.rsp = X.cpu.gpr.rsp ∧ KS X.cpu.gpr g') ∨
      (j' = 41 ∧ V' = V ∧ P41 V X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g') ∨
      (j' = 77 ∧ V' = Vst V (X.cpu.gpr.rsp - 24#64 + 8#64) (toBytesLE X.cpu.gpr.rdi 8) ∧
        g'.rsp = X.cpu.gpr.rsp - 24#64 ∧ g'.rdi = X.cpu.gpr.rdi ∧ KS X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by exact fun i hi => c.hws _ (hR.2.2 i hi)) fp fl f12 (by rw [q16]; exact hs2)
      (fun _ hs hk _ => Or.inl ⟨rfl, rfl, hs, hk⟩)
      (fun _ hP _ => Or.inr (Or.inl ⟨rfl, rfl, hP⟩))
      (fun _ hs hd hk _ => Or.inr (Or.inr ⟨rfl, rfl, hs, hd, hk⟩))) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hs, hk⟩ | ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hs, hd, hk⟩
  · -- the `ret` at 31, the bytes as they were
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_31 _) (by rw [hs]; exact hl) hin₂ h₂
      (by rw [hs]; exact hr) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr _ Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ (Or.inl rfl)
    · rw [hgZ']
      show Y.cpu.gpr.rsp + 8 = _
      rw [hs]
    · rw [hgZ']
      exact hk
  · -- the stores at 41 in place
    exact tail41 c hin hKY hAY hrY hP hR hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs hk (Or.inr (Or.inl rfl))
  · -- `Grow_1`, then the stores at 41 in its buffer
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs]; exact q32 _
    rw [q16] at hAY
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_77 _) hinG (tgt := 0) (Ug1.lt_len (by decide))
      tgt_77 (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hk) ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzk hb hR' hr' hP1
    refine (c_82 prof).run c hin
      (fun j' g' _ V'' => j' = 41 ∧ V'' = V' ∧ P41 V' X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g')
      hKZ hAZ hrZ (vc_82 hzs hzk (by rw [hzs, q16]; exact hb) (by rw [hzs, q16]; exact h16)
        (by exact fun i hi => c.hws _ (hR'.2.2 i hi)) fp
        fun _ hP _ => ⟨rfl, rfl, hP⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hP⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    exact tail41 c hin hKU hAU hrU hP hR' hl hin₂ h₂ hr' fun Z' t₄ hKZ' hAZ' hrZ' hs hk =>
      kr _ Z' t₄ hKZ' hAZ' hrZ' hs hk (Or.inr (Or.inr ⟨Z, _, hP1, rfl⟩))

end FV7z.Ndp
