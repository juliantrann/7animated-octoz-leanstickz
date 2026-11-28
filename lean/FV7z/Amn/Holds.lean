import FV7z.Amn.Cuts
import FV7z.Ag1.Blocks
import FV7z.Rfw.Holds
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `AString::Add_Minus` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Add_Minus ()` at `0x44c810` in `7zzs` (`CPP/Common/MyString.cpp`), the string at `p` = `rdi`
(`Rfw.chs`, `Rfw.len`: the characters at `p`, the length at `p + 8`; 1-byte characters here): `push rbx; mov eax,
[rdi + 8]; mov rbx, rdi; cmp [rdi + 0xc], eax; je 40` (`_len` = `_limit`); at 16 the stores: `mov rcx, [rbx]; lea edx,
[rax + 1]; mov byte [rcx + rax], '-'; mov eax, edx; mov byte [rcx + rax], 0; mov [rbx + 8], edx; pop rbx; ret` (36).
At 40 the `call` of `AString::Grow_1` (`Ag1.ag1_at`); at 45 `mov eax, [rbx + 8]; jmp 16` (the length read again).

The callee is a hypothesis (`k1`), as in `FV7z/Ndp/Holds.lean`: a continuation at its entry, given the run from its
return (`rsp` 8 below the entry's, `rbx` = `p` and the other callee-saved registers as they were, `Room` for the stores
in the new buffer, the return address and the saved `rbx` left by the stores, and the callee's own post `P1`). The
bytes from the entry on are `Fr`: the entry's with `rbx` pushed; the loads at 0 read them. The saved `rbx` comes back
by the `pop` only if the stores leave it (`hb1`, and the like in `k1`), as the return address (`hr1`).

- `K5`: the callee-saved registers but `rbx` as they were; `KS`: all six.
- `Fr`: the bytes after `push rbx`.
- `P16`: the registers at 16 (`eax` the length, `rbx` = `p`).
- `Out`: the bytes after the stores at 16: the character `c` at the end, then 0, the length plus 1.
- `Room`: the footprint of those stores.
- `vc_0`, `vc_16`, `vc_45`: the verification conditions of the three pieces; `tail16`: from 16 to the return.
- `amn_ok`: from the entry to the return address with `rsp` 8 above the entry's, the callee-saved registers as they
  were, and `Out` of `Fr`, or `Out` of `Grow_1`'s bytes.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len)
namespace FV7z.Amn

/-- The `call` of `AString::Grow_1`. -/
def pc1 : List Byte := [0xe8, 0x63, 0xf8, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709549667] 5) := by dec_rfl
theorem wc_40 : pc1 <+: amn.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat amn 40 (FV7z.mk .call 64 [.rel 18446744073709549667] 5) :=
  Dec.shift (j := 40) (k := 0) (pc1_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : amn_at.add (40 + 5) + BitVec.ofNat 64 18446744073709549667 = Ag1.ag1_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_36 : pret <+: amn.drop 36 := by decide +kernel
theorem ret_36 (feat : Features) : Dec feat amn 36 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem inc32z (n : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 n + 1#64) = n + 1#32 := by
  bv_omega

theorem sa8 (s : BitVec 64) : s - 8 + 8 = s := by bv_omega
theorem q16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega

/-! ## The pieces -/

/-- The callee-saved registers but `rbx` as they were. -/
abbrev K5 (g g' : Gprs) : Prop :=
  g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ K5 g g'

/-- The bytes after `push rbx`. -/
abbrev Fr (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The registers at 16, the string at `p` in the bytes `W`, `S` the entry's `rsp`, `g₀` the entry's registers. -/
abbrev P16 (W : Addr → Byte) (p S : Addr) (g₀ g : Gprs) : Prop :=
  g.rax = BitVec.setWidth 64 (len W p) ∧ g.rbx = p ∧ g.rsp = S - 8 ∧ K5 g₀ g

/-- The bytes after the stores at 16: `c` at the end, 0 after it, the length plus 1. -/
abbrev Out (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (chs W p + BitVec.setWidth 64 (len W p)) (toBytesLE (BitVec.ofNat 8 45) 1))
      (chs W p + BitVec.setWidth 64 (len W p + 1#32)) (toBytesLE (BitVec.ofNat 8 0) 1))
    (p + 8#64) (toBytesLE (len W p + 1#32) 4)

/-- The footprint of the stores at 16: writable. -/
abbrev Room (Wl : List Rgn) (W : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p)) i)) ∧
    (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p + 1#32)) i)) ∧
    ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `push rbx`, then the stores at 16, or the `call` at 40. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (h16 : ∀ g', P16 (Fr V g) g.rdi g.rsp g g' → ∀ fl, Q 16 g' fl (Fr V g))
    (h40 : ∀ g', g'.rbx = g.rdi → g'.rdi = g.rdi → g'.rsp = g.rsp - 8 → K5 g g' → ∀ fl, Q 40 g' fl (Fr V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs f8 f12 h16 h40 ⊢
  wpx [W_0, o0, Op.cmpmr]
  all_goals repeat' (first
    | refine h16 _ ?_ _
    | refine h40 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs
    | with_reducible exact f8
    | with_reducible exact f12
    | apply And.intro
    | intro _)

/-- The stores at 16, then `pop rbx` to the `ret` at 36. -/
theorem vc_16 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hP : P16 V p S g₀ g) (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (hR : Room Wl V p)
    (fb : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (h : ∀ g', g'.rsp = S → g'.rbx = rdq(Out V p, S - 8) → K5 g₀ g' → ∀ fl, Q 36 g' fl (Out V p)) :
    W_16 F Wl Q g f V := by
  obtain ⟨ha, hb, hsp, hk⟩ := hP
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hb hsp hk
  subst ha hb hsp
  wpx [W_16, o1, inc32z]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact sa8 _
    | with_reducible exact hk
    | with_reducible exact fp
    | with_reducible exact fb
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | apply And.intro
    | intro _)

/-- Back from `Grow_1` at 45: the length again, to 16. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hb : g.rbx = p) (hS : g.rsp = S - 8) (hk : K5 g₀ g) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (h : ∀ g', P16 V p S g₀ g' → ∀ fl, Q 16 g' fl V) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  dsimp only at hb hS k1 k2 k3 k4 k5
  subst hb hS
  wpx [W_45, o2]
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
    (hin : CodeIn L amn_at amn) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = amn_at.add 16) (hP : P16 W p S g₀ Y.cpu.gpr) (hR : Room Wl W p)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (fb : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(Out W p, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Out W p) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → Z'.cpu.gpr.rbx = rdq(Out W p, S - 8) → K5 g₀ Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_16 prof).run c hin
    (fun j' g' _ V' => j' = 36 ∧ g'.rsp = S ∧ g'.rbx = rdq(Out W p, S - 8) ∧ K5 g₀ g' ∧ V' = Out W p) hK hA hrY
    (vc_16 hP fp hR fb fun _ hs hb hk _ => ⟨rfl, hs, hb, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, hb, hk, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_36 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact hb
  · rw [hgZ']
    exact hk

/-- `Add_Minus ()` (`p` = `rdi`) from its entry. Either straight to the return address with `Out` of `Fr` (room left),
or through `Grow_1` (`k1`: at its entry with `rsp` 16 below the entry's, `rbx` = `p`; from its return as above) to the
return address with `Out` of the bytes `Grow_1` left (`kr`, with `P1`). -/
theorem amn_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amn_at amn)
    (hinG : CodeIn L Ag1.ag1_at Ag1.ag1)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amn_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hR : Room Wl (Fr V X.cpu.gpr) X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr1 : rdq(Out (Fr V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (hb1 : rdq(Out (Fr V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Fr V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (amn_at.add 45) 8)) →
      Y.cpu.rip = Ag1.ag1_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 16 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rbx = X.cpu.gpr.rdi → K5 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = amn_at.add 45 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        K5 X.cpu.gpr Z.cpu.gpr → Room Wl V' X.cpu.gpr.rdi →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (W = Out (Fr V X.cpu.gpr) X.cpu.gpr.rdi ∨ ∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧ W = Out V' X.cpu.gpr.rdi) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 16 ∧ V' = Fr V X.cpu.gpr ∧ P16 (Fr V X.cpu.gpr) X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g') ∨
      (j' = 40 ∧ V' = Fr V X.cpu.gpr ∧ g'.rbx = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi ∧
        g'.rsp = X.cpu.gpr.rsp - 8 ∧ K5 X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 (by exact fun i hi => c.hws _ (hR.2.2 i hi)) f12
      (fun _ hP _ => Or.inl ⟨rfl, rfl, hP⟩)
      (fun _ hb hd hs hk _ => Or.inr ⟨rfl, rfl, hb, hd, hs, hk⟩)) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hb, hd, hs, hk⟩
  · -- the stores at 16 in place
    exact tail16 c hin hKY hAY hrY hP hR fp fb hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs hb hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs ⟨hb.trans hb1, hk⟩ (Or.inl rfl)
  · -- `Grow_1`, then the stores at 16 in its buffer
    have hY16 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hs]; exact q16 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_40 _) hinG (tgt := 0) (Ag1.lt_len (by decide))
      tgt_40 (by rw [hY16]; exact hs2) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY16] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY16) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hb) (by rw [hg₂]; exact hk) ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzk hR' hr' hb' hP1
    refine (c_45 prof).run c hin
      (fun j' g' _ V'' => j' = 16 ∧ V'' = V' ∧ P16 V' X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g')
      hKZ hAZ hrZ (vc_45 hzb hzs hzk (by exact fun i hi => c.hws _ (hR'.2.2 i hi))
        fun _ hP _ => ⟨rfl, rfl, hP⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hP⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    exact tail16 c hin hKU hAU hrU hP hR' fp fb hl hin₂ h₂ hr' fun Z' t₄ hKZ' hAZ' hrZ' hs hb hk =>
      kr _ Z' t₄ hKZ' hAZ' hrZ' hs ⟨hb.trans hb', hk⟩ (Or.inr ⟨Z, _, hP1, rfl⟩)

end FV7z.Amn
