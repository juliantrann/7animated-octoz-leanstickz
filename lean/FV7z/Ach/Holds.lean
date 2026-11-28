import FV7z.Ach.Cuts
import FV7z.Ag1.Blocks
import FV7z.Rfw.Holds
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `AString::operator+= (char)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::operator+= (char c)` at `0x44c6a0` in `7zzs` (`CPP/Common/MyString.h`), the string at `p` =
`rdi`, `c` in `sil`: as `Add_Space` (`FV7z/Asp/Holds.lean`) with `c` kept in `ebp`: `push rbp; mov ebp, esi; push rbx;
mov rbx, rdi; sub rsp, 8; mov eax, [rdi + 8]; cmp [rdi + 0xc], eax; je 56`; at 23 the stores (`mov byte [rcx + rax],
bpl`, then 0, the length plus 1), `add rsp, 8; pop rbx; pop rbp; ret` (48); at 56 the `call` of `AString::Grow_1`
(`Ag1.ag1_at`), at 61 `mov eax, [rbx + 8]; jmp 23`.

The callee is a hypothesis (`k1`), as in `Asp`. The bytes from the entry on are `Fr`: `rbp` and `rbx` pushed. The
saved registers come back by the `pop`s only if the stores leave them (`hb1`, `hp1`, and the like in `k1`).

- `K4`: `r12`–`r15` as they were; `KS`: the six callee-saved registers.
- `Fr`: the bytes after the two `push`es.
- `P23`: the registers at 23 (`eax` the length, `rbx` = `p`, `rbp` = `r`, the character's register).
- `Out`: the bytes after the stores at 23: `ch` at the end, then 0, the length plus 1.
- `Room`: the footprint of those stores.
- `vc_0`, `vc_23`, `vc_61`: the verification conditions of the three pieces; `tail23`: from 23 to the return.
- `ach_ok`: from the entry to the return address with `rsp` 8 above the entry's, the callee-saved registers as they
  were, and `Out` of `Fr`, or `Out` of `Grow_1`'s bytes, with the low byte of `esi` as the character.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len)
namespace FV7z.Ach

/-- The `call` of `AString::Grow_1`. -/
def pc1 : List Byte := [0xe8, 0xc3, 0xf9, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709550019] 5) := by dec_rfl
theorem wc_56 : pc1 <+: ach.drop 56 := by decide +kernel
theorem call_56 (feat : Features) : Dec feat ach 56 (FV7z.mk .call 64 [.rel 18446744073709550019] 5) :=
  Dec.shift (j := 56) (k := 0) (pc1_0 feat) wc_56 (Nat.zero_le _)
theorem tgt_56 : ach_at.add (56 + 5) + BitVec.ofNat 64 18446744073709550019 = Ag1.ag1_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: ach.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat ach 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem inc32z (n : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 n + 1#64) = n + 1#32 := by
  bv_omega

theorem r24 (s : BitVec 64) : s - 8 - 8 - 8#64 = s - 24 := by bv_omega
theorem e16 (s : BitVec 64) : s - 24 + 8#64 = s - 16 := by bv_omega
theorem e8 (s : BitVec 64) : s - 16 + 8 = s - 8 := by bv_omega
theorem e0 (s : BitVec 64) : s - 8 + 8 = s := by bv_omega
theorem q16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega
theorem q32 (s : BitVec 64) : s - 24 - 8 = s - 32 := by bv_omega

/-! ## The pieces -/

/-- `r12`–`r15` as they were. -/
abbrev K4 (g g' : Gprs) : Prop := g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ K4 g g'

/-- The bytes after `push rbp; push rbx`. -/
abbrev Fr (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The character's register at 23: `esi` zero-extended. -/
abbrev cr (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers at 23, the string at `p` in the bytes `W`, `S` the entry's `rsp`, `r` the character's register,
`g₀` the entry's registers. -/
abbrev P23 (W : Addr → Byte) (p S r : Addr) (g₀ g : Gprs) : Prop :=
  g.rax = BitVec.setWidth 64 (len W p) ∧ g.rbx = p ∧ g.rbp = r ∧ g.rsp = S - 24 ∧ K4 g₀ g

/-- The bytes after the stores at 23: `ch` at the end, 0 after it, the length plus 1. -/
abbrev Out (ch : BitVec 8) (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (chs W p + BitVec.setWidth 64 (len W p)) (toBytesLE ch 1))
      (chs W p + BitVec.setWidth 64 (len W p + 1#32)) (toBytesLE (BitVec.ofNat 8 0) 1))
    (p + 8#64) (toBytesLE (len W p + 1#32) 4)

/-- The footprint of the stores at 23: writable. -/
abbrev Room (Wl : List Rgn) (W : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p)) i)) ∧
    (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p + 1#32)) i)) ∧
    ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the two `push`es, then the stores at 23, or the `call` at 56. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (h23 : ∀ g', P23 (Fr V g) g.rdi g.rsp (cr g) g g' → ∀ fl, Q 23 g' fl (Fr V g))
    (h56 : ∀ g', g'.rbx = g.rdi → g'.rdi = g.rdi → g'.rbp = cr g → g'.rsp = g.rsp - 24 → K4 g g' →
      ∀ fl, Q 56 g' fl (Fr V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 f8 f12 h23 h56 ⊢
  wpx [W_0, o0, Op.cmpmr, r24]
  all_goals repeat' (first
    | refine h23 _ ?_ _
    | refine h56 _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact f8
    | with_reducible exact f12
    | apply And.intro
    | intro _)

/-- The stores at 23, then `add rsp, 8; pop rbx; pop rbp` to the `ret` at 48. -/
theorem vc_23 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S r : Addr} {g₀ : Gprs}
    (hP : P23 V p S r g₀ g) (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (hR : Room Wl V p)
    (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i)) (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (h : ∀ g', g'.rsp = S → g'.rbx = rdq(Out (BitVec.setWidth 8 r) V p, S - 16) →
      g'.rbp = rdq(Out (BitVec.setWidth 8 r) V p, S - 8) → K4 g₀ g' →
      ∀ fl, Q 48 g' fl (Out (BitVec.setWidth 8 r) V p)) :
    W_23 F Wl Q g f V := by
  obtain ⟨ha, hb, hr, hsp, hk⟩ := hP
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hb hr hsp hk
  subst ha hb hr hsp
  wpx [W_23, o1, inc32z, e16, e8, e0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hk
    | with_reducible exact fp
    | with_reducible exact fb
    | with_reducible exact fq
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | apply And.intro
    | intro _)

/-- Back from `Grow_1` at 61: the length again, to 23. -/
theorem vc_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S r : Addr} {g₀ : Gprs}
    (hb : g.rbx = p) (hr : g.rbp = r) (hS : g.rsp = S - 24) (hk : K4 g₀ g)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (h : ∀ g', P23 V p S r g₀ g' → ∀ fl, Q 23 g' fl V) :
    W_61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4⟩ := hk
  dsimp only at hb hr hS k1 k2 k3 k4
  subst hb hr hS
  wpx [W_61, o2]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | with_reducible exact f8
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 23 (the registers `P23`, the bytes `W`) to the return address with the bytes `Out`. -/
theorem tail23 {W : Addr → Byte} {p S r : Addr} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L ach_at ach) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = ach_at.add 23) (hP : P23 W p S r g₀ Y.cpu.gpr) (hR : Room Wl W p)
    (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i))
    (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(Out (BitVec.setWidth 8 r) W p, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Out (BitVec.setWidth 8 r) W p) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 →
      Z'.cpu.gpr.rbx = rdq(Out (BitVec.setWidth 8 r) W p, S - 16) →
      Z'.cpu.gpr.rbp = rdq(Out (BitVec.setWidth 8 r) W p, S - 8) → K4 g₀ Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_23 prof).run c hin
    (fun j' g' _ V' => j' = 48 ∧ g'.rsp = S ∧ g'.rbx = rdq(Out (BitVec.setWidth 8 r) W p, S - 16) ∧
      g'.rbp = rdq(Out (BitVec.setWidth 8 r) W p, S - 8) ∧ K4 g₀ g' ∧ V' = Out (BitVec.setWidth 8 r) W p) hK hA hrY
    (vc_23 hP fp hR fb fq fun _ hs hb hp hk _ => ⟨rfl, hs, hb, hp, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, hb, hp, hk, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_48 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact hb
  · rw [hgZ']
    exact hp
  · rw [hgZ']
    exact hk

/-- `operator+= (c)` (`p` = `rdi`, `c` = `sil`) from its entry. Either straight to the return address with `Out` of
`Fr` (room left), or through `Grow_1` (`k1`: at its entry with `rsp` 32 below the entry's, `rbx` = `p`, `rbp` the
character's register; from its return as above) to the return address with `Out` of the bytes `Grow_1` left (`kr`,
with `P1`). -/
theorem ach_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ach_at ach)
    (hinG : CodeIn L Ag1.ag1_at Ag1.ag1)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ach_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hR : Room Wl (Fr V X.cpu.gpr) X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr1 : rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) (Fr V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (hb1 : rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) (Fr V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp - 16) =
      X.cpu.gpr.rbx)
    (hp1 : rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) (Fr V X.cpu.gpr) X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) =
      X.cpu.gpr.rbp)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Fr V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ach_at.add 61) 8)) →
      Y.cpu.rip = Ag1.ag1_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rbx = X.cpu.gpr.rdi → Y.cpu.gpr.rbp = cr X.cpu.gpr → K4 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ach_at.add 61 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = cr X.cpu.gpr → K4 X.cpu.gpr Z.cpu.gpr → Room Wl V' X.cpu.gpr.rdi →
        rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ →
        rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) V' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(Out (BitVec.setWidth 8 (cr X.cpu.gpr)) V' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (W = Out (BitVec.setWidth 8 (cr X.cpu.gpr)) (Fr V X.cpu.gpr) X.cpu.gpr.rdi ∨
        ∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧ W = Out (BitVec.setWidth 8 (cr X.cpu.gpr)) V' X.cpu.gpr.rdi) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have fq : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 23 ∧ V' = Fr V X.cpu.gpr ∧
        P23 (Fr V X.cpu.gpr) X.cpu.gpr.rdi X.cpu.gpr.rsp (cr X.cpu.gpr) X.cpu.gpr g') ∨
      (j' = 56 ∧ V' = Fr V X.cpu.gpr ∧ g'.rbx = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi ∧
        g'.rbp = cr X.cpu.gpr ∧ g'.rsp = X.cpu.gpr.rsp - 24 ∧ K4 X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 (by rw [q16]; exact hs2) (by exact fun i hi => c.hws _ (hR.2.2 i hi)) f12
      (fun _ hP _ => Or.inl ⟨rfl, rfl, hP⟩)
      (fun _ hb hd hp hs hk _ => Or.inr ⟨rfl, rfl, hb, hd, hp, hs, hk⟩)) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hb, hd, hp, hs, hk⟩
  · -- the stores at 23 in place
    exact tail23 c hin hKY hAY hrY hP hR fp fb fq hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs hb hp hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs ⟨hb.trans hb1, hp.trans hp1, hk⟩ (Or.inl rfl)
  · -- `Grow_1`, then the stores at 23 in its buffer
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs]; exact q32 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_56 _) hinG (tgt := 0) (Ag1.lt_len (by decide))
      tgt_56 (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hb) (by rw [hg₂]; exact hp) (by rw [hg₂]; exact hk) ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hzk hR' hr' hb' hp' hP1
    refine (c_61 prof).run c hin
      (fun j' g' _ V'' => j' = 23 ∧ V'' = V' ∧ P23 V' X.cpu.gpr.rdi X.cpu.gpr.rsp (cr X.cpu.gpr) X.cpu.gpr g')
      hKZ hAZ hrZ (vc_61 hzb hzp hzs hzk (by exact fun i hi => c.hws _ (hR'.2.2 i hi))
        fun _ hP _ => ⟨rfl, rfl, hP⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hP⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    exact tail23 c hin hKU hAU hrU hP hR' fp fb fq hl hin₂ h₂ hr' fun Z' t₄ hKZ' hAZ' hrZ' hs hb hp hk =>
      kr _ Z' t₄ hKZ' hAZ' hrZ' hs ⟨hb.trans hb', hp.trans hp', hk⟩ (Or.inr ⟨Z, _, hP1, rfl⟩)

end FV7z.Ach
