import FV7z.Nda.Cuts
import FV7z.Ag1.Blocks
import FV7z.Rfw.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `NormalizeDirPathPrefix (AString &)` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NName::NormalizeDirPathPrefix (AString &dirPath)` at `0x456820` in `7zzs`
(`CPP/Windows/FileName.cpp`; as `FV7z/Ndp/Holds.lean` with 1-byte characters), the string at `p` = `rdi` (`Rfw.chs`,
`Rfw.len`: the characters, the length): `mov eax, [rdi + 8]; test eax, eax; je 23` (empty: the `ret` at 23);
`mov rdx, [rdi]; mov ecx, eax; cmp byte [rdx + rcx - 1], '/'; jne 32` (else the `ret` at 23); `cmp eax, [rdi + 0xc];
je 64` (`_len` = `_limit`); at 37 the stores: `add eax, 1; mov byte [rdx + rcx], '/'; mov ecx, eax; mov byte
[rdx + rcx], 0; mov [rdi + 8], eax; ret` (53). At 64 `sub rsp, 0x18; mov [rsp + 8], rdi`, the `call` (73) of
`AString::Grow_1` (`Ag1.ag1_at`); at 78 `mov rdi, [rsp + 8]; mov ecx, [rdi + 8]; mov rdx, [rdi]; mov rax, rcx` (the
length and the characters read again), at 92 the same stores, `add rsp, 0x18; ret` (112).

The callee is a hypothesis (`k1`), as in `FV7z/Ndp/Holds.lean`: a continuation at its entry, given the run from its
return (`rsp` 24 below the entry's, the callee-saved registers and the saved `p` as they were, `Room` for the stores
in the new buffer, the return address left by the stores, and the callee's own post `P1`).

- `KS`: the callee-saved registers as they were.
- `P92`: the registers at 92 (`rdx` the characters, `ecx` and `eax` the length).
- `Out`: the bytes after the stores: '/' at the end, then 0, the length plus 1.
- `Room`: the footprint of those stores.
- `vc_0`, `vc_78`, `vc_92`: the verification conditions of the three pieces; `tail92`: from 92 to the return.
- `nda_ok`: from the entry to the return address with `rsp` 8 above the entry's, the callee-saved registers as they
  were and the bytes as they were, or `Out` of them, or `Out` of `Grow_1`'s.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len)
namespace FV7z.Nda

/-- The `call` of `AString::Grow_1`. -/
def pc1 : List Byte := [0xe8, 0x32, 0x58, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709508658] 5) := by dec_rfl
theorem wc_73 : pc1 <+: nda.drop 73 := by decide +kernel
theorem call_73 (feat : Features) : Dec feat nda 73 (FV7z.mk .call 64 [.rel 18446744073709508658] 5) :=
  Dec.shift (j := 73) (k := 0) (pc1_0 feat) wc_73 (Nat.zero_le _)
theorem tgt_73 : nda_at.add (73 + 5) + BitVec.ofNat 64 18446744073709508658 = Ag1.ag1_at.add 0 := by decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_23 : pret <+: nda.drop 23 := by decide +kernel
theorem ret_23 (feat : Features) : Dec feat nda 23 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 23) (k := 0) (pret_0 feat) w_23 (Nat.zero_le _)
theorem w_53 : pret <+: nda.drop 53 := by decide +kernel
theorem ret_53 (feat : Features) : Dec feat nda 53 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)
theorem w_112 : pret <+: nda.drop 112 := by decide +kernel
theorem ret_112 (feat : Features) : Dec feat nda 112 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 112) (k := 0) (pret_0 feat) w_112 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem sa24 (s : BitVec 64) : s - 24#64 + 24#64 = s := by bv_omega
theorem q16 (s : BitVec 64) : s - 24#64 + 8#64 = s - 16 := by bv_omega
theorem q32 (s : BitVec 64) : s - 24#64 - 8 = s - 32 := by bv_omega

/-! ## The pieces -/

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The registers at 92, the string at `p` in the bytes `W`, `S` the entry's `rsp`, `g₀` the entry's registers. -/
abbrev P92 (W : Addr → Byte) (p S : Addr) (g₀ g : Gprs) : Prop :=
  g.rdx = chs W p ∧ g.rcx = BitVec.setWidth 64 (len W p) ∧ g.rax = BitVec.setWidth 64 (len W p) ∧ g.rdi = p ∧
    g.rsp = S - 24#64 ∧ KS g₀ g

/-- The bytes after the stores: '/' at the end, 0 after it, the length plus 1. -/
abbrev Out (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst W (chs W p + BitVec.setWidth 64 (len W p)) (toBytesLE (BitVec.ofNat 8 47) 1))
      (chs W p + BitVec.setWidth 64 (len W p + 1#32)) (toBytesLE (BitVec.ofNat 8 0) 1))
    (p + 8#64) (toBytesLE (len W p + 1#32) 4)

/-- The footprint of the stores: writable. -/
abbrev Room (Wl : List Rgn) (W : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p)) i)) ∧
    (∀ i < 1, Foot Wl (Addr.add (chs W p + BitVec.setWidth 64 (len W p + 1#32)) i)) ∧
    ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the `ret` at 23, the stores and the `ret` at 53, or the `call` at 73 with `p` saved at
`rsp + 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fl : ∀ i < 1, Foot F.data
      (Addr.add (chs V g.rdi + BitVec.setWidth 64 (len V g.rdi) + 18446744073709551615#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 24#64 + 8#64) i)) (hR : Room Wl V g.rdi)
    (h23 : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 23 g' fl V)
    (h53 : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 53 g' fl (Out V g.rdi))
    (h73 : ∀ g', g'.rsp = g.rsp - 24#64 → g'.rdi = g.rdi → KS g g' →
      ∀ fl, Q 73 g' fl (Vst V (g.rsp - 24#64 + 8#64) (toBytesLE g.rdi 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 fp fl f12 hs2 r1 r2 r3 h23 h53 h73 ⊢
  wpx [W_0, W_11, W_32, W_37, W_64, o0, o1, o2, o3, o4, Op.cmpmi]
  all_goals repeat' (first
    | refine h23 _ ?_ ?_ _
    | refine h53 _ ?_ ?_ _
    | refine h73 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fp
    | with_reducible exact fl
    | with_reducible exact f12
    | with_reducible exact hs2
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | apply And.intro
    | intro _)

/-- Back from `Grow_1` at 78: `p` from `rsp + 8`, its length and characters again, to 92. -/
theorem vc_78 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hS : g.rsp = S - 24#64) (hk : KS g₀ g) (hz : rdq(V, g.rsp + 8#64) = p)
    (fs : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add p i)) (h : ∀ g', P92 V p S g₀ g' → ∀ fl, Q 92 g' fl V) :
    W_78 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  dsimp only at hS k1 k2 k3 k4 k5 k6 hz fs
  subst hS
  wpx [W_78, o5]
  simp only [hz]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
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

/-- The stores at 92, then `add rsp, 0x18` to the `ret` at 112. -/
theorem vc_92 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p S : Addr} {g₀ : Gprs}
    (hP : P92 V p S g₀ g) (hR : Room Wl V p)
    (h : ∀ g', g'.rsp = S → KS g₀ g' → ∀ fl, Q 112 g' fl (Out V p)) :
    W_92 F Wl Q g f V := by
  obtain ⟨hd, hc, ha, hp, hsp, hk⟩ := hP
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hc ha hp hsp hk
  subst hp hsp hd hc ha
  wpx [W_92, o6]
  repeat' (first
    | exact h _ (sa24 _) (by exact hk) _
    | with_reducible exact r1
    | with_reducible exact r2
    | with_reducible exact r3
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 92 (the registers `P92`, the bytes `W`) to the return address with the bytes `Out`. -/
theorem tail92 {W : Addr → Byte} {p S : Addr} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L nda_at nda) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = nda_at.add 92) (hP : P92 W p S g₀ Y.cpu.gpr) (hR : Room Wl W p)
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(Out W p, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Out W p) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g₀ Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_92 prof).run c hin (fun j' g' _ V' => j' = 112 ∧ g'.rsp = S ∧ KS g₀ g' ∧ V' = Out W p) hK hA hrY
    (vc_92 hP hR fun _ hs hk _ => ⟨rfl, hs, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, hk, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_112 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact hk

/-- `NormalizeDirPathPrefix (dirPath)` (`p` = `rdi`, an `AString`) from its entry. Either straight to the return
address with the bytes as they were (empty, or '/' at the end) or `Out` of them (room left), or through `Grow_1`
(`k1`: at its entry with `rsp` 32 below the entry's and `p` saved at `rsp` - 16; from its return as above) to the
return address with `Out` of the bytes `Grow_1` left (`kr`, with `P1`). -/
theorem nda_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nda_at nda)
    (hinG : CodeIn L Ag1.ag1_at Ag1.ag1)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nda_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fl : ∀ i < 1, Foot F.data (Addr.add (chs V X.cpu.gpr.rdi +
      BitVec.setWidth 64 (len V X.cpu.gpr.rdi) + 18446744073709551615#64) i))
    (hR : Room Wl V X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hr1 : rdq(Out V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE X.cpu.gpr.rdi 8)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (nda_at.add 78) 8)) →
      Y.cpu.rip = Ag1.ag1_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      KS X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = nda_at.add 78 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 → KS X.cpu.gpr Z.cpu.gpr →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rdi → Room Wl V' X.cpu.gpr.rdi →
        rdq(Out V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (W = V ∨ W = Out V X.cpu.gpr.rdi ∨
        ∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧ W = Out V' X.cpu.gpr.rdi) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 23 ∧ V' = V ∧ g'.rsp = X.cpu.gpr.rsp ∧ KS X.cpu.gpr g') ∨
      (j' = 53 ∧ V' = Out V X.cpu.gpr.rdi ∧ g'.rsp = X.cpu.gpr.rsp ∧ KS X.cpu.gpr g') ∨
      (j' = 73 ∧ V' = Vst V (X.cpu.gpr.rsp - 24#64 + 8#64) (toBytesLE X.cpu.gpr.rdi 8) ∧
        g'.rsp = X.cpu.gpr.rsp - 24#64 ∧ g'.rdi = X.cpu.gpr.rdi ∧ KS X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by exact fun i hi => c.hws _ (hR.2.2 i hi)) fp fl f12 (by rw [q16]; exact hs2) hR
      (fun _ hs hk _ => Or.inl ⟨rfl, rfl, hs, hk⟩)
      (fun _ hs hk _ => Or.inr (Or.inl ⟨rfl, rfl, hs, hk⟩))
      (fun _ hs hd hk _ => Or.inr (Or.inr ⟨rfl, rfl, hs, hd, hk⟩))) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hs, hk⟩ | ⟨rfl, rfl, hs, hk⟩ | ⟨rfl, rfl, hs, hd, hk⟩
  · -- the `ret` at 23, the bytes as they were
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_23 _) (by rw [hs]; exact hl) hin₂ h₂
      (by rw [hs]; exact hr) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr _ Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ (Or.inl rfl)
    · rw [hgZ']
      show Y.cpu.gpr.rsp + 8 = _
      rw [hs]
    · rw [hgZ']
      exact hk
  · -- the stores in place, the `ret` at 53
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_53 _) (by rw [hs]; exact hl) hin₂ h₂
      (by rw [hs]; exact hr1) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr _ Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ (Or.inr (Or.inl rfl))
    · rw [hgZ']
      show Y.cpu.gpr.rsp + 8 = _
      rw [hs]
    · rw [hgZ']
      exact hk
  · -- `Grow_1`, then the stores at 92 in its buffer
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs]; exact q32 _
    rw [q16] at hAY
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_73 _) hinG (tgt := 0) (Ag1.lt_len (by decide))
      tgt_73 (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hk) ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzk hb hR' hr' hP1
    refine (c_78 prof).run c hin
      (fun j' g' _ V'' => j' = 92 ∧ V'' = V' ∧ P92 V' X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr g')
      hKZ hAZ hrZ (vc_78 hzs hzk (by rw [hzs, q16]; exact hb) (by rw [hzs, q16]; exact h16)
        (by exact fun i hi => c.hws _ (hR'.2.2 i hi)) fp
        fun _ hP _ => ⟨rfl, rfl, hP⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hP⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    exact tail92 c hin hKU hAU hrU hP hR' hl hin₂ h₂ hr' fun Z' t₄ hKZ' hAZ' hrZ' hs hk =>
      kr _ Z' t₄ hKZ' hAZ' hrZ' hs hk (Or.inr (Or.inr ⟨Z, _, hP1, rfl⟩))

end FV7z.Nda
