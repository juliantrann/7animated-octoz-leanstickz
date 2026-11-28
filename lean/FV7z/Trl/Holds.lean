import FV7z.Trl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# The `_ZThn24` `Release ()` thunk at `0x5b2940` (PLAN.md §M, M1)

7-Zip 26.06's `Release ()` (`MY_ADDREF_RELEASE`, `CPP/Common/MyCom.h`) of a COM class through its base at offset 24
(`_ZThn24`: `this` is `rdi` - 24), the count at `rdi + 0x20`, at `0x5b2940` in `7zzs`: `push r12; push rbp; sub
rsp, 8; mov eax, [rdi + 0x20]; lea r12d, [rax - 1]; mov [rdi + 0x20], r12d; test r12d, r12d; jne 52`; at 27 (the count
0) `lea rbp, [rdi - 0x18]; mov rdi, rbp`, the `call` (34) of the destructor (`0x5b2340`), at 39 `mov esi, 0x2c0;
mov rdi, rbp`, the `call` (47) of the sized `operator delete (p, 0x2c0)` (`0x6014e0`); at 52 `add rsp, 8; mov eax,
r12d; pop rbp; pop r12; ret` (62): the new count in `eax`.

The callees are hypotheses (`kd`, `ke`), as in `FV7z/Ndp/Holds.lean`: continuations at their entries, given the run
from their returns (`rsp` 24 below the entry's, `rbp` the object for the destructor's, `r12` the new count, the other
callee-saved registers as they were, and the callee's own post `P1`, `P2`; the return address and the saved `rbp`,
`r12` left by `operator delete`). No flag fact is kept: the post says which bytes the run may leave, not when (the
calls are made only when the new count is 0).

- `K4`: `rbx`, `r13`–`r15` as they were; `KS`: the six callee-saved registers.
- `Fr`: the bytes after the two `push`es; `cnt`: the new count; `Dn`: the bytes after its store; `ob`: the object.
- `P52`: the registers at 52 and before the calls (`r12` the new count, `rsp` 24 below the entry's).
- `vc_0`, `vc_39`, `vc_52`: the verification conditions of the pieces; `tail52`: from 52 to the return.
- `trl_ok`: from the entry to the return address with `rsp` 8 above the entry's, the new count in `eax`, the
  callee-saved registers as they were, and the bytes `Dn` or those `operator delete` left.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Trl

/-- The `call` of the destructor. -/
def pc1 : List Byte := [0xe8, 0xd9, 0xf9, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709550041] 5) := by dec_rfl
theorem wc_34 : pc1 <+: trl.drop 34 := by decide +kernel
theorem call_34 (feat : Features) : Dec feat trl 34 (FV7z.mk .call 64 [.rel 18446744073709550041] 5) :=
  Dec.shift (j := 34) (k := 0) (pc1_0 feat) wc_34 (Nat.zero_le _)
theorem tgt_34 : trl_at.add (34 + 5) + BitVec.ofNat 64 18446744073709550041 = (0x5b2340#64).add 0 := by decide

/-- The `call` of `operator delete`. -/
def pc2 : List Byte := [0xe8, 0x6c, 0xeb, 0x04, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 322412] 5) := by dec_rfl
theorem wc_47 : pc2 <+: trl.drop 47 := by decide +kernel
theorem call_47 (feat : Features) : Dec feat trl 47 (FV7z.mk .call 64 [.rel 322412] 5) :=
  Dec.shift (j := 47) (k := 0) (pc2_0 feat) wc_47 (Nat.zero_le _)
theorem tgt_47 : trl_at.add (47 + 5) + BitVec.ofNat 64 322412 = (0x6014e0#64).add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_62 : pret <+: trl.drop 62 := by decide +kernel
theorem ret_62 (feat : Features) : Dec feat trl 62 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 62) (k := 0) (pret_0 feat) w_62 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem dec32z (n : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 n + 18446744073709551615#64) = n - 1#32 := by
  bv_omega

theorem r24 (s : BitVec 64) : s - 8 - 8 - 8#64 = s - 24 := by bv_omega
theorem e16 (s : BitVec 64) : s - 24 + 8#64 = s - 16 := by bv_omega
theorem e8 (s : BitVec 64) : s - 16 + 8 = s - 8 := by bv_omega
theorem e0 (s : BitVec 64) : s - 8 + 8 = s := by bv_omega
theorem q16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega
theorem q32 (s : BitVec 64) : s - 24 - 8 = s - 32 := by bv_omega
theorem rsi704 : BitVec.setWidth 64 (BitVec.ofNat 32 704) = 704#64 := by decide

/-! ## The pieces -/

/-- `rbx`, `r13`–`r15` as they were. -/
abbrev K4 (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The bytes after `push r12; push rbp`. -/
abbrev Fr (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)

/-- The new count. -/
abbrev cnt (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(Fr V g, g.rdi + 32#64) - 1#32

/-- The bytes after the new count's store. -/
abbrev Dn (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (Fr V g) (g.rdi + 32#64) (toBytesLE (cnt V g) 4)

/-- The object: `rdi` - 24. -/
abbrev ob (p : Addr) : Addr := p + 18446744073709551592#64

/-- The registers at 52 and before the calls: `r12` the new count `n`, `rsp` 24 below `S`. -/
abbrev P52 (S : Addr) (n : BitVec 32) (g₀ g : Gprs) : Prop :=
  g.r12 = BitVec.setWidth 64 n ∧ g.rsp = S - 24 ∧ K4 g₀ g

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the two `push`es and the new count, then 52, or the `call` at 34 with `rdi` = `rbp` the object. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 32#64) i)) (w32 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 32#64) i))
    (h52 : ∀ g', P52 g.rsp (cnt V g) g g' → ∀ fl, Q 52 g' fl (Dn V g))
    (h34 : ∀ g', g'.rdi = ob g.rdi → g'.rbp = ob g.rdi → P52 g.rsp (cnt V g) g g' → ∀ fl, Q 34 g' fl (Dn V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 f32 w32 h52 h34 ⊢
  wpx [W_0, W_27, o0, o1, r24, dec32z]
  all_goals repeat' (first
    | refine h52 _ ?_ _
    | refine h34 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact f32
    | with_reducible exact w32
    | apply And.intro
    | intro _)

/-- Back from the destructor at 39: `esi` = 0x2c0, `rdi` = `rbp`, to the `call` at 47. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {q S : Addr} {n : BitVec 32} {g₀ : Gprs}
    (hb : g.rbp = q) (hS : g.rsp = S - 24) (hr : g.r12 = BitVec.setWidth 64 n) (hk : K4 g₀ g)
    (h : ∀ g', g'.rdi = q → g'.rsi = 704#64 → g'.rbp = q → P52 S n g₀ g' → ∀ fl, Q 47 g' fl V) :
    W_39 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4⟩ := hk
  dsimp only at hb hS hr k1 k2 k3 k4
  subst hb hS hr
  wpx [W_39, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rsi704
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | apply And.intro
    | intro _)

/-- From 52: `add rsp, 8; mov eax, r12d; pop rbp; pop r12` to the `ret` at 62. -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {S : Addr} {n : BitVec 32} {g₀ : Gprs}
    (hP : P52 S n g₀ g) (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i))
    (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (h : ∀ g', g'.rsp = S → g'.rax = BitVec.setWidth 64 n → g'.rbp = rdq(V, S - 16) → g'.r12 = rdq(V, S - 8) →
      K4 g₀ g' → ∀ fl, Q 62 g' fl V) :
    W_52 F Wl Q g f V := by
  obtain ⟨hr, hsp, hk⟩ := hP
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hsp hk
  subst hr hsp
  wpx [W_52, o3, e16, e8, e0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hk
    | with_reducible exact fb
    | with_reducible exact fq
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 52 (the registers `P52`, the bytes `W`) to the return address. -/
theorem tail52 {W : Addr → Byte} {S : Addr} {n : BitVec 32} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L trl_at trl) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = trl_at.add 52) (hP : P52 S n g₀ Y.cpu.gpr)
    (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i)) (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(W, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → Z'.cpu.gpr.rax = BitVec.setWidth 64 n → Z'.cpu.gpr.rbp = rdq(W, S - 16) →
      Z'.cpu.gpr.r12 = rdq(W, S - 8) → K4 g₀ Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_52 prof).run c hin
    (fun j' g' _ V' => j' = 62 ∧ g'.rsp = S ∧ g'.rax = BitVec.setWidth 64 n ∧ g'.rbp = rdq(W, S - 16) ∧
      g'.r12 = rdq(W, S - 8) ∧ K4 g₀ g' ∧ V' = W) hK hA hrY
    (vc_52 hP fb fq fun _ hs ha hp hq hk _ => ⟨rfl, hs, ha, hp, hq, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, ha, hp, hq, hk, hV⟩ U t₁ hKU hAU hrU hgU -
  subst hgU hV
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_62 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hr) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hs]
  · rw [hgZ']
    exact ha
  · rw [hgZ']
    exact hp
  · rw [hgZ']
    exact hq
  · rw [hgZ']
    exact hk

/-- `Release ()` through the base at offset 24 (`rdi`) from its entry. Either straight to the return address with the
bytes `Dn` (the new count stored), or through the destructor (`kd`: at its entry with `rsp` 32 below the entry's,
`rdi` the object) and `operator delete` (`ke`: likewise, `esi` = 0x2c0) to the return address with the bytes
`operator delete` left (`kr`, with `P2`). -/
theorem trl_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L trl_at trl)
    {codeD : List Byte} (hinD : CodeIn L 0x5b2340#64 codeD) (hD : 0 < codeD.length)
    {codeE : List Byte} (hinE : CodeIn L 0x6014e0#64 codeE) (hE : 0 < codeE.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = trl_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (w32 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (hp1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp)
    (hq1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12)
    (kd : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Dn V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (trl_at.add 39) 8)) →
      Y.cpu.rip = 0x5b2340#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.rbp = ob X.cpu.gpr.rdi → Y.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) →
      K4 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = trl_at.add 39 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = ob X.cpu.gpr.rdi →
        Z.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → K4 X.cpu.gpr Z.cpu.gpr → P1 Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (ke : ∀ (Z₁ : State) (V₁ : Addr → Byte), P1 Z₁ V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 32) (toBytesLE (trl_at.add 52) 8)) →
      Y.cpu.rip = 0x6014e0#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = 704#64 → Y.cpu.gpr.rbp = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → K4 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ →
        Z.cpu.rip = trl_at.add 52 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 →
        Z.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → K4 X.cpu.gpr Z.cpu.gpr →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → P2 Z V₂ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 (cnt V X.cpu.gpr) → KS X.cpu.gpr Z'.cpu.gpr →
      (W = Dn V X.cpu.gpr ∨ ∃ (Z : State), P2 Z W) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have fq : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 52 ∧ V' = Dn V X.cpu.gpr ∧ P52 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g') ∨
      (j' = 34 ∧ V' = Dn V X.cpu.gpr ∧ g'.rdi = ob X.cpu.gpr.rdi ∧ g'.rbp = ob X.cpu.gpr.rdi ∧
        P52 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 (by rw [q16]; exact hs2) f32 w32 (fun _ hP _ => Or.inl ⟨rfl, rfl, hP⟩)
      (fun _ hd hb hP _ => Or.inr ⟨rfl, rfl, hd, hb, hP⟩)) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hd, hb, hr, hs, hk⟩
  · -- the count not 0: the `ret`
    exact tail52 c hin hKY hAY hrY hP fb fq hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs ha hp hq hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs ha ⟨hk.1, hp.trans hp1, hq.trans hq1, hk.2⟩ (Or.inl rfl)
  · -- the destructor, then `operator delete`, then the `ret`
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs]; exact q32 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_34 _) hinD (tgt := 0) hD tgt_34
      (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine kd Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hb) (by rw [hg₂]; exact hr) (by rw [hg₂]; exact hk) ?_
    intro Z V₂ t'' hKZ hAZ hrZ hzs hzb hzr hzk hP1
    refine (c_39 prof).run c hin
      (fun j' g' _ V' => j' = 47 ∧ V' = V₂ ∧ g'.rdi = ob X.cpu.gpr.rdi ∧ g'.rsi = 704#64 ∧
        g'.rbp = ob X.cpu.gpr.rdi ∧ P52 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g')
      hKZ hAZ hrZ (vc_39 hzb hzs hzr hzk fun _ hd hsi hb hP _ => ⟨rfl, rfl, hd, hsi, hb, hP⟩) ?_
    rintro j' g fl₂ V₃ ⟨rfl, rfl, hd', hsi, hb', hr', hs', hk'⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs']; exact q32 _
    refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_47 _) hinE (tgt := 0) hE tgt_47
      (by rw [hU32]; exact hs4) ?_
    rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hU32] at hA₄
    refine ke Z _ hP1 U₂ t₄ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) (by rw [hg₄]; exact hU32)
      (by rw [hg₄]; exact hd') (by rw [hg₄]; exact hsi) (by rw [hg₄]; exact hb') (by rw [hg₄]; exact hr')
      (by rw [hg₄]; exact hk') ?_
    intro Z₂ V₄ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2r hz2k hra hrp hrq hP2
    exact tail52 c hin hKZ₂ hAZ₂ hrZ₂ ⟨hz2r, hz2s, hz2k⟩ fb fq hl hin₂ h₂ hra
      fun Z' t₆ hKZ' hAZ' hrZ' hs ha hp hq hk =>
        kr _ Z' t₆ hKZ' hAZ' hrZ' hs ha ⟨hk.1, hp.trans hrp, hq.trans hrq, hk.2⟩ (Or.inr ⟨Z₂, hP2⟩)

end FV7z.Trl
