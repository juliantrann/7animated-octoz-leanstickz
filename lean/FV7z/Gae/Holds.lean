import FV7z.Gae.Cuts
import FV7z.Raf.Holds
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.LeafRet
/-!
# `GetOpenArcErrorFlags` (PLAN.md §M, M1)

7-Zip 26.06's `GetOpenArcErrorFlags (prop, isDefinedProp)` at `0x5d2ae0` in `7zzs`
(`CPP/7zip/UI/Common/OpenArchive.cpp`), `prop` = `rdi`, `isDefinedProp` = `rsi`: `sub rsp, 8`, the 16-bit type tag
`vt` (the 2 bytes at `prop`) into `eax`; when `rsi` is not 0, `*rsi` = 0 first (16). `VT_UI4` or `VT_UI8` (0x13,
0x15): `*rsi` = 1 (48, `rsi` not 0), the result the 4 bytes at `prop + 8` (51), to the `ret` at 58. `VT_EMPTY` (0):
the result 0 (36), to the `ret` at 42. Any other type: a jump (64 or 89) to the code at `0x4176fe` that throws.

The byte at `rsi` is stored before the result is loaded: the result is read from the bytes as they are at the end.

- `vtOf V g`: the type tag; `st1 V a b`: the byte `b` stored at `a`; `K8 g g'`: the registers kept (`rbx`, `rbp`,
  `r12..r15`, `rdi`, `rsi`).
- `vc_*`: the verification conditions of the pieces (from the entry, one per way; 36; 48; 51).
- `fin36`, `fin51`, `fin48`, `thr`: from the cut points to the return address or to the throw.
- `gae_ok`: from the entry to the return address (`k0`, `k1`) or to the throw (`kt`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gae

theorem gae_42 : ∀ feat, Dec feat gae 42 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem gae_58 : ∀ feat, Dec feat gae 58 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem gae_64 : ∀ feat, Dec feat gae 64 (FV7z.mk .jmp 64 [.rel 18446744073707736025] 5) := by intro feat f; rfl
theorem gae_89 : ∀ feat, Dec feat gae 89 (FV7z.mk .jmp 64 [.rel 18446744073707736000] 5) := by intro feat f; rfl

/-- The type tag `vt`: the 2 bytes at `prop`. -/
abbrev vtOf (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 ((byteAddrs g.rdi 2).map V)

/-- The byte `b` stored at `a`. -/
abbrev st1 (V : Addr → Byte) (a : Addr) (b : BitVec 8) : Addr → Byte := Vst V a (toBytesLE b 1)

/-- The registers kept from `g` to `g'`. -/
def K8 (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
    g'.rdi = g.rdi ∧ g'.rsi = g.rsi

theorem K8.trans {a b c : Gprs} (h : K8 a b) (h' : K8 b c) : K8 a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := h'
  exact ⟨h1'.trans h1, h2'.trans h2, h3'.trans h3, h4'.trans h4, h5'.trans h5, h6'.trans h6, h7'.trans h7,
    h8'.trans h8⟩

theorem K8.set4 {a b : Gprs} {v : Addr} (h : K8 a b) : K8 a (b.set 4 v) := h

theorem sw3 (x : BitVec 16) : ((x.setWidth 32).setWidth 64).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem sw3' (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The closer of the pieces' conditions. -/
macro "gcl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _
    | bv_omega))

variable {F : Footprint} {Wl : List Rgn}

section
variable {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- `rsi` 0, `vt` 0x13 or 0x15 (given as `k`): to 51. -/
theorem vc_z1 {k : BitVec 16} (hk : k = 19#16 ∨ k = 21#16) (hs : g.rsi = 0)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (ht : vtOf V g = k) :
    W_0 F Wl (fun j' g' _ V' => j' = 51 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf] at hs ft ht ⊢
  subst hs
  rcases hk with rfl | rfl <;>
  · wpx [W_0, W_72, W_78, W_84, o0, o2, o3, o7, K8, ht, sw3, sw3', BitVec.and_self, decide_false, decide_true,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    gcl

/-- `rsi` 0, `vt` 0: to 36. -/
theorem vc_z0 (hs : g.rsi = 0) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (ht : vtOf V g = 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 36 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf] at hs ft ht ⊢
  subst hs
  wpx [W_0, W_72, W_78, W_84, o0, o2, o3, o7, K8, ht, sw3, sw3', BitVec.and_self, decide_false, decide_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  gcl

/-- `rsi` 0, any other `vt`: to the jump at 89. -/
theorem vc_zt (hs : g.rsi = 0) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (h0 : vtOf V g ≠ 0#16)
    (h19 : vtOf V g ≠ 19#16) (h21 : vtOf V g ≠ 21#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 89 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf] at hs ft h0 h19 h21 ⊢
  subst hs
  have e0 : (ofBytesLE 16 ((byteAddrs rdi 2).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  have e19 := decide_eq_false h19
  have e21 := decide_eq_false h21
  wpx [W_0, W_72, W_78, W_84, o0, o2, o3, o7, K8, e0, e19, e21, sw3, sw3', BitVec.and_self, decide_false,
    decide_true, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  gcl

/-- `rsi` not 0, `vt` 0x13 or 0x15: `*rsi` = 0, to 48. -/
theorem vc_n1 {k : BitVec 16} (hk : k = 19#16 ∨ k = 21#16) (hs : g.rsi ≠ 0)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (fw : ∀ i < 1, Foot Wl (Addr.add g.rsi i))
    (ht : vtOf V g = k) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = st1 V g.rsi 0#8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf, st1] at hs ft fw ht ⊢
  have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
  rcases hk with rfl | rfl <;>
  · wpx [W_0, W_16, W_25, W_31, o0, o1, o2, o3, K8, ht, hz, sw3, sw3', BitVec.and_self, decide_false, decide_true,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    gcl

/-- `rsi` not 0, `vt` 0: `*rsi` = 0, to 36. -/
theorem vc_n0 (hs : g.rsi ≠ 0) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (fw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) (ht : vtOf V g = 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 36 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = st1 V g.rsi 0#8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf, st1] at hs ft fw ht ⊢
  have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
  wpx [W_0, W_16, W_25, W_31, o0, o1, o2, o3, K8, ht, hz, sw3, sw3', BitVec.and_self, decide_false, decide_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  gcl

/-- `rsi` not 0, any other `vt`: `*rsi` = 0, to the jump at 64. -/
theorem vc_nt (hs : g.rsi ≠ 0) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (fw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) (h0 : vtOf V g ≠ 0#16) (h19 : vtOf V g ≠ 19#16)
    (h21 : vtOf V g ≠ 21#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 64 ∧ K8 g g' ∧ g'.rsp = g.rsp - 8#64 ∧ V' = st1 V g.rsi 0#8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf, st1] at hs ft fw h0 h19 h21 ⊢
  have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
  have e0 : (ofBytesLE 16 ((byteAddrs rdi 2).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  have e19 := decide_eq_false h19
  have e21 := decide_eq_false h21
  wpx [W_0, W_16, W_25, W_31, o0, o1, o2, o3, K8, hz, e0, e19, e21, sw3, sw3', BitVec.and_self, decide_false,
    decide_true, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  gcl

/-- 36: `xor eax, eax; add rsp, 8`, to the `ret` at 42. -/
theorem vc_36 :
    W_36 F Wl (fun j' g' _ V' => j' = 42 ∧ K8 g g' ∧ g'.rsp = g.rsp + 8#64 ∧ g'.rax = 0#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_36, o4, K8, BitVec.xor_self, BitVec.setWidth_zero]
  gcl

/-- 48: `*rsi` = 1, to 51. -/
theorem vc_48 (fw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 51 ∧ g' = g ∧ V' = st1 V g.rsi 1#8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [st1] at fw ⊢
  wpx [W_48, o5]
  gcl

/-- 51: `mov eax, [rdi + 8]; add rsp, 8`, to the `ret` at 58. -/
theorem vc_51 (ft : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) :
    W_51 F Wl (fun j' g' _ V' => j' = 58 ∧ K8 g g' ∧ g'.rsp = g.rsp + 8#64 ∧
      g'.rax = (ofBytesLE 32 ((byteAddrs (g.rdi + 8#64) 4).map V)).setWidth 64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ft ⊢
  wpx [W_51, o6, K8]
  gcl

end

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 36 to the return address: the result 0. -/
theorem fin36 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gae_at gae) {Y : State} {t₁ : Nat} {V₁ : Addr → Byte}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V₁) (hrY : Y.cpu.rip = gae_at.add 36) {g₀ : Gprs}
    (hK8 : K8 g₀ Y.cpu.gpr) (hsp : Y.cpu.gpr.rsp = g₀.rsp - 8#64) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₁, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ → Z.cpu.rip = e₂.add j₂ →
      K8 g₀ Z.cpu.gpr → Z.cpu.gpr.rsp = g₀.rsp + 8#64 → Z.cpu.gpr.rax = 0#64 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  refine (c_36 prof).run c hin _ hKY hAY hrY vc_36 ?_
  rintro j' g fl V₂ ⟨rfl, hk, hs2, hax, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
  subst hgZ
  have hspZ : Z.cpu.gpr.rsp = g₀.rsp := by rw [hs2, hsp]; exact BitVec.sub_add_cancel _ _
  refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (gae_42 _) (by rw [hspZ]; exact hl) hin₂ h₂
    (by rw [hspZ]; exact hra) ?_
  rintro W t₃ hKW hAW ⟨hrW, hgW⟩
  exact k W t₃ hKW hAW hrW (by rw [hgW]; exact (hK8.trans hk).set4)
    (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hspZ]; rfl) (by rw [hgW]; exact hax)

/-- From 51 to the return address: the result the 4 bytes at `prop + 8`. -/
theorem fin51 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gae_at gae) {Y : State} {t₁ : Nat} {V₁ : Addr → Byte}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V₁) (hrY : Y.cpu.rip = gae_at.add 51) {g₀ : Gprs}
    (hK8 : K8 g₀ Y.cpu.gpr) (hsp : Y.cpu.gpr.rsp = g₀.rsp - 8#64) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    (ft : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₁, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ → Z.cpu.rip = e₂.add j₂ →
      K8 g₀ Z.cpu.gpr → Z.cpu.gpr.rsp = g₀.rsp + 8#64 →
      Z.cpu.gpr.rax = (ofBytesLE 32 ((byteAddrs (g₀.rdi + 8#64) 4).map V₁)).setWidth 64 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have hdi : Y.cpu.gpr.rdi = g₀.rdi := hK8.2.2.2.2.2.2.1
  refine (c_51 prof).run c hin _ hKY hAY hrY (vc_51 (by rw [hdi]; exact ft)) ?_
  rintro j' g fl V₂ ⟨rfl, hk, hs2, hax, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
  subst hgZ
  have hspZ : Z.cpu.gpr.rsp = g₀.rsp := by rw [hs2, hsp]; exact BitVec.sub_add_cancel _ _
  refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (gae_58 _) (by rw [hspZ]; exact hl) hin₂ h₂
    (by rw [hspZ]; exact hra) ?_
  rintro W t₃ hKW hAW ⟨hrW, hgW⟩
  exact k W t₃ hKW hAW hrW (by rw [hgW]; exact (hK8.trans hk).set4)
    (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hspZ]; rfl) (by rw [hgW]; show Z.cpu.gpr.rax = _; rw [hax, hdi])

/-- From 48: `*rsi` = 1, then as `fin51`. -/
theorem fin48 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gae_at gae) {Y : State} {t₁ : Nat} {V₁ : Addr → Byte}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V₁) (hrY : Y.cpu.rip = gae_at.add 48) {g₀ : Gprs}
    (hK8 : K8 g₀ Y.cpu.gpr) (hsp : Y.cpu.gpr.rsp = g₀.rsp - 8#64) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    (ft : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 8#64) i)) (fw : ∀ i < 1, Foot Wl (Addr.add g₀.rsi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(st1 V₁ g₀.rsi 1#8, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (st1 V₁ g₀.rsi 1#8) →
      Z.cpu.rip = e₂.add j₂ → K8 g₀ Z.cpu.gpr → Z.cpu.gpr.rsp = g₀.rsp + 8#64 →
      Z.cpu.gpr.rax = (ofBytesLE 32 ((byteAddrs (g₀.rdi + 8#64) 4).map (st1 V₁ g₀.rsi 1#8))).setWidth 64 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have hsi : Y.cpu.gpr.rsi = g₀.rsi := hK8.2.2.2.2.2.2.2
  refine (c_48 prof).run c hin _ hKY hAY hrY (vc_48 (by rw [hsi]; exact fw)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
  rw [hsi] at hAZ
  exact fin51 c hin hKZ hAZ hrZ (by rw [hgZ]; exact hK8) (by rw [hgZ]; exact hsp) hl ft hin₂ h₂ hra k

/-- From a jump (64 or 89) to the throw at `0x4176fe`. -/
theorem thr (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gae_at gae) {codeT : List Byte}
    (hinT : CodeIn L 0x4176fe#64 codeT) (hT : 0 < codeT.length) {Y : State} {t₁ : Nat} {V₁ : Addr → Byte}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V₁) {j : Nat} (hj : j = 64 ∨ j = 89)
    (hrY : Y.cpu.rip = gae_at.add j)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ → Z.cpu.rip = 0x4176fe#64 →
      Z.cpu.gpr = Y.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  rcases hj with rfl | rfl
  · refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (gae_64 _) hinT (tgt := 0) hT (by decide) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ (by rw [hrZ, addr_add_zero]) hgZ
  · refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (gae_89 _) hinT (tgt := 0) hT (by decide) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ (by rw [hrZ, addr_add_zero]) hgZ

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes at the end when the result is 0 or the code throws: `*rsi` = 0 when `rsi` is not 0. -/
def Vz (V : Addr → Byte) (g : Gprs) : Addr → Byte := if g.rsi = 0 then V else st1 V g.rsi 0#8

/-- The bytes at the end for `VT_UI4`, `VT_UI8`: `*rsi` = 0, then 1, when `rsi` is not 0. -/
def V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := if g.rsi = 0 then V else st1 (st1 V g.rsi 0#8) g.rsi 1#8

/-- `GetOpenArcErrorFlags (prop, isDefinedProp)` from its entry: see the module doc. `vt` 0: at the return address,
the result 0 (`k0`); `VT_UI4`/`VT_UI8`: at the return address, the result the 4 bytes at `prop + 8` (`k1`); else at
the throw (`0x4176fe`) with `rsp` 8 below the entry's (`kt`). The registers `K8` as at the entry. -/
theorem gae_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gae_at gae) {codeT : List Byte}
    (hinT : CodeIn L 0x4176fe#64 codeT) (hT : 0 < codeT.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gae_at)
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (ft8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rsi i)) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64) (hr1 : X.cpu.gpr.rsi.toNat + 1 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsi ≠ 0 →
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 1 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : vtOf V X.cpu.gpr = 0#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vz V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ → K8 X.cpu.gpr Z.cpu.gpr →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 → Z.cpu.gpr.rax = 0#64 → GoG prof L o gev gP gE Z t')
    (k1 : vtOf V X.cpu.gpr = 19#16 ∨ vtOf V X.cpu.gpr = 21#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (V1 V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ → K8 X.cpu.gpr Z.cpu.gpr →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 →
      Z.cpu.gpr.rax = (ofBytesLE 32 ((byteAddrs (X.cpu.gpr.rdi + 8#64) 4).map (V1 V X.cpu.gpr))).setWidth 64 →
      GoG prof L o gev gP gE Z t')
    (kt : vtOf V X.cpu.gpr ≠ 0#16 → vtOf V X.cpu.gpr ≠ 19#16 → vtOf V X.cpu.gpr ≠ 21#16 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vz V X.cpu.gpr) →
      Z.cpu.rip = 0x4176fe#64 → K8 X.cpu.gpr Z.cpu.gpr → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = gae_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hs : X.cpu.gpr.rsi = 0
  · have ez : Vz V X.cpu.gpr = V := ite_cond_eq_true _ _ (eq_true hs)
    have e1 : V1 V X.cpu.gpr = V := ite_cond_eq_true _ _ (eq_true hs)
    rw [ez] at k0 kt
    rw [e1] at k1
    by_cases h0 : vtOf V X.cpu.gpr = 0#16
    · refine (c_0 prof).run c hin _ hK hA hrip' (vc_z0 hs ft h0) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact fin36 c hin hKY hAY hrY hk hsp hl hin₂ h₂ hra (k0 h0)
    by_cases h1 : vtOf V X.cpu.gpr = 19#16 ∨ vtOf V X.cpu.gpr = 21#16
    · refine (c_0 prof).run c hin _ hK hA hrip' (vc_z1 h1 hs ft rfl) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact fin51 c hin hKY hAY hrY hk hsp hl ft8 hin₂ h₂ hra (k1 h1)
    · have h19 : vtOf V X.cpu.gpr ≠ 19#16 := fun h => h1 (.inl h)
      have h21 : vtOf V X.cpu.gpr ≠ 21#16 := fun h => h1 (.inr h)
      refine (c_0 prof).run c hin _ hK hA hrip' (vc_zt hs ft h0 h19 h21) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact thr c hin hinT hT hKY hAY (.inr rfl) hrY fun Z t' hKZ hAZ hrZ hgZ =>
        kt h0 h19 h21 Z t' hKZ hAZ hrZ (by rw [hgZ]; exact hk) (by rw [hgZ]; exact hsp)
  · have ez : Vz V X.cpu.gpr = st1 V X.cpu.gpr.rsi 0#8 := ite_cond_eq_false _ _ (eq_false hs)
    have e1 : V1 V X.cpu.gpr = st1 (st1 V X.cpu.gpr.rsi 0#8) X.cpu.gpr.rsi 1#8 := ite_cond_eq_false _ _ (eq_false hs)
    rw [ez] at k0 kt
    rw [e1] at k1
    have oz : Raf.Out X.cpu.gpr.rsi.toNat (X.cpu.gpr.rsi.toNat + 1) V (st1 V X.cpu.gpr.rsi 0#8) :=
      Raf.Out.vst (toBytesLE_length _ _) hr1
    have oo : Raf.Out X.cpu.gpr.rsi.toNat (X.cpu.gpr.rsi.toNat + 1) (st1 V X.cpu.gpr.rsi 0#8)
        (st1 (st1 V X.cpu.gpr.rsi 0#8) X.cpu.gpr.rsi 1#8) := Raf.Out.vst (toBytesLE_length _ _) hr1
    have hra0 : rdq(st1 V X.cpu.gpr.rsi 0#8, X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [oz.rd hs8 (hd hs)]; exact hra
    have hra1 : rdq(st1 (st1 V X.cpu.gpr.rsi 0#8) X.cpu.gpr.rsi 1#8, X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [(oz.trans oo).rd hs8 (hd hs)]; exact hra
    by_cases h0 : vtOf V X.cpu.gpr = 0#16
    · refine (c_0 prof).run c hin _ hK hA hrip' (vc_n0 hs ft fw h0) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact fin36 c hin hKY hAY hrY hk hsp hl hin₂ h₂ hra0 (k0 h0)
    by_cases h1 : vtOf V X.cpu.gpr = 19#16 ∨ vtOf V X.cpu.gpr = 21#16
    · refine (c_0 prof).run c hin _ hK hA hrip' (vc_n1 h1 hs ft fw rfl) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact fin48 c hin hKY hAY hrY hk hsp hl ft8 fw hin₂ h₂ hra1 (k1 h1)
    · have h19 : vtOf V X.cpu.gpr ≠ 19#16 := fun h => h1 (.inl h)
      have h21 : vtOf V X.cpu.gpr ≠ 21#16 := fun h => h1 (.inr h)
      refine (c_0 prof).run c hin _ hK hA hrip' (vc_nt hs ft fw h0 h19 h21) ?_
      rintro j' g fl V₁ ⟨rfl, hk, hsp, rfl⟩ Y t₁ hKY hAY hrY hgY -
      subst hgY
      exact thr c hin hinT hT hKY hAY (.inl rfl) hrY fun Z t' hKZ hAZ hrZ hgZ =>
        kt h0 h19 h21 Z t' hKZ hAZ hrZ (by rw [hgZ]; exact hk) (by rw [hgZ]; exact hsp)

end FV7z.Gae
