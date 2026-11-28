import FV7z.Cir.Cuts
import FV7z.Rel.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `CInFileStream::Release ()` at `0x5a4b20` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::Release ()` (`Z7_COM_UNKNOWN_IMP_*`, `CPP/7zip/Common/FileStreams.h`), the count at
`rdi + 0x28`, at `0x5a4b20` in `7zzs`: the code of `FV7z/Rel/Holds.lean` with the count at `rdi + 0x28`, the
destructor `~CInFileStream ()` at `0x5a4040` (`FV7z/Ifd`) and the sized `operator delete (p, 0x108)` (`0x6014e0`):
`push r12; push rbp; sub rsp, 8; mov eax, [rdi + 0x28]; lea r12d, [rax - 1]; mov [rdi + 0x28], r12d;
test r12d, r12d; jne 48`; at 27 (the count 0) `mov rbp, rdi`, the `call` (30) of the destructor, at 35
`mov esi, 0x108; mov rdi, rbp`, the `call` (43) of `operator delete`; at 48 `add rsp, 8; mov eax, r12d; pop rbp;
pop r12; ret` (58): the new count in `eax`.

The callees are hypotheses (`kd`, `ke`) as in `FV7z/Rel/Holds.lean`, whose `K4`, `KS`, `Fr`, `P48` and
arithmetic are reused.

- `cnt`: the new count; `Dn`: the bytes after its store; `ob`: the object.
- `vc_0`, `vc_35`, `vc_48`: the verification conditions of the pieces; `tail48`: from 48 to the return.
- `cir_ok`: from the entry to the return address with `rsp` 8 above the entry's, the new count in `eax`, the
  callee-saved registers as they were, and the bytes `Dn` or those `operator delete` left.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cir

/-- The `call` of the destructor. -/
def pc1 : List Byte := [0xe8, 0xfd, 0xf4, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709548797] 5) := by dec_rfl
theorem wc_30 : pc1 <+: cir.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat cir 30 (FV7z.mk .call 64 [.rel 18446744073709548797] 5) :=
  Dec.shift (j := 30) (k := 0) (pc1_0 feat) wc_30 (Nat.zero_le _)
theorem tgt_30 : cir_at.add (30 + 5) + BitVec.ofNat 64 18446744073709548797 = (0x5a4040#64).add 0 := by decide

/-- The `call` of `operator delete`. -/
def pc2 : List Byte := [0xe8, 0x90, 0xc9, 0x05, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 379280] 5) := by dec_rfl
theorem wc_43 : pc2 <+: cir.drop 43 := by decide +kernel
theorem call_43 (feat : Features) : Dec feat cir 43 (FV7z.mk .call 64 [.rel 379280] 5) :=
  Dec.shift (j := 43) (k := 0) (pc2_0 feat) wc_43 (Nat.zero_le _)
theorem tgt_43 : cir_at.add (43 + 5) + BitVec.ofNat 64 379280 = (0x6014e0#64).add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_58 : pret <+: cir.drop 58 := by decide +kernel
theorem ret_58 (feat : Features) : Dec feat cir 58 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem rsi264 : BitVec.setWidth 64 (BitVec.ofNat 32 264) = 264#64 := by decide

/-! ## The pieces -/

/-- The new count. -/
abbrev cnt (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(Rel.Fr V g, g.rdi + 40#64) - 1#32

/-- The bytes after the new count's store. -/
abbrev Dn (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (Rel.Fr V g) (g.rdi + 40#64) (toBytesLE (cnt V g) 4)

/-- The object: `rdi`. -/
abbrev ob (p : Addr) : Addr := p

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: the two `push`es and the new count, then 48, or the `call` at 30 with `rdi` = `rbp` the object. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 40#64) i)) (w32 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 40#64) i))
    (h48 : ∀ g', Rel.P48 g.rsp (cnt V g) g g' → ∀ fl, Q 48 g' fl (Dn V g))
    (h30 : ∀ g', g'.rdi = ob g.rdi → g'.rbp = ob g.rdi → Rel.P48 g.rsp (cnt V g) g g' →
      ∀ fl, Q 30 g' fl (Dn V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 f32 w32 h48 h30 ⊢
  wpx [W_0, W_27, o0, o1, Rel.r24, Rel.dec32z]
  all_goals repeat' (first
    | refine h48 _ ?_ _
    | refine h30 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact f32
    | with_reducible exact w32
    | apply And.intro
    | intro _)

/-- Back from the destructor at 35: `esi` = 0x108, `rdi` = `rbp`, to the `call` at 43. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {q S : Addr} {n : BitVec 32} {g₀ : Gprs}
    (hb : g.rbp = q) (hS : g.rsp = S - 24) (hr : g.r12 = BitVec.setWidth 64 n) (hk : Rel.K4 g₀ g)
    (h : ∀ g', g'.rdi = q → g'.rsi = 264#64 → g'.rbp = q → Rel.P48 S n g₀ g' → ∀ fl, Q 43 g' fl V) :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨k1, k2, k3, k4⟩ := hk
  dsimp only at hb hS hr k1 k2 k3 k4
  subst hb hS hr
  wpx [W_35, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rsi264
    | with_reducible exact k1
    | with_reducible exact k2
    | with_reducible exact k3
    | with_reducible exact k4
    | apply And.intro
    | intro _)

/-- From 48: `add rsp, 8; mov eax, r12d; pop rbp; pop r12` to the `ret` at 58. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {S : Addr} {n : BitVec 32} {g₀ : Gprs}
    (hP : Rel.P48 S n g₀ g) (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i))
    (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (h : ∀ g', g'.rsp = S → g'.rax = BitVec.setWidth 64 n → g'.rbp = rdq(V, S - 16) → g'.r12 = rdq(V, S - 8) →
      Rel.K4 g₀ g' → ∀ fl, Q 58 g' fl V) :
    W_48 F Wl Q g f V := by
  obtain ⟨hr, hsp, hk⟩ := hP
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hsp hk
  subst hr hsp
  wpx [W_48, o3, Rel.e16, Rel.e8, Rel.e0]
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

/-- From 48 (the registers `Rel.P48`, the bytes `W`) to the return address. -/
theorem tail48 {W : Addr → Byte} {S : Addr} {n : BitVec 32} {g₀ : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L cir_at cir) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrY : Y.cpu.rip = cir_at.add 48) (hP : Rel.P48 S n g₀ Y.cpu.gpr)
    (fb : ∀ i < 8, Foot F.data (Addr.add (S - 16) i)) (fq : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr : rdq(W, S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → Z'.cpu.gpr.rax = BitVec.setWidth 64 n → Z'.cpu.gpr.rbp = rdq(W, S - 16) →
      Z'.cpu.gpr.r12 = rdq(W, S - 8) → Rel.K4 g₀ Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_48 prof).run c hin
    (fun j' g' _ V' => j' = 58 ∧ g'.rsp = S ∧ g'.rax = BitVec.setWidth 64 n ∧ g'.rbp = rdq(W, S - 16) ∧
      g'.r12 = rdq(W, S - 8) ∧ Rel.K4 g₀ g' ∧ V' = W) hK hA hrY
    (vc_48 hP fb fq fun _ hs ha hp hq hk _ => ⟨rfl, hs, ha, hp, hq, hk, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hs, ha, hp, hq, hk, hV⟩ U t₁ hKU hAU hrU hgU -
  subst hgU hV
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_58 _) (by rw [hs]; exact hl) hin₂ h₂
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

/-- `CInFileStream::Release ()` (`rdi` the object) from its entry. Either straight to the return address with the
bytes `Dn` (the new count stored), or through the destructor (`kd`: at its entry with `rsp` 32 below the entry's,
`rdi` the object) and `operator delete` (`ke`: likewise, `esi` = 0x108) to the return address with the bytes
`operator delete` left (`kr`, with `P2`). -/
theorem cir_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cir_at cir)
    {codeD : List Byte} (hinD : CodeIn L 0x5a4040#64 codeD) (hD : 0 < codeD.length)
    {codeE : List Byte} (hinE : CodeIn L 0x6014e0#64 codeE) (hE : 0 < codeE.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cir_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (w32 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (hp1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp)
    (hq1 : rdq(Dn V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12)
    (kd : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Dn V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (cir_at.add 35) 8)) →
      Y.cpu.rip = 0x5a4040#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.rbp = ob X.cpu.gpr.rdi → Y.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) →
      Rel.K4 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = cir_at.add 35 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = ob X.cpu.gpr.rdi →
        Z.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → Rel.K4 X.cpu.gpr Z.cpu.gpr → P1 Z V₁ →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (ke : ∀ (Z₁ : State) (V₁ : Addr → Byte), P1 Z₁ V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 32) (toBytesLE (cir_at.add 48) 8)) →
      Y.cpu.rip = 0x6014e0#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = 264#64 → Y.cpu.gpr.rbp = ob X.cpu.gpr.rdi →
      Y.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → Rel.K4 X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ →
        Z.cpu.rip = cir_at.add 48 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 →
        Z.cpu.gpr.r12 = BitVec.setWidth 64 (cnt V X.cpu.gpr) → Rel.K4 X.cpu.gpr Z.cpu.gpr →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → P2 Z V₂ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 (cnt V X.cpu.gpr) → Rel.KS X.cpu.gpr Z'.cpu.gpr →
      (W = Dn V X.cpu.gpr ∨ ∃ (Z : State), P2 Z W) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have fq : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 48 ∧ V' = Dn V X.cpu.gpr ∧ Rel.P48 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g') ∨
      (j' = 30 ∧ V' = Dn V X.cpu.gpr ∧ g'.rdi = ob X.cpu.gpr.rdi ∧ g'.rbp = ob X.cpu.gpr.rdi ∧
        Rel.P48 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 (by rw [Rel.q16]; exact hs2) f32 w32 (fun _ hP _ => Or.inl ⟨rfl, rfl, hP⟩)
      (fun _ hd hb hP _ => Or.inr ⟨rfl, rfl, hd, hb, hP⟩)) ?_
  rintro j' g fl' V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨rfl, rfl, hP⟩ | ⟨rfl, rfl, hd, hb, hr, hs, hk⟩
  · -- the count not 0: the `ret`
    exact tail48 c hin hKY hAY hrY hP fb fq hl hin₂ h₂ hr1 fun Z' t₂ hKZ' hAZ' hrZ' hs ha hp hq hk =>
      kr _ Z' t₂ hKZ' hAZ' hrZ' hs ha ⟨hk.1, hp.trans hp1, hq.trans hq1, hk.2⟩ (Or.inl rfl)
  · -- the destructor, then `operator delete`, then the `ret`
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs]; exact Rel.q32 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_30 _) hinD (tgt := 0) hD tgt_30
      (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine kd Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂]; exact hd)
      (by rw [hg₂]; exact hb) (by rw [hg₂]; exact hr) (by rw [hg₂]; exact hk) ?_
    intro Z V₂ t'' hKZ hAZ hrZ hzs hzb hzr hzk hP1
    refine (c_35 prof).run c hin
      (fun j' g' _ V' => j' = 43 ∧ V' = V₂ ∧ g'.rdi = ob X.cpu.gpr.rdi ∧ g'.rsi = 264#64 ∧
        g'.rbp = ob X.cpu.gpr.rdi ∧ Rel.P48 X.cpu.gpr.rsp (cnt V X.cpu.gpr) X.cpu.gpr g')
      hKZ hAZ hrZ (vc_35 hzb hzs hzr hzk fun _ hd hsi hb hP _ => ⟨rfl, rfl, hd, hsi, hb, hP⟩) ?_
    rintro j' g fl₂ V₃ ⟨rfl, rfl, hd', hsi, hb', hr', hs', hk'⟩ U t₃ hKU hAU hrU hgU -
    subst hgU
    have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hs']; exact Rel.q32 _
    refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_43 _) hinE (tgt := 0) hE tgt_43
      (by rw [hU32]; exact hs4) ?_
    rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hU32] at hA₄
    refine ke Z _ hP1 U₂ t₄ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) (by rw [hg₄]; exact hU32)
      (by rw [hg₄]; exact hd') (by rw [hg₄]; exact hsi) (by rw [hg₄]; exact hb') (by rw [hg₄]; exact hr')
      (by rw [hg₄]; exact hk') ?_
    intro Z₂ V₄ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2r hz2k hra hrp hrq hP2
    exact tail48 c hin hKZ₂ hAZ₂ hrZ₂ ⟨hz2r, hz2s, hz2k⟩ fb fq hl hin₂ h₂ hra
      fun Z' t₆ hKZ' hAZ' hrZ' hs ha hp hq hk =>
        kr _ Z' t₆ hKZ' hAZ' hrZ' hs ha ⟨hk.1, hp.trans hrp, hq.trans hrq, hk.2⟩ (Or.inr ⟨Z₂, hP2⟩)

end FV7z.Cir
