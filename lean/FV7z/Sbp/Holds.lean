import FV7z.Sbp.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `z7_SwapBytesPrepare` (0x43d3d0): from the entry to the returns (PLAN.md §M, M1)

7-Zip 26.06's `z7_SwapBytesPrepare ()` (`C/SwapBytes.c`; `objdump -d`) at `0x43d3d0` in `7zzs`: `sub rsp, 8`, the
`call` (8) of `CPU_IsSupported_AVX2` at `0x4244b0`; not 0: the mode 3 stored into `g_SwapBytes_Mode` (4 bytes at
`0x7967b8`), the `ret` (36); 0: the `call` (40) of `CPU_IsSupported_SSSE3` at `0x424340`, the mode 1 or 2 stored,
the `ret` (66). The callees' code is a hypothesis (`Ev.kA`, `Ev.kS`).

- `call_8`, `call_40`, `tgt_*`, `ret_36`, `ret_66`: the instructions outside the blocks.
- `aR`, `Fm`, `KC`, `Ev`, `callK`: the frame, the callee as a continuation, the hypotheses of the runs, a `call` and
  the run from its return.
- `vc_0`, `vc_13`, `vc_45`: the pieces.
- `sbp_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes) to the return
  (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry, the bytes some 4-byte mode stored at
  `0x7967b8` over bytes with `I`) or a callee's goal. The value of the mode is not stated.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Sbp
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `CPU_IsSupported_AVX2` (8). -/
def pc8 : List Byte := [0xe8, 0xd3, 0x70, 0xfe, 0xff]
theorem pc8_0 : ∀ feat, Dec feat pc8 0 (FV7z.mk .call 64 [.rel 18446744073709449427] 5) := by dec_rfl
theorem wc_8 : pc8 <+: sbp.drop 8 := by decide +kernel
theorem call_8 (feat : Features) : Dec feat sbp 8 (FV7z.mk .call 64 [.rel 18446744073709449427] 5) :=
  Dec.shift (j := 8) (k := 0) (pc8_0 feat) wc_8 (Nat.zero_le _)
theorem tgt_8 : sbp_at.add (8 + 5) + BitVec.ofNat 64 18446744073709449427 = 0x4244b0#64 := by decide

/-- The `call` of `CPU_IsSupported_SSSE3` (40). -/
def pc40 : List Byte := [0xe8, 0x43, 0x6f, 0xfe, 0xff]
theorem pc40_0 : ∀ feat, Dec feat pc40 0 (FV7z.mk .call 64 [.rel 18446744073709449027] 5) := by dec_rfl
theorem wc_40 : pc40 <+: sbp.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat sbp 40 (FV7z.mk .call 64 [.rel 18446744073709449027] 5) :=
  Dec.shift (j := 40) (k := 0) (pc40_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : sbp_at.add (40 + 5) + BitVec.ofNat 64 18446744073709449027 = 0x424340#64 := by decide

/-- The `ret`s (36, 66). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_36 : pret <+: sbp.drop 36 := by decide +kernel
theorem ret_36 (feat : Features) : Dec feat sbp 36 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)
theorem w_66 : pret <+: sbp.drop 66 := by decide +kernel
theorem ret_66 (feat : Features) : Dec feat sbp 66 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 66) (k := 0) (pret_0 feat) w_66 (Nat.zero_le _)

/-- `g_SwapBytes_Mode`. -/
abbrev gM : Addr := 7956408#64

/-! ## The frame -/

/-- The stack pointer after `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8#64

theorem q1 (S : Addr) : aR S + 8#64 = S := BitVec.sub_add_cancel _ _

/-- The frame from the prologue on: `rsp` = `aR S`, the callee-saved registers as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- Back from a callee (or a piece that keeps them): `rsp` given, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (sbp_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sbp_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the return address at `S`, apart from `g_SwapBytes_Mode` (`hS`, `hd`); the mode's
bytes in what the run may store into; the callees keep `I`; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L sbp_at sbp
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hS : S.toNat + 8 ≤ 2 ^ 64
  hd : gM.toNat + 4 ≤ S.toNat ∨ S.toNat + 8 ≤ gM.toNat
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  hw : ∀ i < 4, Foot Wl (Addr.add gM i)
  cA : ∃ code : List Byte, CodeIn L 0x4244b0#64 code ∧ 0 < code.length
  cS : ∃ code : List Byte, CodeIn L 0x424340#64 code ∧ 0 < code.length
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x4244b0#64 j W (fun _ => True) (fun _ => True)
  kS : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x424340#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (v : BitVec 32) (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
    Agree F Z'.proc.mm.mem (Vst W gM (toBytesLE v 4)) → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 →
    KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = sbp_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < sbp.length) (hd : Dec prof.feat sbp j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : sbp_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sbp_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ

/-- A `ret` at `j` with `rsp` = `S`, the mode stored over bytes with `I`: to `kr`. -/
theorem retK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) {U : State} {t₁ j : Nat} {v : BitVec 32}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem (Vst W gM (toBytesLE v 4)))
    (hrU : U.cpu.rip = sbp_at.add j) (hj : j < sbp.length) (hd : Dec prof.feat sbp j (FV7z.mk .ret 64 [] 1))
    (hsU : U.cpu.gpr.rsp = S) (hk : KS g0 U.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE U t₁ := by
  have hra : rdq(Vst W gM (toBytesLE v 4), S) = e₂.add j₂ := by
    rw [Tun.rd_Vst W gM (toBytesLE v 4) S 8 (by rw [toBytesLE_length]; decide) E.hS
      (by rw [toBytesLE_length]; exact E.hd)]
    exact E.hI W hIW
  refine E.c.s_ret hKU hAU E.hin hj hrU hd (by rw [hsU]; exact E.hl) E.hin₂ E.h₂ (by rw [hsU]; exact hra) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr v W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact hk

end Runs

/-! ## The pieces -/

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `sub rsp, 8`, to the `call` of `CPU_IsSupported_AVX2` at 8. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = aR g.rsp → KS g g' → ∀ fl, Q 8 g' fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR] at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | ostep)

/-- Back from `CPU_IsSupported_AVX2`: the test; 0: to the `call` of `CPU_IsSupported_SSSE3` at 40; else the mode 3
stored, `add rsp, 8`, to the `ret` at 36. -/
theorem vc_13 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hw : ∀ i < 4, Foot Wl (Addr.add gM i))
    (h40 : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 40 g' fl V)
    (h36 : ∀ g' (v : BitVec 32), g'.rsp = g.rsp + 8#64 → KS g g' →
      ∀ fl, Q 36 g' fl (Vst V gM (toBytesLE v 4))) :
    W_13 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h40 h36 ⊢
  wpx [W_13, W_26, o1, o2, Op.sta]
  all_goals repeat' (first
    | refine h40 _ ?_ ?_ _
    | refine h36 _ _ ?_ ?_ _
    | with_reducible exact hw
    | exact hw
    | ostep)

/-- Back from `CPU_IsSupported_SSSE3`: the mode 1 + (not 0) stored, `add rsp, 8`, to the `ret` at 66. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hw : ∀ i < 4, Foot Wl (Addr.add gM i))
    (h : ∀ g' (v : BitVec 32), g'.rsp = g.rsp + 8#64 → KS g g' → ∀ fl, Q 66 g' fl (Vst V gM (toBytesLE v 4))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_45, o3, Op.sta]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible exact hw
    | exact hw
    | ostep)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 45 (back from `CPU_IsSupported_SSSE3`): the mode stored, the `ret`, to `kr`. -/
theorem from45 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sbp_at.add 45) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_45 prof).run E.c E.hin (fun j' g' _ V' => j' = 66 ∧ (∃ v : BitVec 32, V' = Vst W gM (toBytesLE v 4)) ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 ∧ KS Y.cpu.gpr g') hK hA hr
    (vc_45 E.hw fun _ v a k _ => ⟨rfl, ⟨v, rfl⟩, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨v, rfl⟩, gs, gk⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact retK E hKU hAU hrU (lt_len (by decide)) (ret_66 _) (by rw [gs, hm.1]; exact q1 S)
    ⟨gk.1.trans hm.2.1, gk.2.1.trans hm.2.2.1, gk.2.2.1.trans hm.2.2.2.1, gk.2.2.2.1.trans hm.2.2.2.2.1,
      gk.2.2.2.2.1.trans hm.2.2.2.2.2.1, gk.2.2.2.2.2.trans hm.2.2.2.2.2.2⟩ hIW

/-- From 13 (back from `CPU_IsSupported_AVX2`): the mode 3 and the `ret`, or `CPU_IsSupported_SSSE3` (40) and 45. -/
theorem from13 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sbp_at.add 13) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_13 prof).run E.c E.hin (fun j' g' _ V' => KS Y.cpu.gpr g' ∧
      ((j' = 40 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp) ∨
        (j' = 36 ∧ (∃ v : BitVec 32, V' = Vst W gM (toBytesLE v 4)) ∧ g'.rsp = Y.cpu.gpr.rsp + 8#64))) hK hA hr
    (vc_13 E.hw (fun _ a k _ => ⟨k, .inl ⟨rfl, rfl, a⟩⟩)
      fun _ v a k _ => ⟨k, .inr ⟨rfl, ⟨v, rfl⟩, a⟩⟩) ?_
  rintro j' g fl V₁ ⟨gk, ⟨rfl, rfl, gs⟩ | ⟨rfl, ⟨v, rfl⟩, gs⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst hgU
    have hmU : Fm S g0 U.cpu.gpr := fm_ret hm (gs.trans hm.1) gk
    refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_40 _) tgt_40 E.cS (E.kS _ _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from45 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · subst hgU
    exact retK E hKU hAU hrU (lt_len (by decide)) (ret_36 _) (by rw [gs, hm.1]; exact q1 S)
      ⟨gk.1.trans hm.2.1, gk.2.1.trans hm.2.2.1, gk.2.2.1.trans hm.2.2.2.1, gk.2.2.2.1.trans hm.2.2.2.2.1,
        gk.2.2.2.2.1.trans hm.2.2.2.2.2.1, gk.2.2.2.2.2.trans hm.2.2.2.2.2.2⟩ hIW

/-- `z7_SwapBytesPrepare ()` from its entry (`X`'s registers, `S` = their `rsp`, `I` of the bytes). -/
theorem sbp_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbp_at) (hI0 : I V) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 8 ∧ V' = V ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_8 _) tgt_8 E.cA (E.kA _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from13 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Runs

end FV7z.Sbp
