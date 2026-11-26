import FV7z.Ost.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `COpenCallbackConsole::Open_SetTotal` (PLAN.md §M, M1)

7-Zip 26.06's `COpenCallbackConsole::Open_SetTotal (files, bytes)` at `0x5f65b0` in `7zzs`
(`CPP/7zip/UI/Console/OpenCallbackConsole.cpp`; `objdump -d`), for the object at `p` = `rdi`: with the byte at `p + 249`
0, the 8 bytes at `p + 64` not 0 and the byte at `p + 72` 0 (`Pc`), the percent printer's fields stored from `files`
(`rsi`) and `bytes` (`rdx`) as the code does (`Mo`); then `rax` = `E_ABORT` (`0x80004004`) or `S_OK` (0) as the 4
bytes at `0x79f088` (`NConsoleClose::g_BreakCounter`) are not 0 or 0 (`rE`). One `ret` (79).

- `Ft`: the bytes read and stored; `vc_0`: from the entry to 60; `vc_60`: from 60 to the `ret`.
- `ost_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ost

set_option linter.unusedSimpArgs false

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_79 : pret <+: ost.drop 79 := by decide +kernel
theorem ret_79 (feat : Features) : Dec feat ost 79 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 79) (k := 0) (pret_0 feat) w_79 (Nat.zero_le _)

/-- The byte at `a`. -/
abbrev rb (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs a 1).map V)

/-- The percents are shown: the fields read at the entry. -/
abbrev Pc (V : Addr → Byte) (p : Addr) : Prop :=
  rb V (p + 249#64) = 0#8 ∧ rdq(V, p + 64#64) ≠ 0#64 ∧ rb V (p + 72#64) = 0#8

/-- `files` null: the byte 0 at `p + 248`. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rdi + 248#64) (toBytesLE 0#8 1)

/-- `files` not null: the byte 1 at `p + 248` and `*files` at `p + 16`. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rdi + 248#64) (toBytesLE 1#8 1)) (g.rdi + 16#64) (toBytesLE rdq(V, g.rsi) 8)

/-- The bytes after the stores. -/
def Mo (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if Pc V g.rdi then
    if g.rsi = 0#64 then
      if g.rdx = 0#64 then Vst (V1 V g) (g.rdi + 16#64) (toBytesLE rdq(V1 V g, g.rdi + 240#64) 8)
      else Vst (Vst (V1 V g) (g.rdi + 240#64) (toBytesLE rdq(V1 V g, g.rdx) 8)) (g.rdi + 16#64)
        (toBytesLE rdq(V1 V g, g.rdx) 8)
    else if g.rdx = 0#64 then V2 V g else Vst (V2 V g) (g.rdi + 240#64) (toBytesLE rdq(V2 V g, g.rdx) 8)
  else V

/-- The result from the break counter `x`: `S_OK` or `E_ABORT`. -/
def rE (x : BitVec 32) : BitVec 64 := if x = 0#32 then 0#64 else 2147500036#64

/-- The registers at the return: `rax` the result. -/
abbrev gO (V : Addr → Byte) (g : Gprs) : Gprs := { g with rax := rE rdd(Mo V g, 7991432#64) }

/-- The bytes the method reads (`F.data`) and stores into (`Wl`) for the object at `g.rdi`, `files` = `g.rsi` and
`bytes` = `g.rdx`. -/
structure Ft (F : Footprint) (Wl : List Rgn) (g : Gprs) : Prop where
  r249 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 249#64) i)
  r64 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i)
  r72 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 72#64) i)
  r240 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 240#64) i)
  rs : g.rsi ≠ 0#64 → ∀ i < 8, Foot F.data (Addr.add g.rsi i)
  rd : g.rdx ≠ 0#64 → ∀ i < 8, Foot F.data (Addr.add g.rdx i)
  w248 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 248#64) i)
  w16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i)
  w240 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 240#64) i)

/-- Closes what `wpx` leaves: equalities by `rfl` or `decide`, footprints from the hypotheses. -/
macro "opx" : tactic => `(tactic| (
  all_goals repeat'
    (first
      | exact rfl
      | exact trivial
      | assumption
      | decide
      | apply And.intro
      | intro _)))

set_option hygiene false in
/-- `opx`, and a guard against one of `h0'`, `h1'`, `h2'`, `hs'`, `hd'` (where `wpx` leaves it) closed by defeq. -/
macro "opk" : tactic => `(tactic| (
  all_goals repeat'
    (first
      | exact rfl
      | exact trivial
      | assumption
      | apply And.intro
      | intro _
      | (exfalso; exact absurd (Eq.trans (Eq.symm h0') ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm (congrArg Bool.not h0')) ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm h1') ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm (congrArg Bool.not h1')) ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm h2') ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm (congrArg Bool.not h2')) ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm hs') ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm (congrArg Bool.not hs')) ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm hd') ‹_›) (by decide))
      | (exfalso; exact absurd (Eq.trans (Eq.symm (congrArg Bool.not hd')) ‹_›) (by decide))
      | intro _)))

/-- The simp set for the branches. -/
macro "wpo" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  wpx [W_0, W_13, W_20, W_26, W_31, W_50, W_80, W_92, W_112, o0, o1, o2, o3, o4, o5, o7, o8, o9, Op.cmpmi,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self, $ls,*])

/-- The path's facts on what `wpo` leaves. -/
macro "bsimp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, true_and, and_true, forall_const, $ls,*])

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 800000 in
/-- From the entry to 60: the registers as at the entry but `rax`, the bytes `Mo`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hF : Ft F Wl g) :
    W_0 F Wl (fun j' g' _ V' => j' = 60 ∧ g' = { g with rax := g'.rax } ∧ V' = Mo V g) g f V := by
  obtain ⟨f249, f64, f72, f240, fs, fd, w248, w16, w240⟩ := hF
  by_cases h0 : rb V (g.rdi + 249#64) = 0#8
  rotate_left
  · rw [Mo, if_neg (fun h => h0 h.1)]
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 f249 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = false := decide_eq_false h0
    wpo [h0']
    opx
  by_cases h1 : rdq(V, g.rdi + 64#64) = 0#64
  · rw [Mo, if_neg (fun h => h.2.1 h1)]
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 f249 f64 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = true := decide_eq_true h1
    revert h0' h1'
    wpo [and_self]
    intro h0' h1'
    try bsimp [h0', h1']
    opk
  by_cases h2 : rb V (g.rdi + 72#64) = 0#8
  rotate_left
  · rw [Mo, if_neg (fun h => h2 h.2.2)]
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 h2 f249 f64 f72 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = false := decide_eq_false h1
    have h2' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 72#64) 1)) = 0#8) = false := decide_eq_false h2
    revert h0' h1' h2'
    wpo [and_self]
    intro h0' h1' h2'
    try bsimp [h0', h1', h2']
    opk
  rw [Mo, if_pos (show Pc V g.rdi from ⟨h0, h1, h2⟩)]
  by_cases hs : g.rsi = 0#64 <;> by_cases hd : g.rdx = 0#64
  · rw [if_pos hs, if_pos hd]
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 h2 hs hd f249 f64 f72 f240 w248 w16 w240 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = false := decide_eq_false h1
    have h2' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 72#64) 1)) = 0#8) = true := decide_eq_true h2
    have hs' : (rsi == 0) = true := by rw [hs]; rfl
    have hd' : (rdx == 0) = true := by rw [hd]; rfl
    revert h0' h1' h2' hs' hd'
    wpo [and_self]
    intro h0' h1' h2' hs' hd'
    try bsimp [h0', h1', h2', hs', hd']
    opk
  · rw [if_pos hs, if_neg hd]
    have fd' := fd hd
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 h2 hs hd f249 f64 f72 fd' w248 w16 w240 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = false := decide_eq_false h1
    have h2' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 72#64) 1)) = 0#8) = true := decide_eq_true h2
    have hs' : (rsi == 0) = true := by rw [hs]; rfl
    have hd' : (rdx == 0) = false := beq_eq_false_iff_ne.2 hd
    revert h0' h1' h2' hs' hd'
    wpo [and_self]
    intro h0' h1' h2' hs' hd'
    try bsimp [h0', h1', h2', hs', hd']
    opk
  · rw [if_neg hs, if_pos hd]
    have fs' := fs hs
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 h2 hs hd f249 f64 f72 fs' w248 w16 w240 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = false := decide_eq_false h1
    have h2' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 72#64) 1)) = 0#8) = true := decide_eq_true h2
    have hs' : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
    have hd' : (rdx == 0) = true := by rw [hd]; rfl
    revert h0' h1' h2' hs' hd'
    wpo [and_self]
    intro h0' h1' h2' hs' hd'
    try bsimp [h0', h1', h2', hs', hd']
    opk
  · rw [if_neg hs, if_neg hd]
    have fs' := fs hs
    have fd' := fd hd
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at h0 h1 h2 hs hd f249 f64 f72 fs' fd' w248 w16 w240 ⊢
    have h0' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 249#64) 1)) = 0#8) = true := decide_eq_true h0
    have h1' : decide (ofBytesLE 64 (List.map V (byteAddrs (rdi + 64#64) 8)) = 0#64) = false := decide_eq_false h1
    have h2' : decide (ofBytesLE 8 (List.map V (byteAddrs (rdi + 72#64) 1)) = 0#8) = true := decide_eq_true h2
    have hs' : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
    have hd' : (rdx == 0) = false := beq_eq_false_iff_ne.2 hd
    revert h0' h1' h2' hs' hd'
    wpo [and_self]
    intro h0' h1' h2' hs' hd'
    try bsimp [h0', h1', h2', hs', hd']
    opk

/-- From 60 to the `ret`: `rax` the result `rE` of the break counter. -/
theorem vc_60 {g : Gprs} {f : Rflags} {V : Addr → Byte} (gb : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i)) :
    W_60 F Wl (fun j' g' _ V' => j' = 79 ∧ g'.rax = rE rdd(V, 7991432#64) ∧ g' = { g with rax := g'.rax } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  by_cases hx : rdd(V, 7991432#64) = 0#32
  · have hc : decide ((rdd(V, 7991432#64)).toNat < 1) = true := by rw [hx]; rfl
    have hr : rE rdd(V, 7991432#64) = 0#64 := if_pos hx
    wpx [W_60, o6, Op.cmpmi, Op.not32, hc, hr]
    opx
  · have hc : decide ((rdd(V, 7991432#64)).toNat < 1) = false :=
      decide_eq_false (fun h => hx (by bv_omega))
    have hr : rE rdd(V, 7991432#64) = 2147500036#64 := if_neg hx
    wpx [W_60, o6, Op.cmpmi, Op.not32, hc, hr]
    opx

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COpenCallbackConsole::Open_SetTotal (files, bytes)` from its entry to the return address: the bytes `Mo`, the
registers `gO` (`rax` the result) but `rsp`. -/
theorem ost_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ost_at ost) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ost_at) (hF : Ft F Wl X.cpu.gpr)
    (gb : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Mo V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mo V X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (gO V X.cpu.gpr).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 60 ∧ g' = { X.cpu.gpr with rax := g'.rax } ∧ V' = Mo V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hF) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have e1 : Y.cpu.gpr = { X.cpu.gpr with rax := g.rax } := hgY.trans hg
  refine (c_60 prof).run c hin
    (fun j' g' _ V' => j' = 79 ∧ g'.rax = rE rdd(Mo V X.cpu.gpr, 7991432#64) ∧
      g' = { Y.cpu.gpr with rax := g'.rax } ∧ V' = Mo V X.cpu.gpr) hKY hAY hrY (vc_60 gb) ?_
  rintro j' g₂ fl₂ V₂ ⟨rfl, hax, hg₂, hV₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hgY₂ -
  subst V₂
  have e2 : Y₂.cpu.gpr = { Y.cpu.gpr with rax := rE rdd(Mo V X.cpu.gpr, 7991432#64) } := by
    rw [hgY₂, hg₂, hax]
  have hsp : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [e2, e1]
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_79 _) (by rw [hsp]; exact hl) hin₂ h₂
    (by rw [hsp]; exact hra) ?_
  rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₃ hKZ hAZ hrZ (by rw [hgZ, hsp, e2, e1])

end FV7z.Ost
