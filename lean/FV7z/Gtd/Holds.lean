import FV7z.Gtd.Cuts
import FV7z.Lemmas.SysTod
/-!
# `__gettimeofday` asks the kernel the time (PLAN.md §M, M1)

glibc's `__gettimeofday (tv, tz)` at `0x660360` in `7zzs`. It saves `r12` and `rbp` (then `tv` and `tz`), clears
`tz`'s first byte unless `tz` is 0 (the store at 128), and loads the vDSO's `gettimeofday`
(`GLRO(dl_vdso_gettimeofday)`, 8 bytes at `0x791cd0`). When that is 0 it asks the kernel `gettimeofday (tv, tz)`
(the `syscall` at 107); the answer is then 0 (`Lemmas/SysTod.lean`), not an error, so it restores `rbp` and `r12`
and reaches the `ret` at 127.

- `vc_0`, `vc_22`, `vc_96`, `vc_109`: the verification conditions of the pieces (`Gtd/Cuts.lean`).
- `gtd_ok`: from the entry, `tv` not 0 with its 16 bytes in what the run may store into, `tz` 0 or its 8 bytes so,
  the vDSO's entry 0: the run goes on from the state after the `syscall` (`todY`), its own start, and reaches the
  `ret` at 127 with `todV`'s bytes, `rax` 0, `rsp` as at the entry and `rbp`, `r12` the saved ones.

The way through the vDSO (the `call rax` at 40, then 42 .. 81 and the `errno` store at 60) is not one of these runs:
it needs the vDSO's contract (`ZellicX86.VdsoImplements`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fn.Seg
namespace FV7z.Gtd

set_option linter.unusedSimpArgs false

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_107 : psys <+: gtd.drop 107 := by decide +kernel
theorem sys_107 (feat : Features) : Dec feat gtd 107 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 107) (k := 0) (psys_0 feat) w_107 (Nat.zero_le _)

/-- The stack pointer after the two pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8#64

theorem q1 (S : Addr) : aR S + 8#64 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8#64 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8#64 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

/-- The bytes after the two pushes (`r12`, `rbp`) and, unless `tz` is 0, `tz`'s first byte cleared. -/
def V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if g.rsi = 0 then Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)
  else Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) g.rsi
    (toBytesLE (BitVec.ofNat 8 0) 1)

/-- The registers from the prologue on, from those at the entry `g0`: `rsp` = `aR`, `r12` = `tv`, `rbp` = `tz`, the
other callee-saved and the arguments `rdx`, `r8`..`r10` as at the entry. -/
abbrev Fm (g0 g : Gprs) : Prop :=
  g.rsp = aR g0.rsp ∧ g.r12 = g0.rdi ∧ g.rbp = g0.rsi ∧ g.rbx = g0.rbx ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15 ∧ g.rdx = g0.rdx ∧ g.r8 = g0.r8 ∧ g.r9 = g0.r9 ∧ g.r10 = g0.r10

/-- What a piece keeps: the registers `Fm` speaks of. -/
abbrev Fk (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.rbp = g.rbp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15 ∧ g'.rdx = g.rdx ∧ g'.r8 = g.r8 ∧ g'.r9 = g.r9 ∧ g'.r10 = g.r10

theorem fm_fk {g0 g g' : Gprs} (h : Fm g0 g) (h' : Fk g g') : Fm g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2.2.2.2⟩

theorem fm_mk {g0 g : Gprs} (a : g.rsp = aR g0.rsp) (b : g.r12 = g0.rdi) (c : g.rbp = g0.rsi) (d : g.rbx = g0.rbx)
    (e : g.r13 = g0.r13) (f : g.r14 = g0.r14) (h : g.r15 = g0.r15) (i : g.rdx = g0.rdx) (j : g.r8 = g0.r8)
    (k : g.r9 = g0.r9) (l : g.r10 = g0.r10) : Fm g0 g := ⟨a, b, c, d, e, f, h, i, j, k, l⟩

theorem fk_mk {g g' : Gprs} (a : g'.rsp = g.rsp) (b : g'.r12 = g.r12) (c : g'.rbp = g.rbp) (d : g'.rbx = g.rbx)
    (e : g'.r13 = g.r13) (f : g'.r14 = g.r14) (h : g'.r15 = g.r15) (i : g'.rdx = g.rdx) (j : g'.r8 = g.r8)
    (k : g'.r9 = g.r9) (l : g'.r10 = g.r10) : Fk g g' := ⟨a, b, c, d, e, f, h, i, j, k, l⟩

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the pushes of `r12` and `rbp`, `r12` = `tv`, `rbp` = `tz`, `sub rsp, 8`, `test rsi, rsi`: unless `tz`
is 0 `mov byte [rsi], 0`; to 22. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hz : g.rsi ≠ 0 → ∀ i < 1, Foot Wl (Addr.add g.rsi i))
    (h22 : ∀ g', Fm g g' → ∀ fl, Q 22 g' fl (V1 V g)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  by_cases h0 : rsi = 0
  · subst h0
    simp only [V1, eq_self_iff_true, ↓reduceIte] at h22
    dsimp only [aR] at hs1 hs2 h22 ⊢
    wpx [W_0, W_128, o0, o9, Op.sti, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h22 _ (fm_mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) _
      | with_reducible exact hs1
      | with_reducible exact hs2
      | ostep)
  · have hz' := hz h0
    simp only [V1, h0, ↓reduceIte] at h22
    dsimp only [aR] at hs1 hs2 hz' h22 ⊢
    wpx [W_0, W_128, o0, o9, Op.sti, eaG, optV, BitVec.mul_one, BitVec.add_zero, BitVec.and_self, h0, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h22 _ (fm_mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) _
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hz'
      | ostep)

/-- The vDSO's `gettimeofday` loaded, 0: to 96. -/
theorem vc_22 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add 7937232#64 i)) (hv : rdq(V, 7937232#64) = 0)
    (h96 : ∀ g', Fk g g' → ∀ fl, Q 96 g' fl V) :
    W_22 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h96 ⊢
  wpx [W_22, W_34, o1, o2, Op.lda, hv, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat' (first
    | refine h96 _ (fk_mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) _
    | with_reducible exact hf
    | ostep)

/-- `rsi` = `rbp`, `rdi` = `r12`, `eax` = 96: to the `syscall`. -/
theorem vc_96 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h107 : ∀ g', Fk g g' → g'.rdi = g.r12 → g'.rsi = g.rbp → g'.rax = 96#64 → ∀ fl, Q 107 g' fl V) :
    W_96 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h107 ⊢
  wpx [W_96, o7]
  all_goals repeat' (first
    | refine h107 _ (fk_mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_ _
    | ostep)

/-- After the `syscall`, the answer 0: `rdx` = 0, not above `-4096`; `add rsp, 8`, the pops, to the `ret`. -/
theorem vc_109 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h0 : g.rax = 0)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h127 : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 8#64) →
      g'.r12 = rdq(V, g.rsp + 8#64 + 8) → g'.rax = 0 → g'.rbx = g.rbx → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 127 g' fl V) :
    W_109 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h0' : rax = 0 := h0
  subst h0'
  dsimp only at f1 f2 h127 ⊢
  wpx [W_109, W_120, o8, o6, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, implies_true]
  all_goals repeat' (first
    | refine h127 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | ostep)

end Pieces

/-! ## The run -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes at the `ret`, the stream at `t₁` at the `syscall`: `V1`'s, then the kernel's writes. -/
abbrev Wf (o : Oracle) (t₁ : Nat) (V : Addr → Byte) (g : Gprs) : Addr → Byte := todV o t₁ g.rdi g.rsi (V1 V g)

/-- `__gettimeofday (tv, tz)` from a start with no `rseq` area, its entry `X`: the two saved registers' slots in
what the run may store into and may read, `tv` not 0 with its 16 bytes below the end of the user address space and
in what the run may store into, `tz` 0 or its 8 bytes so, the vDSO's entry (8 bytes at `0x791cd0`, after the pushes
and `tz`'s byte) 0. The run goes on from the state after the `syscall` (`todY` of the state `S` at it, the stream at
some `t₁`), a new start, and reaches the `ret` at 127 with the bytes `Wf`, `rax` 0, `rsp` as at the entry, `rbp`
and `r12` read from their slots and `rbx`, `r13`..`r15` as at the entry. -/
theorem gtd_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L gtd_at gtd) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gtd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (fs1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (fs2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hfv : ∀ i < 8, Foot F.data (Addr.add 7937232#64 i)) (hv : rdq(V1 V X.cpu.gpr, 7937232#64) = 0)
    (htv : X.cpu.gpr.rdi ≠ 0) (htop : X.cpu.gpr.rdi.toNat + 16 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 16, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hz : X.cpu.gpr.rsi ≠ 0 → X.cpu.gpr.rsi.toNat + 8 ≤ userPtrMax prof.feat ∧
      ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (k : ∀ (S : State) (t₁ : Nat), Fm X.cpu.gpr S.cpu.gpr → S.cpu.gpr.rdi = X.cpu.gpr.rdi →
      S.cpu.gpr.rsi = X.cpu.gpr.rsi → S.cpu.gpr.rax = 96#64 → Seg prof F Wl L (todY S 2 o t₁) o →
      ∀ Z t', KeptW Wl (todY S 2 o t₁) Z → Agree F Z.proc.mm.mem (Wf o t₁ V X.cpu.gpr) →
      Z.cpu.rip = gtd_at.add 127 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp → Z.cpu.gpr.rax = 0 →
      Z.cpu.gpr.rbp = rdq(Wf o t₁ V X.cpu.gpr, X.cpu.gpr.rsp - 8 - 8) →
      Z.cpu.gpr.r12 = rdq(Wf o t₁ V X.cpu.gpr, X.cpu.gpr.rsp - 8) → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [todEv S.cpu.gpr o t₁]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to 22
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 22 ∧ Fm X.cpu.gpr g' ∧ V' = V1 V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hs1 hs2 (fun h i hi => (hz h).2 i (by omega))
      fun g' h _ => ⟨rfl, h, rfl⟩) ?_
  rintro j' g fl V' ⟨rfl, hm, rfl⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  -- to 96
  refine (c_22 prof fb).run c hfs hin (fun j' g' _ V' => j' = 96 ∧ Fk Y.cpu.gpr g' ∧ V' = V1 V X.cpu.gpr) hKY hAY
    hrY (vc_22 hfv hv fun g' h _ => ⟨rfl, h, rfl⟩) ?_
  rintro j' g fl V' ⟨rfl, hk, rfl⟩ Y₂ t₂ hKY₂ hAY₂ hrY₂ hgY₂ -
  subst hgY₂
  have hm₂ := fm_fk hm hk
  -- to 107
  refine (c_96 prof fb).run c hfs hin (fun j' g' _ V' => j' = 107 ∧ Fk Y₂.cpu.gpr g' ∧ g'.rdi = Y₂.cpu.gpr.r12 ∧
      g'.rsi = Y₂.cpu.gpr.rbp ∧ g'.rax = 96#64 ∧ V' = V1 V X.cpu.gpr) hKY₂ hAY₂ hrY₂
    (vc_96 fun g' h a b c _ => ⟨rfl, h, a, b, c, rfl⟩) ?_
  rintro j' g fl V' ⟨rfl, hk₃, hdi, hsi, hax, rfl⟩ Y₃ t₃ hKY₃ hAY₃ hrY₃ hgY₃ -
  subst hgY₃
  have hm₃ := fm_fk hm₂ hk₃
  have hdi' : Y₃.cpu.gpr.rdi = X.cpu.gpr.rdi := hdi.trans hm₂.2.1
  have hsi' : Y₃.cpu.gpr.rsi = X.cpu.gpr.rsi := hsi.trans hm₂.2.2.1
  -- the `syscall`
  refine c.s_gettimeofday_re hrs hKY₃ hAY₃ hin (lt_len (by decide)) hrY₃ (sys_107 _) (by rw [hax]; decide)
    (by rw [hdi']; exact htv) (by rw [hdi']; exact htop) (by rw [hdi']; exact hst)
    (by rw [hsi']; exact hz) ?_
  intro M t₄ hKM hAM c₁ hA₁
  rw [hdi', hsi'] at hA₁
  have hfs₁ : (todY (Y₃.withMem M) 2 o t₄).cpu.seg.fsBase = fb := by
    show Y₃.cpu.seg.fsBase = fb
    rw [hKY₃.seg]
    exact hfs
  have hrip₁ : (todY (Y₃.withMem M) 2 o t₄).cpu.rip = gtd_at.add 109 := rip_add hrY₃ M 2
  have hsp : (todY (Y₃.withMem M) 2 o t₄).cpu.gpr.rsp = aR X.cpu.gpr.rsp := hm₃.1
  -- to the `ret`
  refine (c_109 prof fb).run c₁ hfs₁ hin (fun j' g' _ V' => j' = 127 ∧ V' = Wf o t₄ V X.cpu.gpr ∧
      g'.rsp = (todY (Y₃.withMem M) 2 o t₄).cpu.gpr.rsp + 8#64 + 8 + 8 ∧
      g'.rbp = rdq(Wf o t₄ V X.cpu.gpr, (todY (Y₃.withMem M) 2 o t₄).cpu.gpr.rsp + 8#64) ∧
      g'.r12 = rdq(Wf o t₄ V X.cpu.gpr, (todY (Y₃.withMem M) 2 o t₄).cpu.gpr.rsp + 8#64 + 8) ∧ g'.rax = 0 ∧
      g'.rbx = Y₃.cpu.gpr.rbx ∧ g'.r13 = Y₃.cpu.gpr.r13 ∧ g'.r14 = Y₃.cpu.gpr.r14 ∧ g'.r15 = Y₃.cpu.gpr.r15)
    (KeptW.refl _ _) hA₁ hrip₁
    (vc_109 rfl (by rw [hsp, q1]; exact fs1) (by rw [hsp, q2]; exact fs2)
      fun g' a b c d e m n p _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V' ⟨rfl, rfl, gs, gb, g12, gax, gbx, g13, g14, g15⟩ Z t₅ hKZ hAZ hrZ hgZ -
  subst hgZ
  rw [hsp] at gs gb g12
  exact k (Y₃.withMem M) t₄ hm₃ hdi' hsi' hax c₁ Z t₅ hKZ hAZ hrZ (gs.trans (q3 _)) gax (gb.trans (by rw [q1]))
    (g12.trans (by rw [q2])) (gbx.trans hm₃.2.2.2.1) (g13.trans hm₃.2.2.2.2.1) (g14.trans hm₃.2.2.2.2.2.1)
    (g15.trans hm₃.2.2.2.2.2.2.1)

end Runs

end FV7z.Gtd
