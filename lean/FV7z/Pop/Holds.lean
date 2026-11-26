import FV7z.Pop.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnJm
/-!
# `CArchiveExtractCallback::PrepareOperation`, the forwarding way (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::PrepareOperation (askExtractMode)` at `0x5aa500` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`; `objdump -d`): `rax` = `this`, `rdi` = the callback at
`this + 192` (`m`); if it is set, `rax` = its vtable and `jmp qword [rax + 40]` (22, a tail jump,
`Seg.s_jmp_mx`): the call is forwarded to it. The other way (`m` not set: the flags at `this + 109`, the tail jump
through `r10` at 102) is not covered here.

- `m`: the callback at `this + 192`; `gT`: the registers at the jump.
- `vc_0t`: the verification condition of the piece.
- `pop_t`: `m` set: the run at its vtable's entry at 40 with the registers `gT` and the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pop

/-- The jump through the vtable. -/
def pjm : List Byte := [0xff, 0x60, 0x28]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.mem (mbd 0 40 64)] 3) := by dec_rfl
theorem wj_22 : pjm <+: pop.drop 22 := by decide +kernel
theorem jmp_22 (feat : Features) : Dec feat pop 22 (FV7z.mk .jmp 64 [.mem (mbd 0 40 64)] 3) :=
  Dec.shift (j := 22) (k := 0) (pjm_0 feat) wj_22 (Nat.zero_le _)

/-- The callback at `this + 192`. -/
abbrev m (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rdi + 192#64)
/-- The registers at the jump: `rax` `m`'s vtable, `rdi` = `m`. -/
abbrev gT (V : Addr → Byte) (g : Gprs) : Gprs := { g with rax := rdq(V, m V g), rdi := m V g }

variable {F : Footprint} {Wl : List Rgn}

/-- `m` set: `je` not taken, `mov rax, [rdi]`. -/
theorem vc_0t {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : m V g ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 192#64) i)) (fm : ∀ i < 8, Foot F.data (Addr.add (m V g) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = gT V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gT, m] at h fa fm ⊢
  wpx [W_0, W_19, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `PrepareOperation` (`this` = `rdi`) with the callback `m` set: at its vtable's entry at 40 (`e₂.add tgt`), the
registers `gT` and the bytes `V`. -/
theorem pop_t (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pop_at pop) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pop_at) (h : m V X.cpu.gpr ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 192#64) i))
    (fm : ∀ i < 8, Foot F.data (Addr.add (m V X.cpu.gpr) i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, m V X.cpu.gpr) + 40#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, rdq(V, m V X.cpu.gpr) + 40#64) = e₂.add tgt)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = gT V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ g' = gT V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0t h fa fm) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have he : eaD Y 0 40 = rdq(V, m V X.cpu.gpr) + 40#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 40 = _
    rw [hgY]
    rfl
  refine c.s_jmp_mx hKY hAY hin (lt_len (by decide)) hrY (jmp_22 _) (by rw [he]; exact fv) hin₂ ht
    (by rw [he]; exact htgt) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (hg₂.trans hgY)

end FV7z.Pop
