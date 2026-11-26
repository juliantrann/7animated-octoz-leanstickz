import FV7z.Sfst.Cuts
import FV7z.Raf.Holds
/-!
# `CFileInfoBase::SetFrom_stat` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NFind::CFileInfoBase::SetFrom_stat (st)` at `0x4559d0` in `7zzs`
(`CPP/Windows/FileFind.cpp`), `this` = `rdi`, `st` = `rsi`: a leaf that reads 120 bytes of the `struct stat` and
writes the 104 bytes of the file info (the size, 0 for a directory: the `je` at 23; the three times through
`xmm0..2`; the mode, device, inode, `nlink`, `uid`, `gid`, `rdev`), to the `ret` (105).

The `xmm` moves leave the bytes they store any (`Op.vs`): the contract says where the function writes, not what.

- `Kp`: the registers the function keeps (`rbx`, `rbp`, `r12..r15`, `rsp`, `rsi`, `rdi`).
- `ost`: a store inside a range keeps `Raf.Out` of the range.
- `vc_0`, `vc_29`: the verification conditions of the pieces (to the copy; the copy).
- `sfst_ok`: from the entry to the return address with the bytes outside `[rdi, rdi + 104)` as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sfst

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_105 : pret <+: sfst.drop 105 := by decide +kernel
theorem ret_105 (feat : Features) : Dec feat sfst 105 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 105) (k := 0) (pret_0 feat) w_105 (Nat.zero_le _)

/-- The registers kept from `g` to `g'`. -/
def Kp (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
    g'.rsp = g.rsp ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi

/-- A store inside `[lo, hi)` keeps `Raf.Out lo hi`. -/
theorem ost {lo hi : Nat} {V V' : Addr → Byte} {a : Addr} {bs : List Byte} {n : Nat} (h : Raf.Out lo hi V V')
    (hn : bs.length = n) (ha : a.toNat + n ≤ 2 ^ 64) (h1 : lo ≤ a.toNat) (h2 : a.toNat + n ≤ hi) :
    Raf.Out lo hi V (Vst V' a bs) :=
  h.trans ((Raf.Out.vst hn ha).mono h1 h2)

theorem out_rfl {lo hi : Nat} {V : Addr → Byte} : Raf.Out lo hi V V := fun _ _ => rfl

variable {F : Footprint} {Wl : List Rgn}

/-- To the copy: the mode's type, the size or 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : ∀ i < 120, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 29 ∧ V' = V ∧ Kp g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr ⊢
  wpx [W_0, W_25, o0, o1, Kp]
  all_goals repeat' (first | exact rfl | exact Raf.off_ft hr _ rfl (by decide) | apply And.intro | intro _)

/-- The copy. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : ∀ i < 120, Foot F.data (Addr.add g.rsi i))
    (hw : ∀ i < 104, Foot Wl (Addr.add g.rdi i)) (hx : g.rdi.toNat + 104 < 2 ^ 64) :
    W_29 F Wl (fun j' g' _ V' => j' = 105 ∧ Kp g g' ∧ Raf.Out g.rdi.toNat (g.rdi.toNat + 104) V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hw hx ⊢
  wpx [W_29, o2, Kp]
  all_goals repeat' (first
    | exact rfl
    | exact fun i hi => hr i (by omega)
    | exact fun i hi => hw i (by omega)
    | exact Raf.off_ft hr _ rfl (by decide)
    | exact Raf.off_ft hw _ rfl (by decide)
    | exact out_rfl
    | refine ost ?_ (by ln) ?_ ?_ ?_
    | apply And.intro
    | intro _
    | bv_omega)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SetFrom_stat` from its entry: see the module doc. -/
theorem sfst_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sfst_at sfst) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sfst_at)
    (hr : ∀ i < 120, Foot F.data (Addr.add X.cpu.gpr.rsi i)) (hw : ∀ i < 104, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hx : X.cpu.gpr.rdi.toNat + 104 < 2 ^ 64) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 104 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Raf.Out X.cpu.gpr.rdi.toNat (X.cpu.gpr.rdi.toNat + 104) V V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp →
      Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 →
      Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 29 ∧ V' = V ∧ Kp X.cpu.gpr g') hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hr) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hKp⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  obtain ⟨hbx, hbp, h12, h13, h14, h15, hsp, hsi, hdi⟩ := hKp
  refine (c_29 prof).run c hin (fun j' g' _ V' => j' = 105 ∧ Kp Y.cpu.gpr g' ∧
      Raf.Out Y.cpu.gpr.rdi.toNat (Y.cpu.gpr.rdi.toNat + 104) V₁ V') hKY hAY hrY
    (vc_29 (by rw [hsi]; exact hr) (by rw [hdi]; exact hw) (by rw [hdi]; exact hx)) ?_
  rintro j' g₂ fl₂ V₂ ⟨rfl, hKp₂, hO⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst hg₂
  obtain ⟨hbx₂, hbp₂, h12₂, h13₂, h14₂, h15₂, hsp₂, -, -⟩ := hKp₂
  rw [hdi] at hO
  have hsp' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := hsp₂.trans hsp
  have hra' : rdq(V₂, Y₂.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hsp', hO.rd hs8 hd]
    exact hra
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_105 _) (by rw [hsp']; exact hl) hin₂ h₂ hra' ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact k Y₃ t₃ V₂ hK₃ hA₃ hO hr₃ (by rw [hg₃]; show Y₂.cpu.gpr.rsp + 8 = _; rw [hsp'])
    (by rw [hg₃]; exact hbx₂.trans hbx) (by rw [hg₃]; exact hbp₂.trans hbp) (by rw [hg₃]; exact h12₂.trans h12)
    (by rw [hg₃]; exact h13₂.trans h13) (by rw [hg₃]; exact h14₂.trans h14) (by rw [hg₃]; exact h15₂.trans h15)

end FV7z.Sfst
