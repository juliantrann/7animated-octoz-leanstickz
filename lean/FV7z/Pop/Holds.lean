import FV7z.Pop.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnJm
import FV7z.Lemmas.FnJt
/-!
# `CArchiveExtractCallback::PrepareOperation`, the forwarding way (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::PrepareOperation (askExtractMode)` at `0x5aa500` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`; `objdump -d`): `rax` = `this`, `rdi` = the callback at
`this + 192` (`m`); if it is set, `rax` = its vtable and `jmp qword [rax + 40]` (22, a tail jump,
`Seg.s_jmp_mx`): the call is forwarded to it. Otherwise (`m` = 0, `rax` = `this`, `rdi` = 0): the byte at
`this + 109` is set to 0; if `esi` = 0 it is set to 1 unless the byte at `this + 61` is set, in which case `esi` = 1
instead (112); all three ways meet at 50: `r9` = the object at `this + 128`, `r10` = its vtable's entry at 48,
`rdi` = `this + 400` if the byte at `this + 105` is set (70); at 77 the arguments (`rdi` = `r9`, `rsi` = the word at
`this + 208`, `edx` = the byte at `this + 274`, `ecx` = `esi`, `r8` = the old `rdi`) and the tail `jmp r10` (102,
`Seg.s_jmp_rx`).

- `m`: the callback at `this + 192`; `gT`: the registers at the jump.
- `vc_0t`: the verification condition of the piece.
- `pop_t`: `m` set: the run at its vtable's entry at 40 with the registers `gT` and the bytes as they were.
- `Wb`, `gB`: the bytes and registers at 50 (`bt` the byte at `this + 109`, `si` the new `rsi`); `r9v`, `gM`: the
  registers at 77 (`di` the new `rdi`); `gJ`: at the jump through `r10`.
- `vc_0b`, `vc_50`, `vc_77`: the pieces' verification conditions.
- `pop_b`: `m` = 0, from the entry to 50; `pop_m`: from 50 to the target of `jmp r10`.
- `pop_ok`: both ways, from the entry to the tail jump's target.
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

/-- The jump through `r10`. -/
def pjr : List Byte := [0x41, 0xff, 0xe2]
theorem pjr_0 : ∀ feat, Dec feat pjr 0 (FV7z.mk .jmp 64 [gr 64 10] 3) := by dec_rfl
theorem wj_102 : pjr <+: pop.drop 102 := by decide +kernel
theorem jmp_102 (feat : Features) : Dec feat pop 102 (FV7z.mk .jmp 64 [gr 64 10] 3) :=
  Dec.shift (j := 102) (k := 0) (pjr_0 feat) wj_102 (Nat.zero_le _)

/-- The bytes at 50: `bt` at `this + 109`. -/
abbrev Wb (V : Addr → Byte) (g : Gprs) (bt : BitVec 8) : Addr → Byte := Vst V (g.rdi + 109#64) (toBytesLE bt 1)
/-- The registers at 50: `rax` = `this`, `rdi` = 0, `rsi` = `si`. -/
abbrev gB (g : Gprs) (si : BitVec 64) : Gprs := { g with rax := g.rdi, rsi := si, rdi := 0 }
/-- The object at `this + 128` (`this` = `a`). -/
abbrev r9v (V : Addr → Byte) (a : Addr) : Addr := rdq(V, a + 128#64)
/-- The registers at 77: `r9` the object, `rdx` its vtable, `r10` the vtable's entry at 48, `rdi` = `di`. -/
abbrev gM (V : Addr → Byte) (g : Gprs) (di : Addr) : Gprs :=
  { g with rdx := rdq(V, r9v V g.rax), rdi := di, r9 := r9v V g.rax,
    r10 := rdq(V, rdq(V, r9v V g.rax) + 48#64) }
/-- The registers at the jump through `r10`. -/
abbrev gJ (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
    rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (V (g.rax + 274#64))),
    rsi := rdq(V, g.rax + 208#64), rdi := g.r9, r8 := g.rdi, r11 := rdq(V, g.rax + 208#64) }

/-- A byte stored twice at the same place. -/
theorem vst1l (V : Addr → Byte) (a : Addr) : ∀ (l₁ l₂ : List Byte), l₁.length = 1 → l₂.length = 1 →
    Vst (Vst V a l₁) a l₂ = Vst V a l₂
  | [x], [y], _, _ => by
    funext z
    by_cases hz : z = a <;> simp [Vst, upd1, hz]
  | [], _, h, _ => absurd h (by decide)
  | _ :: _ :: _, _, h, _ => absurd h (by simp only [List.length_cons]; omega)
  | _, [], _, h => absurd h (by decide)
  | _, _ :: _ :: _, _, h => absurd h (by simp only [List.length_cons]; omega)

theorem vst11 {w : Nat} (V : Addr → Byte) (a : Addr) (b c : BitVec w) :
    Vst (Vst V a (toBytesLE b 1)) a (toBytesLE c 1) = Vst V a (toBytesLE c 1) :=
  vst1l V a _ _ (toBytesLE_length b 1) (toBytesLE_length c 1)

/-- `m` = 0: to 50 by one of the three ways. -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : m V g = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 192#64) i))
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 109#64) i))
    (f61 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 61#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 50 ∧ ∃ (bt : BitVec 8) (si : BitVec 64), (si = g.rsi ∨ si = 1#64) ∧
      g' = gB g si ∧ V' = Wb V g bt) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gB, Wb, m] at h fa hw f61 ⊢
  wpx [W_0, W_32, W_40, W_46, W_112, W_19, o0, o1, o2, o3, o4, o8, Op.cmpmi, h, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
    Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact ⟨_, _, Or.inl rfl, rfl, rfl⟩
    | exact ⟨_, _, Or.inr rfl, rfl, rfl⟩
    | exact ⟨_, _, Or.inl rfl, rfl, vst11 _ _ _ _⟩
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- From 50 to 77: `rdi` as it was or `this + 400`. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f128 : ∀ i < 8, Foot F.data (Addr.add (g.rax + 128#64) i))
    (f105 : ∀ i < 1, Foot F.data (Addr.add (g.rax + 105#64) i))
    (f9 : ∀ i < 8, Foot F.data (Addr.add (r9v V g.rax) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, r9v V g.rax) + 48#64) i)) :
    W_50 F Wl (fun j' g' _ V' => j' = 77 ∧ ∃ di : Addr, (di = g.rdi ∨ di = g.rax + 400#64) ∧
      g' = gM V g di ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gM, r9v] at f128 f105 f9 f48 ⊢
  wpx [W_50, W_70, o5, o6, Op.cmpmi, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact ⟨_, Or.inl rfl, rfl, rfl⟩
    | exact ⟨_, Or.inr rfl, rfl, rfl⟩
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- From 77 to the jump through `r10`. -/
theorem vc_77 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f208 : ∀ i < 8, Foot F.data (Addr.add (g.rax + 208#64) i))
    (f274 : ∀ i < 1, Foot F.data (Addr.add (g.rax + 274#64) i)) :
    W_77 F Wl (fun j' g' _ V' => j' = 102 ∧ g' = gJ V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gJ] at f208 f274 ⊢
  wpx [W_77, o7]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
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

/-- `PrepareOperation` with `m` = 0, from the entry to 50: the registers `gB` and the bytes `Wb` for some `bt` and
`si` (`rsi` as it was or 1). -/
theorem pop_b (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pop_at pop) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pop_at) (h : m V X.cpu.gpr = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 192#64) i))
    (hw : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 109#64) i))
    (f61 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 61#64) i))
    (kM : ∀ (bt : BitVec 8) (si : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Wb V X.cpu.gpr bt) → Y.cpu.rip = pop_at.add 50 → (si = X.cpu.gpr.rsi ∨ si = 1#64) →
      Y.cpu.gpr = gB X.cpu.gpr si → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 50 ∧ ∃ (bt : BitVec 8) (si : BitVec 64),
      (si = X.cpu.gpr.rsi ∨ si = 1#64) ∧ g' = gB X.cpu.gpr si ∧ V' = Wb V X.cpu.gpr bt) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0b h fa hw f61) ?_
  rintro j' g fl V₁ ⟨rfl, bt, si, hsi, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  exact kM bt si Y t₁ hKY hAY hrY hsi hgY

/-- `PrepareOperation` from 50 (`rax` = `this`): at the target of `jmp r10` with the registers `gJ` of `gM` for
some `di` (`rdi` as it was or `this + 400`) and the bytes `V`. -/
theorem pop_m (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pop_at pop) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pop_at.add 50)
    (f128 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rax + 128#64) i))
    (f105 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rax + 105#64) i))
    (f9 : ∀ i < 8, Foot F.data (Addr.add (r9v V X.cpu.gpr.rax) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, r9v V X.cpu.gpr.rax) + 48#64) i))
    (f208 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rax + 208#64) i))
    (f274 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rax + 274#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, rdq(V, r9v V X.cpu.gpr.rax) + 48#64) = e₂.add tgt)
    (k : ∀ (di : Addr) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e₂.add tgt → (di = X.cpu.gpr.rdi ∨ di = X.cpu.gpr.rax + 400#64) →
      Y.cpu.gpr = gJ V (gM V X.cpu.gpr di) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_50 prof).run c hin (fun j' g' _ V' => j' = 77 ∧ ∃ di : Addr,
      (di = X.cpu.gpr.rdi ∨ di = X.cpu.gpr.rax + 400#64) ∧ g' = gM V X.cpu.gpr di ∧ V' = V) hK hA hrip
    (vc_50 f128 f105 f9 f48) ?_
  rintro j' g fl V₁ ⟨rfl, di, hdi, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine (c_77 prof).run c hin (fun j' g' _ V' => j' = 102 ∧ g' = gJ V Y.cpu.gpr ∧ V' = V) hKY hAY hrY
    (vc_77 (by rw [hgY]; exact f208) (by rw [hgY]; exact f274)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
  subst V₂
  refine c.s_jmp_rx hKU hAU hin (lt_len (by decide)) hrU (jmp_102 _) hin₂ ht (by rw [hgU, hgY]; exact htgt)
    ?_
  rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k di Y₂ t₃ hK₂ hA₂ hr₂ hdi (by rw [hg₂, hgU, hgY])

/-- `PrepareOperation` (`this` = `rdi`), both ways: `m` set, at its vtable's entry at 40 (`e₂.add tgt`) with the
registers `gT` and the bytes `V` (`kA`); `m` = 0, at the target of `jmp r10` (`e₃.add tg₃`) with the registers `gJ`
of `gM` of `gB` and the bytes `Wb` for some `bt`, `si` (`rsi` as it was or 1) and `di` (0 or `this + 400`) (`kB`). -/
theorem pop_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pop_at pop) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pop_at)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 192#64) i))
    (fm : m V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (m V X.cpu.gpr) i))
    (fv : m V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (rdq(V, m V X.cpu.gpr) + 40#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htA : m V X.cpu.gpr ≠ 0 → rdq(V, rdq(V, m V X.cpu.gpr) + 40#64) = e₂.add tgt)
    (kA : m V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e₂.add tgt → Y.cpu.gpr = gT V X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (hw : m V X.cpu.gpr = 0 → ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 109#64) i))
    (f61 : m V X.cpu.gpr = 0 → ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 61#64) i))
    (f128 : m V X.cpu.gpr = 0 → ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 128#64) i))
    (f105 : m V X.cpu.gpr = 0 → ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 105#64) i))
    (f208 : m V X.cpu.gpr = 0 → ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 208#64) i))
    (f274 : m V X.cpu.gpr = 0 → ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 274#64) i))
    (f9 : m V X.cpu.gpr = 0 → ∀ bt, ∀ i < 8, Foot F.data (Addr.add (r9v (Wb V X.cpu.gpr bt) X.cpu.gpr.rdi) i))
    (f48 : m V X.cpu.gpr = 0 → ∀ bt, ∀ i < 8,
      Foot F.data (Addr.add (rdq(Wb V X.cpu.gpr bt, r9v (Wb V X.cpu.gpr bt) X.cpu.gpr.rdi) + 48#64) i))
    {e₃ : Addr} {code₃ : List Byte} {tg₃ : Nat} (hin₃ : CodeIn L e₃ code₃) (ht₃ : tg₃ < code₃.length)
    (htB : m V X.cpu.gpr = 0 → ∀ bt,
      rdq(Wb V X.cpu.gpr bt, rdq(Wb V X.cpu.gpr bt, r9v (Wb V X.cpu.gpr bt) X.cpu.gpr.rdi) + 48#64) = e₃.add tg₃)
    (kB : m V X.cpu.gpr = 0 → ∀ (bt : BitVec 8) (si di : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Wb V X.cpu.gpr bt) → Y.cpu.rip = e₃.add tg₃ →
      (si = X.cpu.gpr.rsi ∨ si = 1#64) → (di = 0 ∨ di = X.cpu.gpr.rdi + 400#64) →
      Y.cpu.gpr = gJ (Wb V X.cpu.gpr bt) (gM (Wb V X.cpu.gpr bt) (gB X.cpu.gpr si) di) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases h : m V X.cpu.gpr = 0
  · refine pop_b c hin hK hA hrip h fa (hw h) (f61 h) ?_
    intro bt si Y t₁ hKY hAY hrY hsi hgY
    refine pop_m c hin hKY hAY hrY (by rw [hgY]; exact f128 h) (by rw [hgY]; exact f105 h)
      (by rw [hgY]; exact f9 h bt) (by rw [hgY]; exact f48 h bt) (by rw [hgY]; exact f208 h)
      (by rw [hgY]; exact f274 h) hin₃ ht₃ (by rw [hgY]; exact htB h bt) ?_
    intro di Y₂ t₂ hK₂ hA₂ hr₂ hdi hg₂
    rw [hgY] at hdi
    exact kB h bt si di Y₂ t₂ hK₂ hA₂ hr₂ hsi hdi (by rw [hg₂, hgY])
  · exact pop_t c hin hK hA hrip h fa (fm h) (fv h) hin₂ ht (htA h) (kA h)

end FV7z.Pop
