import FV7z.Sto.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.FnJt
/-!
# `COpenCallbackImp::SetTotal` (PLAN.md §M, M1)

7-Zip 26.06's `COpenCallbackImp::SetTotal (files, bytes)` at `0x5b2c80` in `7zzs` (`CPP/7zip/UI/Common/
ArchiveOpenCallback.cpp`; `objdump -d`): `if (ReOpenCallback) return ReOpenCallback->SetTotal (files,
bytes); if (!Callback) return S_OK; return Callback->Open_SetTotal (files, bytes)`. `r8` = `ReOpenCallback` (the 8
bytes at `this + 96`, `q`); if it is set, `rdi` = `r8`, `rax` = its vtable's entry at 24 and `jmp rax` (23, a tail
jump, `Seg.s_jmp_rx`). Else `rdi` = `Callback` (the 8 bytes at `this + 104`, `s`); if it is set, `sub rsp, 8`,
`rax` = its vtable, `call qword [rax + 8]` (48, `Seg.s_callM`), `add rsp, 8; ret` (51 to 55); else `xor eax, eax;
ret` (64 to 66).

The callee of the `call` is a hypothesis (`kf`), as in `FV7z.Ris`: a continuation at its entry, given the run from
its return (`sto_at + 51`, `rsp` 8 below the entry's, the return address of `SetTotal` left as it was, and the
callee's own post `Pc`) to the return address.

- `q`, `s`: `ReOpenCallback` and `Callback`; `gR`, `gC`, `gZ`: the registers at the jump, at the `call` and at the
  `ret` (64 to 66).
- `vc_0r`, `vc_0c`, `vc_0z`, `vc_51`: the verification conditions of the pieces.
- `sto_r`: `ReOpenCallback` set: the run at its vtable's entry with the registers `gR` and the bytes as they were.
- `sto_c`: `ReOpenCallback` not set, `Callback` set: through the callee to the return address.
- `sto_z`: neither set: to the return address with `rax` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sto

/-- The jump through `rax`. -/
def pjm : List Byte := [0xff, 0xe0]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem wj_23 : pjm <+: sto.drop 23 := by decide +kernel
theorem jmp_23 (feat : Features) : Dec feat sto 23 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 23) (k := 0) (pjm_0 feat) wj_23 (Nat.zero_le _)

/-- The `call` through the vtable. -/
def pcall : List Byte := [0xff, 0x50, 0x08]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) := by dec_rfl
theorem wc_48 : pcall <+: sto.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat sto 48 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) :=
  Dec.shift (j := 48) (k := 0) (pcall_0 feat) wc_48 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_55 : pret <+: sto.drop 55 := by decide +kernel
theorem ret_55 (feat : Features) : Dec feat sto 55 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 55) (k := 0) (pret_0 feat) w_55 (Nat.zero_le _)
theorem w_66 : pret <+: sto.drop 66 := by decide +kernel
theorem ret_66 (feat : Features) : Dec feat sto 66 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 66) (k := 0) (pret_0 feat) w_66 (Nat.zero_le _)

/-- `ReOpenCallback`. -/
abbrev q (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rdi + 96#64)
/-- `Callback`. -/
abbrev s (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rdi + 104#64)
/-- The registers at the jump: `rax` the entry at 24 of `ReOpenCallback`'s vtable, `rdi` = `r8` = it. -/
abbrev gR (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V, rdq(V, q V g) + 24#64), rdi := q V g, r8 := q V g }
/-- The registers at the `call`: `rax` `Callback`'s vtable, `rdi` = it, `r8` 0. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V, s V g), rsp := g.rsp - 8#64, rdi := s V g, r8 := 0#64 }
/-- The registers at the `ret` (66). -/
abbrev gZ (g : Gprs) : Gprs := { g with rax := 0#64, rdi := 0#64, r8 := 0#64 }

theorem b16 (S : Addr) : S - 8#64 - 8 = S - 16 := by bv_omega
theorem u8 (S : Addr) : S - 8#64 + 8#64 = S := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- `ReOpenCallback` set: `je` not taken, up to the jump. -/
theorem vc_0r {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : q V g ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i)) (fq : ∀ i < 8, Foot F.data (Addr.add (q V g) i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, q V g) + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 23 ∧ g' = gR V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gR, q] at h fa fq fv ⊢
  wpx [W_0, W_13, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | (intro hh; exact absurd hh h)
    | apply And.intro | intro _)

/-- `ReOpenCallback` not set, `Callback` set: `je` taken, `je` not taken, `sub rsp, 8; mov rax, [rdi]`. -/
theorem vc_0c {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : q V g = 0) (h : s V g ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 104#64) i)) (fs : ∀ i < 8, Foot F.data (Addr.add (s V g) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, q, s] at h0 h fa fb fs ⊢
  wpx [W_0, W_32, W_41, o0, o2, o3, h0, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true,
    implies_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh (by decide)) | apply And.intro | intro _)

/-- Neither set: `je` taken twice, `xor eax, eax`. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : q V g = 0) (h1 : s V g = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 104#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 66 ∧ g' = gZ g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gZ, q, s] at h0 h1 fa fb ⊢
  wpx [W_0, W_32, W_64, o0, o2, o5, h0, h1, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
    beq_iff_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false,
    Bool.false_eq_true, implies_true, decide_false, decide_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | (intro hh; exact absurd hh (by decide))
    | apply And.intro | intro _)

/-- `add rsp, 8`. -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 55 { g with rsp := g.rsp + 8#64 } fl V) : W_51 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_51, o4]
  first
  | exact h _
  | exact fun _ => h _
  | simpa using h _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SetTotal` (`this` = `rdi`) with `ReOpenCallback` (`q`) set: at its vtable's entry at 24 (`e₂.add tgt`), the
registers `gR` and the bytes `V`. -/
theorem sto_r (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sto_at sto) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sto_at) (h : q V X.cpu.gpr ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (fq : ∀ i < 8, Foot F.data (Addr.add (q V X.cpu.gpr) i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, q V X.cpu.gpr) + 24#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, rdq(V, q V X.cpu.gpr) + 24#64) = e₂.add tgt)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = gR V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 23 ∧ g' = gR V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0r h fa fq fv) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_jmp_rx hKY hAY hin (lt_len (by decide)) hrY (jmp_23 _) hin₂ ht (by rw [hgY]; exact htgt) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (hg₂.trans hgY)

/-- `SetTotal` with neither `ReOpenCallback` nor `Callback` set: at the return address with `rax` = `rdi` = `r8` =
0 and the bytes `V`. -/
theorem sto_z (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sto_at sto) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sto_at) (h0 : q V X.cpu.gpr = 0) (h1 : s V X.cpu.gpr = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 104#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (gZ X.cpu.gpr).set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 66 ∧ g' = gZ X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0z h0 h1 fa fb) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_66 _) (by rw [hsY]; exact hl) hin₂ h₂
    (by rw [hsY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hgY]
  try rfl

/-- `SetTotal` with `ReOpenCallback` not set and `Callback` (`s`) set. At the callee's entry `eF` (the 8 bytes at
its vtable + 8) the registers are `gC` with `rsp` 16 below the entry's and the bytes `V` with the return address
into `SetTotal` pushed (`kf`); if the callee returns to `sto_at + 51` with `rsp` as at its entry and the return
address of `SetTotal` as it was, the run reaches that return address with the callee's registers but `rsp`
restored (`kr`). -/
theorem sto_c {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sto_at sto)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sto_at)
    (h0 : q V X.cpu.gpr = 0) (h : s V X.cpu.gpr ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 104#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (s V X.cpu.gpr) i))
    (fv : ∀ i < 8, Foot F.data (Addr.add (rdq(V, s V X.cpu.gpr) + 8#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(V, rdq(V, s V X.cpu.gpr) + 8#64) = eF)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (sto_at.add 51) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = sto_at.add 51 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have e16 := b16 X.cpu.gpr.rsp
  have e8 := u8 X.cpu.gpr.rsp
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ g' = gC V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0c h0 h fa fb fs) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
  have he : eaD Y 0 8 = rdq(V, s V X.cpu.gpr) + 8#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
    rw [hgY]
    rfl
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_48 _) (by rw [he]; exact fv) hinF hF0
    (by rw [he]; exact htgt) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
  refine (c_51 prof).run c hin (fun j' g' _ V'' => j' = 55 ∧ g' = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp } ∧
      V'' = V') hKZ hAZ hrZ (vc_51 fun _ => ⟨rfl, by rw [hzs, e8], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_55 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Sto
