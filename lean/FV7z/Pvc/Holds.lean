import FV7z.Pvc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `NWindows::NCOM::CPropVariant::Clear` (PLAN.md §M, M1)

7-Zip 26.06's `CPropVariant::Clear ()` at `0x457020` in `7zzs` (`CPP/Windows/PropVariant.cpp`; `objdump -d`), with
`this` = `p` in `rdi`: if `vt` (the 2 bytes at `p`, `vt V p`) is `VT_EMPTY` (0), `wReserved1` (the 2 bytes at `p + 2`)
= 0 and `S_OK` (`xor eax, eax; mov [rdi + 2], ax; xor eax, eax`, the `ret` at 18; the bytes `Vs`); else a tail jump
(24) to `PropVariant_Clear (this)` (`0x456fb0`, its code a hypothesis, `hinT`), the registers as they came.

- `vt`: `vt`; `Vs`: the bytes after the store.
- `vc_0`: the verification condition, split on `vt`.
- `pvc_ok`: from the entry (the object outside the frame, `hd`): `VT_EMPTY`, at the return address with `rax` = 0
  and the bytes `Vs` (`kn`); else at `PropVariant_Clear` with the registers and bytes as they were (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pvc

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x73, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551475] 5) := by dec_rfl
theorem wj_24 : pjm <+: pvc.drop 24 := by decide +kernel
theorem jmp_24 (feat : Features) : Dec feat pvc 24 (FV7z.mk .jmp 64 [.rel 18446744073709551475] 5) :=
  Dec.shift (j := 24) (k := 0) (pjm_0 feat) wj_24 (Nat.zero_le _)

/-- `PropVariant_Clear` (not proved here). -/
abbrev tgt_at : Addr := 0x456fb0
theorem tgt24 : pvc_at.add (24 + 5) + BitVec.ofNat 64 18446744073709551475 = tgt_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_18 : pret <+: pvc.drop 18 := by decide +kernel
theorem ret_18 (feat : Features) : Dec feat pvc 18 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 18) (k := 0) (pret_0 feat) w_18 (Nat.zero_le _)

/-- `vt` of the variant at `p`. -/
abbrev vt (V : Addr → Byte) (p : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs p 2).map V)
/-- The bytes after `wReserved1` = 0. -/
abbrev Vs (V : Addr → Byte) (p : Addr) : Addr → Byte := Vst V (p + 2#64) (toBytesLE 0#16 2)

variable {F : Footprint} {Wl : List Rgn}

/-- The clean-up of the test. -/
local macro "sfx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [Op.cmpmi, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth, decide_false,
    decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, false_implies,
    implies_true, eq_self_iff_true, ↓reduceIte, $ls,*])

/-- `cmp word [rdi], 0; jne`, then `xor eax, eax; mov [rdi + 2], ax; xor eax, eax` to the `ret` at 18, or the jump at
24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (fw : vt V g.rdi = 0#16 → ∀ i < 2, Foot Wl (Addr.add (g.rdi + 2#64) i))
    (h18 : vt V g.rdi = 0#16 → ∀ fl, Q 18 { g with rax := 0#64 } fl (Vs V g.rdi))
    (h24 : ¬ vt V g.rdi = 0#16 → ∀ fl, Q 24 g fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 fw h18 h24 ⊢
  by_cases h : ofBytesLE 16 ((byteAddrs rdi 2).map V) = 0#16
  · have fw' := fw h
    sfx [W_0, W_10, o0, o1, h]
    all_goals repeat' (first | exact h18 h _ | assumption | exact trivial | apply And.intro | intro _)
  · sfx [W_0, W_10, o0, o1, h]
    all_goals repeat' (first | exact h24 h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::Clear ()` (`this` = `rdi`) from its entry. `VT_EMPTY`: at the return address with `rax` = 0 and
the bytes `Vs` (`kn`). Else: at `PropVariant_Clear` with the registers and bytes as they were (`kf`). -/
theorem pvc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pvc_at pvc) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pvc_at)
    (f0 : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw : vt V X.cpu.gpr.rdi = 0#16 → ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (kn : vt V X.cpu.gpr.rdi = 0#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vs V X.cpu.gpr.rdi) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } → GoG prof L o gev gP gE Z t')
    (kf : ¬ vt V X.cpu.gpr.rdi = 0#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- the store of `wReserved1` leaves the return address as it was (the object outside the frame)
  have t2 : (X.cpu.gpr.rdi + 2#64).toNat = X.cpu.gpr.rdi.toNat + 2 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have hra' : rdq(Vs V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ := by
    show rdq(Vst V (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp) = e₂.add j₂
    rw [Tun.rd_Vst V (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2) X.cpu.gpr.rsp 8
      (by rw [toBytesLE_length, t2]; omega) hp8 (by rw [toBytesLE_length, t2]; omega)]
    exact hra
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 18 ∧ g' = { X.cpu.gpr with rax := 0#64 } ∧ V' = Vs V X.cpu.gpr.rdi ∧ vt V X.cpu.gpr.rdi = 0#16) ∨
      (j' = 24 ∧ g' = X.cpu.gpr ∧ V' = V ∧ ¬ vt V X.cpu.gpr.rdi = 0#16)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f0 fw (fun hz _ => Or.inl ⟨rfl, rfl, rfl, hz⟩) (fun hn _ => Or.inr ⟨rfl, rfl, rfl, hn⟩)) ?_
  rintro j' g fl V₁ (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, hV₁, hn⟩) Y t₁ hKY hAY hrY hgY -
  · -- `ret`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_18 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra') ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hz Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- the jump to `PropVariant_Clear`
    subst V₁
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_24 _) hinT hT tgt24 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf hn Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Pvc
