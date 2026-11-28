import FV7z.Pvc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `NWindows::NCOM::CPropVariant::Clear ()` (PLAN.md §M, M1)

7-Zip 26.06's `CPropVariant::Clear ()` at `0x457020` in `7zzs` (`CPP/Windows/PropVariant.cpp`), `this` in `rdi`:
`cmp word [rdi], 0; jne` on `vt` (the 2 bytes at `this`): for `VT_EMPTY` (0) `wReserved1 = 0` (the 2 bytes at
`this + 2`) and `return S_OK` (`xor eax, eax`, the `ret` at 18), else a tail jump (24) to
`PropVariant_Clear (this)` (`0x456fb0`, a hypothesis `kf`), the registers as at the entry.

- `vt`: the tag; `xz`: `xor eax, eax`.
- `vc_0`: the verification condition of the piece (both ways).
- `pvc_ok`: from the entry to `PropVariant_Clear`'s entry (`kf`) or to the return address (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pvc

/-- The jump to `PropVariant_Clear`. -/
def pjm : List Byte := [0xe9, 0x73, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551475] 5) := by dec_rfl
theorem wj_24 : pjm <+: pvc.drop 24 := by decide +kernel
theorem jmp_24 (feat : Features) : Dec feat pvc 24 (FV7z.mk .jmp 64 [.rel 18446744073709551475] 5) :=
  Dec.shift (j := 24) (k := 0) (pjm_0 feat) wj_24 (Nat.zero_le _)
theorem tgt_24 : pvc_at.add (24 + 5) + BitVec.ofNat 64 18446744073709551475 = (4550576#64).add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_18 : pret <+: pvc.drop 18 := by decide +kernel
theorem ret_18 (feat : Features) : Dec feat pvc 18 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 18) (k := 0) (pret_0 feat) w_18 (Nat.zero_le _)

/-- The tag `vt` (the 2 bytes at `this` = `g.rdi`). -/
abbrev vt (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 (List.map V (byteAddrs g.rdi 2))

/-- `xor eax, eax`. -/
theorem xz (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x) = 0#64 := by
  rw [BitVec.xor_self]
  decide

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp word [rdi], 0; jne 24`; else `xor eax, eax; mov [rdi + 2], ax; xor eax, eax` to the `ret` at 18. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f0 : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (w2 : ∀ i < 2, Foot Wl (Addr.add (g.rdi + 2#64) i)) :
    W_0 F Wl (fun j' g' _ V' => (j' = 24 ∧ ¬ vt V g = 0#16 ∧ g' = g ∧ V' = V) ∨
      (j' = 18 ∧ vt V g = 0#16 ∧ g' = { g with rax := 0#64 } ∧
        V' = Vst V (g.rdi + 2#64) (toBytesLE 0#16 2))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 w2 ⊢
  wpx [W_0, W_10, o0, o1, Op.cmpmi, xz, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_false']
  all_goals repeat'
    first
    | exact Or.inl ⟨rfl, ‹_›, rfl, rfl⟩
    | exact Or.inr ⟨rfl, ‹_›, rfl, rfl⟩
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::Clear ()` (`this` = `rdi`) from its entry: for `vt` not 0 at `PropVariant_Clear`'s entry with the
registers and the bytes as at the entry (`kf`); for `vt` 0 at the return address with `wReserved1 = 0`, `rax` = 0
(`S_OK`) and `rsp` 8 up (`kr`). -/
theorem pvc_ok {codeP : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pvc_at pvc)
    (hinP : CodeIn L 4550576#64 codeP) (hP : 0 < codeP.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pvc_at)
    (f0 : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 2)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kf : ¬ vt V X.cpu.gpr = 0#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 4550576#64 → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : vt V X.cpu.gpr = 0#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have t2 : (X.cpu.gpr.rdi + 2#64).toNat = X.cpu.gpr.rdi.toNat + 2 := by
    rw [BitVec.toNat_add]; simp; omega
  have hrip' : X.cpu.rip = pvc_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' => (j' = 24 ∧ ¬ vt V X.cpu.gpr = 0#16 ∧ g' = X.cpu.gpr ∧ V' = V) ∨
      (j' = 18 ∧ vt V X.cpu.gpr = 0#16 ∧ g' = { X.cpu.gpr with rax := 0#64 } ∧
        V' = Vst V (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2))) hK hA hrip' (vc_0 f0 w2) ?_
  rintro j' g fl V₁ hq' Y t₁ hKY hAY hrY hgY -
  rcases hq' with ⟨rfl, hz, rfl, hV₁⟩ | ⟨rfl, hz, rfl, hV₁⟩
  · subst V₁
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_24 _) hinP (tgt := 0) hP tgt_24 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf hz Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])
  · subst V₁
    have hra' : rdq(Vst V (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [Tun.rd_Vst V _ _ X.cpu.gpr.rsp 8 (by rw [toBytesLE_length, t2]; omega) hp8
        (by rw [toBytesLE_length, t2]; omega)]
      exact hra
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_18 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra') ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kr hz Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl

end FV7z.Pvc
