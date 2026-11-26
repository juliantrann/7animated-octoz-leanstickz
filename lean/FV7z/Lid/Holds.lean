import FV7z.Lid.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `LzmaDec_InitDicAndState` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_InitDicAndState (p, initDic, initState)` at `0x42b600` in `7zzs` (`C/LzmaDec.c`;
`objdump -d`): `remainLen` (the 4 bytes at `p + 92`) = 275 (`kMatchSpecLenStart + 1`), `tempBufSize` (at `p + 100`)
= 0; with `initDic` (`esi` not 0) `processedPos` and `checkDicSize` (the 8 bytes at `p + 64`) = 0 and `remainLen` =
276 (`kMatchSpecLenStart + 2`); with `initState` (`edx` not 0) `remainLen` = 276. No register is written. Cut points:
the entry and 37 (`test edx, edx`); one `ret` (48).

- `MA`, `MB`, `MC`: the stores of the three pieces; `M1`: the bytes at 37; `Mf`: the bytes at the end.
- `vc_0z`, `vc_0n`, `vc_37z`, `vc_37n`: the two pieces for each value of the flag.
- `lid_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lid

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: lid.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat lid 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)

/-- `remainLen` = 275, `tempBufSize` = 0. -/
abbrev MA (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst V (p + 92#64) (toBytesLE 275#32 4)) (p + 100#64) (toBytesLE 0#32 4)
/-- Then, with `initDic`, `processedPos` = `checkDicSize` = 0 and `remainLen` = 276. -/
abbrev MB (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (MA V p) (p + 64#64) (toBytesLE 0#64 8)) (p + 92#64) (toBytesLE 276#32 4)
/-- With `initState`, `remainLen` = 276. -/
abbrev MC (V : Addr → Byte) (p : Addr) : Addr → Byte := Vst V (p + 92#64) (toBytesLE 276#32 4)
/-- The bytes at 37. -/
abbrev M1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if BitVec.setWidth 32 g.rsi = 0 then MA V g.rdi else MB V g.rdi
/-- The bytes at the end. -/
abbrev Mf (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if BitVec.setWidth 32 g.rdx = 0 then M1 V g else MC (M1 V g) g.rdi

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `initDic` 0: the two stores, `test esi, esi; je` taken. -/
theorem vc_0z {g : Gprs} {f : Rflags} (h : BitVec.setWidth 32 g.rsi = 0)
    (w92 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 92#64) i)) (w100 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 100#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 37 ∧ g' = g ∧ V' = MA V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h w92 w100 ⊢
  wpx [W_0, W_22, o0, o1, MA, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact ⟨w92, w100⟩
  | exact ⟨w92, w100, fun _ => ⟨rfl, rfl, rfl⟩⟩
  | exact ⟨w92, w100, fun _ => ⟨rfl, rfl, rfl⟩, fun hh => absurd hh (by decide)⟩
  | (refine ⟨w92, w100, ?_⟩; done)

/-- `initDic` not 0: the two stores, `test esi, esi; je` not taken, the two stores at 22. -/
theorem vc_0n {g : Gprs} {f : Rflags} (h : BitVec.setWidth 32 g.rsi ≠ 0)
    (w92 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 92#64) i)) (w100 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 100#64) i))
    (w64 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 64#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 37 ∧ g' = g ∧ V' = MB V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h w92 w100 w64 ⊢
  wpx [W_0, W_22, o0, o1, MA, MB, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact ⟨w92, w100, w64, w92⟩
  | exact ⟨w92, w100, fun hh => absurd hh h, fun _ => ⟨w64, w92, rfl, rfl, rfl⟩⟩
  | exact ⟨w92, w100, fun hh => absurd hh h, fun _ => ⟨w64, w92⟩⟩
  | (refine ⟨w92, w100, ?_⟩; done)

/-- `initState` 0: `test edx, edx; je` taken. -/
theorem vc_37z {g : Gprs} {f : Rflags} (h : BitVec.setWidth 32 g.rdx = 0) :
    W_37 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_37, W_41, o2, o3, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact fun _ => ⟨rfl, rfl, rfl⟩
  | exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun hh => absurd hh (by decide)⟩
  | done

/-- `initState` not 0: `test edx, edx; je` not taken, the store at 41. -/
theorem vc_37n {g : Gprs} {f : Rflags} (h : BitVec.setWidth 32 g.rdx ≠ 0)
    (w92 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 92#64) i)) :
    W_37 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = g ∧ V' = MC V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h w92 ⊢
  wpx [W_37, W_41, o2, o3, MC, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact w92
  | exact ⟨fun hh => absurd hh h, fun _ => ⟨w92, rfl, rfl, rfl⟩⟩
  | exact ⟨fun hh => absurd hh h, fun _ => w92⟩
  | done

/-- `LzmaDec_InitDicAndState (p, initDic, initState)` from its entry to the return address: the bytes `Mf`, the
registers as at the entry but `rsp`. -/
theorem lid_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lid_at lid) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lid_at)
    (w92 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 92#64) i))
    (w100 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 100#64) i))
    (w64 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Mf V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mf V X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- from 37, the bytes `M1`, to the return address
  have h37 : ∀ (W : Addr → Byte) (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = lid_at.add 37 → Y.cpu.gpr = X.cpu.gpr → W = M1 V X.cpu.gpr → GoG prof L o gev gP gE Y t₁ := by
    intro W Y t₁ hKY hAY hrY hgY hW
    subst hW
    by_cases hd : BitVec.setWidth 32 X.cpu.gpr.rdx = 0
    · have hM : Mf V X.cpu.gpr = M1 V X.cpu.gpr := ite_eq_left hd
      refine (c_37 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ g' = X.cpu.gpr ∧ V' = M1 V X.cpu.gpr) hKY hAY hrY
        (by rw [hgY]; exact vc_37z hd) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₂ hKU hAU hrU hgU -
      subst V₁
      have hspU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_48 _) (by rw [hspU]; exact hl) hin₂ h₂
        (by rw [hspU, ← hM]; exact hra) ?_
      rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
      exact k Z t₃ hKZ (by rw [hM]; exact hAZ) hrZ (by rw [hgZ, hspU, hgU])
    · have hM : Mf V X.cpu.gpr = MC (M1 V X.cpu.gpr) X.cpu.gpr.rdi := ite_eq_right hd
      refine (c_37 prof).run c hin
        (fun j' g' _ V' => j' = 48 ∧ g' = X.cpu.gpr ∧ V' = MC (M1 V X.cpu.gpr) X.cpu.gpr.rdi) hKY hAY hrY
        (by rw [hgY]; exact vc_37n hd w92) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₂ hKU hAU hrU hgU -
      subst V₁
      have hspU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_48 _) (by rw [hspU]; exact hl) hin₂ h₂
        (by rw [hspU, ← hM]; exact hra) ?_
      rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
      exact k Z t₃ hKZ (by rw [hM]; exact hAZ) hrZ (by rw [hgZ, hspU, hgU])
  by_cases hs : BitVec.setWidth 32 X.cpu.gpr.rsi = 0
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧ g' = X.cpu.gpr ∧ V' = MA V X.cpu.gpr.rdi) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0z hs w92 w100) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact h37 _ Y t₁ hKY hAY hrY hgY (ite_eq_left hs).symm
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧ g' = X.cpu.gpr ∧ V' = MB V X.cpu.gpr.rdi) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n hs w92 w100 w64) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact h37 _ Y t₁ hKY hAY hrY hgY (ite_eq_right hs).symm

end FV7z.Lid
