import FV7z.Iap.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NWindows::NFile::NName::IsAbsolutePath (s)` (PLAN.md §M, M1)

7-Zip 26.06's `NName::IsAbsolutePath (const wchar_t *s)` at `0x456a50` in `7zzs` (`CPP/Windows/FileName.cpp`;
`objdump -d`), `s` in `rdi`: `return IS_PATH_SEPAR (s[0]);` as `cmp dword [rdi], 0x2f; sete al; ret` (10), a leaf
that writes no byte.

- `vc_0`: the code to the `ret`, `al` = 1 if the 4 bytes at `s` are `'/'`, else 0.
- `iap_ok`: from the entry to the return address, only `rax` changed (and `rsp` popped).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Iap

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_10 : pret <+: iap.drop 10 := by decide +kernel
theorem ret_10 (feat : Features) : Dec feat iap 10 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 10) (k := 0) (pret_0 feat) w_10 (Nat.zero_le _)

/-- A low byte made of a `wrLo` (`setcc`), bit by bit: equal to a literal (as in `FV7z/Dde/Holds.lean`). -/
local macro "lob" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp dword [rdi], 0x2f; sete al` to the `ret` at 10. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (h : ∀ ra fl, ra.setWidth 8 = (if rdd(V, g.rdi) = 47#32 then 1#8 else 0#8) → Q 10 { g with rax := ra } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa h ⊢
  by_cases hz : rdd(V, rdi) = 47#32
  · simp only [if_pos hz] at h
    wpx [W_0, o0, Op.cmpmi, Op.setcc, hz, decide_true, BitVec.ofBool_true, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
    all_goals repeat' (first | exact h _ _ (by lob) | with_reducible exact fa | apply And.intro | intro _)
  · simp only [if_neg hz] at h
    wpx [W_0, o0, Op.cmpmi, Op.setcc, hz, decide_false, BitVec.ofBool_false, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
    all_goals repeat' (first | exact h _ _ (by lob) | with_reducible exact fa | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NName::IsAbsolutePath (s)` (`s` = `rdi`) from its entry: at the return address with the bytes as they were,
`al` = 1 if `s[0]` (4 bytes) is `'/'`, else 0, the other registers as at the entry and `rsp` 8 above (`kr`). -/
theorem iap_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L iap_at iap)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = iap_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr : ∀ (Z' : State) (t' : Nat) (ra : BitVec 64),
      ra.setWidth 8 = (if rdd(V, X.cpu.gpr.rdi) = 47#32 then 1#8 else 0#8) → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := ra, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 10 ∧
      (∃ ra : BitVec 64, g' = { X.cpu.gpr with rax := ra } ∧
        ra.setWidth 8 = (if rdd(V, X.cpu.gpr.rdi) = 47#32 then 1#8 else 0#8)) ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fa fun ra _ hr8 => ⟨rfl, ⟨ra, rfl, hr8⟩, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, ⟨ra, rfl, hr8⟩, hV₂⟩ U t₁ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_10 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z' t₂ ra hr8 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Iap
