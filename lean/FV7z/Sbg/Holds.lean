import FV7z.Sbg.Cuts
import FV7z.Fsk.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `NWindows::NFile::NIO::CFileBase::seekToBegin ()` (PLAN.md §M, M1)

7-Zip 26.06's `CFileBase::seekToBegin () const` at `0x4560c0` in `7zzs` (`CPP/Windows/FileIO.cpp`; `objdump -d`),
`this` in `rdi`: `return seek (0, SEEK_SET);` as `sub rsp, 8; xor edx, edx; xor esi, esi`, the `call` at 12 to
`CFileBase::seek` (`Fsk.fsk_at`), then `add rsp, 8; ret` (21) with `rax` as `seek` left it.

`seek` is a hypothesis, as `__errno_location` in `FV7z/Gle/Holds.lean`: `ks` is a continuation at its entry, given
the run from its return (`rsp` 8 below the entry's, the return address as it was) and its own post `Ps`.

- `gC`: the registers at the `call` (`rdx`, `rsi` 0, `rsp` 8 lower).
- `vc_0`, `vc_17`: the verification conditions of the pieces.
- `sbg_ok`: from the entry, through `seek`, to the return address with the registers as `seek` returned them and
  `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sbg

/-- The `call` to `CFileBase::seek`. -/
def pcs : List Byte := [0xe8, 0xdf, 0xff, 0xff, 0xff]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 18446744073709551583] 5) := by dec_rfl
theorem wc_12 : pcs <+: sbg.drop 12 := by decide +kernel
theorem call_12 (feat : Features) : Dec feat sbg 12 (FV7z.mk .call 64 [.rel 18446744073709551583] 5) :=
  Dec.shift (j := 12) (k := 0) (pcs_0 feat) wc_12 (Nat.zero_le _)
theorem tgt_12 : sbg_at.add (12 + 5) + BitVec.ofNat 64 18446744073709551583 = Fsk.fsk_at.add 0 := by decide

theorem fsk_lt : 0 < Fsk.fsk.length := by rw [Fsk.fsk_length]; decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_21 : pret <+: sbg.drop 21 := by decide +kernel
theorem ret_21 (feat : Features) : Dec feat sbg 21 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 21) (k := 0) (pret_0 feat) w_21 (Nat.zero_le _)

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := by bv_omega

/-- The registers at the `call`: `rsp` 8 lower, `rdx` and `rsi` 0. -/
abbrev gC (g : Gprs) : Gprs := { g with rdx := 0#64, rsp := g.rsp - 8#64, rsi := 0#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8; xor edx, edx; xor esi, esi` to the `call` at 12. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 12 (gC g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, xz]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- Back from `seek`: `add rsp, 8` to the `ret` at 21. -/
theorem vc_17 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 21 { g with rsp := g.rsp + 8#64 } fl V) : W_17 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_17, o1]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CFileBase::seekToBegin ()` (`this` = `rdi`) from its entry. At `seek`'s entry the registers are `gC` with `rsp`
16 below the entry's, the bytes with the return address pushed (`ks`); back at `sbg_at + 17` (`Ps`), at the return
address with the registers as `seek` returned them and `rsp` 8 above the entry's (`kr`). -/
theorem sbg_ok {Ps : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sbg_at sbg) (hinS : CodeIn L Fsk.fsk_at Fsk.fsk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbg_at)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ks : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (sbg_at.add 17) 8)) →
      Y.cpu.rip = Fsk.fsk_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = sbg_at.add 17 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V₁, X.cpu.gpr.rsp) = e₂.add j₂ → Ps Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), Ps Z V₁ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₁ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- to the `call` of `seek`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 12 ∧ g' = gC X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY0 : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hsY0]; exact q16 _
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_12 _) hinS (tgt := 0) fsk_lt tgt_12
    (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine ks Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, hgY]) ?_
  -- back from `seek`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hra hPs
  refine (c_17 prof).run c hin (fun j' g' _ V' => j' = 21 ∧ g' = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp } ∧
      V' = V₁) hKZ hAZ hrZ (vc_17 fun _ => ⟨rfl, by rw [hzs, sa8], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_21 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V₁ Z' t₅ hPs hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Sbg
