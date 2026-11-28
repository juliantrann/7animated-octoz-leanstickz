import FV7z.Sts.Cuts
import FV7z.Aac.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `CExtractScanConsole::StartScanning` (PLAN.md §M, M1)

7-Zip 26.06's `CExtractScanConsole::StartScanning ()` at `0x5e85c0` in `7zzs`
(`CPP/UI/Console/ExtractCallbackConsole.cpp`), `this` in `rdi`: `cmp qword [rdi + 0x50], 0; je 40;
cmp byte [rdi + 0x58], 0; jne 40; add rdi, 0x30; lea rsi, [rip + …]` (the string "Scan" at `0x6e9b63`), then a tail
jump (28) to `AString::operator= (const char *)` (`Aac.aac_at`); at 40 the `ret`. No byte is written.

The callee is a hypothesis (`kf`), and so is the run from the return address (`kr`).

- `gs`: the registers at the jump: `rdi` = `this + 0x30`, `rsi` = the string.
- `vc_0`: the verification condition of the one piece (the three blocks).
- `sts_ok`: from the entry to `AString::operator=`'s entry with the registers `gs` (`kf`), or to the return address
  with `rsp` 8 above the entry's (`kr`); the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sts

/-- The tail jump to `AString::operator= (const char *)`. -/
def pjm : List Byte := [0xe9, 0xdf, 0x3e, 0xe6, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073707863775] 5) := by dec_rfl
theorem wm_28 : pjm <+: sts.drop 28 := by decide +kernel
theorem jmp_28 (feat : Features) : Dec feat sts 28 (FV7z.mk .jmp 64 [.rel 18446744073707863775] 5) :=
  Dec.shift (j := 28) (k := 0) (pjm_0 feat) wm_28 (Nat.zero_le _)
theorem tgt_28 : sts_at.add (28 + 5) + BitVec.ofNat 64 18446744073707863775 = Aac.aac_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_40 : pret <+: sts.drop 40 := by decide +kernel
theorem ret_40 (feat : Features) : Dec feat sts 40 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 40) (k := 0) (pret_0 feat) w_40 (Nat.zero_le _)

/-- The registers at the jump. -/
abbrev gs (g : Gprs) : Gprs := { g with rsi := 7248739#64, rdi := g.rdi + 48#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- The three blocks: to the `ret` at 40 with the registers as they were, or to the jump at 28 with `gs`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 80#64) i)) (f2 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 88#64) i))
    (h40 : ∀ fl, Q 40 g fl V) (h28 : ∀ fl, Q 28 (gs g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 h40 h28 ⊢
  wpx [W_0, W_11, W_17, o0, o1, o2, Op.cmpmi]
  all_goals repeat' (first | exact h40 _ | exact h28 _ | exact f1 | exact f2 | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CExtractScanConsole::StartScanning ()` (`this` = `rdi`) from its entry, no byte written: at
`AString::operator= (const char *)`'s entry with the registers `gs` (`kf`), or at the return address with `rsp` 8
above the entry's (`kr`). -/
theorem sts_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sts_at sts) (hinC : CodeIn L Aac.aac_at Aac.aac)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sts_at)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 80#64) i))
    (f2 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 88#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hr' : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Aac.aac_at →
      Y.cpu.gpr = gs X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 40 ∧ g' = X.cpu.gpr) ∨ (j' = 28 ∧ g' = gs X.cpu.gpr)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f1 f2 (fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩) (fun _ => ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, hg⟩ | ⟨rfl, hg⟩
  · subst hg
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_40 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hr') ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kr Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY])
  · subst hg
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_28 _) hinC (tgt := 0)
      (Aac.lt_len (by decide)) tgt_28 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Sts
