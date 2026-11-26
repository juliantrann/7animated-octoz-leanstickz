import FV7z.Irp.Cuts
import FV7z.Read.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CmpImm
/-!
# `CInFile::read_part` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NIO::CInFile::read_part (data, size)` at `0x4561a0` in `7zzs`
(`CPP/Windows/FileIO.cpp`): `read (_handle, data, min (size, 1 << 22))`, `_handle` the 4 bytes at `this`; the `call`
(26) of `__libc_read` (`Read.rd_at`), `sub rsp, 8` before it and `add rsp, 8; ret` (35) after it.

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`irp_at + 31`, `rsp` 8 below the entry's, the return address of `read_part` as it was, and the callee's own
post `Pc`) to that return address (`kr`).

- `capOf n`: `min (n, 1 << 22)`; `gC V g`: the registers at the `call`.
- `vc_0`, `vc_31`: the verification conditions of the two pieces.
- `irp_ok`: from the entry through `read` to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Irp

theorem irp_26 : ∀ feat, Dec feat irp 26 (FV7z.mk .call 64 [.rel 1741137] 5) := by intro feat f; rfl
theorem irp_35 : ∀ feat, Dec feat irp 35 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- `min (n, 1 << 22)`, unsigned: the size asked of `read`. -/
abbrev capOf (n : BitVec 64) : BitVec 64 := if n.toNat ≤ 4194304 then n else 4194304#64

/-- The registers at the `call`: `rax` = `1 << 22`, `rdx` capped, `rdi` = `_handle` (zero-extended), `rsp` 8 down. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := 4194304#64
    rdx := capOf g.rdx
    rsp := g.rsp - 8
    rdi := (ofBytesLE 32 ((byteAddrs g.rdi 4).map V)).setWidth 64 }

theorem sw4m : (4194304#32).setWidth 64 = 4194304#64 := by decide

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8; mov eax, 1 << 22; cmp rdx, 1 << 22; mov edi, [rdi]; cmova rdx, rax`, to the `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 26 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa ⊢
  by_cases hc : rdx.toNat ≤ 4194304
  · have hc' : decide (rdx.toNat ≤ 4194304) = true := decide_eq_true hc
    wpx [W_0, o0, gC, capOf, sw4m, be_imm (w := 64) _ 4194304 (by decide), hc', hc, Bool.not_true, Bool.false_eq_true]
    all_goals repeat'
      first
      | exact rfl
      | assumption
      | exact trivial
      | (congr 1 <;> first | rfl | decide)
      | apply And.intro
      | intro _
  · have hc' : decide (rdx.toNat ≤ 4194304) = false := decide_eq_false hc
    wpx [W_0, o0, gC, capOf, sw4m, be_imm (w := 64) _ 4194304 (by decide), hc', hc, Bool.not_false]
    all_goals repeat'
      first
      | exact rfl
      | assumption
      | exact trivial
      | (congr 1 <;> first | rfl | decide)
      | apply And.intro
      | intro _

/-- Back from `read`: `add rsp, 8`, to the `ret` at 35. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 35 { g with rsp := g.rsp + 8 } fl V) : W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_31, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFile::read_part (data, size)` (`this` = `rdi`, `data` = `rsi`, `size` = `rdx`) from its entry: at `read`'s
entry the registers are `gC` with `rsp` 16 below the entry's and the bytes `V` with the return address into
`read_part` pushed (`kf`); if `read` returns to `irp_at + 31` with `rsp` as at its entry and the return address of
`read_part` as it was, the run reaches that return address with `rsp` 8 above the entry's, the other registers as
`read` left them (`kr`). -/
theorem irp_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L irp_at irp)
    (hinR : CodeIn L Read.rd_at Read.rd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = irp_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (irp_at.add 31) 8)) →
      Y.cpu.rip = Read.rd_at → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = irp_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hrip' : X.cpu.rip = irp_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 26 ∧ g' = gC V X.cpu.gpr ∧ V' = V) hK hA hrip'
    (vc_0 fa) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (irp_26 _) hinR (by rw [Read.rd_length]; decide)
    (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
  refine (c_31 prof).run c hin (fun j' g' _ V'' => j' = 35 ∧
      g' = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKZ hAZ hrZ
    (vc_31 fun _ => ⟨rfl, by rw [hzs, e8], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (irp_35 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Irp
