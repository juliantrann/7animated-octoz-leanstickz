import FV7z.Wmc.Cuts
import FV7z.Tls.Holds
import FV7z.Memcpy.Plt
/-!
# `__wmemcpy` is `memcpy` over `4 * n` bytes (PLAN.md §M, M1)

glibc 2.31's `__wmemcpy (d, s, n)` at `0x65d300` in `7zzs`: `n` scaled to bytes (`shl rdx, 2`), then a tail jump to
`memcpy`'s PLT entry (`0x401070`, `Memcpy.plt_pin_cpy`). One piece of the code, from the entry (0) to the jump (8).

- `wmc_ok`: given `memcpy`'s contract at the PLT entry (`Tls.CpyAt`, e.g. `Memcpy.cpyAt_plt`), the contract of
  `CpyAt` with `rdx <<< 2` bytes in place of `rdx`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Wmc

/-- The jump to `memcpy`'s PLT entry. -/
def pjm : List Byte := [0xe9, 0x63, 0x3d, 0xda, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073707076963] 5) := by dec_rfl
theorem wj_8 : pjm <+: wmc.drop 8 := by decide +kernel
theorem jmp_8 (feat : Features) : Dec feat wmc 8 (FV7z.mk .jmp 64 [.rel 18446744073707076963] 5) :=
  Dec.shift (j := 8) (k := 0) (pjm_0 feat) wj_8 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the jump: `rdx` four times as large. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 8 ∧ g' = { g with rdx := g.rdx <<< 2 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.shl64]
  first
  | exact fun _ => trivial
  | trivial
  | exact ⟨rfl, rfl⟩
  | exact ⟨rfl, rfl, rfl⟩
  | rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__wmemcpy (d, s, n)` from its entry, given `memcpy`'s contract at its PLT entry: `CpyAt`'s with `n <<< 2`. -/
theorem wmc_ok {Pm : (Addr → Byte) → Prop} (hcpy : Tls.CpyAt prof L o 4198512#64 Pm)
    (c : Seg prof F Wl L s₀ o) (hG : GotF F) (hin : CodeIn L wmc_at wmc) (hinP : CodeIn L 4198512#64 Strlen.pltLen)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = wmc_at) (hPm : Pm V)
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsrc : ∀ i < (X.cpu.gpr.rdx <<< 2).toNat, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hdst : ∀ i < (X.cpu.gpr.rdx <<< 2).toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hs64 : X.cpu.gpr.rsi.toNat + (X.cpu.gpr.rdx <<< 2).toNat < 2 ^ 64)
    (hd64 : X.cpu.gpr.rdi.toNat + (X.cpu.gpr.rdx <<< 2).toNat < 2 ^ 64)
    (hap : X.cpu.gpr.rsi.toNat + (X.cpu.gpr.rdx <<< 2).toNat ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + (X.cpu.gpr.rdx <<< 2).toNat ≤ X.cpu.gpr.rsi.toNat)
    (hsp : X.cpu.gpr.rdi.toNat + (X.cpu.gpr.rdx <<< 2).toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (K : ∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < (X.cpu.gpr.rdx <<< 2).toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = V (Addr.add X.cpu.gpr.rsi i)) →
      (∀ a : Addr,
        ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + (X.cpu.gpr.rdx <<< 2).toNat) →
          V₂ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 8 ∧ g' = { X.cpu.gpr with rdx := X.cpu.gpr.rdx <<< 2 } ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_8 _) hinP (tgt := 0) (by decide) (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hg : Y₂.cpu.gpr = { X.cpu.gpr with rdx := X.cpu.gpr.rdx <<< 2 } := hg₂.trans hgY
  have hrsp : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg]
  have hrsi : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg]
  have hrdi : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg]
  have hrdx : Y₂.cpu.gpr.rdx = X.cpu.gpr.rdx <<< 2 := by rw [hg]
  have hrbx : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [hg]
  have hrbp : Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg]
  have hr12 : Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg]
  have hr13 : Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg]
  have hr14 : Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg]
  have hr15 : Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg]
  refine hcpy c hG hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hPm hin₂ hj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hK₂.df.trans hdf₀) ?_ ?_ <;>
    simp only [hrsp, hrsi, hrdi, hrdx, hrbx, hrbp, hr12, hr13, hr14, hr15] <;>
    first
    | assumption
    | exact K

end FV7z.Wmc
