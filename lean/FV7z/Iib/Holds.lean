import FV7z.Iib.Cuts
import FV7z.Tun.Inv
/-!
# `_IO_iter_begin` (PLAN.md §M, M1)

glibc 2.31's `_IO_iter_begin ()` at `0x60e050` in `7zzs`: `_IO_list_all` (`0x7a31c8`). One stretch of code, to the
`ret` (11).

- `iib_ok`: called with the variable in the footprint's data, the run reaches the `ret` with `rax` the variable's
  value; the registers else are as at the entry, the bytes as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Iib

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_11 : pret <+: iib.drop 11 := by decide +kernel
theorem ret_11 (feat : Features) : Dec feat iib 11 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 11) (k := 0) (pret_0 feat) w_11 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ∀ i < 8, Foot F.data (Addr.add 8008136#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 11 ∧ g' = g.set 0 rdq(V, 8008136#64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.lda]
  exact ⟨h1, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `_IO_iter_begin ()` from its entry to its `ret`: `rax` is `_IO_list_all`; the registers else are as at the
entry, the bytes as at the entry. -/
theorem iib_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L iib_at iib) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = iib_at)
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8008136#64 i))
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = iib_at.add 11 →
      Z.cpu.gpr = X.cpu.gpr.set 0 rdq(V, 8008136#64) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 11 ∧ g' = X.cpu.gpr.set 0 rdq(V, 8008136#64) ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 h1) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY hgY

end FV7z.Iib
