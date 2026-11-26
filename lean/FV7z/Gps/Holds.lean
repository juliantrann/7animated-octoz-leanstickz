import FV7z.Gps.Cuts
import FV7z.Close.Holds
/-!
# `__getpagesize` returns the page size (PLAN.md §M, M1)

glibc 2.31's `__getpagesize ()` at `0x666460` in `7zzs`: `rax` = `GLRO(dl_pagesize)` (the 8 bytes at `0x7933d8`);
when it is not 0, `ret` (16); else `__assert_fail` (17), not covered.

- `ret_16`: the instruction outside the block; `vc_0`: the verification condition of the block.
- `gps_ok`: with the page size not 0, the run reaches the return address with `rax` the page size, memory as it was.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gps

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_16 : pret <+: gps.drop 16 := by decide +kernel
theorem ret_16 (feat : Features) : Dec feat gps 16 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 16) (k := 0) (pret_0 feat) w_16 (Nat.zero_le _)

/-- `GLRO(dl_pagesize)`. -/
abbrev psz (V : Addr → Byte) : BitVec 64 := ofBytesLE 64 (List.map V (byteAddrs 7943128#64 8))

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rax, [GLRO(dl_pagesize)]; test rax, rax; je`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hm : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (hp : psz V ≠ 0)
    (h : ∀ fl, Q 16 { g with rax := psz V } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.lda]
  exact ⟨hm, fun hc => absurd (by simpa using hc) hp, fun _ => h _⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `__getpagesize ()` with `GLRO(dl_pagesize)` not 0: the run reaches the return address with `rax` the page size,
the memory as it was. -/
theorem gps_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gps_at gps) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gps_at)
    (hm : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (hp : psz V ≠ 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := psz V, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ g' = { X.cpu.gpr with rax := psz V } ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hm hp fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_16 _) (by rw [hsp]; exact hl) hin₂ h₂
    (by rw [hsp]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hgY]
  try rfl

end FV7z.Gps
