import FV7z.Dmw.Cuts
import FV7z.Close.Holds
/-!
# `_dl_mcount_wrapper_check` returns when no object is profiled (PLAN.md §M, M1)

glibc 2.31's `_dl_mcount_wrapper_check (selfpc)` at `0x670700` in `7zzs`: `rsi` = `selfpc`; when
`GLRO(dl_profile_map)` (the 8 bytes at `0x7a8588`) is 0, `ret` (32); else a tail jump to `_dl_mcount` (21), not
covered.

- `ret_32`: the instruction outside the block; `vc_0`: the verification condition of the block.
- `dmw_ok`: with the map 0, the run reaches the return address with `rsi` = `rdi`, memory as it was.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dmw

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_32 : pret <+: dmw.drop 32 := by decide +kernel
theorem ret_32 (feat : Features) : Dec feat dmw 32 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 32) (k := 0) (pret_0 feat) w_32 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp qword [GLRO(dl_profile_map)], 0; mov rsi, rdi; je`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hm : ∀ i < 8, Foot F.data (Addr.add 8029576#64 i)) (hz : ofBytesLE 64 (List.map V (byteAddrs 8029576#64 8)) = 0)
    (h : ∀ fl, Q 32 { g with rsi := g.rdi } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.cmpmia]
  refine ⟨hm, fun _ => h _, fun hc => ?_⟩
  first
  | (rw [hz] at hc; exact absurd hc (by decide))
  | simp [hz] at hc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `_dl_mcount_wrapper_check (selfpc)` with `GLRO(dl_profile_map)` 0: the run reaches the return address with `rsi`
= `rdi`, the memory as it was. -/
theorem dmw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dmw_at dmw) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dmw_at)
    (hm : ∀ i < 8, Foot F.data (Addr.add 8029576#64 i)) (hz : ofBytesLE 64 (List.map V (byteAddrs 8029576#64 8)) = 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 32 ∧ g' = { X.cpu.gpr with rsi := X.cpu.gpr.rdi } ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hm hz fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_32 _) (by rw [hsp]; exact hl) hin₂ h₂
    (by rw [hsp]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hgY]
  try rfl

end FV7z.Dmw
