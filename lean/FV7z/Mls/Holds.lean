import FV7z.Mls.Cuts
import FV7z.Xst.Blocks
import FV7z.Lemmas.Rmw
import FV7z.Lemmas.FnFar
/-!
# `MY_lstat` (PLAN.md §M, M1)

7-Zip 26.06's `MY_lstat (path, st, followLink)` at `0x4558a0` in `7zzs` (`CPP/Windows/FileFind.cpp`; `objdump -d`):
`r9` = `path`, the 144 bytes of `*st` zeroed (`rep stos qword [rdi], rax` at 13, 18 quadwords, `Seg.s_rep_stosq`),
then `edi` = 1 (`_STAT_VER`), `rdx` = `st`, `rsi` = `path`, and a tail jump: to `__xstat` (`Xst.xst_at`, 40) when
`followLink` (`dl`) is not 0, else to `__lxstat` (`lxs_at`, 31).

- `vc_0`, `vc_16`: the two pieces around the `rep stos`;
- `mls_ok`: from the entry to the entry of `__xstat` (`kx`) or `__lxstat` (`kl`) with the registers `gT` and `*st` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mls

/-- `rep stos qword [rdi], rax`. -/
def pstos : List Byte := [0xf3, 0x48, 0xab]
theorem pstos_0 : ∀ feat, Dec feat pstos 0 (repStosq 3) := by dec_rfl
theorem w_13 : pstos <+: mls.drop 13 := by decide +kernel
theorem stos_13 (feat : Features) : Dec feat mls 13 (repStosq 3) :=
  Dec.shift (j := 13) (k := 0) (pstos_0 feat) w_13 (Nat.zero_le _)

/-- The jump to `__lxstat`. -/
def pjl : List Byte := [0xe9, 0xfc, 0xfa, 0x20, 0x00]
theorem pjl_0 : ∀ feat, Dec feat pjl 0 (FV7z.mk .jmp 64 [.rel 2161404] 5) := by dec_rfl
theorem wj_31 : pjl <+: mls.drop 31 := by decide +kernel
theorem jmp_31 (feat : Features) : Dec feat mls 31 (FV7z.mk .jmp 64 [.rel 2161404] 5) :=
  Dec.shift (j := 31) (k := 0) (pjl_0 feat) wj_31 (Nat.zero_le _)

/-- The jump to `__xstat`. -/
def pjx : List Byte := [0xe9, 0x33, 0xfa, 0x20, 0x00]
theorem pjx_0 : ∀ feat, Dec feat pjx 0 (FV7z.mk .jmp 64 [.rel 2161203] 5) := by dec_rfl
theorem wj_40 : pjx <+: mls.drop 40 := by decide +kernel
theorem jmp_40 (feat : Features) : Dec feat mls 40 (FV7z.mk .jmp 64 [.rel 2161203] 5) :=
  Dec.shift (j := 40) (k := 0) (pjx_0 feat) wj_40 (Nat.zero_le _)

/-- `__lxstat` in `7zzs`. -/
abbrev lxs_at : Addr := 0x6653c0

/-- The registers at either callee's entry: `edi` 1, `rsi` = `path`, `rdx` = `st`, `rax` and `rcx` 0 (after the
`rep stos`), `r9` = `path`. -/
abbrev gT (g : Gprs) : Gprs :=
  { g with rax := 0#64, rcx := 0#64, rdx := g.rsi, rsi := g.rdi, rdi := 1#64, r9 := g.rdi }

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- `mov r9, rdi; xor eax, eax; mov rdi, rsi; mov ecx, 18`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j g' _ V' => j = 13 ∧ g' = { g with rax := 0#64, rcx := 18#64, rdi := g.rsi, r9 := g.rdi } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, xz, BitVec.xor_self, show BitVec.setWidth 64 18#32 = 18#64 from by decide]
  all_goals (try intro _)
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl, rfl⟩ | rfl | trivial

/-- `test dl, dl; mov edi, 1; mov rdx, rsi; mov rsi, r9; jne`: to 40 when `dl` is not 0, else to 31. -/
theorem vc_16 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h40 : g.rdx.setWidth 8 ≠ 0#8 → ∀ fl, Q 40 { g with rdx := g.rsi, rsi := g.r9, rdi := 1#64 } fl V)
    (h31 : g.rdx.setWidth 8 = 0#8 → ∀ fl, Q 31 { g with rdx := g.rsi, rsi := g.r9, rdi := 1#64 } fl V) :
    W_16 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h40 h31 ⊢
  wpx [W_16, o1, BitVec.and_self, show BitVec.setWidth 64 1#32 = 1#64 from by decide]
  all_goals (try intro _)
  refine ⟨fun hc => h40 ?_ _, fun hc => h31 ?_ _⟩ <;> simpa using hc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `MY_lstat (path, st, followLink)` from its entry: the 144 bytes at `st` (`rsi`) 0 (`Vfill`), then at the entry of
`__xstat` when `followLink` (`dl`) is not 0 (`kx`), else at the entry of `__lxstat` (`kl`), with the registers `gT`
(`__xstat (1, path, st)`); the return address is left for the callee. -/
theorem mls_ok {codeL : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L mls_at mls)
    (hinX : CodeIn L Xst.xst_at Xst.xst) (hinL : CodeIn L lxs_at codeL) (hL : 0 < codeL.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mls_at)
    (hdf : s₀.cpu.rflags.df = false) (hst : ∀ i < 144, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (kx : X.cpu.gpr.rdx.setWidth 8 ≠ 0#8 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vfill V X.cpu.gpr.rsi 0#64 18) → Y.cpu.rip = Xst.xst_at → Y.cpu.gpr = gT X.cpu.gpr →
      GoG prof L o gev gP gE Y t')
    (kl : X.cpu.gpr.rdx.setWidth 8 = 0#8 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vfill V X.cpu.gpr.rsi 0#64 18) → Y.cpu.rip = lxs_at → Y.cpu.gpr = gT X.cpu.gpr →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = mls_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin _ hK hA hrip' vc_0 ?_
  rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
  subst V'
  refine c.s_rep_stosq hdf hin (by decide) (lt_len (by decide)) (stos_13 _) 17 hKY hAY hrY
    (by rw [hgY, hg] <;> rfl) (fun i hi => by rw [hgY, hg]; exact hst i (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rsi := by rw [hgY, hg]
  have hax : Y.cpu.gpr.rax = 0#64 := by rw [hgY, hg]
  rw [hdi, hax] at hA₂
  have hdx : Y₂.cpu.gpr.rdx = X.cpu.gpr.rdx := by rw [hg₂, hgY, hg] <;> rfl
  refine (c_16 prof).run c hin (fun j g' _ V' =>
      ((j = 40 ∧ X.cpu.gpr.rdx.setWidth 8 ≠ 0#8) ∨ (j = 31 ∧ X.cpu.gpr.rdx.setWidth 8 = 0#8)) ∧
      g' = { Y₂.cpu.gpr with rdx := Y₂.cpu.gpr.rsi, rsi := Y₂.cpu.gpr.r9, rdi := 1#64 } ∧
      V' = Vfill V X.cpu.gpr.rsi 0#64 (17 + 1)) hK₂ hA₂ hr₂
    (vc_16 (fun h _ => ⟨Or.inl ⟨rfl, by rw [← hdx]; exact h⟩, rfl, rfl⟩)
      (fun h _ => ⟨Or.inr ⟨rfl, by rw [← hdx]; exact h⟩, rfl, rfl⟩)) ?_
  rintro j' g₃ fl₃ V₃ ⟨hj, hg₃, hV₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hgY₃ -
  subst V₃
  have hgT : Y₃.cpu.gpr = gT X.cpu.gpr := by rw [hgY₃, hg₃, hg₂, hgY, hg] <;> rfl
  rcases hj with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · refine c.s_jmp_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_40 _) hinX (Xst.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    exact kx h Y₄ t₄ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) (by rw [hg₄, hgT])
  · refine c.s_jmp_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_31 _) hinL hL (by decide) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    exact kl h Y₄ t₄ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) (by rw [hg₄, hgT])

end FV7z.Mls
