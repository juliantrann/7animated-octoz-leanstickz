import FV7z.Dsp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnJt
import FV7z.Tun.Inv
/-!
# `CDirItems::ScanProgress` (PLAN.md §M, M1)

7-Zip 26.06's `CDirItems::ScanProgress (dirIndex)` at `0x5c01d0` in `7zzs` (`CPP/7zip/UI/Common/EnumDirItems.cpp`):
`Callback` (the 8 bytes at `this + 0xc0`); if it is NULL, `return S_OK` (`xor eax, eax; ret`, 48 and 50); else a tail
call through its vtable (`jmp rax`, 38) to the second entry, `ScanProgress (Stat, FS_GetPrefix (dirIndex), true)`,
with `rdi` = `Callback`, `rsi` = `&Stat` (`this + 0x48`), `rdx` = `dirIndex` and `ecx` = 1. One piece of the code from
the entry, its two ways ending at the `ret` and at the jump.

- `cb`: `Callback`; `fn`: the second entry of its vtable.
- `vc_z`, `vc_nz`: the verification conditions of the piece, one for each way.
- `dsp_ok`: with `Callback` NULL, at the return address with `rax` = 0 (`kn`); else at `fn`, a code byte (`hR`), with
  the registers of the call (`kx`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dsp

/-- The `jmp rax`. -/
def pjr : List Byte := [0xff, 0xe0]
theorem pjr_0 : ∀ feat, Dec feat pjr 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem wr_38 : pjr <+: dsp.drop 38 := by decide +kernel
theorem jmp_38 (feat : Features) : Dec feat dsp 38 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 38) (k := 0) (pjr_0 feat) wr_38 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_50 : pret <+: dsp.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat dsp 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)

/-- `Callback`, for the object at `p`. -/
abbrev cb (V : Addr → Byte) (p : Addr) : BitVec 64 := rdq(V, p + 192#64)
/-- The second entry of `Callback`'s vtable. -/
abbrev fn (V : Addr → Byte) (p : Addr) : BitVec 64 := rdq(V, rdq(V, rdq(V, p + 192#64)) + 8#64)

variable {F : Footprint} {Wl : List Rgn}

/-- `Callback` NULL: the load, the test, `xor eax, eax`, up to the `ret`. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdq(V, g.rdi + 192#64) == 0) = true)
    (hb : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 192#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 50 ∧
      g' = { g with rax := 0#64, rdx := g.rsi, r8 := rdq(V, g.rdi + 192#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hb ⊢
  wpx [W_0, W_19, W_48, o0, o1, o2, hz, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | (intro hc; simp [hz] at hc)
    | (intro hc; exact absurd hz (by simp [hc]))
    | intro _

/-- `Callback` not NULL: the load, the test, the loads of the vtable and its entry, up to the jump. -/
theorem vc_nz {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdq(V, g.rdi + 192#64) == 0) = false)
    (hb : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 192#64) i))
    (h1 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rdi + 192#64)) i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, g.rdi + 192#64)) + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 38 ∧
      g' = { g with
          rax := rdq(V, rdq(V, rdq(V, g.rdi + 192#64)) + 8#64),
          rcx := 1#64,
          rdx := g.rsi,
          rsi := g.rdi + 72#64,
          rdi := rdq(V, g.rdi + 192#64),
          r8 := rdq(V, g.rdi + 192#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hb h1 h2 ⊢
  wpx [W_0, W_19, W_48, o0, o1, o2, hz, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | (intro hc; simp [hz] at hc)
    | (intro hc; exact absurd hz (by simp [hc]))
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `CDirItems::ScanProgress (dirIndex)` (`this` = `rdi`): with `Callback` NULL, at the return address with `rax` = 0
(`kn`); else at the second entry of `Callback`'s vtable, a code byte (`hR`), with `rax` that entry, `rdi` = `r8` =
`Callback`, `rsi` = `this + 0x48`, `rdx` = `dirIndex` and `rcx` = 1 (`kx`). No bytes are stored. -/
theorem dsp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dsp_at dsp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dsp_at)
    (hb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 192#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (h1 : cb V X.cpu.gpr.rdi ≠ 0#64 → ∀ i < 8, Foot F.data (Addr.add (cb V X.cpu.gpr.rdi) i))
    (h2 : cb V X.cpu.gpr.rdi ≠ 0#64 → ∀ i < 8, Foot F.data (Addr.add (rdq(V, cb V X.cpu.gpr.rdi) + 8#64) i))
    (hR : cb V X.cpu.gpr.rdi ≠ 0#64 → ∃ (eR : Addr) (codeR : List Byte) (jR : Nat),
      CodeIn L eR codeR ∧ jR < codeR.length ∧ fn V X.cpu.gpr.rdi = eR.add jR)
    (kn : cb V X.cpu.gpr.rdi = 0#64 → ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
          rax := 0#64,
          rdx := X.cpu.gpr.rsi,
          rsp := X.cpu.gpr.rsp + 8,
          r8 := cb V X.cpu.gpr.rdi } →
      GoG prof L o gev gP gE Z t')
    (kx : cb V X.cpu.gpr.rdi ≠ 0#64 → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = fn V X.cpu.gpr.rdi →
      Y.cpu.gpr = { X.cpu.gpr with
          rax := fn V X.cpu.gpr.rdi,
          rcx := 1#64,
          rdx := X.cpu.gpr.rsi,
          rsi := X.cpu.gpr.rdi + 72#64,
          rdi := cb V X.cpu.gpr.rdi,
          r8 := cb V X.cpu.gpr.rdi } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = dsp_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : cb V X.cpu.gpr.rdi = 0#64
  · have hz : (rdq(V, X.cpu.gpr.rdi + 192#64) == 0) = true := beq_iff_eq.2 h0
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 50 ∧
        g' = { X.cpu.gpr with rax := 0#64, rdx := X.cpu.gpr.rsi, r8 := rdq(V, X.cpu.gpr.rdi + 192#64) } ∧ V' = V)
      hK hA hrip' (vc_z hz hb) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_50 _) (by rw [hsp]; exact hl) hin₂ h₂
      (by rw [hsp]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn h0 Z t' hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · have hz : (rdq(V, X.cpu.gpr.rdi + 192#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    obtain ⟨eR, codeR, jR, hinR, hjR, hRt⟩ := hR h0
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 38 ∧
        g' = { X.cpu.gpr with
          rax := rdq(V, rdq(V, rdq(V, X.cpu.gpr.rdi + 192#64)) + 8#64),
          rcx := 1#64,
          rdx := X.cpu.gpr.rsi,
          rsi := X.cpu.gpr.rdi + 72#64,
          rdi := rdq(V, X.cpu.gpr.rdi + 192#64),
          r8 := rdq(V, X.cpu.gpr.rdi + 192#64) } ∧ V' = V)
      hK hA hrip' (vc_nz hz hb (h1 h0) (h2 h0)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine c.s_jmp_rx hKY hAY hin (lt_len (by decide)) hrY (jmp_38 _) hinR hjR (by rw [hgY]; exact hRt) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kx h0 Y₂ t₂ hK₂ hA₂ (hr₂.trans hRt.symm) (hg₂.trans hgY)

end FV7z.Dsp
