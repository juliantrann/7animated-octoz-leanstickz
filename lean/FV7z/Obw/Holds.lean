import FV7z.Obw.Cuts
import FV7z.Aac.Code
import FV7z.Fob.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
/-!
# `NWindows::NFile::NIO::COutFile::OpenBinary_forWrite_oflag (name, flags)` (PLAN.md §M, M1)

7-Zip 26.06's `COutFile::OpenBinary_forWrite_oflag (name, flags)` at `0x456250` in `7zzs`
(`CPP/Windows/FileIO.cpp`; `objdump -d`), `this` in `rdi`, `name` in `rsi`, `flags` in `edx`: `Path = name;
return OpenBinary (name, flags, mode_for_Create)`. `push r13; mov r13d, edx; push r12; mov r12, rsi; push rbp;
mov rbp, rdi; lea rdi, [rdi + 0x48]`, the `call` at 22 to `AString::operator= (const char *)` (`Aac.aac_at`) on the
field `Path` at `this + 0x48`, then `mov ecx, [rbp + 0x58]` (the field `mode_for_Create`), `mov edx, r13d; mov rsi,
r12; mov rdi, rbp; pop rbp; pop r12; pop r13` and the tail `jmp` at 44 to `CFileBase::OpenBinary` (`Fob.fob_at`),
with the return address of the caller on top of the stack.

The callee is a hypothesis (`ku`), as in `FV7z/Ucu/Holds.lean`: a continuation at its entry, given the run from its
return (`rsp` 24 below the entry's, `rbp` = `this`, `r12` = `name`, `r13` = `flags`, the saved registers and the
return address as they were: `Sv`) and its own post `Pa`. `kj` is the continuation at `OpenBinary`'s entry, given
that the return address is still on top of the stack.

- `V0`, `gC`: the bytes and the registers at the `call`.
- `Sv`: the saved `rbp`, `r12`, `r13` and the return address in the bytes.
- `vc_0`, `vc_27`: the verification conditions of the pieces.
- `obw_ok`: from the entry, through `AString::operator=`, to `OpenBinary`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Obw

/-- The `call` to `AString::operator= (const char *)`. -/
def pca : List Byte := [0xe8, 0x55, 0x62, 0xff, 0xff]
theorem pca_0 : ∀ feat, Dec feat pca 0 (FV7z.mk .call 64 [.rel 18446744073709511253] 5) := by dec_rfl
theorem wc_22 : pca <+: obw.drop 22 := by decide +kernel
theorem call_22 (feat : Features) : Dec feat obw 22 (FV7z.mk .call 64 [.rel 18446744073709511253] 5) :=
  Dec.shift (j := 22) (k := 0) (pca_0 feat) wc_22 (Nat.zero_le _)
theorem tgt_22 : obw_at.add (22 + 5) + BitVec.ofNat 64 18446744073709511253 = Aac.aac_at.add 0 := by decide

/-- The tail `jmp` to `CFileBase::OpenBinary`. -/
def pjm : List Byte := [0xe9, 0xdf, 0xfd, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551071] 5) := by dec_rfl
theorem wj_44 : pjm <+: obw.drop 44 := by decide +kernel
theorem jmp_44 (feat : Features) : Dec feat obw 44 (FV7z.mk .jmp 64 [.rel 18446744073709551071] 5) :=
  Dec.shift (j := 44) (k := 0) (pjm_0 feat) wj_44 (Nat.zero_le _)
theorem tgt_44 : obw_at.add (44 + 5) + BitVec.ofNat 64 18446744073709551071 = Fob.fob_at.add 0 := by decide

theorem aac_lt : 0 < Aac.aac.length := by rw [Aac.aac_length]; decide
theorem fob_lt : 0 < Fob.fob.length := by rw [Fob.fob_length]; decide

/-- The bytes at the `call`: `r13`, `r12`, `rbp` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)

/-- The registers at the `call`: `r13` = `flags`, `r12` = `name`, `rbp` = `this`, `rdi` = `&Path`, 24 below the
entry. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      r13 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx), r12 := g.rsi, rbp := g.rdi, rdi := g.rdi + 72#64,
      rsp := g.rsp - 8 - 8 - 8 }

/-- The saved `rbp`, `r12`, `r13` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 24) = x.rbp ∧ rdq(V, x.rsp - 16) = x.r12 ∧ rdq(V, x.rsp - 8) = x.r13 ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `push r13; mov r13d, edx; push r12; mov r12, rsi; push rbp; mov rbp, rdi; lea rdi, [rdi + 0x48]` to the `call`
at 22. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 ⊢
  wpx [W_0, o0, V0, gC]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `AString::operator=`: `mov ecx, [rbp + 0x58]; mov edx, r13d; mov rsi, r12; mov rdi, rbp; pop rbp;
pop r12; pop r13` to the `jmp` at 44. -/
theorem vc_27 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {q : Addr} (hbp : g.rbp = q)
    (fq : ∀ i < 4, Foot F.data (Addr.add (q + 88#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 44
      { g with
          rcx := (rdd(V, q + 88#64)).setWidth 64, rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.r13),
          rsi := g.r12, rdi := q, rbp := rdq(V, g.rsp), r12 := rdq(V, g.rsp + 8), r13 := rdq(V, g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl V) :
    W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp fq hl0 hl1 hl2 h ⊢
  subst hbp
  wpx [W_27, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COutFile::OpenBinary_forWrite_oflag (name, flags)` (`this` = `rdi`, `name` = `rsi`, `flags` = `edx`) from its
entry. At `AString::operator=`'s entry the registers are `gC` with `rsp` 32 below the entry's, the bytes `V0` with
the return address pushed (`ku`); back at `obw_at + 27` (`Sv`, `Pa`), at `OpenBinary`'s entry with `rdi` = `this`,
`rsi` = `name`, `edx` = `flags`, `ecx` = `mode_for_Create`, `rbp`, `r12`, `r13` and `rsp` as at the entry and the
return address still on top of the stack (`kj`). -/
theorem obw_ok {Pa : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L obw_at obw) (hinA : CodeIn L Aac.aac_at Aac.aac)
    (hinF : CodeIn L Fob.fob_at Fob.fob)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = obw_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (fq : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 88#64) i))
    {e₂ : Addr}
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (obw_at.add 27) 8)) →
      Y.cpu.rip = Aac.aac_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = obw_at.add 27 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Z.cpu.gpr.r12 = X.cpu.gpr.rsi → Z.cpu.gpr.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) →
        Sv V₁ X.cpu.gpr e₂ → Pa Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kj : ∀ (Z : State) (V₁ : Addr → Byte) (Y : State) (t' : Nat), Pa Z V₁ → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V₁ → Y.cpu.rip = Fob.fob_at →
      Y.cpu.gpr = { Z.cpu.gpr with
          rcx := (rdd(V₁, X.cpu.gpr.rdi + 88#64)).setWidth 64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx), rsi := X.cpu.gpr.rsi,
          rdi := X.cpu.gpr.rdi, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
          rsp := X.cpu.gpr.rsp } →
      rdq(V₁, X.cpu.gpr.rsp) = e₂ →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have c32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = obw_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `AString::operator=`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_22 _) hinA (tgt := 0) aac_lt tgt_22 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hsY, c32, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `AString::operator=`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzp hz12 hz13 hsv hPa
  refine (c_27 prof).run c hin (fun j' g' _ V' => j' = 44 ∧
      g' = { Z.cpu.gpr with
          rcx := (rdd(V₁, X.cpu.gpr.rdi + 88#64)).setWidth 64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx), rsi := X.cpu.gpr.rsi,
          rdi := X.cpu.gpr.rdi, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
          rsp := X.cpu.gpr.rsp } ∧
      V' = V₁) hKZ hAZ hrZ
    (vc_27 hzp fq (by rw [hzs]; exact h24) (by rw [hzs, a16]; exact h16) (by rw [hzs, a16, a8]; exact h8)
      fun _ => ⟨rfl, by rw [hzs, a16, a8, e8, hz12, hz13, sw_64_32, hsv.1, hsv.2.1, hsv.2.2.1], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  -- the tail `jmp` to `CFileBase::OpenBinary`
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_44 _) hinF (tgt := 0) fob_lt tgt_44 ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact kj Z V₁ Y₃ t₅ hPa hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (by rw [hg₃, hgU]) hsv.2.2.2

end FV7z.Obw
