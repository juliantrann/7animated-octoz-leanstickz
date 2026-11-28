import FV7z.Cst.Cuts
import FV7z.Cfn.Code
import FV7z.Cfn.Blocks
import FV7z.Lemmas.LeafRet
/-!
# `CompareStrings` (PLAN.md §M, M1)

7-Zip 26.06's `CompareStrings (p1, p2, param)` at `0x5dca50` in `7zzs` (`CPP/7zip/UI/Common/SortUtils.cpp`;
`objdump -d`), the comparison `SortFileNames` sorts the indices with: `p1`, `p2` (`rdi`, `rsi`) point to two 32-bit
indices and `param` (`rdx`) to the `UStringVector`, whose first 8 bytes are its items `P`. It loads the strings
`s1` = `P[*p1]` and `s2` = `P[*p2]` (the 8-byte pointers at `P + 8 * index`) and their characters (each `UString`'s
first 8 bytes), then jumps (21) to `CompareFileNames` (`Cfn.cfn_at`) with them in `rdi` and `rsi`. No stores.

The callee is a hypothesis (`kf`), as in `FV7z/Sos/Holds.lean`; `Cfn.cfn_ok` is its contract.

- `gS`: the registers at the jump; `Ft`: the bytes read.
- `vc_0`: from the entry to the jump; `cst_ok`: from the entry to `CompareFileNames`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cst

set_option linter.unusedSimpArgs false

/-- The jump to `CompareFileNames`. -/
def pjm : List Byte := [0xe9, 0x46, 0x58, 0xe7, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073707935814] 5) := by dec_rfl
theorem wj_21 : pjm <+: cst.drop 21 := by decide +kernel
theorem jmp_21 (feat : Features) : Dec feat cst 21 (FV7z.mk .jmp 64 [.rel 18446744073707935814] 5) :=
  Dec.shift (j := 21) (k := 0) (pjm_0 feat) wj_21 (Nat.zero_le _)

/-- The items `P` of the vector. -/
abbrev iP (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rdx)
/-- The index at `p1`, zero-extended. -/
abbrev i1 (V : Addr → Byte) (g : Gprs) : BitVec 64 := BitVec.setWidth 64 rdd(V, g.rdi)
/-- The index at `p2`, zero-extended. -/
abbrev i2 (V : Addr → Byte) (g : Gprs) : BitVec 64 := BitVec.setWidth 64 rdd(V, g.rsi)
/-- The string `P[*p1]`. -/
abbrev s1 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, iP V g + i1 V g * 8#64)
/-- The string `P[*p2]`. -/
abbrev s2 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, iP V g + i2 V g * 8#64)

/-- The registers at the jump: `rdi`, `rsi` the characters of `s1`, `s2`. -/
def gS (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := s1 V g, rcx := i1 V g, rdx := s2 V g, rsi := rdq(V, s2 V g), rdi := rdq(V, s1 V g) }

/-- The bytes read. -/
structure Ft (F : Footprint) (V : Addr → Byte) (g : Gprs) : Prop where
  fp : ∀ i < 8, Foot F.data (Addr.add g.rdx i)
  f1 : ∀ i < 4, Foot F.data (Addr.add g.rdi i)
  f2 : ∀ i < 4, Foot F.data (Addr.add g.rsi i)
  fs2 : ∀ i < 8, Foot F.data (Addr.add (iP V g + i2 V g * 8#64) i)
  fs1 : ∀ i < 8, Foot F.data (Addr.add (iP V g + i1 V g * 8#64) i)
  fc2 : ∀ i < 8, Foot F.data (Addr.add (s2 V g) i)
  fc1 : ∀ i < 8, Foot F.data (Addr.add (s1 V g) i)

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 800000 in
/-- From the entry to the jump. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hF : Ft F V g) :
    W_0 F Wl (fun j' g' _ V' => j' = 21 ∧ g' = gS V g ∧ V' = V) g f V := by
  obtain ⟨fp, f1, f2, fs2, fs1, fc2, fc1⟩ := hF
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp f1 f2 fs2 fs1 fc2 fc1 ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact rfl | exact trivial | assumption | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CompareStrings (p1, p2, param)` from its entry to `CompareFileNames`'s entry: the registers `gS`, the bytes as
they were. -/
theorem cst_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cst_at cst) (hinC : CodeIn L Cfn.cfn_at Cfn.cfn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cst_at) (hF : Ft F V X.cpu.gpr)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Cfn.cfn_at → Y.cpu.gpr = gS V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 21 ∧ g' = gS V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hF) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_21 _) hinC (Cfn.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Cst
