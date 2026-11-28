import FV7z.Sdf.Cuts
import FV7z.Sdr.Holds
/-!
# `CFiTimesCAM::SetDirTime_to_FS` (PLAN.md §M, M1)

7-Zip 26.06's `CFiTimesCAM::SetDirTime_to_FS (path)` at `0x5ad590` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`; `objdump -d`): with `this` = `p` in `rdi`, the three times
`CTime`, `ATime`, `MTime` at `p`, `p + 16`, `p + 32` and their flags `CTime_Defined`, `ATime_Defined`,
`MTime_Defined` the bytes at `p + 48`, `p + 49`, `p + 50`,
`NDir::SetDirTime (path, CTime_Defined ? &CTime : NULL, ATime_Defined ? &ATime : NULL, MTime_Defined ? &MTime : NULL)`
as a tail jump (47) to `Sdr.sdr_at`: `rcx` the `MTime` pointer (`xor ecx, ecx; cmp byte [rdi + 50], 0; mov r8, rsi;
je; lea rcx, [rdi + 32]`, joined at 19), `rdx` the `ATime` pointer (`xor edx, edx; cmp byte [rdi + 49], 0; je;
lea rdx, [rdi + 16]`, joined at 31), `rsi` the `CTime` pointer (`cmp byte [rdi + 48], 0; mov esi, 0;
cmovne rsi, rdi`) and `rdi` = `path` (`mov rdi, r8`). No stores.

- `bt`: a flag byte; `ptr`: the pointer or NULL by a flag; `g19`, `g31`, `gF`: the registers at 19, 31 and the jump.
- `vc_0`, `vc_19`, `vc_31`: the verification conditions of the three pieces, each split on its flag.
- `sdf_ok`: from the entry, through `NDir::SetDirTime` (`Sdr.sdr_ok`), at `SetFileTime_Base` (its code a
  hypothesis) with the registers `Sdr.gR (gF V g)`, the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sdf

/-- The tail jump to `NDir::SetDirTime`. -/
def pjm : List Byte := [0xe9, 0x1c, 0x81, 0xea, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073708142876] 5) := by dec_rfl
theorem wj_47 : pjm <+: sdf.drop 47 := by decide +kernel
theorem jmp_47 (feat : Features) : Dec feat sdf 47 (FV7z.mk .jmp 64 [.rel 18446744073708142876] 5) :=
  Dec.shift (j := 47) (k := 0) (pjm_0 feat) wj_47 (Nat.zero_le _)
theorem tgt47 : sdf_at.add (47 + 5) + BitVec.ofNat 64 18446744073708142876 = Sdr.sdr_at.add 0 := by decide

/-- The byte at `p + k`. -/
abbrev bt (V : Addr → Byte) (p k : Addr) : Byte := ofBytesLE 8 ((byteAddrs (p + k) 1).map V)

/-- `q` if the flag `b` is set, else NULL. -/
def ptr (b : Byte) (q : Addr) : Addr := if b = 0#8 then 0#64 else q

/-- At 19: `rcx` the `MTime` pointer, `r8` = `path`. -/
abbrev g19 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rcx := ptr (bt V g.rdi 50#64) (g.rdi + 32#64), r8 := g.rsi }
/-- At 31: `rdx` the `ATime` pointer. -/
abbrev g31 (V : Addr → Byte) (g : Gprs) : Gprs := { g with rdx := ptr (bt V g.rdi 49#64) (g.rdi + 16#64) }
/-- At the jump: `rsi` the `CTime` pointer, `rdi` = `r8`. -/
abbrev g47 (V : Addr → Byte) (g : Gprs) : Gprs := { g with rsi := ptr (bt V g.rdi 48#64) g.rdi, rdi := g.r8 }
/-- From the entry to the jump. -/
abbrev gF (V : Addr → Byte) (g : Gprs) : Gprs := g47 V (g31 V (g19 V g))

variable {F : Footprint} {Wl : List Rgn}

/-- The clean-up of a flag's test. -/
local macro "sfx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [Op.cmpmi, ptr, bt, g19, g31, g47, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth,
    decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, false_implies,
    implies_true, eq_self_iff_true, ↓reduceIte, $ls,*])

/-- The closers. -/
local macro "cls" : tactic =>
  `(tactic| all_goals repeat'
    (first | (with_reducible rfl) | exact rfl | assumption | exact trivial | apply And.intro | intro _))

/-- `xor ecx, ecx; cmp byte [rdi + 50], 0; mov r8, rsi; je`, `lea rcx, [rdi + 32]` to 19. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f50 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 50#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 19 ∧ g' = g19 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f50 ⊢
  by_cases h : ofBytesLE 8 ((byteAddrs (rdi + 50#64) 1).map V) = 0#8
  · sfx [W_0, W_15, o0, o1, h]
    cls
  · sfx [W_0, W_15, o0, o1, h]
    cls

/-- `xor edx, edx; cmp byte [rdi + 49], 0; je`, `lea rdx, [rdi + 16]` to 31. -/
theorem vc_19 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f49 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 49#64) i)) :
    W_19 F Wl (fun j' g' _ V' => j' = 31 ∧ g' = g31 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f49 ⊢
  by_cases h : ofBytesLE 8 ((byteAddrs (rdi + 49#64) 1).map V) = 0#8
  · sfx [W_19, W_27, o2, o3, h]
    cls
  · sfx [W_19, W_27, o2, o3, h]
    cls

/-- `cmp byte [rdi + 48], 0; mov esi, 0; cmovne rsi, rdi; mov rdi, r8` to the jump at 47. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f48 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 48#64) i)) :
    W_31 F Wl (fun j' g' _ V' => j' = 47 ∧ g' = g47 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f48 ⊢
  by_cases h : ofBytesLE 8 ((byteAddrs (rdi + 48#64) 1).map V) = 0#8
  · sfx [W_31, o4, h]
    cls
  · sfx [W_31, o4, h]
    cls

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CFiTimesCAM::SetDirTime_to_FS (path)` (`this` = `rdi`, `path` = `rsi`) from its entry, through
`NDir::SetDirTime`: at `SetFileTime_Base` (`Sdr.tgt_at`) with the registers `Sdr.gR (gF V X.cpu.gpr)` (`rdi` = `path`,
`rsi` the `ATime` pointer, `rdx` the `MTime` pointer, `rcx` = 0), the bytes as they were. -/
theorem sdf_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdf_at sdf) (hinR : CodeIn L Sdr.sdr_at Sdr.sdr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sdf_at)
    (f48 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (f49 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 49#64) i))
    (f50 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 50#64) i))
    {cT : List Byte} (hinT : CodeIn L Sdr.tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Sdr.tgt_at →
      Y.cpu.gpr = Sdr.gR (gF V X.cpu.gpr) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 19 ∧ g' = g19 V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 f50) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine (c_19 prof).run c hin (fun j' g' _ V' => j' = 31 ∧ g' = g31 V (g19 V X.cpu.gpr) ∧ V' = V) hKY hAY hrY
    (by rw [hgY]; exact vc_19 f49) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₂
  refine (c_31 prof).run c hin (fun j' g' _ V' => j' = 47 ∧ g' = gF V X.cpu.gpr ∧ V' = V) hK₂ hA₂ hr₂
    (by rw [hg₂]; exact vc_31 f48) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₃
  refine c.s_jmp_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_47 _) hinR (Sdr.lt_len (j := 0) (by decide)) tgt47 ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  refine Sdr.sdr_ok c hinR hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hinT hT ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅
  exact k Y₅ t₅ hK₅ hA₅ hr₅ (hg₅.trans (congrArg Sdr.gR (hg₄.trans hg₃)))

end FV7z.Sdf
