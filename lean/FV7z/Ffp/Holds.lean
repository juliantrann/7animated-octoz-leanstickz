import FV7z.Ffp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensor::FindPairForPrefix` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensor::FindPairForPrefix (prefix)` at `0x453550` in `7zzs` (`CPP/Common/Wildcard.cpp`;
`objdump -d`): `for (i = 0; i < Pairs.Size(); i++) if (CompareFileNames (Pairs[i].Prefix, prefix) == 0) return i;
return -1;` (`this` = `rdi`, `prefix` = `rsi`; `CompareFileNames` at `0x4522b0`, called at 57).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ffp

/-! ## The instructions outside the blocks -/

def pc57 : List Byte := [0xe8, 0x22, 0xed, 0xff, 0xff]
def pret : List Byte := [0xc3]
theorem pc57_0 : ∀ feat, Dec feat pc57 0 (FV7z.mk .call 64 [.rel 18446744073709546786] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc57 : pc57 <+: ffp.drop 57 := by decide +kernel
theorem w_72 : pret <+: ffp.drop 72 := by decide +kernel
theorem w_89 : pret <+: ffp.drop 89 := by decide +kernel
theorem w_95 : pret <+: ffp.drop 95 := by decide +kernel
theorem call_57 (feat : Features) : Dec feat ffp 57 (FV7z.mk .call 64 [.rel 18446744073709546786] 5) :=
  Dec.shift (j := 57) (k := 0) (pc57_0 feat) wc57 (Nat.zero_le _)
theorem ret_72 (feat : Features) : Dec feat ffp 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)
theorem ret_89 (feat : Features) : Dec feat ffp 89 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 89) (k := 0) (pret_0 feat) w_89 (Nat.zero_le _)
theorem ret_95 (feat : Features) : Dec feat ffp 95 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 95) (k := 0) (pret_0 feat) w_95 (Nat.zero_le _)

/-- `CompareFileNames`. -/
abbrev cfn_at : Addr := 0x4522b0
theorem tgt57 : ffp_at.add (57 + 5) + BitVec.ofNat 64 18446744073709546786 = cfn_at := by decide

/-! ## The pieces -/

/-- The registers at the loop's head the first time. -/
abbrev g40 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rbx := 0#64, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi,
    r12 := g.rsi }
/-- The three registers pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)
/-- The pair's address read at 50. -/
abbrev ia (V : Addr → Byte) (g : Gprs) : Addr :=
  rdq(V, rdq(V, g.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64)
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := ia V g, rdx := rdq(V, g.rbp), rsi := rdq(V, g.r12), rdi := rdq(V, ia V g) }

variable {F : Footprint} {Wl : List Rgn}

/-- No pairs: `eax` = -1, the `ret` at 95. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 8#64) = 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 95 ∧ g' = { g with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h f8 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- Pairs: the pushes, `i` = 0, to the loop's head. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 8#64) ≠ 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = g40 V g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g40, V1] at h f8 hs1 hs2 hs3 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
    Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- The loop's head to the `call`. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (f12 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add (ia V g) i)) :
    W_40 F Wl (fun j' g' _ V' => j' = 57 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, ia] at f0 f12 fi fp ⊢
  wpx [W_40, o3]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- PROBE: the goals of the piece after the `call`. -/
theorem vc_62p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_62 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_62, W_32, W_66, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]

end FV7z.Ffp
