import FV7z.Cpt.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensorNode::CheckPathCurrent` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensorNode::CheckPathCurrent (include, pathParts, isFile)` at `0x453050` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): `const CObjectVector<CItem> &items = include ? IncludeItems :
ExcludeItems; FOR_VECTOR (i, items) if (items[i].CheckPath (pathParts, isFile)) return true; return false;`
(`this` = `rdi`, `include` = `sil`, `pathParts` = `rdx`, `isFile` = `cl`; `CItem::CheckPath` at `0x4529d0`, called
at 74).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cpt

variable {F : Footprint} {Wl : List Rgn}

/-- PROBE: the entry. -/
theorem vc_0p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_46, o0, Op.cmov64, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]

/-- PROBE: the loop's body. -/
theorem vc_58p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_58 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_58, o2]

/-- PROBE: after the call. -/
theorem vc_79p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_79 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_79, W_48, W_83, o3, o1, o4, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]

/-- PROBE: none matched. -/
theorem vc_96p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_96 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_96, o5]

end FV7z.Cpt
