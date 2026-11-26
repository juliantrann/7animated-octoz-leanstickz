import FV7z.Eex.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensor::ExtendExclude` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensor::ExtendExclude ()` at `0x4535b0` in `7zzs` (`CPP/Common/Wildcard.cpp`;
`objdump -d`). PROBES of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Eex

variable {F : Footprint} {Wl : List Rgn}

/-- PROBE. -/
theorem vc_0p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_24, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

/-- PROBE. -/
theorem vc_55p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_55 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_55, W_40, W_52, W_136, W_140, o4, o2, o3, o10, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

/-- PROBE. -/
theorem vc_68p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_68 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_68, o5, Op.shl64, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

/-- PROBE. -/
theorem vc_80p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_80 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_80, W_84, o6, o7, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

/-- PROBE. -/
theorem vc_111p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_111 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_111, o8, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

/-- PROBE. -/
theorem vc_121p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_121 F Wl (fun _ _ _ _ => False) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_121, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]

end FV7z.Eex
