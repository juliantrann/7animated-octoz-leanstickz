import FV7z.Ecq.Cuts
import FV7z.Lemmas.LeafRet
/-! Triage probe (not imported): the goals `wpx` leaves for the pieces at 0, 24 and 35. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq.Probe

set_option linter.unusedVariables false
variable {F : Footprint} {Wl : List Rgn}

example {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  trace_state
  sorry

example {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_35, o2]
  trace_state
  sorry

example {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_24, W_35, W_64, W_84, o1, o2, o5, o6, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  trace_state
  sorry

end FV7z.Ecq.Probe
