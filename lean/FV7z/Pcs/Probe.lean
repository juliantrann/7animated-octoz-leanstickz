import FV7z.Pcs.Cuts
import FV7z.Lemmas.CmovLd
/-! Probe of the pieces' conditions (temporary). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.ProbePcs
set_option linter.unusedVariables false
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_0, Pcs.o0, Op.ldf, Op.stf, Op.xormf]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_47 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx -implicitDefEqProofs [Pcs.W_47, Pcs.W_56, Pcs.W_65, Pcs.W_74, Pcs.W_94, Pcs.o1, Pcs.o2, Pcs.o3, Pcs.o4,
    Pcs.o5, Op.ldsx]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_112 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_112, Pcs.o6]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_122 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_122, Pcs.W_129, Pcs.o7, Pcs.o8, Op.shl64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_144 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_144, Pcs.W_160, Pcs.o9, Pcs.o10, Op.xormf]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_176 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_176, Pcs.o11]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_184 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_184, Pcs.o12]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Pcs.W_200 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Pcs.W_200, Pcs.o13]
  trace_state
  sorry

end FV7z.ProbePcs
