import FV7z.Mun.Cuts
import FV7z.Mmp.Cuts
import FV7z.Gdt.Cuts
import FV7z.Tcg.Cuts
import FV7z.Lemmas.CmovLd
/-! Probe of the pieces' conditions (temporary). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.ProbeB3
set_option linter.unusedVariables false
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mun.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mun.W_0, Mun.o0, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mun.W_11 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mun.W_11, Mun.o1, Mun.W_20, Mun.o2, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mmp.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mmp.W_0, Mmp.o0, Mmp.W_13, Mmp.o1, Mmp.W_80, Mmp.o5, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mmp.W_25 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mmp.W_25, Mmp.o2, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mmp.W_38 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mmp.W_38, Mmp.o3, Mmp.W_144, Mmp.o6, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Mmp.W_46 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mmp.W_46, Mmp.o4, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Gdt.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Gdt.W_0, Gdt.o0, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Gdt.W_37 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Gdt.W_37, Gdt.o1, Gdt.W_64, Gdt.o2, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Tcg.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Tcg.W_0, Tcg.o0, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Tcg.W_42 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Tcg.W_42, Tcg.o1, Tcg.W_176, Tcg.o6, Tcg.W_50, Tcg.o2, Tcg.W_57, Tcg.o3, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Tcg.W_143 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Tcg.W_143, Tcg.o4, Tcg.W_159, Tcg.o5, Op.ldf, Op.stf, Op.xormf, Op.cmovld32]
  trace_state
  sorry

end FV7z.ProbeB3
