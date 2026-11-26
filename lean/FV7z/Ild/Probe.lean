import FV7z.Ild.Cuts
/-! Probe of the pieces' conditions (temporary). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.ProbeIld
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_0, Ild.o0, Ild.W_28, Ild.o1, Ild.W_48, Ild.o2, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi,
    Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_65 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_65, Ild.o3, Ild.W_73, Ild.o4, Ild.W_97, Ild.o5, Ild.W_114, Ild.o6, Op.ldsx, Op.lea, Op.cmpmi,
    Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_127 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_127, Ild.o7, Ild.W_136, Ild.o8, Ild.W_177, Ild.o9, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm,
    Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_196 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_196, Ild.o10, Ild.W_208, Ild.o11, Ild.W_217, Ild.o12, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm,
    Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_228 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_228, Ild.o13, Ild.W_234, Ild.o14, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_240 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_240, Ild.o15, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_248 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_248, Ild.o16, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_264 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_264, Ild.o17, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_279 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_279, Ild.o18, Ild.W_285, Ild.o19, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_288 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_288, Ild.o20, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_299 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_299, Ild.o21, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_307 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_307, Ild.o22, Ild.W_316, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_318 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_318, Ild.o23, Ild.W_324, Ild.o20, Ild.W_335, Ild.o24, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm,
    Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_336 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_336, Ild.o25, Ild.W_341, Ild.o26, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Ild.W_435 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Ild.W_435, Ild.o34, Ild.W_439, Ild.o35, Ild.W_449, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi,
    Op.cmov32]
  trace_state
  sorry
