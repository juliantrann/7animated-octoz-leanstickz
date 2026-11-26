import FV7z.Stl.Cuts
/-! Probe of the pieces' conditions (temporary). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.ProbeStl
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_0, Stl.W_40, Stl.W_49, Stl.W_58, Stl.o0, Stl.o1, Stl.o2, Stl.o3, Op.ldsxq, Op.ldzx, Op.lda, Op.lea,
    Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_80 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_80, Stl.o4, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_99 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_99, Stl.W_107, Stl.W_116, Stl.W_496, Stl.W_672, Stl.W_969, Stl.W_981, Stl.o5, Stl.o6, Stl.o7, Stl.o38,
    Stl.o41, Stl.o43, Stl.o52, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa,
    Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_133 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_133, Stl.W_142, Stl.W_464, Stl.W_473, Stl.W_592, Stl.W_808, Stl.W_827, Stl.W_835, Stl.W_881, Stl.o8,
    Stl.o9, Stl.o36, Stl.o37, Stl.o39, Stl.o47, Stl.o48, Stl.o49, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_150 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_150, Stl.W_159, Stl.o10, Stl.o11, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_171 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_171, Stl.W_207, Stl.o12, Stl.o13, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_216 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_216, Stl.o14, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_223 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_223, Stl.o15, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_265 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_265, Stl.W_279, Stl.o17, Stl.o18, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_291 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_291, Stl.o19, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_296 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_296, Stl.W_305, Stl.W_314, Stl.W_317, Stl.W_325, Stl.o20, Stl.o21, Stl.o22, Stl.o23, Stl.o24, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64,
    Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_332 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_332, Stl.W_340, Stl.W_256, Stl.W_258, Stl.o16, Stl.o25, Stl.o26, Op.ldsxq, Op.ldzx, Op.lda, Op.lea,
    Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_345 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_345, Stl.W_366, Stl.o27, Stl.o28, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_368 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_368, Stl.W_377, Stl.W_387, Stl.o29, Stl.o30, Stl.o31, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_390 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_390, Stl.W_399, Stl.W_1194, Stl.o32, Stl.o33, Stl.o54, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_432 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_432, Stl.o34, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_448 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_448, Stl.o35, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_604 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_604, Stl.W_613, Stl.W_934, Stl.W_939, Stl.o10, Stl.o36, Stl.o40, Stl.o53, Op.ldsxq, Op.ldzx, Op.lda,
    Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_745 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_745, Stl.o42, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_748 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_748, Stl.W_760, Stl.W_772, Stl.W_909, Stl.W_915, Stl.o43, Stl.o44, Stl.o45, Stl.o50, Stl.o51, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64,
    Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_790 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_790, Stl.o46, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_927 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_927, Stl.o52, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

end FV7z.ProbeStl
