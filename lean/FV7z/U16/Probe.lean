import FV7z.U16.Cuts
/-! Probe (triage only): the goals `wpx` leaves for each piece. -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.U16

variable {F : Footprint} {Wl : List Rgn}

theorem probe_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_579, W_24, o0, o43, o1, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_109 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_109 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_109, o5, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_116 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_116 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_116, o6, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_125, W_80, W_152, W_432, W_504, W_436, W_163, W_88, W_93, W_136, o7, o2, o9, o36, o40, o37, o10, o3, o4,
      Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_141 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_141 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_141, o8, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_174 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_174 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_174, o11, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_192 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_192 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_192, W_368, W_376, W_552, W_561, o12, o30, o31, o3, o42, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_201 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_201 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_201, o13, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_209 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_209 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_209, W_214, W_225, W_238, W_242, W_336, W_345, W_363, W_252, W_257, W_265, o14, o15, o16, o17, o18, o27,
      o28, o29, o19, o20, o21, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_272 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_272 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_272, W_528, W_547, W_281, o22, o41, o23, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_295 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_295 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_295, o24, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_299 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_299 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_299, o25, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_312 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_312 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_312, o26, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_392 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_392 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_392, W_456, W_461, W_400, W_405, o32, o3, o38, o33, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_409 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_409 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_409, o34, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_413 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_413 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_413, o35, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_492 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_492 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_492, o39, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  done

end FV7z.U16
