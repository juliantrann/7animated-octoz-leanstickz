import FV7z.U8w.Cuts
/-! Probe (triage only): the goals `wpx` leaves for each piece. -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.U8w

variable {F : Footprint} {Wl : List Rgn}

theorem probe_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_15, o0, o1]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_32, W_50, W_216, W_62, W_67, o2, o3, o15, o4, o5]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_83 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_83 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_83, W_256, W_264, W_269, W_488, W_106, W_352, W_118, W_384, W_416, W_464, W_420, W_392, W_130, o6, o16,
      o17, o18, o29, o7, o22, o8, o23, o25, o28, o26, o24, o9]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_141 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_141 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_141, o10]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_152 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_152 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_152, W_178, o11, o12]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_184 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_184 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_184, o13]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_200 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_200 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_200, o14]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_296 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_296 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_296, W_440, W_305, o19, o27, o20]
  repeat' (first | apply And.intro | intro _)
  done

theorem probe_328 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_328 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_328, o21]
  repeat' (first | apply And.intro | intro _)
  done

end FV7z.U8w
