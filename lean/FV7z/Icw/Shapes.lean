import FV7z.Icw.Cuts
import FV7z.Lemmas.BlkOps20
/-! Goal shapes of the pieces of `intel_check_word` after `wpx` (triage only, not imported). -/
namespace FV7z.Icw
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
set_option linter.unusedSimpArgs false

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_464 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_464, W_472, W_525, W_763, o0, o1, o2, o19, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_558 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_558, o4, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_567 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_567, W_577, W_588, W_593, W_599, W_610, W_621, W_766, W_544, o5, o6, o7, o8, o9, o10, o11, o23, o3, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_630 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_630, o12, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_640 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_640, o13, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_656 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_656, W_658, W_663, W_736, W_745, o14, o15, o21, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_682 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_682, W_696, W_705, W_929, W_940, W_945, W_954, W_964, W_1024, o16, o17, o18, o34, o35, o32, o37, o38, o40, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_717 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_717, o19, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_719 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_719, o20, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_752 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_752, o22, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_775 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_775, W_782, W_794, W_803, W_1152, W_1224, o24, o25, o26, o27, o45, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_821 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_821, o29, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_831 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_831, o24, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_838 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_838, W_816, o30, o28, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_856 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_856, W_861, o31, o28, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_866 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_866, W_875, o32, o33, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_885 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_885, W_896, W_905, W_914, W_1072, W_974, o34, o35, o32, o36, o44, o39, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1033 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1033, W_1038, o41, o8, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1048 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1048, W_1057, W_1067, o42, o43, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1230 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1230, W_1241, o49, o50, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1250 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1250, o47, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1260 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1260, W_1267, o24, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc]
  trace_state
  sorry

end FV7z.Icw
