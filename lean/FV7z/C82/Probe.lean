import FV7z.C82.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-! Probe: the goals after `wpx` at each cut point of `csuTg 82`. -/
namespace FV7z.C82
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {F : Footprint} {Wl : List Rgn}

theorem p1888 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_1888 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p1936 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_1936 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p1968 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_1968 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p1979 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_1979 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p2032 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2032 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p2048 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2048 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

theorem p2062 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2062 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1888, W_1945, W_1936, W_1968, W_2000, W_1989, W_1979, W_2046, W_2032, W_2048, W_2080, W_2072, W_2062, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12]
  done

end FV7z.C82
