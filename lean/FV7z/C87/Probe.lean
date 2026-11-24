import FV7z.C87.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-! Probe: the goals after `wpx` at each cut point of `csuTg 87`. -/
namespace FV7z.C87
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {F : Footprint} {Wl : List Rgn}

theorem p2160 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2160 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2208 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2208 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2233 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2233 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2250 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2250 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2272 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2272 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2296 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2296 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

theorem p2364 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_2364 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2199, W_2160, W_2221, W_2208, W_2233, W_2264, W_2250, W_2272, W_2325, W_2296, W_2360, W_2364, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11]
  done

end FV7z.C87
