import FV7z.Sen.Cuts
import FV7z.Rfw.Holds
/-!
# `StringsAreEqualNoCase` (PLAN.md §M, M1) — probe
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sen

variable {F : Footprint} {Wl : List Rgn}

theorem pr_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals done

theorem pr_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_45, o4]
  all_goals done

theorem pr_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_48, o5]
  all_goals done

theorem pr_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_53, o6]
  all_goals done

theorem pr_58 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_58 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_58, W_128, o7, o16]
  all_goals done

theorem pr_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_62, W_82, W_24, W_33, W_38, o8, o9, o1, o2, o3]
  all_goals done

theorem pr_87 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_87 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_87, W_92, o5, o10]
  all_goals done

theorem pr_95 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_95 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_95, W_120, W_100, W_105, o11, o15, o12, o13]
  all_goals done

theorem pr_112 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_112 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_112, o14]
  all_goals done

theorem pr_144 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_144 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_144, o17]
  all_goals done

end FV7z.Sen
