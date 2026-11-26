import FV7z.Utr.Cuts
import FV7z.Rfw.Holds
/-!
# `UString::TrimRight` (PLAN.md §M, M1) — probe
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Utr

variable {F : Footprint} {Wl : List Rgn}

theorem pr_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_16, o0, o1, Op.shl64]
  all_goals done

theorem pr_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_32, W_45, W_80, W_85, o2, o3, o6, o7]
  all_goals done

theorem pr_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_50, o4]
  all_goals done

theorem pr_59 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_59 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_59, o5]
  all_goals done

end FV7z.Utr
