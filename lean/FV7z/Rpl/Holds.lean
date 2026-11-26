import FV7z.Rpl.Cuts
import FV7z.Lemmas.BlkOps12
/-!
# `AString::Replace` (PLAN.md §M, M1) — probe
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rpl

variable {F : Footprint} {Wl : List Rgn}

theorem pr_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_27, W_136, o0, o1, o10]
  all_goals done

theorem pr_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_45, W_53, o2, o3]
  all_goals done

theorem pr_77 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_77 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_77, o5]
  all_goals done

theorem pr_90 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_90 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_90, o6, Op.cmpmr]
  all_goals done

theorem pr_100 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_100 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_100, o7]
  all_goals done

theorem pr_112 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_112 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_112, W_64, o8, o4]
  all_goals done

theorem pr_118 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_118 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_118, o9]
  all_goals done

theorem pr_148 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_148 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_148, W_152, o11, o9]
  all_goals done

end FV7z.Rpl
