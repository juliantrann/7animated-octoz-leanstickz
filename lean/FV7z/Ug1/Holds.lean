import FV7z.Ug1.Cuts
import FV7z.Lemmas.BlkOps12
/-! probe -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ug1

variable {F : Footprint} {Wl : List Rgn}

theorem pr_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_33, o0, o1]
  all_goals done

theorem pr_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_37, o2]
  all_goals done

theorem pr_42 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_42 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_42, o3]
  all_goals done

theorem pr_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_50, o4]
  all_goals done

end FV7z.Ug1
