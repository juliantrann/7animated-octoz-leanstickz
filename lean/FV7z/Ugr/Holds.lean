import FV7z.Ugr.Cuts
import FV7z.Lemmas.BlkOps12
/-! probe -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ugr

variable {F : Footprint} {Wl : List Rgn}

theorem pr_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_16, W_41, o0, o1, o2]
  all_goals done

theorem pr_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_48, o3]
  all_goals done

theorem pr_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_53, o4]
  all_goals done

theorem pr_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_61, o5]
  all_goals done

theorem pr_73 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_73 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_73, o6]
  all_goals done

end FV7z.Ugr
