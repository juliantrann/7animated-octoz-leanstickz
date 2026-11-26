import FV7z.Fcl.Cuts
import FV7z.Close.Holds
/-!
# `CFileBase::Close` (PLAN.md §M, M1) — probe of the goals
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fcl

variable {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.ld]
  done

theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, W_35, o1, o2, Op.sti]
  done

theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_46 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_46, o3]
  done

end FV7z.Fcl
