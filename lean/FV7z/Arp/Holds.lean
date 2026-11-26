import FV7z.Arp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps17
/-! Probe. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Arp

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_11, W_24, o0, o1]
  done

theorem p_41 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_41 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_41, W_32, o3, o2]
  done

theorem p_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_46 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_46, o4]
  done

theorem p_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_56, o5]
  done

end FV7z.Arp
