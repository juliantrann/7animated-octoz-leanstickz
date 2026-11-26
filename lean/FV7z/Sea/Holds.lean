import FV7z.Sea.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps17
/-! Probe. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sea

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_13, o0, o1]
  done

theorem p_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_40 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_40, W_24, W_44, o3, o2, o4]
  done

theorem p_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_56, o1]
  done

end FV7z.Sea
