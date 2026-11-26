import FV7z.Fcc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps17
/-! Probe. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fcc

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_17, W_51, o0, o5]
  done

theorem p_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_36 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_36, W_24, W_48, W_40, o2, o1, o4, o3]
  done

end FV7z.Fcc
