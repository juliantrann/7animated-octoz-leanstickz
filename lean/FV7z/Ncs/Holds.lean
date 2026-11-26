import FV7z.Ncs.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-! Probe: the goals after `wpx` (to be replaced). -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ncs

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_74, W_11, o0, o7, o1, BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero]
  done

theorem p_47 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_47 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_47, W_32, W_64, W_38, o4, o2, o6, o3, BitVec.and_self]
  done

theorem p_60 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_60 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_60, o5]
  done

end FV7z.Ncs
