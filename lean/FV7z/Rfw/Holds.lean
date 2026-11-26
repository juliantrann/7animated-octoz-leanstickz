import FV7z.Rfw.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-! Probe: the goals after `wpx` (to be replaced). -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rfw

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_11, o0, o1, BitVec.and_self]
  done

theorem p_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_29, W_24, W_37, o3, o2, o4, Op.cmpmr]
  done

theorem p_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_48, o5]
  done

end FV7z.Rfw
