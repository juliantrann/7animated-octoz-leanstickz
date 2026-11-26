import FV7z.Rpp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-! Probe: the goals after `wpx` (to be replaced). -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rpp

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  done

theorem p_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, W_16, W_40, W_30, o2, o1, o4, o3, Op.cmpmi]
  done

end FV7z.Rpp
