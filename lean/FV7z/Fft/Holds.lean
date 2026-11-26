import FV7z.Fft.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps17
/-! Probe. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fft

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  done

theorem p_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, o1, Op.mul64, Op.mulp, Op.shr64, Op.shl64]
  done

end FV7z.Fft
