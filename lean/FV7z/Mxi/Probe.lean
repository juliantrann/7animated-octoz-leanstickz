import FV7z.Mxi.Cuts
import FV7z.Mxs.Cuts
/-! Probe: the goals after `wpx` from the entries of `__pthread_mutex_init` and `CriticalSection_Init`. -/
namespace FV7z.Mxi
open ZellicX86 Decode FV7z FV7z.Leaf

variable {F : Footprint} {Wl : List Rgn}

theorem q0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_240, W_134, W_140, W_160, o0, o1, o2, o3, o4, Op.ldf, Op.xormf, BitVec.xor_self]
  done

theorem s0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post) : Mxs.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Mxs.W_0, Mxs.W_9, Mxs.o0, Mxs.o1]
  done

end FV7z.Mxi
