import FV7z.Ftn.Cuts
import FV7z.Lemmas.BlkOps17
/-! Triage probe (to be removed): the goal `wpx` leaves for `W_25`. -/
namespace FV7z.Ftn
open ZellicX86 Decode FV7z.Leaf

theorem pr25 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, o1, Op.mul64, mulp, Op.shr64, Op.shl64]
  done

end FV7z.Ftn
