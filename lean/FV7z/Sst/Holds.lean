import FV7z.Sst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps7
/-! Probe. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sst

variable {F : Footprint} {Wl : List Rgn}

theorem p_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_25, o0, o1]
  done

theorem p_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_29, o2, Op.vl, Op.vs]
  done

end FV7z.Sst
