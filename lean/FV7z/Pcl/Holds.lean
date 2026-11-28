import FV7z.Pcl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps16
/-! Probe (triage only): the goals `wpx` leaves for the pieces of `PropVariant_Clear`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pcl

variable {F : Footprint} {Wl : List Rgn}

theorem probe_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_17, W_26, o0, o1, o2, Op.bt64]
  done

theorem probe_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_50, W_54, o4, o5, Op.cmpmi]
  done

theorem probe_67 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_67 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_67, o8, BitVec.xor_self, BitVec.setWidth_zero]
  done

end FV7z.Pcl
