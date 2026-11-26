import FV7z.Ifr.Cuts
import FV7z.Tun.Inv
/-! Probe: the goals of `_int_free`'s pieces after `wpx` (removed once the proofs are in). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Ifr
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_59, W_72, W_82, o0, o1, o2, o3, Op.ldf, BitVec.and_self, Bool.false_eq_true, false_implies]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop) :
    W_90 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_90, W_107, W_124, W_139, o4, o5, o6, o7, Op.ldf, Op.cmpmra, Op.cmpma, BitVec.and_self]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop) :
    W_696 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_696, o10]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop) :
    W_307 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_307, W_327, o8, o9, Op.xormf]
  trace_state
  sorry

end FV7z.Ifr
