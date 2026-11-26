import FV7z.Onc.Cuts
import FV7z.Write.Holds
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Onc

example {F : Footprint} {Wl : List Rgn} {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (P : Gprs → (Addr → Byte) → Prop) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 74 ∧ P g' V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_44, W_58, o0, o1, o2, Op.ldf]
  trace_state
  sorry

example {F : Footprint} {Wl : List Rgn} {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (P : Gprs → (Addr → Byte) → Prop) :
    W_76 fb F Wl (fun j' g' _ V' => j' = 84 ∧ P g' V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_76, W_152, o3, o6, Op.stf, Write.ja_cmp]
  trace_state
  sorry

example {F : Footprint} {Wl : List Rgn} {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (P : Gprs → (Addr → Byte) → Prop) :
    W_84 fb F Wl (fun j' g' _ V' => j' = 104 ∧ P g' V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_84, W_100, o4, o5, Op.xormf]
  trace_state
  sorry

end FV7z.Onc
