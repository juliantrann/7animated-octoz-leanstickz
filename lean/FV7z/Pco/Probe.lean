import FV7z.Pco.Cuts
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pco
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 31 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_21, o0, o1, Op.ld, Op.stf, BitVec.and_self]
  trace_state
  sorry

end FV7z.Pco
