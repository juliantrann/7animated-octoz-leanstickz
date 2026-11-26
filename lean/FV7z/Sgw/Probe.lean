import FV7z.Sgw.Cuts
import FV7z.Close.Holds
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Sgw
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 20 ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_12, o0, o1]
  trace_state
  sorry

end FV7z.Sgw
