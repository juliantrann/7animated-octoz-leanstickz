import FV7z.Fxs.Cuts
import FV7z.Close.Holds
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fxs

variable {F : Footprint} {Wl : List Rgn}

theorem probe_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 23 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_18, W_64, o0, o1, o4, Op.stfi]
  trace_state
  sorry

end FV7z.Fxs
