import FV7z.Fre.Cuts
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fre
variable {F : Footprint} {Wl : List Rgn}

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfk : rdq(V, 8013160#64) = 0#64) (h0 : g.rdi = 0#64) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 148 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0
  subst h0
  wpx [W_0, W_24, W_144, o0, o1, o11, Op.lda, BitVec.and_self, hfk, BitVec.sub_add_cancel]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfk : rdq(V, 8013160#64) = 0#64) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 86 ∧ (∃ a, g' = { g with rax := a, rsi := g.rdi + 18446744073709551600#64,
      rdi := 7940672#64, rdx := 0#64 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_24, W_29, W_41, o0, o1, o2, o3, Op.lda, Op.cmpmif, BitVec.and_self, hfk, BitVec.sub_add_cancel]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_57 fb F Wl (fun j' g' _ V' => j' = 86 ∧ (∃ a, g' = { g with rdi := 7940672#64, rdx := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_57, W_68, W_80, o4, o5, o6, BitVec.and_self, BitVec.xor_self]
  trace_state
  sorry

end FV7z.Fre
