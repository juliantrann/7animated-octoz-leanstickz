import FV7z.Hin.Cuts
import FV7z.Lemmas.BlkOps21
/-! Goal shapes of the pieces of `handle_intel` after `wpx` (triage only, not imported). -/
namespace FV7z.Hin
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
set_option linter.unusedSimpArgs false

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1280 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1280, W_1610, W_1323, o0, o17, o1, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1371 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1371, o3, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1378 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1378, W_1393, o4, o5, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1403 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1403, o6, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1427 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1427, W_1436, o7, o8, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1462 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1462, W_1467, o7, o9, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1494 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1494, W_1499, o7, o10, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1527 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1527, W_1532, W_1368, W_1547, W_1600, W_1558, o7, o11, o2, o12, o16, o13, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

example (fb : Addr) (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_1568 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1568, W_1584, o14, o15, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.xor8, Op.ldf]
  trace_state
  sorry

end FV7z.Hin
