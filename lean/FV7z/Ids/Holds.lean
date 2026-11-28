import FV7z.Ids.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NWindows::NFile::NFind::CDirEntry::IsDots ()` (PLAN.md §M, M1)

Work in progress (a triage probe of the goal after `wpx`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ids

variable {F : Footprint} {Wl : List Rgn}

theorem probe {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_12, W_32, W_41, W_51, o0, o1, o2, o3, o4, Op.cmpmi, Op.testmi, Op.setcc]
  trace_state
  sorry

end FV7z.Ids
