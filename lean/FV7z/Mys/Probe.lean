import FV7z.Fcp.Cuts
import FV7z.Fcw.Cuts
import FV7z.Lwa.Cuts
import FV7z.Lww.Cuts
import FV7z.Sea.Cuts
import FV7z.Rfp.Cuts
import FV7z.Tun.Inv
/-! Probe: the goals of `wpx` at each cut point, with `Q` opaque. -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Mys.Probe
set_option maxHeartbeats 400000

theorem fcp_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Fcp.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Fcp.W_0, Fcp.W_17, Fcp.W_51, Fcp.o0, Fcp.o1, Fcp.o2, Fcp.o3, Fcp.o4, Fcp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem fcp_36 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Fcp.W_36 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Fcp.W_36, Fcp.W_24, Fcp.W_48, Fcp.W_40, Fcp.o0, Fcp.o1, Fcp.o2, Fcp.o3, Fcp.o4, Fcp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem fcw_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Fcw.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Fcw.W_0, Fcw.W_13, Fcw.W_48, Fcw.o0, Fcw.o1, Fcw.o2, Fcw.o3, Fcw.o4, Fcw.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem fcw_27 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Fcw.W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Fcw.W_27, Fcw.W_16, Fcw.W_40, Fcw.W_31, Fcw.o0, Fcw.o1, Fcw.o2, Fcw.o3, Fcw.o4, Fcw.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem lwa_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Lwa.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Lwa.W_0, Lwa.o0, Lwa.o1, Lwa.o2,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem lwa_35 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Lwa.W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Lwa.W_35, Lwa.W_16, Lwa.o0, Lwa.o1, Lwa.o2,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem lww_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Lww.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Lww.W_0, Lww.o0, Lww.o1, Lww.o2,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem lww_35 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Lww.W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Lww.W_35, Lww.W_16, Lww.o0, Lww.o1, Lww.o2,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem sea_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Sea.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Sea.W_0, Sea.W_13, Sea.o0, Sea.o1, Sea.o2, Sea.o3, Sea.o4,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem sea_40 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Sea.W_40 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Sea.W_40, Sea.W_24, Sea.W_44, Sea.o0, Sea.o1, Sea.o2, Sea.o3, Sea.o4,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem sea_56 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Sea.W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Sea.W_56, Sea.o0, Sea.o1, Sea.o2, Sea.o3, Sea.o4,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem rfp_0 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Rfp.W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Rfp.W_0, Rfp.W_11, Rfp.W_24, Rfp.o0, Rfp.o1, Rfp.o2, Rfp.o3, Rfp.o4, Rfp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem rfp_41 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Rfp.W_41 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Rfp.W_41, Rfp.W_32, Rfp.o0, Rfp.o1, Rfp.o2, Rfp.o3, Rfp.o4, Rfp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem rfp_46 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Rfp.W_46 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Rfp.W_46, Rfp.o0, Rfp.o1, Rfp.o2, Rfp.o3, Rfp.o4, Rfp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

theorem rfp_56 {F : Footprint} {Wl : List Rgn} {Q : Nat → Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte} : Rfp.W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Rfp.W_56, Rfp.o0, Rfp.o1, Rfp.o2, Rfp.o3, Rfp.o4, Rfp.o5,
    Op.cmpmi, Op.sar64, Op.st, Tun.rd1]
  done

end FV7z.Mys.Probe
