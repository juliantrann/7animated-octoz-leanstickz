import FV7z.C103.Cuts
import FV7z.Lemmas.BlkOps21
/-! Goal shapes of the pieces of `init_cacheinfo` after `wpx` (triage only, not imported). -/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
set_option linter.unusedSimpArgs false

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3504 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3504, W_3537, W_3546, W_3562, W_3732, W_3744, W_4035, W_3746, o0, o1, o2, o3, o14, o15, o43, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3566 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3566, o4, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3569 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3569, W_3574, o5, o6, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3617 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3617, o7, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3629 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3629, o8, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3632 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3632, W_3637, o9, o10, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3680 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3680, W_3692, o11, o12, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3710 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3710, o13, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3763 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3763, o16, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3776 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3776, o17, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3789 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3789, W_3801, W_3934, o18, o19, o32, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3809 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3809, W_3822, W_3828, W_4241, W_3951, o20, o21, o22, o33, o63, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3841 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3841, o23, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3858 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3858, o24, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3867 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3867, W_3871, W_3888, W_3893, W_3899, W_4163, W_4173, o25, o26, o27, o28, o29, o56, o57, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3921 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3921, W_4254, W_4264, W_4295, o30, o64, o65, o66, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3929 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3929, o31, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3960 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3960, o34, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3967 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3967, W_3972, W_3976, o9, o35, o36, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3984 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3984, o8, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_3987 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3987, W_3992, W_3997, o37, o38, o39, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4008 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4008, o40, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4011 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4011, o41, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4014 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4014, W_4030, o42, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4045 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4045, o16, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4058 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4058, o44, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4071 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4071, o45, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4081 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4081, W_4088, W_4095, W_4192, o46, o47, o48, o58, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4102 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4102, W_4112, o49, o50, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4125, o51, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4128, W_4136, o52, o53, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4143 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4143, W_4231, W_4239, o54, o62, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4148 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4148, o55, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4199 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4199, o59, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4216 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4216, o60, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4226 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4226, o61, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4306 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4306, o67, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4329 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4329, o69, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4332 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4332, W_4337, o70, o71, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4348 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4348, W_4362, W_4366, W_4374, W_4321, W_4435, W_4441, o68, o72, o73, o74, o75, o80, o81, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4384 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4384, o76, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4409 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4409, W_4421, W_4427, W_4478, W_4484, W_4492, o35, o77, o78, o79, o84, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4457 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4457, o82, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4469 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4469, o83, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4502 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4502, W_4519, W_4532, W_4541, W_4553, W_4580, W_4589, o37, o85, o86, o87, o88, o89, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4570 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4570, o90, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

example (F : Footprint) (Wl : List Rgn) (Q : Post) (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    W_4598 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_4598, o91, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  trace_state
  sorry

end FV7z.C103
