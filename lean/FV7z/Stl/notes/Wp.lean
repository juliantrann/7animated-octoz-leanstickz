/-
Weakest preconditions of the cut points of `____strtoul_l_internal`, as printed by `trace_state` after `wpx`
(not built; kept for writing `Stl/Vc1.lean` and `Stl/Vc2.lean`). Section `pr_i` is the i-th cut point in the order
0, 80, 99, 133, 150, 171, 216, 223, 265, 291, 296, 332, 345, 368, 390, 432, 448, 604, 745, 748, 790, 927.
In this compact form the long `Gprs` record literal is shortened to `G` where it is unchanged; lines are wrapped
at 120 columns.

The probe that printed them (`Stl/Probe.lean`, removed; one `example` per cut point):

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_0, Stl.W_40, Stl.W_49, Stl.W_58, Stl.o0, Stl.o1, Stl.o2, Stl.o3, Op.ldsxq, Op.ldzx, Op.lda, Op.lea,
    Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_80 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_80, Stl.o4, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_99 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_99, Stl.W_107, Stl.W_116, Stl.W_496, Stl.W_672, Stl.W_969, Stl.W_981, Stl.o5, Stl.o6, Stl.o7, Stl.o38,
    Stl.o41, Stl.o43, Stl.o52, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa,
    Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_133 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_133, Stl.W_142, Stl.W_464, Stl.W_473, Stl.W_592, Stl.W_808, Stl.W_827, Stl.W_835, Stl.W_881, Stl.o8,
    Stl.o9, Stl.o36, Stl.o37, Stl.o39, Stl.o47, Stl.o48, Stl.o49, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_150 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_150, Stl.W_159, Stl.o10, Stl.o11, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_171 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_171, Stl.W_207, Stl.o12, Stl.o13, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_216 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_216, Stl.o14, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_223 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_223, Stl.o15, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_265 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_265, Stl.W_279, Stl.o17, Stl.o18, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_291 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_291, Stl.o19, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_296 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_296, Stl.W_305, Stl.W_314, Stl.W_317, Stl.W_325, Stl.o20, Stl.o21, Stl.o22, Stl.o23, Stl.o24, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64,
    Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_332 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_332, Stl.W_340, Stl.W_256, Stl.W_258, Stl.o16, Stl.o25, Stl.o26, Op.ldsxq, Op.ldzx, Op.lda, Op.lea,
    Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_345 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_345, Stl.W_366, Stl.o27, Stl.o28, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi,
    Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_368 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_368, Stl.W_377, Stl.W_387, Stl.o29, Stl.o30, Stl.o31, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_390 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_390, Stl.W_399, Stl.W_1194, Stl.o32, Stl.o33, Stl.o54, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_432 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_432, Stl.o34, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_448 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_448, Stl.o35, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_604 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_604, Stl.W_613, Stl.W_934, Stl.W_939, Stl.o10, Stl.o36, Stl.o40, Stl.o53, Op.ldsxq, Op.ldzx, Op.lda,
    Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_745 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_745, Stl.o42, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_748 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_748, Stl.W_760, Stl.W_772, Stl.W_909, Stl.W_915, Stl.o43, Stl.o44, Stl.o45, Stl.o50, Stl.o51, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe, Op.sxr, Op.neg, Op.imul64,
    Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_790 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_790, Stl.o46, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} :
    Stl.W_927 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Stl.W_927, Stl.o52, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64]
  trace_state
  sorry

end FV7z.ProbeStl


=== pr_1 (cut 0)
⊢ (∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8 - 8) i)) ∧
∀ (af : Bool), (∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8 - 8 - 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8) i)) ∧
∀ (af_1 : Bool), (∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8 - 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl ((rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64).add i)) ∧
∀ (af_2 : Bool), ((!setWidth 32 rcx &&& setWidth 32 rcx == 0) = true →
Q 696 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64, rbp := rbp, rsi :=
  rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := setWidth 64 (setWidth 32 r12 ^^^ setWidth 32 r12),
  r13 := rdi, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst (Vst (Vst (Vst (Vst (Vst (Vst
  V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8
  - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))
  (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8))) ∧
((!setWidth 32 rcx &&& setWidth 32 rcx == 0) = false →
(decide (setWidth 32 rdx = 1#32) = true →
Q 432 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64, rbp := rbp, rsi :=
  rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := setWidth 64 (setWidth 32 r12 ^^^ setWidth 32 r12),
  r13 := rdi, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst (Vst (Vst (Vst (Vst (Vst (Vst
  V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8
  - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))
  (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8))) ∧
(decide (setWidth 32 rdx = 1#32) = false →
((!(decide ((setWidth 32 rdx).toNat < 36) || decide (setWidth 32 rdx = 36#32))) = true →
Q 432 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64, rbp := rbp, rsi :=
  rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := setWidth 64 (setWidth 32 r12 ^^^ setWidth 32 r12),
  r13 := rdi, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst (Vst (Vst (Vst (Vst (Vst (Vst
  V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8
  - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))
  (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8))) ∧
((!(decide ((setWidth 32 rdx).toNat < 36) || decide (setWidth 32 rdx = 36#32))) = false →
(∀ (i : Nat), i < 1 →
Foot F.data (Addr.add rdi i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data ((r8 + 104#64).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot F.data ((ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8)
  (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8
  - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64)
  (toBytesLE rsi 8)) (byteAddrs (r8 + 104#64) 8)) + signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst
  (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8
  - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx
  8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))) * 2#64 + 1#64).add i)) ∧
∀ (af_3 : Bool), ((ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8)
  (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8
  - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64)
  (toBytesLE rsi 8)) (byteAddrs (ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15
  8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
  (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8
  - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs (r8 + 104#64) 8)) + signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst
  (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE
  r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8
  - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))) * 2#64 +
  1#64) 1)) &&& 32#8 == 0) = true →
Q 99 { rax := signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8))
  (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp -
  8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 -
  40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))), rcx := signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst
  (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8))
  (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8)
  (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))), rdx := rdx,
  rbx := rdi, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64, rbp := rbp, rsi := ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst
  (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8))
  (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8)
  (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs (r8 + 104#64) 8)), rdi
  := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := setWidth 64 (setWidth 32 r12 ^^^ setWidth 32 r12), r13 :=
  rdi, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp
  - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8)
  (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp
  - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8))) ∧
((ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14
  8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE
  rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi
  8)) (byteAddrs (ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8)
  (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8
  - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64)
  (toBytesLE rsi 8)) (byteAddrs (r8 + 104#64) 8)) + signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst
  (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8
  - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx
  8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))) * 2#64 + 1#64) 1)) &&& 32#8 ==
  0) = false →
Q 80 { rax := signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8))
  (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp -
  8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 -
  40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))), rcx := signExtend 64 (ofBytesLE 8 (List.map (Vst (Vst (Vst (Vst
  (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8))
  (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8)
  (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs rdi 1))), rdx := rdx,
  rbx := rdi, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64, rbp := rbp, rsi := ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst
  (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8))
  (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8)
  (toBytesLE rbx 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8)) (byteAddrs (r8 + 104#64) 8)), rdi
  := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := setWidth 64 (setWidth 32 r12 ^^^ setWidth 32 r12), r13 :=
  rdi, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (rsp
  - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8)) (rsp - 8 - 8 - 8) (toBytesLE r13 8)) (rsp - 8 - 8 - 8 - 8)
  (toBytesLE r12 8)) (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8)) (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8)) (rsp
  - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 + 8#64) (toBytesLE rsi 8))))))
=== pr_2 (cut 80)
⊢ (∀ (i : Nat), i < 1 →
Foot F.data ((rbx + 1#64).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot F.data ((rsi + signExtend 64 (B( (rbx + 1#64) 1))) * 2#64 + 1#64).add i)) ∧
∀ (af : Bool), ((!B( (rsi + signExtend 64 (B( (rbx + 1#64) 1))) * 2#64 + 1#64) 1)) &&& 32#8 == 0) = true →
Q 80 { rax := signExtend 64 (B( (rbx + 1#64) 1))), rcx := signExtend 64 (B( (rbx + 1#64) 1))), rdx := rdx, rbx := rbx +
  1#64, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }  V) ∧
((!B( (rsi + signExtend 64 (B( (rbx + 1#64) 1))) * 2#64 + 1#64) 1)) &&& 32#8 == 0) = false →
Q 99 { rax := signExtend 64 (B( (rbx + 1#64) 1))), rcx := signExtend 64 (B( (rbx + 1#64) 1))), rdx := rdx, rbx := rbx +
  1#64, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }  V)
=== pr_3 (cut 99)
⊢ ∀ (af : Bool), ((setWidth 8 rcx &&& setWidth 8 rcx == 0) = true →
(∀ (i : Nat), i < 8 →
Foot F.data ((rsp + 8#64).add i)) ∧
((!decide (Q8( (rsp + 8#64) 8)) = 0#64)) = true →
Q 790 G  V) ∧
((!decide (Q8( (rsp + 8#64) 8)) = 0#64)) = false →
∀ (af_1 : Bool), Q 448 { rax := setWidth 64 (setWidth 32 rax ^^^ setWidth 32 rax), rcx := rcx, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V)) ∧
((setWidth 8 rcx &&& setWidth 8 rcx == 0) = false →
(decide (setWidth 8 rcx = 45#8) = true →
(∀ (i : Nat), i < 1 →
Foot F.data ((rbx + 1#64).add i)) ∧
(∀ (i : Nat), i < 4 →
Foot Wl ((rsp + 20#64).add i)) ∧
Q 133 { rax := rax, rcx := setWidth 64 (setWidth 32 (B( (rbx + 1#64) 1)))), rdx := rdx, rbx := rbx + 1#64, rsp := rsp,
  rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14,
  r15 := r15 }  (Vst V (rsp + 20#64) (toBytesLE (1#32) 4))) ∧
(decide (setWidth 8 rcx = 45#8) = false →
(∀ (i : Nat), i < 4 →
Foot Wl ((rsp + 20#64).add i)) ∧
(decide (setWidth 8 rcx = 43#8) = true →
(∀ (i : Nat), i < 1 →
Foot F.data ((rbx + 1#64).add i)) ∧
Q 133 { rax := rax, rcx := setWidth 64 (setWidth 32 (ofBytesLE 8 (List.map (Vst V (rsp + 20#64) (toBytesLE (0#32) 4))
  (byteAddrs (rbx + 1#64) 1)))), rdx := rdx, rbx := rbx + 1#64, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (rsp + 20#64)
  (toBytesLE (0#32) 4))) ∧
(decide (setWidth 8 rcx = 43#8) = false →
Q 133 G  (Vst V (rsp + 20#64) (toBytesLE (0#32) 4))))) 
=== pr_4 (cut 133)
⊢ (decide (setWidth 8 rcx = 48#8) = true →
∀ (af : Bool), ((setWidth 32 rdx &&& 4294967279#32 == 0) = true →
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7935192#64) i)) ∧
(∀ (i : Nat), i < 1 →
Foot F.data ((rbx + 1#64).add i)) ∧
(∀ (i : Nat), i < 4 →
Foot F.data ((Q8( (7935192#64) 8)) + signExtend 64 (B( (rbx + 1#64) 1))) * 4#64).add i)) ∧
(decide (ofBytesLE 32 (MV( (Q8( (7935192#64) 8)) + signExtend 64 (B( (rbx + 1#64) 1))) * 4#64) 4)) = 88#32) = true →
(∀ (i : Nat), i < 1 →
Foot F.data ((rbx + 2#64).add i)) ∧
∀ (af_1 af_2 : Bool), Q 171 { rax := setWidth 64 14#32, rcx := setWidth 64 (setWidth 32 (B( (rbx + 2#64) 1)))), rdx :=
  setWidth 64 16#32, rbx := rbx + 2#64, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi :=
  rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := Q8( (7935192#64) 8)), r11 := r11, r12 := r12, r13 := r13, r14 := setWidth
  64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  V) ∧
(decide (ofBytesLE 32 (MV( (Q8( (7935192#64) 8)) + signExtend 64 (B( (rbx + 1#64) 1))) * 4#64) 4)) = 88#32) = false →
∀ (af_1 : Bool), ((!setWidth 32 rdx &&& setWidth 32 rdx == 0) = true →
Q 604 { rax := signExtend 64 (B( (rbx + 1#64) 1))), rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi :=
  rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := Q8( (7935192#64) 8)), r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15
  := r15 }  V) ∧
((!setWidth 32 rdx &&& setWidth 32 rdx == 0) = false →
∀ (af_2 af_3 : Bool), (∀ (i : Nat), i < 1 →
Foot F.data (Addr.add (7353702#64) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7353808#64) i)) ∧
(∀ (i : Nat), i < 1 →
Foot Wl ((rsp + 18#64).add i)) ∧
Q 223 { rax := setWidth 64 (setWidth 32 (B( (7353702#64) 1)))), rcx := setWidth 64 48#32, rdx := setWidth 64 8#32, rbx
  := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := Q8(
  (7353808#64) 8)), r9 := r9, r10 := Q8( (7935192#64) 8)), r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64
  (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }  (Vst V (rsp + 18#64) (toBytesLE (setWidth 8 (setWidth 32 (B(
  (7353702#64) 1))))) 1))))) ∧
((setWidth 32 rdx &&& 4294967279#32 == 0) = false →
Q 604 G  V)) ∧
(decide (setWidth 8 rcx = 48#8) = false →
∀ (af : Bool), ((!setWidth 32 rdx &&& setWidth 32 rdx == 0) = true →
(decide (setWidth 32 rdx = 10#32) = true →
Q 150 G  V) ∧
(decide (setWidth 32 rdx = 10#32) = false →
∀ (af_1 af_2 : Bool), Q 171 { rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := rcx, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }  V)) ∧
((!setWidth 32 rdx &&& setWidth 32 rdx == 0) = false →
Q 150 G  V)) 
=== pr_5 (cut 150)
⊢ ∀ (af : Bool), ((!r14 &&& r14 == 0) = true →
Q 992 G  V) ∧
((!r14 &&& r14 == 0) = false →
∀ (af_1 : Bool), Q 171 { rax := setWidth 64 8#32, rcx := rcx, rdx := setWidth 64 10#32, rbx := rbx, rsp := rsp, rbp :=
  setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11,
  r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V)
=== pr_6 (cut 171)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data ((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot F.data ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot Wl (((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 4) + 18#64).add
  i)) ∧
∀ (af : ⋯), ((setWidth 8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8(
  (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0)
  (setWidth 64 (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8)
  (Q8( (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) +
  ((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf
  6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1)) &&&
  setWidth 8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1)) == 0) = true →
Q 745 (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))) (rfz ((rfz f).arith (setWidth
  8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend
  64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set
  (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32
  (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1)) &&& setWidth 8
  ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend
  64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set
  (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32
  (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1))) false false
  af)) (Vst V ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 4) + 18#64)
  (toBytesLE (setWidth 8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8(
  (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0)
  (setWidth 64 (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8)
  (Q8( (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) +
  ((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf
  6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 0))) 1))) ∧
(⋯ →
(⋯ →
Q 745 (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))) (rfz (subF (rfz ((rfz
  f).arith (setWidth 8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8(
  (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0)
  (setWidth 64 (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8)
  (Q8( (((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) +
  ((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64
  (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf
  6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1)) &&&
  setWidth 8 ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 1))) false false
  af)) ((((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64
  (setWidth 32 (B( (((((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set
  0 (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 6) + ((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).get (regOf 0)) 1)))))).get (regOf 14)) ((((((G.set 0
  (signExtend 64 (setWidth 32 rax))).set (regOf 6) 7353760#64).set (regOf 8) (Q8( (((G.set 0 (signExtend 64 (setWidth 32
  rax))).set (regOf 6) 7353760#64).get (regOf 6) + ((G.set 0 (signExtend 64 (setWidth 32 rax))).set (regOf 6)
  7353760#64).get (regOf 0) * 8#64) 8)))).set (regOf 6) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32 (B( ((((({
  rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9,
  r10 := r10, r11 := r11, r12 := ⋯, r13 := ⋯, r14 := ⋯, r15 := ⋯ }.set ⋯ ⋯).set ⋯ ⋯).set ⋯ ⋯).set ⋯ ⋯).get ⋯ + ⋯)
  ⋯)))))).get ⋯))) ⋯) ∧
⋯) 
=== pr_7 (cut 216)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7935192#64) i)) ∧
Q 223 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := Q8( (7935192#64) 8)), r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V
=== pr_8 (cut 223)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7935176#64) i)) ∧
∀ (af : Bool), (∀ (i : Nat), i < 8 →
Foot Wl ((rsp + 24#64).add i)) ∧
∀ (af_1 : Bool), Q 296 { rax := setWidth 64 (setWidth 32 rax ^^^ setWidth 32 rax), rcx := rcx, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := rbp, rsi := rbp + 18446744073709551615#64, rdi := rbx, r8 := r8, r9 := setWidth 64 (setWidth 32 r9
  ^^^ setWidth 32 r9), r10 := r10, r11 := Q8( (7935176#64) 8)), r12 := r12, r13 := r13, r14 := r14, r15 := signExtend 64
  (setWidth 32 rdx) }  (Vst V (rsp + 24#64) (toBytesLE (rbp + 18446744073709551615#64) 8))
=== pr_9 (cut 265)
⊢ ∀ (fl : Rflags), (∀ (i : Nat), i < 1 →
Foot F.data ((rdi + 1#64).add i)) ∧
∀ (af : Bool), ((setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) &&& setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) == 0)
  = true →
Q 368 { rax := setWidth 64 (signExtend 128 rax * signExtend 128 r15) + setWidth 64 (setWidth 32 (setWidth 8 rsi)), rcx
  := setWidth 64 (setWidth 32 (B( (rdi + 1#64) 1)))), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := setWidth 64
  (setWidth 32 (setWidth 8 rsi)), rdi := rdi + 1#64, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V) ∧
((setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) &&& setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) == 0) = false →
Q 291 { rax := setWidth 64 (signExtend 128 rax * signExtend 128 r15) + setWidth 64 (setWidth 32 (setWidth 8 rsi)), rcx
  := setWidth 64 (setWidth 32 (B( (rdi + 1#64) 1)))), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := setWidth 64
  (setWidth 32 (setWidth 8 rsi)), rdi := rdi + 1#64, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V)
=== pr_10 (cut 291)
⊢ (decide (rdi = r14) = true →
Q 368 G  V) ∧
(decide (rdi = r14) = false →
Q 296 G  V) 
=== pr_11 (cut 296)
⊢ ((decide ((setWidth 8 (setWidth 32 (rcx + 18446744073709551568#64))).toNat < 9) || decide (setWidth 8 (setWidth 32
  (rcx + 18446744073709551568#64)) = 9#8)) = true →
Q 332 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := setWidth 64 (setWidth 32 (rcx +
  18446744073709551568#64)), rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14,
  r15 := r15 }  V) ∧
((decide ((setWidth 8 (setWidth 32 (rcx + 18446744073709551568#64))).toNat < 9) || decide (setWidth 8 (setWidth 32 (rcx
  + 18446744073709551568#64)) = 9#8)) = false →
∀ (af : Bool), ((!rbp &&& rbp == 0) = true →
Q 512 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := setWidth 64 (setWidth 32 (rcx +
  18446744073709551568#64)), rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14,
  r15 := r15 }  V) ∧
((!rbp &&& rbp == 0) = false →
(∀ (i : Nat), i < 1 →
Foot F.data ((r11 + setWidth 64 (setWidth 32 (setWidth 8 rcx)) * 2#64 + 1#64).add i)) ∧
∀ (af_1 : Bool), ((B( (r11 + setWidth 64 (setWidth 32 (setWidth 8 rcx)) * 2#64 + 1#64) 1)) &&& 4#8 == 0) = true →
Q 368 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rcx)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := setWidth 64 (setWidth 32 (rcx + 18446744073709551568#64)), rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V) ∧
((B( (r11 + setWidth 64 (setWidth 32 (setWidth 8 rcx)) * 2#64 + 1#64) 1)) &&& 4#8 == 0) = false →
(∀ (i : Nat), i < 4 →
Foot F.data ((r10 + setWidth 64 (setWidth 32 (setWidth 8 rcx)) * 4#64).add i)) ∧
Q 332 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rcx)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := setWidth 64 (ofBytesLE 32 (MV( (r10 + setWidth 64 (setWidth 32 (setWidth 8 rcx)) * 4#64) 4)) - 55#32), rdi :=
  rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V)))
=== pr_12 (cut 332)
⊢ ((subF (rfz f) (setWidth 32 (setWidth 8 rsi)) (setWidth 32 rdx)).cond 13 = true →
Q 368 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rsi)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
  V) ∧
((subF (rfz f) (setWidth 32 (setWidth 8 rsi)) (setWidth 32 rdx)).cond 13 = false →
((!decide (r8.toNat < rax.toNat)) = true →
((!decide (r8 = rax)) = true →
Q 265 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rsi)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
  V) ∧
((!decide (r8 = rax)) = false →
(∀ (i : Nat), i < 1 →
Foot F.data ((rsp + 18#64).add i)) ∧
((!(decide ((setWidth 8 rsi).toNat < (B( (rsp + 18#64) 1))).toNat) || decide (setWidth 8 rsi = B( (rsp + 18#64) 1))))) =
  true →
Q 345 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rsi)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
  V) ∧
((!(decide ((setWidth 8 rsi).toNat < (B( (rsp + 18#64) 1))).toNat) || decide (setWidth 8 rsi = B( (rsp + 18#64) 1))))) =
  false →
Q 265 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rsi)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
  V))) ∧
((!decide (r8.toNat < rax.toNat)) = false →
Q 345 { rax := rax, rcx := setWidth 64 (setWidth 32 (setWidth 8 rsi)), rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
  rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
  V))
=== pr_13 (cut 345)
⊢ (∀ (i : Nat), i < 1 →
Foot F.data ((rdi + 1#64).add i)) ∧
∀ (af : Bool), ((!setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) &&& setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) ==
  0) = true →
Q 291 { rax := rax, rcx := setWidth 64 (setWidth 32 (B( (rdi + 1#64) 1)))), rdx := rdx, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi + 1#64, r8 := r8, r9 := setWidth 64 1#32, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V) ∧
((!setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) &&& setWidth 8 (setWidth 32 (B( (rdi + 1#64) 1)))) == 0) = false →
Q 368 { rax := rax, rcx := setWidth 64 (setWidth 32 (B( (rdi + 1#64) 1)))), rdx := rdx, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi + 1#64, r8 := r8, r9 := setWidth 64 1#32, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V)
=== pr_14 (cut 368)
⊢ (decide (rbx = rdi) = true →
Q 748 G  V) ∧
(decide (rbx = rdi) = false →
(∀ (i : Nat), i < 8 →
Foot F.data ((rsp + 8#64).add i)) ∧
∀ (af : Bool), ((Q8( (rsp + 8#64) 8)) &&& Q8( (rsp + 8#64) 8)) == 0) = true →
Q 390 { rax := rax, rcx := rcx, rdx := rdx, rbx := Q8( (rsp + 8#64) 8)), rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
  r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V) ∧
((Q8( (rsp + 8#64) 8)) &&& Q8( (rsp + 8#64) 8)) == 0) = false →
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (Q8( (rsp + 8#64) 8))) i)) ∧
Q 390 { rax := rax, rcx := rcx, rdx := rdx, rbx := Q8( (rsp + 8#64) 8)), rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
  r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (Q8( (rsp + 8#64)
  8))) (toBytesLE rdi 8))))
=== pr_15 (cut 390)
⊢ ∀ (af : ⋯), ((!setWidth 32 r9 &&& setWidth 32 r9 == 0) = true →
(∀ (i : Nat), i < 4 →
Foot Wl ((fb + 18446744073709551544#64).add i)) ∧
Q 448 { rax := 18446744073709551615#64, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi :=
  rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (fb +
  18446744073709551544#64) (toBytesLE (34#32) 4))) ∧
(⋯ →
(∀ (i : Nat), i < 4 →
Foot F.data ((rsp + 20#64).add i)) ∧
∀ (af_1 : ⋯), (∀ (i : Nat), i < 8 →
Foot F.data (Addr.add ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add ((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if
  (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx
  := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax :=
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get
  (regOf 4) + 40#64)).rsp + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp
  + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&&
  ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp +
  20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32
  (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).rsp
  i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add ((((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if
  (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx
  := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax :=
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get
  (regOf 4) + 40#64)).rsp + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp
  + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&&
  ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp +
  20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32
  (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).set 4
  (((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 -
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else
  { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 :=
  r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE
  32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64)
  4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11
  := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp
  + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp
  + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).rsp + 8)).set (regOf 5) (Q8(
  ((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 -
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else
  { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 :=
  r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE
  32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64)
  4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11
  := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp
  + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp
  + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).rsp 8)))).rsp i)) ∧
(∀ (i : ⋯), ⋯ →
Foot F.data (Addr.add ((((((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if
  (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx
  := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax :=
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get
  (regOf 4) + 40#64)).rsp + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp
  + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&&
  ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp +
  20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32
  (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).set 4
  (((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 -
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else
  { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 :=
  r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE
  32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64)
  4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11
  := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp
  + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp
  + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).rsp + 8)).set (regOf 5) (Q8(
  ((((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 -
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else
  { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 :=
  r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true
  then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE
  32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64)
  4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11
  := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp
  + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp +
  20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE
  32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64
  (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp
  + 8)).set (regOf 3) (Q8( ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) =
  true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp
  := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp +
  20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 -
  rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))),
  rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp 8)))).rsp 8)))).set 4 (((((((if
  (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx
  := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax :=
  rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi
  := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set
  (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax
  := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp :=
  rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 :=
  r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp :=
  rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 :=
  r14, r15 := r15 }).get (regOf 4) + 40#64)).set 4 (((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&& ofBytesLE 32 (MV(
  (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64) 4))), rdx :=
  0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12
  := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp + 20#64)
  4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11
  := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).set (regOf 4) ((if (!ofBytesLE 32 (MV( (rsp + 20#64) 4)) &&&
  ofBytesLE 32 (MV( (rsp + 20#64) 4)) == 0) = true then { rax := 0 - rax, rcx := setWidth 64 (ofBytesLE 32 (MV( (rsp +
  20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 } else { rax := rax, rcx := setWidth 64 (ofBytesLE 32
  (MV( (rsp + 20#64) 4))), rdx := 0 - rax, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }).get (regOf 4) + 40#64)).rsp + 8)).set
  (regOf 3) (ofBytesLE ⋯ ⋯)).set ⋯ ⋯).set ⋯ ⋯).rsp + ⋯)).set ⋯ ⋯).rsp ⋯)) ∧
⋯) 
=== pr_16 (cut 432)
⊢ (∀ (i : Nat), i < 4 →
Foot Wl ((fb + 18446744073709551544#64).add i)) ∧
∀ (af : Bool), Q 448 { rax := setWidth 64 (setWidth 32 18446744073709551544#64 ^^^ setWidth 32 18446744073709551544#64),
  rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10,
  r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (fb + 18446744073709551544#64) (toBytesLE (22#32)
  4))
=== pr_17 (cut 448)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64 + 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64 + 8 + 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64 + 8 + 8 + 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64 + 8 + 8 + 8 + 8) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (rsp + 40#64 + 8 + 8 + 8 + 8 + 8) i)) ∧
Q 462 { rax := rax, rcx := rcx, rdx := rdx, rbx := Q8( (rsp + 40#64) 8)), rsp := rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8,
  rbp := Q8( (rsp + 40#64 + 8) 8)), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := Q8( (rsp
  + 40#64 + 8 + 8) 8)), r13 := Q8( (rsp + 40#64 + 8 + 8 + 8) 8)), r14 := Q8( (rsp + 40#64 + 8 + 8 + 8 + 8) 8)), r15 :=
  Q8( (rsp + 40#64 + 8 + 8 + 8 + 8 + 8) 8)) }  V
=== pr_18 (cut 604)
⊢ (decide (setWidth 32 rdx = 10#32) = true →
∀ (af : Bool), ((!r14 &&& r14 == 0) = true →
Q 992 G  V) ∧
((!r14 &&& r14 == 0) = false →
(∀ (i : Nat), i < 1 →
Foot F.data (Addr.add (7353704#64) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7353824#64) i)) ∧
∀ (af_1 : Bool), (∀ (i : Nat), i < 1 →
Foot Wl ((rsp + 18#64).add i)) ∧
Q 216 { rax := setWidth 64 (setWidth 32 (B( (7353704#64) 1)))), rcx := setWidth 64 48#32, rdx := rdx, rbx := rbx, rsp :=
  rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := Q8( (7353824#64) 8)), r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (rsp + 18#64) (toBytesLE
  (setWidth 8 (setWidth 32 (B( (7353704#64) 1))))) 1)))) ∧
(decide (setWidth 32 rdx = 10#32) = false →
∀ (af af_1 : Bool), (∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7935192#64) i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx
  := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 :=
  r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get
  (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx
  := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 :=
  r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get
  (regOf 0) * 8#64).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot F.data (((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx
  := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 :=
  r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set
  (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64)
  8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx :=
  rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).get (regOf 1) + (((({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth
  64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp :=
  setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11,
  r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64
  (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax :=
  setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp
  := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend
  64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64)
  8)))).set (regOf 1) 7353696#64).get (regOf 0)).add i)) ∧
(∀ (i : Nat), i < 1 →
Foot Wl (((((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx
  := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 :=
  r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 :=
  r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set
  (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64)
  8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx :=
  rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32 (B(
  ((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10
  := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set
  0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8)
  (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10
  := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set
  0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1)
  + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp
  := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0
  (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) *
  8#64) 8)))).set (regOf 1) 7353696#64).get (regOf 1) + (((({ rax := setWidth 64 (setWidth 32 (rdx +
  18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp
  ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14
  := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx +
  18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1)
  7353696#64).get (regOf 0)) 1)))))).set (regOf 1) (setWidth 64 48#32)).get (regOf 4) + 18#64).add i)) ∧
Q 223 (((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx :=
  rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9,
  r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15
  }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set
  (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64)
  8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx :=
  rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32 (B(
  ((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10
  := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set
  0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8)
  (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10
  := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set
  0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1)
  + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp
  := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 :=
  r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0
  (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) *
  8#64) 8)))).set (regOf 1) 7353696#64).get (regOf 1) + (((({ rax := setWidth 64 (setWidth 32 (rdx +
  18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp
  ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14
  := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx +
  18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1)
  7353696#64).get (regOf 0)) 1)))))).set (regOf 1) (setWidth 64 48#32)) (rfz ((rfz ((rfz (subF (rfz f) (setWidth 32 rdx)
  10#32)).arith (setWidth 32 r14 ^^^ setWidth 32 r14) false false af)).arith (setWidth 32 rbp ^^^ setWidth 32 rbp) false
  false af_1)) (Vst V ((((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx
  := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8
  := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx :=
  7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14
  ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10)
  (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx :=
  7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14
  ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10)
  (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32
  (B( ((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx :=
  rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9,
  r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15
  }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set
  (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64)
  8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx :=
  rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).get (regOf 1) + (((({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth
  64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp :=
  setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11,
  r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64
  (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax :=
  setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp
  := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend
  64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64)
  8)))).set (regOf 1) 7353696#64).get (regOf 0)) 1)))))).set (regOf 1) (setWidth 64 48#32)).get (regOf 4) + 18#64)
  (toBytesLE (setWidth 8 ((((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64,
  rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi,
  r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth
  32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx :=
  7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14
  ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10)
  (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx :=
  7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi,
  rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14
  ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10)
  (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).set (regOf 0) (setWidth 64 (setWidth 32
  (B( ((((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx :=
  rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9,
  r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15
  }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set
  (regOf 8) (Q8( ((({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx,
  rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15
  := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64)
  8)))).get (regOf 1) + (({ rax := setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx :=
  rdx, rbx := rbx, rsp := rsp, rbp := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 :=
  r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32
  r14), r15 := r15 }.set 0 (signExtend 64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8(
  (7935192#64) 8)))).get (regOf 0) * 8#64) 8)))).set (regOf 1) 7353696#64).get (regOf 1) + (((({ rax := setWidth 64
  (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := setWidth
  64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 :=
  r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64 (setWidth
  32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).set (regOf 8) (Q8( ((({ rax := setWidth
  64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp :=
  setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11,
  r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend 64
  (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 1) + (({ rax :=
  setWidth 64 (setWidth 32 (rdx + 18446744073709551614#64)), rcx := 7353760#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp
  := setWidth 64 (setWidth 32 rbp ^^^ setWidth 32 rbp), rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 :=
  r11, r12 := r12, r13 := r13, r14 := setWidth 64 (setWidth 32 r14 ^^^ setWidth 32 r14), r15 := r15 }.set 0 (signExtend
  64 (setWidth 32 (rdx + 18446744073709551614#64)))).set (regOf 10) (Q8( (7935192#64) 8)))).get (regOf 0) * 8#64)
  8)))).set (regOf 1) 7353696#64).get (regOf 0)) 1)))))).set (regOf 1) (setWidth 64 48#32)).get (regOf 0))) 1)))
=== pr_19 (cut 745)
⊢ Q 748 { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rbx, r8 := r8, r9
  := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V
=== pr_20 (cut 748)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data ((rsp + 8#64).add i)) ∧
(decide (Q8( (rsp + 8#64) 8)) = 0#64) = true →
Q 927 G  V) ∧
(decide (Q8( (rsp + 8#64) 8)) = 0#64) = false →
((subF (rfz (subF (rfz (subF (rfz f) (Q8( (rsp + 8#64) 8))) 0#64)) rdi r13)) (rdi - r13) 1#64).cond 14 = true →
Q 790 { rax := rdi - r13, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
  r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  V) ∧
((subF (rfz (subF (rfz (subF (rfz f) (Q8( (rsp + 8#64) 8))) 0#64)) rdi r13)) (rdi - r13) 1#64).cond 14 = false →
(∀ (i : Nat), i < 1 →
Foot F.data ((rdi + 18446744073709551615#64).add i)) ∧
(∀ (i : Nat), i < 8 →
Foot F.data (Addr.add (7935192#64) i)) ∧
(∀ (i : Nat), i < 4 →
Foot F.data ((Q8( (7935192#64) 8)) + signExtend 64 (B( (rdi + 18446744073709551615#64) 1))) * 4#64).add i)) ∧
(decide (ofBytesLE 32 (MV( (Q8( (7935192#64) 8)) + signExtend 64 (B( (rdi + 18446744073709551615#64) 1))) * 4#64) 4)) =
  88#32) = true →
(∀ (i : Nat), i < 1 →
Foot F.data ((rdi + 18446744073709551614#64).add i)) ∧
((!decide (B( (rdi + 18446744073709551614#64) 1)) = 48#8)) = true →
Q 790 { rax := Q8( (7935192#64) 8)), rcx := rcx, rdx := signExtend 64 (B( (rdi + 18446744073709551615#64) 1))), rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }  V) ∧
((!decide (B( (rdi + 18446744073709551614#64) 1)) = 48#8)) = false →
(∀ (i : Nat), i < 8 →
Foot F.data ((rsp + 8#64).add i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (Q8( (rsp + 8#64) 8))) i)) ∧
Q 927 { rax := Q8( (rsp + 8#64) 8)), rcx := rcx, rdx := signExtend 64 (B( (rdi + 18446744073709551615#64) 1))), rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi - 1#64, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12,
  r13 := r13, r14 := r14, r15 := r15 }  (Vst V (Q8( (rsp + 8#64) 8))) (toBytesLE (rdi - 1#64) 8)))) ∧
(decide (ofBytesLE 32 (MV( (Q8( (7935192#64) 8)) + signExtend 64 (B( (rdi + 18446744073709551615#64) 1))) * 4#64) 4)) =
  88#32) = false →
Q 790 { rax := Q8( (7935192#64) 8)), rcx := rcx, rdx := signExtend 64 (B( (rdi + 18446744073709551615#64) 1))), rbx :=
  rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 :=
  r13, r14 := r14, r15 := r15 }  V)))
=== pr_21 (cut 790)
⊢ (∀ (i : Nat), i < 8 →
Foot F.data ((rsp + 8#64).add i)) ∧
(∀ (i : Nat), i < 8 →
Foot Wl (Addr.add (Q8( (rsp + 8#64) 8))) i)) ∧
∀ (af : Bool), Q 448 { rax := setWidth 64 (setWidth 32 (Q8( (rsp + 8#64) 8))) ^^^ setWidth 32 (Q8( (rsp + 8#64) 8)))),
  rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10,
  r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }  (Vst V (Q8( (rsp + 8#64) 8))) (toBytesLE r13 8))
=== pr_22 (cut 927)
⊢ ∀ (af : Bool), Q 448 { rax := setWidth 64 (setWidth 32 rax ^^^ setWidth 32 rax), rcx := rcx, rdx := rdx, rbx := rbx,
  rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
  r14 := r14, r15 := r15 }  V

-/
