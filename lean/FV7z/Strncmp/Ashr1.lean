import FV7z.Strncmp.AshrT
/-!
# The shifted loops `k = 1` to `3` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

theorem d400 : ∀ feat, Dec feat scm 400 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d404 : ∀ feat, Dec feat scm 404 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d408 : ∀ feat, Dec feat scm 408 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d412 : ∀ feat, Dec feat scm 412 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d416 : ∀ feat, Dec feat scm 416 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 15] 5) := by dec_rfl
theorem d421 : ∀ feat, Dec feat scm 421 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d425 : ∀ feat, Dec feat scm 425 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d429 : ∀ feat, Dec feat scm 429 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d434 : ∀ feat, Dec feat scm 434 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d436 : ∀ feat, Dec feat scm 436 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d439 : ∀ feat, Dec feat scm 439 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d442 : ∀ feat, Dec feat scm 442 (FV7z.mk (.jcc 5) 64 [.rel 5717] 6) := by dec_rfl
theorem d448 : ∀ feat, Dec feat scm 448 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d452 : ∀ feat, Dec feat scm 452
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d457 : ∀ feat, Dec feat scm 457 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d460 : ∀ feat, Dec feat scm 460 (FV7z.mk (.jcc 2) 64 [.rel 5746] 6) := by dec_rfl
theorem d466 : ∀ feat, Dec feat scm 466 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d469 : ∀ feat, Dec feat scm 469 (FV7z.mk (.jcc 4) 64 [.rel 5737] 6) := by dec_rfl
theorem d475 : ∀ feat, Dec feat scm 475 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d478 : ∀ feat, Dec feat scm 478 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d482 : ∀ feat, Dec feat scm 482 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d489 : ∀ feat, Dec feat scm 489 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem d495 : ∀ feat, Dec feat scm 495 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 1 0)] 4) := by dec_rfl
theorem d499 : ∀ feat, Dec feat scm 499 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d506 : ∀ feat, Dec feat scm 506 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d513 : ∀ feat, Dec feat scm 513 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d524 : ∀ feat, Dec feat scm 524 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d528 : ∀ feat, Dec feat scm 528 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d532 : ∀ feat, Dec feat scm 532 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d538 : ∀ feat, Dec feat scm 538 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d543 : ∀ feat, Dec feat scm 543 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d548 : ∀ feat, Dec feat scm 548 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d552 : ∀ feat, Dec feat scm 552 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 1] 5) := by dec_rfl
theorem d557 : ∀ feat, Dec feat scm 557 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 15] 5) := by dec_rfl
theorem d562 : ∀ feat, Dec feat scm 562 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d566 : ∀ feat, Dec feat scm 566 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d570 : ∀ feat, Dec feat scm 570 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d574 : ∀ feat, Dec feat scm 574 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d578 : ∀ feat, Dec feat scm 578 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d582 : ∀ feat, Dec feat scm 582 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d588 : ∀ feat, Dec feat scm 588 (FV7z.mk (.jcc 5) 64 [.rel 5566] 6) := by dec_rfl
theorem d594 : ∀ feat, Dec feat scm 594 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d598 : ∀ feat, Dec feat scm 598 (FV7z.mk (.jcc 6) 64 [.rel 5608] 6) := by dec_rfl
theorem d604 : ∀ feat, Dec feat scm 604 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d608 : ∀ feat, Dec feat scm 608 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d612 : ∀ feat, Dec feat scm 612 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d616 : ∀ feat, Dec feat scm 616 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d618 : ∀ feat, Dec feat scm 618 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d623 : ∀ feat, Dec feat scm 623 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d628 : ∀ feat, Dec feat scm 628 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d632 : ∀ feat, Dec feat scm 632 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 1] 5) := by dec_rfl
theorem d637 : ∀ feat, Dec feat scm 637 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 15] 5) := by dec_rfl
theorem d642 : ∀ feat, Dec feat scm 642 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d646 : ∀ feat, Dec feat scm 646 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d650 : ∀ feat, Dec feat scm 650 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d654 : ∀ feat, Dec feat scm 654 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d658 : ∀ feat, Dec feat scm 658 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d662 : ∀ feat, Dec feat scm 662 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d668 : ∀ feat, Dec feat scm 668 (FV7z.mk (.jcc 5) 64 [.rel 5486] 6) := by dec_rfl
theorem d674 : ∀ feat, Dec feat scm 674 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d678 : ∀ feat, Dec feat scm 678 (FV7z.mk (.jcc 6) 64 [.rel 5528] 6) := by dec_rfl
theorem d684 : ∀ feat, Dec feat scm 684 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d688 : ∀ feat, Dec feat scm 688 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d692 : ∀ feat, Dec feat scm 692 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d704 : ∀ feat, Dec feat scm 704 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d708 : ∀ feat, Dec feat scm 708 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d712 : ∀ feat, Dec feat scm 712 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65534)] 6) := by dec_rfl
theorem d718 : ∀ feat, Dec feat scm 718 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d720 : ∀ feat, Dec feat scm 720 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 15)] 4) := by dec_rfl
theorem d724 : ∀ feat, Dec feat scm 724 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d726 : ∀ feat, Dec feat scm 726 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d730 : ∀ feat, Dec feat scm 730 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d737 : ∀ feat, Dec feat scm 737 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d752 : ∀ feat, Dec feat scm 752 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d757 : ∀ feat, Dec feat scm 757 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 1] 5) := by dec_rfl
theorem d762 : ∀ feat, Dec feat scm 762 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 1] 5) := by dec_rfl
theorem d767 : ∀ feat, Dec feat scm 767 (FV7z.mk .jmp 64 [.rel 5372] 5) := by dec_rfl

/-- The loop at `400`, `k = 1`. -/
theorem ashr1 (prof : Profile) : AshrC prof 1 400 4 := by
  have b400 : BlkV prof scm 400 425 (A0 1) :=
    .cons (d400 _) (VOpI.pxor) (by decide) <|
    .cons (d404 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d408 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d412 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d416 _) (VOpI.pslldq) (by decide) <|
    .cons (d421 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 425
  have b425 : BlkV prof scm 425 442 (A25) :=
    .cons (d425 _) (VOpI.psubb) (by decide) <|
    .cons (d429 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d434 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d436 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d439 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 442
  have b448 : BlkV prof scm 448 460 (A48) :=
    .cons (d448 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d452 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d457 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 460
  have b466 : BlkV prof scm 466 469 (A66) :=
    .cons (d466 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 469
  have b475 : BlkV prof scm 475 506 (A75 1) :=
    .cons (d475 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d478 _) (VOpI.pxor) (by decide) <|
    .cons (d482 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d489 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
    .cons (d495 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d499 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 506
  have b506 : BlkV prof scm 506 528 (A106) :=
    .cons (d506 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d513 _) (OpI.nop) (by decide) <|
    .cons (d524 _) (OpI.nop) (by decide) <|
    .nil 528
  have b528 : BlkV prof scm 528 532 (A128) :=
    .cons (d528 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 532
  have b538 : BlkV prof scm 538 566 (A138 1) :=
    .cons (d538 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d543 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d548 _) (VOpI.movdqa) (by decide) <|
    .cons (d552 _) (VOpI.psrldq) (by decide) <|
    .cons (d557 _) (VOpI.pslldq) (by decide) <|
    .cons (d562 _) (VOpI.por) (by decide) <|
    .nil 566
  have b566 : BlkV prof scm 566 588 (A166) :=
    .cons (d566 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d570 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d574 _) (VOpI.psubb) (by decide) <|
    .cons (d578 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d582 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 588
  have b594 : BlkV prof scm 594 598 (A194) :=
    .cons (d594 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 598
  have b604 : BlkV prof scm 604 616 (A204) :=
    .cons (d604 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d608 _) (VOpI.movdqa) (by decide) <|
    .cons (d612 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 616
  have b618 : BlkV prof scm 618 646 (A218 1) :=
    .cons (d618 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d623 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d628 _) (VOpI.movdqa) (by decide) <|
    .cons (d632 _) (VOpI.psrldq) (by decide) <|
    .cons (d637 _) (VOpI.pslldq) (by decide) <|
    .cons (d642 _) (VOpI.por) (by decide) <|
    .nil 646
  have b646 : BlkV prof scm 646 668 (A246) :=
    .cons (d646 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d650 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d654 _) (VOpI.psubb) (by decide) <|
    .cons (d658 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d662 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 668
  have b674 : BlkV prof scm 674 678 (A274) :=
    .cons (d674 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 678
  have b684 : BlkV prof scm 684 692 (A284) :=
    .cons (d684 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d688 _) (VOpI.movdqa) (by decide) <|
    .nil 692
  have b704 : BlkV prof scm 704 718 (A304 1) :=
    .cons (d704 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d708 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d712 _) (OpI.test (.i 65534) (.inl rfl)) (by decide) <|
    .nil 718
  have b720 : BlkV prof scm 720 724 (A320 1) :=
    .cons (d720 _) (OpI.cmp (.i 15) (.inr rfl)) (by decide) <|
    .nil 724
  have b726 : BlkV prof scm 726 737 (A326) :=
    .cons (d726 _) (VOpI.pxor) (by decide) <|
    .cons (d730 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 737
  have b752 : BlkV prof scm 752 767 (T352 1) :=
    .cons (d752 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d757 _) (VOpI.psrldq) (by decide) <|
    .cons (d762 _) (VOpI.psrldq) (by decide) <|
    .nil 767
  exact ⟨b400, b425, ⟨_, d442 _, rfl⟩, b448, ⟨_, d460 _, rfl⟩, b466, ⟨_, d469 _, rfl⟩, b475, b506, b528,
    ⟨_, d532 _, rfl⟩, b538, b566, ⟨_, d588 _, rfl⟩, b594, ⟨_, d598 _, rfl⟩, b604, ⟨_, d616 _, rfl⟩, b618, b646,
    ⟨_, d668 _, rfl⟩, b674, ⟨_, d678 _, rfl⟩, b684, ⟨_, d692 _, rfl⟩, b704, ⟨_, d718 _, rfl⟩, b720, ⟨_, d724 _, rfl⟩,
    b726, ⟨_, d737 _, rfl⟩, (.inl ⟨b752, _, d767 _, rfl⟩)⟩

theorem d784 : ∀ feat, Dec feat scm 784 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d788 : ∀ feat, Dec feat scm 788 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d792 : ∀ feat, Dec feat scm 792 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d796 : ∀ feat, Dec feat scm 796 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d800 : ∀ feat, Dec feat scm 800 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 14] 5) := by dec_rfl
theorem d805 : ∀ feat, Dec feat scm 805 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d809 : ∀ feat, Dec feat scm 809 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d813 : ∀ feat, Dec feat scm 813 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d818 : ∀ feat, Dec feat scm 818 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d820 : ∀ feat, Dec feat scm 820 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d823 : ∀ feat, Dec feat scm 823 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d826 : ∀ feat, Dec feat scm 826 (FV7z.mk (.jcc 5) 64 [.rel 5333] 6) := by dec_rfl
theorem d832 : ∀ feat, Dec feat scm 832 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d836 : ∀ feat, Dec feat scm 836
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d841 : ∀ feat, Dec feat scm 841 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d844 : ∀ feat, Dec feat scm 844 (FV7z.mk (.jcc 2) 64 [.rel 5362] 6) := by dec_rfl
theorem d850 : ∀ feat, Dec feat scm 850 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d853 : ∀ feat, Dec feat scm 853 (FV7z.mk (.jcc 4) 64 [.rel 5353] 6) := by dec_rfl
theorem d859 : ∀ feat, Dec feat scm 859 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d862 : ∀ feat, Dec feat scm 862 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d866 : ∀ feat, Dec feat scm 866 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d873 : ∀ feat, Dec feat scm 873 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 2)] 6) := by dec_rfl
theorem d879 : ∀ feat, Dec feat scm 879 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 2 0)] 4) := by dec_rfl
theorem d883 : ∀ feat, Dec feat scm 883 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d890 : ∀ feat, Dec feat scm 890 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d897 : ∀ feat, Dec feat scm 897 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d908 : ∀ feat, Dec feat scm 908 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d912 : ∀ feat, Dec feat scm 912 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d916 : ∀ feat, Dec feat scm 916 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d922 : ∀ feat, Dec feat scm 922 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d927 : ∀ feat, Dec feat scm 927 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d932 : ∀ feat, Dec feat scm 932 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d936 : ∀ feat, Dec feat scm 936 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 2] 5) := by dec_rfl
theorem d941 : ∀ feat, Dec feat scm 941 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 14] 5) := by dec_rfl
theorem d946 : ∀ feat, Dec feat scm 946 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d950 : ∀ feat, Dec feat scm 950 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d954 : ∀ feat, Dec feat scm 954 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d958 : ∀ feat, Dec feat scm 958 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d962 : ∀ feat, Dec feat scm 962 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d966 : ∀ feat, Dec feat scm 966 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d972 : ∀ feat, Dec feat scm 972 (FV7z.mk (.jcc 5) 64 [.rel 5182] 6) := by dec_rfl
theorem d978 : ∀ feat, Dec feat scm 978 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d982 : ∀ feat, Dec feat scm 982 (FV7z.mk (.jcc 6) 64 [.rel 5224] 6) := by dec_rfl
theorem d988 : ∀ feat, Dec feat scm 988 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d992 : ∀ feat, Dec feat scm 992 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d996 : ∀ feat, Dec feat scm 996 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1000 : ∀ feat, Dec feat scm 1000 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d1002 : ∀ feat, Dec feat scm 1002 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1007 : ∀ feat, Dec feat scm 1007 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d1012 : ∀ feat, Dec feat scm 1012 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d1016 : ∀ feat, Dec feat scm 1016 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 2] 5) := by dec_rfl
theorem d1021 : ∀ feat, Dec feat scm 1021 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 14] 5) := by dec_rfl
theorem d1026 : ∀ feat, Dec feat scm 1026 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d1030 : ∀ feat, Dec feat scm 1030 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1034 : ∀ feat, Dec feat scm 1034 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d1038 : ∀ feat, Dec feat scm 1038 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d1042 : ∀ feat, Dec feat scm 1042 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d1046 : ∀ feat, Dec feat scm 1046 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d1052 : ∀ feat, Dec feat scm 1052 (FV7z.mk (.jcc 5) 64 [.rel 5102] 6) := by dec_rfl
theorem d1058 : ∀ feat, Dec feat scm 1058 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1062 : ∀ feat, Dec feat scm 1062 (FV7z.mk (.jcc 6) 64 [.rel 5144] 6) := by dec_rfl
theorem d1068 : ∀ feat, Dec feat scm 1068 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1072 : ∀ feat, Dec feat scm 1072 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d1076 : ∀ feat, Dec feat scm 1076 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d1088 : ∀ feat, Dec feat scm 1088 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d1092 : ∀ feat, Dec feat scm 1092 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d1096 : ∀ feat, Dec feat scm 1096 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65532)] 6) := by dec_rfl
theorem d1102 : ∀ feat, Dec feat scm 1102 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d1104 : ∀ feat, Dec feat scm 1104 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 14)] 4) := by dec_rfl
theorem d1108 : ∀ feat, Dec feat scm 1108 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d1110 : ∀ feat, Dec feat scm 1110 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1114 : ∀ feat, Dec feat scm 1114 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d1121 : ∀ feat, Dec feat scm 1121 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d1136 : ∀ feat, Dec feat scm 1136 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1141 : ∀ feat, Dec feat scm 1141 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 2] 5) := by dec_rfl
theorem d1146 : ∀ feat, Dec feat scm 1146 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 2] 5) := by dec_rfl
theorem d1151 : ∀ feat, Dec feat scm 1151 (FV7z.mk .jmp 64 [.rel 4988] 5) := by dec_rfl

/-- The loop at `784`, `k = 2`. -/
theorem ashr2 (prof : Profile) : AshrC prof 2 784 4 := by
  have b784 : BlkV prof scm 784 809 (A0 2) :=
    .cons (d784 _) (VOpI.pxor) (by decide) <|
    .cons (d788 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d792 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d796 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d800 _) (VOpI.pslldq) (by decide) <|
    .cons (d805 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 809
  have b809 : BlkV prof scm 809 826 (A25) :=
    .cons (d809 _) (VOpI.psubb) (by decide) <|
    .cons (d813 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d818 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d820 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d823 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 826
  have b832 : BlkV prof scm 832 844 (A48) :=
    .cons (d832 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d836 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d841 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 844
  have b850 : BlkV prof scm 850 853 (A66) :=
    .cons (d850 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 853
  have b859 : BlkV prof scm 859 890 (A75 2) :=
    .cons (d859 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d862 _) (VOpI.pxor) (by decide) <|
    .cons (d866 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d873 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
    .cons (d879 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d883 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 890
  have b890 : BlkV prof scm 890 912 (A106) :=
    .cons (d890 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d897 _) (OpI.nop) (by decide) <|
    .cons (d908 _) (OpI.nop) (by decide) <|
    .nil 912
  have b912 : BlkV prof scm 912 916 (A128) :=
    .cons (d912 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 916
  have b922 : BlkV prof scm 922 950 (A138 2) :=
    .cons (d922 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d927 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d932 _) (VOpI.movdqa) (by decide) <|
    .cons (d936 _) (VOpI.psrldq) (by decide) <|
    .cons (d941 _) (VOpI.pslldq) (by decide) <|
    .cons (d946 _) (VOpI.por) (by decide) <|
    .nil 950
  have b950 : BlkV prof scm 950 972 (A166) :=
    .cons (d950 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d954 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d958 _) (VOpI.psubb) (by decide) <|
    .cons (d962 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d966 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 972
  have b978 : BlkV prof scm 978 982 (A194) :=
    .cons (d978 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 982
  have b988 : BlkV prof scm 988 1000 (A204) :=
    .cons (d988 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d992 _) (VOpI.movdqa) (by decide) <|
    .cons (d996 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 1000
  have b1002 : BlkV prof scm 1002 1030 (A218 2) :=
    .cons (d1002 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1007 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1012 _) (VOpI.movdqa) (by decide) <|
    .cons (d1016 _) (VOpI.psrldq) (by decide) <|
    .cons (d1021 _) (VOpI.pslldq) (by decide) <|
    .cons (d1026 _) (VOpI.por) (by decide) <|
    .nil 1030
  have b1030 : BlkV prof scm 1030 1052 (A246) :=
    .cons (d1030 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1034 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1038 _) (VOpI.psubb) (by decide) <|
    .cons (d1042 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1046 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 1052
  have b1058 : BlkV prof scm 1058 1062 (A274) :=
    .cons (d1058 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 1062
  have b1068 : BlkV prof scm 1068 1076 (A284) :=
    .cons (d1068 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1072 _) (VOpI.movdqa) (by decide) <|
    .nil 1076
  have b1088 : BlkV prof scm 1088 1102 (A304 2) :=
    .cons (d1088 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1092 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1096 _) (OpI.test (.i 65532) (.inl rfl)) (by decide) <|
    .nil 1102
  have b1104 : BlkV prof scm 1104 1108 (A320 2) :=
    .cons (d1104 _) (OpI.cmp (.i 14) (.inr rfl)) (by decide) <|
    .nil 1108
  have b1110 : BlkV prof scm 1110 1121 (A326) :=
    .cons (d1110 _) (VOpI.pxor) (by decide) <|
    .cons (d1114 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 1121
  have b1136 : BlkV prof scm 1136 1151 (T352 2) :=
    .cons (d1136 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1141 _) (VOpI.psrldq) (by decide) <|
    .cons (d1146 _) (VOpI.psrldq) (by decide) <|
    .nil 1151
  exact ⟨b784, b809, ⟨_, d826 _, rfl⟩, b832, ⟨_, d844 _, rfl⟩, b850, ⟨_, d853 _, rfl⟩, b859, b890, b912,
    ⟨_, d916 _, rfl⟩, b922, b950, ⟨_, d972 _, rfl⟩, b978, ⟨_, d982 _, rfl⟩, b988, ⟨_, d1000 _, rfl⟩, b1002, b1030,
    ⟨_, d1052 _, rfl⟩, b1058, ⟨_, d1062 _, rfl⟩, b1068, ⟨_, d1076 _, rfl⟩, b1088, ⟨_, d1102 _, rfl⟩, b1104,
    ⟨_, d1108 _, rfl⟩, b1110, ⟨_, d1121 _, rfl⟩, (.inl ⟨b1136, _, d1151 _, rfl⟩)⟩

theorem d1168 : ∀ feat, Dec feat scm 1168 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1172 : ∀ feat, Dec feat scm 1172 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1176 : ∀ feat, Dec feat scm 1176 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d1180 : ∀ feat, Dec feat scm 1180 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1184 : ∀ feat, Dec feat scm 1184 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 13] 5) := by dec_rfl
theorem d1189 : ∀ feat, Dec feat scm 1189 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d1193 : ∀ feat, Dec feat scm 1193 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d1197 : ∀ feat, Dec feat scm 1197 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d1202 : ∀ feat, Dec feat scm 1202 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d1204 : ∀ feat, Dec feat scm 1204 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d1207 : ∀ feat, Dec feat scm 1207 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d1210 : ∀ feat, Dec feat scm 1210 (FV7z.mk (.jcc 5) 64 [.rel 4949] 6) := by dec_rfl
theorem d1216 : ∀ feat, Dec feat scm 1216 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1220 : ∀ feat, Dec feat scm 1220
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d1225 : ∀ feat, Dec feat scm 1225 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1228 : ∀ feat, Dec feat scm 1228 (FV7z.mk (.jcc 2) 64 [.rel 4978] 6) := by dec_rfl
theorem d1234 : ∀ feat, Dec feat scm 1234 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1237 : ∀ feat, Dec feat scm 1237 (FV7z.mk (.jcc 4) 64 [.rel 4969] 6) := by dec_rfl
theorem d1243 : ∀ feat, Dec feat scm 1243 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1246 : ∀ feat, Dec feat scm 1246 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1250 : ∀ feat, Dec feat scm 1250 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d1257 : ∀ feat, Dec feat scm 1257 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 3)] 6) := by dec_rfl
theorem d1263 : ∀ feat, Dec feat scm 1263 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 3 0)] 4) := by dec_rfl
theorem d1267 : ∀ feat, Dec feat scm 1267 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d1274 : ∀ feat, Dec feat scm 1274 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d1281 : ∀ feat, Dec feat scm 1281 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d1292 : ∀ feat, Dec feat scm 1292 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d1296 : ∀ feat, Dec feat scm 1296 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1300 : ∀ feat, Dec feat scm 1300 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d1306 : ∀ feat, Dec feat scm 1306 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1311 : ∀ feat, Dec feat scm 1311 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d1316 : ∀ feat, Dec feat scm 1316 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d1320 : ∀ feat, Dec feat scm 1320 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 3] 5) := by dec_rfl
theorem d1325 : ∀ feat, Dec feat scm 1325 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 13] 5) := by dec_rfl
theorem d1330 : ∀ feat, Dec feat scm 1330 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d1334 : ∀ feat, Dec feat scm 1334 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1338 : ∀ feat, Dec feat scm 1338 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d1342 : ∀ feat, Dec feat scm 1342 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d1346 : ∀ feat, Dec feat scm 1346 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d1350 : ∀ feat, Dec feat scm 1350 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d1356 : ∀ feat, Dec feat scm 1356 (FV7z.mk (.jcc 5) 64 [.rel 4798] 6) := by dec_rfl
theorem d1362 : ∀ feat, Dec feat scm 1362 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1366 : ∀ feat, Dec feat scm 1366 (FV7z.mk (.jcc 6) 64 [.rel 4840] 6) := by dec_rfl
theorem d1372 : ∀ feat, Dec feat scm 1372 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1376 : ∀ feat, Dec feat scm 1376 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d1380 : ∀ feat, Dec feat scm 1380 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1384 : ∀ feat, Dec feat scm 1384 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d1386 : ∀ feat, Dec feat scm 1386 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1391 : ∀ feat, Dec feat scm 1391 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d1396 : ∀ feat, Dec feat scm 1396 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d1400 : ∀ feat, Dec feat scm 1400 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 3] 5) := by dec_rfl
theorem d1405 : ∀ feat, Dec feat scm 1405 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 13] 5) := by dec_rfl
theorem d1410 : ∀ feat, Dec feat scm 1410 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d1414 : ∀ feat, Dec feat scm 1414 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1418 : ∀ feat, Dec feat scm 1418 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d1422 : ∀ feat, Dec feat scm 1422 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d1426 : ∀ feat, Dec feat scm 1426 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d1430 : ∀ feat, Dec feat scm 1430 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d1436 : ∀ feat, Dec feat scm 1436 (FV7z.mk (.jcc 5) 64 [.rel 4718] 6) := by dec_rfl
theorem d1442 : ∀ feat, Dec feat scm 1442 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1446 : ∀ feat, Dec feat scm 1446 (FV7z.mk (.jcc 6) 64 [.rel 4760] 6) := by dec_rfl
theorem d1452 : ∀ feat, Dec feat scm 1452 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1456 : ∀ feat, Dec feat scm 1456 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d1460 : ∀ feat, Dec feat scm 1460 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d1472 : ∀ feat, Dec feat scm 1472 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d1476 : ∀ feat, Dec feat scm 1476 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d1480 : ∀ feat, Dec feat scm 1480 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65528)] 6) := by dec_rfl
theorem d1486 : ∀ feat, Dec feat scm 1486 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d1488 : ∀ feat, Dec feat scm 1488 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 13)] 4) := by dec_rfl
theorem d1492 : ∀ feat, Dec feat scm 1492 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d1494 : ∀ feat, Dec feat scm 1494 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1498 : ∀ feat, Dec feat scm 1498 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d1505 : ∀ feat, Dec feat scm 1505 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d1520 : ∀ feat, Dec feat scm 1520 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1525 : ∀ feat, Dec feat scm 1525 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 3] 5) := by dec_rfl
theorem d1530 : ∀ feat, Dec feat scm 1530 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 3] 5) := by dec_rfl
theorem d1535 : ∀ feat, Dec feat scm 1535 (FV7z.mk .jmp 64 [.rel 4604] 5) := by dec_rfl

/-- The loop at `1168`, `k = 3`. -/
theorem ashr3 (prof : Profile) : AshrC prof 3 1168 4 := by
  have b1168 : BlkV prof scm 1168 1193 (A0 3) :=
    .cons (d1168 _) (VOpI.pxor) (by decide) <|
    .cons (d1172 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1176 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1180 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1184 _) (VOpI.pslldq) (by decide) <|
    .cons (d1189 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 1193
  have b1193 : BlkV prof scm 1193 1210 (A25) :=
    .cons (d1193 _) (VOpI.psubb) (by decide) <|
    .cons (d1197 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1202 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1204 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1207 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 1210
  have b1216 : BlkV prof scm 1216 1228 (A48) :=
    .cons (d1216 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1220 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d1225 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 1228
  have b1234 : BlkV prof scm 1234 1237 (A66) :=
    .cons (d1234 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 1237
  have b1243 : BlkV prof scm 1243 1274 (A75 3) :=
    .cons (d1243 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d1246 _) (VOpI.pxor) (by decide) <|
    .cons (d1250 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1257 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
    .cons (d1263 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d1267 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 1274
  have b1274 : BlkV prof scm 1274 1296 (A106) :=
    .cons (d1274 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d1281 _) (OpI.nop) (by decide) <|
    .cons (d1292 _) (OpI.nop) (by decide) <|
    .nil 1296
  have b1296 : BlkV prof scm 1296 1300 (A128) :=
    .cons (d1296 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 1300
  have b1306 : BlkV prof scm 1306 1334 (A138 3) :=
    .cons (d1306 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1311 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1316 _) (VOpI.movdqa) (by decide) <|
    .cons (d1320 _) (VOpI.psrldq) (by decide) <|
    .cons (d1325 _) (VOpI.pslldq) (by decide) <|
    .cons (d1330 _) (VOpI.por) (by decide) <|
    .nil 1334
  have b1334 : BlkV prof scm 1334 1356 (A166) :=
    .cons (d1334 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1338 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1342 _) (VOpI.psubb) (by decide) <|
    .cons (d1346 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1350 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 1356
  have b1362 : BlkV prof scm 1362 1366 (A194) :=
    .cons (d1362 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 1366
  have b1372 : BlkV prof scm 1372 1384 (A204) :=
    .cons (d1372 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1376 _) (VOpI.movdqa) (by decide) <|
    .cons (d1380 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 1384
  have b1386 : BlkV prof scm 1386 1414 (A218 3) :=
    .cons (d1386 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1391 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1396 _) (VOpI.movdqa) (by decide) <|
    .cons (d1400 _) (VOpI.psrldq) (by decide) <|
    .cons (d1405 _) (VOpI.pslldq) (by decide) <|
    .cons (d1410 _) (VOpI.por) (by decide) <|
    .nil 1414
  have b1414 : BlkV prof scm 1414 1436 (A246) :=
    .cons (d1414 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1418 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1422 _) (VOpI.psubb) (by decide) <|
    .cons (d1426 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1430 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 1436
  have b1442 : BlkV prof scm 1442 1446 (A274) :=
    .cons (d1442 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 1446
  have b1452 : BlkV prof scm 1452 1460 (A284) :=
    .cons (d1452 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1456 _) (VOpI.movdqa) (by decide) <|
    .nil 1460
  have b1472 : BlkV prof scm 1472 1486 (A304 3) :=
    .cons (d1472 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1476 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1480 _) (OpI.test (.i 65528) (.inl rfl)) (by decide) <|
    .nil 1486
  have b1488 : BlkV prof scm 1488 1492 (A320 3) :=
    .cons (d1488 _) (OpI.cmp (.i 13) (.inr rfl)) (by decide) <|
    .nil 1492
  have b1494 : BlkV prof scm 1494 1505 (A326) :=
    .cons (d1494 _) (VOpI.pxor) (by decide) <|
    .cons (d1498 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 1505
  have b1520 : BlkV prof scm 1520 1535 (T352 3) :=
    .cons (d1520 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1525 _) (VOpI.psrldq) (by decide) <|
    .cons (d1530 _) (VOpI.psrldq) (by decide) <|
    .nil 1535
  exact ⟨b1168, b1193, ⟨_, d1210 _, rfl⟩, b1216, ⟨_, d1228 _, rfl⟩, b1234, ⟨_, d1237 _, rfl⟩, b1243, b1274, b1296,
    ⟨_, d1300 _, rfl⟩, b1306, b1334, ⟨_, d1356 _, rfl⟩, b1362, ⟨_, d1366 _, rfl⟩, b1372, ⟨_, d1384 _, rfl⟩, b1386,
    b1414, ⟨_, d1436 _, rfl⟩, b1442, ⟨_, d1446 _, rfl⟩, b1452, ⟨_, d1460 _, rfl⟩, b1472, ⟨_, d1486 _, rfl⟩, b1488,
    ⟨_, d1492 _, rfl⟩, b1494, ⟨_, d1505 _, rfl⟩, (.inl ⟨b1520, _, d1535 _, rfl⟩)⟩

end FV7z.Strncmp
