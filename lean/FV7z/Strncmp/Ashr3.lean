import FV7z.Strncmp.AshrT
/-!
# The shifted loops `k = 7` to `9` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

theorem d2704 : ∀ feat, Dec feat scm 2704 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2708 : ∀ feat, Dec feat scm 2708 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d2712 : ∀ feat, Dec feat scm 2712 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d2716 : ∀ feat, Dec feat scm 2716 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2720 : ∀ feat, Dec feat scm 2720 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 9] 5) := by dec_rfl
theorem d2725 : ∀ feat, Dec feat scm 2725 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d2729 : ∀ feat, Dec feat scm 2729 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d2733 : ∀ feat, Dec feat scm 2733 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d2738 : ∀ feat, Dec feat scm 2738 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d2740 : ∀ feat, Dec feat scm 2740 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d2743 : ∀ feat, Dec feat scm 2743 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d2746 : ∀ feat, Dec feat scm 2746 (FV7z.mk (.jcc 5) 64 [.rel 3413] 6) := by dec_rfl
theorem d2752 : ∀ feat, Dec feat scm 2752 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d2756 : ∀ feat, Dec feat scm 2756
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d2761 : ∀ feat, Dec feat scm 2761 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2764 : ∀ feat, Dec feat scm 2764 (FV7z.mk (.jcc 2) 64 [.rel 3442] 6) := by dec_rfl
theorem d2770 : ∀ feat, Dec feat scm 2770 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2773 : ∀ feat, Dec feat scm 2773 (FV7z.mk (.jcc 4) 64 [.rel 3433] 6) := by dec_rfl
theorem d2779 : ∀ feat, Dec feat scm 2779 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2782 : ∀ feat, Dec feat scm 2782 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2786 : ∀ feat, Dec feat scm 2786 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d2793 : ∀ feat, Dec feat scm 2793 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 7)] 6) := by dec_rfl
theorem d2799 : ∀ feat, Dec feat scm 2799 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 7 0)] 4) := by dec_rfl
theorem d2803 : ∀ feat, Dec feat scm 2803 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d2810 : ∀ feat, Dec feat scm 2810 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d2817 : ∀ feat, Dec feat scm 2817 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d2828 : ∀ feat, Dec feat scm 2828 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d2832 : ∀ feat, Dec feat scm 2832 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2836 : ∀ feat, Dec feat scm 2836 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d2842 : ∀ feat, Dec feat scm 2842 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2847 : ∀ feat, Dec feat scm 2847 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2852 : ∀ feat, Dec feat scm 2852 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2856 : ∀ feat, Dec feat scm 2856 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 7] 5) := by dec_rfl
theorem d2861 : ∀ feat, Dec feat scm 2861 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 9] 5) := by dec_rfl
theorem d2866 : ∀ feat, Dec feat scm 2866 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2870 : ∀ feat, Dec feat scm 2870 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2874 : ∀ feat, Dec feat scm 2874 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2878 : ∀ feat, Dec feat scm 2878 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2882 : ∀ feat, Dec feat scm 2882 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2886 : ∀ feat, Dec feat scm 2886 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2892 : ∀ feat, Dec feat scm 2892 (FV7z.mk (.jcc 5) 64 [.rel 3262] 6) := by dec_rfl
theorem d2898 : ∀ feat, Dec feat scm 2898 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2902 : ∀ feat, Dec feat scm 2902 (FV7z.mk (.jcc 6) 64 [.rel 3304] 6) := by dec_rfl
theorem d2908 : ∀ feat, Dec feat scm 2908 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2912 : ∀ feat, Dec feat scm 2912 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2916 : ∀ feat, Dec feat scm 2916 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2920 : ∀ feat, Dec feat scm 2920 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d2922 : ∀ feat, Dec feat scm 2922 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2927 : ∀ feat, Dec feat scm 2927 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2932 : ∀ feat, Dec feat scm 2932 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2936 : ∀ feat, Dec feat scm 2936 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 7] 5) := by dec_rfl
theorem d2941 : ∀ feat, Dec feat scm 2941 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 9] 5) := by dec_rfl
theorem d2946 : ∀ feat, Dec feat scm 2946 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2950 : ∀ feat, Dec feat scm 2950 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2954 : ∀ feat, Dec feat scm 2954 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2958 : ∀ feat, Dec feat scm 2958 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2962 : ∀ feat, Dec feat scm 2962 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2966 : ∀ feat, Dec feat scm 2966 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2972 : ∀ feat, Dec feat scm 2972 (FV7z.mk (.jcc 5) 64 [.rel 3182] 6) := by dec_rfl
theorem d2978 : ∀ feat, Dec feat scm 2978 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2982 : ∀ feat, Dec feat scm 2982 (FV7z.mk (.jcc 6) 64 [.rel 3224] 6) := by dec_rfl
theorem d2988 : ∀ feat, Dec feat scm 2988 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2992 : ∀ feat, Dec feat scm 2992 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2996 : ∀ feat, Dec feat scm 2996 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d3008 : ∀ feat, Dec feat scm 3008 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d3012 : ∀ feat, Dec feat scm 3012 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d3016 : ∀ feat, Dec feat scm 3016 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65408)] 6) := by dec_rfl
theorem d3022 : ∀ feat, Dec feat scm 3022 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d3024 : ∀ feat, Dec feat scm 3024 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 9)] 4) := by dec_rfl
theorem d3028 : ∀ feat, Dec feat scm 3028 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d3030 : ∀ feat, Dec feat scm 3030 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3034 : ∀ feat, Dec feat scm 3034 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d3041 : ∀ feat, Dec feat scm 3041 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d3056 : ∀ feat, Dec feat scm 3056 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3061 : ∀ feat, Dec feat scm 3061 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 7] 5) := by dec_rfl
theorem d3066 : ∀ feat, Dec feat scm 3066 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 7] 5) := by dec_rfl
theorem d3071 : ∀ feat, Dec feat scm 3071 (FV7z.mk .jmp 64 [.rel 3068] 5) := by dec_rfl

/-- The loop at `2704`, `k = 7`. -/
theorem ashr7 (prof : Profile) : AshrC prof 7 2704 4 := by
  have b2704 : BlkV prof scm 2704 2729 (A0 7) :=
    .cons (d2704 _) (VOpI.pxor) (by decide) <|
    .cons (d2708 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2712 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2716 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2720 _) (VOpI.pslldq) (by decide) <|
    .cons (d2725 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 2729
  have b2729 : BlkV prof scm 2729 2746 (A25) :=
    .cons (d2729 _) (VOpI.psubb) (by decide) <|
    .cons (d2733 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2738 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d2740 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d2743 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 2746
  have b2752 : BlkV prof scm 2752 2764 (A48) :=
    .cons (d2752 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2756 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d2761 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 2764
  have b2770 : BlkV prof scm 2770 2773 (A66) :=
    .cons (d2770 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 2773
  have b2779 : BlkV prof scm 2779 2810 (A75 7) :=
    .cons (d2779 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d2782 _) (VOpI.pxor) (by decide) <|
    .cons (d2786 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2793 _) (OpI.mov (.i 7) (.inl rfl)) (by decide) <|
    .cons (d2799 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d2803 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 2810
  have b2810 : BlkV prof scm 2810 2832 (A106) :=
    .cons (d2810 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d2817 _) (OpI.nop) (by decide) <|
    .cons (d2828 _) (OpI.nop) (by decide) <|
    .nil 2832
  have b2832 : BlkV prof scm 2832 2836 (A128) :=
    .cons (d2832 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2836
  have b2842 : BlkV prof scm 2842 2870 (A138 7) :=
    .cons (d2842 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2847 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2852 _) (VOpI.movdqa) (by decide) <|
    .cons (d2856 _) (VOpI.psrldq) (by decide) <|
    .cons (d2861 _) (VOpI.pslldq) (by decide) <|
    .cons (d2866 _) (VOpI.por) (by decide) <|
    .nil 2870
  have b2870 : BlkV prof scm 2870 2892 (A166) :=
    .cons (d2870 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2874 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2878 _) (VOpI.psubb) (by decide) <|
    .cons (d2882 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2886 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2892
  have b2898 : BlkV prof scm 2898 2902 (A194) :=
    .cons (d2898 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2902
  have b2908 : BlkV prof scm 2908 2920 (A204) :=
    .cons (d2908 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2912 _) (VOpI.movdqa) (by decide) <|
    .cons (d2916 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2920
  have b2922 : BlkV prof scm 2922 2950 (A218 7) :=
    .cons (d2922 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2927 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2932 _) (VOpI.movdqa) (by decide) <|
    .cons (d2936 _) (VOpI.psrldq) (by decide) <|
    .cons (d2941 _) (VOpI.pslldq) (by decide) <|
    .cons (d2946 _) (VOpI.por) (by decide) <|
    .nil 2950
  have b2950 : BlkV prof scm 2950 2972 (A246) :=
    .cons (d2950 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2954 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2958 _) (VOpI.psubb) (by decide) <|
    .cons (d2962 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2966 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2972
  have b2978 : BlkV prof scm 2978 2982 (A274) :=
    .cons (d2978 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2982
  have b2988 : BlkV prof scm 2988 2996 (A284) :=
    .cons (d2988 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2992 _) (VOpI.movdqa) (by decide) <|
    .nil 2996
  have b3008 : BlkV prof scm 3008 3022 (A304 7) :=
    .cons (d3008 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3012 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3016 _) (OpI.test (.i 65408) (.inl rfl)) (by decide) <|
    .nil 3022
  have b3024 : BlkV prof scm 3024 3028 (A320 7) :=
    .cons (d3024 _) (OpI.cmp (.i 9) (.inr rfl)) (by decide) <|
    .nil 3028
  have b3030 : BlkV prof scm 3030 3041 (A326) :=
    .cons (d3030 _) (VOpI.pxor) (by decide) <|
    .cons (d3034 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 3041
  have b3056 : BlkV prof scm 3056 3071 (T352 7) :=
    .cons (d3056 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3061 _) (VOpI.psrldq) (by decide) <|
    .cons (d3066 _) (VOpI.psrldq) (by decide) <|
    .nil 3071
  exact ⟨b2704, b2729, ⟨_, d2746 _, rfl⟩, b2752, ⟨_, d2764 _, rfl⟩, b2770, ⟨_, d2773 _, rfl⟩, b2779, b2810, b2832,
    ⟨_, d2836 _, rfl⟩, b2842, b2870, ⟨_, d2892 _, rfl⟩, b2898, ⟨_, d2902 _, rfl⟩, b2908, ⟨_, d2920 _, rfl⟩, b2922,
    b2950, ⟨_, d2972 _, rfl⟩, b2978, ⟨_, d2982 _, rfl⟩, b2988, ⟨_, d2996 _, rfl⟩, b3008, ⟨_, d3022 _, rfl⟩, b3024,
    ⟨_, d3028 _, rfl⟩, b3030, ⟨_, d3041 _, rfl⟩, (.inl ⟨b3056, _, d3071 _, rfl⟩)⟩

theorem d3088 : ∀ feat, Dec feat scm 3088 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3092 : ∀ feat, Dec feat scm 3092 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d3096 : ∀ feat, Dec feat scm 3096 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d3100 : ∀ feat, Dec feat scm 3100 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3104 : ∀ feat, Dec feat scm 3104 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 8] 5) := by dec_rfl
theorem d3109 : ∀ feat, Dec feat scm 3109 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d3113 : ∀ feat, Dec feat scm 3113 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d3117 : ∀ feat, Dec feat scm 3117 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d3122 : ∀ feat, Dec feat scm 3122 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d3124 : ∀ feat, Dec feat scm 3124 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d3127 : ∀ feat, Dec feat scm 3127 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d3130 : ∀ feat, Dec feat scm 3130 (FV7z.mk (.jcc 5) 64 [.rel 3029] 6) := by dec_rfl
theorem d3136 : ∀ feat, Dec feat scm 3136 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d3140 : ∀ feat, Dec feat scm 3140
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d3145 : ∀ feat, Dec feat scm 3145 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3148 : ∀ feat, Dec feat scm 3148 (FV7z.mk (.jcc 2) 64 [.rel 3058] 6) := by dec_rfl
theorem d3154 : ∀ feat, Dec feat scm 3154 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3157 : ∀ feat, Dec feat scm 3157 (FV7z.mk (.jcc 4) 64 [.rel 3049] 6) := by dec_rfl
theorem d3163 : ∀ feat, Dec feat scm 3163 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3166 : ∀ feat, Dec feat scm 3166 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3170 : ∀ feat, Dec feat scm 3170 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d3177 : ∀ feat, Dec feat scm 3177 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 8)] 6) := by dec_rfl
theorem d3183 : ∀ feat, Dec feat scm 3183 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 8 0)] 4) := by dec_rfl
theorem d3187 : ∀ feat, Dec feat scm 3187 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d3194 : ∀ feat, Dec feat scm 3194 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d3201 : ∀ feat, Dec feat scm 3201 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d3212 : ∀ feat, Dec feat scm 3212 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d3216 : ∀ feat, Dec feat scm 3216 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3220 : ∀ feat, Dec feat scm 3220 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d3226 : ∀ feat, Dec feat scm 3226 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3231 : ∀ feat, Dec feat scm 3231 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d3236 : ∀ feat, Dec feat scm 3236 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d3240 : ∀ feat, Dec feat scm 3240 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 8] 5) := by dec_rfl
theorem d3245 : ∀ feat, Dec feat scm 3245 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 8] 5) := by dec_rfl
theorem d3250 : ∀ feat, Dec feat scm 3250 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d3254 : ∀ feat, Dec feat scm 3254 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3258 : ∀ feat, Dec feat scm 3258 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d3262 : ∀ feat, Dec feat scm 3262 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d3266 : ∀ feat, Dec feat scm 3266 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d3270 : ∀ feat, Dec feat scm 3270 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d3276 : ∀ feat, Dec feat scm 3276 (FV7z.mk (.jcc 5) 64 [.rel 2878] 6) := by dec_rfl
theorem d3282 : ∀ feat, Dec feat scm 3282 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3286 : ∀ feat, Dec feat scm 3286 (FV7z.mk (.jcc 6) 64 [.rel 2920] 6) := by dec_rfl
theorem d3292 : ∀ feat, Dec feat scm 3292 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3296 : ∀ feat, Dec feat scm 3296 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d3300 : ∀ feat, Dec feat scm 3300 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3304 : ∀ feat, Dec feat scm 3304 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d3306 : ∀ feat, Dec feat scm 3306 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3311 : ∀ feat, Dec feat scm 3311 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d3316 : ∀ feat, Dec feat scm 3316 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d3320 : ∀ feat, Dec feat scm 3320 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 8] 5) := by dec_rfl
theorem d3325 : ∀ feat, Dec feat scm 3325 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 8] 5) := by dec_rfl
theorem d3330 : ∀ feat, Dec feat scm 3330 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d3334 : ∀ feat, Dec feat scm 3334 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3338 : ∀ feat, Dec feat scm 3338 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d3342 : ∀ feat, Dec feat scm 3342 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d3346 : ∀ feat, Dec feat scm 3346 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d3350 : ∀ feat, Dec feat scm 3350 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d3356 : ∀ feat, Dec feat scm 3356 (FV7z.mk (.jcc 5) 64 [.rel 2798] 6) := by dec_rfl
theorem d3362 : ∀ feat, Dec feat scm 3362 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3366 : ∀ feat, Dec feat scm 3366 (FV7z.mk (.jcc 6) 64 [.rel 2840] 6) := by dec_rfl
theorem d3372 : ∀ feat, Dec feat scm 3372 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3376 : ∀ feat, Dec feat scm 3376 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d3380 : ∀ feat, Dec feat scm 3380 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d3392 : ∀ feat, Dec feat scm 3392 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d3396 : ∀ feat, Dec feat scm 3396 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d3400 : ∀ feat, Dec feat scm 3400 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65280)] 6) := by dec_rfl
theorem d3406 : ∀ feat, Dec feat scm 3406 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d3408 : ∀ feat, Dec feat scm 3408 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem d3412 : ∀ feat, Dec feat scm 3412 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d3414 : ∀ feat, Dec feat scm 3414 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3418 : ∀ feat, Dec feat scm 3418 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d3425 : ∀ feat, Dec feat scm 3425 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d3440 : ∀ feat, Dec feat scm 3440 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3445 : ∀ feat, Dec feat scm 3445 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 8] 5) := by dec_rfl
theorem d3450 : ∀ feat, Dec feat scm 3450 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 8] 5) := by dec_rfl
theorem d3455 : ∀ feat, Dec feat scm 3455 (FV7z.mk .jmp 64 [.rel 2684] 5) := by dec_rfl

/-- The loop at `3088`, `k = 8`. -/
theorem ashr8 (prof : Profile) : AshrC prof 8 3088 4 := by
  have b3088 : BlkV prof scm 3088 3113 (A0 8) :=
    .cons (d3088 _) (VOpI.pxor) (by decide) <|
    .cons (d3092 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3096 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3100 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3104 _) (VOpI.pslldq) (by decide) <|
    .cons (d3109 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 3113
  have b3113 : BlkV prof scm 3113 3130 (A25) :=
    .cons (d3113 _) (VOpI.psubb) (by decide) <|
    .cons (d3117 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3122 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d3124 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d3127 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 3130
  have b3136 : BlkV prof scm 3136 3148 (A48) :=
    .cons (d3136 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3140 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d3145 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 3148
  have b3154 : BlkV prof scm 3154 3157 (A66) :=
    .cons (d3154 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 3157
  have b3163 : BlkV prof scm 3163 3194 (A75 8) :=
    .cons (d3163 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d3166 _) (VOpI.pxor) (by decide) <|
    .cons (d3170 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3177 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
    .cons (d3183 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d3187 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 3194
  have b3194 : BlkV prof scm 3194 3216 (A106) :=
    .cons (d3194 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d3201 _) (OpI.nop) (by decide) <|
    .cons (d3212 _) (OpI.nop) (by decide) <|
    .nil 3216
  have b3216 : BlkV prof scm 3216 3220 (A128) :=
    .cons (d3216 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 3220
  have b3226 : BlkV prof scm 3226 3254 (A138 8) :=
    .cons (d3226 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3231 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3236 _) (VOpI.movdqa) (by decide) <|
    .cons (d3240 _) (VOpI.psrldq) (by decide) <|
    .cons (d3245 _) (VOpI.pslldq) (by decide) <|
    .cons (d3250 _) (VOpI.por) (by decide) <|
    .nil 3254
  have b3254 : BlkV prof scm 3254 3276 (A166) :=
    .cons (d3254 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3258 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3262 _) (VOpI.psubb) (by decide) <|
    .cons (d3266 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3270 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 3276
  have b3282 : BlkV prof scm 3282 3286 (A194) :=
    .cons (d3282 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 3286
  have b3292 : BlkV prof scm 3292 3304 (A204) :=
    .cons (d3292 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3296 _) (VOpI.movdqa) (by decide) <|
    .cons (d3300 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 3304
  have b3306 : BlkV prof scm 3306 3334 (A218 8) :=
    .cons (d3306 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3311 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3316 _) (VOpI.movdqa) (by decide) <|
    .cons (d3320 _) (VOpI.psrldq) (by decide) <|
    .cons (d3325 _) (VOpI.pslldq) (by decide) <|
    .cons (d3330 _) (VOpI.por) (by decide) <|
    .nil 3334
  have b3334 : BlkV prof scm 3334 3356 (A246) :=
    .cons (d3334 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3338 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3342 _) (VOpI.psubb) (by decide) <|
    .cons (d3346 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3350 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 3356
  have b3362 : BlkV prof scm 3362 3366 (A274) :=
    .cons (d3362 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 3366
  have b3372 : BlkV prof scm 3372 3380 (A284) :=
    .cons (d3372 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3376 _) (VOpI.movdqa) (by decide) <|
    .nil 3380
  have b3392 : BlkV prof scm 3392 3406 (A304 8) :=
    .cons (d3392 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3396 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3400 _) (OpI.test (.i 65280) (.inl rfl)) (by decide) <|
    .nil 3406
  have b3408 : BlkV prof scm 3408 3412 (A320 8) :=
    .cons (d3408 _) (OpI.cmp (.i 8) (.inr rfl)) (by decide) <|
    .nil 3412
  have b3414 : BlkV prof scm 3414 3425 (A326) :=
    .cons (d3414 _) (VOpI.pxor) (by decide) <|
    .cons (d3418 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 3425
  have b3440 : BlkV prof scm 3440 3455 (T352 8) :=
    .cons (d3440 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3445 _) (VOpI.psrldq) (by decide) <|
    .cons (d3450 _) (VOpI.psrldq) (by decide) <|
    .nil 3455
  exact ⟨b3088, b3113, ⟨_, d3130 _, rfl⟩, b3136, ⟨_, d3148 _, rfl⟩, b3154, ⟨_, d3157 _, rfl⟩, b3163, b3194, b3216,
    ⟨_, d3220 _, rfl⟩, b3226, b3254, ⟨_, d3276 _, rfl⟩, b3282, ⟨_, d3286 _, rfl⟩, b3292, ⟨_, d3304 _, rfl⟩, b3306,
    b3334, ⟨_, d3356 _, rfl⟩, b3362, ⟨_, d3366 _, rfl⟩, b3372, ⟨_, d3380 _, rfl⟩, b3392, ⟨_, d3406 _, rfl⟩, b3408,
    ⟨_, d3412 _, rfl⟩, b3414, ⟨_, d3425 _, rfl⟩, (.inl ⟨b3440, _, d3455 _, rfl⟩)⟩

theorem d3472 : ∀ feat, Dec feat scm 3472 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3476 : ∀ feat, Dec feat scm 3476 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d3480 : ∀ feat, Dec feat scm 3480 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d3484 : ∀ feat, Dec feat scm 3484 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3488 : ∀ feat, Dec feat scm 3488 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 7] 5) := by dec_rfl
theorem d3493 : ∀ feat, Dec feat scm 3493 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d3497 : ∀ feat, Dec feat scm 3497 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d3501 : ∀ feat, Dec feat scm 3501 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d3506 : ∀ feat, Dec feat scm 3506 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d3508 : ∀ feat, Dec feat scm 3508 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d3511 : ∀ feat, Dec feat scm 3511 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d3514 : ∀ feat, Dec feat scm 3514 (FV7z.mk (.jcc 5) 64 [.rel 2645] 6) := by dec_rfl
theorem d3520 : ∀ feat, Dec feat scm 3520 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d3524 : ∀ feat, Dec feat scm 3524
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d3529 : ∀ feat, Dec feat scm 3529 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3532 : ∀ feat, Dec feat scm 3532 (FV7z.mk (.jcc 2) 64 [.rel 2674] 6) := by dec_rfl
theorem d3538 : ∀ feat, Dec feat scm 3538 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3541 : ∀ feat, Dec feat scm 3541 (FV7z.mk (.jcc 4) 64 [.rel 2665] 6) := by dec_rfl
theorem d3547 : ∀ feat, Dec feat scm 3547 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d3550 : ∀ feat, Dec feat scm 3550 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3554 : ∀ feat, Dec feat scm 3554 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d3561 : ∀ feat, Dec feat scm 3561 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 9)] 6) := by dec_rfl
theorem d3567 : ∀ feat, Dec feat scm 3567 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 9 0)] 4) := by dec_rfl
theorem d3571 : ∀ feat, Dec feat scm 3571 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d3578 : ∀ feat, Dec feat scm 3578 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d3585 : ∀ feat, Dec feat scm 3585 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d3596 : ∀ feat, Dec feat scm 3596 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d3600 : ∀ feat, Dec feat scm 3600 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3604 : ∀ feat, Dec feat scm 3604 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d3610 : ∀ feat, Dec feat scm 3610 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3615 : ∀ feat, Dec feat scm 3615 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d3620 : ∀ feat, Dec feat scm 3620 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d3624 : ∀ feat, Dec feat scm 3624 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 9] 5) := by dec_rfl
theorem d3629 : ∀ feat, Dec feat scm 3629 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 7] 5) := by dec_rfl
theorem d3634 : ∀ feat, Dec feat scm 3634 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d3638 : ∀ feat, Dec feat scm 3638 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3642 : ∀ feat, Dec feat scm 3642 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d3646 : ∀ feat, Dec feat scm 3646 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d3650 : ∀ feat, Dec feat scm 3650 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d3654 : ∀ feat, Dec feat scm 3654 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d3660 : ∀ feat, Dec feat scm 3660 (FV7z.mk (.jcc 5) 64 [.rel 2494] 6) := by dec_rfl
theorem d3666 : ∀ feat, Dec feat scm 3666 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3670 : ∀ feat, Dec feat scm 3670 (FV7z.mk (.jcc 6) 64 [.rel 2536] 6) := by dec_rfl
theorem d3676 : ∀ feat, Dec feat scm 3676 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3680 : ∀ feat, Dec feat scm 3680 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d3684 : ∀ feat, Dec feat scm 3684 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3688 : ∀ feat, Dec feat scm 3688 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d3690 : ∀ feat, Dec feat scm 3690 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3695 : ∀ feat, Dec feat scm 3695 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d3700 : ∀ feat, Dec feat scm 3700 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d3704 : ∀ feat, Dec feat scm 3704 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 9] 5) := by dec_rfl
theorem d3709 : ∀ feat, Dec feat scm 3709 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 7] 5) := by dec_rfl
theorem d3714 : ∀ feat, Dec feat scm 3714 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d3718 : ∀ feat, Dec feat scm 3718 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d3722 : ∀ feat, Dec feat scm 3722 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d3726 : ∀ feat, Dec feat scm 3726 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d3730 : ∀ feat, Dec feat scm 3730 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d3734 : ∀ feat, Dec feat scm 3734 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d3740 : ∀ feat, Dec feat scm 3740 (FV7z.mk (.jcc 5) 64 [.rel 2414] 6) := by dec_rfl
theorem d3746 : ∀ feat, Dec feat scm 3746 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3750 : ∀ feat, Dec feat scm 3750 (FV7z.mk (.jcc 6) 64 [.rel 2456] 6) := by dec_rfl
theorem d3756 : ∀ feat, Dec feat scm 3756 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d3760 : ∀ feat, Dec feat scm 3760 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d3764 : ∀ feat, Dec feat scm 3764 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d3776 : ∀ feat, Dec feat scm 3776 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d3780 : ∀ feat, Dec feat scm 3780 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d3784 : ∀ feat, Dec feat scm 3784 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65024)] 6) := by dec_rfl
theorem d3790 : ∀ feat, Dec feat scm 3790 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d3792 : ∀ feat, Dec feat scm 3792 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 7)] 4) := by dec_rfl
theorem d3796 : ∀ feat, Dec feat scm 3796 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d3798 : ∀ feat, Dec feat scm 3798 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d3802 : ∀ feat, Dec feat scm 3802 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d3809 : ∀ feat, Dec feat scm 3809 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d3824 : ∀ feat, Dec feat scm 3824 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d3829 : ∀ feat, Dec feat scm 3829 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 9] 5) := by dec_rfl
theorem d3834 : ∀ feat, Dec feat scm 3834 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 9] 5) := by dec_rfl
theorem d3839 : ∀ feat, Dec feat scm 3839 (FV7z.mk .jmp 64 [.rel 2300] 5) := by dec_rfl

/-- The loop at `3472`, `k = 9`. -/
theorem ashr9 (prof : Profile) : AshrC prof 9 3472 4 := by
  have b3472 : BlkV prof scm 3472 3497 (A0 9) :=
    .cons (d3472 _) (VOpI.pxor) (by decide) <|
    .cons (d3476 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3480 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3484 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3488 _) (VOpI.pslldq) (by decide) <|
    .cons (d3493 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 3497
  have b3497 : BlkV prof scm 3497 3514 (A25) :=
    .cons (d3497 _) (VOpI.psubb) (by decide) <|
    .cons (d3501 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3506 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d3508 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d3511 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 3514
  have b3520 : BlkV prof scm 3520 3532 (A48) :=
    .cons (d3520 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d3524 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d3529 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 3532
  have b3538 : BlkV prof scm 3538 3541 (A66) :=
    .cons (d3538 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 3541
  have b3547 : BlkV prof scm 3547 3578 (A75 9) :=
    .cons (d3547 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d3550 _) (VOpI.pxor) (by decide) <|
    .cons (d3554 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3561 _) (OpI.mov (.i 9) (.inl rfl)) (by decide) <|
    .cons (d3567 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d3571 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 3578
  have b3578 : BlkV prof scm 3578 3600 (A106) :=
    .cons (d3578 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d3585 _) (OpI.nop) (by decide) <|
    .cons (d3596 _) (OpI.nop) (by decide) <|
    .nil 3600
  have b3600 : BlkV prof scm 3600 3604 (A128) :=
    .cons (d3600 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 3604
  have b3610 : BlkV prof scm 3610 3638 (A138 9) :=
    .cons (d3610 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3615 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3620 _) (VOpI.movdqa) (by decide) <|
    .cons (d3624 _) (VOpI.psrldq) (by decide) <|
    .cons (d3629 _) (VOpI.pslldq) (by decide) <|
    .cons (d3634 _) (VOpI.por) (by decide) <|
    .nil 3638
  have b3638 : BlkV prof scm 3638 3660 (A166) :=
    .cons (d3638 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3642 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3646 _) (VOpI.psubb) (by decide) <|
    .cons (d3650 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3654 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 3660
  have b3666 : BlkV prof scm 3666 3670 (A194) :=
    .cons (d3666 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 3670
  have b3676 : BlkV prof scm 3676 3688 (A204) :=
    .cons (d3676 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3680 _) (VOpI.movdqa) (by decide) <|
    .cons (d3684 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 3688
  have b3690 : BlkV prof scm 3690 3718 (A218 9) :=
    .cons (d3690 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3695 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3700 _) (VOpI.movdqa) (by decide) <|
    .cons (d3704 _) (VOpI.psrldq) (by decide) <|
    .cons (d3709 _) (VOpI.pslldq) (by decide) <|
    .cons (d3714 _) (VOpI.por) (by decide) <|
    .nil 3718
  have b3718 : BlkV prof scm 3718 3740 (A246) :=
    .cons (d3718 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3722 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3726 _) (VOpI.psubb) (by decide) <|
    .cons (d3730 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3734 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 3740
  have b3746 : BlkV prof scm 3746 3750 (A274) :=
    .cons (d3746 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 3750
  have b3756 : BlkV prof scm 3756 3764 (A284) :=
    .cons (d3756 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d3760 _) (VOpI.movdqa) (by decide) <|
    .nil 3764
  have b3776 : BlkV prof scm 3776 3790 (A304 9) :=
    .cons (d3776 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d3780 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d3784 _) (OpI.test (.i 65024) (.inl rfl)) (by decide) <|
    .nil 3790
  have b3792 : BlkV prof scm 3792 3796 (A320 9) :=
    .cons (d3792 _) (OpI.cmp (.i 7) (.inr rfl)) (by decide) <|
    .nil 3796
  have b3798 : BlkV prof scm 3798 3809 (A326) :=
    .cons (d3798 _) (VOpI.pxor) (by decide) <|
    .cons (d3802 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 3809
  have b3824 : BlkV prof scm 3824 3839 (T352 9) :=
    .cons (d3824 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d3829 _) (VOpI.psrldq) (by decide) <|
    .cons (d3834 _) (VOpI.psrldq) (by decide) <|
    .nil 3839
  exact ⟨b3472, b3497, ⟨_, d3514 _, rfl⟩, b3520, ⟨_, d3532 _, rfl⟩, b3538, ⟨_, d3541 _, rfl⟩, b3547, b3578, b3600,
    ⟨_, d3604 _, rfl⟩, b3610, b3638, ⟨_, d3660 _, rfl⟩, b3666, ⟨_, d3670 _, rfl⟩, b3676, ⟨_, d3688 _, rfl⟩, b3690,
    b3718, ⟨_, d3740 _, rfl⟩, b3746, ⟨_, d3750 _, rfl⟩, b3756, ⟨_, d3764 _, rfl⟩, b3776, ⟨_, d3790 _, rfl⟩, b3792,
    ⟨_, d3796 _, rfl⟩, b3798, ⟨_, d3809 _, rfl⟩, (.inl ⟨b3824, _, d3839 _, rfl⟩)⟩

end FV7z.Strncmp
