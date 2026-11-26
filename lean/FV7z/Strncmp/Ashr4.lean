import FV7z.Strncmp.AshrT
/-!
# The shifted loops `k = 10` to `12` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf


theorem d3856 : ∀ feat, Dec feat scm 3856 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift10 (k := 0) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3860 : ∀ feat, Dec feat scm 3860 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift10 (k := 4) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3864 : ∀ feat, Dec feat scm 3864 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) :=
  fun _ => lift10 (k := 8) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3868 : ∀ feat, Dec feat scm 3868 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift10 (k := 12) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3872 : ∀ feat, Dec feat scm 3872 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 6] 5) :=
  fun _ => lift10 (k := 16) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3877 : ∀ feat, Dec feat scm 3877 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) :=
  fun _ => lift10 (k := 21) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3881 : ∀ feat, Dec feat scm 3881 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) :=
  fun _ => lift10 (k := 25) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3885 : ∀ feat, Dec feat scm 3885 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) :=
  fun _ => lift10 (k := 29) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3890 : ∀ feat, Dec feat scm 3890 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) :=
  fun _ => lift10 (k := 34) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3892 : ∀ feat, Dec feat scm 3892 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) :=
  fun _ => lift10 (k := 36) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3895 : ∀ feat, Dec feat scm 3895 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) :=
  fun _ => lift10 (k := 39) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3898 : ∀ feat, Dec feat scm 3898 (FV7z.mk (.jcc 5) 64 [.rel 2261] 6) :=
  fun _ => lift10 (k := 42) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3904 : ∀ feat, Dec feat scm 3904 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift10 (k := 48) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3908 : ∀ feat, Dec feat scm 3908
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) :=
  fun _ => lift10 (k := 52) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3913 : ∀ feat, Dec feat scm 3913 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift10 (k := 57) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3916 : ∀ feat, Dec feat scm 3916 (FV7z.mk (.jcc 2) 64 [.rel 2290] 6) :=
  fun _ => lift10 (k := 60) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3922 : ∀ feat, Dec feat scm 3922 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift10 (k := 66) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3925 : ∀ feat, Dec feat scm 3925 (FV7z.mk (.jcc 4) 64 [.rel 2281] 6) :=
  fun _ => lift10 (k := 69) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3931 : ∀ feat, Dec feat scm 3931 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift10 (k := 75) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3934 : ∀ feat, Dec feat scm 3934 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift10 (k := 78) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3938 : ∀ feat, Dec feat scm 3938 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) :=
  fun _ => lift10 (k := 82) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3945 : ∀ feat, Dec feat scm 3945 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 10)] 6) :=
  fun _ => lift10 (k := 89) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3951 : ∀ feat, Dec feat scm 3951 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 10 0)] 4) :=
  fun _ => lift10 (k := 95) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3955 : ∀ feat, Dec feat scm 3955 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) :=
  fun _ => lift10 (k := 99) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3962 : ∀ feat, Dec feat scm 3962 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift10 (k := 106) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3969 : ∀ feat, Dec feat scm 3969 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) :=
  fun _ => lift10 (k := 113) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3980 : ∀ feat, Dec feat scm 3980 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) :=
  fun _ => lift10 (k := 124) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3984 : ∀ feat, Dec feat scm 3984 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 128) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3988 : ∀ feat, Dec feat scm 3988 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) :=
  fun _ => lift10 (k := 132) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3994 : ∀ feat, Dec feat scm 3994 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift10 (k := 138) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d3999 : ∀ feat, Dec feat scm 3999 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift10 (k := 143) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4004 : ∀ feat, Dec feat scm 4004 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift10 (k := 148) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4008 : ∀ feat, Dec feat scm 4008 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 10] 5) :=
  fun _ => lift10 (k := 152) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4013 : ∀ feat, Dec feat scm 4013 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 6] 5) :=
  fun _ => lift10 (k := 157) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4018 : ∀ feat, Dec feat scm 4018 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift10 (k := 162) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4022 : ∀ feat, Dec feat scm 4022 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift10 (k := 166) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4026 : ∀ feat, Dec feat scm 4026 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift10 (k := 170) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4030 : ∀ feat, Dec feat scm 4030 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift10 (k := 174) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4034 : ∀ feat, Dec feat scm 4034 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift10 (k := 178) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4038 : ∀ feat, Dec feat scm 4038 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift10 (k := 182) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4044 : ∀ feat, Dec feat scm 4044 (FV7z.mk (.jcc 5) 64 [.rel 2110] 6) :=
  fun _ => lift10 (k := 188) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4050 : ∀ feat, Dec feat scm 4050 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 194) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4054 : ∀ feat, Dec feat scm 4054 (FV7z.mk (.jcc 6) 64 [.rel 2152] 6) :=
  fun _ => lift10 (k := 198) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4060 : ∀ feat, Dec feat scm 4060 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 204) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4064 : ∀ feat, Dec feat scm 4064 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift10 (k := 208) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4068 : ∀ feat, Dec feat scm 4068 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 212) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4072 : ∀ feat, Dec feat scm 4072 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) :=
  fun _ => lift10 (k := 216) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4074 : ∀ feat, Dec feat scm 4074 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift10 (k := 218) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4079 : ∀ feat, Dec feat scm 4079 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift10 (k := 223) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4084 : ∀ feat, Dec feat scm 4084 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift10 (k := 228) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4088 : ∀ feat, Dec feat scm 4088 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 10] 5) :=
  fun _ => lift10 (k := 232) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4093 : ∀ feat, Dec feat scm 4093 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 6] 5) :=
  fun _ => lift10 (k := 237) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4098 : ∀ feat, Dec feat scm 4098 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift10 (k := 242) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4102 : ∀ feat, Dec feat scm 4102 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift10 (k := 246) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4106 : ∀ feat, Dec feat scm 4106 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift10 (k := 250) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4110 : ∀ feat, Dec feat scm 4110 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift10 (k := 254) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4114 : ∀ feat, Dec feat scm 4114 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift10 (k := 258) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4118 : ∀ feat, Dec feat scm 4118 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift10 (k := 262) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4124 : ∀ feat, Dec feat scm 4124 (FV7z.mk (.jcc 5) 64 [.rel 2030] 6) :=
  fun _ => lift10 (k := 268) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4130 : ∀ feat, Dec feat scm 4130 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 274) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4134 : ∀ feat, Dec feat scm 4134 (FV7z.mk (.jcc 6) 64 [.rel 2072] 6) :=
  fun _ => lift10 (k := 278) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4140 : ∀ feat, Dec feat scm 4140 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift10 (k := 284) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4144 : ∀ feat, Dec feat scm 4144 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift10 (k := 288) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4148 : ∀ feat, Dec feat scm 4148 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) :=
  fun _ => lift10 (k := 292) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4160 : ∀ feat, Dec feat scm 4160 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) :=
  fun _ => lift10 (k := 304) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4164 : ∀ feat, Dec feat scm 4164 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) :=
  fun _ => lift10 (k := 308) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4168 : ∀ feat, Dec feat scm 4168 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 64512)] 6) :=
  fun _ => lift10 (k := 312) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4174 : ∀ feat, Dec feat scm 4174 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) :=
  fun _ => lift10 (k := 318) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4176 : ∀ feat, Dec feat scm 4176 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 6)] 4) :=
  fun _ => lift10 (k := 320) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4180 : ∀ feat, Dec feat scm 4180 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) :=
  fun _ => lift10 (k := 324) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4182 : ∀ feat, Dec feat scm 4182 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift10 (k := 326) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4186 : ∀ feat, Dec feat scm 4186 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift10 (k := 330) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4193 : ∀ feat, Dec feat scm 4193 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) :=
  fun _ => lift10 (k := 337) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4208 : ∀ feat, Dec feat scm 4208 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift10 (k := 352) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4213 : ∀ feat, Dec feat scm 4213 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 10] 5) :=
  fun _ => lift10 (k := 357) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4218 : ∀ feat, Dec feat scm 4218 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 10] 5) :=
  fun _ => lift10 (k := 362) (by rw [ch10_length]; decide) (by intro f; rfl)
theorem d4223 : ∀ feat, Dec feat scm 4223 (FV7z.mk .jmp 64 [.rel 1916] 5) :=
  fun _ => lift10 (k := 367) (by rw [ch10_length]; decide) (by intro f; rfl)

/-- The loop at `3856`, `k = 10`. -/
theorem ashr10 (prof : Profile) : AshrC prof 10 3856 4 := by
  have b3856 : BlkV prof scm 3856 3881 (A0 10) :=
    .cons (d3856 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d3860 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d3864 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d3868 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d3872 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d3877 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .nil 3881
  have b3881 : BlkV prof scm 3881 3898 (A25) :=
    .cons (d3881 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d3885 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d3890 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d3892 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d3895 _) (OpI.sub (.r 9) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 3898
  have b3904 : BlkV prof scm 3904 3916 (A48) :=
    .cons (d3904 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d3908 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d3913 _) (OpI.cmp (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 3916
  have b3922 : BlkV prof scm 3922 3925 (A66) :=
    .cons (d3922 _) (OpI.test (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 3925
  have b3931 : BlkV prof scm 3931 3962 (A75 10) :=
    .cons (d3931 _) (OpI.mov (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d3934 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d3938 _) (OpI.mov (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d3945 _) (OpI.mov (.i 10) (.inl rfl)) (lt_scm (by decide)) <|
    .cons (d3951 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d3955 _) (OpI.and (.i 4095) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 3962
  have b3962 : BlkV prof scm 3962 3984 (A106) :=
    .cons (d3962 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d3969 _) (OpI.nop) (lt_scm (by decide)) <|
    .cons (d3980 _) (OpI.nop) (lt_scm (by decide)) <|
    .nil 3984
  have b3984 : BlkV prof scm 3984 3988 (A128) :=
    .cons (d3984 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 3988
  have b3994 : BlkV prof scm 3994 4022 (A138 10) :=
    .cons (d3994 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d3999 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4004 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4008 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4013 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4018 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4022
  have b4022 : BlkV prof scm 4022 4044 (A166) :=
    .cons (d4022 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4026 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4030 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4034 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4038 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4044
  have b4050 : BlkV prof scm 4050 4054 (A194) :=
    .cons (d4050 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4054
  have b4060 : BlkV prof scm 4060 4072 (A204) :=
    .cons (d4060 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4064 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4068 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4072
  have b4074 : BlkV prof scm 4074 4102 (A218 10) :=
    .cons (d4074 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4079 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4084 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4088 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4093 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4098 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4102
  have b4102 : BlkV prof scm 4102 4124 (A246) :=
    .cons (d4102 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4106 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4110 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4114 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4118 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4124
  have b4130 : BlkV prof scm 4130 4134 (A274) :=
    .cons (d4130 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4134
  have b4140 : BlkV prof scm 4140 4148 (A284) :=
    .cons (d4140 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4144 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .nil 4148
  have b4160 : BlkV prof scm 4160 4174 (A304 10) :=
    .cons (d4160 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4164 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4168 _) (OpI.test (.i 64512) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4174
  have b4176 : BlkV prof scm 4176 4180 (A320 10) :=
    .cons (d4176 _) (OpI.cmp (.i 6) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4180
  have b4182 : BlkV prof scm 4182 4193 (A326) :=
    .cons (d4182 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4186 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4193
  have b4208 : BlkV prof scm 4208 4223 (T352 10) :=
    .cons (d4208 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4213 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4218 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .nil 4223
  exact ⟨b3856, b3881, ⟨_, d3898 _, rfl⟩, b3904, ⟨_, d3916 _, rfl⟩, b3922, ⟨_, d3925 _, rfl⟩, b3931, b3962, b3984,
    ⟨_, d3988 _, rfl⟩, b3994, b4022, ⟨_, d4044 _, rfl⟩, b4050, ⟨_, d4054 _, rfl⟩, b4060, ⟨_, d4072 _, rfl⟩, b4074,
    b4102, ⟨_, d4124 _, rfl⟩, b4130, ⟨_, d4134 _, rfl⟩, b4140, ⟨_, d4148 _, rfl⟩, b4160, ⟨_, d4174 _, rfl⟩, b4176,
    ⟨_, d4180 _, rfl⟩, b4182, ⟨_, d4193 _, rfl⟩, (.inl ⟨b4208, _, d4223 _, rfl⟩)⟩

theorem d4240 : ∀ feat, Dec feat scm 4240 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift11 (k := 0) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4244 : ∀ feat, Dec feat scm 4244 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift11 (k := 4) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4248 : ∀ feat, Dec feat scm 4248 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) :=
  fun _ => lift11 (k := 8) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4252 : ∀ feat, Dec feat scm 4252 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift11 (k := 12) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4256 : ∀ feat, Dec feat scm 4256 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 5] 5) :=
  fun _ => lift11 (k := 16) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4261 : ∀ feat, Dec feat scm 4261 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) :=
  fun _ => lift11 (k := 21) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4265 : ∀ feat, Dec feat scm 4265 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) :=
  fun _ => lift11 (k := 25) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4269 : ∀ feat, Dec feat scm 4269 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) :=
  fun _ => lift11 (k := 29) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4274 : ∀ feat, Dec feat scm 4274 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) :=
  fun _ => lift11 (k := 34) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4276 : ∀ feat, Dec feat scm 4276 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) :=
  fun _ => lift11 (k := 36) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4279 : ∀ feat, Dec feat scm 4279 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) :=
  fun _ => lift11 (k := 39) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4282 : ∀ feat, Dec feat scm 4282 (FV7z.mk (.jcc 5) 64 [.rel 1877] 6) :=
  fun _ => lift11 (k := 42) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4288 : ∀ feat, Dec feat scm 4288 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift11 (k := 48) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4292 : ∀ feat, Dec feat scm 4292
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) :=
  fun _ => lift11 (k := 52) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4297 : ∀ feat, Dec feat scm 4297 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift11 (k := 57) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4300 : ∀ feat, Dec feat scm 4300 (FV7z.mk (.jcc 2) 64 [.rel 1906] 6) :=
  fun _ => lift11 (k := 60) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4306 : ∀ feat, Dec feat scm 4306 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift11 (k := 66) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4309 : ∀ feat, Dec feat scm 4309 (FV7z.mk (.jcc 4) 64 [.rel 1897] 6) :=
  fun _ => lift11 (k := 69) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4315 : ∀ feat, Dec feat scm 4315 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift11 (k := 75) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4318 : ∀ feat, Dec feat scm 4318 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift11 (k := 78) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4322 : ∀ feat, Dec feat scm 4322 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) :=
  fun _ => lift11 (k := 82) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4329 : ∀ feat, Dec feat scm 4329 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 11)] 6) :=
  fun _ => lift11 (k := 89) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4335 : ∀ feat, Dec feat scm 4335 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 11 0)] 4) :=
  fun _ => lift11 (k := 95) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4339 : ∀ feat, Dec feat scm 4339 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) :=
  fun _ => lift11 (k := 99) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4346 : ∀ feat, Dec feat scm 4346 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift11 (k := 106) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4353 : ∀ feat, Dec feat scm 4353 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) :=
  fun _ => lift11 (k := 113) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4364 : ∀ feat, Dec feat scm 4364 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) :=
  fun _ => lift11 (k := 124) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4368 : ∀ feat, Dec feat scm 4368 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 128) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4372 : ∀ feat, Dec feat scm 4372 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) :=
  fun _ => lift11 (k := 132) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4378 : ∀ feat, Dec feat scm 4378 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift11 (k := 138) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4383 : ∀ feat, Dec feat scm 4383 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift11 (k := 143) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4388 : ∀ feat, Dec feat scm 4388 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift11 (k := 148) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4392 : ∀ feat, Dec feat scm 4392 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 11] 5) :=
  fun _ => lift11 (k := 152) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4397 : ∀ feat, Dec feat scm 4397 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 5] 5) :=
  fun _ => lift11 (k := 157) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4402 : ∀ feat, Dec feat scm 4402 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift11 (k := 162) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4406 : ∀ feat, Dec feat scm 4406 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift11 (k := 166) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4410 : ∀ feat, Dec feat scm 4410 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift11 (k := 170) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4414 : ∀ feat, Dec feat scm 4414 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift11 (k := 174) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4418 : ∀ feat, Dec feat scm 4418 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift11 (k := 178) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4422 : ∀ feat, Dec feat scm 4422 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift11 (k := 182) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4428 : ∀ feat, Dec feat scm 4428 (FV7z.mk (.jcc 5) 64 [.rel 1726] 6) :=
  fun _ => lift11 (k := 188) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4434 : ∀ feat, Dec feat scm 4434 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 194) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4438 : ∀ feat, Dec feat scm 4438 (FV7z.mk (.jcc 6) 64 [.rel 1768] 6) :=
  fun _ => lift11 (k := 198) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4444 : ∀ feat, Dec feat scm 4444 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 204) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4448 : ∀ feat, Dec feat scm 4448 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift11 (k := 208) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4452 : ∀ feat, Dec feat scm 4452 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 212) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4456 : ∀ feat, Dec feat scm 4456 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) :=
  fun _ => lift11 (k := 216) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4458 : ∀ feat, Dec feat scm 4458 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift11 (k := 218) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4463 : ∀ feat, Dec feat scm 4463 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift11 (k := 223) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4468 : ∀ feat, Dec feat scm 4468 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift11 (k := 228) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4472 : ∀ feat, Dec feat scm 4472 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 11] 5) :=
  fun _ => lift11 (k := 232) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4477 : ∀ feat, Dec feat scm 4477 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 5] 5) :=
  fun _ => lift11 (k := 237) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4482 : ∀ feat, Dec feat scm 4482 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift11 (k := 242) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4486 : ∀ feat, Dec feat scm 4486 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift11 (k := 246) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4490 : ∀ feat, Dec feat scm 4490 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift11 (k := 250) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4494 : ∀ feat, Dec feat scm 4494 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift11 (k := 254) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4498 : ∀ feat, Dec feat scm 4498 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift11 (k := 258) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4502 : ∀ feat, Dec feat scm 4502 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift11 (k := 262) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4508 : ∀ feat, Dec feat scm 4508 (FV7z.mk (.jcc 5) 64 [.rel 1646] 6) :=
  fun _ => lift11 (k := 268) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4514 : ∀ feat, Dec feat scm 4514 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 274) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4518 : ∀ feat, Dec feat scm 4518 (FV7z.mk (.jcc 6) 64 [.rel 1688] 6) :=
  fun _ => lift11 (k := 278) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4524 : ∀ feat, Dec feat scm 4524 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift11 (k := 284) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4528 : ∀ feat, Dec feat scm 4528 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift11 (k := 288) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4532 : ∀ feat, Dec feat scm 4532 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) :=
  fun _ => lift11 (k := 292) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4544 : ∀ feat, Dec feat scm 4544 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) :=
  fun _ => lift11 (k := 304) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4548 : ∀ feat, Dec feat scm 4548 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) :=
  fun _ => lift11 (k := 308) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4552 : ∀ feat, Dec feat scm 4552 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 63488)] 6) :=
  fun _ => lift11 (k := 312) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4558 : ∀ feat, Dec feat scm 4558 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) :=
  fun _ => lift11 (k := 318) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4560 : ∀ feat, Dec feat scm 4560 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 5)] 4) :=
  fun _ => lift11 (k := 320) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4564 : ∀ feat, Dec feat scm 4564 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) :=
  fun _ => lift11 (k := 324) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4566 : ∀ feat, Dec feat scm 4566 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift11 (k := 326) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4570 : ∀ feat, Dec feat scm 4570 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift11 (k := 330) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4577 : ∀ feat, Dec feat scm 4577 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) :=
  fun _ => lift11 (k := 337) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4592 : ∀ feat, Dec feat scm 4592 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift11 (k := 352) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4597 : ∀ feat, Dec feat scm 4597 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 11] 5) :=
  fun _ => lift11 (k := 357) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4602 : ∀ feat, Dec feat scm 4602 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 11] 5) :=
  fun _ => lift11 (k := 362) (by rw [ch11_length]; decide) (by intro f; rfl)
theorem d4607 : ∀ feat, Dec feat scm 4607 (FV7z.mk .jmp 64 [.rel 1532] 5) :=
  fun _ => lift11 (k := 367) (by rw [ch11_length]; decide) (by intro f; rfl)

/-- The loop at `4240`, `k = 11`. -/
theorem ashr11 (prof : Profile) : AshrC prof 11 4240 4 := by
  have b4240 : BlkV prof scm 4240 4265 (A0 11) :=
    .cons (d4240 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4244 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4248 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4252 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4256 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4261 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .nil 4265
  have b4265 : BlkV prof scm 4265 4282 (A25) :=
    .cons (d4265 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4269 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4274 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d4276 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d4279 _) (OpI.sub (.r 9) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4282
  have b4288 : BlkV prof scm 4288 4300 (A48) :=
    .cons (d4288 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4292 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4297 _) (OpI.cmp (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4300
  have b4306 : BlkV prof scm 4306 4309 (A66) :=
    .cons (d4306 _) (OpI.test (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4309
  have b4315 : BlkV prof scm 4315 4346 (A75 11) :=
    .cons (d4315 _) (OpI.mov (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4318 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4322 _) (OpI.mov (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4329 _) (OpI.mov (.i 11) (.inl rfl)) (lt_scm (by decide)) <|
    .cons (d4335 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4339 _) (OpI.and (.i 4095) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4346
  have b4346 : BlkV prof scm 4346 4368 (A106) :=
    .cons (d4346 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4353 _) (OpI.nop) (lt_scm (by decide)) <|
    .cons (d4364 _) (OpI.nop) (lt_scm (by decide)) <|
    .nil 4368
  have b4368 : BlkV prof scm 4368 4372 (A128) :=
    .cons (d4368 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4372
  have b4378 : BlkV prof scm 4378 4406 (A138 11) :=
    .cons (d4378 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4383 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4388 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4392 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4397 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4402 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4406
  have b4406 : BlkV prof scm 4406 4428 (A166) :=
    .cons (d4406 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4410 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4414 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4418 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4422 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4428
  have b4434 : BlkV prof scm 4434 4438 (A194) :=
    .cons (d4434 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4438
  have b4444 : BlkV prof scm 4444 4456 (A204) :=
    .cons (d4444 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4448 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4452 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4456
  have b4458 : BlkV prof scm 4458 4486 (A218 11) :=
    .cons (d4458 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4463 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4468 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4472 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4477 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4482 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4486
  have b4486 : BlkV prof scm 4486 4508 (A246) :=
    .cons (d4486 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4490 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4494 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4498 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4502 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4508
  have b4514 : BlkV prof scm 4514 4518 (A274) :=
    .cons (d4514 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4518
  have b4524 : BlkV prof scm 4524 4532 (A284) :=
    .cons (d4524 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4528 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .nil 4532
  have b4544 : BlkV prof scm 4544 4558 (A304 11) :=
    .cons (d4544 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4548 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4552 _) (OpI.test (.i 63488) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4558
  have b4560 : BlkV prof scm 4560 4564 (A320 11) :=
    .cons (d4560 _) (OpI.cmp (.i 5) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4564
  have b4566 : BlkV prof scm 4566 4577 (A326) :=
    .cons (d4566 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4570 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4577
  have b4592 : BlkV prof scm 4592 4607 (T352 11) :=
    .cons (d4592 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4597 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4602 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .nil 4607
  exact ⟨b4240, b4265, ⟨_, d4282 _, rfl⟩, b4288, ⟨_, d4300 _, rfl⟩, b4306, ⟨_, d4309 _, rfl⟩, b4315, b4346, b4368,
    ⟨_, d4372 _, rfl⟩, b4378, b4406, ⟨_, d4428 _, rfl⟩, b4434, ⟨_, d4438 _, rfl⟩, b4444, ⟨_, d4456 _, rfl⟩, b4458,
    b4486, ⟨_, d4508 _, rfl⟩, b4514, ⟨_, d4518 _, rfl⟩, b4524, ⟨_, d4532 _, rfl⟩, b4544, ⟨_, d4558 _, rfl⟩, b4560,
    ⟨_, d4564 _, rfl⟩, b4566, ⟨_, d4577 _, rfl⟩, (.inl ⟨b4592, _, d4607 _, rfl⟩)⟩

theorem d4624 : ∀ feat, Dec feat scm 4624 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift12 (k := 0) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4628 : ∀ feat, Dec feat scm 4628 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift12 (k := 4) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4632 : ∀ feat, Dec feat scm 4632 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) :=
  fun _ => lift12 (k := 8) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4636 : ∀ feat, Dec feat scm 4636 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift12 (k := 12) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4640 : ∀ feat, Dec feat scm 4640 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 4] 5) :=
  fun _ => lift12 (k := 16) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4645 : ∀ feat, Dec feat scm 4645 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) :=
  fun _ => lift12 (k := 21) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4649 : ∀ feat, Dec feat scm 4649 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) :=
  fun _ => lift12 (k := 25) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4653 : ∀ feat, Dec feat scm 4653 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) :=
  fun _ => lift12 (k := 29) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4658 : ∀ feat, Dec feat scm 4658 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) :=
  fun _ => lift12 (k := 34) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4660 : ∀ feat, Dec feat scm 4660 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) :=
  fun _ => lift12 (k := 36) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4663 : ∀ feat, Dec feat scm 4663 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) :=
  fun _ => lift12 (k := 39) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4666 : ∀ feat, Dec feat scm 4666 (FV7z.mk (.jcc 5) 64 [.rel 1493] 6) :=
  fun _ => lift12 (k := 42) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4672 : ∀ feat, Dec feat scm 4672 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) :=
  fun _ => lift12 (k := 48) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4676 : ∀ feat, Dec feat scm 4676
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) :=
  fun _ => lift12 (k := 52) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4681 : ∀ feat, Dec feat scm 4681 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift12 (k := 57) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4684 : ∀ feat, Dec feat scm 4684 (FV7z.mk (.jcc 2) 64 [.rel 1522] 6) :=
  fun _ => lift12 (k := 60) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4690 : ∀ feat, Dec feat scm 4690 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift12 (k := 66) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4693 : ∀ feat, Dec feat scm 4693 (FV7z.mk (.jcc 4) 64 [.rel 1513] 6) :=
  fun _ => lift12 (k := 69) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4699 : ∀ feat, Dec feat scm 4699 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) :=
  fun _ => lift12 (k := 75) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4702 : ∀ feat, Dec feat scm 4702 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift12 (k := 78) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4706 : ∀ feat, Dec feat scm 4706 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) :=
  fun _ => lift12 (k := 82) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4713 : ∀ feat, Dec feat scm 4713 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 12)] 6) :=
  fun _ => lift12 (k := 89) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4719 : ∀ feat, Dec feat scm 4719 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 12 0)] 4) :=
  fun _ => lift12 (k := 95) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4723 : ∀ feat, Dec feat scm 4723 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) :=
  fun _ => lift12 (k := 99) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4730 : ∀ feat, Dec feat scm 4730 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift12 (k := 106) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4737 : ∀ feat, Dec feat scm 4737 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) :=
  fun _ => lift12 (k := 113) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4748 : ∀ feat, Dec feat scm 4748 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) :=
  fun _ => lift12 (k := 124) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4752 : ∀ feat, Dec feat scm 4752 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 128) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4756 : ∀ feat, Dec feat scm 4756 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) :=
  fun _ => lift12 (k := 132) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4762 : ∀ feat, Dec feat scm 4762 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift12 (k := 138) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4767 : ∀ feat, Dec feat scm 4767 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift12 (k := 143) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4772 : ∀ feat, Dec feat scm 4772 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift12 (k := 148) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4776 : ∀ feat, Dec feat scm 4776 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 12] 5) :=
  fun _ => lift12 (k := 152) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4781 : ∀ feat, Dec feat scm 4781 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 4] 5) :=
  fun _ => lift12 (k := 157) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4786 : ∀ feat, Dec feat scm 4786 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift12 (k := 162) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4790 : ∀ feat, Dec feat scm 4790 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift12 (k := 166) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4794 : ∀ feat, Dec feat scm 4794 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift12 (k := 170) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4798 : ∀ feat, Dec feat scm 4798 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift12 (k := 174) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4802 : ∀ feat, Dec feat scm 4802 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift12 (k := 178) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4806 : ∀ feat, Dec feat scm 4806 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift12 (k := 182) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4812 : ∀ feat, Dec feat scm 4812 (FV7z.mk (.jcc 5) 64 [.rel 1342] 6) :=
  fun _ => lift12 (k := 188) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4818 : ∀ feat, Dec feat scm 4818 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 194) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4822 : ∀ feat, Dec feat scm 4822 (FV7z.mk (.jcc 6) 64 [.rel 1384] 6) :=
  fun _ => lift12 (k := 198) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4828 : ∀ feat, Dec feat scm 4828 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 204) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4832 : ∀ feat, Dec feat scm 4832 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift12 (k := 208) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4836 : ∀ feat, Dec feat scm 4836 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 212) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4840 : ∀ feat, Dec feat scm 4840 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) :=
  fun _ => lift12 (k := 216) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4842 : ∀ feat, Dec feat scm 4842 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift12 (k := 218) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4847 : ∀ feat, Dec feat scm 4847 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) :=
  fun _ => lift12 (k := 223) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4852 : ∀ feat, Dec feat scm 4852 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) :=
  fun _ => lift12 (k := 228) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4856 : ∀ feat, Dec feat scm 4856 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 12] 5) :=
  fun _ => lift12 (k := 232) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4861 : ∀ feat, Dec feat scm 4861 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 4] 5) :=
  fun _ => lift12 (k := 237) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4866 : ∀ feat, Dec feat scm 4866 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) :=
  fun _ => lift12 (k := 242) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4870 : ∀ feat, Dec feat scm 4870 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) :=
  fun _ => lift12 (k := 246) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4874 : ∀ feat, Dec feat scm 4874 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) :=
  fun _ => lift12 (k := 250) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4878 : ∀ feat, Dec feat scm 4878 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) :=
  fun _ => lift12 (k := 254) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4882 : ∀ feat, Dec feat scm 4882 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) :=
  fun _ => lift12 (k := 258) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4886 : ∀ feat, Dec feat scm 4886 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) :=
  fun _ => lift12 (k := 262) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4892 : ∀ feat, Dec feat scm 4892 (FV7z.mk (.jcc 5) 64 [.rel 1262] 6) :=
  fun _ => lift12 (k := 268) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4898 : ∀ feat, Dec feat scm 4898 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 274) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4902 : ∀ feat, Dec feat scm 4902 (FV7z.mk (.jcc 6) 64 [.rel 1304] 6) :=
  fun _ => lift12 (k := 278) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4908 : ∀ feat, Dec feat scm 4908 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) :=
  fun _ => lift12 (k := 284) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4912 : ∀ feat, Dec feat scm 4912 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) :=
  fun _ => lift12 (k := 288) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4916 : ∀ feat, Dec feat scm 4916 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) :=
  fun _ => lift12 (k := 292) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4928 : ∀ feat, Dec feat scm 4928 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) :=
  fun _ => lift12 (k := 304) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4932 : ∀ feat, Dec feat scm 4932 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) :=
  fun _ => lift12 (k := 308) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4936 : ∀ feat, Dec feat scm 4936 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 61440)] 6) :=
  fun _ => lift12 (k := 312) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4942 : ∀ feat, Dec feat scm 4942 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) :=
  fun _ => lift12 (k := 318) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4944 : ∀ feat, Dec feat scm 4944 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 4)] 4) :=
  fun _ => lift12 (k := 320) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4948 : ∀ feat, Dec feat scm 4948 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) :=
  fun _ => lift12 (k := 324) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4950 : ∀ feat, Dec feat scm 4950 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) :=
  fun _ => lift12 (k := 326) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4954 : ∀ feat, Dec feat scm 4954 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) :=
  fun _ => lift12 (k := 330) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4961 : ∀ feat, Dec feat scm 4961 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) :=
  fun _ => lift12 (k := 337) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4976 : ∀ feat, Dec feat scm 4976 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) :=
  fun _ => lift12 (k := 352) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4981 : ∀ feat, Dec feat scm 4981 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 12] 5) :=
  fun _ => lift12 (k := 357) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4986 : ∀ feat, Dec feat scm 4986 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 12] 5) :=
  fun _ => lift12 (k := 362) (by rw [ch12_length]; decide) (by intro f; rfl)
theorem d4991 : ∀ feat, Dec feat scm 4991 (FV7z.mk .jmp 64 [.rel 1148] 5) :=
  fun _ => lift12 (k := 367) (by rw [ch12_length]; decide) (by intro f; rfl)

/-- The loop at `4624`, `k = 12`. -/
theorem ashr12 (prof : Profile) : AshrC prof 12 4624 4 := by
  have b4624 : BlkV prof scm 4624 4649 (A0 12) :=
    .cons (d4624 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4628 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4632 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4636 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4640 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4645 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .nil 4649
  have b4649 : BlkV prof scm 4649 4666 (A25) :=
    .cons (d4649 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4653 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4658 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d4660 _) (OpI.shr (.r 1)) (lt_scm (by decide)) <|
    .cons (d4663 _) (OpI.sub (.r 9) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4666
  have b4672 : BlkV prof scm 4672 4684 (A48) :=
    .cons (d4672 _) (VOpI.movdqa_m) (lt_scm (by decide)) <|
    .cons (d4676 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4681 _) (OpI.cmp (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4684
  have b4690 : BlkV prof scm 4690 4693 (A66) :=
    .cons (d4690 _) (OpI.test (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4693
  have b4699 : BlkV prof scm 4699 4730 (A75 12) :=
    .cons (d4699 _) (OpI.mov (.r 9) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4702 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4706 _) (OpI.mov (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4713 _) (OpI.mov (.i 12) (.inl rfl)) (lt_scm (by decide)) <|
    .cons (d4719 _) (OpI.lea (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4723 _) (OpI.and (.i 4095) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4730
  have b4730 : BlkV prof scm 4730 4752 (A106) :=
    .cons (d4730 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4737 _) (OpI.nop) (lt_scm (by decide)) <|
    .cons (d4748 _) (OpI.nop) (lt_scm (by decide)) <|
    .nil 4752
  have b4752 : BlkV prof scm 4752 4756 (A128) :=
    .cons (d4752 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4756
  have b4762 : BlkV prof scm 4762 4790 (A138 12) :=
    .cons (d4762 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4767 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4772 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4776 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4781 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4786 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4790
  have b4790 : BlkV prof scm 4790 4812 (A166) :=
    .cons (d4790 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4794 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4798 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4802 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4806 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4812
  have b4818 : BlkV prof scm 4818 4822 (A194) :=
    .cons (d4818 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4822
  have b4828 : BlkV prof scm 4828 4840 (A204) :=
    .cons (d4828 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4832 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4836 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4840
  have b4842 : BlkV prof scm 4842 4870 (A218 12) :=
    .cons (d4842 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4847 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4852 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .cons (d4856 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4861 _) (VOpI.pslldq) (lt_scm (by decide)) <|
    .cons (d4866 _) (VOpI.por) (lt_scm (by decide)) <|
    .nil 4870
  have b4870 : BlkV prof scm 4870 4892 (A246) :=
    .cons (d4870 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4874 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4878 _) (VOpI.psubb) (lt_scm (by decide)) <|
    .cons (d4882 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4886 _) (OpI.sub (.i 65535) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4892
  have b4898 : BlkV prof scm 4898 4902 (A274) :=
    .cons (d4898 _) (OpI.sub (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4902
  have b4908 : BlkV prof scm 4908 4916 (A284) :=
    .cons (d4908 _) (OpI.add (.i 16) (.inr rfl)) (lt_scm (by decide)) <|
    .cons (d4912 _) (VOpI.movdqa) (lt_scm (by decide)) <|
    .nil 4916
  have b4928 : BlkV prof scm 4928 4942 (A304 12) :=
    .cons (d4928 _) (VOpI.pcmpeqb) (lt_scm (by decide)) <|
    .cons (d4932 _) (VOpI.pmovmskb) (lt_scm (by decide)) <|
    .cons (d4936 _) (OpI.test (.i 61440) (.inl rfl)) (lt_scm (by decide)) <|
    .nil 4942
  have b4944 : BlkV prof scm 4944 4948 (A320 12) :=
    .cons (d4944 _) (OpI.cmp (.i 4) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4948
  have b4950 : BlkV prof scm 4950 4961 (A326) :=
    .cons (d4950 _) (VOpI.pxor) (lt_scm (by decide)) <|
    .cons (d4954 _) (OpI.sub (.i 4096) (.inr rfl)) (lt_scm (by decide)) <|
    .nil 4961
  have b4976 : BlkV prof scm 4976 4991 (T352 12) :=
    .cons (d4976 _) (VOpI.movdqa_mi) (lt_scm (by decide)) <|
    .cons (d4981 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .cons (d4986 _) (VOpI.psrldq) (lt_scm (by decide)) <|
    .nil 4991
  exact ⟨b4624, b4649, ⟨_, d4666 _, rfl⟩, b4672, ⟨_, d4684 _, rfl⟩, b4690, ⟨_, d4693 _, rfl⟩, b4699, b4730, b4752,
    ⟨_, d4756 _, rfl⟩, b4762, b4790, ⟨_, d4812 _, rfl⟩, b4818, ⟨_, d4822 _, rfl⟩, b4828, ⟨_, d4840 _, rfl⟩, b4842,
    b4870, ⟨_, d4892 _, rfl⟩, b4898, ⟨_, d4902 _, rfl⟩, b4908, ⟨_, d4916 _, rfl⟩, b4928, ⟨_, d4942 _, rfl⟩, b4944,
    ⟨_, d4948 _, rfl⟩, b4950, ⟨_, d4961 _, rfl⟩, (.inl ⟨b4976, _, d4991 _, rfl⟩)⟩

end FV7z.Strncmp
