import FV7z.Strncmp.AshrT
/-!
# The shifted loops `k = 13` to `15` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

theorem d5008 : ∀ feat, Dec feat scm 5008 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5012 : ∀ feat, Dec feat scm 5012 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5016 : ∀ feat, Dec feat scm 5016 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d5020 : ∀ feat, Dec feat scm 5020 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5024 : ∀ feat, Dec feat scm 5024 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 3] 5) := by dec_rfl
theorem d5029 : ∀ feat, Dec feat scm 5029 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d5033 : ∀ feat, Dec feat scm 5033 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d5037 : ∀ feat, Dec feat scm 5037 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d5042 : ∀ feat, Dec feat scm 5042 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d5044 : ∀ feat, Dec feat scm 5044 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d5047 : ∀ feat, Dec feat scm 5047 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d5050 : ∀ feat, Dec feat scm 5050 (FV7z.mk (.jcc 5) 64 [.rel 1109] 6) := by dec_rfl
theorem d5056 : ∀ feat, Dec feat scm 5056 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5060 : ∀ feat, Dec feat scm 5060
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d5065 : ∀ feat, Dec feat scm 5065 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5068 : ∀ feat, Dec feat scm 5068 (FV7z.mk (.jcc 2) 64 [.rel 1138] 6) := by dec_rfl
theorem d5074 : ∀ feat, Dec feat scm 5074 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5077 : ∀ feat, Dec feat scm 5077 (FV7z.mk (.jcc 4) 64 [.rel 1129] 6) := by dec_rfl
theorem d5083 : ∀ feat, Dec feat scm 5083 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5086 : ∀ feat, Dec feat scm 5086 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5090 : ∀ feat, Dec feat scm 5090 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d5097 : ∀ feat, Dec feat scm 5097 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 13)] 6) := by dec_rfl
theorem d5103 : ∀ feat, Dec feat scm 5103 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 13 0)] 4) := by dec_rfl
theorem d5107 : ∀ feat, Dec feat scm 5107 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d5114 : ∀ feat, Dec feat scm 5114 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d5121 : ∀ feat, Dec feat scm 5121 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d5132 : ∀ feat, Dec feat scm 5132 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d5136 : ∀ feat, Dec feat scm 5136 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5140 : ∀ feat, Dec feat scm 5140 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d5146 : ∀ feat, Dec feat scm 5146 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5151 : ∀ feat, Dec feat scm 5151 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d5156 : ∀ feat, Dec feat scm 5156 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d5160 : ∀ feat, Dec feat scm 5160 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 13] 5) := by dec_rfl
theorem d5165 : ∀ feat, Dec feat scm 5165 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 3] 5) := by dec_rfl
theorem d5170 : ∀ feat, Dec feat scm 5170 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d5174 : ∀ feat, Dec feat scm 5174 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5178 : ∀ feat, Dec feat scm 5178 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d5182 : ∀ feat, Dec feat scm 5182 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d5186 : ∀ feat, Dec feat scm 5186 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d5190 : ∀ feat, Dec feat scm 5190 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d5196 : ∀ feat, Dec feat scm 5196 (FV7z.mk (.jcc 5) 64 [.rel 958] 6) := by dec_rfl
theorem d5202 : ∀ feat, Dec feat scm 5202 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5206 : ∀ feat, Dec feat scm 5206 (FV7z.mk (.jcc 6) 64 [.rel 1000] 6) := by dec_rfl
theorem d5212 : ∀ feat, Dec feat scm 5212 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5216 : ∀ feat, Dec feat scm 5216 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d5220 : ∀ feat, Dec feat scm 5220 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5224 : ∀ feat, Dec feat scm 5224 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d5226 : ∀ feat, Dec feat scm 5226 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5231 : ∀ feat, Dec feat scm 5231 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d5236 : ∀ feat, Dec feat scm 5236 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d5240 : ∀ feat, Dec feat scm 5240 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 13] 5) := by dec_rfl
theorem d5245 : ∀ feat, Dec feat scm 5245 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 3] 5) := by dec_rfl
theorem d5250 : ∀ feat, Dec feat scm 5250 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d5254 : ∀ feat, Dec feat scm 5254 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5258 : ∀ feat, Dec feat scm 5258 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d5262 : ∀ feat, Dec feat scm 5262 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d5266 : ∀ feat, Dec feat scm 5266 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d5270 : ∀ feat, Dec feat scm 5270 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d5276 : ∀ feat, Dec feat scm 5276 (FV7z.mk (.jcc 5) 64 [.rel 878] 6) := by dec_rfl
theorem d5282 : ∀ feat, Dec feat scm 5282 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5286 : ∀ feat, Dec feat scm 5286 (FV7z.mk (.jcc 6) 64 [.rel 920] 6) := by dec_rfl
theorem d5292 : ∀ feat, Dec feat scm 5292 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5296 : ∀ feat, Dec feat scm 5296 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d5300 : ∀ feat, Dec feat scm 5300 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d5312 : ∀ feat, Dec feat scm 5312 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d5316 : ∀ feat, Dec feat scm 5316 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d5320 : ∀ feat, Dec feat scm 5320 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 57344)] 6) := by dec_rfl
theorem d5326 : ∀ feat, Dec feat scm 5326 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d5328 : ∀ feat, Dec feat scm 5328 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 3)] 4) := by dec_rfl
theorem d5332 : ∀ feat, Dec feat scm 5332 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d5334 : ∀ feat, Dec feat scm 5334 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5338 : ∀ feat, Dec feat scm 5338 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d5345 : ∀ feat, Dec feat scm 5345 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d5360 : ∀ feat, Dec feat scm 5360 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5365 : ∀ feat, Dec feat scm 5365 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 13] 5) := by dec_rfl
theorem d5370 : ∀ feat, Dec feat scm 5370 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 13] 5) := by dec_rfl
theorem d5375 : ∀ feat, Dec feat scm 5375 (FV7z.mk .jmp 64 [.rel 764] 5) := by dec_rfl

/-- The loop at `5008`, `k = 13`. -/
theorem ashr13 (prof : Profile) : AshrC prof 13 5008 4 := by
  have b5008 : BlkV prof scm 5008 5033 (A0 13) :=
    .cons (d5008 _) (VOpI.pxor) (by decide) <|
    .cons (d5012 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5016 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5020 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5024 _) (VOpI.pslldq) (by decide) <|
    .cons (d5029 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 5033
  have b5033 : BlkV prof scm 5033 5050 (A25) :=
    .cons (d5033 _) (VOpI.psubb) (by decide) <|
    .cons (d5037 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5042 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5044 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5047 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 5050
  have b5056 : BlkV prof scm 5056 5068 (A48) :=
    .cons (d5056 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5060 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5065 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 5068
  have b5074 : BlkV prof scm 5074 5077 (A66) :=
    .cons (d5074 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 5077
  have b5083 : BlkV prof scm 5083 5114 (A75 13) :=
    .cons (d5083 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d5086 _) (VOpI.pxor) (by decide) <|
    .cons (d5090 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5097 _) (OpI.mov (.i 13) (.inl rfl)) (by decide) <|
    .cons (d5103 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5107 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 5114
  have b5114 : BlkV prof scm 5114 5136 (A106) :=
    .cons (d5114 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d5121 _) (OpI.nop) (by decide) <|
    .cons (d5132 _) (OpI.nop) (by decide) <|
    .nil 5136
  have b5136 : BlkV prof scm 5136 5140 (A128) :=
    .cons (d5136 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5140
  have b5146 : BlkV prof scm 5146 5174 (A138 13) :=
    .cons (d5146 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5151 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5156 _) (VOpI.movdqa) (by decide) <|
    .cons (d5160 _) (VOpI.psrldq) (by decide) <|
    .cons (d5165 _) (VOpI.pslldq) (by decide) <|
    .cons (d5170 _) (VOpI.por) (by decide) <|
    .nil 5174
  have b5174 : BlkV prof scm 5174 5196 (A166) :=
    .cons (d5174 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5178 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5182 _) (VOpI.psubb) (by decide) <|
    .cons (d5186 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5190 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 5196
  have b5202 : BlkV prof scm 5202 5206 (A194) :=
    .cons (d5202 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 5206
  have b5212 : BlkV prof scm 5212 5224 (A204) :=
    .cons (d5212 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5216 _) (VOpI.movdqa) (by decide) <|
    .cons (d5220 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5224
  have b5226 : BlkV prof scm 5226 5254 (A218 13) :=
    .cons (d5226 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5231 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5236 _) (VOpI.movdqa) (by decide) <|
    .cons (d5240 _) (VOpI.psrldq) (by decide) <|
    .cons (d5245 _) (VOpI.pslldq) (by decide) <|
    .cons (d5250 _) (VOpI.por) (by decide) <|
    .nil 5254
  have b5254 : BlkV prof scm 5254 5276 (A246) :=
    .cons (d5254 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5258 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5262 _) (VOpI.psubb) (by decide) <|
    .cons (d5266 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5270 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 5276
  have b5282 : BlkV prof scm 5282 5286 (A274) :=
    .cons (d5282 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 5286
  have b5292 : BlkV prof scm 5292 5300 (A284) :=
    .cons (d5292 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5296 _) (VOpI.movdqa) (by decide) <|
    .nil 5300
  have b5312 : BlkV prof scm 5312 5326 (A304 13) :=
    .cons (d5312 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5316 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5320 _) (OpI.test (.i 57344) (.inl rfl)) (by decide) <|
    .nil 5326
  have b5328 : BlkV prof scm 5328 5332 (A320 13) :=
    .cons (d5328 _) (OpI.cmp (.i 3) (.inr rfl)) (by decide) <|
    .nil 5332
  have b5334 : BlkV prof scm 5334 5345 (A326) :=
    .cons (d5334 _) (VOpI.pxor) (by decide) <|
    .cons (d5338 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 5345
  have b5360 : BlkV prof scm 5360 5375 (T352 13) :=
    .cons (d5360 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5365 _) (VOpI.psrldq) (by decide) <|
    .cons (d5370 _) (VOpI.psrldq) (by decide) <|
    .nil 5375
  exact ⟨b5008, b5033, ⟨_, d5050 _, rfl⟩, b5056, ⟨_, d5068 _, rfl⟩, b5074, ⟨_, d5077 _, rfl⟩, b5083, b5114, b5136,
    ⟨_, d5140 _, rfl⟩, b5146, b5174, ⟨_, d5196 _, rfl⟩, b5202, ⟨_, d5206 _, rfl⟩, b5212, ⟨_, d5224 _, rfl⟩, b5226,
    b5254, ⟨_, d5276 _, rfl⟩, b5282, ⟨_, d5286 _, rfl⟩, b5292, ⟨_, d5300 _, rfl⟩, b5312, ⟨_, d5326 _, rfl⟩, b5328,
    ⟨_, d5332 _, rfl⟩, b5334, ⟨_, d5345 _, rfl⟩, (.inl ⟨b5360, _, d5375 _, rfl⟩)⟩

theorem d5392 : ∀ feat, Dec feat scm 5392 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5396 : ∀ feat, Dec feat scm 5396 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5400 : ∀ feat, Dec feat scm 5400 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d5404 : ∀ feat, Dec feat scm 5404 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5408 : ∀ feat, Dec feat scm 5408 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 2] 5) := by dec_rfl
theorem d5413 : ∀ feat, Dec feat scm 5413 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d5417 : ∀ feat, Dec feat scm 5417 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d5421 : ∀ feat, Dec feat scm 5421 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d5426 : ∀ feat, Dec feat scm 5426 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d5428 : ∀ feat, Dec feat scm 5428 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d5431 : ∀ feat, Dec feat scm 5431 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d5434 : ∀ feat, Dec feat scm 5434 (FV7z.mk (.jcc 5) 64 [.rel 725] 6) := by dec_rfl
theorem d5440 : ∀ feat, Dec feat scm 5440 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5444 : ∀ feat, Dec feat scm 5444
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d5449 : ∀ feat, Dec feat scm 5449 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5452 : ∀ feat, Dec feat scm 5452 (FV7z.mk (.jcc 2) 64 [.rel 754] 6) := by dec_rfl
theorem d5458 : ∀ feat, Dec feat scm 5458 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5461 : ∀ feat, Dec feat scm 5461 (FV7z.mk (.jcc 4) 64 [.rel 745] 6) := by dec_rfl
theorem d5467 : ∀ feat, Dec feat scm 5467 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5470 : ∀ feat, Dec feat scm 5470 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5474 : ∀ feat, Dec feat scm 5474 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d5481 : ∀ feat, Dec feat scm 5481 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 14)] 6) := by dec_rfl
theorem d5487 : ∀ feat, Dec feat scm 5487 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 14 0)] 4) := by dec_rfl
theorem d5491 : ∀ feat, Dec feat scm 5491 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d5498 : ∀ feat, Dec feat scm 5498 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d5505 : ∀ feat, Dec feat scm 5505 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d5516 : ∀ feat, Dec feat scm 5516 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d5520 : ∀ feat, Dec feat scm 5520 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5524 : ∀ feat, Dec feat scm 5524 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d5530 : ∀ feat, Dec feat scm 5530 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5535 : ∀ feat, Dec feat scm 5535 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d5540 : ∀ feat, Dec feat scm 5540 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d5544 : ∀ feat, Dec feat scm 5544 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 14] 5) := by dec_rfl
theorem d5549 : ∀ feat, Dec feat scm 5549 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 2] 5) := by dec_rfl
theorem d5554 : ∀ feat, Dec feat scm 5554 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d5558 : ∀ feat, Dec feat scm 5558 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5562 : ∀ feat, Dec feat scm 5562 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d5566 : ∀ feat, Dec feat scm 5566 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d5570 : ∀ feat, Dec feat scm 5570 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d5574 : ∀ feat, Dec feat scm 5574 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d5580 : ∀ feat, Dec feat scm 5580 (FV7z.mk (.jcc 5) 64 [.rel 574] 6) := by dec_rfl
theorem d5586 : ∀ feat, Dec feat scm 5586 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5590 : ∀ feat, Dec feat scm 5590 (FV7z.mk (.jcc 6) 64 [.rel 616] 6) := by dec_rfl
theorem d5596 : ∀ feat, Dec feat scm 5596 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5600 : ∀ feat, Dec feat scm 5600 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d5604 : ∀ feat, Dec feat scm 5604 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5608 : ∀ feat, Dec feat scm 5608 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d5610 : ∀ feat, Dec feat scm 5610 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5615 : ∀ feat, Dec feat scm 5615 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d5620 : ∀ feat, Dec feat scm 5620 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d5624 : ∀ feat, Dec feat scm 5624 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 14] 5) := by dec_rfl
theorem d5629 : ∀ feat, Dec feat scm 5629 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 2] 5) := by dec_rfl
theorem d5634 : ∀ feat, Dec feat scm 5634 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d5638 : ∀ feat, Dec feat scm 5638 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5642 : ∀ feat, Dec feat scm 5642 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d5646 : ∀ feat, Dec feat scm 5646 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d5650 : ∀ feat, Dec feat scm 5650 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d5654 : ∀ feat, Dec feat scm 5654 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d5660 : ∀ feat, Dec feat scm 5660 (FV7z.mk (.jcc 5) 64 [.rel 494] 6) := by dec_rfl
theorem d5666 : ∀ feat, Dec feat scm 5666 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5670 : ∀ feat, Dec feat scm 5670 (FV7z.mk (.jcc 6) 64 [.rel 536] 6) := by dec_rfl
theorem d5676 : ∀ feat, Dec feat scm 5676 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5680 : ∀ feat, Dec feat scm 5680 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d5684 : ∀ feat, Dec feat scm 5684 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d5696 : ∀ feat, Dec feat scm 5696 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d5700 : ∀ feat, Dec feat scm 5700 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d5704 : ∀ feat, Dec feat scm 5704 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 49152)] 6) := by dec_rfl
theorem d5710 : ∀ feat, Dec feat scm 5710 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d5712 : ∀ feat, Dec feat scm 5712 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem d5716 : ∀ feat, Dec feat scm 5716 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d5718 : ∀ feat, Dec feat scm 5718 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5722 : ∀ feat, Dec feat scm 5722 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d5729 : ∀ feat, Dec feat scm 5729 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d5744 : ∀ feat, Dec feat scm 5744 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5749 : ∀ feat, Dec feat scm 5749 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 14] 5) := by dec_rfl
theorem d5754 : ∀ feat, Dec feat scm 5754 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 14] 5) := by dec_rfl
theorem d5759 : ∀ feat, Dec feat scm 5759 (FV7z.mk .jmp 64 [.rel 380] 5) := by dec_rfl

/-- The loop at `5392`, `k = 14`. -/
theorem ashr14 (prof : Profile) : AshrC prof 14 5392 4 := by
  have b5392 : BlkV prof scm 5392 5417 (A0 14) :=
    .cons (d5392 _) (VOpI.pxor) (by decide) <|
    .cons (d5396 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5400 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5404 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5408 _) (VOpI.pslldq) (by decide) <|
    .cons (d5413 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 5417
  have b5417 : BlkV prof scm 5417 5434 (A25) :=
    .cons (d5417 _) (VOpI.psubb) (by decide) <|
    .cons (d5421 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5426 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5428 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5431 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 5434
  have b5440 : BlkV prof scm 5440 5452 (A48) :=
    .cons (d5440 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5444 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5449 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 5452
  have b5458 : BlkV prof scm 5458 5461 (A66) :=
    .cons (d5458 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 5461
  have b5467 : BlkV prof scm 5467 5498 (A75 14) :=
    .cons (d5467 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d5470 _) (VOpI.pxor) (by decide) <|
    .cons (d5474 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5481 _) (OpI.mov (.i 14) (.inl rfl)) (by decide) <|
    .cons (d5487 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5491 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 5498
  have b5498 : BlkV prof scm 5498 5520 (A106) :=
    .cons (d5498 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d5505 _) (OpI.nop) (by decide) <|
    .cons (d5516 _) (OpI.nop) (by decide) <|
    .nil 5520
  have b5520 : BlkV prof scm 5520 5524 (A128) :=
    .cons (d5520 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5524
  have b5530 : BlkV prof scm 5530 5558 (A138 14) :=
    .cons (d5530 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5535 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5540 _) (VOpI.movdqa) (by decide) <|
    .cons (d5544 _) (VOpI.psrldq) (by decide) <|
    .cons (d5549 _) (VOpI.pslldq) (by decide) <|
    .cons (d5554 _) (VOpI.por) (by decide) <|
    .nil 5558
  have b5558 : BlkV prof scm 5558 5580 (A166) :=
    .cons (d5558 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5562 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5566 _) (VOpI.psubb) (by decide) <|
    .cons (d5570 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5574 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 5580
  have b5586 : BlkV prof scm 5586 5590 (A194) :=
    .cons (d5586 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 5590
  have b5596 : BlkV prof scm 5596 5608 (A204) :=
    .cons (d5596 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5600 _) (VOpI.movdqa) (by decide) <|
    .cons (d5604 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5608
  have b5610 : BlkV prof scm 5610 5638 (A218 14) :=
    .cons (d5610 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5615 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5620 _) (VOpI.movdqa) (by decide) <|
    .cons (d5624 _) (VOpI.psrldq) (by decide) <|
    .cons (d5629 _) (VOpI.pslldq) (by decide) <|
    .cons (d5634 _) (VOpI.por) (by decide) <|
    .nil 5638
  have b5638 : BlkV prof scm 5638 5660 (A246) :=
    .cons (d5638 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5642 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5646 _) (VOpI.psubb) (by decide) <|
    .cons (d5650 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5654 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 5660
  have b5666 : BlkV prof scm 5666 5670 (A274) :=
    .cons (d5666 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 5670
  have b5676 : BlkV prof scm 5676 5684 (A284) :=
    .cons (d5676 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5680 _) (VOpI.movdqa) (by decide) <|
    .nil 5684
  have b5696 : BlkV prof scm 5696 5710 (A304 14) :=
    .cons (d5696 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5700 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5704 _) (OpI.test (.i 49152) (.inl rfl)) (by decide) <|
    .nil 5710
  have b5712 : BlkV prof scm 5712 5716 (A320 14) :=
    .cons (d5712 _) (OpI.cmp (.i 2) (.inr rfl)) (by decide) <|
    .nil 5716
  have b5718 : BlkV prof scm 5718 5729 (A326) :=
    .cons (d5718 _) (VOpI.pxor) (by decide) <|
    .cons (d5722 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 5729
  have b5744 : BlkV prof scm 5744 5759 (T352 14) :=
    .cons (d5744 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5749 _) (VOpI.psrldq) (by decide) <|
    .cons (d5754 _) (VOpI.psrldq) (by decide) <|
    .nil 5759
  exact ⟨b5392, b5417, ⟨_, d5434 _, rfl⟩, b5440, ⟨_, d5452 _, rfl⟩, b5458, ⟨_, d5461 _, rfl⟩, b5467, b5498, b5520,
    ⟨_, d5524 _, rfl⟩, b5530, b5558, ⟨_, d5580 _, rfl⟩, b5586, ⟨_, d5590 _, rfl⟩, b5596, ⟨_, d5608 _, rfl⟩, b5610,
    b5638, ⟨_, d5660 _, rfl⟩, b5666, ⟨_, d5670 _, rfl⟩, b5676, ⟨_, d5684 _, rfl⟩, b5696, ⟨_, d5710 _, rfl⟩, b5712,
    ⟨_, d5716 _, rfl⟩, b5718, ⟨_, d5729 _, rfl⟩, (.inl ⟨b5744, _, d5759 _, rfl⟩)⟩

theorem d5776 : ∀ feat, Dec feat scm 5776 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5780 : ∀ feat, Dec feat scm 5780 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5784 : ∀ feat, Dec feat scm 5784 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d5788 : ∀ feat, Dec feat scm 5788 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5792 : ∀ feat, Dec feat scm 5792 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 1] 5) := by dec_rfl
theorem d5797 : ∀ feat, Dec feat scm 5797 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d5801 : ∀ feat, Dec feat scm 5801 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d5805 : ∀ feat, Dec feat scm 5805 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d5810 : ∀ feat, Dec feat scm 5810 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d5812 : ∀ feat, Dec feat scm 5812 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d5815 : ∀ feat, Dec feat scm 5815 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d5818 : ∀ feat, Dec feat scm 5818 (FV7z.mk (.jcc 5) 64 [.rel 341] 6) := by dec_rfl
theorem d5824 : ∀ feat, Dec feat scm 5824 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d5828 : ∀ feat, Dec feat scm 5828
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d5833 : ∀ feat, Dec feat scm 5833 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5836 : ∀ feat, Dec feat scm 5836 (FV7z.mk (.jcc 2) 64 [.rel 370] 6) := by dec_rfl
theorem d5842 : ∀ feat, Dec feat scm 5842 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5845 : ∀ feat, Dec feat scm 5845 (FV7z.mk (.jcc 4) 64 [.rel 361] 6) := by dec_rfl
theorem d5851 : ∀ feat, Dec feat scm 5851 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d5854 : ∀ feat, Dec feat scm 5854 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d5858 : ∀ feat, Dec feat scm 5858 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d5865 : ∀ feat, Dec feat scm 5865 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 15)] 6) := by dec_rfl
theorem d5871 : ∀ feat, Dec feat scm 5871 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 15 0)] 4) := by dec_rfl
theorem d5875 : ∀ feat, Dec feat scm 5875 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d5882 : ∀ feat, Dec feat scm 5882 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d5889 : ∀ feat, Dec feat scm 5889 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d5900 : ∀ feat, Dec feat scm 5900 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d5904 : ∀ feat, Dec feat scm 5904 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5908 : ∀ feat, Dec feat scm 5908 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d5914 : ∀ feat, Dec feat scm 5914 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5919 : ∀ feat, Dec feat scm 5919 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d5924 : ∀ feat, Dec feat scm 5924 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d5928 : ∀ feat, Dec feat scm 5928 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 15] 5) := by dec_rfl
theorem d5933 : ∀ feat, Dec feat scm 5933 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 1] 5) := by dec_rfl
theorem d5938 : ∀ feat, Dec feat scm 5938 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d5942 : ∀ feat, Dec feat scm 5942 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d5946 : ∀ feat, Dec feat scm 5946 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d5950 : ∀ feat, Dec feat scm 5950 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d5954 : ∀ feat, Dec feat scm 5954 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d5958 : ∀ feat, Dec feat scm 5958 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d5964 : ∀ feat, Dec feat scm 5964 (FV7z.mk (.jcc 5) 64 [.rel 190] 6) := by dec_rfl
theorem d5970 : ∀ feat, Dec feat scm 5970 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5974 : ∀ feat, Dec feat scm 5974 (FV7z.mk (.jcc 6) 64 [.rel 232] 6) := by dec_rfl
theorem d5980 : ∀ feat, Dec feat scm 5980 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5984 : ∀ feat, Dec feat scm 5984 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d5988 : ∀ feat, Dec feat scm 5988 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d5992 : ∀ feat, Dec feat scm 5992 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d5994 : ∀ feat, Dec feat scm 5994 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d5999 : ∀ feat, Dec feat scm 5999 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d6004 : ∀ feat, Dec feat scm 6004 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d6008 : ∀ feat, Dec feat scm 6008 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 15] 5) := by dec_rfl
theorem d6013 : ∀ feat, Dec feat scm 6013 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 1] 5) := by dec_rfl
theorem d6018 : ∀ feat, Dec feat scm 6018 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d6022 : ∀ feat, Dec feat scm 6022 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d6026 : ∀ feat, Dec feat scm 6026 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d6030 : ∀ feat, Dec feat scm 6030 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d6034 : ∀ feat, Dec feat scm 6034 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d6038 : ∀ feat, Dec feat scm 6038 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d6044 : ∀ feat, Dec feat scm 6044 (FV7z.mk (.jcc 5) 64 [.rel 114] 2) := by dec_rfl
theorem d6046 : ∀ feat, Dec feat scm 6046 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d6050 : ∀ feat, Dec feat scm 6050 (FV7z.mk (.jcc 6) 64 [.rel 156] 6) := by dec_rfl
theorem d6056 : ∀ feat, Dec feat scm 6056 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d6060 : ∀ feat, Dec feat scm 6060 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d6064 : ∀ feat, Dec feat scm 6064 (FV7z.mk .jmp 64 [.rel 18446744073709551451] 5) := by dec_rfl
theorem d6080 : ∀ feat, Dec feat scm 6080 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d6084 : ∀ feat, Dec feat scm 6084 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d6088 : ∀ feat, Dec feat scm 6088 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 32768)] 6) := by dec_rfl
theorem d6094 : ∀ feat, Dec feat scm 6094 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d6096 : ∀ feat, Dec feat scm 6096 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem d6100 : ∀ feat, Dec feat scm 6100 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d6102 : ∀ feat, Dec feat scm 6102 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d6106 : ∀ feat, Dec feat scm 6106 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d6113 : ∀ feat, Dec feat scm 6113 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d6128 : ∀ feat, Dec feat scm 6128 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d6133 : ∀ feat, Dec feat scm 6133 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 15] 5) := by dec_rfl
theorem d6138 : ∀ feat, Dec feat scm 6138 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 15] 5) := by dec_rfl
theorem d6143 : ∀ feat, Dec feat scm 6143 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- The loop at `5776`, `k = 15`. -/
theorem ashr15 (prof : Profile) : AshrC prof 15 5776 0 := by
  have b5776 : BlkV prof scm 5776 5801 (A0 15) :=
    .cons (d5776 _) (VOpI.pxor) (by decide) <|
    .cons (d5780 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5784 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5788 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5792 _) (VOpI.pslldq) (by decide) <|
    .cons (d5797 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 5801
  have b5801 : BlkV prof scm 5801 5818 (A25) :=
    .cons (d5801 _) (VOpI.psubb) (by decide) <|
    .cons (d5805 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5810 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5812 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d5815 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 5818
  have b5824 : BlkV prof scm 5824 5836 (A48) :=
    .cons (d5824 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d5828 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5833 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 5836
  have b5842 : BlkV prof scm 5842 5845 (A66) :=
    .cons (d5842 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 5845
  have b5851 : BlkV prof scm 5851 5882 (A75 15) :=
    .cons (d5851 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d5854 _) (VOpI.pxor) (by decide) <|
    .cons (d5858 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5865 _) (OpI.mov (.i 15) (.inl rfl)) (by decide) <|
    .cons (d5871 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d5875 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 5882
  have b5882 : BlkV prof scm 5882 5904 (A106) :=
    .cons (d5882 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d5889 _) (OpI.nop) (by decide) <|
    .cons (d5900 _) (OpI.nop) (by decide) <|
    .nil 5904
  have b5904 : BlkV prof scm 5904 5908 (A128) :=
    .cons (d5904 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5908
  have b5914 : BlkV prof scm 5914 5942 (A138 15) :=
    .cons (d5914 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5919 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5924 _) (VOpI.movdqa) (by decide) <|
    .cons (d5928 _) (VOpI.psrldq) (by decide) <|
    .cons (d5933 _) (VOpI.pslldq) (by decide) <|
    .cons (d5938 _) (VOpI.por) (by decide) <|
    .nil 5942
  have b5942 : BlkV prof scm 5942 5964 (A166) :=
    .cons (d5942 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5946 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d5950 _) (VOpI.psubb) (by decide) <|
    .cons (d5954 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d5958 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 5964
  have b5970 : BlkV prof scm 5970 5974 (A194) :=
    .cons (d5970 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 5974
  have b5980 : BlkV prof scm 5980 5992 (A204) :=
    .cons (d5980 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d5984 _) (VOpI.movdqa) (by decide) <|
    .cons (d5988 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 5992
  have b5994 : BlkV prof scm 5994 6022 (A218 15) :=
    .cons (d5994 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d5999 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d6004 _) (VOpI.movdqa) (by decide) <|
    .cons (d6008 _) (VOpI.psrldq) (by decide) <|
    .cons (d6013 _) (VOpI.pslldq) (by decide) <|
    .cons (d6018 _) (VOpI.por) (by decide) <|
    .nil 6022
  have b6022 : BlkV prof scm 6022 6044 (A246) :=
    .cons (d6022 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d6026 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d6030 _) (VOpI.psubb) (by decide) <|
    .cons (d6034 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d6038 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 6044
  have b6046 : BlkV prof scm 6046 6050 (A274) :=
    .cons (d6046 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 6050
  have b6056 : BlkV prof scm 6056 6064 (A284) :=
    .cons (d6056 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d6060 _) (VOpI.movdqa) (by decide) <|
    .nil 6064
  have b6080 : BlkV prof scm 6080 6094 (A304 15) :=
    .cons (d6080 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d6084 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d6088 _) (OpI.test (.i 32768) (.inl rfl)) (by decide) <|
    .nil 6094
  have b6096 : BlkV prof scm 6096 6100 (A320 15) :=
    .cons (d6096 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
    .nil 6100
  have b6102 : BlkV prof scm 6102 6113 (A326) :=
    .cons (d6102 _) (VOpI.pxor) (by decide) <|
    .cons (d6106 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 6113
  have b6128 : BlkV prof scm 6128 6144 (T352s 15) :=
    .cons (d6128 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d6133 _) (VOpI.psrldq) (by decide) <|
    .cons (d6138 _) (VOpI.psrldq) (by decide) <|
    .cons (d6143 _) (OpI.nop) (by decide) <|
    .nil 6144
  exact ⟨b5776, b5801, ⟨_, d5818 _, rfl⟩, b5824, ⟨_, d5836 _, rfl⟩, b5842, ⟨_, d5845 _, rfl⟩, b5851, b5882, b5904,
    ⟨_, d5908 _, rfl⟩, b5914, b5942, ⟨_, d5964 _, rfl⟩, b5970, ⟨_, d5974 _, rfl⟩, b5980, ⟨_, d5992 _, rfl⟩, b5994,
    b6022, ⟨_, d6044 _, rfl⟩, b6046, ⟨_, d6050 _, rfl⟩, b6056, ⟨_, d6064 _, rfl⟩, b6080, ⟨_, d6094 _, rfl⟩, b6096,
    ⟨_, d6100 _, rfl⟩, b6102, ⟨_, d6113 _, rfl⟩, (.inr ⟨b6128, rfl⟩)⟩

end FV7z.Strncmp
