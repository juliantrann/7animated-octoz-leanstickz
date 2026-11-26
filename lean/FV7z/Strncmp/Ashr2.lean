import FV7z.Strncmp.AshrT
/-!
# The shifted loops `k = 4` to `6` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

theorem d1552 : ∀ feat, Dec feat scm 1552 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1556 : ∀ feat, Dec feat scm 1556 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1560 : ∀ feat, Dec feat scm 1560 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d1564 : ∀ feat, Dec feat scm 1564 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1568 : ∀ feat, Dec feat scm 1568 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 12] 5) := by dec_rfl
theorem d1573 : ∀ feat, Dec feat scm 1573 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d1577 : ∀ feat, Dec feat scm 1577 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d1581 : ∀ feat, Dec feat scm 1581 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d1586 : ∀ feat, Dec feat scm 1586 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d1588 : ∀ feat, Dec feat scm 1588 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d1591 : ∀ feat, Dec feat scm 1591 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d1594 : ∀ feat, Dec feat scm 1594 (FV7z.mk (.jcc 5) 64 [.rel 4565] 6) := by dec_rfl
theorem d1600 : ∀ feat, Dec feat scm 1600 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1604 : ∀ feat, Dec feat scm 1604
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d1609 : ∀ feat, Dec feat scm 1609 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1612 : ∀ feat, Dec feat scm 1612 (FV7z.mk (.jcc 2) 64 [.rel 4594] 6) := by dec_rfl
theorem d1618 : ∀ feat, Dec feat scm 1618 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1621 : ∀ feat, Dec feat scm 1621 (FV7z.mk (.jcc 4) 64 [.rel 4585] 6) := by dec_rfl
theorem d1627 : ∀ feat, Dec feat scm 1627 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1630 : ∀ feat, Dec feat scm 1630 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1634 : ∀ feat, Dec feat scm 1634 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d1641 : ∀ feat, Dec feat scm 1641 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 4)] 6) := by dec_rfl
theorem d1647 : ∀ feat, Dec feat scm 1647 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 4 0)] 4) := by dec_rfl
theorem d1651 : ∀ feat, Dec feat scm 1651 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d1658 : ∀ feat, Dec feat scm 1658 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d1665 : ∀ feat, Dec feat scm 1665 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d1676 : ∀ feat, Dec feat scm 1676 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d1680 : ∀ feat, Dec feat scm 1680 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1684 : ∀ feat, Dec feat scm 1684 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d1690 : ∀ feat, Dec feat scm 1690 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1695 : ∀ feat, Dec feat scm 1695 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d1700 : ∀ feat, Dec feat scm 1700 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d1704 : ∀ feat, Dec feat scm 1704 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 4] 5) := by dec_rfl
theorem d1709 : ∀ feat, Dec feat scm 1709 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 12] 5) := by dec_rfl
theorem d1714 : ∀ feat, Dec feat scm 1714 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d1718 : ∀ feat, Dec feat scm 1718 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1722 : ∀ feat, Dec feat scm 1722 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d1726 : ∀ feat, Dec feat scm 1726 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d1730 : ∀ feat, Dec feat scm 1730 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d1734 : ∀ feat, Dec feat scm 1734 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d1740 : ∀ feat, Dec feat scm 1740 (FV7z.mk (.jcc 5) 64 [.rel 4414] 6) := by dec_rfl
theorem d1746 : ∀ feat, Dec feat scm 1746 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1750 : ∀ feat, Dec feat scm 1750 (FV7z.mk (.jcc 6) 64 [.rel 4456] 6) := by dec_rfl
theorem d1756 : ∀ feat, Dec feat scm 1756 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1760 : ∀ feat, Dec feat scm 1760 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d1764 : ∀ feat, Dec feat scm 1764 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1768 : ∀ feat, Dec feat scm 1768 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d1770 : ∀ feat, Dec feat scm 1770 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1775 : ∀ feat, Dec feat scm 1775 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d1780 : ∀ feat, Dec feat scm 1780 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d1784 : ∀ feat, Dec feat scm 1784 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 4] 5) := by dec_rfl
theorem d1789 : ∀ feat, Dec feat scm 1789 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 12] 5) := by dec_rfl
theorem d1794 : ∀ feat, Dec feat scm 1794 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d1798 : ∀ feat, Dec feat scm 1798 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1802 : ∀ feat, Dec feat scm 1802 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d1806 : ∀ feat, Dec feat scm 1806 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d1810 : ∀ feat, Dec feat scm 1810 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d1814 : ∀ feat, Dec feat scm 1814 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d1820 : ∀ feat, Dec feat scm 1820 (FV7z.mk (.jcc 5) 64 [.rel 4334] 6) := by dec_rfl
theorem d1826 : ∀ feat, Dec feat scm 1826 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1830 : ∀ feat, Dec feat scm 1830 (FV7z.mk (.jcc 6) 64 [.rel 4376] 6) := by dec_rfl
theorem d1836 : ∀ feat, Dec feat scm 1836 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d1840 : ∀ feat, Dec feat scm 1840 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d1844 : ∀ feat, Dec feat scm 1844 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d1856 : ∀ feat, Dec feat scm 1856 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d1860 : ∀ feat, Dec feat scm 1860 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d1864 : ∀ feat, Dec feat scm 1864 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65520)] 6) := by dec_rfl
theorem d1870 : ∀ feat, Dec feat scm 1870 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d1872 : ∀ feat, Dec feat scm 1872 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 12)] 4) := by dec_rfl
theorem d1876 : ∀ feat, Dec feat scm 1876 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d1878 : ∀ feat, Dec feat scm 1878 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1882 : ∀ feat, Dec feat scm 1882 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d1889 : ∀ feat, Dec feat scm 1889 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d1904 : ∀ feat, Dec feat scm 1904 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d1909 : ∀ feat, Dec feat scm 1909 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 4] 5) := by dec_rfl
theorem d1914 : ∀ feat, Dec feat scm 1914 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 4] 5) := by dec_rfl
theorem d1919 : ∀ feat, Dec feat scm 1919 (FV7z.mk .jmp 64 [.rel 4220] 5) := by dec_rfl

/-- The loop at `1552`, `k = 4`. -/
theorem ashr4 (prof : Profile) : AshrC prof 4 1552 4 := by
  have b1552 : BlkV prof scm 1552 1577 (A0 4) :=
    .cons (d1552 _) (VOpI.pxor) (by decide) <|
    .cons (d1556 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1560 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1564 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1568 _) (VOpI.pslldq) (by decide) <|
    .cons (d1573 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 1577
  have b1577 : BlkV prof scm 1577 1594 (A25) :=
    .cons (d1577 _) (VOpI.psubb) (by decide) <|
    .cons (d1581 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1586 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1588 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1591 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 1594
  have b1600 : BlkV prof scm 1600 1612 (A48) :=
    .cons (d1600 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1604 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d1609 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 1612
  have b1618 : BlkV prof scm 1618 1621 (A66) :=
    .cons (d1618 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 1621
  have b1627 : BlkV prof scm 1627 1658 (A75 4) :=
    .cons (d1627 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d1630 _) (VOpI.pxor) (by decide) <|
    .cons (d1634 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1641 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
    .cons (d1647 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d1651 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 1658
  have b1658 : BlkV prof scm 1658 1680 (A106) :=
    .cons (d1658 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d1665 _) (OpI.nop) (by decide) <|
    .cons (d1676 _) (OpI.nop) (by decide) <|
    .nil 1680
  have b1680 : BlkV prof scm 1680 1684 (A128) :=
    .cons (d1680 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 1684
  have b1690 : BlkV prof scm 1690 1718 (A138 4) :=
    .cons (d1690 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1695 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1700 _) (VOpI.movdqa) (by decide) <|
    .cons (d1704 _) (VOpI.psrldq) (by decide) <|
    .cons (d1709 _) (VOpI.pslldq) (by decide) <|
    .cons (d1714 _) (VOpI.por) (by decide) <|
    .nil 1718
  have b1718 : BlkV prof scm 1718 1740 (A166) :=
    .cons (d1718 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1722 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1726 _) (VOpI.psubb) (by decide) <|
    .cons (d1730 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1734 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 1740
  have b1746 : BlkV prof scm 1746 1750 (A194) :=
    .cons (d1746 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 1750
  have b1756 : BlkV prof scm 1756 1768 (A204) :=
    .cons (d1756 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1760 _) (VOpI.movdqa) (by decide) <|
    .cons (d1764 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 1768
  have b1770 : BlkV prof scm 1770 1798 (A218 4) :=
    .cons (d1770 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1775 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1780 _) (VOpI.movdqa) (by decide) <|
    .cons (d1784 _) (VOpI.psrldq) (by decide) <|
    .cons (d1789 _) (VOpI.pslldq) (by decide) <|
    .cons (d1794 _) (VOpI.por) (by decide) <|
    .nil 1798
  have b1798 : BlkV prof scm 1798 1820 (A246) :=
    .cons (d1798 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1802 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1806 _) (VOpI.psubb) (by decide) <|
    .cons (d1810 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1814 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 1820
  have b1826 : BlkV prof scm 1826 1830 (A274) :=
    .cons (d1826 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 1830
  have b1836 : BlkV prof scm 1836 1844 (A284) :=
    .cons (d1836 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d1840 _) (VOpI.movdqa) (by decide) <|
    .nil 1844
  have b1856 : BlkV prof scm 1856 1870 (A304 4) :=
    .cons (d1856 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1860 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1864 _) (OpI.test (.i 65520) (.inl rfl)) (by decide) <|
    .nil 1870
  have b1872 : BlkV prof scm 1872 1876 (A320 4) :=
    .cons (d1872 _) (OpI.cmp (.i 12) (.inr rfl)) (by decide) <|
    .nil 1876
  have b1878 : BlkV prof scm 1878 1889 (A326) :=
    .cons (d1878 _) (VOpI.pxor) (by decide) <|
    .cons (d1882 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 1889
  have b1904 : BlkV prof scm 1904 1919 (T352 4) :=
    .cons (d1904 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d1909 _) (VOpI.psrldq) (by decide) <|
    .cons (d1914 _) (VOpI.psrldq) (by decide) <|
    .nil 1919
  exact ⟨b1552, b1577, ⟨_, d1594 _, rfl⟩, b1600, ⟨_, d1612 _, rfl⟩, b1618, ⟨_, d1621 _, rfl⟩, b1627, b1658, b1680,
    ⟨_, d1684 _, rfl⟩, b1690, b1718, ⟨_, d1740 _, rfl⟩, b1746, ⟨_, d1750 _, rfl⟩, b1756, ⟨_, d1768 _, rfl⟩, b1770,
    b1798, ⟨_, d1820 _, rfl⟩, b1826, ⟨_, d1830 _, rfl⟩, b1836, ⟨_, d1844 _, rfl⟩, b1856, ⟨_, d1870 _, rfl⟩, b1872,
    ⟨_, d1876 _, rfl⟩, b1878, ⟨_, d1889 _, rfl⟩, (.inl ⟨b1904, _, d1919 _, rfl⟩)⟩

theorem d1936 : ∀ feat, Dec feat scm 1936 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d1940 : ∀ feat, Dec feat scm 1940 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1944 : ∀ feat, Dec feat scm 1944 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d1948 : ∀ feat, Dec feat scm 1948 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d1952 : ∀ feat, Dec feat scm 1952 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 11] 5) := by dec_rfl
theorem d1957 : ∀ feat, Dec feat scm 1957 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d1961 : ∀ feat, Dec feat scm 1961 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d1965 : ∀ feat, Dec feat scm 1965 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d1970 : ∀ feat, Dec feat scm 1970 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d1972 : ∀ feat, Dec feat scm 1972 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d1975 : ∀ feat, Dec feat scm 1975 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d1978 : ∀ feat, Dec feat scm 1978 (FV7z.mk (.jcc 5) 64 [.rel 4181] 6) := by dec_rfl
theorem d1984 : ∀ feat, Dec feat scm 1984 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d1988 : ∀ feat, Dec feat scm 1988
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d1993 : ∀ feat, Dec feat scm 1993 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d1996 : ∀ feat, Dec feat scm 1996 (FV7z.mk (.jcc 2) 64 [.rel 4210] 6) := by dec_rfl
theorem d2002 : ∀ feat, Dec feat scm 2002 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2005 : ∀ feat, Dec feat scm 2005 (FV7z.mk (.jcc 4) 64 [.rel 4201] 6) := by dec_rfl
theorem d2011 : ∀ feat, Dec feat scm 2011 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2014 : ∀ feat, Dec feat scm 2014 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2018 : ∀ feat, Dec feat scm 2018 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d2025 : ∀ feat, Dec feat scm 2025 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 5)] 6) := by dec_rfl
theorem d2031 : ∀ feat, Dec feat scm 2031 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 5 0)] 4) := by dec_rfl
theorem d2035 : ∀ feat, Dec feat scm 2035 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d2042 : ∀ feat, Dec feat scm 2042 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d2049 : ∀ feat, Dec feat scm 2049 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d2060 : ∀ feat, Dec feat scm 2060 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d2064 : ∀ feat, Dec feat scm 2064 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2068 : ∀ feat, Dec feat scm 2068 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d2074 : ∀ feat, Dec feat scm 2074 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2079 : ∀ feat, Dec feat scm 2079 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2084 : ∀ feat, Dec feat scm 2084 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2088 : ∀ feat, Dec feat scm 2088 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 5] 5) := by dec_rfl
theorem d2093 : ∀ feat, Dec feat scm 2093 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 11] 5) := by dec_rfl
theorem d2098 : ∀ feat, Dec feat scm 2098 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2102 : ∀ feat, Dec feat scm 2102 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2106 : ∀ feat, Dec feat scm 2106 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2110 : ∀ feat, Dec feat scm 2110 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2114 : ∀ feat, Dec feat scm 2114 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2118 : ∀ feat, Dec feat scm 2118 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2124 : ∀ feat, Dec feat scm 2124 (FV7z.mk (.jcc 5) 64 [.rel 4030] 6) := by dec_rfl
theorem d2130 : ∀ feat, Dec feat scm 2130 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2134 : ∀ feat, Dec feat scm 2134 (FV7z.mk (.jcc 6) 64 [.rel 4072] 6) := by dec_rfl
theorem d2140 : ∀ feat, Dec feat scm 2140 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2144 : ∀ feat, Dec feat scm 2144 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2148 : ∀ feat, Dec feat scm 2148 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2152 : ∀ feat, Dec feat scm 2152 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d2154 : ∀ feat, Dec feat scm 2154 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2159 : ∀ feat, Dec feat scm 2159 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2164 : ∀ feat, Dec feat scm 2164 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2168 : ∀ feat, Dec feat scm 2168 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 5] 5) := by dec_rfl
theorem d2173 : ∀ feat, Dec feat scm 2173 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 11] 5) := by dec_rfl
theorem d2178 : ∀ feat, Dec feat scm 2178 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2182 : ∀ feat, Dec feat scm 2182 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2186 : ∀ feat, Dec feat scm 2186 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2190 : ∀ feat, Dec feat scm 2190 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2194 : ∀ feat, Dec feat scm 2194 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2198 : ∀ feat, Dec feat scm 2198 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2204 : ∀ feat, Dec feat scm 2204 (FV7z.mk (.jcc 5) 64 [.rel 3950] 6) := by dec_rfl
theorem d2210 : ∀ feat, Dec feat scm 2210 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2214 : ∀ feat, Dec feat scm 2214 (FV7z.mk (.jcc 6) 64 [.rel 3992] 6) := by dec_rfl
theorem d2220 : ∀ feat, Dec feat scm 2220 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2224 : ∀ feat, Dec feat scm 2224 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2228 : ∀ feat, Dec feat scm 2228 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d2240 : ∀ feat, Dec feat scm 2240 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d2244 : ∀ feat, Dec feat scm 2244 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d2248 : ∀ feat, Dec feat scm 2248 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65504)] 6) := by dec_rfl
theorem d2254 : ∀ feat, Dec feat scm 2254 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d2256 : ∀ feat, Dec feat scm 2256 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 11)] 4) := by dec_rfl
theorem d2260 : ∀ feat, Dec feat scm 2260 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d2262 : ∀ feat, Dec feat scm 2262 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2266 : ∀ feat, Dec feat scm 2266 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d2273 : ∀ feat, Dec feat scm 2273 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d2288 : ∀ feat, Dec feat scm 2288 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2293 : ∀ feat, Dec feat scm 2293 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 5] 5) := by dec_rfl
theorem d2298 : ∀ feat, Dec feat scm 2298 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 5] 5) := by dec_rfl
theorem d2303 : ∀ feat, Dec feat scm 2303 (FV7z.mk .jmp 64 [.rel 3836] 5) := by dec_rfl

/-- The loop at `1936`, `k = 5`. -/
theorem ashr5 (prof : Profile) : AshrC prof 5 1936 4 := by
  have b1936 : BlkV prof scm 1936 1961 (A0 5) :=
    .cons (d1936 _) (VOpI.pxor) (by decide) <|
    .cons (d1940 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1944 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1948 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d1952 _) (VOpI.pslldq) (by decide) <|
    .cons (d1957 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 1961
  have b1961 : BlkV prof scm 1961 1978 (A25) :=
    .cons (d1961 _) (VOpI.psubb) (by decide) <|
    .cons (d1965 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d1970 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1972 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d1975 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 1978
  have b1984 : BlkV prof scm 1984 1996 (A48) :=
    .cons (d1984 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d1988 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d1993 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 1996
  have b2002 : BlkV prof scm 2002 2005 (A66) :=
    .cons (d2002 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 2005
  have b2011 : BlkV prof scm 2011 2042 (A75 5) :=
    .cons (d2011 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d2014 _) (VOpI.pxor) (by decide) <|
    .cons (d2018 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2025 _) (OpI.mov (.i 5) (.inl rfl)) (by decide) <|
    .cons (d2031 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d2035 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 2042
  have b2042 : BlkV prof scm 2042 2064 (A106) :=
    .cons (d2042 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d2049 _) (OpI.nop) (by decide) <|
    .cons (d2060 _) (OpI.nop) (by decide) <|
    .nil 2064
  have b2064 : BlkV prof scm 2064 2068 (A128) :=
    .cons (d2064 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2068
  have b2074 : BlkV prof scm 2074 2102 (A138 5) :=
    .cons (d2074 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2079 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2084 _) (VOpI.movdqa) (by decide) <|
    .cons (d2088 _) (VOpI.psrldq) (by decide) <|
    .cons (d2093 _) (VOpI.pslldq) (by decide) <|
    .cons (d2098 _) (VOpI.por) (by decide) <|
    .nil 2102
  have b2102 : BlkV prof scm 2102 2124 (A166) :=
    .cons (d2102 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2106 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2110 _) (VOpI.psubb) (by decide) <|
    .cons (d2114 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2118 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2124
  have b2130 : BlkV prof scm 2130 2134 (A194) :=
    .cons (d2130 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2134
  have b2140 : BlkV prof scm 2140 2152 (A204) :=
    .cons (d2140 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2144 _) (VOpI.movdqa) (by decide) <|
    .cons (d2148 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2152
  have b2154 : BlkV prof scm 2154 2182 (A218 5) :=
    .cons (d2154 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2159 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2164 _) (VOpI.movdqa) (by decide) <|
    .cons (d2168 _) (VOpI.psrldq) (by decide) <|
    .cons (d2173 _) (VOpI.pslldq) (by decide) <|
    .cons (d2178 _) (VOpI.por) (by decide) <|
    .nil 2182
  have b2182 : BlkV prof scm 2182 2204 (A246) :=
    .cons (d2182 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2186 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2190 _) (VOpI.psubb) (by decide) <|
    .cons (d2194 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2198 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2204
  have b2210 : BlkV prof scm 2210 2214 (A274) :=
    .cons (d2210 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2214
  have b2220 : BlkV prof scm 2220 2228 (A284) :=
    .cons (d2220 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2224 _) (VOpI.movdqa) (by decide) <|
    .nil 2228
  have b2240 : BlkV prof scm 2240 2254 (A304 5) :=
    .cons (d2240 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2244 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2248 _) (OpI.test (.i 65504) (.inl rfl)) (by decide) <|
    .nil 2254
  have b2256 : BlkV prof scm 2256 2260 (A320 5) :=
    .cons (d2256 _) (OpI.cmp (.i 11) (.inr rfl)) (by decide) <|
    .nil 2260
  have b2262 : BlkV prof scm 2262 2273 (A326) :=
    .cons (d2262 _) (VOpI.pxor) (by decide) <|
    .cons (d2266 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 2273
  have b2288 : BlkV prof scm 2288 2303 (T352 5) :=
    .cons (d2288 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2293 _) (VOpI.psrldq) (by decide) <|
    .cons (d2298 _) (VOpI.psrldq) (by decide) <|
    .nil 2303
  exact ⟨b1936, b1961, ⟨_, d1978 _, rfl⟩, b1984, ⟨_, d1996 _, rfl⟩, b2002, ⟨_, d2005 _, rfl⟩, b2011, b2042, b2064,
    ⟨_, d2068 _, rfl⟩, b2074, b2102, ⟨_, d2124 _, rfl⟩, b2130, ⟨_, d2134 _, rfl⟩, b2140, ⟨_, d2152 _, rfl⟩, b2154,
    b2182, ⟨_, d2204 _, rfl⟩, b2210, ⟨_, d2214 _, rfl⟩, b2220, ⟨_, d2228 _, rfl⟩, b2240, ⟨_, d2254 _, rfl⟩, b2256,
    ⟨_, d2260 _, rfl⟩, b2262, ⟨_, d2273 _, rfl⟩, (.inl ⟨b2288, _, d2303 _, rfl⟩)⟩

theorem d2320 : ∀ feat, Dec feat scm 2320 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2324 : ∀ feat, Dec feat scm 2324 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d2328 : ∀ feat, Dec feat scm 2328 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d2332 : ∀ feat, Dec feat scm 2332 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2336 : ∀ feat, Dec feat scm 2336 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 10] 5) := by dec_rfl
theorem d2341 : ∀ feat, Dec feat scm 2341 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d2345 : ∀ feat, Dec feat scm 2345 (FV7z.mk (.sse .psubb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d2349 : ∀ feat, Dec feat scm 2349 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 2] 5) := by dec_rfl
theorem d2354 : ∀ feat, Dec feat scm 2354 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem d2356 : ∀ feat, Dec feat scm 2356 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d2359 : ∀ feat, Dec feat scm 2359 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem d2362 : ∀ feat, Dec feat scm 2362 (FV7z.mk (.jcc 5) 64 [.rel 3797] 6) := by dec_rfl
theorem d2368 : ∀ feat, Dec feat scm 2368 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d2372 : ∀ feat, Dec feat scm 2372
    (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 1) (some 11) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem d2377 : ∀ feat, Dec feat scm 2377 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2380 : ∀ feat, Dec feat scm 2380 (FV7z.mk (.jcc 2) 64 [.rel 3826] 6) := by dec_rfl
theorem d2386 : ∀ feat, Dec feat scm 2386 (FV7z.mk .test 64 [gr 64 9, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2389 : ∀ feat, Dec feat scm 2389 (FV7z.mk (.jcc 4) 64 [.rel 3817] 6) := by dec_rfl
theorem d2395 : ∀ feat, Dec feat scm 2395 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d2398 : ∀ feat, Dec feat scm 2398 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2402 : ∀ feat, Dec feat scm 2402 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 16)] 7) := by dec_rfl
theorem d2409 : ∀ feat, Dec feat scm 2409 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 6)] 6) := by dec_rfl
theorem d2415 : ∀ feat, Dec feat scm 2415 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 7) none 1 6 0)] 4) := by dec_rfl
theorem d2419 : ∀ feat, Dec feat scm 2419 (FV7z.mk .and 64 [gr 64 10, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d2426 : ∀ feat, Dec feat scm 2426 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d2433 : ∀ feat, Dec feat scm 2433 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 11) := by dec_rfl
theorem d2444 : ∀ feat, Dec feat scm 2444 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d2448 : ∀ feat, Dec feat scm 2448 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2452 : ∀ feat, Dec feat scm 2452 (FV7z.mk (.jcc 15) 64 [.rel 166] 6) := by dec_rfl
theorem d2458 : ∀ feat, Dec feat scm 2458 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2463 : ∀ feat, Dec feat scm 2463 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2468 : ∀ feat, Dec feat scm 2468 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2472 : ∀ feat, Dec feat scm 2472 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 6] 5) := by dec_rfl
theorem d2477 : ∀ feat, Dec feat scm 2477 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 10] 5) := by dec_rfl
theorem d2482 : ∀ feat, Dec feat scm 2482 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2486 : ∀ feat, Dec feat scm 2486 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2490 : ∀ feat, Dec feat scm 2490 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2494 : ∀ feat, Dec feat scm 2494 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2498 : ∀ feat, Dec feat scm 2498 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2502 : ∀ feat, Dec feat scm 2502 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2508 : ∀ feat, Dec feat scm 2508 (FV7z.mk (.jcc 5) 64 [.rel 3646] 6) := by dec_rfl
theorem d2514 : ∀ feat, Dec feat scm 2514 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2518 : ∀ feat, Dec feat scm 2518 (FV7z.mk (.jcc 6) 64 [.rel 3688] 6) := by dec_rfl
theorem d2524 : ∀ feat, Dec feat scm 2524 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2528 : ∀ feat, Dec feat scm 2528 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2532 : ∀ feat, Dec feat scm 2532 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2536 : ∀ feat, Dec feat scm 2536 (FV7z.mk (.jcc 15) 64 [.rel 86] 2) := by dec_rfl
theorem d2538 : ∀ feat, Dec feat scm 2538 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2543 : ∀ feat, Dec feat scm 2543 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbi 7 1 0 128)] 5) := by dec_rfl
theorem d2548 : ∀ feat, Dec feat scm 2548 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .xmm 2] 4) := by dec_rfl
theorem d2552 : ∀ feat, Dec feat scm 2552 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 6] 5) := by dec_rfl
theorem d2557 : ∀ feat, Dec feat scm 2557 (FV7z.mk (.sse .pslldq) 16 [.xmm 2, .imm 8 10] 5) := by dec_rfl
theorem d2562 : ∀ feat, Dec feat scm 2562 (FV7z.mk (.sse .por) 16 [.xmm 2, .xmm 3] 4) := by dec_rfl
theorem d2566 : ∀ feat, Dec feat scm 2566 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d2570 : ∀ feat, Dec feat scm 2570 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .xmm 2] 4) := by dec_rfl
theorem d2574 : ∀ feat, Dec feat scm 2574 (FV7z.mk (.sse .psubb) 16 [.xmm 1, .xmm 0] 4) := by dec_rfl
theorem d2578 : ∀ feat, Dec feat scm 2578 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d2582 : ∀ feat, Dec feat scm 2582 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl
theorem d2588 : ∀ feat, Dec feat scm 2588 (FV7z.mk (.jcc 5) 64 [.rel 3566] 6) := by dec_rfl
theorem d2594 : ∀ feat, Dec feat scm 2594 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2598 : ∀ feat, Dec feat scm 2598 (FV7z.mk (.jcc 6) 64 [.rel 3608] 6) := by dec_rfl
theorem d2604 : ∀ feat, Dec feat scm 2604 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d2608 : ∀ feat, Dec feat scm 2608 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 4] 4) := by dec_rfl
theorem d2612 : ∀ feat, Dec feat scm 2612 (FV7z.mk .jmp 64 [.rel 18446744073709551447] 5) := by dec_rfl
theorem d2624 : ∀ feat, Dec feat scm 2624 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d2628 : ∀ feat, Dec feat scm 2628 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d2632 : ∀ feat, Dec feat scm 2632 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 65472)] 6) := by dec_rfl
theorem d2638 : ∀ feat, Dec feat scm 2638 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl
theorem d2640 : ∀ feat, Dec feat scm 2640 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.i 10)] 4) := by dec_rfl
theorem d2644 : ∀ feat, Dec feat scm 2644 (FV7z.mk (.jcc 6) 64 [.rel 26] 2) := by dec_rfl
theorem d2646 : ∀ feat, Dec feat scm 2646 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d2650 : ∀ feat, Dec feat scm 2650 (FV7z.mk .sub 64 [gr 64 10, Src.opd 64 (.i 4096)] 7) := by dec_rfl
theorem d2657 : ∀ feat, Dec feat scm 2657 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl
theorem d2672 : ∀ feat, Dec feat scm 2672 (FV7z.mk (.sse .movdqa) 16 [.xmm 1, .mem (mbi 6 1 0 128)] 5) := by dec_rfl
theorem d2677 : ∀ feat, Dec feat scm 2677 (FV7z.mk (.sse .psrldq) 16 [.xmm 0, .imm 8 6] 5) := by dec_rfl
theorem d2682 : ∀ feat, Dec feat scm 2682 (FV7z.mk (.sse .psrldq) 16 [.xmm 3, .imm 8 6] 5) := by dec_rfl
theorem d2687 : ∀ feat, Dec feat scm 2687 (FV7z.mk .jmp 64 [.rel 3452] 5) := by dec_rfl

/-- The loop at `2320`, `k = 6`. -/
theorem ashr6 (prof : Profile) : AshrC prof 6 2320 4 := by
  have b2320 : BlkV prof scm 2320 2345 (A0 6) :=
    .cons (d2320 _) (VOpI.pxor) (by decide) <|
    .cons (d2324 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2328 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2332 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2336 _) (VOpI.pslldq) (by decide) <|
    .cons (d2341 _) (VOpI.pcmpeqb) (by decide) <|
    .nil 2345
  have b2345 : BlkV prof scm 2345 2362 (A25) :=
    .cons (d2345 _) (VOpI.psubb) (by decide) <|
    .cons (d2349 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2354 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d2356 _) (OpI.shr (.r 1)) (by decide) <|
    .cons (d2359 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
    .nil 2362
  have b2368 : BlkV prof scm 2368 2380 (A48) :=
    .cons (d2368 _) (VOpI.movdqa_m) (by decide) <|
    .cons (d2372 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d2377 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
    .nil 2380
  have b2386 : BlkV prof scm 2386 2389 (A66) :=
    .cons (d2386 _) (OpI.test (.r 9) (.inr rfl)) (by decide) <|
    .nil 2389
  have b2395 : BlkV prof scm 2395 2426 (A75 6) :=
    .cons (d2395 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
    .cons (d2398 _) (VOpI.pxor) (by decide) <|
    .cons (d2402 _) (OpI.mov (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2409 _) (OpI.mov (.i 6) (.inl rfl)) (by decide) <|
    .cons (d2415 _) (OpI.lea (.inr rfl)) (by decide) <|
    .cons (d2419 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
    .nil 2426
  have b2426 : BlkV prof scm 2426 2448 (A106) :=
    .cons (d2426 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .cons (d2433 _) (OpI.nop) (by decide) <|
    .cons (d2444 _) (OpI.nop) (by decide) <|
    .nil 2448
  have b2448 : BlkV prof scm 2448 2452 (A128) :=
    .cons (d2448 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2452
  have b2458 : BlkV prof scm 2458 2486 (A138 6) :=
    .cons (d2458 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2463 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2468 _) (VOpI.movdqa) (by decide) <|
    .cons (d2472 _) (VOpI.psrldq) (by decide) <|
    .cons (d2477 _) (VOpI.pslldq) (by decide) <|
    .cons (d2482 _) (VOpI.por) (by decide) <|
    .nil 2486
  have b2486 : BlkV prof scm 2486 2508 (A166) :=
    .cons (d2486 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2490 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2494 _) (VOpI.psubb) (by decide) <|
    .cons (d2498 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2502 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2508
  have b2514 : BlkV prof scm 2514 2518 (A194) :=
    .cons (d2514 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2518
  have b2524 : BlkV prof scm 2524 2536 (A204) :=
    .cons (d2524 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2528 _) (VOpI.movdqa) (by decide) <|
    .cons (d2532 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .nil 2536
  have b2538 : BlkV prof scm 2538 2566 (A218 6) :=
    .cons (d2538 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2543 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2548 _) (VOpI.movdqa) (by decide) <|
    .cons (d2552 _) (VOpI.psrldq) (by decide) <|
    .cons (d2557 _) (VOpI.pslldq) (by decide) <|
    .cons (d2562 _) (VOpI.por) (by decide) <|
    .nil 2566
  have b2566 : BlkV prof scm 2566 2588 (A246) :=
    .cons (d2566 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2570 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2574 _) (VOpI.psubb) (by decide) <|
    .cons (d2578 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2582 _) (OpI.sub (.i 65535) (.inl rfl)) (by decide) <|
    .nil 2588
  have b2594 : BlkV prof scm 2594 2598 (A274) :=
    .cons (d2594 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
    .nil 2598
  have b2604 : BlkV prof scm 2604 2612 (A284) :=
    .cons (d2604 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
    .cons (d2608 _) (VOpI.movdqa) (by decide) <|
    .nil 2612
  have b2624 : BlkV prof scm 2624 2638 (A304 6) :=
    .cons (d2624 _) (VOpI.pcmpeqb) (by decide) <|
    .cons (d2628 _) (VOpI.pmovmskb) (by decide) <|
    .cons (d2632 _) (OpI.test (.i 65472) (.inl rfl)) (by decide) <|
    .nil 2638
  have b2640 : BlkV prof scm 2640 2644 (A320 6) :=
    .cons (d2640 _) (OpI.cmp (.i 10) (.inr rfl)) (by decide) <|
    .nil 2644
  have b2646 : BlkV prof scm 2646 2657 (A326) :=
    .cons (d2646 _) (VOpI.pxor) (by decide) <|
    .cons (d2650 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
    .nil 2657
  have b2672 : BlkV prof scm 2672 2687 (T352 6) :=
    .cons (d2672 _) (VOpI.movdqa_mi) (by decide) <|
    .cons (d2677 _) (VOpI.psrldq) (by decide) <|
    .cons (d2682 _) (VOpI.psrldq) (by decide) <|
    .nil 2687
  exact ⟨b2320, b2345, ⟨_, d2362 _, rfl⟩, b2368, ⟨_, d2380 _, rfl⟩, b2386, ⟨_, d2389 _, rfl⟩, b2395, b2426, b2448,
    ⟨_, d2452 _, rfl⟩, b2458, b2486, ⟨_, d2508 _, rfl⟩, b2514, ⟨_, d2518 _, rfl⟩, b2524, ⟨_, d2536 _, rfl⟩, b2538,
    b2566, ⟨_, d2588 _, rfl⟩, b2594, ⟨_, d2598 _, rfl⟩, b2604, ⟨_, d2612 _, rfl⟩, b2624, ⟨_, d2638 _, rfl⟩, b2640,
    ⟨_, d2644 _, rfl⟩, b2646, ⟨_, d2657 _, rfl⟩, (.inl ⟨b2672, _, d2687 _, rfl⟩)⟩

end FV7z.Strncmp
