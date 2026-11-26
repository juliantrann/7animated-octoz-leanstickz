import FV7z.Ulk.Cuts
import FV7z.Strlen.Steps
import FV7z.Lemmas.Xmm2
/-!
# `unlink_chunk`: the steps outside the generated pieces (PLAN.md §M, M1)

- `ret_110`: the `ret`.
- `mq_117`, `mq_122`, `pu_127`, `mv_131`: `movq xmm0, rdx`, `movq xmm1, rcx`, `punpcklqdq xmm0, xmm1`,
  `movups [rax + 0x20], xmm0` (`fd->fd_nextsize`, `fd->bk_nextsize` = `p`'s, in one store).
- `mq_176`, `pu_181`, `mv_185`: `movq xmm0, rax`, `punpcklqdq xmm0, xmm0`, `movups [rax + 0x20], xmm0`
  (`fd->fd_nextsize` = `fd->bk_nextsize` = `fd`).
-/
namespace FV7z.Ulk
open ZellicX86 Decode FV7z.Leaf

def pr110 : List Byte := [0xc3]
theorem pr110_0 : ∀ feat, Dec feat pr110 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_110 : pr110 <+: ulk.drop 110 := by decide +kernel
theorem ret_110 (feat : Features) : Dec feat ulk 110 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 110) (k := 0) (pr110_0 feat) w_110 (Nat.zero_le _)

def mq117 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xc2]
theorem mq117_0 : ∀ feat, Dec feat mq117 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 2] 5) := by dec_rfl
theorem w_117 : mq117 <+: ulk.drop 117 := by decide +kernel
theorem mq_117 (feat : Features) : Dec feat ulk 117 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 2] 5) :=
  Dec.shift (j := 117) (k := 0) (mq117_0 feat) w_117 (Nat.zero_le _)

def mq122 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xc9]
theorem mq122_0 : ∀ feat, Dec feat mq122 0 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 1] 5) := by dec_rfl
theorem w_122 : mq122 <+: ulk.drop 122 := by decide +kernel
theorem mq_122 (feat : Features) : Dec feat ulk 122 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 1] 5) :=
  Dec.shift (j := 122) (k := 0) (mq122_0 feat) w_122 (Nat.zero_le _)

def pu127 : List Byte := [0x66, 0x0f, 0x6c, 0xc1]
theorem pu127_0 : ∀ feat, Dec feat pu127 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem w_127 : pu127 <+: ulk.drop 127 := by decide +kernel
theorem pu_127 (feat : Features) : Dec feat ulk 127 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 1] 4) :=
  Dec.shift (j := 127) (k := 0) (pu127_0 feat) w_127 (Nat.zero_le _)

def mv131 : List Byte := [0x0f, 0x11, 0x40, 0x20]
theorem mv131_0 : ∀ feat, Dec feat mv131 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 0 32 128), .xmm 0] 4) := by
  dec_rfl
theorem w_131 : mv131 <+: ulk.drop 131 := by decide +kernel
theorem mv_131 (feat : Features) : Dec feat ulk 131 (FV7z.mk (.sse .movups) 32 [.mem (mbd 0 32 128), .xmm 0] 4) :=
  Dec.shift (j := 131) (k := 0) (mv131_0 feat) w_131 (Nat.zero_le _)

def mq176 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xc0]
theorem mq176_0 : ∀ feat, Dec feat mq176 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) := by dec_rfl
theorem w_176 : mq176 <+: ulk.drop 176 := by decide +kernel
theorem mq_176 (feat : Features) : Dec feat ulk 176 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) :=
  Dec.shift (j := 176) (k := 0) (mq176_0 feat) w_176 (Nat.zero_le _)

def pu181 : List Byte := [0x66, 0x0f, 0x6c, 0xc0]
theorem pu181_0 : ∀ feat, Dec feat pu181 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem w_181 : pu181 <+: ulk.drop 181 := by decide +kernel
theorem pu_181 (feat : Features) : Dec feat ulk 181 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) :=
  Dec.shift (j := 181) (k := 0) (pu181_0 feat) w_181 (Nat.zero_le _)

theorem w_185 : mv131 <+: ulk.drop 185 := by decide +kernel
theorem mv_185 (feat : Features) : Dec feat ulk 185 (FV7z.mk (.sse .movups) 32 [.mem (mbd 0 32 128), .xmm 0] 4) :=
  Dec.shift (j := 185) (k := 0) (mv131_0 feat) w_185 (Nat.zero_le _)

end FV7z.Ulk
