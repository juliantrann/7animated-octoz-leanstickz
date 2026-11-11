import FV7z.Pim.Cuts
import FV7z.Lemmas.Lock
/-!
# `__pthread_initialize_minimal_internal`: the instructions at the stops (PLAN.md G3, startup)

The instructions of `0x6000b0` that `Pim/Cuts.lean` leaves to a lemma of their own, decoded (`movq_14` … `ret_698`):
the moves through `xmm0` and `xmm1`, the three `syscall`s, `rep stos`, `or [rsp + 40], rax`, `div rcx`, the lock
(`lock cmpxchg`, `xchg`), the six `call`s and the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pim

def pmq0 : List Byte := [0x66, 0x49, 0x0f, 0x6e, 0xc0]
theorem pmq0_0 : ∀ feat, Dec feat pmq0 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 8] 5) := by dec_rfl
def ppu0 : List Byte := [0x66, 0x0f, 0x6c, 0xc0]
theorem ppu0_0 : ∀ feat, Dec feat ppu0 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
def pmq1 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xcf]
theorem pmq1_0 : ∀ feat, Dec feat pmq1 0 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 7] 5) := by dec_rfl
def ppu1 : List Byte := [0x66, 0x0f, 0x6c, 0xc9]
theorem ppu1_0 : ∀ feat, Dec feat ppu1 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
def pmu1 : List Byte := [0x0f, 0x11, 0x8a, 0xd8, 0x02, 0x00, 0x00]
theorem pmu1_0 : ∀ feat, Dec feat pmu1 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 2 728 128), .xmm 1] 7) := by dec_rfl
def pmu0 : List Byte := [0x0f, 0x11, 0x82, 0xc0, 0x02, 0x00, 0x00]
theorem pmu0_0 : ∀ feat, Dec feat pmu0 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 2 704 128), .xmm 0] 7) := by dec_rfl
def pstos : List Byte := [0xf3, 0x48, 0xab]
theorem pstos_0 : ∀ feat, Dec feat pstos 0 (repStosq 3) := by dec_rfl
def pc271 : List Byte := [0xe8, 0x2c, 0x0e, 0x00, 0x00]
theorem pc271_0 : ∀ feat, Dec feat pc271 0 (FV7z.mk .call 64 [.rel 3628] 5) := by dec_rfl
def pc309 : List Byte := [0xe8, 0x06, 0x0e, 0x00, 0x00]
theorem pc309_0 : ∀ feat, Dec feat pc309 0 (FV7z.mk .call 64 [.rel 3590] 5) := by dec_rfl
def por : List Byte := [0x48, 0x09, 0x44, 0x24, 0x28]
theorem por_0 : ∀ feat, Dec feat por 0 (FV7z.mk .or 64 [.mem (mbd 4 40 64), gr 64 0] 5) := by dec_rfl
def pc364 : List Byte := [0xe8, 0x9f, 0xe4, 0x06, 0x00]
theorem pc364_0 : ∀ feat, Dec feat pc364 0 (FV7z.mk .call 64 [.rel 451743] 5) := by dec_rfl
def pdiv1 : List Byte := [0x48, 0xf7, 0xf1]
theorem pdiv1_0 : ∀ feat, Dec feat pdiv1 0 (FV7z.mk .div 64 [gr 64 1] 3) := by dec_rfl
def pc448 : List Byte := [0xe8, 0x9b, 0x60, 0x06, 0x00]
theorem pc448_0 : ∀ feat, Dec feat pc448 0 (FV7z.mk .call 64 [.rel 417947] 5) := by dec_rfl
def pcx : List Byte := [0xf0, 0x0f, 0xb1, 0x15, 0x87, 0x2e, 0x1a, 0x00]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (lockCmpxchg32 1715847 2 8) := by dec_rfl
def pxchg : List Byte := [0x87, 0x05, 0x5f, 0x2e, 0x1a, 0x00]
theorem pxchg_0 : ∀ feat, Dec feat pxchg 0 (FV7z.mk .xchg 32 [.mem (mrip 1715807 32), gr 32 0] 6) := by dec_rfl
def pc642 : List Byte := [0xe8, 0xf9, 0xd6, 0x02, 0x00]
theorem pc642_0 : ∀ feat, Dec feat pc642 0 (FV7z.mk .call 64 [.rel 186105] 5) := by dec_rfl
def pc664 : List Byte := [0xe8, 0x73, 0xf8, 0xff, 0xff]
theorem pc664_0 : ∀ feat, Dec feat pc664 0 (FV7z.mk .call 64 [.rel 18446744073709549683] 5) := by dec_rfl
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wd_14 : pmq0 <+: pim.drop 14 := by decide +kernel
theorem movq_14 (feat : Features) : Dec feat pim 14 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 8] 5) :=
  Dec.shift (j := 14) (k := 0) (pmq0_0 feat) wd_14 (Nat.zero_le _)
theorem wd_28 : ppu0 <+: pim.drop 28 := by decide +kernel
theorem punp_28 (feat : Features) : Dec feat pim 28 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) :=
  Dec.shift (j := 28) (k := 0) (ppu0_0 feat) wd_28 (Nat.zero_le _)
theorem wd_70 : psys <+: pim.drop 70 := by decide +kernel
theorem sys_70 (feat : Features) : Dec feat pim 70 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 70) (k := 0) (psys_0 feat) wd_70 (Nat.zero_le _)
theorem wd_131 : pmq1 <+: pim.drop 131 := by decide +kernel
theorem movq_131 (feat : Features) : Dec feat pim 131 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 7] 5) :=
  Dec.shift (j := 131) (k := 0) (pmq1_0 feat) wd_131 (Nat.zero_le _)
theorem wd_136 : ppu1 <+: pim.drop 136 := by decide +kernel
theorem punp_136 (feat : Features) : Dec feat pim 136 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 1, .xmm 1] 4) :=
  Dec.shift (j := 136) (k := 0) (ppu1_0 feat) wd_136 (Nat.zero_le _)
theorem wd_140 : pmu1 <+: pim.drop 140 := by decide +kernel
theorem movups_140 (feat : Features) : Dec feat pim 140 (FV7z.mk (.sse .movups) 32 [.mem (mbd 2 728 128), .xmm 1] 7) :=
  Dec.shift (j := 140) (k := 0) (pmu1_0 feat) wd_140 (Nat.zero_le _)
theorem wd_147 : psys <+: pim.drop 147 := by decide +kernel
theorem sys_147 (feat : Features) : Dec feat pim 147 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 147) (k := 0) (psys_0 feat) wd_147 (Nat.zero_le _)
theorem wd_186 : pmu0 <+: pim.drop 186 := by decide +kernel
theorem movups_186 (feat : Features) : Dec feat pim 186 (FV7z.mk (.sse .movups) 32 [.mem (mbd 2 704 128), .xmm 0] 7) :=
  Dec.shift (j := 186) (k := 0) (pmu0_0 feat) wd_186 (Nat.zero_le _)
theorem wd_248 : pstos <+: pim.drop 248 := by decide +kernel
theorem stos_248 (feat : Features) : Dec feat pim 248 (repStosq 3) :=
  Dec.shift (j := 248) (k := 0) (pstos_0 feat) wd_248 (Nat.zero_le _)
theorem wd_271 : pc271 <+: pim.drop 271 := by decide +kernel
theorem call_271 (feat : Features) : Dec feat pim 271 (FV7z.mk .call 64 [.rel 3628] 5) :=
  Dec.shift (j := 271) (k := 0) (pc271_0 feat) wd_271 (Nat.zero_le _)
theorem wd_309 : pc309 <+: pim.drop 309 := by decide +kernel
theorem call_309 (feat : Features) : Dec feat pim 309 (FV7z.mk .call 64 [.rel 3590] 5) :=
  Dec.shift (j := 309) (k := 0) (pc309_0 feat) wd_309 (Nat.zero_le _)
theorem wd_340 : por <+: pim.drop 340 := by decide +kernel
theorem or_340 (feat : Features) : Dec feat pim 340 (FV7z.mk .or 64 [.mem (mbd 4 40 64), gr 64 0] 5) :=
  Dec.shift (j := 340) (k := 0) (por_0 feat) wd_340 (Nat.zero_le _)
theorem wd_350 : psys <+: pim.drop 350 := by decide +kernel
theorem sys_350 (feat : Features) : Dec feat pim 350 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 350) (k := 0) (psys_0 feat) wd_350 (Nat.zero_le _)
theorem wd_364 : pc364 <+: pim.drop 364 := by decide +kernel
theorem call_364 (feat : Features) : Dec feat pim 364 (FV7z.mk .call 64 [.rel 451743] 5) :=
  Dec.shift (j := 364) (k := 0) (pc364_0 feat) wd_364 (Nat.zero_le _)
theorem wd_434 : pdiv1 <+: pim.drop 434 := by decide +kernel
theorem div_434 (feat : Features) : Dec feat pim 434 (FV7z.mk .div 64 [gr 64 1] 3) :=
  Dec.shift (j := 434) (k := 0) (pdiv1_0 feat) wd_434 (Nat.zero_le _)
theorem wd_448 : pc448 <+: pim.drop 448 := by decide +kernel
theorem call_448 (feat : Features) : Dec feat pim 448 (FV7z.mk .call 64 [.rel 417947] 5) :=
  Dec.shift (j := 448) (k := 0) (pc448_0 feat) wd_448 (Nat.zero_le _)
theorem wd_545 : pcx <+: pim.drop 545 := by decide +kernel
theorem cmpxchg_545 (feat : Features) : Dec feat pim 545 (lockCmpxchg32 1715847 2 8) :=
  Dec.shift (j := 545) (k := 0) (pcx_0 feat) wd_545 (Nat.zero_le _)
theorem wd_587 : pxchg <+: pim.drop 587 := by decide +kernel
theorem xchg_587 (feat : Features) : Dec feat pim 587 (FV7z.mk .xchg 32 [.mem (mrip 1715807 32), gr 32 0] 6) :=
  Dec.shift (j := 587) (k := 0) (pxchg_0 feat) wd_587 (Nat.zero_le _)
theorem wd_642 : pc642 <+: pim.drop 642 := by decide +kernel
theorem call_642 (feat : Features) : Dec feat pim 642 (FV7z.mk .call 64 [.rel 186105] 5) :=
  Dec.shift (j := 642) (k := 0) (pc642_0 feat) wd_642 (Nat.zero_le _)
theorem wd_664 : pc664 <+: pim.drop 664 := by decide +kernel
theorem call_664 (feat : Features) : Dec feat pim 664 (FV7z.mk .call 64 [.rel 18446744073709549683] 5) :=
  Dec.shift (j := 664) (k := 0) (pc664_0 feat) wd_664 (Nat.zero_le _)
theorem wd_698 : pret <+: pim.drop 698 := by decide +kernel
theorem ret_698 (feat : Features) : Dec feat pim 698 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 698) (k := 0) (pret_0 feat) wd_698 (Nat.zero_le _)

end FV7z.Pim
