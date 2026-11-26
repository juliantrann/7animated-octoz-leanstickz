import FV7z.Mcn.Cuts
import FV7z.Lemmas.Rmw7
import FV7z.Ulk.Holds
/-!
# `malloc_consolidate`: the steps outside the generated pieces (PLAN.md §M, M1)

- `xchg_39`: `xchg qword [r13], rbx` (`atomic_exchange_acq (fb, NULL)`).
- `and_92`: `and qword [r12 + 8], -2` (`clear_inuse_bit_at_offset (nextchunk, 0)`).
- `pxor_119`, `movups_123`: `p->fd_nextsize = NULL`, `p->bk_nextsize = NULL`.
- `movq_130`, `movhps_139`, `movups_148`: `p->fd = first_unsorted`, `p->bk = unsorted_bin`.
- `call_247`, `call_298`: `unlink_chunk` of the chunk before and of the chunk after; `ul_247`, `ul_298`: their
  target.
- `ret_73`: the `ret`.
-/
namespace FV7z.Mcn
open ZellicX86 Decode FV7z.Leaf

def px39 : List Byte := [0x49, 0x87, 0x5d, 0x00]
theorem px39_0 : ∀ feat, Dec feat px39 0 (FV7z.mk .xchg 64 [.mem (mbd 13 0 64), gr 64 3] 4) := by dec_rfl
theorem w_39 : px39 <+: mcn.drop 39 := by decide +kernel
theorem xchg_39 (feat : Features) : Dec feat mcn 39 (FV7z.mk .xchg 64 [.mem (mbd 13 0 64), gr 64 3] 4) :=
  Dec.shift (j := 39) (k := 0) (px39_0 feat) w_39 (Nat.zero_le _)

/-- `and qword [r12 + 8], -2`. -/
abbrev andM : Inst := FV7z.mk .and 64 [.mem (mbd 12 8 64), .imm 64 18446744073709551614] 6
def pa92 : List Byte := [0x49, 0x83, 0x64, 0x24, 0x08, 0xfe]
theorem pa92_0 : ∀ feat, Dec feat pa92 0 (andM) := by dec_rfl
theorem w_92 : pa92 <+: mcn.drop 92 := by decide +kernel
theorem and_92 (feat : Features) : Dec feat mcn 92 andM :=
  Dec.shift (j := 92) (k := 0) (pa92_0 feat) w_92 (Nat.zero_le _)

def pp119 : List Byte := [0x66, 0x0f, 0xef, 0xc9]
theorem pp119_0 : ∀ feat, Dec feat pp119 0 (FV7z.mk (.sse .pxor) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
theorem w_119 : pp119 <+: mcn.drop 119 := by decide +kernel
theorem pxor_119 (feat : Features) : Dec feat mcn 119 (FV7z.mk (.sse .pxor) 16 [.xmm 1, .xmm 1] 4) :=
  Dec.shift (j := 119) (k := 0) (pp119_0 feat) w_119 (Nat.zero_le _)

def pu123 : List Byte := [0x0f, 0x11, 0x4b, 0x20]
theorem pu123_0 : ∀ feat, Dec feat pu123 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 32 128), .xmm 1] 4) := by dec_rfl
theorem w_123 : pu123 <+: mcn.drop 123 := by decide +kernel
theorem movups_123 (feat : Features) : Dec feat mcn 123 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 32 128), .xmm 1] 4) :=
  Dec.shift (j := 123) (k := 0) (pu123_0 feat) w_123 (Nat.zero_le _)

def pq130 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xc0]
theorem pq130_0 : ∀ feat, Dec feat pq130 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) := by dec_rfl
theorem w_130 : pq130 <+: mcn.drop 130 := by decide +kernel
theorem movq_130 (feat : Features) : Dec feat mcn 130 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) :=
  Dec.shift (j := 130) (k := 0) (pq130_0 feat) w_130 (Nat.zero_le _)

def ph139 : List Byte := [0x0f, 0x16, 0x44, 0x24, 0x08]
theorem ph139_0 : ∀ feat, Dec feat ph139 0 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) := by dec_rfl
theorem w_139 : ph139 <+: mcn.drop 139 := by decide +kernel
theorem movhps_139 (feat : Features) : Dec feat mcn 139 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) :=
  Dec.shift (j := 139) (k := 0) (ph139_0 feat) w_139 (Nat.zero_le _)

def pu148 : List Byte := [0x0f, 0x11, 0x43, 0x10]
theorem pu148_0 : ∀ feat, Dec feat pu148 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 16 128), .xmm 0] 4) := by dec_rfl
theorem w_148 : pu148 <+: mcn.drop 148 := by decide +kernel
theorem movups_148 (feat : Features) : Dec feat mcn 148 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 16 128), .xmm 0] 4) :=
  Dec.shift (j := 148) (k := 0) (pu148_0 feat) w_148 (Nat.zero_le _)

def pc247 : List Byte := [0xe8, 0x24, 0xfe, 0xff, 0xff]
theorem pc247_0 : ∀ feat, Dec feat pc247 0 (FV7z.mk .call 64 [.rel 18446744073709551140] 5) := by dec_rfl
theorem w_247 : pc247 <+: mcn.drop 247 := by decide +kernel
theorem call_247 (feat : Features) : Dec feat mcn 247 (FV7z.mk .call 64 [.rel 18446744073709551140] 5) :=
  Dec.shift (j := 247) (k := 0) (pc247_0 feat) w_247 (Nat.zero_le _)

def pc298 : List Byte := [0xe8, 0xf1, 0xfd, 0xff, 0xff]
theorem pc298_0 : ∀ feat, Dec feat pc298 0 (FV7z.mk .call 64 [.rel 18446744073709551089] 5) := by dec_rfl
theorem w_298 : pc298 <+: mcn.drop 298 := by decide +kernel
theorem call_298 (feat : Features) : Dec feat mcn 298 (FV7z.mk .call 64 [.rel 18446744073709551089] 5) :=
  Dec.shift (j := 298) (k := 0) (pc298_0 feat) w_298 (Nat.zero_le _)

theorem w_73 : Sbrk.pret <+: mcn.drop 73 := by decide +kernel
theorem ret_73 (feat : Features) : Dec feat mcn 73 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 73) (k := 0) (Sbrk.pret_0 feat) w_73 (Nat.zero_le _)

/-- The two calls are of `unlink_chunk`. -/
theorem ul_247 : mcn_at.add (247 + 5) + BitVec.ofNat 64 18446744073709551140 = Ulk.ulk_at := by decide
theorem ul_298 : mcn_at.add (298 + 5) + BitVec.ofNat 64 18446744073709551089 = Ulk.ulk_at := by decide

end FV7z.Mcn
