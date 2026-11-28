import FV7z.Alr.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr40
import FV7z.Ocv.Holds
/-!
# `CArchiveLink::Release` (PLAN.md §M, M1): the instructions outside the blocks, the frame, the pieces

7-Zip 26.06's `CArchiveLink::Release ()` at `0x5d34b0` in `7zzs` (`CPP/7zip/UI/Common/OpenArchive.cpp`; `objdump
-d`): `this` in `rdi` (`r13`). `S` the stack pointer at the entry: `push r14, r13, r12, rbp, rbx` (the frame of
`FV7z/Lemmas/Fr40.lean`), no `sub rsp`.

- 0–24: the pushes, `NonOpen_ErrorInfo.ClearErrors ()` (19, `0x5d2b40`, `rdi` = `this + 0x40`); then
  `NonOpen_ArcPath.Empty ()` in line (the 4 bytes at `this + 0x38` and at `_chars` = the 8 bytes at `this + 0x30`
  set to 0: `Z1`), `eax` = `Arcs.Size ()` (the 4 bytes at `this + 8`): 0 to the epilogue (493).
- `while (!Arcs.IsEmpty ()) Arcs.DeleteBack ()` (head 64, `rax` = the size `k`): the arc `p` = `_items[k - 1]`
  (`rbp`; the 8 bytes at `it + 8 rax - 8`, `it` the 8 bytes at `this`) not 0 has `~CArc ()` in line: `delete []`
  (`0x6014f0`) of the chars at `p + 0xf8`, `0xe8`, `0xc0`, `0xb0`, `0x48`, `0x38`, `0x28` unless 0 (calls at 94,
  111, 128, 145, 159, 173, 187), `Release ()` (`call [rax + 0x10]`, `rax` the vtable) of the interfaces at
  `p + 0x18`, `0x10`, `8` unless 0 (204, 219, 234); then the `CMyComPtr` at `p` (`r14` = `b`): unless 0, its
  `Release` (the vtable's word at 16) not the one in line (`0x5db1e0`) is called (`call rax`, 515, then `jmp` 463);
  else in line (270, `sub dword [b + 0x10], 1`, by hand: `Seg.s_sub_mi32`): not 0 to 463, else `~CHandler ()`
  (the vtables at `b` and `b + 8` stored, `Release ()` of the interface at `b + 0x30` unless 0 (317)), the items
  (the 4-byte size `n` at `b + 0x20`, `_items` at `b + 0x18`) from the last down (head 344, `rbx` = `8 i`, `r12` =
  the item, `Ocv.rbx0`): `delete []` of the chars at `+ 0x48`, `0x38`, `0x20`, `0x10` unless 0 (363, 378, 393, 408),
  `operator delete (item, 0x80)` (421, `0x6014e0`), `rdi` = `_items` again (426), `rbx` -= 8 (430); `delete []` of
  `_items` unless 0 (445), `operator delete (b, 0x38)` (458). At 463 `operator delete (p, 0x110)` (471); at 476 the
  size one less, stored, and back to 64 unless 0. At 493 the pops, the `ret` (501).

The pieces (`vc_*`) are stated on the registers and the bytes: the loads by named values (`hp`, `hq`, ...), a
branch's condition on them; the stores of `NonOpen_ArcPath.Empty ()` by `Z1`, the size's by its value, the vtables'
by an invariant `I` the caller chooses and the stores that keep it (`Ok`, `hcl`, as in `FV7z/Api/Holds.lean`).
After the `sub` by hand (270) the flags are not tracked: both ways of the `jne` at 275 are the piece's
continuations.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Alr
set_option linter.unusedVariables false

open FV7z.Fr40 (KS r1 r2 r3 r4 r5)
open FV7z.Ocv (rbx0)

/-! ## The instructions outside the blocks -/

/-- The `call` at 19: `NonOpen_ErrorInfo.ClearErrors ()` (`0x5d2b40`). -/
def pc19 : List Byte := [0xe8, 0x78, 0xf6, 0xff, 0xff]
theorem pc19_0 : ∀ feat, Dec feat pc19 0 (FV7z.mk .call 64 [.rel 18446744073709549176] 5) := by dec_rfl
theorem wc_19 : pc19 <+: alr.drop 19 := by decide +kernel
theorem call_19 (feat : Features) : Dec feat alr 19 (FV7z.mk .call 64 [.rel 18446744073709549176] 5) :=
  Dec.shift (j := 19) (k := 0) (pc19_0 feat) wc_19 (Nat.zero_le _)
theorem tgt_19 : alr_at.add (19 + 5) + BitVec.ofNat 64 18446744073709549176 = 0x5d2b40#64 := by decide

/-- The `call` at 94: `operator delete []` (`0x6014f0`). -/
def pc94 : List Byte := [0xe8, 0xdd, 0xdf, 0x02, 0x00]
theorem pc94_0 : ∀ feat, Dec feat pc94 0 (FV7z.mk .call 64 [.rel 188381] 5) := by dec_rfl
theorem wc_94 : pc94 <+: alr.drop 94 := by decide +kernel
theorem call_94 (feat : Features) : Dec feat alr 94 (FV7z.mk .call 64 [.rel 188381] 5) :=
  Dec.shift (j := 94) (k := 0) (pc94_0 feat) wc_94 (Nat.zero_le _)
theorem tgt_94 : alr_at.add (94 + 5) + BitVec.ofNat 64 188381 = 0x6014f0#64 := by decide

/-- The `call` at 111: `operator delete []` (`0x6014f0`). -/
def pc111 : List Byte := [0xe8, 0xcc, 0xdf, 0x02, 0x00]
theorem pc111_0 : ∀ feat, Dec feat pc111 0 (FV7z.mk .call 64 [.rel 188364] 5) := by dec_rfl
theorem wc_111 : pc111 <+: alr.drop 111 := by decide +kernel
theorem call_111 (feat : Features) : Dec feat alr 111 (FV7z.mk .call 64 [.rel 188364] 5) :=
  Dec.shift (j := 111) (k := 0) (pc111_0 feat) wc_111 (Nat.zero_le _)
theorem tgt_111 : alr_at.add (111 + 5) + BitVec.ofNat 64 188364 = 0x6014f0#64 := by decide

/-- The `call` at 128: `operator delete []` (`0x6014f0`). -/
def pc128 : List Byte := [0xe8, 0xbb, 0xdf, 0x02, 0x00]
theorem pc128_0 : ∀ feat, Dec feat pc128 0 (FV7z.mk .call 64 [.rel 188347] 5) := by dec_rfl
theorem wc_128 : pc128 <+: alr.drop 128 := by decide +kernel
theorem call_128 (feat : Features) : Dec feat alr 128 (FV7z.mk .call 64 [.rel 188347] 5) :=
  Dec.shift (j := 128) (k := 0) (pc128_0 feat) wc_128 (Nat.zero_le _)
theorem tgt_128 : alr_at.add (128 + 5) + BitVec.ofNat 64 188347 = 0x6014f0#64 := by decide

/-- The `call` at 145: `operator delete []` (`0x6014f0`). -/
def pc145 : List Byte := [0xe8, 0xaa, 0xdf, 0x02, 0x00]
theorem pc145_0 : ∀ feat, Dec feat pc145 0 (FV7z.mk .call 64 [.rel 188330] 5) := by dec_rfl
theorem wc_145 : pc145 <+: alr.drop 145 := by decide +kernel
theorem call_145 (feat : Features) : Dec feat alr 145 (FV7z.mk .call 64 [.rel 188330] 5) :=
  Dec.shift (j := 145) (k := 0) (pc145_0 feat) wc_145 (Nat.zero_le _)
theorem tgt_145 : alr_at.add (145 + 5) + BitVec.ofNat 64 188330 = 0x6014f0#64 := by decide

/-- The `call` at 159: `operator delete []` (`0x6014f0`). -/
def pc159 : List Byte := [0xe8, 0x9c, 0xdf, 0x02, 0x00]
theorem pc159_0 : ∀ feat, Dec feat pc159 0 (FV7z.mk .call 64 [.rel 188316] 5) := by dec_rfl
theorem wc_159 : pc159 <+: alr.drop 159 := by decide +kernel
theorem call_159 (feat : Features) : Dec feat alr 159 (FV7z.mk .call 64 [.rel 188316] 5) :=
  Dec.shift (j := 159) (k := 0) (pc159_0 feat) wc_159 (Nat.zero_le _)
theorem tgt_159 : alr_at.add (159 + 5) + BitVec.ofNat 64 188316 = 0x6014f0#64 := by decide

/-- The `call` at 173: `operator delete []` (`0x6014f0`). -/
def pc173 : List Byte := [0xe8, 0x8e, 0xdf, 0x02, 0x00]
theorem pc173_0 : ∀ feat, Dec feat pc173 0 (FV7z.mk .call 64 [.rel 188302] 5) := by dec_rfl
theorem wc_173 : pc173 <+: alr.drop 173 := by decide +kernel
theorem call_173 (feat : Features) : Dec feat alr 173 (FV7z.mk .call 64 [.rel 188302] 5) :=
  Dec.shift (j := 173) (k := 0) (pc173_0 feat) wc_173 (Nat.zero_le _)
theorem tgt_173 : alr_at.add (173 + 5) + BitVec.ofNat 64 188302 = 0x6014f0#64 := by decide

/-- The `call` at 187: `operator delete []` (`0x6014f0`). -/
def pc187 : List Byte := [0xe8, 0x80, 0xdf, 0x02, 0x00]
theorem pc187_0 : ∀ feat, Dec feat pc187 0 (FV7z.mk .call 64 [.rel 188288] 5) := by dec_rfl
theorem wc_187 : pc187 <+: alr.drop 187 := by decide +kernel
theorem call_187 (feat : Features) : Dec feat alr 187 (FV7z.mk .call 64 [.rel 188288] 5) :=
  Dec.shift (j := 187) (k := 0) (pc187_0 feat) wc_187 (Nat.zero_le _)
theorem tgt_187 : alr_at.add (187 + 5) + BitVec.ofNat 64 188288 = 0x6014f0#64 := by decide

/-- The `call` at 363: `operator delete []` (`0x6014f0`). -/
def pc363 : List Byte := [0xe8, 0xd0, 0xde, 0x02, 0x00]
theorem pc363_0 : ∀ feat, Dec feat pc363 0 (FV7z.mk .call 64 [.rel 188112] 5) := by dec_rfl
theorem wc_363 : pc363 <+: alr.drop 363 := by decide +kernel
theorem call_363 (feat : Features) : Dec feat alr 363 (FV7z.mk .call 64 [.rel 188112] 5) :=
  Dec.shift (j := 363) (k := 0) (pc363_0 feat) wc_363 (Nat.zero_le _)
theorem tgt_363 : alr_at.add (363 + 5) + BitVec.ofNat 64 188112 = 0x6014f0#64 := by decide

/-- The `call` at 378: `operator delete []` (`0x6014f0`). -/
def pc378 : List Byte := [0xe8, 0xc1, 0xde, 0x02, 0x00]
theorem pc378_0 : ∀ feat, Dec feat pc378 0 (FV7z.mk .call 64 [.rel 188097] 5) := by dec_rfl
theorem wc_378 : pc378 <+: alr.drop 378 := by decide +kernel
theorem call_378 (feat : Features) : Dec feat alr 378 (FV7z.mk .call 64 [.rel 188097] 5) :=
  Dec.shift (j := 378) (k := 0) (pc378_0 feat) wc_378 (Nat.zero_le _)
theorem tgt_378 : alr_at.add (378 + 5) + BitVec.ofNat 64 188097 = 0x6014f0#64 := by decide

/-- The `call` at 393: `operator delete []` (`0x6014f0`). -/
def pc393 : List Byte := [0xe8, 0xb2, 0xde, 0x02, 0x00]
theorem pc393_0 : ∀ feat, Dec feat pc393 0 (FV7z.mk .call 64 [.rel 188082] 5) := by dec_rfl
theorem wc_393 : pc393 <+: alr.drop 393 := by decide +kernel
theorem call_393 (feat : Features) : Dec feat alr 393 (FV7z.mk .call 64 [.rel 188082] 5) :=
  Dec.shift (j := 393) (k := 0) (pc393_0 feat) wc_393 (Nat.zero_le _)
theorem tgt_393 : alr_at.add (393 + 5) + BitVec.ofNat 64 188082 = 0x6014f0#64 := by decide

/-- The `call` at 408: `operator delete []` (`0x6014f0`). -/
def pc408 : List Byte := [0xe8, 0xa3, 0xde, 0x02, 0x00]
theorem pc408_0 : ∀ feat, Dec feat pc408 0 (FV7z.mk .call 64 [.rel 188067] 5) := by dec_rfl
theorem wc_408 : pc408 <+: alr.drop 408 := by decide +kernel
theorem call_408 (feat : Features) : Dec feat alr 408 (FV7z.mk .call 64 [.rel 188067] 5) :=
  Dec.shift (j := 408) (k := 0) (pc408_0 feat) wc_408 (Nat.zero_le _)
theorem tgt_408 : alr_at.add (408 + 5) + BitVec.ofNat 64 188067 = 0x6014f0#64 := by decide

/-- The `call` at 421: `operator delete` (`0x6014e0`). -/
def pc421 : List Byte := [0xe8, 0x86, 0xde, 0x02, 0x00]
theorem pc421_0 : ∀ feat, Dec feat pc421 0 (FV7z.mk .call 64 [.rel 188038] 5) := by dec_rfl
theorem wc_421 : pc421 <+: alr.drop 421 := by decide +kernel
theorem call_421 (feat : Features) : Dec feat alr 421 (FV7z.mk .call 64 [.rel 188038] 5) :=
  Dec.shift (j := 421) (k := 0) (pc421_0 feat) wc_421 (Nat.zero_le _)
theorem tgt_421 : alr_at.add (421 + 5) + BitVec.ofNat 64 188038 = 0x6014e0#64 := by decide

/-- The `call` at 445: `operator delete []` (`0x6014f0`). -/
def pc445 : List Byte := [0xe8, 0x7e, 0xde, 0x02, 0x00]
theorem pc445_0 : ∀ feat, Dec feat pc445 0 (FV7z.mk .call 64 [.rel 188030] 5) := by dec_rfl
theorem wc_445 : pc445 <+: alr.drop 445 := by decide +kernel
theorem call_445 (feat : Features) : Dec feat alr 445 (FV7z.mk .call 64 [.rel 188030] 5) :=
  Dec.shift (j := 445) (k := 0) (pc445_0 feat) wc_445 (Nat.zero_le _)
theorem tgt_445 : alr_at.add (445 + 5) + BitVec.ofNat 64 188030 = 0x6014f0#64 := by decide

/-- The `call` at 458: `operator delete` (`0x6014e0`). -/
def pc458 : List Byte := [0xe8, 0x61, 0xde, 0x02, 0x00]
theorem pc458_0 : ∀ feat, Dec feat pc458 0 (FV7z.mk .call 64 [.rel 188001] 5) := by dec_rfl
theorem wc_458 : pc458 <+: alr.drop 458 := by decide +kernel
theorem call_458 (feat : Features) : Dec feat alr 458 (FV7z.mk .call 64 [.rel 188001] 5) :=
  Dec.shift (j := 458) (k := 0) (pc458_0 feat) wc_458 (Nat.zero_le _)
theorem tgt_458 : alr_at.add (458 + 5) + BitVec.ofNat 64 188001 = 0x6014e0#64 := by decide

/-- The `call` at 471: `operator delete` (`0x6014e0`). -/
def pc471 : List Byte := [0xe8, 0x54, 0xde, 0x02, 0x00]
theorem pc471_0 : ∀ feat, Dec feat pc471 0 (FV7z.mk .call 64 [.rel 187988] 5) := by dec_rfl
theorem wc_471 : pc471 <+: alr.drop 471 := by decide +kernel
theorem call_471 (feat : Features) : Dec feat alr 471 (FV7z.mk .call 64 [.rel 187988] 5) :=
  Dec.shift (j := 471) (k := 0) (pc471_0 feat) wc_471 (Nat.zero_le _)
theorem tgt_471 : alr_at.add (471 + 5) + BitVec.ofNat 64 187988 = 0x6014e0#64 := by decide

/-- `call [rax + 0x10]` (a `Release ()` through the vtable). -/
def pcm : List Byte := [0xff, 0x50, 0x10]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl

theorem wm_204 : pcm <+: alr.drop 204 := by decide +kernel
theorem callm_204 (feat : Features) : Dec feat alr 204 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 204) (k := 0) (pcm_0 feat) wm_204 (Nat.zero_le _)
theorem wm_219 : pcm <+: alr.drop 219 := by decide +kernel
theorem callm_219 (feat : Features) : Dec feat alr 219 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 219) (k := 0) (pcm_0 feat) wm_219 (Nat.zero_le _)
theorem wm_234 : pcm <+: alr.drop 234 := by decide +kernel
theorem callm_234 (feat : Features) : Dec feat alr 234 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 234) (k := 0) (pcm_0 feat) wm_234 (Nat.zero_le _)
theorem wm_317 : pcm <+: alr.drop 317 := by decide +kernel
theorem callm_317 (feat : Features) : Dec feat alr 317 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 317) (k := 0) (pcm_0 feat) wm_317 (Nat.zero_le _)

/-- `call rax` (the `Release` not in line). -/
def pcr : List Byte := [0xff, 0xd0]
theorem pcr_0 : ∀ feat, Dec feat pcr 0 (FV7z.mk .call 64 [gr 64 0] 2) := by dec_rfl
theorem wr_515 : pcr <+: alr.drop 515 := by decide +kernel
theorem callr_515 (feat : Features) : Dec feat alr 515 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 515) (k := 0) (pcr_0 feat) wr_515 (Nat.zero_le _)

/-- `sub dword [r14 + 0x10], 1` (the count of the `Release` in line). -/
def psb : List Byte := [0x41, 0x83, 0x6e, 0x10, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mbd 14 16 32), .imm 32 1] 5) := by dec_rfl
theorem w_270 : psb <+: alr.drop 270 := by decide +kernel
theorem sb_270 (feat : Features) : Dec feat alr 270 (FV7z.mk .sub 32 [.mem (mbd 14 16 32), .imm 32 1] 5) :=
  Dec.shift (j := 270) (k := 0) (psb_0 feat) w_270 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_501 : pret <+: alr.drop 501 := by decide +kernel
theorem ret_501 (feat : Features) : Dec feat alr 501 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 501) (k := 0) (pret_0 feat) wt_501 (Nat.zero_le _)

/-! ## The frame -/

/-- The bytes after the five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after `NonOpen_ArcPath.Empty ()` (`a` = `this`, `p` its `_chars`): its length and first char 0. -/
abbrev Z1 (V : Addr → Byte) (a p : Addr) : Addr → Byte :=
  Vst (Vst V (a + 56#64) (toBytesLE 0#32 4)) p (toBytesLE 0#32 4)

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- `Fr` but `rbp`. -/
abbrev Fp (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- `Fr` but `r14`. -/
abbrev Ft (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r15 = g.r15

/-- `Fr` but `rbx`. -/
abbrev Fb (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- `Fr` but `r12`. -/
abbrev Fc (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- The pushes, `r13` = `this`, `rdi` = `this + 0x40`: to the `call` at 19. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 → g'.rdi = g.rdi + 64#64 → g'.rbx = g.rbx → g'.rbp = g.rbp →
      g'.r12 = g.r12 → g'.r13 = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 19 g' fl (P5 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P5] at hs1 hs2 hs3 hs4 hs5 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | apply And.intro
    | intro _)

/-- Back from `ClearErrors`: `NonOpen_ArcPath.Empty ()` (`p` its `_chars`, `Z1`), `eax` = the size `n`: 0 to 493,
else to the loop's head 64. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : BitVec 64} {n : BitVec 32}
    (hp : rdq(V, g.r13 + 48#64) = p) (f48 : ∀ i < 8, Foot F.data (Addr.add (g.r13 + 48#64) i))
    (w56 : ∀ i < 4, Foot Wl (Addr.add (g.r13 + 56#64) i)) (wp : ∀ i < 4, Foot Wl (Addr.add p i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 8#64) i)) (hn : rdd(Z1 V g.r13 p, g.r13 + 8#64) = n)
    (h493 : n = 0 → ∀ g', Fr g g' → ∀ fl, Q 493 g' fl (Z1 V g.r13 p))
    (h64 : ¬n = 0 → ∀ g', Fr g g' → g'.rax = BitVec.setWidth 64 n → ∀ fl, Q 64 g' fl (Z1 V g.r13 p)) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Z1] at hp f48 w56 wp f8 hn h493 h64 ⊢
  wpx [W_24, W_54, o1, o2, hp, hn, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h493 ?_ _ ?_ _
    | refine h64 ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact f48
    | with_reducible exact w56
    | with_reducible exact wp
    | with_reducible exact f8
    | apply And.intro
    | intro _)

/-- The loop's head (`rax` = the size `k`): `rdx` = `_items` (`it`), `rbp` = the arc `p` (the 8 bytes at
`it + 8 k - 8`); 0 to 476; else `rdi` = the chars `q` at `p + 0xf8`: 0 to 99, else to the `call` at 94. -/
theorem vc_64 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {it p q : BitVec 64}
    (hit : rdq(V, g.r13) = it) (fi : ∀ i < 8, Foot F.data (Addr.add g.r13 i))
    (hp : rdq(V, it + g.rax * 8#64 + 18446744073709551608#64) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rax * 8#64 + 18446744073709551608#64) i))
    (hq : rdq(V, p + 248#64) = q) (fq : ¬p = 0 → ∀ i < 8, Foot F.data (Addr.add (p + 248#64) i))
    (h476 : p = 0 → ∀ g', Fp g g' → g'.rbp = p → ∀ fl, Q 476 g' fl V)
    (h99 : ¬p = 0 → q = 0 → ∀ g', Fp g g' → g'.rbp = p → ∀ fl, Q 99 g' fl V)
    (h94 : ¬p = 0 → ¬q = 0 → ∀ g', Fp g g' → g'.rbp = p → g'.rdi = q → ∀ fl, Q 94 g' fl V) :
    W_64 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fi hp fp hq fq h476 h99 h94 ⊢
  wpx [W_64, W_82, o3, o4, hit, hp, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h476 ?_ _ ?_ ?_ _
    | refine h99 ?_ ?_ _ ?_ ?_ _
    | refine h94 ?_ ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible assumption
    | with_reducible exact fi
    | with_reducible exact fp
    | (with_reducible exact fq (by assumption))
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0xe8`: 0 to 116, else to the `call` at 111. -/
theorem vc_99 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 232#64) i))
    (hz : rdq(V, g.rbp + 232#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 116 g' fl V)
    (hc : ¬rdq(V, g.rbp + 232#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 232#64) → ∀ fl, Q 111 g' fl V) :
    W_99 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_99, o5, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0xc0`: 0 to 133, else to the `call` at 128. -/
theorem vc_116 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 192#64) i))
    (hz : rdq(V, g.rbp + 192#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 133 g' fl V)
    (hc : ¬rdq(V, g.rbp + 192#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 192#64) → ∀ fl, Q 128 g' fl V) :
    W_116 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_116, o6, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0xb0`: 0 to 150, else to the `call` at 145. -/
theorem vc_133 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 176#64) i))
    (hz : rdq(V, g.rbp + 176#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 150 g' fl V)
    (hc : ¬rdq(V, g.rbp + 176#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 176#64) → ∀ fl, Q 145 g' fl V) :
    W_133 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_133, o7, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0x48`: 0 to 164, else to the `call` at 159. -/
theorem vc_150 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 72#64) i))
    (hz : rdq(V, g.rbp + 72#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 164 g' fl V)
    (hc : ¬rdq(V, g.rbp + 72#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 72#64) → ∀ fl, Q 159 g' fl V) :
    W_150 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_150, o8, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0x38`: 0 to 178, else to the `call` at 173. -/
theorem vc_164 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 56#64) i))
    (hz : rdq(V, g.rbp + 56#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 178 g' fl V)
    (hc : ¬rdq(V, g.rbp + 56#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 56#64) → ∀ fl, Q 173 g' fl V) :
    W_164 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_164, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `rbp + 0x28`: 0 to 192, else to the `call` at 187. -/
theorem vc_178 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 40#64) i))
    (hz : rdq(V, g.rbp + 40#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 192 g' fl V)
    (hc : ¬rdq(V, g.rbp + 40#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 40#64) → ∀ fl, Q 187 g' fl V) :
    W_178 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_178, o10, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the interface at `rbp + 0x18`: 0 to 207, else `rax` = its vtable, to the `call` at 204. -/
theorem vc_192 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 24#64) i))
    (fv : ¬rdq(V, g.rbp + 24#64) = 0 → ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbp + 24#64) i))
    (hz : rdq(V, g.rbp + 24#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 207 g' fl V)
    (hc : ¬rdq(V, g.rbp + 24#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 24#64) → g'.rax = rdq(V, rdq(V,
      g.rbp + 24#64)) →
      ∀ fl, Q 204 g' fl V) :
    W_192 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq fv hz hc ⊢
  wpx [W_192, W_201, o11, o12, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | (with_reducible exact fv (by assumption))
    | apply And.intro
    | intro _)

/-- `rdi` = the interface at `rbp + 0x10`: 0 to 222, else `rax` = its vtable, to the `call` at 219. -/
theorem vc_207 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 16#64) i))
    (fv : ¬rdq(V, g.rbp + 16#64) = 0 → ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbp + 16#64) i))
    (hz : rdq(V, g.rbp + 16#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 222 g' fl V)
    (hc : ¬rdq(V, g.rbp + 16#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 16#64) → g'.rax = rdq(V, rdq(V,
      g.rbp + 16#64)) →
      ∀ fl, Q 219 g' fl V) :
    W_207 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq fv hz hc ⊢
  wpx [W_207, W_216, o13, o12, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | (with_reducible exact fv (by assumption))
    | apply And.intro
    | intro _)

/-- `rdi` = the interface at `rbp + 0x8`: 0 to 237, else `rax` = its vtable, to the `call` at 234. -/
theorem vc_222 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (fv : ¬rdq(V, g.rbp + 8#64) = 0 → ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbp + 8#64) i))
    (hz : rdq(V, g.rbp + 8#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 237 g' fl V)
    (hc : ¬rdq(V, g.rbp + 8#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.rbp + 8#64) → g'.rax = rdq(V, rdq(V,
      g.rbp + 8#64)) →
      ∀ fl, Q 234 g' fl V) :
    W_222 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq fv hz hc ⊢
  wpx [W_222, W_231, o14, o12, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | (with_reducible exact fv (by assumption))
    | apply And.intro
    | intro _)

/-- `r14` = the `CMyComPtr` `b` at `rbp`: 0 to 463; else its `Release` `fn` (the vtable's word at 16): the one in
line (`0x5db1e0`) to the `sub` at 270, else `rdi` = `b`, to the `call rax` at 515. -/
theorem vc_237 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {b fn : BitVec 64}
    (fb : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (hb : rdq(V, g.rbp) = b)
    (fv : ¬b = 0 → ∀ i < 8, Foot F.data (Addr.add b i))
    (ff : ¬b = 0 → ∀ i < 8, Foot F.data (Addr.add (rdq(V, b) + 16#64) i)) (hf : rdq(V, rdq(V, b) + 16#64) = fn)
    (h463 : b = 0 → ∀ g', Ft g g' → g'.r14 = b → ∀ fl, Q 463 g' fl V)
    (h270 : ¬b = 0 → fn = 6140384#64 → ∀ g', Ft g g' → g'.r14 = b → ∀ fl, Q 270 g' fl V)
    (h515 : ¬b = 0 → ¬fn = 6140384#64 → ∀ g', Ft g g' → g'.r14 = b → g'.rax = fn → g'.rdi = b →
      ∀ fl, Q 515 g' fl V) :
    W_237 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb hb fv ff hf h463 h270 h515 ⊢
  wpx [W_237, W_250, W_512, o15, o16, o33, hb, hf, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h463 ?_ _ ?_ ?_ _
    | refine h270 ?_ ?_ _ ?_ ?_ _
    | refine h515 ?_ ?_ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fb
    | (with_reducible exact fv (by assumption))
    | (with_reducible exact ff (by assumption))
    | apply And.intro
    | intro _)

/-- After the `sub` (the flags not tracked): to 463; or `~CHandler ()`: the vtables stored (`I`, `Ok`), `rdi` = the
interface `q` at `b + 0x30`: 0 to 320, else `rax` = its vtable, to the `call` at 317. -/
theorem vc_275 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {q : BitVec 64}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.r14 i)) (w8 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 8#64) i))
    (o0 : Ok g.r14 8) (o8 : Ok (g.r14 + 8#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 48#64) i)) (hq : rdq(V, g.r14 + 48#64) = q)
    (fq : ¬q = 0 → ∀ i < 8, Foot F.data (Addr.add q i))
    (h463 : ∀ g', Fr g g' → ∀ fl, Q 463 g' fl V)
    (h320 : ∀ g' V', I V' → q = 0 → Fr g g' → ∀ fl, Q 320 g' fl V')
    (h317 : ∀ g' V', I V' → ¬q = 0 → Fr g g' → g'.rdi = q → g'.rax = rdq(V', q) → ∀ fl, Q 317 g' fl V') :
    W_275 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w8 o0 o8 f48 hq fq h463 h320 h317 ⊢
  wpx [W_275, W_281, W_314, o17, o12, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h463 _ ?_ _
    | refine h320 _ _ ?_ ?_ ?_ _
    | refine h317 _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact w0
    | with_reducible exact w8
    | with_reducible exact o0
    | with_reducible exact o8
    | with_reducible exact hI
    | with_reducible exact f48
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | (with_reducible exact fq (by assumption))
    | apply And.intro
    | intro _)

/-- `eax` = the size `n` at `b + 0x20`, `rdi` = `_items` `d` at `b + 0x18`: `n` = 0 to 440; else `rbx` = `8 (n - 1)`
(`rbx0`), to the items' loop (344). -/
theorem vc_320 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n : BitVec 32} {d : BitVec 64}
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.r14 + 32#64) i))
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (hn : rdd(V, g.r14 + 32#64) = n) (hd : rdq(V, g.r14 + 24#64) = d)
    (h440 : n = 0 → ∀ g', Fr g g' → g'.rdi = d → ∀ fl, Q 440 g' fl V)
    (h344 : ¬n = 0 → ∀ g', Fb g g' → g'.rdi = d → g'.rbx = rbx0 n → ∀ fl, Q 344 g' fl V) :
    W_320 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fn fd hn hd h440 h344 ⊢
  wpx [W_320, W_332, o18, o19, Op.shl64, hn, hd, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h440 ?_ _ ?_ ?_ _
    | refine h344 ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fn
    | with_reducible exact fd
    | apply And.intro
    | intro _)

/-- The items' loop head: `r12` = the item `p` (the 8 bytes at `rdi + rbx`): 0 to 430; else `rdi` = the chars `q`
at `p + 0x48`: 0 to 368, else to the `call` at 363. -/
theorem vc_344 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64}
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp : rdq(V, g.rdi + g.rbx) = p)
    (hq : rdq(V, p + 72#64) = q) (fq : ¬p = 0 → ∀ i < 8, Foot F.data (Addr.add (p + 72#64) i))
    (h430 : p = 0 → ∀ g', Fc g g' → g'.r12 = p → g'.rdi = g.rdi → ∀ fl, Q 430 g' fl V)
    (h368 : ¬p = 0 → q = 0 → ∀ g', Fc g g' → g'.r12 = p → ∀ fl, Q 368 g' fl V)
    (h363 : ¬p = 0 → ¬q = 0 → ∀ g', Fc g g' → g'.r12 = p → g'.rdi = q → ∀ fl, Q 363 g' fl V) :
    W_344 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp hp hq fq h430 h368 h363 ⊢
  wpx [W_344, W_353, o20, o21, hp, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h430 ?_ _ ?_ ?_ ?_ _
    | refine h368 ?_ ?_ _ ?_ ?_ _
    | refine h363 ?_ ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fp
    | (with_reducible exact fq (by assumption))
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `r12 + 0x38`: 0 to 383, else to the `call` at 378. -/
theorem vc_368 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 56#64) i))
    (hz : rdq(V, g.r12 + 56#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 383 g' fl V)
    (hc : ¬rdq(V, g.r12 + 56#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.r12 + 56#64) → ∀ fl, Q 378 g' fl V) :
    W_368 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_368, o22, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `r12 + 0x20`: 0 to 398, else to the `call` at 393. -/
theorem vc_383 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 32#64) i))
    (hz : rdq(V, g.r12 + 32#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 398 g' fl V)
    (hc : ¬rdq(V, g.r12 + 32#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.r12 + 32#64) → ∀ fl, Q 393 g' fl V) :
    W_383 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_383, o23, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the chars at `r12 + 0x10`: 0 to 413, else to the `call` at 408. -/
theorem vc_398 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 16#64) i))
    (hz : rdq(V, g.r12 + 16#64) = 0 → ∀ g', Fr g g' → ∀ fl, Q 413 g' fl V)
    (hc : ¬rdq(V, g.r12 + 16#64) = 0 → ∀ g', Fr g g' → g'.rdi = rdq(V, g.r12 + 16#64) → ∀ fl, Q 408 g' fl V) :
    W_398 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq hz hc ⊢
  wpx [W_398, o24, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fq
    | apply And.intro
    | intro _)

/-- `rdi` = the item, `esi` = 0x80: to the `call` at 421. -/
theorem vc_413 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.r12 → g'.rsi = 128#64 → ∀ fl, Q 421 g' fl V) :
    W_413 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_413, o25, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | apply And.intro
    | intro _)

/-- Back from `operator delete`: `rdi` = `_items` again: to 430. -/
theorem vc_426 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (h : ∀ g', Fr g g' → g'.rdi = rdq(V, g.r14 + 24#64) → ∀ fl, Q 430 g' fl V) :
    W_426 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fd h ⊢
  wpx [W_426, o26]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fd
    | apply And.intro
    | intro _)

/-- `rbx` -= 8: `-8` (the last item done) to 440, else back to 344. -/
theorem vc_430 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h440 : g.rbx - 8#64 = 18446744073709551608#64 → ∀ g', Fb g g' → g'.rdi = g.rdi → ∀ fl, Q 440 g' fl V)
    (h344 : ¬g.rbx - 8#64 = 18446744073709551608#64 → ∀ g', Fb g g' → g'.rbx = g.rbx - 8#64 → g'.rdi = g.rdi →
      ∀ fl, Q 344 g' fl V) :
    W_430 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h440 h344 ⊢
  wpx [W_430, o27, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h440 ?_ _ ?_ ?_ _
    | refine h344 ?_ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | apply And.intro
    | intro _)

/-- `_items` (`rdi`): 0 to 450, else to the `call` at 445. -/
theorem vc_440 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hz : g.rdi = 0 → ∀ g', Fr g g' → ∀ fl, Q 450 g' fl V)
    (hc : ¬g.rdi = 0 → ∀ g', Fr g g' → g'.rdi = g.rdi → ∀ fl, Q 445 g' fl V) :
    W_440 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hc ⊢
  wpx [W_440, o28, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine hz ?_ _ ?_ _
    | refine hc ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | apply And.intro
    | intro _)

/-- `esi` = 0x38, `rdi` = `b`: to the `call` at 458. -/
theorem vc_450 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.r14 → g'.rsi = 56#64 → ∀ fl, Q 458 g' fl V) :
    W_450 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_450, o29, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | apply And.intro
    | intro _)

/-- `esi` = 0x110, `rdi` = the arc: to the `call` at 471. -/
theorem vc_463 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.rbp → g'.rsi = 272#64 → ∀ fl, Q 471 g' fl V) :
    W_463 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_463, o30, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | apply And.intro
    | intro _)

/-- The size `c` one less, stored: 0 to 493, else `eax` = it, back to 64. -/
theorem vc_476 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {c : BitVec 32}
    (fc : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 8#64) i)) (wc : ∀ i < 4, Foot Wl (Addr.add (g.r13 + 8#64) i))
    (hc : rdd(V, g.r13 + 8#64) = c)
    (h493 : c = 1#32 → ∀ g', Fr g g' → ∀ fl, Q 493 g' fl (Vst V (g.r13 + 8#64) (toBytesLE (c - 1#32) 4)))
    (h64 : ¬c = 1#32 → ∀ g', Fr g g' → g'.rax = BitVec.setWidth 64 (c - 1#32) →
      ∀ fl, Q 64 g' fl (Vst V (g.r13 + 8#64) (toBytesLE (c - 1#32) 4))) :
    W_476 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fc wc hc h493 h64 ⊢
  wpx [W_476, o31, hc, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    Bool.false_eq_true, Bool.true_eq_false, false_implies, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h493 ?_ _ ?_ _
    | refine h64 ?_ _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact fc
    | with_reducible exact wc
    | apply And.intro
    | intro _)

/-- The pops, to the `ret` (501). -/
theorem vc_493 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → g'.r13 = rdq(V, g.rsp + 8 + 8 + 8) →
      g'.r14 = rdq(V, g.rsp + 8 + 8 + 8 + 8) → g'.r15 = g.r15 → ∀ fl, Q 501 g' fl V) :
    W_493 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p1 p2 p3 p4 p5 h ⊢
  wpx [W_493, o32]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | with_reducible exact p5
    | apply And.intro
    | intro _)

/-- Back from the `call rax`: `jmp` to 463. -/
theorem vc_517 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 463 g fl V) :
    W_517 F Wl Q g f V := h _

end Pieces

end FV7z.Alr
