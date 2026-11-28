import FV7z.Cfd.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr40
/-!
# `__libc_check_standard_fds` (PLAN.md G3, startup)

glibc 2.31's `__libc_check_standard_fds ()` at `0x613860` in `7zzs` (`csu/check_fds.c`; `objdump -d`), called by
`__libc_start_main` when `__libc_enable_secure`. `S` the stack pointer at the entry: a frame of 152 bytes
(`aR S` = `S - 152`), the `struct stat` at `aR S`. For each fd `k` = 0, 1, 2, `check_one_fd (k, mode)` in line:

- `__fcntl64_nocancel (k, F_GETFD)` (`0x665f50`; calls at 20, 42, 68; back at 25, 47, 73): unless the answer is
  -1 and `errno` (the 4 bytes at `fs:-0x48`, `errnoAt`) is `EBADF` (9), on to the next fd (30, 56) or the end (82);
- else `__open64_nocancel (name, flags)` (`0x666090`; 125, 233, 345): "/dev/full" (`0x6ee802`) with
  `O_WRONLY | O_NOFOLLOW` for 0, "/dev/null" (`0x6ee80c`) with `O_RDONLY | O_NOFOLLOW` for 1 and 2; when the answer
  is `k`, `__fxstat (1, k, &st)` (`0x665360`; 144, 256, 368); when that answers 0, `st.st_mode & S_IFMT` (the 4
  bytes at `rsp + 24`) is `S_IFCHR` (`0x2000`) and `st.st_rdev` (the 8 bytes at `rsp + 40`) is the device's
  (`makedev (1, 7)` = 263 for 0, `makedev (1, 3)` = 259 for 1 and 2), on as above; else the `hlt` (192, 304, 416).
- At 82 the frame dropped, the `ret` (89).

The pieces (`vc_*`) are stated on the registers and the bytes, one for each way through a cut point; the runs (`R*`)
from the cut points to the goal take the callees as continuations (`KC`, as in `FV7z/Spp/Holds.lean`) that come
back with `rsp` as it was, the callee-saved registers (`KS`) as at the `call` and bytes with the invariant `I` the
caller chooses (it gives the return address at `S`, `hra`). `cfd_ok`: from the entry to the return address.

Not covered: the `hlt` itself (a `#GP`, `Sem.hlt`): the run reaches it with bytes `I` (`kh`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cfd

set_option linter.unusedVariables false

open FV7z.Fr40 (KS)

/-! ## The calls and the `ret` -/

/-- The `call` at 20: `__fcntl64_nocancel` (`0x665f50`). -/
def pc20 : List Byte := [0xe8, 0xd7, 0x26, 0x05, 0x00]
theorem pc20_0 : ∀ feat, Dec feat pc20 0 (FV7z.mk .call 64 [.rel 337623] 5) := by dec_rfl
theorem wc_20 : pc20 <+: cfd.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat cfd 20 (FV7z.mk .call 64 [.rel 337623] 5) :=
  Dec.shift (j := 20) (k := 0) (pc20_0 feat) wc_20 (Nat.zero_le _)
theorem tgt_20 : cfd_at.add (20 + 5) + BitVec.ofNat 64 337623 = 0x665f50#64 := by decide

/-- The `call` at 42: `__fcntl64_nocancel` (`0x665f50`). -/
def pc42 : List Byte := [0xe8, 0xc1, 0x26, 0x05, 0x00]
theorem pc42_0 : ∀ feat, Dec feat pc42 0 (FV7z.mk .call 64 [.rel 337601] 5) := by dec_rfl
theorem wc_42 : pc42 <+: cfd.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat cfd 42 (FV7z.mk .call 64 [.rel 337601] 5) :=
  Dec.shift (j := 42) (k := 0) (pc42_0 feat) wc_42 (Nat.zero_le _)
theorem tgt_42 : cfd_at.add (42 + 5) + BitVec.ofNat 64 337601 = 0x665f50#64 := by decide

/-- The `call` at 68: `__fcntl64_nocancel` (`0x665f50`). -/
def pc68 : List Byte := [0xe8, 0xa7, 0x26, 0x05, 0x00]
theorem pc68_0 : ∀ feat, Dec feat pc68 0 (FV7z.mk .call 64 [.rel 337575] 5) := by dec_rfl
theorem wc_68 : pc68 <+: cfd.drop 68 := by decide +kernel
theorem call_68 (feat : Features) : Dec feat cfd 68 (FV7z.mk .call 64 [.rel 337575] 5) :=
  Dec.shift (j := 68) (k := 0) (pc68_0 feat) wc_68 (Nat.zero_le _)
theorem tgt_68 : cfd_at.add (68 + 5) + BitVec.ofNat 64 337575 = 0x665f50#64 := by decide

/-- The `call` at 125: `__open64_nocancel` (`0x666090`). -/
def pc125 : List Byte := [0xe8, 0xae, 0x27, 0x05, 0x00]
theorem pc125_0 : ∀ feat, Dec feat pc125 0 (FV7z.mk .call 64 [.rel 337838] 5) := by dec_rfl
theorem wc_125 : pc125 <+: cfd.drop 125 := by decide +kernel
theorem call_125 (feat : Features) : Dec feat cfd 125 (FV7z.mk .call 64 [.rel 337838] 5) :=
  Dec.shift (j := 125) (k := 0) (pc125_0 feat) wc_125 (Nat.zero_le _)
theorem tgt_125 : cfd_at.add (125 + 5) + BitVec.ofNat 64 337838 = 0x666090#64 := by decide

/-- The `call` at 144: `__fxstat` (`0x665360`). -/
def pc144 : List Byte := [0xe8, 0x6b, 0x1a, 0x05, 0x00]
theorem pc144_0 : ∀ feat, Dec feat pc144 0 (FV7z.mk .call 64 [.rel 334443] 5) := by dec_rfl
theorem wc_144 : pc144 <+: cfd.drop 144 := by decide +kernel
theorem call_144 (feat : Features) : Dec feat cfd 144 (FV7z.mk .call 64 [.rel 334443] 5) :=
  Dec.shift (j := 144) (k := 0) (pc144_0 feat) wc_144 (Nat.zero_le _)
theorem tgt_144 : cfd_at.add (144 + 5) + BitVec.ofNat 64 334443 = 0x665360#64 := by decide

/-- The `call` at 233: `__open64_nocancel` (`0x666090`). -/
def pc233 : List Byte := [0xe8, 0x42, 0x27, 0x05, 0x00]
theorem pc233_0 : ∀ feat, Dec feat pc233 0 (FV7z.mk .call 64 [.rel 337730] 5) := by dec_rfl
theorem wc_233 : pc233 <+: cfd.drop 233 := by decide +kernel
theorem call_233 (feat : Features) : Dec feat cfd 233 (FV7z.mk .call 64 [.rel 337730] 5) :=
  Dec.shift (j := 233) (k := 0) (pc233_0 feat) wc_233 (Nat.zero_le _)
theorem tgt_233 : cfd_at.add (233 + 5) + BitVec.ofNat 64 337730 = 0x666090#64 := by decide

/-- The `call` at 256: `__fxstat` (`0x665360`). -/
def pc256 : List Byte := [0xe8, 0xfb, 0x19, 0x05, 0x00]
theorem pc256_0 : ∀ feat, Dec feat pc256 0 (FV7z.mk .call 64 [.rel 334331] 5) := by dec_rfl
theorem wc_256 : pc256 <+: cfd.drop 256 := by decide +kernel
theorem call_256 (feat : Features) : Dec feat cfd 256 (FV7z.mk .call 64 [.rel 334331] 5) :=
  Dec.shift (j := 256) (k := 0) (pc256_0 feat) wc_256 (Nat.zero_le _)
theorem tgt_256 : cfd_at.add (256 + 5) + BitVec.ofNat 64 334331 = 0x665360#64 := by decide

/-- The `call` at 345: `__open64_nocancel` (`0x666090`). -/
def pc345 : List Byte := [0xe8, 0xd2, 0x26, 0x05, 0x00]
theorem pc345_0 : ∀ feat, Dec feat pc345 0 (FV7z.mk .call 64 [.rel 337618] 5) := by dec_rfl
theorem wc_345 : pc345 <+: cfd.drop 345 := by decide +kernel
theorem call_345 (feat : Features) : Dec feat cfd 345 (FV7z.mk .call 64 [.rel 337618] 5) :=
  Dec.shift (j := 345) (k := 0) (pc345_0 feat) wc_345 (Nat.zero_le _)
theorem tgt_345 : cfd_at.add (345 + 5) + BitVec.ofNat 64 337618 = 0x666090#64 := by decide

/-- The `call` at 368: `__fxstat` (`0x665360`). -/
def pc368 : List Byte := [0xe8, 0x8b, 0x19, 0x05, 0x00]
theorem pc368_0 : ∀ feat, Dec feat pc368 0 (FV7z.mk .call 64 [.rel 334219] 5) := by dec_rfl
theorem wc_368 : pc368 <+: cfd.drop 368 := by decide +kernel
theorem call_368 (feat : Features) : Dec feat cfd 368 (FV7z.mk .call 64 [.rel 334219] 5) :=
  Dec.shift (j := 368) (k := 0) (pc368_0 feat) wc_368 (Nat.zero_le _)
theorem tgt_368 : cfd_at.add (368 + 5) + BitVec.ofNat 64 334219 = 0x665360#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_89 : pret <+: cfd.drop 89 := by decide +kernel
theorem ret_89 (feat : Features) : Dec feat cfd 89 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 89) (k := 0) (pret_0 feat) wt_89 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `sub rsp, 152`. -/
abbrev aR (S : Addr) : Addr := S - 152#64

/-- `errno`: the 4 bytes at `fs:-0x48`. -/
abbrev errnoAt (fb : Addr) : Addr := fb + 18446744073709551544#64

theorem q152 (S : Addr) : S - 152#64 + 152#64 = S := by bv_omega
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

theorem ks_tr {g0 g g' : Gprs} (h : KS g0 g) (h' : KS g g') : KS g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

/-- `wpx` with the Boolean and literal clean-up and the loads of this code. -/
local macro "cfx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, decide_true, decide_false, BitVec.and_self, eq_self_iff_true,
    Bool.true_or, Bool.false_or, ↓reduceIte, BitVec.reduceSetWidth, BitVec.xor_self, BitVec.sub_self,
    BitVec.ofBool_true, BitVec.ofBool_false, BitVec.reduceSub, BitVec.reduceAdd, Op.cmpmi, Op.cmpmif, xz, $ls,*])

/-- A `jne` on a literal the hypothesis `h` says is not there. -/
local macro "lit" h:ident : tactic =>
  `(tactic| all_goals (try (rename_i hx; rw [Bool.not_eq_false', decide_eq_true_eq] at hx; exact absurd hx $h)))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry: the frame, `fcntl (0, F_GETFD)`'s arguments; to the call (20). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 20 ∧
      g' = { g with rax := 0#64, rsp := aR g.rsp, rsi := 1#64, rdi := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cfx [W_0, o0]
  all_goals vfin

/-- From 30: `fcntl (1, F_GETFD)`'s arguments; to the call (42). -/
theorem vc_30 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_30 fb F Wl (fun j' g' _ V' => j' = 42 ∧ g' = { g with rax := 0#64, rsi := 1#64, rdi := 1#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cfx [W_30, o2]
  all_goals vfin

/-- From 56: `fcntl (2, F_GETFD)`'s arguments; to the call (68). -/
theorem vc_56 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_56 fb F Wl (fun j' g' _ V' => j' = 68 ∧ g' = { g with rax := 0#64, rsi := 1#64, rdi := 2#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cfx [W_56, o3]
  all_goals vfin

/-- From 82: the frame dropped; to the `ret` (89). -/
theorem vc_82 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_82 fb F Wl (fun j' g' _ V' => j' = 89 ∧ g' = { g with rsp := g.rsp + 152#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cfx [W_82, o4]
  all_goals vfin

/-! ### The fd 0 -/

/-- From 25, `fcntl`'s answer not -1: to 30. -/
theorem vc_25n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ¬ g.rax.setWidth 32 = 4294967295#32) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 30 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 ⊢
  cfx [W_25, W_96, W_109, o1, o5, o6, h1]
  all_goals vfin

/-- From 25, `fcntl`'s answer -1, `errno` not `EBADF`: to 30. -/
theorem vc_25b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : ¬ rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 30 ∧ g' = { g with rax := 18446744073709551544#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  have hd : decide (rdd(V, fb + 18446744073709551544#64) = 9#32) = false := decide_eq_false h2
  cfx [W_25, W_96, W_109, o1, o5, o6, h1, h2, hd]
  all_goals vfin
  lit h2

/-- From 25, `fcntl`'s answer -1, `errno` `EBADF`: `open`'s arguments; to the call (125). -/
theorem vc_25o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 125 ∧
      g' = { g with rax := 0#64, rdx := 0#64, rsi := 131073#64, rdi := 7268354#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  cfx [W_25, W_96, W_109, o1, o5, o6, h1, h2]
  all_goals vfin

/-- From 130, `open`'s answer not 0: to the `hlt` (192). -/
theorem vc_130f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 0#32) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 192 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 h
  cfx [W_130, W_134, o7, o8, e]
  all_goals vfin

/-- From 130, `open`'s answer 0: `fxstat`'s arguments; to the call (144). -/
theorem vc_130o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 144 ∧ g' = { g with rdx := g.rsp, rsi := 0#64, rdi := 1#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  cfx [W_130, W_134, o7, o8, e]
  all_goals vfin

/-- From 149, `fxstat`'s answer not 0: to the `hlt` (192). -/
theorem vc_149h1 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 0#32) :
    W_149 fb F Wl (fun j' g' _ V' => j' = 192 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 h
  cfx [W_149, W_153, W_169, W_184, o7, o9, o10, o11, e]
  all_goals vfin

/-- From 149, `fxstat`'s answer 0, not a character device: to the `hlt` (192). -/
theorem vc_149h2 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : ¬ rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) :
    W_149 fb F Wl (fun j' g' _ V' => j' = 192 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm f24 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hm
  cfx [W_149, W_153, W_169, W_184, o7, o9, o10, o11, e, d, hm]
  all_goals vfin
  lit hm

/-- From 149, `fxstat`'s answer 0, a character device, not the one: to the `hlt` (192). -/
theorem vc_149h3 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : ¬ rdq(V, g.rsp + 40#64) = 263#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_149 fb F Wl (fun j' g' _ V' => j' = 192 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hr
  cfx [W_149, W_153, W_169, W_184, o7, o9, o10, o11, e, hm, d, hr]
  all_goals vfin
  lit hr

/-- From 149, the fd 0 the device it should be: to 30, `rax` changed. -/
theorem vc_149o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : rdq(V, g.rsp + 40#64) = 263#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_149 fb F Wl (fun j' g' _ V' => j' = 30 ∧ (∃ ra, g' = { g with rax := ra }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  cfx [W_149, W_153, W_169, W_184, o7, o9, o10, o11, e, hm, hr]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ### The fd 1 -/

/-- From 47, `fcntl`'s answer not -1: to 56. -/
theorem vc_47n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ¬ g.rax.setWidth 32 = 4294967295#32) :
    W_47 fb F Wl (fun j' g' _ V' => j' = 56 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 ⊢
  cfx [W_47, W_200, W_217, o1, o12, o13, h1]
  all_goals vfin

/-- From 47, `fcntl`'s answer -1, `errno` not `EBADF`: to 56. -/
theorem vc_47b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : ¬ rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_47 fb F Wl (fun j' g' _ V' => j' = 56 ∧ g' = { g with rax := 18446744073709551544#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  have hd : decide (rdd(V, fb + 18446744073709551544#64) = 9#32) = false := decide_eq_false h2
  cfx [W_47, W_200, W_217, o1, o12, o13, h1, h2, hd]
  all_goals vfin
  lit h2

/-- From 47, `fcntl`'s answer -1, `errno` `EBADF`: `open`'s arguments; to the call (233). -/
theorem vc_47o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_47 fb F Wl (fun j' g' _ V' => j' = 233 ∧
      g' = { g with rax := 0#64, rdx := 0#64, rsi := 131072#64, rdi := 7268364#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  cfx [W_47, W_200, W_217, o1, o12, o13, h1, h2]
  all_goals vfin

/-- From 238, `open`'s answer not 1: to the `hlt` (304). -/
theorem vc_238f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 1#32) :
    W_238 fb F Wl (fun j' g' _ V' => j' = 304 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have hd : decide (BitVec.setWidth 32 rax = 1#32) = false := decide_eq_false h
  cfx [W_238, W_243, o14, o15, h, hd]
  all_goals vfin
  lit h

/-- From 238, `open`'s answer 1: `fxstat`'s arguments; to the call (256). -/
theorem vc_238o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 1#32) :
    W_238 fb F Wl (fun j' g' _ V' => j' = 256 ∧ g' = { g with rdx := g.rsp, rsi := 1#64, rdi := 1#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cfx [W_238, W_243, o14, o15, h]
  all_goals vfin

/-- From 261, `fxstat`'s answer not 0: to the `hlt` (304). -/
theorem vc_261h1 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 0#32) :
    W_261 fb F Wl (fun j' g' _ V' => j' = 304 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 h
  cfx [W_261, W_265, W_281, W_296, o7, o9, o16, o11, e]
  all_goals vfin

/-- From 261, `fxstat`'s answer 0, not a character device: to the `hlt` (304). -/
theorem vc_261h2 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : ¬ rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) :
    W_261 fb F Wl (fun j' g' _ V' => j' = 304 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm f24 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hm
  cfx [W_261, W_265, W_281, W_296, o7, o9, o16, o11, e, d, hm]
  all_goals vfin
  lit hm

/-- From 261, `fxstat`'s answer 0, a character device, not the one: to the `hlt` (304). -/
theorem vc_261h3 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : ¬ rdq(V, g.rsp + 40#64) = 259#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_261 fb F Wl (fun j' g' _ V' => j' = 304 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hr
  cfx [W_261, W_265, W_281, W_296, o7, o9, o16, o11, e, hm, d, hr]
  all_goals vfin
  lit hr

/-- From 261, the fd 1 the device it should be: to 56, `rax` changed. -/
theorem vc_261o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : rdq(V, g.rsp + 40#64) = 259#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_261 fb F Wl (fun j' g' _ V' => j' = 56 ∧ (∃ ra, g' = { g with rax := ra }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  cfx [W_261, W_265, W_281, W_296, o7, o9, o16, o11, e, hm, hr]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ### The fd 2 -/

/-- From 73, `fcntl`'s answer not -1: to 82. -/
theorem vc_73n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ¬ g.rax.setWidth 32 = 4294967295#32) :
    W_73 fb F Wl (fun j' g' _ V' => j' = 82 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 ⊢
  cfx [W_73, W_312, W_329, o1, o17, o18, h1]
  all_goals vfin

/-- From 73, `fcntl`'s answer -1, `errno` not `EBADF`: to 82. -/
theorem vc_73b {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : ¬ rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_73 fb F Wl (fun j' g' _ V' => j' = 82 ∧ g' = { g with rax := 18446744073709551544#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  have hd : decide (rdd(V, fb + 18446744073709551544#64) = 9#32) = false := decide_eq_false h2
  cfx [W_73, W_312, W_329, o1, o17, o18, h1, h2, hd]
  all_goals vfin
  lit h2

/-- From 73, `fcntl`'s answer -1, `errno` `EBADF`: `open`'s arguments; to the call (345). -/
theorem vc_73o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax.setWidth 32 = 4294967295#32)
    (h2 : rdd(V, errnoAt fb) = 9#32) (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_73 fb F Wl (fun j' g' _ V' => j' = 345 ∧
      g' = { g with rax := 0#64, rdx := 0#64, rsi := 131072#64, rdi := 7268364#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at h1 h2 fe ⊢
  cfx [W_73, W_312, W_329, o1, o17, o18, h1, h2]
  all_goals vfin

/-- From 350, `open`'s answer not 2: to the `hlt` (416). -/
theorem vc_350f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 2#32) :
    W_350 fb F Wl (fun j' g' _ V' => j' = 416 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have hd : decide (BitVec.setWidth 32 rax = 2#32) = false := decide_eq_false h
  cfx [W_350, W_355, o19, o20, h, hd]
  all_goals vfin
  lit h

/-- From 350, `open`'s answer 2: `fxstat`'s arguments; to the call (368). -/
theorem vc_350o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 2#32) :
    W_350 fb F Wl (fun j' g' _ V' => j' = 368 ∧ g' = { g with rdx := g.rsp, rsi := 2#64, rdi := 1#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cfx [W_350, W_355, o19, o20, h]
  all_goals vfin

/-- From 373, `fxstat`'s answer not 0: to the `hlt` (416). -/
theorem vc_373h1 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rax.setWidth 32 = 0#32) :
    W_373 fb F Wl (fun j' g' _ V' => j' = 416 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 h
  cfx [W_373, W_377, W_393, W_408, o7, o9, o16, o11, e]
  all_goals vfin

/-- From 373, `fxstat`'s answer 0, not a character device: to the `hlt` (416). -/
theorem vc_373h2 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : ¬ rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) :
    W_373 fb F Wl (fun j' g' _ V' => j' = 416 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm f24 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hm
  cfx [W_373, W_377, W_393, W_408, o7, o9, o16, o11, e, d, hm]
  all_goals vfin
  lit hm

/-- From 373, `fxstat`'s answer 0, a character device, not the one: to the `hlt` (416). -/
theorem vc_373h3 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : ¬ rdq(V, g.rsp + 40#64) = 259#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_373 fb F Wl (fun j' g' _ V' => j' = 416 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  have d := decide_eq_false hr
  cfx [W_373, W_377, W_393, W_408, o7, o9, o16, o11, e, hm, d, hr]
  all_goals vfin
  lit hr

/-- From 373, the fd 2 the device it should be: to 82, `rax` changed. -/
theorem vc_373o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.setWidth 32 = 0#32)
    (hm : rdd(V, g.rsp + 24#64) &&& 61440#32 = 8192#32) (hr : rdq(V, g.rsp + 40#64) = 259#64)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) :
    W_373 fb F Wl (fun j' g' _ V' => j' = 82 ∧ (∃ ra, g' = { g with rax := ra }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hm hr f24 f40 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 h
  cfx [W_373, W_377, W_393, W_408, o7, o9, o16, o11, e, hm, hr]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ## The callees and the hypotheses of the runs -/

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and bytes with `N`, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (cfd_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cfd_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = cfd_at.add j → P Y.cpu.gpr W → GoG prof L o gev gP gE Y t

/-- At a cut point: `rsp` = `aR S`, the callee-saved registers of `g0`, the bytes with `I`. -/
abbrev PS (S : Addr) (g0 : Gprs) (I : (Addr → Byte) → Prop) (g : Gprs) (W : Addr → Byte) : Prop :=
  g.rsp = aR S ∧ KS g0 g ∧ I W

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L cfd_at cfd
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hra : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)
  f24 : ∀ i < 4, Foot F.data (Addr.add (aR S + 24#64) i)
  f40 : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)
  cF : ∃ code : List Byte, CodeIn L 0x665f50#64 code ∧ 0 < code.length
  cO : ∃ code : List Byte, CodeIn L 0x666090#64 code ∧ 0 < code.length
  cX : ∃ code : List Byte, CodeIn L 0x665360#64 code ∧ 0 < code.length
  kF0 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665f50#64 25 W (fun g => g.rdi = 0#64 ∧ g.rsi = 1#64) I
  kF1 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665f50#64 47 W (fun g => g.rdi = 1#64 ∧ g.rsi = 1#64) I
  kF2 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665f50#64 73 W (fun g => g.rdi = 2#64 ∧ g.rsi = 1#64) I
  kO0 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x666090#64 130 W
    (fun g => g.rdi = 7268354#64 ∧ g.rsi = 131073#64 ∧ g.rdx = 0#64) I
  kO1 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x666090#64 238 W
    (fun g => g.rdi = 7268364#64 ∧ g.rsi = 131072#64 ∧ g.rdx = 0#64) I
  kO2 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x666090#64 350 W
    (fun g => g.rdi = 7268364#64 ∧ g.rsi = 131072#64 ∧ g.rdx = 0#64) I
  kX0 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665360#64 149 W
    (fun g => g.rdi = 1#64 ∧ g.rsi = 0#64 ∧ g.rdx = aR S) I
  kX1 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665360#64 261 W
    (fun g => g.rdi = 1#64 ∧ g.rsi = 1#64 ∧ g.rdx = aR S) I
  kX2 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S 0x665360#64 373 W
    (fun g => g.rdi = 1#64 ∧ g.rsi = 2#64 ∧ g.rdx = aR S) I
  kh : ∀ W, I W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    (Y.cpu.rip = cfd_at.add 192 ∨ Y.cpu.rip = cfd_at.add 304 ∨ Y.cpu.rip = cfd_at.add 416) →
    GoG prof L o gev gP gE Y t'
  kr : ∀ (W : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
    Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = S + 8 → KS g0 Z.cpu.gpr → I W → GoG prof L o gev gP gE Z t'

/-! ## The runs -/

section Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) {U : State} {t₁ : Nat} {W : Addr → Byte}
    {j R : Nat} {ent : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = cfd_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < cfd.length) (hd : Dec prof.feat cfd j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : cfd_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 5) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cfd_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ

/-- From 82: the frame dropped, the `ret`, to `kr`. -/
theorem R82 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 82 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  refine (c_82 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_82 (g := Y.cpu.gpr)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = S := by
    rw [hgU]
    show Y.cpu.gpr.rsp + 152#64 = S
    rw [hs]
    exact q152 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_89 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact E.hra W hI) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine E.kr W Z t₂ hKZ hAZ hrZ ?_ ?_ hI
  · rw [hgZ]
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ, hgU]
    exact hks

/-- From 373 (back from `fxstat`): the device checked; to 82 or the `hlt` (416). -/
theorem R373 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 373 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  have f24 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by rw [hs]; exact E.f24
  have f40 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 40#64) i) := by rw [hs]; exact E.f40
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases h2 : rdd(W, Y.cpu.gpr.rsp + 24#64) &&& 61440#32 = 8192#32
    · by_cases h3 : rdq(W, Y.cpu.gpr.rsp + 40#64) = 259#64
      · refine (c_373 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_373o h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact R82 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
      · refine (c_373 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_373h3 h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inr hrU))
    · refine (c_373 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_373h2 h1 h2 f24) ?_
      rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inr hrU))
  · refine (c_373 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_373h1 (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inr hrU))

/-- From 350 (back from `open`): `fxstat (1, 2, &st)` (368) when the answer is 2, else the `hlt` (416). -/
theorem R350 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 350 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h : Y.cpu.gpr.rax.setWidth 32 = 2#32
  · refine (c_350 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_350o (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
    refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_368 _) tgt_368 E.cX (E.kX2 W hI)
      (by rw [hgU]; exact ⟨rfl, rfl, hs⟩) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact R373 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
  · refine (c_350 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_350f (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inr hrU))

/-- From 73 (back from `fcntl`): on to 82 unless the fd 2 is closed (`EBADF`), else `open` (345). -/
theorem R73 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 73 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 4294967295#32
  · by_cases h2 : rdd(W, errnoAt fb) = 9#32
    · refine (c_73 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_73o h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
      refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_345 _) tgt_345 E.cO (E.kO2 W hI)
        (by rw [hgU]; exact ⟨rfl, rfl, rfl⟩) ?_
      intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
      exact R350 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
    · refine (c_73 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_73b h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact R82 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
  · refine (c_73 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_73n (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact R82 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩

/-- From 56: `fcntl (2, F_GETFD)` (68), from its return to 73. -/
theorem R56 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 56 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  refine (c_56 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_56 (g := Y.cpu.gpr) (V := W)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
  refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_68 _) tgt_68 E.cF (E.kF2 W hI)
    (by rw [hgU]; exact ⟨rfl, rfl⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact R73 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩

/-- From 261 (back from `fxstat`): the device checked; to 56 or the `hlt` (304). -/
theorem R261 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 261 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  have f24 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by rw [hs]; exact E.f24
  have f40 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 40#64) i) := by rw [hs]; exact E.f40
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases h2 : rdd(W, Y.cpu.gpr.rsp + 24#64) &&& 61440#32 = 8192#32
    · by_cases h3 : rdq(W, Y.cpu.gpr.rsp + 40#64) = 259#64
      · refine (c_261 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_261o h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact R56 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
      · refine (c_261 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_261h3 h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inl hrU))
    · refine (c_261 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_261h2 h1 h2 f24) ?_
      rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inl hrU))
  · refine (c_261 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_261h1 (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inl hrU))

/-- From 238 (back from `open`): `fxstat (1, 1, &st)` (256) when the answer is 1, else the `hlt` (304). -/
theorem R238 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 238 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h : Y.cpu.gpr.rax.setWidth 32 = 1#32
  · refine (c_238 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_238o (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
    refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_256 _) tgt_256 E.cX (E.kX1 W hI)
      (by rw [hgU]; exact ⟨rfl, rfl, hs⟩) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact R261 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
  · refine (c_238 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_238f (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inr (Or.inl hrU))

/-- From 47 (back from `fcntl`): on to 56 unless the fd 1 is closed (`EBADF`), else `open` (233). -/
theorem R47 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 47 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 4294967295#32
  · by_cases h2 : rdd(W, errnoAt fb) = 9#32
    · refine (c_47 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_47o h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
      refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_233 _) tgt_233 E.cO (E.kO1 W hI)
        (by rw [hgU]; exact ⟨rfl, rfl, rfl⟩) ?_
      intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
      exact R238 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
    · refine (c_47 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_47b h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact R56 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
  · refine (c_47 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_47n (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact R56 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩

/-- From 30: `fcntl (1, F_GETFD)` (42), from its return to 47. -/
theorem R30 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 30 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  refine (c_30 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_30 (g := Y.cpu.gpr) (V := W)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
  refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_42 _) tgt_42 E.cF (E.kF1 W hI)
    (by rw [hgU]; exact ⟨rfl, rfl⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact R47 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩

/-- From 149 (back from `fxstat`): the device checked; to 30 or the `hlt` (192). -/
theorem R149 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 149 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  have f24 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by rw [hs]; exact E.f24
  have f40 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 40#64) i) := by rw [hs]; exact E.f40
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases h2 : rdd(W, Y.cpu.gpr.rsp + 24#64) &&& 61440#32 = 8192#32
    · by_cases h3 : rdq(W, Y.cpu.gpr.rsp + 40#64) = 263#64
      · refine (c_149 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_149o h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact R30 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
      · refine (c_149 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_149h3 h1 h2 h3 f24 f40) ?_
        rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact E.kh W hI U t₁ hKU hAU (Or.inl hrU)
    · refine (c_149 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_149h2 h1 h2 f24) ?_
      rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact E.kh W hI U t₁ hKU hAU (Or.inl hrU)
  · refine (c_149 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_149h1 (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inl hrU)

/-- From 130 (back from `open`): `fxstat (1, 0, &st)` (144) when the answer is 0, else the `hlt` (192). -/
theorem R130 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 130 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h : Y.cpu.gpr.rax.setWidth 32 = 0#32
  · refine (c_130 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_130o (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
    refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_144 _) tgt_144 E.cX (E.kX0 W hI)
      (by rw [hgU]; exact ⟨rfl, rfl, hs⟩) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact R149 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
  · refine (c_130 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_130f (V := W) h) ?_
    rintro j' g fl V₁ ⟨rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact E.kh W hI U t₁ hKU hAU (Or.inl hrU)

/-- From 25 (back from `fcntl`): on to 30 unless the fd 0 is closed (`EBADF`), else `open` (125). -/
theorem R25 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) :
    AtJ prof F Wl L s₀ o gev gP gE 25 (PS S g0 I) := by
  intro Y W t hK hA hr ⟨hs, hks, hI⟩
  by_cases h1 : Y.cpu.gpr.rax.setWidth 32 = 4294967295#32
  · by_cases h2 : rdd(W, errnoAt fb) = 9#32
    · refine (c_25 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_25o h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = aR S := by rw [hgU]; exact hs
      refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_125 _) tgt_125 E.cO (E.kO0 W hI)
        (by rw [hgU]; exact ⟨rfl, rfl, rfl⟩) ?_
      intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
      exact R130 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr (by rw [hgU]; exact hks) hkZ, hIZ⟩
    · refine (c_25 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_25b h1 h2 E.fe) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact R30 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩
  · refine (c_25 prof fb).run E.c E.hfs E.hin _ hK hA hr (vc_25n (V := W) h1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact R30 E U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hs, by rw [hgU]; exact hks, hI⟩

/-- `__libc_check_standard_fds ()` from its entry (`rsp` = `S`, the registers `g0`, the bytes with `I`): to the
return address with `rsp` = `S + 8` and the callee-saved registers of `g0` (`kr`), or to a `hlt` (`kh`). -/
theorem cfd_ok (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cfd_at) (hS : X.cpu.gpr.rsp = S)
    (hg : X.cpu.gpr = g0) (hI : I V) : GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 (g := X.cpu.gpr)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = aR S := by
    rw [hgU]
    show aR X.cpu.gpr.rsp = aR S
    rw [hS]
  refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_20 _) tgt_20 E.cF (E.kF0 V hI)
    (by rw [hgU]; exact ⟨rfl, rfl⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  have k0 : KS g0 U.cpu.gpr := by
    rw [hgU, ← hg]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact R25 E Z W' t₃ hKZ hAZ hrZ ⟨hsZ, ks_tr k0 hkZ, hIZ⟩

end Runs

end FV7z.Cfd
