import FV7z.C103.Code
import FV7z.Hca.Holds
import FV7z.Lemmas.Signed
/-!
# `init_cacheinfo`: the contract and the invariants of its cut points (PLAN.md M, ctor 103)

glibc's `dl_init_cacheinfo` (`sysdeps/x86/dl-cacheinfo.h`, inlined into `init_cacheinfo`) at `0x41cef0` in `7zzs`
(offset 3504 of `sti`). Its frame: the six saved registers (`P6`, 48 bytes below the return address) and 8 bytes
(`fr`, 56 below). It reads `cpu_features` (8014560–8014727) and the two jump tables (`handle_amd`'s at `0x6f2000`, its
own at `0x6f20a4`), stores into the globals `Gw` (`__x86_shared_cache_size` and friends) and calls `handle_intel` (3758,
3771, 3784) or `handle_amd` (4040, 4053, 4066), whose frames are below its own: 192 bytes below the return address in
all.

The loops: `cpuid(4)` over the subleaves `ecx` (3858–3929) until the cache type is 0, at subleaf 64 at the latest
(H-CPU-cache, `Glibc.CacheEnds.leaf4`); `cpuid(0xB)` over `esi` (4329–4469) until the level type is 0
(`CacheEnds.leafB`). Their measures: `10 · (65 - ecx)` and `20 · (65 - esi)` plus the place in the round. The four
`idiv`s divide by positive numbers: 4 (3707), the threads of a cache (3981, `edi < 2^32` and not 0), the cores'
`threads` (4005, `r9d` at most 1024), `ecx` (4223, not 0); the three `bsr`s take sources not 0.

`Te` is what it needs at its entry, `Rc` what holds at its return address: `rsp` 8 up, `rbx`, `rbp`, `r12`–`r15` as at
the entry, the bytes as at the entry (`Kd`) but for the 192 below the return address and the globals.
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
open FV7z.Hca (hca hca_at hca_length hca_jt)
open FV7z.Hin (P6 p_1 p_2 p_3 p_4 p_5 p_6 tc t8 ts8 fsub sa8 hin_at hin_at_eq)

/-- The entry. -/
abbrev c103_at : Addr := 0x41cef0
theorem c103_at_eq : Addr.add sti_at 3504 = c103_at := by decide

/-! ## The jump table at `0x6f20a4`: 39 offsets of 32 bits, to 3967 or 4570 -/

def c103_jt : List Byte := [
  0x76, 0xb2, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x76, 0xb2, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x76, 0xb2, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x76, 0xb2, 0xd2, 0xff,
  0x1b, 0xb0, 0xd2, 0xff, 0x1b, 0xb0, 0xd2, 0xff, 0x76, 0xb2, 0xd2, 0xff]

theorem c103_jt_pin : Exe.bytesAt V2606.zzs.blob 0x6f20a4 156 = some c103_jt := by decide +kernel

set_option maxRecDepth 100000 in
/-- Every entry leads to 3967 or to 4570. -/
theorem jt_tg : ∀ k < 39,
    (ofBytesLE 32 ((c103_jt.drop (4 * k)).take 4)).signExtend 64 + 7282852#64 = Addr.add sti_at 3967 ∨
    (ofBytesLE 32 ((c103_jt.drop (4 * k)).take 4)).signExtend 64 + 7282852#64 = Addr.add sti_at 4570 := by
  decide +kernel

theorem jaddr (k : BitVec 32) (h : k.toNat ≤ 38) :
    7282852#64 + k.setWidth 64 * 4#64 = Addr.add 7282852#64 (4 * k.toNat) := by
  unfold Addr.add; bv_omega

/-! ## The contract -/

/-- The globals it stores into. -/
def Gw (a : Addr) : Prop :=
  (7942880 ≤ a.toNat ∧ a.toNat < 7942944) ∨ (8029224 ≤ a.toNat ∧ a.toNat < 8029236)

/-- What `init_cacheinfo` needs at its entry (`rsp` at the return address, `fb` the `fs` base). -/
structure Te (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb : Addr) (g : Gprs)
    (V : Addr → Byte) : Prop where
  /-- Its frame, the callees' frames and their return addresses' slots. -/
  st : ∀ i < 192, Foot Wl (Addr.add (g.rsp - 192#64) i)
  /-- The same and the return address. -/
  ld : ∀ i < 200, Foot F.data (Addr.add (g.rsp - 192#64) i)
  lo : 8029236 + 192 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  /-- The canary at `fs:0x28` (for `handle_intel`), apart from the stack. -/
  cn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  cnf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  cna : (fb + 40#64).toNat + 8 + 192 ≤ g.rsp.toNat ∨ g.rsp.toNat ≤ (fb + 40#64).toNat
  /-- `cpu_features`. -/
  cpu : ∀ x : Addr, 8014560 ≤ x.toNat → x.toNat < 8014728 → Foot F.data x
  /-- The jump tables and `intel_02_known`. -/
  tab : ∀ x : Addr, 7282688 ≤ x.toNat → x.toNat < 7283552 → Foot F.data x
  gw : ∀ x : Addr, Gw x → Foot Wl x ∧ Foot F.data x
  hjt : List.map V (byteAddrs 0x6f2000#64 36) = hca_jt
  cjt : List.map V (byteAddrs 7282852#64 156) = c103_jt
  ret : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
    ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)) = e₂.add j₂

/-- `rsp` after the six `push`es and `sub rsp, 8`. -/
abbrev fr (s : Addr) : Addr := s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64

/-- The bytes that stay as after the `push`es: not in the 144 bytes below them, not the globals. -/
def Out (s a : Addr) : Prop := (a.toNat + 192 < s.toNat ∨ s.toNat ≤ a.toNat + 48) ∧ ¬ Gw a

/-- The bytes as at the entry but for the 192 below the return address and the globals. -/
def Kd (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ a : Addr, (a.toNat + 192 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) → ¬ Gw a → V a = V₀ a

/-- At the return address. -/
def Rc (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15 ∧ Kd g₀ V₀ V

/-! ## The invariants -/

/-- In the frame. -/
def Mf (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = fr g₀.rsp ∧ ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a

/-- `r15`: 2 for `threads_l2`, 3 for `threads_l3`. -/
def R15 (r : BitVec 64) : Prop := r = 2#64 ∨ r = 3#64

/-- In the leaf-4 loop: `threads` (`r9d`) at most 1023, `eax` 4 for `cpuid`; for `threads_l2`, `edi` is -1 and the
two flags in `esi` at most 1. -/
def L4 (g : Gprs) : Prop :=
  R15 g.r15 ∧ (g.r9.setWidth 32).toNat ≤ 1023 ∧ g.r10 = 4#64 ∧
    (g.r15 = 2#64 → g.rdi.setWidth 32 = 4294967295#32 ∧ (g.rsi = 1#64 ∨ g.rsi = 0#64))

/-- The leaf-`0xB` loop's flags in `r8`: bit 0 (`threads_l2`'s level still to find) only for `threads_l3` with
`threads` not 0, bit 1 only with the `bsr`'s source not 0. -/
def Bits (g : Gprs) : Prop :=
  (g.r8 = 0#64 ∨ g.r8 = 1#64 ∨ g.r8 = 2#64 ∨ g.r8 = 3#64) ∧
    (g.r8 = 1#64 ∨ g.r8 = 3#64 → g.r15 = 3#64 ∧ g.r9.setWidth 32 ≠ 0#32) ∧
    (g.r8 = 2#64 ∨ g.r8 = 3#64 →
      (g.r15 = 3#64 → g.rdi.setWidth 32 ≠ 0#32) ∧ (g.r15 = 2#64 → g.r9.setWidth 32 ≠ 0#32))

/-- In the leaf-`0xB` loop. -/
def LB (g : Gprs) : Prop :=
  R15 g.r15 ∧ (g.r9.setWidth 32).toNat ≤ 1023 ∧ g.r13 = 11#64 ∧ Bits g

/-- At the `bsr`s of bit 1. -/
def P69 (g : Gprs) : Prop :=
  R15 g.r15 ∧ (g.r9.setWidth 32).toNat ≤ 1023 ∧ g.r13 = 11#64 ∧ (g.r10.setWidth 32).toNat ≤ 64 ∧
    (g.r8 = 2#64 ∨ g.r8 = 3#64 ∧ g.r15 = 3#64 ∧ g.r9.setWidth 32 ≠ 0#32)

/-- Before the leaf-`0xB` loop: its two flags in `rax` and `rdx`. -/
def A06 (g : Gprs) : Prop :=
  R15 g.r15 ∧ (g.r9.setWidth 32).toNat ≤ 1023 ∧ g.rsi.setWidth 32 = 0#32 ∧ (g.rax = 0#64 ∨ g.rax = 1#64) ∧
    (g.rdx = 0#64 ∨ g.rdx = 1#64) ∧ (g.rdx = 1#64 → g.r15 = 3#64 ∧ g.r9.setWidth 32 ≠ 0#32) ∧
    (g.rax = 1#64 → (g.r15 = 3#64 → g.rdi.setWidth 32 ≠ 0#32) ∧ (g.r15 = 2#64 → g.r9.setWidth 32 ≠ 0#32))

/-- After `cqo`. -/
def Cq (g : Gprs) : Prop := g.rdx = if g.rax.msb then BitVec.allOnes 64 else 0

/-- `threads` at most 1024. -/
def N9 (g : Gprs) : Prop := (g.r9.setWidth 32).toNat ≤ 1024

/-- The invariants of the cut points (and of the instructions the pieces stop at), with the measure `n`. -/
def Ih (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  if ℓ = 3504 then n = 100000 ∧ g = g₀ ∧ V = V₀ else
  if ℓ = 3566 then n = 1000 ∧ Mf g₀ V₀ g V else
  if ℓ = 3569 then n = 990 ∧ Mf g₀ V₀ g V else
  if ℓ = 3617 then n = 980 ∧ Mf g₀ V₀ g V else
  if ℓ = 3629 then n = 970 ∧ Mf g₀ V₀ g V else
  if ℓ = 3632 then n = 960 ∧ Mf g₀ V₀ g V else
  if ℓ = 3680 then n = 950 ∧ Mf g₀ V₀ g V else
  if ℓ = 3707 then n = 940 ∧ Mf g₀ V₀ g V ∧ g.rcx = 4#64 ∧ Cq g else
  if ℓ = 3710 then n = 930 ∧ Mf g₀ V₀ g V else
  if ℓ = 3758 then n = 90000 ∧ Mf g₀ V₀ g V ∧ g.rdi = 188#64 else
  if ℓ = 3763 then n = 89990 ∧ Mf g₀ V₀ g V else
  if ℓ = 3771 then n = 89980 ∧ Mf g₀ V₀ g V ∧ g.rdi = 191#64 else
  if ℓ = 3776 then n = 89970 ∧ Mf g₀ V₀ g V else
  if ℓ = 3784 then n = 89960 ∧ Mf g₀ V₀ g V ∧ g.rdi = 194#64 else
  if ℓ = 3789 then n = 89950 ∧ Mf g₀ V₀ g V else
  if ℓ = 3809 then n = 89940 ∧ Mf g₀ V₀ g V ∧
    (g.r15 = 2#64 ∧ g.rdi.setWidth 32 = 4294967295#32 ∨ g.r15 = 3#64 ∧ g.rdi.setWidth 32 = 0#32) else
  if ℓ = 3841 then n = 89930 ∧ Mf g₀ V₀ g V ∧ R15 g.r15 ∧
    (g.r15 = 2#64 → g.rdi.setWidth 32 = 4294967295#32 ∧ (g.rsi = 1#64 ∨ g.rsi = 0#64)) else
  if ℓ = 3858 then n = 60000 + 10 * (65 - (g.rcx.setWidth 32).toNat) + 8 ∧ Mf g₀ V₀ g V ∧ L4 g ∧
    (g.rcx.setWidth 32).toNat ≤ 64 else
  if ℓ = 3865 then n = 60000 + 10 * (66 - (g.r8.setWidth 32).toNat) + 6 ∧ Mf g₀ V₀ g V ∧ L4 g ∧
    (g.r8.setWidth 32).toNat = (g.rcx.setWidth 32).toNat + 1 ∧ (g.rcx.setWidth 32).toNat ≤ 64 ∧
    g.rax.setWidth 32 = 4#32 else
  if ℓ = 3867 then n = 60000 + 10 * (66 - (g.r8.setWidth 32).toNat) + 4 ∧ Mf g₀ V₀ g V ∧ L4 g ∧
    (g.r8.setWidth 32).toNat ≤ 65 ∧ ((g.r8.setWidth 32).toNat = 65 → g.rax.setWidth 8 &&& 31#8 = 0#8) else
  if ℓ = 3921 then n = 60000 + 10 * (66 - (g.r8.setWidth 32).toNat) + 2 ∧ Mf g₀ V₀ g V ∧ L4 g ∧
    (g.r8.setWidth 32).toNat ≤ 64 else
  if ℓ = 3929 then n = 60000 + 10 * (66 - (g.r8.setWidth 32).toNat) + 1 ∧ Mf g₀ V₀ g V ∧ L4 g ∧
    (g.r8.setWidth 32).toNat ≤ 64 else
  if ℓ = 4306 then n = 41500 ∧ Mf g₀ V₀ g V ∧ A06 g else
  if ℓ = 4332 then n = 40000 + 20 * (65 - (g.rsi.setWidth 32).toNat) + 19 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.rsi.setWidth 32).toNat ≤ 64 else
  if ℓ = 4346 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 17 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.r10.setWidth 32).toNat = (g.rsi.setWidth 32).toNat + 1 ∧ (g.rsi.setWidth 32).toNat ≤ 64 ∧
    g.rax.setWidth 32 = 11#32 ∧ g.rcx.setWidth 32 = g.rsi.setWidth 32 else
  if ℓ = 4348 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 15 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.r10.setWidth 32).toNat ≤ 65 ∧
    ((g.r10.setWidth 32).toNat = 65 → g.rcx.setWidth 32 &&& 65280#32 = 0#32) else
  if ℓ = 4380 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 13 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.r10.setWidth 32).toNat ≤ 64 ∧ (g.r8 = 1#64 ∨ g.r8 = 3#64) ∧ 1 ≤ (g.rbx.setWidth 32).toNat ∧
    (g.rbx.setWidth 32).toNat ≤ 255 else
  if ℓ = 4384 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 11 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.r10.setWidth 32).toNat ≤ 64 ∧ (g.r8 = 1#64 ∨ g.r8 = 3#64) ∧ 1 ≤ (g.rbx.setWidth 32).toNat ∧
    (g.rbx.setWidth 32).toNat ≤ 255 else
  if ℓ = 4329 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 5 ∧ Mf g₀ V₀ g V ∧ LB g ∧
    (g.r10.setWidth 32).toNat ≤ 64 else
  if ℓ = 4454 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 13 ∧ Mf g₀ V₀ g V ∧ P69 g ∧
    g.r15 = 3#64 ∧ g.rdi.setWidth 32 ≠ 0#32 else
  if ℓ = 4457 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 11 ∧ Mf g₀ V₀ g V ∧ P69 g else
  if ℓ = 4594 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 13 ∧ Mf g₀ V₀ g V ∧ P69 g ∧
    g.r8 = 2#64 ∧ g.r9.setWidth 32 ≠ 0#32 ∧ (g.rbx.setWidth 32).toNat ≤ 255 else
  if ℓ = 4598 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 11 ∧ Mf g₀ V₀ g V ∧ P69 g ∧
    g.r8 = 2#64 ∧ (g.rbx.setWidth 32).toNat ≤ 255 else
  if ℓ = 4469 then n = 40000 + 20 * (66 - (g.r10.setWidth 32).toNat) + 9 ∧ Mf g₀ V₀ g V ∧ P69 g else
  if ℓ = 4409 then n = 30000 ∧ Mf g₀ V₀ g V ∧ (g.r9.setWidth 32).toNat ≤ 1023 else
  if ℓ = 4502 then n = 29990 ∧ Mf g₀ V₀ g V ∧ N9 g else
  if ℓ = 4570 then n = 29980 ∧ Mf g₀ V₀ g V ∧ N9 g else
  if ℓ = 3960 then n = 5000 ∧ Mf g₀ V₀ g V ∧ N9 g else
  if ℓ = 3967 then n = 4990 ∧ Mf g₀ V₀ g V ∧ N9 g ∧ g.rdi.toNat < 2 ^ 32 else
  if ℓ = 3981 then n = 4980 ∧ Mf g₀ V₀ g V ∧ N9 g ∧ g.rdi ≠ 0#64 ∧ g.rdi.msb = false ∧ Cq g else
  if ℓ = 3984 then n = 4970 ∧ Mf g₀ V₀ g V ∧ N9 g else
  if ℓ = 3987 then n = 4960 ∧ Mf g₀ V₀ g V ∧ N9 g else
  if ℓ = 4005 then n = 4950 ∧ Mf g₀ V₀ g V ∧ g.r9 ≠ 0#64 ∧ g.r9.msb = false ∧ Cq g else
  if ℓ = 4008 then n = 4940 ∧ Mf g₀ V₀ g V else
  if ℓ = 4011 then n = 4930 ∧ Mf g₀ V₀ g V else
  if ℓ = 4014 then n = 4920 ∧ Mf g₀ V₀ g V else
  if ℓ = 4040 then n = 80000 ∧ Mf g₀ V₀ g V ∧ g.rdi = 188#64 else
  if ℓ = 4045 then n = 79990 ∧ Mf g₀ V₀ g V else
  if ℓ = 4053 then n = 79980 ∧ Mf g₀ V₀ g V ∧ g.rdi = 191#64 else
  if ℓ = 4058 then n = 79970 ∧ Mf g₀ V₀ g V else
  if ℓ = 4066 then n = 79960 ∧ Mf g₀ V₀ g V ∧ g.rdi = 194#64 else
  if ℓ = 4071 then n = 79950 ∧ Mf g₀ V₀ g V else
  if ℓ = 4079 then n = 79940 ∧ Mf g₀ V₀ g V else
  if ℓ = 4081 then n = 79930 ∧ Mf g₀ V₀ g V else
  if ℓ = 4100 then n = 79920 ∧ Mf g₀ V₀ g V else
  if ℓ = 4102 then n = 79910 ∧ Mf g₀ V₀ g V else
  if ℓ = 4197 then n = 79900 ∧ Mf g₀ V₀ g V else
  if ℓ = 4199 then n = 79890 ∧ Mf g₀ V₀ g V else
  if ℓ = 4216 then n = 79880 ∧ Mf g₀ V₀ g V ∧ g.rcx.setWidth 32 ≠ 0#32 else
  if ℓ = 4223 then n = 79870 ∧ Mf g₀ V₀ g V ∧ g.rcx ≠ 0#64 ∧ g.rcx.msb = false ∧ Cq g else
  if ℓ = 4226 then n = 79860 ∧ Mf g₀ V₀ g V else
  if ℓ = 4125 then n = 79850 ∧ Mf g₀ V₀ g V else
  if ℓ = 4128 then n = 79840 ∧ Mf g₀ V₀ g V else
  if ℓ = 4141 then n = 79830 ∧ Mf g₀ V₀ g V else
  if ℓ = 4143 then n = 79820 ∧ Mf g₀ V₀ g V else
  if ℓ = 4148 then n = 79810 ∧ Mf g₀ V₀ g V else
  False

/-- At the `ret`. -/
def Fh (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 3731 ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧
    g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧ Kd g₀ V₀ V

/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ Ih g₀ V₀ j' n' g' V') ∨ Fh g₀ V₀ j' g' V'

/-- `idiv r64` at `j`. -/
abbrev Dv (j r : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop := fun Q g _ V =>
  g.rdx = (if g.rax.msb then BitVec.allOnes 64 else 0) ∧ (g.get (regOf r)).setWidth 64 ≠ 0 ∧
    ((g.get (regOf r)).setWidth 64).msb = false ∧ ∀ fl, Q (j + 3) (idivG g ((g.get (regOf r)).setWidth 64)) fl V

/-- `bsr r32, q32` at `j`. -/
abbrev Bs (j r q len : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop := fun Q g _ V =>
  (g.get (regOf q)).setWidth 32 ≠ 0 ∧
    ∀ fl, Q (j + len) (wr g r (BitVec.ofNat 32 (highestSetBit ((g.get (regOf q)).setWidth 32)))) fl V

/-- `cpuid` at `j`. -/
abbrev Cp (prof : Profile) (j : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop := fun Q g _ V =>
  ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q (j + 2) (cpuidG prof cpu g) fl V

/-- What the code from a cut point needs for `Q` at the next ones: the `idiv`s', `bsr`s' and `cpuid`s' conditions,
`handle_intel`'s and `handle_amd`'s contracts at their calls. -/
def WtC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb : Addr) (ℓ : Nat) :
    Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 3707 then Dv 3707 1 else
  if ℓ = 3981 then Dv 3981 7 else
  if ℓ = 4005 then Dv 4005 9 else
  if ℓ = 4223 then Dv 4223 1 else
  if ℓ = 4380 then Bs 4380 1 9 4 else
  if ℓ = 4454 then Bs 4454 1 7 3 else
  if ℓ = 4594 then Bs 4594 1 9 4 else
  if ℓ = 3865 then Cp prof 3865 else
  if ℓ = 4079 then Cp prof 4079 else
  if ℓ = 4100 then Cp prof 4100 else
  if ℓ = 4141 then Cp prof 4141 else
  if ℓ = 4197 then Cp prof 4197 else
  if ℓ = 4346 then Cp prof 4346 else
  if ℓ = 3758 then CallK Wl sti_at 3763 (Hin.Te F Wl L fb) Hin.Rh else
  if ℓ = 3771 then CallK Wl sti_at 3776 (Hin.Te F Wl L fb) Hin.Rh else
  if ℓ = 3784 then CallK Wl sti_at 3789 (Hin.Te F Wl L fb) Hin.Rh else
  if ℓ = 4040 then CallK Wl sti_at 4045 (Hca.Te F Wl L) Hca.Rh else
  if ℓ = 4053 then CallK Wl sti_at 4058 (Hca.Te F Wl L) Hca.Rh else
  if ℓ = 4066 then CallK Wl sti_at 4071 (Hca.Te F Wl L) Hca.Rh else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-- The cut points' pieces in a run with the code, the `fs` base, `handle_intel` and `handle_amd`. -/
theorem spC (hC : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L sti_at sti) (hinH : CodeIn L hca_at hca) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o sti_at ℓ (WtC prof F Wl L fb ℓ) := by
  have hi := Hin.hin_fnK hC c hfs hinH
  have ha := Hca.ham_fnK c hinH
  have hl : 1280 < hca.length := by rw [hca_length]; decide
  have hl0 : 0 < hca.length := by rw [hca_length]; decide
  unfold WtC
  split
  · subst ℓ; exact SpAt.idiv64 c hin (lt_len (by decide)) (dv3707 _)
  split
  · subst ℓ; exact SpAt.idiv64 c hin (lt_len (by decide)) (dv3981 _)
  split
  · subst ℓ; exact SpAt.idiv64 c hin (lt_len (by decide)) (dv4005 _)
  split
  · subst ℓ; exact SpAt.idiv64 c hin (lt_len (by decide)) (dv4223 _)
  split
  · subst ℓ; exact SpAt.bsr32 c hin (lt_len (by decide)) (bs4380 _)
  split
  · subst ℓ; exact SpAt.bsr32 c hin (lt_len (by decide)) (bs4454 _)
  split
  · subst ℓ; exact SpAt.bsr32 c hin (lt_len (by decide)) (bs4594 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp3865 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp4079 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp4100 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp4141 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp4197 _)
  split
  · subst ℓ; exact SpAt.cpuid c hin (lt_len (by decide)) (cp4346 _)
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl3758 _) hinH hl tg3758 hin_at_eq hi
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl3771 _) hinH hl tg3771 hin_at_eq hi
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl3784 _) hinH hl tg3784 hin_at_eq hi
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl4040 _) hinH hl0 tg4040 hca_at0 ha
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl4053 _) hinH hl0 tg4053 hca_at0 ha
  split
  · subst ℓ; exact SpAt.callKx c hin (lt_len (by decide)) (cl4066 _) hinH hl0 tg4066 hca_at0 ha
  exact (spAll prof ℓ).at c hin

/-! ## Arithmetic -/

theorem t192 (s : Addr) (h : 192 ≤ s.toNat) : (s - 192#64).toNat = s.toNat - 192 := by bv_omega
theorem t_fr (s : Addr) (h : 192 ≤ s.toNat) : (fr s).toNat = s.toNat - 56 := by unfold fr; bv_omega

/-- The `pop`s' slots are the `push`es'. -/
theorem q_all (s : Addr) (h : 192 ≤ s.toNat) :
    fr s + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 = s ∧ fr s + 8#64 + 8 + 8 + 8 + 8 + 8 = s - 8 ∧
    fr s + 8#64 + 8 + 8 + 8 + 8 = s - 8 - 8 ∧ fr s + 8#64 + 8 + 8 + 8 = s - 8 - 8 - 8 ∧
    fr s + 8#64 + 8 + 8 = s - 8 - 8 - 8 - 8 ∧ fr s + 8#64 + 8 = s - 8 - 8 - 8 - 8 - 8 ∧
    fr s + 8#64 = s - 8 - 8 - 8 - 8 - 8 - 8 := by
  have hi := s.isLt
  have h' : 128 ≤ s.toNat := by omega
  have a0 := tc 8 (t_fr s h) (by omega)
  have a1 := t8 a0 (by omega)
  have a2 := t8 a1 (by omega)
  have a3 := t8 a2 (by omega)
  have a4 := t8 a3 (by omega)
  have a5 := t8 a4 (by omega)
  have a6 := t8 a5 (by omega)
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [a6]; omega
  · rw [a5, p_1 s h']; omega
  · rw [a4, p_2 s h']; omega
  · rw [a3, p_3 s h']; omega
  · rw [a2, p_4 s h']; omega
  · rw [a1, p_5 s h']; omega
  · rw [a0, p_6 s h']; omega

/-- A measure goal: the registers' literal projected out, then `omega`. -/
macro "c_om" : tactic => `(tactic| ((try dsimp only) <;> (try simp only [sw_64_32]) <;> omega))

/-! ## The footprint -/

/-- Bytes the run may store into on the stack: the 192 below the return address. -/
theorem fW (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : g₀.rsp.toNat ≤ x.toNat + 192)
    (h2 : x.toNat + n ≤ g₀.rsp.toNat) : ∀ i < n, Foot Wl (Addr.add x i) := by
  have lo := hT.lo
  have hi := hT.hi
  have e := t192 _ (by omega : 192 ≤ g₀.rsp.toNat)
  exact fsub (k := x.toNat + 192 - g₀.rsp.toNat) hT.st (by omega) (by omega) (by omega)

/-- Bytes the run may load on the stack: the same and the return address. -/
theorem fD (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : g₀.rsp.toNat ≤ x.toNat + 192)
    (h2 : x.toNat + n ≤ g₀.rsp.toNat + 8) : ∀ i < n, Foot F.data (Addr.add x i) := by
  have lo := hT.lo
  have hi := hT.hi
  have e := t192 _ (by omega : 192 ≤ g₀.rsp.toNat)
  exact fsub (k := x.toNat + 192 - g₀.rsp.toNat) hT.ld (by omega) (by omega) (by omega)

/-- `cpu_features`' bytes may be loaded. -/
theorem fC (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : 8014560 ≤ x.toNat) (h2 : x.toNat + n ≤ 8014728) :
    ∀ i < n, Foot F.data (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact hT.cpu _ (by omega) (by omega)

/-- The tables' bytes may be loaded. -/
theorem fT (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : 7282688 ≤ x.toNat) (h2 : x.toNat + n ≤ 7283552) :
    ∀ i < n, Foot F.data (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact hT.tab _ (by omega) (by omega)

/-- The globals' bytes may be stored into. -/
theorem fGw (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat}
    (h : 7942880 ≤ x.toNat ∧ x.toNat + n ≤ 7942944 ∨ 8029224 ≤ x.toNat ∧ x.toNat + n ≤ 8029236) :
    ∀ i < n, Foot Wl (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact (hT.gw _ (by unfold Gw; omega)).1

/-- The globals' bytes may be loaded. -/
theorem fGd (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat}
    (h : 7942880 ≤ x.toNat ∧ x.toNat + n ≤ 7942944 ∨ 8029224 ≤ x.toNat ∧ x.toNat + n ≤ 8029236) :
    ∀ i < n, Foot F.data (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact (hT.gw _ (by unfold Gw; omega)).2

/-- The six `push`es' slots. -/
theorem ent_foot (hT : Te F Wl L fb g₀ V₀) :
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) := by
  have lo := hT.lo
  have h' : 128 ≤ g₀.rsp.toNat := by omega
  have e1 := p_1 _ h'
  have e2 := p_2 _ h'
  have e3 := p_3 _ h'
  have e4 := p_4 _ h'
  have e5 := p_5 _ h'
  have e6 := p_6 _ h'
  exact ⟨fW hT (by omega) (by omega), fW hT (by omega) (by omega), fW hT (by omega) (by omega),
    fW hT (by omega) (by omega), fW hT (by omega) (by omega), fW hT (by omega) (by omega)⟩

/-- The table's entry may be loaded. -/
theorem ft_ent (hT : Te F Wl L fb g₀ V₀) (k : BitVec 32) (hk : k.toNat ≤ 38) :
    ∀ i < 4, Foot F.data (Addr.add (7282852#64 + k.setWidth 64 * 4#64) i) := by
  have c : (7282852#64 : Addr).toNat = 7282852 := rfl
  have e : (Addr.add 7282852#64 (4 * k.toNat)).toNat = 7282852 + 4 * k.toNat :=
    toNat_add_of_fits (n := 4 * k.toNat + 1) (by omega) (by omega)
  rw [jaddr k hk]
  exact fT hT (by omega) (by omega)

/-! ## Bytes -/

/-- Out of the 48 bytes below the return address, the bytes after the `push`es are those at the entry. -/
theorem P6_out (hT : Te F Wl L fb g₀ V₀) (a : Addr)
    (h : a.toNat + 48 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) : P6 g₀ V₀ a = V₀ a := by
  have lo := hT.lo
  have hi := hT.hi
  have h' : 128 ≤ g₀.rsp.toNat := by omega
  have e1 := p_1 _ h'
  have e2 := p_2 _ h'
  have e3 := p_3 _ h'
  have e4 := p_4 _ h'
  have e5 := p_5 _ h'
  have e6 := p_6 _ h'
  dsimp only [P6]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e5]; omega) (by rw [toBytesLE_length, e5]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- A store into the globals keeps the bytes that stay. -/
theorem st_G {S : Addr} {V W : Addr → Byte} (hm : ∀ a, Out S a → V a = W a) (x : Addr) (bs : List Byte)
    (h : 7942880 ≤ x.toNat ∧ x.toNat + bs.length ≤ 7942944 ∨ 8029224 ≤ x.toNat ∧ x.toNat + bs.length ≤ 8029236) :
    ∀ a, Out S a → Vst V x bs a = W a := by
  intro a ha
  have hg : ¬ Gw a := by obtain ⟨-, h⟩ := ha; exact h
  unfold Gw at hg
  rw [Tun.Vst_out _ _ _ _ (by omega) (by omega)]
  exact hm a ha

/-- A load of bytes that stay. -/
theorem rdM {S : Addr} {V W : Addr → Byte} (hm : ∀ a, Out S a → V a = W a) (x : Addr) (n : Nat)
    (hx : x.toNat + n ≤ 2 ^ 64) (hO : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → Out S a) :
    List.map V (byteAddrs x n) = List.map W (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits (a := x) hj hx
  exact hm _ (hO _ (by omega) (by omega))

/-- Below the globals, the bytes are those at the entry. -/
theorem rd_far (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) (x : Addr) (n : Nat)
    (h : x.toNat + n ≤ 7942880) : List.map V (byteAddrs x n) = List.map V₀ (byteAddrs x n) := by
  have lo := hT.lo
  rw [rdM hm x n (by omega) (fun a h1 h2 => by unfold Out Gw; omega)]
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits (a := x) hj (by omega)
  exact P6_out hT _ (Or.inl (by omega))

theorem hjt_V (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) :
    List.map V (byteAddrs 0x6f2000#64 36) = hca_jt :=
  (rd_far hT hm _ _ (by decide)).trans hT.hjt

theorem cjt_V (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) :
    List.map V (byteAddrs 7282852#64 156) = c103_jt :=
  (rd_far hT hm _ _ (by decide)).trans hT.cjt

/-- The table's entry `k`: to 3967 or to 4570. -/
theorem jt_ent (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) (k : BitVec 32)
    (hk : k.toNat ≤ 38) :
    (ofBytesLE 32 (List.map V (byteAddrs (7282852#64 + k.setWidth 64 * 4#64) 4))).signExtend 64 + 7282852#64 =
      Addr.add sti_at 3967 ∨
    (ofBytesLE 32 (List.map V (byteAddrs (7282852#64 + k.setWidth 64 * 4#64) 4))).signExtend 64 + 7282852#64 =
      Addr.add sti_at 4570 := by
  rw [jaddr k hk, Hca.sub_rd V _ _ 156 (cjt_V hT hm) (4 * k.toNat) 4 (by omega)]
  exact jt_tg _ (by omega)

/-- From the frame's bytes to `Kd`. -/
theorem kd_of (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) : Kd g₀ V₀ V := by
  intro a h hg
  rw [hm a ⟨by omega, hg⟩]
  exact P6_out hT a (by omega)

/-- The return address after the run. -/
theorem rd_kd (hT : Te F Wl L fb g₀ V₀) (hK : Kd g₀ V₀ V) :
    List.map V (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have hi := hT.hi
  have lo := hT.lo
  have e := toNat_add_of_fits (a := g₀.rsp) hj (by omega)
  exact hK _ (Or.inr (by omega)) (by unfold Gw; omega)

/-- The six `pop`s. -/
theorem pops (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = P6 g₀ V₀ a) :
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64) 8)) = g₀.rbx ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64 + 8) 8)) = g₀.rbp ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64 + 8 + 8) 8)) = g₀.r12 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64 + 8 + 8 + 8) 8)) = g₀.r13 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64 + 8 + 8 + 8 + 8) 8)) = g₀.r14 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 8#64 + 8 + 8 + 8 + 8 + 8) 8)) = g₀.r15 := by
  have lo := hT.lo
  have hi := hT.hi
  have h' : 128 ≤ g₀.rsp.toNat := by omega
  have e1 := p_1 _ h'
  have e2 := p_2 _ h'
  have e3 := p_3 _ h'
  have e4 := p_4 _ h'
  have e5 := p_5 _ h'
  have e6 := p_6 _ h'
  have b := fun k => ofBytesLE_toBytesLE (w := 64) (n := 8) rfl k
  obtain ⟨-, q6, q5, q4, q3, q2, q1⟩ := q_all _ (by omega)
  rw [q6, q5, q4, q3, q2, q1]
  rw [rdM hm (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8 - 8 - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8 - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega),
    rdM hm (g₀.rsp - 8 - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega),
    rdM hm (g₀.rsp - 8) 8 (by omega) (fun a h1 h2 => by unfold Out Gw; omega)]
  dsimp only [P6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _

/-! ## The calls of `handle_intel` and `handle_amd` -/

/-- `handle_intel`'s contract at a call: its frame and return address's slot are the 136 bytes below `fr`. -/
theorem te_hin (hT : Te F Wl L fb g₀ V₀) {g : Gprs} {W : Addr → Byte}
    (hd : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64) (hs : g.rsp = fr g₀.rsp - 8)
    (hr : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
      ofBytesLE 64 (List.map W (byteAddrs (fr g₀.rsp - 8) 8)) = e₂.add j₂) :
    Hin.Te F Wl L fb g W := by
  have lo := hT.lo
  have hi := hT.hi
  have ca := hT.cna
  have e0 := t_fr _ (by omega : 192 ≤ g₀.rsp.toNat)
  have e1 := ts8 e0 (by omega)
  have e128 := Hin.t128 (fr g₀.rsp - 8) (by omega)
  refine ⟨hd, ?_, ?_, ?_, ?_, hT.cn, hT.cnf, ?_, ?_, ?_, ?_, fun x h1 h2 => hT.tab x (by omega) (by omega), ?_⟩
  · rw [hs]; exact fW hT (by omega) (by omega)
  · rw [hs]; exact fD hT (by omega) (by omega)
  · rw [hs]; omega
  · rw [hs]; omega
  · rw [hs]; omega
  · exact fC hT (by decide) (by decide)
  · exact fC hT (by decide) (by decide)
  · exact fC hT (by decide) (by decide)
  · rw [hs]; exact hr

/-- After `handle_intel`: the bytes out of its 128 and its return address's slot. -/
theorem keep_hin {S : Addr} {g : Gprs} {V V' : Addr → Byte} (h192 : 192 ≤ S.toNat) (bs : List Byte)
    (hb : bs.length = 8) (hK : Hin.KeepH (g.set 4 (fr S - 8)) (Vst V (fr S - 8) bs) V') (a : Addr)
    (ha : Out S a) : V' a = V a := by
  have hi := S.isLt
  have e0 := t_fr _ h192
  have e1 := ts8 e0 (by omega)
  obtain ⟨ha, -⟩ := ha
  rw [hK a (show a.toNat + 128 < (fr S - 8).toNat ∨ (fr S - 8).toNat ≤ a.toNat by omega),
    Tun.Vst_out _ _ _ _ (by rw [hb]; omega) (by rw [hb]; omega)]

/-- A call of `handle_intel`, to the instruction after it. -/
theorem hin_call (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) {j : Nat} (hj : j < sti.length)
    (h : Mf g₀ V₀ g V) (hd : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64) {Q : Post}
    (hQ : ∀ g' V', Mf g₀ V₀ g' V' → ∀ fl, Q j g' fl V') :
    CallK Wl sti_at j (Hin.Te F Wl L fb) Hin.Rh Q g f V := by
  obtain ⟨hs, hm⟩ := h
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ (by omega : 192 ≤ g₀.rsp.toNat)
  have e1 := ts8 e0 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs]; exact fW hT (by omega) (by omega)
  · rw [hs]; omega
  · rw [hs]
    refine te_hin hT hd rfl ⟨sti_at, sti, j, hin, hj, ?_⟩
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hs]
    intro g' V' hR fl
    obtain ⟨hs', -, -, -, -, -, -, hK⟩ := hR
    exact hQ g' V' ⟨hs'.trans (sa8 _), fun a ha =>
      (keep_hin (by omega) _ (toBytesLE_length _ _) hK a ha).trans (hm a ha)⟩ fl

/-- A call of `handle_amd`, to the instruction after it. -/
theorem ham_call (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) {j : Nat} (hj : j < sti.length)
    (h : Mf g₀ V₀ g V) (hd : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64) {Q : Post}
    (hQ : ∀ g' V', Mf g₀ V₀ g' V' → ∀ fl, Q j g' fl V') :
    CallK Wl sti_at j (Hca.Te F Wl L) Hca.Rh Q g f V := by
  obtain ⟨hs, hm⟩ := h
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ (by omega : 192 ≤ g₀.rsp.toNat)
  have e1 := ts8 e0 (by omega)
  have e2 := ts8 e1 (by omega)
  have c : (0x6f2000#64 : Addr).toNat = 7282688 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs]; exact fW hT (by omega) (by omega)
  · rw [hs]; omega
  · rw [hs]
    refine ⟨hd, ?_, ?_, ?_, ?_, fun x h1 h2 => hT.tab x (by omega) (by omega), ?_, ⟨sti_at, sti, j, hin, hj, ?_⟩⟩
    · exact fW hT (x := fr g₀.rsp - 8 - 8) (by omega) (by omega)
    · exact fD hT (x := fr g₀.rsp - 8 - 8) (by omega) (by omega)
    · show 0x6f2000 + 44 ≤ (fr g₀.rsp - 8).toNat
      omega
    · show (fr g₀.rsp - 8).toNat + 8 ≤ 2 ^ 64
      omega
    · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (Or.inr (by omega))]
      exact hjt_V hT hm
    · show ofBytesLE 64 (List.map (Vst V (fr g₀.rsp - 8) (toBytesLE (sti_at.add j) 8))
        (byteAddrs (fr g₀.rsp - 8) 8)) = sti_at.add j
      rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
      exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hs]
    intro g' V' hR fl
    obtain ⟨hs', -, -, -, -, -, -, hV⟩ := hR
    refine hQ g' V' ⟨hs'.trans (sa8 _), fun a ha => ?_⟩ fl
    have ha' := ha
    obtain ⟨ha1, -⟩ := ha'
    have e : (g.set 4 (fr g₀.rsp - 8)).rsp = fr g₀.rsp - 8 := rfl
    rw [hV]
    dsimp only [Hca.V1]
    try rw [e]
    rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]
    exact hm a ha

/-! ## After `cpuid` -/

theorem cp_mf {cpu : Nat} (h : Mf g₀ V₀ g V) : Mf g₀ V₀ (cpuidG prof cpu g) V := by cases g; exact h

end FV7z.C103
