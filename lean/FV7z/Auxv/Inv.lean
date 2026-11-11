import FV7z.Auxv.Cuts
import FV7z.Spec.AuxInit
import FV7z.Tun.Inv
/-!
# The call of `_dl_aux_init`, and the invariants of its cut points (PLAN.md G3, startup)

`Ctx`: what stays the same through a call: where the frame lies and the registers the prologue saves there, the
vector (its address, the types and values of its entries, an entry `AT_SECURE`), the variables after each entry
(`vs`), and the bytes of memory at the call (`V0`). `Ctx.Ok`: what the contract's precondition gives of them. `Env`:
what may be read and written.

The compiled code keeps the variables in registers (`RR`) and in the red zone (`RF`), each with a flag, non-zero once
an entry has set it; at the vector's end it stores those whose flag is set. `Lp`: in the loop, after `n` entries.
`Ex`: after the loop, with the variables in memory (`Gl`) those of the call but for the ones stored so far (`W1` to
`W11`).

The invariants: `P0` at the entry; `I216` at the head of the loop (`rax` the type of the `n`-th entry); `Ic` at a case
of the `switch` (the type known); `I256` after a case; `E0` to `E12` after the loop, before each variable's store;
`E13` before the epilogue. The measure: three for each entry left, then what is left of the code.
-/
namespace FV7z.Auxv
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.AuxInit
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)

/-- The 2 bytes, the byte of `V` at `a`. -/
notation "rdw(" V ", " a ")" => ofBytesLE 16 (List.map V (byteAddrs a 2))
notation "rdb(" V ", " a ")" => ofBytesLE 8 (List.map V (byteAddrs a 1))

/-- The `k`-th entry of the jump table. -/
def jt (k : Nat) : BitVec 32 := ofBytesLE 32 ((aux_jt.drop (4 * k)).take 4)

/-- What stays the same through a call. -/
structure Ctx where
  /-- The frame's 104 bytes: the red zone's 56, then the registers the prologue saves. -/
  sp : Addr
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  /-- The vector: its address, the number of its entries, their types and values, and an entry `AT_SECURE`. -/
  av : Addr
  N : Nat
  ty : Nat → BitVec 64
  val : Nat → BitVec 64
  sn : Nat
  /-- The variables after the first `n` entries. -/
  vs : Nat → Vars
  /-- The bytes at the call. -/
  V0 : Addr → Byte

/-- A byte of the frame. -/
def InFr (K : Ctx) (a : Addr) : Prop := K.sp.toNat ≤ a.toNat ∧ a.toNat < K.sp.toNat + 104

/-- `n` bytes at `a` apart from the frame. -/
def Off (K : Ctx) (a : Nat) (n : Nat) : Prop := K.sp.toNat + 104 ≤ a ∨ a + n ≤ K.sp.toNat

/-- The bytes `V` hold the variables `w`. -/
structure Gl (V : Addr → Byte) (w : Vars) : Prop where
  pagesize : rdq(V, 0x7933d8#64) = w.pagesize
  clktck : rdd(V, 0x7a85c0#64) = w.clktck
  phdr : rdq(V, 0x7a8580#64) = w.phdr
  phnum : rdq(V, 0x7a8598#64) = w.phnum
  platform : rdq(V, 0x7a8548#64) = w.platform
  hwcap : rdq(V, 0x7a4ac8#64) = w.hwcap
  hwcap2 : rdq(V, 0x7a4ac0#64) = w.hwcap2
  sysinfoDso : rdq(V, 0x7a8508#64) = w.sysinfoDso
  fpuControl : rdw(V, 0x7933cc#64) = w.fpuControl
  secure : rdd(V, 0x791ce0#64) = w.secure
  decided : rdd(V, 0x7a85c4#64) = w.decided
  random : rdq(V, 0x791ca0#64) = w.random

/-- What the precondition gives. -/
structure Ctx.Ok (K : Ctx) : Prop where
  hsp : K.sp.toNat + 112 ≤ 2 ^ 64
  /-- The vector. -/
  hfit : K.av.toNat + (16 * K.N + 8) ≤ 2 ^ 64
  aAv : Off K K.av.toNat (16 * K.N + 8)
  xAv : K.av.toNat + (16 * K.N + 8) ≤ 0x7a8540 ∨ 0x7a8548 ≤ K.av.toNat
  hty : ∀ n : Nat, n < K.N → rdq(K.V0, K.av.add (16 * n)) = K.ty n
  hval : ∀ n : Nat, n < K.N → rdq(K.V0, K.av.add (16 * n + 8)) = K.val n
  hnz : ∀ n : Nat, n < K.N → K.ty n ≠ 0
  hend : rdq(K.V0, K.av.add (16 * K.N)) = 0
  hsn : K.sn < K.N
  hsec : K.ty K.sn = 23
  /-- The jump table. -/
  aJt : Off K 0x6f3660 124
  hjt : ∀ k : Nat, k < 31 → rdd(K.V0, Addr.add 0x6f3660#64 (4 * k)) = jt k
  /-- The variables. -/
  hvs : ∀ n : Nat, n < K.N → K.vs (n + 1) = step (K.vs n) (K.ty n, K.val n)
  hgl : Gl K.V0 (K.vs 0)
  oAx : Off K 0x7a8540 8
  oPs : Off K 0x7933d8 8
  oCk : Off K 0x7a85c0 4
  oPh : Off K 0x7a8580 8
  oPn : Off K 0x7a8598 8
  oPl : Off K 0x7a8548 8
  oHw : Off K 0x7a4ac8 8
  oH2 : Off K 0x7a4ac0 8
  oSy : Off K 0x7a8508 8
  oFp : Off K 0x7933cc 2
  oSe : Off K 0x791ce0 4
  oDe : Off K 0x7a85c4 4
  oRa : Off K 0x791ca0 8

/-- What may be read and written. -/
structure Env (K : Ctx) (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  fr : ∀ y : Addr, K.sp.toNat ≤ y.toNat → y.toNat < K.sp.toNat + 104 → Foot Wl y
  gl : ∀ r ∈ globals, ∀ y, r.Mem y → Foot Wl y
  tab : ∀ y : Addr, 0x6f3660 ≤ y.toNat → y.toNat < 0x6f3660 + 124 → Foot F.data y
  vec : ∀ y : Addr, K.av.toNat ≤ y.toNat → y.toNat < K.av.toNat + (16 * K.N + 8) → Foot F.data y

/-- The variables the loop keeps in registers: `r10`, `ebp`, `r13`, `r15`, and the flags `r9b`, `r11b`, `bl`, `r12b`,
and `r14b` for the red zone's `_dl_platform`. -/
structure RR (K : Ctx) (v : Vars) (g : Gprs) : Prop where
  r10 : g.r10 = v.pagesize
  f9 : g.r9.setWidth 8 = 0#8 → v.pagesize = (K.vs 0).pagesize
  rbp : g.rbp.setWidth 32 = v.clktck
  f11 : g.r11.setWidth 8 = 0#8 → v.clktck = (K.vs 0).clktck
  r13 : g.r13 = v.phdr
  fbx : g.rbx.setWidth 8 = 0#8 → v.phdr = (K.vs 0).phdr
  r15 : g.r15 = v.phnum
  f12 : g.r12.setWidth 8 = 0#8 → v.phnum = (K.vs 0).phnum
  f14 : g.r14.setWidth 8 = 0#8 → v.platform = (K.vs 0).platform

/-- The frame: the variables the loop keeps in the red zone with their flags, and the saved registers. -/
structure RF (K : Ctx) (v : Vars) (V : Addr → Byte) : Prop where
  platform : rdq(V, K.sp) = v.platform
  hwcap : rdq(V, K.sp + 8#64) = v.hwcap
  hwcap2 : rdq(V, K.sp + 16#64) = v.hwcap2
  sysinfo : rdq(V, K.sp + 24#64) = v.sysinfoDso
  fpu : rdw(V, K.sp + 32#64) = v.fpuControl
  secure : rdd(V, K.sp + 36#64) = v.secure
  random : rdq(V, K.sp + 40#64) = v.random
  decided : rdd(V, K.sp + 48#64) = v.decided
  fHwcap2 : rdb(V, K.sp + 34#64) = 0#8 → v.hwcap2 = (K.vs 0).hwcap2
  fFpu : rdb(V, K.sp + 35#64) = 0#8 → v.fpuControl = (K.vs 0).fpuControl
  fHwcap : rdb(V, K.sp + 52#64) = 0#8 → v.hwcap = (K.vs 0).hwcap
  fSysinfo : rdb(V, K.sp + 53#64) = 0#8 → v.sysinfoDso = (K.vs 0).sysinfoDso
  fSecure : rdb(V, K.sp + 54#64) = 0#8 → v.secure = (K.vs 0).secure ∧ v.decided = (K.vs 0).decided
  fRandom : rdb(V, K.sp + 55#64) = 0#8 → v.random = (K.vs 0).random
  v0 : rdq(V, K.sp + 56#64) = K.rbx
  v1 : rdq(V, K.sp + 64#64) = K.rbp
  v2 : rdq(V, K.sp + 72#64) = K.r12
  v3 : rdq(V, K.sp + 80#64) = K.r13
  v4 : rdq(V, K.sp + 88#64) = K.r14
  v5 : rdq(V, K.sp + 96#64) = K.r15

/-- In the loop, the bytes outside the frame are those at the call, but for `_dl_auxv`. -/
def Out (K : Ctx) (V : Addr → Byte) : Prop :=
  ∀ a : Addr, ¬ InFr K a → (a.toNat < 0x7a8540 ∨ 0x7a8548 ≤ a.toNat) → V a = K.V0 a

/-- In the loop, after `n` entries. -/
def Lp (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 56#64 ∧ g.rdx = 0x6f3660#64 ∧ RR K (K.vs n) g ∧ RF K (K.vs n) V ∧ Out K V ∧
    rdq(V, 0x7a8540#64) = K.av ∧ (K.sn < n → g.rcx.setWidth 32 = 0xffffffff#32)

/-- Outside the frame, `_dl_auxv` and the variables, the bytes are those at the call. -/
def OutG (K : Ctx) (V : Addr → Byte) : Prop :=
  ∀ a : Addr, ¬ InFr K a → ¬ Foot globals a → V a = K.V0 a

/-- After the loop: the variables in memory are `w`. -/
def Ex (K : Ctx) (w : Vars) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 56#64 ∧ RR K (K.vs K.N) g ∧ RF K (K.vs K.N) V ∧ Gl V w ∧
    (rdq(V, 0x7a8540#64) = K.av ∧ OutG K V) ∧ g.rcx.setWidth 32 = 0xffffffff#32

/-! ## The variables in memory after the loop, as they are stored one after the other -/

def W1 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize }
def W2 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck }
def W3 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr }
def W4 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum }
def W5 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform }
def W6 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap }
def W7 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap, hwcap2 := v.hwcap2 }
def W8 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap, hwcap2 := v.hwcap2, fpuControl := v.fpuControl }
def W9 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap, hwcap2 := v.hwcap2, fpuControl := v.fpuControl, sysinfoDso := v.sysinfoDso }
def W10 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap, hwcap2 := v.hwcap2, fpuControl := v.fpuControl, sysinfoDso := v.sysinfoDso, secure := v.secure, decided := v.decided }
def W11 (v0 v : Vars) : Vars := { v0 with pagesize := v.pagesize, clktck := v.clktck, phdr := v.phdr, phnum := v.phnum, platform := v.platform, hwcap := v.hwcap, hwcap2 := v.hwcap2, fpuControl := v.fpuControl, sysinfoDso := v.sysinfoDso, secure := v.secure, decided := v.decided, random := v.random }

theorem W11_eq (v0 v : Vars) : W11 v0 v = v := rfl

/-! ## The invariants -/

/-- At the entry. -/
def P0 (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 104#64 ∧ g.rdi = K.av ∧ g.rbx = K.rbx ∧ g.rbp = K.rbp ∧ g.r12 = K.r12 ∧ g.r13 = K.r13 ∧
    g.r14 = K.r14 ∧ g.r15 = K.r15 ∧ V = K.V0 ∧ m = 3 * K.N + 400

/-- At the head of the loop: `rax` the type of the `n`-th entry. -/
def I216 (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ n, n < K.N ∧ Lp K n g V ∧ g.rdi = K.av.add (16 * n) ∧ g.rax = K.ty n ∧ m = 3 * (K.N - n) + 302

/-- At the case of the type `t`. -/
def Ic (t : BitVec 64) (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ n, n < K.N ∧ Lp K n g V ∧ g.rdi = K.av.add (16 * n) ∧ K.ty n = t ∧ m = 3 * (K.N - n) + 301

/-- After a case: the `n`-th entry done, `rdi` still at it. -/
def I256 (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ n, n < K.N ∧ Lp K (n + 1) g V ∧ g.rdi = K.av.add (16 * n) ∧ m = 3 * (K.N - n) + 300

/-- After the loop, at the cut point `ℓ`. -/
def E (ℓ : Nat) (w : Vars → Vars → Vars) (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Ex K (w (K.vs 0) (K.vs K.N)) g V ∧ m = 500 - ℓ

/-- Before the epilogue. -/
def E483 (K : Ctx) (m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 56#64 ∧ RF K (K.vs K.N) V ∧ Gl V (K.vs K.N) ∧ (rdq(V, 0x7a8540#64) = K.av ∧ OutG K V) ∧ m = 17

/-- At the `ret`: the registers a call keeps, the variables as the entries set them, `_dl_auxv` the vector's address,
and the other bytes outside the frame as at the call. -/
def Ret (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 104#64 ∧ g.rbx = K.rbx ∧ g.rbp = K.rbp ∧ g.r12 = K.r12 ∧ g.r13 = K.r13 ∧ g.r14 = K.r14 ∧
    g.r15 = K.r15 ∧ Gl V (K.vs K.N) ∧ rdq(V, 0x7a8540#64) = K.av ∧ OutG K V

/-- The invariant at each cut point. -/
def InvT (K : Ctx) (ℓ : Nat) : Nat → Gprs → (Addr → Byte) → Prop :=
  if ℓ = 0 then P0 K else
  if ℓ = 216 then I216 K else
  if ℓ = 240 then Ic 25 K else
  if ℓ = 256 then I256 K else
  if ℓ = 272 then E 272 (fun v0 _ => v0) K else
  if ℓ = 281 then E 281 W1 K else
  if ℓ = 292 then E 292 W2 K else
  if ℓ = 303 then E 303 W3 K else
  if ℓ = 315 then E 315 W4 K else
  if ℓ = 332 then E 332 W5 K else
  if ℓ = 351 then E 351 W6 K else
  if ℓ = 370 then E 370 W7 K else
  if ℓ = 389 then E 389 W8 K else
  if ℓ = 408 then E 408 W9 K else
  if ℓ = 435 then E 435 W10 K else
  if ℓ = 454 then E 454 W11 K else
  if ℓ = 483 then E483 K else
  if ℓ = 496 then Ic 33 K else
  if ℓ = 536 then Ic 26 K else
  if ℓ = 576 then Ic 23 K else
  if ℓ = 624 then Ic 18 K else
  if ℓ = 664 then Ic 17 K else
  if ℓ = 704 then Ic 16 K else
  if ℓ = 744 then Ic 15 K else
  if ℓ = 784 then Ic 14 K else
  if ℓ = 816 then Ic 13 K else
  if ℓ = 848 then Ic 12 K else
  if ℓ = 880 then Ic 11 K else
  if ℓ = 912 then Ic 6 K else
  if ℓ = 960 then Ic 5 K else
  if ℓ = 992 then Ic 3 K else
  fun _ _ _ => False

/-- At an exit: the invariant with a smaller measure, or the `ret`. -/
def Nx (K : Ctx) (m : Nat) : Post := fun j' g' _ V' =>
  (∃ m', m' < m ∧ InvT K j' m' g' V') ∨ (j' = 493 ∧ Ret K g' V')

theorem nx {K : Ctx} {m m' j : Nat} {g : Gprs} {fl : Rflags} {V : Addr → Byte} (hn : m' < m)
    (h : InvT K j m' g V) : Nx K m j g fl V := Or.inl ⟨m', hn, h⟩

end FV7z.Auxv
