import FV7z.Cxa.Cuts
import FV7z.Nef.Holds
import FV7z.Pim.Frame
/-!
# `__cxa_atexit` registers an exit function (PLAN.md G3, startup)

glibc 2.31's `__cxa_atexit (func, arg, d)` at `0x623690` in `7zzs`, with one thread and the first list of
`__exit_funcs` not full: the lock `__exit_funcs_lock` at `0x7a8400` is taken with an unlocked `cmpxchg` and given back
with `sub`, `__new_exitfn (&__exit_funcs)` gives the next place `p` of the list `l` that `__exit_funcs` at `0x7923b0`
points at, and the place gets its four words: the flavor 4 (`ef_cxa`), the function mangled with the pointer guard at
`fs:0x30` (`PTR_MANGLE`: xor, then rotate left by 17), the argument and the DSO handle.

- `cx_47`, `call_61`, `movq_75`, `movhps_103`, `movups_112`, `sb_130`, `ret_145`: the instructions outside the blocks.
- `tb16`, `Vst_append`, `st16`, `two_q`: the 16 bytes that `movups` stores are the two quadwords.
- `vc_*`: the verification conditions of the pieces.
- `Reg`: what the bytes after the call have of those before it.
- `cxa_ok`: called with one thread (`fs:0x18` is 0), a function that is not null, the lock free, no exit function
  run, the list with `n < 32` places taken (none and no list after it, or the last of them not free again), the run
  reaches the return address with `rax` 0, the registers a call keeps as at the entry, place `n` filled, the lock
  free again.

The ways with a null function, more threads, a lock that is held and no place (`__new_exitfn` returns null) are not
ones of this call.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out sk0')
open FV7z.Raf (Out off_ft rd_out2)
open FV7z.Nef (rd_out3 rd_out4)
namespace FV7z.Cxa

/-- `cmpxchg [0x7a8400], edx`, not locked. -/
def pcx : List Byte := [0x0f, 0xb1, 0x15, 0x3a, 0x4d, 0x18, 0x00]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (FV7z.mk .cmpxchg 32 [.mem (mrip 1592634 32), gr 32 2] 7) := by dec_rfl
theorem w_47 : pcx <+: cxa.drop 47 := by decide +kernel
theorem cx_47 (feat : Features) : Dec feat cxa 47 (FV7z.mk .cmpxchg 32 [.mem (mrip 1592634 32), gr 32 2] 7) :=
  Dec.shift (j := 47) (k := 0) (pcx_0 feat) w_47 (Nat.zero_le _)

/-- `call __new_exitfn`. -/
def pcl : List Byte := [0xe8, 0x5e, 0xfd, 0xff, 0xff]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 18446744073709550942] 5) := by dec_rfl
theorem w_61 : pcl <+: cxa.drop 61 := by decide +kernel
theorem call_61 (feat : Features) : Dec feat cxa 61 (FV7z.mk .call 64 [.rel 18446744073709550942] 5) :=
  Dec.shift (j := 61) (k := 0) (pcl_0 feat) w_61 (Nat.zero_le _)

/-- `movq xmm0, [rsp]`. -/
def pmq : List Byte := [0xf3, 0x0f, 0x7e, 0x04, 0x24]
theorem pmq_0 : ∀ feat, Dec feat pmq 0 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 0 64)] 5) := by dec_rfl
theorem w_75 : pmq <+: cxa.drop 75 := by decide +kernel
theorem movq_75 (feat : Features) : Dec feat cxa 75 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 0 64)] 5) :=
  Dec.shift (j := 75) (k := 0) (pmq_0 feat) w_75 (Nat.zero_le _)

/-- `movhps xmm0, [rsp + 8]`. -/
def pmh : List Byte := [0x0f, 0x16, 0x44, 0x24, 0x08]
theorem pmh_0 : ∀ feat, Dec feat pmh 0 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) := by dec_rfl
theorem w_103 : pmh <+: cxa.drop 103 := by decide +kernel
theorem movhps_103 (feat : Features) :
    Dec feat cxa 103 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) :=
  Dec.shift (j := 103) (k := 0) (pmh_0 feat) w_103 (Nat.zero_le _)

/-- `movups [rax + 16], xmm0`. -/
def pmu : List Byte := [0x0f, 0x11, 0x40, 0x10]
theorem pmu_0 : ∀ feat, Dec feat pmu 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 0 16 128), .xmm 0] 4) := by dec_rfl
theorem w_112 : pmu <+: cxa.drop 112 := by decide +kernel
theorem movups_112 (feat : Features) :
    Dec feat cxa 112 (FV7z.mk (.sse .movups) 32 [.mem (mbd 0 16 128), .xmm 0] 4) :=
  Dec.shift (j := 112) (k := 0) (pmu_0 feat) w_112 (Nat.zero_le _)

/-- `sub dword [0x7a8400], 1`. -/
def psb : List Byte := [0x83, 0x2d, 0xe7, 0x4c, 0x18, 0x00, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mrip 1592551 32), .imm 32 1] 7) := by dec_rfl
theorem w_130 : psb <+: cxa.drop 130 := by decide +kernel
theorem sb_130 (feat : Features) : Dec feat cxa 130 (FV7z.mk .sub 32 [.mem (mrip 1592551 32), .imm 32 1] 7) :=
  Dec.shift (j := 130) (k := 0) (psb_0 feat) w_130 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_145 : pret <+: cxa.drop 145 := by decide +kernel
theorem ret_145 (feat : Features) : Dec feat cxa 145 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 145) (k := 0) (pret_0 feat) w_145 (Nat.zero_le _)

/-! ## The 16 bytes of two quadwords -/

/-- The 16 bytes of a vector register's low half: the low quadword's, then the high one's. -/
theorem tb16 (lo hi : BitVec 64) :
    toBytesLE ((hi ++ lo).setWidth 128) 16 = toBytesLE lo 8 ++ toBytesLE hi 8 := by
  apply List.ext_getElem (by simp)
  intro j h₁ _
  rw [toBytesLE_length] at h₁
  simp only [toBytesLE, List.getElem_append, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range]
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [show 8 * j + i < 64 from by omega, show 8 * j + i < 128 from by omega]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [show ¬ (8 * j + i < 64) from by omega, show 8 * j + i - 64 = 8 * (j - 8) + i from by omega,
      show 8 * j + i < 128 from by omega]

/-- The low quadword of a vector register's low half that holds one quadword. -/
theorem lane_lo (x : BitVec 64) : lane 64 (x.setWidth 128) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lane, hi]
  intro _
  omega

/-- A store of bytes in two parts. -/
theorem Vst_append : ∀ (xs ys : List Byte) (V : Addr → Byte) (a : Addr),
    Vst V a (xs ++ ys) = Vst (Vst V a xs) (a.add xs.length) ys
  | [], ys, V, a => by simp [Vst, addr_add_zero]
  | x :: xs, ys, V, a => by
    simp only [List.cons_append, Vst, List.length_cons]
    rw [Vst_append xs ys, addr_add_add, Nat.add_comm]

/-- The store of a vector register's low half that holds two quadwords: two stores. -/
theorem st16 (V : Addr → Byte) (a : Addr) (lo hi : BitVec 64) :
    Vst V a (toBytesLE ((hi ++ lo).setWidth 128) 16) =
      Vst (Vst V a (toBytesLE lo 8)) (a + 8#64) (toBytesLE hi 8) := by
  rw [tb16, Vst_append, toBytesLE_length]
  rfl

/-- Two quadwords stored one after the other: what differs, what is read back. -/
theorem two_q (V : Addr → Byte) (a : Addr) (x y : BitVec 64) (ha : a.toNat + 16 ≤ 2 ^ 64) :
    Out a.toNat (a.toNat + 16) V (Vst (Vst V a (toBytesLE x 8)) (a + 8#64) (toBytesLE y 8)) ∧
      rdq(Vst (Vst V a (toBytesLE x 8)) (a + 8#64) (toBytesLE y 8), a) = x ∧
      rdq(Vst (Vst V a (toBytesLE x 8)) (a + 8#64) (toBytesLE y 8), a + 8#64) = y := by
  refine ⟨fun b hb => ?_, ?_, ?_⟩
  · repeat pv
  · pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- What the bytes `V'` at the lock have of the bytes `V` at the entry, the stack pointer `sp` there: all outside
the frame, in the frame `rbx`, the argument and the DSO handle. -/
structure F0 (V V' : Addr → Byte) (sp : Addr) (rbx rsi rdx : BitVec 64) : Prop where
  out : Out (sp.toNat - 24) sp.toNat V V'
  sbx : rdq(V', sp - 8) = rbx
  sarg : rdq(V', sp - 24#64) = rsi
  sdso : rdq(V', sp - 16) = rdx

/-- From the entry to the lock, a function that is not null, one thread: the frame, `eax` 0 and `edx` 1 for the
`cmpxchg`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hsp : 24 < g.rsp.toNat)
    (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24#64) i)) (h0 : g.rdi ≠ 0)
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) (hfb : (fb + 24#64).toNat + 4 ≤ 2 ^ 64)
    (hfd : (fb + 24#64).toNat + 4 ≤ g.rsp.toNat - 24 ∨ g.rsp.toNat ≤ (fb + 24#64).toNat)
    (hmt : rdd(V, fb + 24#64) = 0) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 47 ∧
      g' = { g with rax := 0, rdx := 1, rbx := g.rdi, rsp := g.rsp - 24#64 } ∧
      F0 V V' g.rsp g.rbx g.rsi g.rdx) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst h0 hfd
  wpx [W_0, W_27, W_42, o0, o1, o2, Op.ldf]
  have e : rdd(Vst (Vst (Vst V (rsp - 8) (toBytesLE rbx 8)) (rsp - 8 - 16#64) (toBytesLE rsi 8))
      (rsp - 8 - 16#64 + 8#64) (toBytesLE rdx 8), fb + 24#64) = 0 := by
    repeat pv
    exact hmt
  rw [e]
  refine ⟨off_ft hst 16 (by bv_omega) (by decide), off_ft hst 0 (by bv_omega) (by decide),
    off_ft hst 8 (by bv_omega) (by decide), fun h => ?_,
    fun _ => ⟨hfl, fun h => absurd h (by decide), fun _ => ⟨?_, fun a ha => ?_, ?_, ?_, ?_⟩⟩⟩
  · simp only [BitVec.and_self, beq_iff_eq] at h
    exact absurd h h0
  · rw [show rsp - 8 - 16#64 = rsp - 24#64 from by bv_omega]
    rfl
  · repeat pv
  · pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [show rsp - 24#64 = rsp - 8 - 16#64 from by bv_omega]
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [show rsp - 16 = rsp - 8 - 16#64 + 8#64 from by bv_omega, vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- `&__exit_funcs` for `__new_exitfn`. -/
theorem vc_54 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_54 fb F Wl (fun j' g' _ V' => j' = 61 ∧ g' = { g with rdi := 7938992#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_54, o3]

/-- A place was given. -/
theorem vc_66 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax ≠ 0) :
    W_66 fb F Wl (fun j' g' _ V' => j' = 75 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  wpx [W_66, o4]
  refine ⟨fun h' => ?_, fun _ => trivial⟩
  simp only [BitVec.and_self, beq_iff_eq] at h'
  exact absurd h' h

/-- The place's flavor 4, the function mangled with the pointer guard `pg`. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {pg : BitVec 64}
    (hw : ∀ i < 8, Foot Wl (Addr.add g.rax i)) (hgf : ∀ i < 8, Foot F.data ((fb + 48#64).add i))
    (hax : g.rax.toNat + 8 ≤ 2 ^ 64) (hfb : (fb + 48#64).toNat + 8 ≤ 2 ^ 64)
    (hd : g.rax.toNat + 8 ≤ (fb + 48#64).toNat ∨ (fb + 48#64).toNat + 8 ≤ g.rax.toNat)
    (hpg : rdq(V, fb + 48#64) = pg) :
    wp F Wl (o5 fb) (fun g' _ V' => g' = { g with rdi := (g.rbx ^^^ pg).rotateLeft 17 } ∧
      Out g.rax.toNat (g.rax.toNat + 8) V V' ∧ rdq(V', g.rax) = 4) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hax hd
  wpx [o5, Op.xormf, Op.rol64]
  have e : rdq(Vst V rax (toBytesLE (4#64) 8), fb + 48#64) = pg := by
    pv
    exact hpg
  rw [e]
  refine ⟨hw, hgf, fun fl => ⟨rfl, fun a ha => ?_, ?_⟩⟩
  · pv
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The place's function. -/
theorem vc_108 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i))
    (hax : g.rax.toNat + 16 ≤ 2 ^ 64) :
    wp F Wl o6 (fun g' _ V' => g' = g ∧ Out (g.rax.toNat + 8) (g.rax.toNat + 16) V V' ∧
      rdq(V', g.rax + 8#64) = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hax
  wpx [o6]
  refine ⟨hw, fun a ha => ?_, ?_⟩
  · pv
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- One thread still: to the lock's `sub`, `r8d` 0 for the answer. -/
theorem vc_116 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) (hmt : rdd(V, fb + 24#64) = 0) :
    W_116 fb F Wl (fun j' g' _ V' => j' = 130 ∧ g' = { g with r8 := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_116, o7, Op.ldf, hmt]
  exact ⟨hfl, fun h => absurd h (by decide), fun _ => rfl⟩

/-- The answer 0 and the frame given back, to the `ret`. -/
theorem vc_137 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : g.r8 = 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_137 fb F Wl (fun j' g' _ V' => j' = 145 ∧
      g' = { g with rax := 0, rbx := rdq(V, g.rsp + 16#64), rsp := g.rsp + 24#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hl
  subst h8
  wpx [W_137, o8]
  refine ⟨hl, ?_⟩
  rw [show rsp + 16#64 + 8 = rsp + 24#64 from by bv_omega]
  rfl

/-! ## The call -/

/-- The registers `g` in the function's body, from those at the entry `g₀`: the frame's stack pointer, `rbx` the
function, the other registers a call keeps as they were. -/
structure St (g₀ g : Gprs) (sp fn : BitVec 64) : Prop where
  rsp : g.rsp = sp - 24#64
  rbx : g.rbx = fn
  kp : g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- Addresses in the 56 bytes under `sp`: the frame, the return address of the call, the callee's frame. -/
theorem sp_c (sp : Addr) (h : 56 ≤ sp.toNat) :
    sp - 24#64 = sp - 56#64 + BitVec.ofNat 64 32 ∧ sp - 24#64 - 8 = sp - 32#64 ∧
    sp - 32#64 = sp - 56#64 + BitVec.ofNat 64 24 ∧ (sp - 32#64).toNat + 32 = sp.toNat ∧
    sp - 32#64 - 24#64 = sp - 56#64 ∧ sp - 32#64 + 8#64 = sp - 24#64 ∧ (sp - 24#64).toNat + 24 = sp.toNat ∧
    sp - 24#64 + 8#64 = sp - 16 ∧ (sp - 16).toNat + 16 = sp.toNat ∧ sp - 24#64 + 16#64 = sp - 8 ∧
    (sp - 8).toNat + 8 = sp.toNat ∧ sp - 24#64 + 24#64 = sp ∧ sp - 16 = sp - 56#64 + BitVec.ofNat 64 40 ∧
    sp - 8 = sp - 56#64 + BitVec.ofNat 64 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Addresses in the place at `p`: its four words. -/
theorem p_c (p : Addr) (h0 : 0 < p.toNat) (h : p.toNat + 32 ≤ 2 ^ 64) :
    (p + 8#64).toNat = p.toNat + 8 ∧ (p + 16#64).toNat = p.toNat + 16 ∧ p + 16#64 + 8#64 = p + 24#64 ∧
    (p + 24#64).toNat = p.toNat + 24 ∧ p ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Addresses in the thread's block at `fb`: `multiple_threads` and the pointer guard. -/
theorem f_c (fb : Addr) (h : fb.toNat + 56 ≤ 2 ^ 64) :
    (fb + 24#64).toNat = fb.toNat + 24 ∧ (fb + 48#64).toNat = fb.toNat + 48 := by
  refine ⟨?_, ?_⟩ <;> bv_omega

/-- What the bytes `V'` after the call have of the bytes `V` before it, the stack pointer `sp` at the entry, the
list `l`, its place `p` that had `n` places before it: all outside the 56 bytes under `sp`, the list's count, the
place, and the lock with the counter of `__new_exitfn`; the count `n + 1`, the place's flavor 4 with the function
`fn` (mangled), the argument and the DSO handle, the counter one more, the lock free. -/
structure Reg (V V' : Addr → Byte) (sp l p : Addr) (n : Nat) (fn arg dso : BitVec 64) : Prop where
  out : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat) →
    ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) → ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 32) →
    ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V' a = V a
  idx : rdq(V', l + 8#64) = BitVec.ofNat 64 (n + 1)
  flv : rdq(V', p) = 4
  fn : rdq(V', p + 8#64) = fn
  arg : rdq(V', p + 16#64) = arg
  dso : rdq(V', p + 24#64) = dso
  cnt : rdq(V', 8029192#64) = rdq(V, 8029192#64) + 1
  lock : rdd(V', 8029184#64) = 0

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- `__cxa_atexit (fn, arg, dso)` with one thread, `fn` not null, the lock free, no exit function run, the list `l`
of `__exit_funcs` with `n < 32` places taken, none of them and no list after it or the last of them not free again:
the run reaches the return address with `rax` 0, the list's place `p = l + 16 + 32 n` filled (`Reg`), the registers
a call keeps as at the entry. -/
theorem cxa_ok {fb sp l p : Addr} {n : Nat} {fn arg dso : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L cxa_at cxa) (hinn : CodeIn L Nef.nef_at Nef.nef)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cxa_at)
    (hsp : X.cpu.gpr.rsp = sp) (hdi : X.cpu.gpr.rdi = fn) (hsi : X.cpu.gpr.rsi = arg) (hdx : X.cpu.gpr.rdx = dso)
    (hst : ∀ i < 56, Foot Wl (Addr.add (sp - 56#64) i)) (hlr : ∀ i < 8, Foot F.data (Addr.add sp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, sp) = e₂.add j₂) (hs8 : sp.toNat + 8 ≤ 2 ^ 64) (h0 : fn ≠ 0)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat ∨ sp.toNat ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat) (hmt : rdd(V, fb + 24#64) = 0)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hflag : rdb(V, 8010388#64) = 0)
    (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i)) (hl : rdq(V, 7938992#64) = l) (hl0 : l ≠ 0)
    (hn : n < 32) (hpe : p = l + BitVec.ofNat 64 (16 + 32 * n))
    (hlw : ∀ i < 1040, Foot Wl (Addr.add l i)) (hld : l.toNat + 1096 ≤ sp.toNat)
    (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i)) (hcd : 8029256 ≤ sp.toNat)
    (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat)
    (hlock : rdd(V, 8029184#64) = 0) (hidx : rdq(V, l + 8#64) = BitVec.ofNat 64 n)
    (hnext : n = 0 → rdq(V, l) = 0) (hprev : 0 < n → rdq(V, p - 32#64) ≠ 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Reg V V' sp l p n ((fn ^^^ rdq(V, fb + 48#64)).rotateLeft 17) arg dso →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = 0 → Osv.Back X.cpu.gpr g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨sa, sb, sc, sd, se, sf, sg, sh, si, sj, sk, sm, sn, so⟩ := sp_c sp (by omega)
  obtain ⟨t8, -, ep, -, -, hpos⟩ := Nef.l_n l n hn (by omega)
  rw [← hpe] at ep hpos
  obtain ⟨p8, p16, a24, p24, np⟩ := p_c p (by omega) (by omega)
  obtain ⟨f24, f48⟩ := f_c fb hfn
  have ek : (8029184#64).toNat = 8029184 := rfl
  have ec : (8029192#64).toNat = 8029192 := rfl
  have eg : (8010388#64).toNat = 8010388 := rfl
  have ep : (7938992#64).toNat = 7938992 := rfl
  have hstd : ∀ i < 56, Foot F.data (Addr.add (sp - 56#64) i) := fun i hi => c.hws _ (hst i hi)
  have hf24 : ∀ i < 4, Foot F.data ((fb + 24#64).add i) := off_ft hft 24 rfl (by decide)
  have hf48 : ∀ i < 8, Foot F.data ((fb + 48#64).add i) := off_ft hft 48 rfl (by decide)
  have hpw : ∀ i < 32, Foot Wl (Addr.add p i) := off_ft hlw (16 + 32 * n) hpe (by omega)
  -- the frame
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by rw [hsp]; omega) (by rw [hsp, sa]; exact off_ft hst 32 rfl (by decide)) (by rw [hdi]; exact h0)
      hf24 (by omega) (by rw [hsp]; omega) hmt) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hsp, hsi, hdx] at hF
  rw [hsp, hdi] at hg₁
  have hS₁ : St X.cpu.gpr Y₁.cpu.gpr sp fn := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the lock
  refine c.s_cmpxchg_rip32 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (cx_47 _) (g := 8029184#64) (by decide)
    (fun i hi => hkw i (by omega)) ?_ ?_
  · rw [show rv Y₁ 32 0 = 0 from by show (Y₁.cpu.gpr.get (regOf 0)).setWidth 32 = 0; rw [hg₁]; rfl, ← hlock]
    exact congrArg (ofBytesLE 32) (hF.out.rd (by omega) (by omega))
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
  obtain ⟨V₂, o2, hl2, hA₂⟩ : ∃ V₂, Out 8029184 8029188 V₁ V₂ ∧ rdd(V₂, 8029184#64) = 1 ∧
      Agree F Y₂.proc.mm.mem V₂ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by decide)).mono (by decide) (by decide), by
      rw [vs (by ln) (by decide), ofBytesLE_toBytesLE (n := 4) rfl]
      show (Y₁.cpu.gpr.get (regOf 2)).setWidth 32 = 1
      rw [hg₁]
      rfl, hA₂⟩
  have hS₂ : St X.cpu.gpr Y₂.cpu.gpr sp fn := by rw [hg₂]; exact ⟨hS₁.rsp, hS₁.rbx, hS₁.kp⟩
  -- `__new_exitfn (&__exit_funcs)`
  refine (c_54 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ vc_54 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hS₃ : St X.cpu.gpr Y₃.cpu.gpr sp fn := by rw [hg₃]; exact ⟨hS₂.rsp, hS₂.rbx, hS₂.kp⟩
  refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_61 _) hinn (Nef.lt_len (by decide)) (by decide)
    (fun i hi => by rw [hS₃.rsp, sb, sc]; exact off_ft hst 24 rfl (by decide) i hi) ?_
  rintro Z₁ u₁ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hS₃.rsp, sb] at hAZ hgZ
  obtain ⟨V₃, o3, hra3, hAZ⟩ : ∃ V₃, Out (sp.toNat - 32) (sp.toNat - 24) V₂ V₃ ∧
      rdq(V₃, sp - 32#64) = cxa_at.add 66 ∧ Agree F Z₁.proc.mm.mem V₃ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by omega)).mono (by omega) (by omega), by
      rw [vs (by ln) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _, hAZ⟩
  have hZsp : Z₁.cpu.gpr.rsp = sp - 32#64 := by rw [hgZ]; rfl
  have hZdi : Z₁.cpu.gpr.rdi = 7938992#64 := by
    rw [hgZ]
    show Y₃.cpu.gpr.rdi = _
    rw [hg₃]
  have hZ : Z₁.cpu.gpr.rbx = fn ∧ Z₁.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Z₁.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Z₁.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z₁.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hgZ]
    exact ⟨hS₃.rbx, hS₃.kp⟩
  have h3 : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029188) → V₃ a = V a := fun a h1 h2 =>
    (o3 a (by omega)).trans ((o2 a h2).trans (hF.out a (by omega)))
  refine Nef.nef_ok (l := l) (p := p) (n := n) c hinn hKZ hAZ hrZ (by rw [hZsp, se]; exact fun i hi => hst i (by omega))
    (by rw [hZsp, sc]; exact off_ft hstd 24 rfl (by decide)) hin (lt_len (j := 66) (by decide))
    (by rw [hZsp]; exact hra3) (by rw [hZsp]; omega) hfl
    (by rw [← hflag]; exact congrArg (ofBytesLE 8) (rd_out2 h3 (by omega) (by omega) (by omega)))
    (by rw [hZdi]; exact hp) (by rw [hZdi, hZsp]; omega)
    (by rw [hZdi, ← hl]; exact congrArg (ofBytesLE 64) (rd_out2 h3 (by omega) (by omega) (by omega))) hl0
    hn hpe hlw (by rw [hZsp]; omega) (off_ft hkw 8 (by decide) (by decide))
    (by rw [hZsp]; omega) (by omega)
    (by rw [← hidx]; exact congrArg (ofBytesLE 64) (rd_out2 h3 (by omega) (by omega) (by omega)))
    (fun h => by rw [← hnext h]; exact congrArg (ofBytesLE 64) (rd_out2 h3 (by omega) (by omega) (by omega)))
    (fun h e => by
      obtain ⟨-, -, em⟩ := hpos h
      exact hprev h ((congrArg (ofBytesLE 64) (rd_out2 h3 (by omega) (by omega) (by omega))).symm.trans e)) ?_
  rintro V₄ g' Z₂ u₂ hK₄ hA₄ hN hr₄ rfl hax₄ ⟨b1, b2, b3, b4, b5, b6, b7⟩
  rw [hZsp] at hN b1
  have n4 : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat - 32) →
      ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) → ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 8) →
      ¬ (8029192 ≤ a.toNat ∧ a.toNat < 8029200) → V₄ a = V₃ a := fun a h1 h2 h3 h4 => hN.out a (by omega) h2 h3 h4
  have hS₄ : St X.cpu.gpr Z₂.cpu.gpr sp fn :=
    ⟨b1.trans sf, b2.trans hZ.1, b3.trans hZ.2.1, b4.trans hZ.2.2.1, b5.trans hZ.2.2.2.1, b6.trans hZ.2.2.2.2.1,
      b7.trans hZ.2.2.2.2.2⟩
  have h41 : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat - 24) →
      ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) → ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 8) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₄ a = V₁ a := fun a h1 h2 h3 h4 =>
    (n4 a (by omega) h2 h3 (by omega)).trans ((o3 a (by omega)).trans (o2 a (by omega)))
  -- a place was given
  refine (c_66 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_66 (by rw [hax₄]; exact np)) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hS₅ : St X.cpu.gpr Y₅.cpu.gpr sp fn := by rw [hg₅]; exact ⟨hS₄.rsp, hS₄.rbx, hS₄.kp⟩
  have hax₅ : Y₅.cpu.gpr.rax = p := by rw [hg₅]; exact hax₄
  -- the argument
  have e0 : eaD Y₅ 4 0 = sp - 24#64 := by
    show Y₅.cpu.gpr.rsp + 0#64 = _
    rw [hS₅.rsp]
    exact BitVec.add_zero _
  refine c.s_movq_ld hK₅ hA₅ hin (lt_len (by decide)) hr₅ (movq_75 _) (fun i hi => ?_) ?_
  · rw [e0, sa]
    exact off_ft hstd 32 rfl (by decide) i hi
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hx₆⟩
  have harg : rdq(V₄, sp - 24#64) = arg := by
    rw [← hF.sarg]
    exact congrArg (ofBytesLE 64) (rd_out4 h41 (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [e0, harg] at hx₆
  have hS₆ : St X.cpu.gpr Y₆.cpu.gpr sp fn := by rw [hg₆]; exact ⟨hS₅.rsp, hS₅.rbx, hS₅.kp⟩
  have hax₆ : Y₆.cpu.gpr.rax = p := by rw [hg₆]; exact hax₅
  -- the flavor, the function mangled
  have hpg : rdq(V₄, fb + 48#64) = rdq(V, fb + 48#64) :=
    congrArg (ofBytesLE 64) ((rd_out4 h41 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hF.out.rd (by omega) (by omega)))
  refine c.runV hfs hin (blk_80 prof fb) rfl _ hK₆ hA₆ hr₆ (vc_80 (pg := rdq(V, fb + 48#64))
    (by rw [hax₆]; exact fun i hi => hpw i (by omega)) hf48 (by rw [hax₆]; omega) (by omega)
    (by rw [hax₆]; omega) hpg) ?_
  rintro g fl V₅ ⟨rfl, o5, hf5⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ hv₇
  rw [hax₆] at o5 hf5
  have hS₇ : St X.cpu.gpr Y₇.cpu.gpr sp fn := by rw [hg₇]; exact ⟨hS₆.rsp, hS₆.rbx, hS₆.kp⟩
  have hax₇ : Y₇.cpu.gpr.rax = p := by rw [hg₇]; exact hax₆
  have hdi₇ : Y₇.cpu.gpr.rdi = (fn ^^^ rdq(V, fb + 48#64)).rotateLeft 17 := by
    rw [hg₇]
    show (Y₆.cpu.gpr.rbx ^^^ _).rotateLeft 17 = _
    rw [hS₆.rbx]
  -- the DSO handle
  have e8 : eaD Y₇ 4 8 = sp - 16 := by
    show Y₇.cpu.gpr.rsp + 8#64 = _
    rw [hS₇.rsp]
    exact sh
  refine c.s_movhps_ld hK₇ hA₇ hin (lt_len (by decide)) hr₇ (movhps_103 _) (fun i hi => ?_) ?_
  · rw [e8, sn]
    exact off_ft hstd 40 rfl (by decide) i hi
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈, hx₈⟩
  have hx₇ : xlo Y₇ 0 = arg.setWidth 128 := by
    show (Y₇.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₇]
    exact hx₆
  have hdso : rdq(V₅, sp - 16) = dso := by
    rw [← hF.sdso]
    exact congrArg (ofBytesLE 64) ((o5.rd (by omega) (by omega)).trans
      (rd_out4 h41 (by omega) (by omega) (by omega) (by omega) (by omega)))
  rw [e8, hdso, hx₇, lane_lo] at hx₈
  have hS₈ : St X.cpu.gpr Y₈.cpu.gpr sp fn := by rw [hg₈]; exact ⟨hS₇.rsp, hS₇.rbx, hS₇.kp⟩
  have hax₈ : Y₈.cpu.gpr.rax = p := by rw [hg₈]; exact hax₇
  have hdi₈ : Y₈.cpu.gpr.rdi = (fn ^^^ rdq(V, fb + 48#64)).rotateLeft 17 := by rw [hg₈]; exact hdi₇
  -- the function
  refine c.runV hfs hin (((blk_108 prof).at cxa_at).fs fb) rfl _ hK₈ hA₈ hr₈
    (vc_108 (by rw [hax₈]; exact off_ft hpw 8 rfl (by decide)) (by rw [hax₈]; omega)) ?_
  rintro g fl V₆ ⟨rfl, o6, hf6⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ hv₉
  rw [hax₈] at o6
  rw [hax₈, hdi₈] at hf6
  have hS₉ : St X.cpu.gpr Y₉.cpu.gpr sp fn := by rw [hg₉]; exact ⟨hS₈.rsp, hS₈.rbx, hS₈.kp⟩
  have hax₉ : Y₉.cpu.gpr.rax = p := by rw [hg₉]; exact hax₈
  -- the argument and the DSO handle
  have e16 : eaD Y₉ 0 16 = p + 16#64 := by
    show Y₉.cpu.gpr.rax + 16#64 = _
    rw [hax₉]
  refine c.s_movups_st hK₉ hA₉ hin (lt_len (by decide)) hr₉ (movups_112 _) (fun i hi => ?_) ?_
  · rw [e16]
    exact off_ft hpw 16 rfl (by decide) i hi
  rintro Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀⟩
  have hx₉ : xlo Y₉ 0 = (dso ++ arg).setWidth 128 := by
    show (Y₉.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₉]
    exact hx₈
  rw [e16, hx₉, st16] at hA₁₀
  obtain ⟨V₇, ⟨o7, ha7, hd7⟩, hA₁₀⟩ : ∃ V₇, (Out (p + 16#64).toNat ((p + 16#64).toNat + 16) V₆ V₇ ∧
      rdq(V₇, p + 16#64) = arg ∧ rdq(V₇, p + 16#64 + 8#64) = dso) ∧ Agree F Y₁₀.proc.mm.mem V₇ :=
    ⟨_, two_q V₆ (p + 16#64) arg dso (by omega), hA₁₀⟩
  rw [p16] at o7
  rw [a24] at hd7
  have hS₁₀ : St X.cpu.gpr Y₁₀.cpu.gpr sp fn := by rw [hg₁₀]; exact ⟨hS₉.rsp, hS₉.rbx, hS₉.kp⟩
  have h71 : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat - 24) →
      ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) → ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 32) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₇ a = V₁ a := fun a h1 h2 h3 h4 =>
    (o7 a (by omega)).trans ((o6 a (by omega)).trans ((o5 a (by omega)).trans (h41 a h1 h2 (by omega) h4)))
  -- the lock given back
  have hmt7 : rdd(V₇, fb + 24#64) = 0 := by
    rw [← hmt]
    exact congrArg (ofBytesLE 32) ((rd_out4 h71 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hF.out.rd (by omega) (by omega)))
  have hl7 : rdd(V₇, 8029184#64) = 1 := by
    rw [← hl2]
    exact congrArg (ofBytesLE 32) ((o7.rd (by omega) (by omega)).trans ((o6.rd (by omega) (by omega)).trans
      ((o5.rd (by omega) (by omega)).trans ((rd_out4 n4 (by omega) (by omega) (by omega) (by omega)
        (by omega)).trans (o3.rd (by omega) (by omega))))))
  refine (c_116 prof fb).run c hfs hin _ hK₁₀ hA₁₀ hr₁₀ (vc_116 hf24 hmt7) ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ hg₁₁ -
  have hS₁₁ : St X.cpu.gpr Y₁₁.cpu.gpr sp fn := by rw [hg₁₁]; exact ⟨hS₁₀.rsp, hS₁₀.rbx, hS₁₀.kp⟩
  have h8₁₁ : Y₁₁.cpu.gpr.r8 = 0 := by rw [hg₁₁]
  refine c.s_sub_rip32 hK₁₁ hA₁₁ hin (lt_len (by decide)) hr₁₁ (sb_130 _) (g := 8029184#64) (by decide)
    (fun i hi => hkw i (by omega)) ?_
  rintro Y₁₂ t₁₂ hK₁₂ hA₁₂ ⟨hr₁₂, hg₁₂⟩
  obtain ⟨V₈, o8, hl8, hA₁₂⟩ : ∃ V₈, Out 8029184 8029188 V₇ V₈ ∧ rdd(V₈, 8029184#64) = 0 ∧
      Agree F Y₁₂.proc.mm.mem V₈ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by decide)).mono (by decide) (by decide), by
      rw [vs (by ln) (by decide), ofBytesLE_toBytesLE (n := 4) rfl, hl7]
      decide, hA₁₂⟩
  have hS₁₂ : St X.cpu.gpr Y₁₂.cpu.gpr sp fn := by rw [hg₁₂]; exact ⟨hS₁₁.rsp, hS₁₁.rbx, hS₁₁.kp⟩
  -- to the `ret`
  refine (c_137 prof fb).run c hfs hin _ hK₁₂ hA₁₂ hr₁₂ (vc_137 (by rw [hg₁₂]; exact h8₁₁)
    (by rw [hS₁₂.rsp, sj, so]; exact off_ft hstd 48 rfl (by decide))) ?_
  rintro j' g fl V₈ ⟨rfl, rfl, rfl⟩ Y₁₃ t₁₃ hK₁₃ hA₁₃ hr₁₃ hg₁₃ -
  have hb : ∀ a : Addr, ¬ (sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat - 24) →
      ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) → ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 32) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₈ a = V₁ a := fun a h1 h2 h3 h4 =>
    (o8 a (by omega)).trans (h71 a h1 h2 h3 h4)
  have hsp₁₃ : Y₁₃.cpu.gpr.rsp = sp := by
    rw [hg₁₃]
    show Y₁₂.cpu.gpr.rsp + 24#64 = _
    rw [hS₁₂.rsp]
    exact sm
  refine c.s_ret hK₁₃ hA₁₃ hin (lt_len (by decide)) hr₁₃ (ret_145 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₁₃]
    exact hlr i hi
  · rw [hsp₁₃, ← hra]
    exact congrArg (ofBytesLE 64) ((rd_out4 hb hs8 (by omega) (by omega) (by omega) (by omega)).trans
      (hF.out.rd hs8 (by omega)))
  rintro Z t' hKZ' hAZ' ⟨hrZ', hgZ'⟩
  have hbx : Y₁₃.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₁₃]
    show rdq(V₈, Y₁₂.cpu.gpr.rsp + 16#64) = _
    rw [hS₁₂.rsp, sj, ← hF.sbx]
    exact congrArg (ofBytesLE 64) (rd_out4 hb (by omega) (by omega) (by omega) (by omega) (by omega))
  have hkp : Y₁₃.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₁₃.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₁₃.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₁₃.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₁₃.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₁₃]
    exact hS₁₂.kp
  have hax : Y₁₃.cpu.gpr.rax = 0 := by rw [hg₁₃]
  refine k V₈ _ Z t' hKZ' hAZ'
    ⟨fun a h1 h2 h3 h4 => (hb a (by omega) h2 h3 h4).trans (hF.out a (by omega)), ?_, ?_, ?_, ?_, ?_, ?_, hl8⟩
    hrZ' hgZ' hax ⟨?_, hbx, hkp.1, hkp.2.1, hkp.2.2.1, hkp.2.2.2.1, hkp.2.2.2.2⟩
  · rw [← hN.idx]
    exact congrArg (ofBytesLE 64) ((o8.rd (by omega) (by omega)).trans ((o7.rd (by omega) (by omega)).trans
      ((o6.rd (by omega) (by omega)).trans (o5.rd (by omega) (by omega)))))
  · rw [← hf5]
    exact congrArg (ofBytesLE 64) ((o8.rd (by omega) (by omega)).trans ((o7.rd (by omega) (by omega)).trans
      (o6.rd (by omega) (by omega))))
  · rw [← hf6]
    exact congrArg (ofBytesLE 64) ((o8.rd (by omega) (by omega)).trans (o7.rd (by omega) (by omega)))
  · rw [← ha7]
    exact congrArg (ofBytesLE 64) (o8.rd (by omega) (by omega))
  · rw [← hd7]
    exact congrArg (ofBytesLE 64) (o8.rd (by omega) (by omega))
  · have e1 : rdq(V₈, 8029192#64) = rdq(V₄, 8029192#64) :=
      congrArg (ofBytesLE 64) ((o8.rd (by omega) (by omega)).trans ((o7.rd (by omega) (by omega)).trans
        ((o6.rd (by omega) (by omega)).trans (o5.rd (by omega) (by omega)))))
    have e2 : rdq(V₃, 8029192#64) = rdq(V, 8029192#64) :=
      congrArg (ofBytesLE 64) (rd_out2 h3 (by omega) (by omega) (by omega))
    rw [e1, hN.cnt, e2]
  · show Y₁₃.cpu.gpr.rsp + 8 = X.cpu.gpr.rsp + 8#64
    rw [hsp₁₃, hsp]
    rfl

end FV7z.Cxa
