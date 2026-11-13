import FV7z.Gor.Mem
import FV7z.Tun.Inv
import FV7z.Sbrk.Holds
/-!
# `_dl_get_origin`: the conditions of the pieces between cut points (PLAN.md G3, startup)

- The instructions the pieces stop at: `or qword [rsp], 0` (17), `syscall` (49), `ret` (271), the `call` of `mempcpy`
  (300), as `Dec` facts.
- `vc_0`: the four `push`es and `sub rsp, 4096`; `vc_22`: the arguments of `readlink`.
- `vc_51e`: an error (`eax` above `-4096`) to 152; `vc_51k`: `n` bytes, `1 ≤ n < 4096`, the first `/`, to the loop.
- `vc_114`: the loop from the end of the `c` bytes back to the last `/` (`c ≥ 2`); `vc_114o` (`c = 1`): `malloc (2)`.
- `vc_129`: the directory `/` stored; `vc_283`: the arguments of `mempcpy`; `vc_305`: the NUL after the bytes.
- `vc_152`: `_dl_origin_path` null, to 248; `vc_248`: `-1`; `vc_255`: the epilogue to the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gor

/-! ## The instructions the pieces stop at -/

def por : List Byte := [0x48, 0x83, 0x0c, 0x24, 0x00]
theorem por_0 : ∀ feat, Dec feat por 0 (FV7z.mk .or 64 [.mem (mbd 4 0 64), .imm 64 0] 5) := by dec_rfl
theorem w_17 : por <+: gor.drop 17 := by decide +kernel
theorem or_17 (feat : Features) : Dec feat gor 17 (FV7z.mk .or 64 [.mem (mbd 4 0 64), .imm 64 0] 5) :=
  Dec.shift (j := 17) (k := 0) (por_0 feat) w_17 (Nat.zero_le _)

def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_49 : psys <+: gor.drop 49 := by decide +kernel
theorem sys_49 (feat : Features) : Dec feat gor 49 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 49) (k := 0) (psys_0 feat) w_49 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_271 : pret <+: gor.drop 271 := by decide +kernel
theorem ret_271 (feat : Features) : Dec feat gor 271 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 271) (k := 0) (pret_0 feat) w_271 (Nat.zero_le _)

def pc300 : List Byte := [0xe8, 0xef, 0x1f, 0xd5, 0xff]
theorem pc300_0 : ∀ feat, Dec feat pc300 0 (FV7z.mk .call 64 [.rel 18446744073706741743] 5) := by dec_rfl
theorem w_300 : pc300 <+: gor.drop 300 := by decide +kernel
theorem call_300 (feat : Features) : Dec feat gor 300 (FV7z.mk .call 64 [.rel 18446744073706741743] 5) :=
  Dec.shift (j := 300) (k := 0) (pc300_0 feat) w_300 (Nat.zero_le _)

/-! ## Numbers in registers -/

theorem sk0n (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 0 v =
      Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl

theorem sw32n {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw64n {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sx32n {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false
    (BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [BitVec.toNat_ofNat]; omega))]
  exact sw64n (by omega)

theorem add32n {n : Nat} (h : n + 1 < 2 ^ 32) : BitVec.ofNat 32 n + 1#32 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem dec64n {n : Nat} (h1 : 1 ≤ n) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + 18446744073709551615#64)) =
      BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ne32n {n m : Nat} (h : n < 2 ^ 32) (hm : m < 2 ^ 32) (hne : n ≠ m) :
    decide (BitVec.ofNat 32 n = BitVec.ofNat 32 m) = false :=
  decide_eq_false fun e => by
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- The registers the pieces keep. -/
abbrev Kp (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- The prologue: four `push`es, `sub rsp, 4096`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hst : ∀ i < 32, Foot Wl (Addr.add (g.rsp - 32#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 17 ∧ g' = { g with rsp := g.rsp - 8 - 8 - 8 - 8 - 4096#64 } ∧
      V' = frV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst
  have slot : ∀ (a : Addr) (k : Nat), k < 32 → a = Addr.add (rsp - 32#64) k → Foot Wl a :=
    fun a k hk ha => ha ▸ hst k hk
  wpx [W_0, o0, Op.push]
  refine ⟨fun i hi => slot _ (24 + i) (by omega) ?_, fun i hi => slot _ (16 + i) (by omega) ?_,
    fun i hi => slot _ (8 + i) (by omega) ?_, fun i hi => slot _ i (by omega) ?_, ?_⟩
  all_goals first | (simp only [Addr.add]; bv_omega) | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | rfl

/-- The arguments of `readlink ("/proc/self/exe", rsp, 4096)`. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_22 F Wl (fun j' g' _ V' => j' = 49 ∧ g' = { g with rax := BitVec.setWidth 64 89#32,
      rdx := BitVec.setWidth 64 4096#32, rsp := g.rsp - 8#64, rbp := g.rsp - 8#64, rsi := g.rsp - 8#64,
      rdi := 7366691#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_22, o1]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩

/-- `readlink` failed: `eax` above `-4096`, to 152. -/
theorem vc_51e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : 4294963200 < (BitVec.setWidth 32 g.rax).toNat) :
    W_51 F Wl (fun j' g' _ V' => j' = 152 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax
  have d1 : decide ((BitVec.setWidth 32 rax).toNat < 4294963200) = false := decide_eq_false (by omega)
  have d2 : decide (BitVec.setWidth 32 rax = 4294963200#32) = false :=
    decide_eq_false fun h => by rw [h] at hax; exact absurd hax (by decide)
  wpx [W_51, W_58, W_62, W_71, W_80, o2, o3, o4, o5, o6, Op.cdqe, Sbrk.cond_14, d1, d2, Bool.or_false,
    Bool.not_false, Bool.false_eq_true, false_implies, Bool.or_self]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | trivial

/-- `readlink` gave `n` bytes, `1 ≤ n < 4096`, the first `/`: to the loop at 114 with `ecx = n`, `rax` the end. -/
theorem vc_51k {g : Gprs} {f : Rflags} {V : Addr → Byte} {n : Nat} (hn1 : 1 ≤ n) (hn2 : n < 4096)
    (hax : g.rax = BitVec.ofNat 64 n) (hf : ∀ i < 1, Foot F.data (Addr.add g.rsp i)) (h0 : V g.rsp = 0x2f) :
    W_51 F Wl (fun j' g' _ V' => j' = 114 ∧ g'.rcx = BitVec.ofNat 64 n ∧ g'.rax = g.rbp + BitVec.ofNat 64 n ∧
      Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hf h0
  subst hax
  have e32 := sw32n (n := n) (by omega)
  have hmod : n % 4294967296 = n := Nat.mod_eq_of_lt (by omega)
  have d1 : decide (n < 4294963200) = true := decide_eq_true (by omega)
  have d2 : decide (BitVec.ofNat 32 n = 4294963200#32) = false := ne32n (by omega) (by omega) (by omega)
  have d3 : (BitVec.ofNat 32 n == 0) = false := beq_eq_false_iff_ne.2 fun e => by
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  have d4 : (BitVec.ofNat 32 n).msb = false :=
    BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [BitVec.toNat_ofNat]; omega)
  have hb : ofBytesLE 8 (List.map V (byteAddrs rsp 1)) = 0x2f := by rw [Tun.rd1, h0]
  have d5 : decide (BitVec.setWidth 8 (BitVec.setWidth 32 (0x2f : Byte)) = 91#8) = false := by decide
  have d6 : decide (BitVec.setWidth 8 (BitVec.setWidth 32 (0x2f : Byte)) = 47#8) = true := by decide
  wpx [W_51, W_58, W_62, W_71, W_80, o2, o3, o4, o5, o6, Op.cdqe, Sbrk.cond_14, Sbrk.arith_of, sk0n, e32, hmod,
    d1, d2, d3, d4, hb, d5, d6, BitVec.and_self, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, false_implies, Bool.or_self, bne_self_eq_false, Bool.bne_false]
  all_goals first | exact hf | trivial | skip
  refine ⟨hf, ?_⟩
  refine ⟨?_, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact sw64n (by omega)
  · rw [sx32n (by omega), BitVec.add_comm]

/-- The loop, `c ≥ 2` bytes before `rax`: the byte at `c - 1` a `/` (to the `malloc` at 278 with `c + 1`, `ebx` the
`c - 1` bytes to copy), or not (back to 114 with `c - 1`). -/
theorem vc_114 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c : Nat} (hc1 : 2 ≤ c) (hc2 : c < 4096)
    (hcx : g.rcx = BitVec.ofNat 64 c) (hax : g.rax = g.rbp + BitVec.ofNat 64 c)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + BitVec.ofNat 64 (c - 1)) i)) :
    W_114 F Wl (fun j' g' _ V' =>
      (V (g.rbp + BitVec.ofNat 64 (c - 1)) = 0x2f ∧ j' = 278 ∧ g'.rdi = BitVec.ofNat 64 (c + 1) ∧
        g'.rbx = BitVec.ofNat 64 (c - 1) ∧ Kp g g' ∧ V' = V) ∨
      (V (g.rbp + BitVec.ofNat 64 (c - 1)) ≠ 0x2f ∧ j' = 114 ∧ g'.rcx = BitVec.ofNat 64 (c - 1) ∧
        g'.rax = g.rbp + BitVec.ofNat 64 (c - 1) ∧ Kp g g' ∧ V' = V)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hcx hax hf ⊢
  subst hcx hax
  have e32 := sw32n (n := c) (by omega)
  have d1 : decide (BitVec.ofNat 32 c = 1#32) = false := ne32n (by omega) (by omega) (by omega)
  have ea : rbp + BitVec.ofNat 64 c - 1#64 = rbp + BitVec.ofNat 64 (c - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have ec : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 c + 18446744073709551615#64)) =
      BitVec.ofNat 64 (c - 1) := dec64n (by omega) (by omega)
  have ed : BitVec.signExtend 64 (BitVec.ofNat 32 c + 1#32) = BitVec.ofNat 64 (c + 1) := by
    rw [add32n (by omega), sx32n (by omega)]
  by_cases hs : V (rbp + BitVec.ofNat 64 (c - 1)) = 0x2f
  · have d2 : decide (V (rbp + BitVec.ofNat 64 (c - 1)) = 47#8) = true := decide_eq_true hs
    wpx [W_114, W_96, W_112, W_119, W_272, o7, o8, o9, o10, o16, Op.sxr, Op.cmpmi, e32, d1, ea, Tun.rd1, d2, ec, ed,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_implies, true_implies]
    all_goals first | exact hf | skip
    first
    | exact ⟨hf, fun _ => .inl ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩, fun h => absurd rfl h⟩
    | exact ⟨hf, .inl ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    | exact .inl ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    | skip
  · have d2 : decide (V (rbp + BitVec.ofNat 64 (c - 1)) = 47#8) = false := decide_eq_false hs
    wpx [W_114, W_96, W_112, W_119, W_272, o7, o8, o9, o10, o16, Op.sxr, Op.cmpmi, e32, d1, ea, Tun.rd1, d2, ec, ed,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_implies, true_implies]
    all_goals first | exact hf | skip
    first
    | exact ⟨hf, fun h => absurd h (by decide), fun _ => .inr ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    | exact ⟨hf, .inr ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩
    | exact .inr ⟨hs, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    | skip

/-- The loop at `ecx = 1`: no `/` after the first, `malloc (2)`. -/
theorem vc_114o {g : Gprs} {f : Rflags} {V : Addr → Byte} (hcx : g.rcx = BitVec.ofNat 64 1) :
    W_114 F Wl (fun j' g' _ V' => j' = 124 ∧ g'.rdi = BitVec.ofNat 64 2 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hcx
  subst hcx
  wpx [W_114, W_96, W_112, W_119, W_272, o7, o8, o9, o10, o16, Op.sxr, Op.cmpmi, BitVec.reduceSetWidth,
    BitVec.reduceOfNat, decide_true, Bool.not_true, Bool.false_eq_true, false_implies, true_implies]
  all_goals first | exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | exact ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | skip

/-- After `malloc (2)` returned `p ≠ 0`: `/` and a NUL stored at `p`, to the epilogue. -/
theorem vc_129 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hp : g.rax ≠ 0) (hw : ∀ i < 2, Foot Wl (Addr.add g.rax i)) :
    W_129 F Wl (fun j' g' _ V' => j' = 255 ∧ g'.r12 = g.rax ∧ Kp g g' ∧
      V' = Vst V g.rax (toBytesLE (BitVec.setWidth 16 47#32) 2)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp hw
  have dz : (rax &&& rax == 0) = false := by
    rw [BitVec.and_self]
    exact beq_eq_false_iff_ne.2 hp
  wpx [W_129, W_137, o11, o12, dz, Bool.false_eq_true, false_implies]
  all_goals first | exact ⟨hw, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | exact ⟨hw, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | skip

/-- After `malloc (k + 2)` returned `p ≠ 0`: the arguments of `mempcpy (p, rbp, k)`, `ebx = k`. -/
theorem vc_283 {g : Gprs} {f : Rflags} {V : Addr → Byte} {k : Nat} (hk : k < 2 ^ 31) (hp : g.rax ≠ 0)
    (hbx : g.rbx = BitVec.ofNat 64 k) :
    W_283 F Wl (fun j' g' _ V' => j' = 300 ∧ g'.rdi = g.rax ∧ g'.r12 = g.rax ∧ g'.rsi = g.rbp ∧
      g'.rdx = BitVec.ofNat 64 k ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp hbx
  subst hbx
  have dz : (rax &&& rax == 0) = false := by
    rw [BitVec.and_self]
    exact beq_eq_false_iff_ne.2 hp
  have e32 := sw32n (n := k) (by omega)
  have ex := sx32n (n := k) hk
  wpx [W_283, W_291, o11, o17, Op.sxr, dz, e32, ex, Bool.false_eq_true, false_implies]
  all_goals first | exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | skip

/-- After `mempcpy`: the NUL at its end `rax`, to the epilogue. -/
theorem vc_305 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 1, Foot Wl (Addr.add g.rax i)) :
    W_305 F Wl (fun j' g' _ V' => j' = 255 ∧ g' = g ∧ V' = Vst V g.rax (toBytesLE 0#8 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw
  wpx [W_305, o18]
  all_goals first | exact ⟨hw, rfl⟩ | exact ⟨hw, rfl, rfl⟩ | exact hw | skip

/-- `_dl_origin_path` null: to 248. -/
theorem vc_152 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hf : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i))
    (hz : rdq(V, 8029440#64) = 0#64) :
    W_152 F Wl (fun j' g' _ V' => j' = 248 ∧ g' = { g with rbp := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_152, o13, Op.lda, hz, BitVec.and_self, BitVec.reduceAnd, BitVec.reduceBEq, beq_self_eq_true,
    Bool.true_eq_false, false_implies, true_implies]
  all_goals first | exact ⟨hf, rfl⟩ | exact hf | rfl | skip

/-- The way of the errors: `r12 = -1`. -/
theorem vc_248 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_248 F Wl (fun j' g' _ V' => j' = 255 ∧ g' = { g with r12 := 18446744073709551615#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_248, o14]
  all_goals first | rfl | skip

/-- The epilogue: `rax = r12`, the four registers back from the frame, to the `ret`. -/
theorem vc_255 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hf : ∀ i < 32, Foot F.data (Addr.add (g.rsp + 4104#64) i)) :
    W_255 F Wl (fun j' g' _ V' => j' = 271 ∧ g'.rax = g.r12 ∧ g'.rsp = g.rsp + 4104#64 + 8 + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp + 4104#64) ∧ g'.rbp = rdq(V, g.rsp + 4104#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 4104#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 4104#64 + 8 + 8 + 8) ∧
      g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf
  have slot : ∀ (a : Addr) (k : Nat), k < 32 → a = Addr.add (rsp + 4104#64) k → Foot F.data a :=
    fun a k hk ha => ha ▸ hf k hk
  wpx [W_255, o15, Op.pop]
  refine ⟨fun i hi => slot _ i (by omega) ?_, fun i hi => slot _ (8 + i) (by omega) ?_,
    fun i hi => slot _ (16 + i) (by omega) ?_, fun i hi => slot _ (24 + i) (by omega) ?_, ?_⟩
  all_goals first | (simp only [Addr.add]; bv_omega) | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | skip

end FV7z.Gor
