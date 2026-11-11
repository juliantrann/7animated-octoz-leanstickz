import FV7z.Lzma.VcExit
/-!
# The verification conditions of the prologue (PLAN.md G2.2)

0: the call. The prologue saves six registers, takes the frame, copies the `CLzmaDec`'s fields into it (the masks of
`lp` and `pb`, `lc + 1`, the four `reps`, the pointers and sizes) and reads the range coder's state. `In`: what the
caller gives of the `CLzmaDec`; `Pre`: the registers at the call. 211: the first symbol's slot, by the state.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

/-! ## Loads from the `CLzmaDec` after stores into the frame -/

theorem rd_p_fr (hK : K.Ok) (V : Addr → Byte) {a x : Addr} {bs : List Byte} {n : Nat}
    (ha : K.sp.toNat ≤ a.toNat ∧ a.toNat + bs.length ≤ K.sq.toNat + 48)
    (hx : K.p.toNat ≤ x.toNat ∧ x.toNat + n ≤ K.p.toNat + 95) :
    List.map (Vst V a bs) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have := hK.hsq; have := hK.hp; have := hK.aFp
  exact rd_Vst _ _ _ _ _ (by omega) (by omega) (by omega)

theorem rd_p_sp (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128)
    (h2 : c + n ≤ 95) : List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.p + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.p + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p_sp0 (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h1 : bs.length ≤ 128)
    (h2 : c + n ≤ 95) : List.map (Vst V K.sp bs) (byteAddrs (K.p + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.p + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p_sq (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 48)
    (h2 : c + n ≤ 95) : List.map (Vst V (K.sq + BitVec.ofNat 64 c') bs) (byteAddrs (K.p + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.p + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p_sq0 (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h1 : bs.length ≤ 48)
    (h2 : c + n ≤ 95) : List.map (Vst V K.sq bs) (byteAddrs (K.p + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.p + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p0_sp (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128)
    (h2 : n ≤ 95) : List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs K.p n) = List.map V (byteAddrs K.p n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p0_sp0 (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (h1 : bs.length ≤ 128)
    (h2 : n ≤ 95) : List.map (Vst V K.sp bs) (byteAddrs K.p n) = List.map V (byteAddrs K.p n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p0_sq (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 48)
    (h2 : n ≤ 95) : List.map (Vst V (K.sq + BitVec.ofNat 64 c') bs) (byteAddrs K.p n) = List.map V (byteAddrs K.p n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem rd_p0_sq0 (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (h1 : bs.length ≤ 48)
    (h2 : n ≤ 95) : List.map (Vst V K.sq bs) (byteAddrs K.p n) = List.map V (byteAddrs K.p n) := by
  have := hK.hsq; have := hK.hp; have := hK.hsp2
  exact rd_p_fr hK V (by constructor <;> bv_omega) (by constructor <;> bv_omega)

theorem ite_mk7 (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 b7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 64) :
    (if c then (⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ : Gprs)
      else ⟨a0, a1, a2, a3, a4, a5, a6, b7, a8, a9, a10, a11, a12, a13, a14, a15⟩) =
      ⟨a0, a1, a2, a3, a4, a5, a6, if c then a7 else b7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := by
  split <;> rfl

/-! ## A byte into a register -/

theorem lo8 (x : BitVec 64) (b : BitVec 8) :
    BitVec.setWidth 8 (x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| BitVec.setWidth 64 b <<< 0) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, BitVec.shiftLeft_zero, Nat.or_mod_two_pow,
    Nat.and_mod_two_pow]
  have e : (~~~BitVec.ofNat 64 ((256 - 1) * 1)).toNat % 2 ^ 8 = 0 := by decide
  rw [e, Nat.and_zero, Nat.zero_or]
  omega
theorem lo8' (x : BitVec 64) (b : BitVec 8) :
    (BitVec.setWidth 32 (x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| BitVec.setWidth 64 b <<< 0)).toNat % 256 =
      b.toNat := by
  have h := congrArg BitVec.toNat (lo8 x b)
  generalize x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| BitVec.setWidth 64 b <<< 0 = y at h ⊢
  bv_omega
/-! ## The call, and 211 -/

theorem lo8x (x : BitVec 64) (b : BitVec 8) :
    (BitVec.setWidth 32 (x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| BitVec.setWidth 64 b <<< 0)).toNat % 32 =
      b.toNat % 32 := by
  have := lo8' x b
  omega

/-- The `CLzmaDec` at the call: the properties' three bytes with the masks they give, the pointers and sizes, a
range of at least `2^24`, a state below 12, `reps` no larger than the dictionary's buffer, `buf` at most `bufLimit`,
`dicPos` below `limit`, `processedPos` within its bound; the probabilities in `[31, 2017]`. -/
structure In (K : Ctx) (V : Addr → Byte) : Prop where
  sp : K.sq + 18446744073709551488#64 &&& 18446744073709551488#64 = K.sp
  lc : (ofBytesLE 8 (List.map V (byteAddrs K.p 1))).toNat = K.lc
  lpm : 256#32 <<< ((ofBytesLE 8 (List.map V (byteAddrs (K.p + 1#64) 1))).toNat % 32) -
    256#32 >>> ((ofBytesLE 8 (List.map V (byteAddrs K.p 1))).toNat % 32) = K.lpm
  pbm : 1#32 <<< ((ofBytesLE 8 (List.map V (byteAddrs (K.p + 2#64) 1))).toNat % 32) - 1 = K.pbm
  P : rdq(V, K.p + 16#64) = K.P
  dic : rdq(V, K.p + 24#64) = K.dic
  dbs : rdq(V, K.p + 32#64) = BitVec.ofNat 64 K.dbs
  dp0 : rdq(V, K.p + 40#64) = BitVec.ofNat 64 K.dp0
  dpl : K.dp0 < K.lim
  b0 : K.b0 ≤ (rdq(V, K.p + 48#64)).toNat
  bl : (rdq(V, K.p + 48#64)).toNat ≤ K.bl.toNat
  rng : 2 ^ 24 ≤ (rdd(V, K.p + 56#64)).toNat
  pp : K.ckd.toNat = 0 → (rdd(V, K.p + 64#64)).toNat + (K.lim - K.dp0) ≤ K.ppb
  ckd : rdd(V, K.p + 68#64) = K.ckd
  r0 : (rdd(V, K.p + 72#64)).toNat ≤ K.dbs
  r1 : (rdd(V, K.p + 76#64)).toNat ≤ K.dbs
  r2 : (rdd(V, K.p + 80#64)).toNat ≤ K.dbs
  r3 : (rdd(V, K.p + 84#64)).toNat ≤ K.dbs
  st : (rdd(V, K.p + 88#64)).toNat < 12
  pr : ∀ a, InPr K a → Pv ((rdw(V, a)).setWidth 32)

/-- 0, the call: `rsp` at the return address, the `CLzmaDec` in `rdi`, `limit` in `rsi`, `bufLimit` in `rdx`. -/
def Pre (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sq + 48#64 ∧ g.rdi = K.p ∧ g.rsi = BitVec.ofNat 64 K.lim ∧ g.rdx = K.bl ∧ g.r15 = K.sv 0 ∧
    g.r14 = K.sv 1 ∧ g.r13 = K.sv 2 ∧ g.r12 = K.sv 3 ∧ g.rbp = K.sv 4 ∧ g.rbx = K.sv 5 ∧ In K V ∧
    n = 2 ^ 20 * (K.lim - K.dp0) + 10000

/-- 211: after the prologue. -/
def Pro211 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ pp : BitVec 32, g.rsp = K.sp ∧ g.r10 = 2048#64 ∧ Mem K V ∧ g.r13 = pp.setWidth 64 ∧
    (K.ckd.toNat = 0 → pp.toNat + (K.lim - K.dp0) ≤ K.ppb) ∧ K.dp0 < K.lim ∧
    g.r14 = K.dic + BitVec.ofNat 64 K.dp0 ∧ St g.r8 0 24 ∧ g.r11 = K.P ∧ g.r12 = K.dic ∧
    g.r9.setWidth 32 = K.lpm ∧ RcU K 0 0 g.rax g.r15 ∧ n = 2 ^ 20 * (K.lim - K.dp0) + 9500

/-- A load from the frame past a store to another slot of it. -/
macro "rdt" : tactic =>
  `(tactic| (rw [rd_Vst]; rotate_left; (rw [toBytesLE_length]; bv_omega); bv_omega; (rw [toBytesLE_length]; bv_omega)))

/-! ## Loads from the frame after stores into the frame: the slots by their offsets -/

theorem rd_sp_sp (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128) (h2 : c + n ≤ 128)
    (h : c' + bs.length ≤ c ∨ c + n ≤ c') :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp_sp0 (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128) (h : n ≤ c') :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs K.sp n) = List.map V (byteAddrs K.sp n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp0_sp (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h2 : c + n ≤ 128) (h : bs.length ≤ c) :
    List.map (Vst V K.sp bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp_sq (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128) (h2 : c + n ≤ 48) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.sq + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sq + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp_sq0 (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 128) (h2 : n ≤ 48) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs K.sq n) = List.map V (byteAddrs K.sq n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp0_sq (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h1 : bs.length ≤ 128) (h2 : c + n ≤ 48) :
    List.map (Vst V K.sp bs) (byteAddrs (K.sq + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sq + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp0_sq0 (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (h1 : bs.length ≤ 128) (h2 : n ≤ 48) :
    List.map (Vst V K.sp bs) (byteAddrs K.sq n) = List.map V (byteAddrs K.sq n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sq_sq (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 48) (h2 : c + n ≤ 48)
    (h : c' + bs.length ≤ c ∨ c + n ≤ c') :
    List.map (Vst V (K.sq + BitVec.ofNat 64 c') bs) (byteAddrs (K.sq + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sq + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sq_sq0 (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 48) (h : n ≤ c') :
    List.map (Vst V (K.sq + BitVec.ofNat 64 c') bs) (byteAddrs K.sq n) = List.map V (byteAddrs K.sq n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sq0_sq (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h2 : c + n ≤ 48) (h : bs.length ≤ c) :
    List.map (Vst V K.sq bs) (byteAddrs (K.sq + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.sq + BitVec.ofNat 64 c) n) := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sp_self (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (hn : bs.length = n) (h : c + n ≤ 128) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c) bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) = bs := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst_self _ _ _ hn (by bv_omega)

theorem rd_sp0_self (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (hn : bs.length = n) (h : n ≤ 128) :
    List.map (Vst V K.sp bs) (byteAddrs K.sp n) = bs := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst_self _ _ _ hn (by bv_omega)

theorem rd_sq_self (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (hn : bs.length = n) (h : c + n ≤ 48) :
    List.map (Vst V (K.sq + BitVec.ofNat 64 c) bs) (byteAddrs (K.sq + BitVec.ofNat 64 c) n) = bs := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst_self _ _ _ hn (by bv_omega)

theorem rd_sq0_self (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (hn : bs.length = n) (h : n ≤ 48) :
    List.map (Vst V K.sq bs) (byteAddrs K.sq n) = bs := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2
  exact rd_Vst_self _ _ _ hn (by bv_omega)

/-- A slot of the frame after the prologue: the value stored there. -/
macro "slotv" h:term : tactic => `(tactic| simp only [rd_sp_sp $h, rd_sp_sp0 $h, rd_sp0_sp $h, rd_sp_sq $h, rd_sp_sq0 $h,
  rd_sp0_sq $h, rd_sp0_sq0 $h, rd_sq_sq $h, rd_sq_sq0 $h, rd_sq0_sq $h, rd_sp_self $h, rd_sp0_self $h, rd_sq_self $h,
  rd_sq0_self $h, toBytesLE_length, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff, Nat.reduceEqDiff, true_or, or_true,
  ofBytesLE_toBytesLE])

set_option maxHeartbeats 4000000 in
theorem vc_0 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Pre K n g V)
    (hq : ∀ n' g' fl V', n' < n → Pro211 K n' g' V' → Q 211 g' fl V') :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI, rfl⟩ := h
  have e1 : K.sq + 48#64 - 8 = K.sq + 40#64 := by bv_omega
  have e2 : K.sq + 40#64 - 8 = K.sq + 32#64 := by bv_omega
  have e3 : K.sq + 32#64 - 8 = K.sq + 24#64 := by bv_omega
  have e4 : K.sq + 24#64 - 8 = K.sq + 16#64 := by bv_omega
  have e5 : K.sq + 16#64 - 8 = K.sq + 8#64 := by bv_omega
  have e6 : K.sq + 8#64 - 8 = K.sq := by bv_omega
  wpx [W_0, o0, W_197, o1, BitVec.reduceSetWidth, e1, e2, e3, e4, e5, e6, hI.sp, rd_p_sp hK, rd_p_sp0 hK, rd_p_sq hK,
    rd_p_sq0 hK, rd_p0_sp hK, rd_p0_sp0 hK, rd_p0_sq hK, rd_p0_sq0 hK, Nat.reduceAdd, Nat.reduceLeDiff, ite_mk7]
  simp only [lo8, hI.P, hI.dic, hI.dbs, hI.dp0, hI.ckd, hI.lpm, hI.pbm, BitVec.xor_self]
  clear e1 e2 e3 e4 e5 e6
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have hp := hK.hp
  generalize hV : Vst _ (K.sp + 92#64) _ = V'
  have hM : Mem K V' := by
    have a2 : K.sq + 8#64 + 8#64 = K.sq + 16#64 := by bv_omega
    have a3 : K.sq + 16#64 + 8#64 = K.sq + 24#64 := by bv_omega
    have a4 : K.sq + 24#64 + 8#64 = K.sq + 32#64 := by bv_omega
    have a5 : K.sq + 32#64 + 8#64 = K.sq + 40#64 := by bv_omega
    have hnp := hK.hnp; have := hK.aFP
    subst hV
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · slotv hK
    · slotv hK
    · slotv hK
    · slotv hK
    · slotv hK
    · slotv hK; exact BitVec.add_comm _ _
    · slotv hK
    · slotv hK
      rw [lo8x]
      have h2 := hI.lc; have h3 := hK.hlc
      bv_omega
    · slotv hK
    · slotv hK
    · slotv hK
    · slotv hK
    · slotv hK
    · rw [a2]; slotv hK
    · rw [a2, a3]; slotv hK
    · rw [a2, a3, a4]; slotv hK
    · rw [a2, a3, a4, a5]; slotv hK
    · intro a ⟨i, hi, hai⟩
      repeat rdt
      exact hI.pr a ⟨i, hi, hai⟩
    · slotv hK; exact hI.r0
    · slotv hK; exact hI.r1
    · slotv hK; exact hI.r2
    · slotv hK; exact hI.r3
  have fq : ∀ (c n : Nat) (a : Addr), a.toNat = K.sq.toNat + c → c + n ≤ 48 → ∀ i, i < n → Foot Wl (a.add i) := by
    intro c n a ha hc i hi
    have e := toNat_add_of_fits (a := a) hi (by omega)
    exact hE.fr _ (by omega) (by omega)
  have fp : ∀ (c n : Nat) (a : Addr), a.toNat = K.p.toNat + c → c + n ≤ 0x60 → ∀ i, i < n → Foot F.data (a.add i) := by
    intro c n a ha hc i hi
    have e := toNat_add_of_fits (a := a) hi (by omega)
    exact hE.prd _ (by omega) (by omega)
  have hex : ∀ (rcx' rdx' rbx' rbp' rdi' : BitVec 64) (fl : Rflags), Q 211 ⟨BitVec.setWidth 64 (rdd(V, K.p + 56#64)),
      rcx', rdx', rbx', K.sp, rbp', BitVec.ofNat 64 K.lim + K.dic, rdi',
      BitVec.setWidth 64 (rdd(V, K.p + 88#64) <<< 1), BitVec.setWidth 64 K.lpm, 2048#64, K.P, K.dic,
      BitVec.setWidth 64 (rdd(V, K.p + 64#64)), BitVec.ofNat 64 K.dp0 + K.dic, rdq(V, K.p + 48#64)⟩ fl V' := by
    intro rcx' rdx' rbx' rbp' rdi' fl
    have h8 := hI.st
    refine hq (2 ^ 20 * (K.lim - K.dp0) + 9500) _ _ _ (by omega) ⟨rdd(V, K.p + 64#64), rfl, rfl, hM, rfl, hI.pp, hI.dpl,
      BitVec.add_comm _ _, ⟨rdd(V, K.p + 88#64) <<< 1, rfl, by bv_omega, by omega, by bv_omega⟩, rfl, rfl, ?_,
      RcU.init hI.rng hI.b0 hI.bl, rfl⟩
    show BitVec.setWidth 32 (BitVec.setWidth 64 K.lpm) = K.lpm
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
  refine ⟨fq 40 8 _ (by bv_omega) (by omega), fq 32 8 _ (by bv_omega) (by omega), fq 24 8 _ (by bv_omega) (by omega),
    fq 16 8 _ (by bv_omega) (by omega), fq 8 8 _ (by bv_omega) (by omega), fq 0 8 _ (by bv_omega) (by omega),
    hE.wr_fr hK 0 (by bv_omega) (by omega), hE.wr_fr hK 8 (by bv_omega) (by omega),
    hE.wr_fr hK 100 (by bv_omega) (by omega), hE.wr_fr hK 72 (by bv_omega) (by omega),
    fp 24 8 _ (by bv_omega) (by omega), hE.wr_fr hK 64 (by bv_omega) (by omega),
    fp 72 4 _ (by bv_omega) (by omega), hE.wr_fr hK 112 (by bv_omega) (by omega),
    fp 76 4 _ (by bv_omega) (by omega), hE.wr_fr hK 116 (by bv_omega) (by omega),
    fp 80 4 _ (by bv_omega) (by omega), hE.wr_fr hK 120 (by bv_omega) (by omega),
    fp 84 4 _ (by bv_omega) (by omega), hE.wr_fr hK 124 (by bv_omega) (by omega),
    fp 40 8 _ (by bv_omega) (by omega), hE.wr_fr hK 104 (by bv_omega) (by omega),
    hE.wr_fr hK 56 (by bv_omega) (by omega), fp 2 1 _ (by bv_omega) (by omega), fun _ =>
    ⟨hE.wr_fr hK 88 (by bv_omega) (by omega), fp 0 1 _ (by bv_omega) (by omega), fun _ =>
    ⟨hE.wr_fr hK 80 (by bv_omega) (by omega), fp 1 1 _ (by bv_omega) (by omega), fun _ =>
    ⟨hE.wr_fr hK 84 (by bv_omega) (by omega), fp 16 8 _ (by bv_omega) (by omega),
    hE.wr_fr hK 48 (by bv_omega) (by omega), fp 32 8 _ (by bv_omega) (by omega),
    hE.wr_fr hK 40 (by bv_omega) (by omega), fp 68 4 _ (by bv_omega) (by omega),
    hE.wr_fr hK 92 (by bv_omega) (by omega), fp 64 4 _ (by bv_omega) (by omega),
    fp 88 4 _ (by bv_omega) (by omega), fun _ =>
    ⟨fp 48 8 _ (by bv_omega) (by omega), fp 56 4 _ (by bv_omega) (by omega), fp 60 4 _ (by bv_omega) (by omega),
    fun _ _ => ⟨fun _ => hex _ _ _ _ _ _, fun _ => ⟨?_, hex _ _ _ _ _ _⟩⟩⟩⟩⟩⟩⟩
  clear hex hM fq fp
  have hdl := hI.dpl; have := hK.hlim; have := hK.hdic
  split
  · rename_i hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hc
    exact hE.rd_dic hK (K.dp0 - 1) (by bv_omega) (by omega)
  · rename_i hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not] at hc
    exact hE.rd_dic hK (K.dbs - 1) (by bv_omega) (by omega)

theorem vc_211 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Pro211 K n g V)
    (hq1 : ∀ n' g' fl, n' < n → Sym K n' g' V 0 8 (g'.r9.setWidth 32 = K.lpm) → Q 1001 g' fl V)
    (hq2 : ∀ n' g' fl, n' < n → Sym K n' g' V 8 14 True → Q 3770 g' fl V)
    (hq3 : ∀ n' g' fl, n' < n → Sym K n' g' V 14 24 (g'.r12 = K.dic) → Q 2825 g' fl V) :
    W_211 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pro211, St] at h
  obtain ⟨pp, rfl, rfl, hMem, rfl, hpp, hdl, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, h9, hU, rfl⟩ := h
  wpx [W_211, o2, W_235, o3, W_245, BitVec.reduceSetWidth]
  simp only [hMem.s58]
  have := hK.hsq; have := hK.hsp2
  have hpx := px_of K.pbm pp hK.hpbm
  exact ⟨hE.rd_fr hK 88 (by bv_omega) (by omega), fun fl =>
    ⟨fun h1 => hq1 (2 ^ 20 * (K.lim - K.dp0) + 9000) _ _ (by omega) ⟨K.dp0, ⟨⟨rfl, rfl, hMem, Nat.le_refl _, hdl, pp, rfl,
      hpp⟩, rfl, ⟨s, rfl, hs2, hsl, of_decide_eq_true h1⟩, rfl, rfl, hpx⟩, hU, h9, rfl⟩,
    fun h1 => ⟨fun h2 => hq2 (2 ^ 20 * (K.lim - K.dp0) + 9000) _ _ (by omega) ⟨K.dp0, ⟨⟨rfl, rfl, hMem, Nat.le_refl _,
      hdl, pp, rfl, hpp⟩, rfl, ⟨s, rfl, hs2, Nat.le_of_not_lt (of_decide_eq_false h1), of_decide_eq_true h2⟩, rfl, rfl,
      hpx⟩, hU, trivial, rfl⟩,
    fun h2 => hq3 (2 ^ 20 * (K.lim - K.dp0) + 9000) _ _ (by omega) ⟨K.dp0, ⟨⟨rfl, rfl, hMem, Nat.le_refl _,
      hdl, pp, rfl, hpp⟩, rfl, ⟨s, rfl, hs2, Nat.le_of_not_lt (of_decide_eq_false h2), hsh⟩, rfl, rfl,
      hpx⟩, hU, rfl, rfl⟩⟩⟩⟩
end FV7z.Lzma
