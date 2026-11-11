import FV7z.Tun.Cuts
/-!
# The call of `__tunables_init`, and the invariants of its cut points (PLAN.md G3, startup)

`Ctx`: what stays the same through a call: where the frame lies and the registers the prologue saves there, the
environment's array and strings, the tunables' aliases, and the bytes of memory at the call (`V0`). `Ctx.Ok`: what
the contract's precondition gives of them, in terms of bytes: the strings as functions from an index to a byte, with
a 0 at their length. `Mem K V`: the footprint's bytes `V` are those at the call outside the frame, and the frame
holds the saved registers. `Env`: what may be read and written.

The invariants: `P0` at the entry; `I57` at the head of the loop over the environment (`i`, the string's index);
`I104` scanning the `i`-th string for `=` (`j`); `I1205`, `I128` with the `=` found; `I203` comparing the string
with `GLIBC_TUNABLES` (`j`); `I210`, `I232` at the head of the loop over the tunables (`t`); `I292` comparing the
string with the `t`-th tunable's alias (`m`); `I352` at the alias's end; `I304`, `I318` going on to the next tunable
and string; `I330` before the epilogue. The measure: `B` for each string left, `C` for each tunable left, and within
them what is left of the string.
-/
namespace FV7z.Tun
open ZellicX86 Decode FV7z FV7z.Leaf

/-- The 8, 4 bytes of `V` at `a`. -/
notation "rdq(" V ", " a ")" => ofBytesLE 64 (List.map V (byteAddrs a 8))
notation "rdd(" V ", " a ")" => ofBytesLE 32 (List.map V (byteAddrs a 4))

/-- `GLIBC_TUNABLES` with its 0, by index. -/
def gz (k : Nat) : Byte := [0x47, 0x4c, 0x49, 0x42, 0x43, 0x5f, 0x54, 0x55, 0x4e, 0x41, 0x42, 0x4c, 0x45, 0x53].getD k 0

/-- What stays the same through a call. -/
structure Ctx where
  /-- `rsp` after the prologue: the frame's 104 bytes. -/
  sp : Addr
  /-- The registers the prologue saves. -/
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  /-- The environment: its array, the number of its strings, their addresses, bytes (with a 0 at the length) and
  lengths, and a bound of the lengths. -/
  envp : Addr
  N : Nat
  ptr : Nat → Addr
  ez : Nat → Nat → Byte
  len : Nat → Nat
  lmax : Nat
  /-- The tunables' aliases: their addresses (0 without one), bytes and lengths. -/
  aq : Nat → Addr
  az : Nat → Nat → Byte
  alen : Nat → Nat
  /-- The measure's units: for a string of the environment, for a tunable. -/
  B : Nat
  C : Nat
  /-- The bytes at the call. -/
  V0 : Addr → Byte

/-- A byte of the frame. -/
def InFr (K : Ctx) (a : Addr) : Prop := K.sp.toNat ≤ a.toNat ∧ a.toNat < K.sp.toNat + 104

/-- `n` bytes at `a` apart from the frame. -/
def Off (K : Ctx) (a : Nat) (n : Nat) : Prop := K.sp.toNat + 104 ≤ a ∨ a + n ≤ K.sp.toNat

/-- What the precondition gives. -/
structure Ctx.Ok (K : Ctx) : Prop where
  hsp : K.sp.toNat + 112 ≤ 2 ^ 64
  hC : K.C = K.lmax + 10
  hB : K.B = 26 * K.C + 30 + K.lmax
  /-- `__libc_enable_secure` is 0. -/
  hsec : rdd(K.V0, 0x791ce0#64) = 0
  aSec : Off K 0x791ce0 4
  /-- `GLIBC_TUNABLES`. -/
  hG : ∀ k : Nat, k < 15 → K.V0 (Addr.add 0x6f32b3#64 k) = gz k
  aG : Off K 0x6f32b3 15
  /-- The environment's array. -/
  hfit : K.envp.toNat + 8 * (K.N + 1) ≤ 2 ^ 64
  aEnv : Off K K.envp.toNat (8 * (K.N + 1))
  henv : ∀ i : Nat, i < K.N → rdq(K.V0, K.envp.add (8 * i)) = K.ptr i
  hend : rdq(K.V0, K.envp.add (8 * K.N)) = 0
  hnz : ∀ i : Nat, i < K.N → K.ptr i ≠ 0
  /-- The environment's strings. -/
  sfit : ∀ i : Nat, i < K.N → (K.ptr i).toNat + K.len i + 1 ≤ 2 ^ 64
  aStr : ∀ i : Nat, i < K.N → Off K (K.ptr i).toNat (K.len i + 1)
  hstr : ∀ i : Nat, i < K.N → ∀ k : Nat, k ≤ K.len i → K.V0 ((K.ptr i).add k) = K.ez i k
  hz : ∀ i : Nat, i < K.N → K.ez i (K.len i) = 0
  hlen : ∀ i : Nat, i < K.N → K.len i ≤ K.lmax
  /-- The list of tunables: the aliases' pointers. -/
  aList : Off K 0x791660 1456
  hal : ∀ t : Nat, t < 26 → rdq(K.V0, BitVec.ofNat 64 (0x791690 + 56 * t)) = K.aq t
  /-- The aliases' strings. -/
  afit : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → (K.aq t).toNat + K.alen t + 1 ≤ 2 ^ 64
  aAl : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → Off K (K.aq t).toNat (K.alen t + 1)
  hastr : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ k : Nat, k ≤ K.alen t → K.V0 ((K.aq t).add k) = K.az t k
  haz : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → K.az t (K.alen t) = 0
  hanz : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ k : Nat, k < K.alen t → K.az t k ≠ 0
  /-- No string of the environment begins with `GLIBC_TUNABLES=` or an alias and `=`. -/
  noG : ∀ i : Nat, i < K.N → (∀ k : Nat, k < 14 → K.ez i k = gz k) → K.ez i 14 ≠ 61
  noA : ∀ i : Nat, i < K.N → ∀ t : Nat, t < 26 → K.aq t ≠ 0 → (∀ k : Nat, k < K.alen t → K.ez i k = K.az t k) →
    K.ez i (K.alen t) ≠ 61

/-- What may be read and written. -/
structure Env (K : Ctx) (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  fr : ∀ y : Addr, K.sp.toNat ≤ y.toNat → y.toNat < K.sp.toNat + 104 → Foot Wl y
  sec : ∀ y : Addr, 0x791ce0 ≤ y.toNat → y.toNat < 0x791ce0 + 4 → Foot F.data y
  nm : ∀ y : Addr, 0x6f32b3 ≤ y.toNat → y.toNat < 0x6f32b3 + 15 → Foot F.data y
  lst : ∀ y : Addr, 0x791660 ≤ y.toNat → y.toNat < 0x791660 + 1456 → Foot F.data y
  env : ∀ y : Addr, K.envp.toNat ≤ y.toNat → y.toNat < K.envp.toNat + 8 * (K.N + 1) → Foot F.data y
  str : ∀ i : Nat, i < K.N → ∀ y : Addr, (K.ptr i).toNat ≤ y.toNat → y.toNat < (K.ptr i).toNat + K.len i + 1 →
    Foot F.data y
  al : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ y : Addr, (K.aq t).toNat ≤ y.toNat →
    y.toNat < (K.aq t).toNat + K.alen t + 1 → Foot F.data y

/-- What the footprint's bytes keep through the call, after the prologue: outside the frame the bytes at the call,
in the frame the saved registers. -/
structure Mem (K : Ctx) (V : Addr → Byte) : Prop where
  out : ∀ a, ¬ InFr K a → V a = K.V0 a
  v0 : rdq(V, K.sp + 56#64) = K.rbx
  v1 : rdq(V, K.sp + 64#64) = K.rbp
  v2 : rdq(V, K.sp + 72#64) = K.r12
  v3 : rdq(V, K.sp + 80#64) = K.r13
  v4 : rdq(V, K.sp + 88#64) = K.r14
  v5 : rdq(V, K.sp + 96#64) = K.r15

variable {K : Ctx} {V : Addr → Byte}

/-! ## Loads -/

/-- A load apart from a store. -/
theorem rd_Vst (V : Addr → Byte) (a : Addr) (bs : List Byte) (x : Addr) (n : Nat)
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64)
    (h : a.toNat + bs.length ≤ x.toNat ∨ x.toNat + n ≤ a.toNat) :
    List.map (Vst V a bs) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  apply Vst_apart
  intro i hi e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hj hx, toNat_add_of_fits hi ha] at this
  omega

/-- A load of what a store stored. -/
theorem rd_Vst_self (V : Addr → Byte) (a : Addr) (bs : List Byte) {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) : List.map (Vst V a bs) (byteAddrs a n) = bs := by
  subst hn; exact Vst_self bs V a ha

/-- A byte outside what a store stored. -/
theorem Vst_out (V : Addr → Byte) (a : Addr) (bs : List Byte) (x : Addr) (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (h : x.toNat < a.toNat ∨ a.toNat + bs.length ≤ x.toNat) : Vst V a bs x = V x := by
  apply Vst_apart
  intro i hi e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hi ha] at this
  omega

/-- The byte of a one-byte load. -/
theorem rd1 (V : Addr → Byte) (a : Addr) : ofBytesLE 8 (List.map V (byteAddrs a 1)) = V a := by
  simp [byteAddrs, ofBytesLE]

/-- `n` bytes apart from the frame are those at the call. -/
theorem Mem.rd (hM : Mem K V) {a : Addr} {n : Nat} (hf : a.toNat + n ≤ 2 ^ 64) (h : Off K a.toNat n) :
    List.map V (byteAddrs a n) = List.map K.V0 (byteAddrs a n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  apply hM.out
  have e := toNat_add_of_fits hj hf
  simp only [InFr, Off] at h ⊢
  omega

/-- A byte apart from the frame is the one at the call. -/
theorem Mem.rd1 (hM : Mem K V) {a : Addr} {b : Nat} {n k : Nat} (h : Off K b n)
    (ha : a.toNat = b + k) (hk : k < n) : V a = K.V0 a := by
  apply hM.out
  simp only [InFr, Off] at h ⊢
  omega

/-- A store into the frame below the saved registers keeps `Mem`. -/
theorem Mem.st (hM : Mem K V) (hK : K.Ok) {a : Addr} {bs : List Byte} (c : Nat) (ha : a.toNat = K.sp.toNat + c)
    (hc : c + bs.length ≤ 56) : Mem K (Vst V a bs) := by
  have hsp := hK.hsp
  have r : ∀ d, 56 ≤ d → d + 8 ≤ 104 → List.map (Vst V a bs) (byteAddrs (K.sp + BitVec.ofNat 64 d) 8) =
      List.map V (byteAddrs (K.sp + BitVec.ofNat 64 d) 8) := by
    intro d h1 h2
    exact rd_Vst _ _ _ _ _ (by omega) (by bv_omega) (by bv_omega)
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Vst_out _ _ _ _ (by omega) (by simp only [InFr] at hx; omega)]
    exact hM.out x hx
  · rw [r 56 (by omega) (by omega)]; exact hM.v0
  · rw [r 64 (by omega) (by omega)]; exact hM.v1
  · rw [r 72 (by omega) (by omega)]; exact hM.v2
  · rw [r 80 (by omega) (by omega)]; exact hM.v3
  · rw [r 88 (by omega) (by omega)]; exact hM.v4
  · rw [r 96 (by omega) (by omega)]; exact hM.v5

/-! ## Widths of a byte -/

theorem sw_8_32_8 (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_8_64_8 (x : BitVec 8) : (x.setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp
theorem sw_8_32_64_8 (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The measure -/

theorem mul_step {N i B : Nat} (h : i < N) : (N - i) * B = (N - (i + 1)) * B + B := by
  rw [show N - i = (N - (i + 1)) + 1 by omega, Nat.succ_mul]

/-! ## The invariants -/

/-- At the entry. -/
def P0 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 104#64 ∧ g.rdi = K.envp ∧ g.rbx = K.rbx ∧ g.rbp = K.rbp ∧ g.r12 = K.r12 ∧ g.r13 = K.r13 ∧
    g.r14 = K.r14 ∧ g.r15 = K.r15 ∧ V = K.V0 ∧ n = K.N * K.B + K.B + 1

/-- At the head of the loop over the environment. -/
def I57 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp ∧ Mem K V ∧ ∃ i, i ≤ K.N ∧ g.r13 = K.envp.add (8 * i) ∧ n = (K.N - i) * K.B + K.B

/-- In the `i`-th string: `rbx` the string, `r15` the array's next slot, `y` what is left of the string's unit. -/
def Str (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (i y : Nat) : Prop :=
  g.rsp = K.sp ∧ Mem K V ∧ i < K.N ∧ g.rbx = K.ptr i ∧ g.r15 = K.envp.add (8 * (i + 1)) ∧ n = (K.N - i) * K.B + y

/-- Scanning for `=`. -/
def I104 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i j, Str K n g V i (26 * K.C + 23 + (K.lmax + 1 - j)) ∧ g.rax = BitVec.ofNat 64 j ∧ 1 ≤ j ∧ j ≤ K.len i

/-- The string's first byte is `=` or 0. -/
def I1205 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i, Str K n g V i (26 * K.C + 22)

/-- The scan's end. -/
def I128 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i, Str K n g V i (26 * K.C + 21)

/-- Comparing with `GLIBC_TUNABLES`. -/
def I203 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i j, Str K n g V i (26 * K.C + 20 - j) ∧ j ≤ 13 ∧ g.rax = (K.ptr i).add j ∧ g.rsi = Addr.add 0x6f32b3#64 j ∧
    g.rdx.setWidth 8 = gz j ∧ (∀ k : Nat, k < j → K.ez i k = gz k) ∧ j ≤ K.len i

/-- Before the tunables. -/
def I210 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i, Str K n g V i (26 * K.C + 3)

/-- At the `t`-th tunable: `r8` its `initialized`, `r9` its index. -/
def Tn (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (i t y : Nat) : Prop :=
  Str K n g V i ((25 - t) * K.C + y) ∧ t < 26 ∧ g.r8 = BitVec.ofNat 64 (0x791688 + 56 * t) ∧
    g.r9 = BitVec.ofNat 64 t

/-- At the head of the loop over the tunables. -/
def I232 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i t, Tn K n g V i t (K.C + 2)

/-- Comparing with the `t`-th tunable's alias. -/
def I292 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i t m, Tn K n g V i t (K.C - m) ∧ K.aq t ≠ 0 ∧ g.rax = (K.ptr i).add m ∧ g.rsi = (K.aq t).add m ∧
    g.rcx.setWidth 8 = K.az t m ∧ m < K.alen t ∧ (∀ k : Nat, k < m → K.ez i k = K.az t k) ∧ m ≤ K.len i

/-- At the alias's end. -/
def I352 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i t, Tn K n g V i t 5 ∧ K.aq t ≠ 0 ∧ g.rax = (K.ptr i).add (K.alen t) ∧
    (∀ k : Nat, k < K.alen t → K.ez i k = K.az t k) ∧ K.alen t ≤ K.len i

/-- To the next tunable. -/
def I304 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ i t, Tn K n g V i t 4

/-- To the next string. -/
def I318 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp ∧ Mem K V ∧ ∃ i, i < K.N ∧ g.r15 = K.envp.add (8 * (i + 1)) ∧ n = (K.N - i) * K.B + 1

/-- Before the epilogue. -/
def I330 (K : Ctx) (_ : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp ∧ Mem K V

/-- At the `ret`: the registers a call keeps, and the bytes outside the frame as at the call. -/
def Ret (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sp + 104#64 ∧ g.rbx = K.rbx ∧ g.rbp = K.rbp ∧ g.r12 = K.r12 ∧ g.r13 = K.r13 ∧ g.r14 = K.r14 ∧
    g.r15 = K.r15 ∧ ∀ a, ¬ InFr K a → V a = K.V0 a

/-- The invariant at each cut point. -/
def InvT (K : Ctx) (ℓ : Nat) : Nat → Gprs → (Addr → Byte) → Prop :=
  if ℓ = 0 then P0 K else
  if ℓ = 57 then I57 K else
  if ℓ = 104 then I104 K else
  if ℓ = 128 then I128 K else
  if ℓ = 203 then I203 K else
  if ℓ = 210 then I210 K else
  if ℓ = 232 then I232 K else
  if ℓ = 292 then I292 K else
  if ℓ = 304 then I304 K else
  if ℓ = 318 then I318 K else
  if ℓ = 330 then I330 K else
  if ℓ = 352 then I352 K else
  if ℓ = 1205 then I1205 K else
  fun _ _ _ => False

/-- At an exit: the invariant with a smaller measure, or the `ret`. -/
def Nx (K : Ctx) (n : Nat) : Post := fun j' g' _ V' =>
  (∃ n', n' < n ∧ InvT K j' n' g' V') ∨ (j' = 344 ∧ Ret K g' V')

theorem nx {n n' j : Nat} {g : Gprs} {fl : Rflags} {V : Addr → Byte} (hn : n' < n) (h : InvT K j n' g V) :
    Nx K n j g fl V := Or.inl ⟨n', hn, h⟩

end FV7z.Tun
