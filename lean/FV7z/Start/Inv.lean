import FV7z.Start.Calls
/-!
# The start of `__libc_start_main`: what the launch gives, and the invariants (PLAN.md G3, startup)

From the entry to where `init_cpu_features` begins (offset 211): the prologue, `__libc_multiple_libcs`,
`_dl_relocate_static_pie`, `__environ` and `__libc_stack_end`, the scan of the environment to its end, `_dl_aux_init`
on the vector after it, the test of `_dl_phdr`, `__libc_init_secure` and `__tunables_init`.

`Ctx`: what stays the same: the stack (`bp`, 376 bytes below `rsp` at the entry: the 264 of the function's frame, the
return address of a call and a callee's 104), the arguments, the environment's array with the auxiliary vector after
it, the environment's strings, the tunables' aliases, and the bytes at the entry (`V0`). `Ctx.Ok`: what the launch has
to give of them; `Env`: what may be read and written. `Same K D V`: the bytes `V` are those at the entry outside the
stack and the variables `D` (`d3`: the three the function sets itself; then also `_dl_aux_init`'s).

The invariants: `I0` at the entry; `I65`, `I71` (the call of `_dl_relocate_static_pie`), `I76`; `I120` in the scan
(`i` pointers passed); `I131` at the call of `_dl_aux_init`; `I136`, `I194` (the call of `__libc_init_secure`), `I199`,
`I206` (the call of `__tunables_init`); `FinP` at offset 211.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.AuxInit (Vars step globals)
open FV7z.Auxv (Gl)

/-- The variables after the first `n` entries of a vector. -/
def vsOf (ty val : Nat → BitVec 64) (w : Vars) : Nat → Vars
  | 0 => w
  | n + 1 => step (vsOf ty val w n) (ty n, val n)

/-- What stays the same. -/
structure Ctx where
  /-- The stack's 376 bytes; `rsp` at the entry is `bp + 376`. -/
  bp : Addr
  /-- The arguments: `main`, `argc`, `argv`, `init`, `fini`, `rtld_fini`, and on the stack `stack_end`. -/
  main : BitVec 64
  argc : BitVec 32
  argv : Addr
  init : BitVec 64
  fini : BitVec 64
  rtld : BitVec 64
  stackEnd : BitVec 64
  /-- The environment's array, and the number of its strings. -/
  envp : Addr
  N : Nat
  /-- The auxiliary vector after it: the number of its entries, their types and values, an entry `AT_SECURE`; and
  `_dl_aux_init`'s variables at the entry. -/
  M : Nat
  ty : Nat → BitVec 64
  val : Nat → BitVec 64
  sn : Nat
  w0 : Vars
  /-- The environment's strings: addresses, bytes (with a 0 at the length), lengths and a bound of them. -/
  ptr : Nat → Addr
  ez : Nat → Nat → Byte
  len : Nat → Nat
  lmax : Nat
  /-- The tunables' aliases: their addresses (0 without one), bytes and lengths. -/
  aq : Nat → Addr
  az : Nat → Nat → Byte
  alen : Nat → Nat
  /-- The bytes at the entry. -/
  V0 : Addr → Byte

/-- The auxiliary vector's address. -/
def Ctx.av (K : Ctx) : Addr := K.envp.add (8 * (K.N + 1))
/-- `_dl_aux_init`'s variables after the vector's first `n` entries. -/
def Ctx.vs (K : Ctx) : Nat → Vars := vsOf K.ty K.val K.w0

/-- A byte of the stack. -/
def InStk (K : Ctx) (a : Addr) : Prop := K.bp.toNat ≤ a.toNat ∧ a.toNat < K.bp.toNat + 376

/-- A byte of a callee's frame or of the return address of its call. -/
def Low (K : Ctx) (a : Addr) : Prop := K.bp.toNat ≤ a.toNat ∧ a.toNat < K.bp.toNat + 112

/-- `__libc_multiple_libcs`, `__environ`, `__libc_stack_end`. -/
def d3 : List Rgn := [⟨0x7939c0, 4⟩, ⟨0x7a4798, 8⟩, ⟨0x791cb0, 8⟩]

/-- `n` bytes at `a` apart from the stack and from where the variables set here lie. -/
def Clean (K : Ctx) (a n : Nat) : Prop :=
  (K.bp.toNat + 376 ≤ a ∨ a + n ≤ K.bp.toNat) ∧ (a + n ≤ 0x791ca0 ∨ 0x7a85c8 ≤ a)

/-- What the launch gives: the stack, the arguments, the environment and the auxiliary vector. -/
structure Ctx.Lch (K : Ctx) : Prop where
  hbp : K.bp.toNat + 392 ≤ 2 ^ 64
  /-- The stack is apart from the image. -/
  himg : K.bp.toNat + 376 ≤ 0x400000 ∨ 0x7a9000 ≤ K.bp.toNat
  hse : rdq(K.V0, K.bp + 384#64) = K.stackEnd
  /-- The environment's array is after `argv`'s `argc` pointers and their null. -/
  henvp : K.argv + BitVec.signExtend 64 K.argc * 8#64 + 8#64 = K.envp
  /-- The environment's array and the vector. -/
  hfit : K.envp.toNat + (8 * (K.N + 1) + 16 * K.M + 8) ≤ 2 ^ 64
  cEnv : Clean K K.envp.toNat (8 * (K.N + 1) + 16 * K.M + 8)
  henv : ∀ i : Nat, i < K.N → rdq(K.V0, K.envp.add (8 * i)) = K.ptr i
  hend : rdq(K.V0, K.envp.add (8 * K.N)) = 0
  hnz : ∀ i : Nat, i < K.N → K.ptr i ≠ 0
  hty : ∀ n : Nat, n < K.M → rdq(K.V0, K.av.add (16 * n)) = K.ty n
  hval : ∀ n : Nat, n < K.M → rdq(K.V0, K.av.add (16 * n + 8)) = K.val n
  hnzT : ∀ n : Nat, n < K.M → K.ty n ≠ 0
  hendT : rdq(K.V0, K.av.add (16 * K.M)) = 0
  hsn : K.sn < K.M
  hsec : K.ty K.sn = 23
  /-- `AT_SECURE` is 0, and there is an `AT_PHDR`, not null. -/
  hsec0 : ∀ n : Nat, n < K.M → K.ty n = 23 → (K.val n).setWidth 32 = 0#32
  hph : ∃ n : Nat, n < K.M ∧ K.ty n = 3
  hph0 : ∀ n : Nat, n < K.M → K.ty n = 3 → K.val n ≠ 0
  /-- `_dl_aux_init`'s variables. -/
  hgl : Gl K.V0 K.w0
  /-- The environment's strings. -/
  sfit : ∀ i : Nat, i < K.N → (K.ptr i).toNat + K.len i + 1 ≤ 2 ^ 64
  cStr : ∀ i : Nat, i < K.N → Clean K (K.ptr i).toNat (K.len i + 1)
  hstr : ∀ i : Nat, i < K.N → ∀ k : Nat, k ≤ K.len i → K.V0 ((K.ptr i).add k) = K.ez i k
  hz : ∀ i : Nat, i < K.N → K.ez i (K.len i) = 0
  hlen : ∀ i : Nat, i < K.N → K.len i ≤ K.lmax
  /-- No string of the environment begins with `GLIBC_TUNABLES=` or an alias and `=`. -/
  noG : ∀ i : Nat, i < K.N → (∀ k : Nat, k < 14 → K.ez i k = gz k) → K.ez i 14 ≠ 61
  noA : ∀ i : Nat, i < K.N → ∀ t : Nat, t < 26 → K.aq t ≠ 0 → (∀ k : Nat, k < K.alen t → K.ez i k = K.az t k) →
    K.ez i (K.alen t) ≠ 61

/-- What the image gives (`Start/Image.lean`: these are the file's bytes). -/
structure Ctx.Im (K : Ctx) : Prop where
  /-- `_dl_aux_init`'s jump table. -/
  hjt : ∀ k : Nat, k < 31 → rdd(K.V0, Addr.add 0x6f3660#64 (4 * k)) = Auxv.jt k
  /-- `GLIBC_TUNABLES`. -/
  hG : ∀ k : Nat, k < 15 → K.V0 (Addr.add 0x6f32b3#64 k) = gz k
  /-- The list of tunables: the aliases' pointers, and the aliases' strings. -/
  hal : ∀ t : Nat, t < 26 → rdq(K.V0, BitVec.ofNat 64 (0x791690 + 56 * t)) = K.aq t
  afit : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → (K.aq t).toNat + K.alen t + 1 ≤ 2 ^ 64
  cAl : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → Clean K (K.aq t).toNat (K.alen t + 1)
  hastr : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ k : Nat, k ≤ K.alen t → K.V0 ((K.aq t).add k) = K.az t k
  haz : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → K.az t (K.alen t) = 0
  hanz : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ k : Nat, k < K.alen t → K.az t k ≠ 0

/-- What the launch and the image give. -/
structure Ctx.Ok (K : Ctx) : Prop extends K.Lch, K.Im

/-- What may be read and written. -/
structure Env (K : Ctx) (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  stk : ∀ y : Addr, K.bp.toNat ≤ y.toNat → y.toNat < K.bp.toNat + 376 → Foot Wl y
  arg : ∀ y : Addr, K.bp.toNat + 384 ≤ y.toNat → y.toNat < K.bp.toNat + 392 → Foot F.data y
  gl : ∀ r ∈ d3 ++ globals, ∀ y, r.Mem y → Foot Wl y
  tab : ∀ y : Addr, 0x6f3660 ≤ y.toNat → y.toNat < 0x6f3660 + 124 → Foot F.data y
  nm : ∀ y : Addr, 0x6f32b3 ≤ y.toNat → y.toNat < 0x6f32b3 + 15 → Foot F.data y
  lst : ∀ y : Addr, 0x791660 ≤ y.toNat → y.toNat < 0x791660 + 1456 → Foot F.data y
  env : ∀ y : Addr, K.envp.toNat ≤ y.toNat → y.toNat < K.envp.toNat + (8 * (K.N + 1) + 16 * K.M + 8) → Foot F.data y
  str : ∀ i : Nat, i < K.N → ∀ y : Addr, (K.ptr i).toNat ≤ y.toNat → y.toNat < (K.ptr i).toNat + K.len i + 1 →
    Foot F.data y
  al : ∀ t : Nat, t < 26 → K.aq t ≠ 0 → ∀ y : Addr, (K.aq t).toNat ≤ y.toNat →
    y.toNat < (K.aq t).toNat + K.alen t + 1 → Foot F.data y

/-- The bytes `V` are those at the entry outside the stack and the variables `D`. -/
def Same (K : Ctx) (D : List Rgn) (V : Addr → Byte) : Prop := ∀ a, ¬ InStk K a → ¬ Foot D a → V a = K.V0 a

/-- The frame's slots: `argv`, `main`, `argc`. -/
structure Fr (K : Ctx) (V : Addr → Byte) : Prop where
  argv : rdq(V, K.bp + 128#64) = K.argv
  main : rdq(V, K.bp + 136#64) = K.main
  argc : rdd(V, K.bp + 124#64) = K.argc

/-- The bytes before `_dl_aux_init`. -/
structure MA (K : Ctx) (V : Addr → Byte) : Prop where
  same : Same K d3 V
  fr : Fr K V
  mlibs : rdd(V, 0x7939c0#64) = 0
  env : rdq(V, 0x7a4798#64) = K.envp
  se : rdq(V, 0x791cb0#64) = K.stackEnd

/-- The bytes after `_dl_aux_init`. -/
structure MB (K : Ctx) (V : Addr → Byte) : Prop where
  same : Same K (d3 ++ globals) V
  fr : Fr K V
  mlibs : rdd(V, 0x7939c0#64) = 0
  env : rdq(V, 0x7a4798#64) = K.envp
  se : rdq(V, 0x791cb0#64) = K.stackEnd
  gl : Gl V (K.vs K.M)
  auxv : rdq(V, 0x7a8540#64) = K.av

/-- The registers after the prologue. -/
def Rg (K : Ctx) (g : Gprs) : Prop :=
  g.rsp = K.bp + 112#64 ∧ g.rbp = K.init ∧ g.r12 = K.fini ∧ g.r13 = K.rtld

def I0 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.bp + 376#64 ∧ g.rdi = K.main ∧ g.rsi.setWidth 32 = K.argc ∧ g.rdx = K.argv ∧ g.rcx = K.init ∧
    g.r8 = K.fini ∧ g.r9 = K.rtld ∧ V = K.V0 ∧ n = K.N + 20

def I65 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rax = 0 ∧ Same K d3 V ∧ Fr K V ∧ n = K.N + 19

def I71 (K : Ctx) (m : Nat) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ Same K d3 V ∧ Fr K V ∧ rdd(V, 0x7939c0#64) = 0 ∧ n = K.N + m

def I120 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rbx = K.argv ∧ MA K V ∧ ∃ i, i ≤ K.N ∧ g.rdi = K.envp.add (8 * i) ∧ n = K.N - i + 10

def I131 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rbx = K.argv ∧ MA K V ∧ g.rdi = K.av ∧ n = 8

def I136 (K : Ctx) (m : Nat) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rbx = K.argv ∧ MB K V ∧ n = m

def I206 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rbx = K.argv ∧ MB K V ∧ g.rdi = K.envp ∧ n = 4

/-- At offset 211, where `init_cpu_features` begins. -/
def FinP (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rg K g ∧ g.rbx = K.argv ∧ MB K V

/-- The invariant at each cut point. -/
def InvT (K : Ctx) (ℓ : Nat) : Nat → Gprs → (Addr → Byte) → Prop :=
  if ℓ = 0 then I0 K else
  if ℓ = 65 then I65 K else
  if ℓ = 71 then I71 K 18 else
  if ℓ = 76 then I71 K 17 else
  if ℓ = 120 then I120 K else
  if ℓ = 131 then I131 K else
  if ℓ = 136 then I136 K 7 else
  if ℓ = 194 then I136 K 6 else
  if ℓ = 199 then I136 K 5 else
  if ℓ = 206 then I206 K else
  fun _ _ _ => False

variable {K : Ctx} {V V' : Addr → Byte} {D : List Rgn}

/-! ## Addresses -/

theorem tn (hK : K.Ok) {c i n : Nat} (hi : i < n) (h : c + n ≤ 392) :
    (Addr.add (K.bp + BitVec.ofNat 64 c) i).toNat = K.bp.toNat + c + i := by
  have := hK.hbp
  simp only [Addr.add]; bv_omega

theorem tg {b i n : Nat} (hi : i < n) (h : b + n ≤ 2 ^ 64) : (Addr.add (BitVec.ofNat 64 b) i).toNat = b + i := by
  simp only [Addr.add]; bv_omega

/-- Where the variables lie. -/
theorem bd_gl : ∀ a, Foot globals a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8 := by
  rintro a ⟨r, hr, h1, h2⟩
  simp only [globals, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BitVec.reduceToNat] at h1 h2 <;> omega

theorem bd_d3 : ∀ a, Foot d3 a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8 := by
  rintro a ⟨r, hr, h1, h2⟩
  simp only [d3, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [BitVec.reduceToNat] at h1 h2 <;> omega

theorem bd_dg : ∀ a, Foot (d3 ++ globals) a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8 := by
  rintro a ⟨r, hr, h⟩
  rcases List.mem_append.1 hr with h' | h'
  · exact bd_d3 a ⟨r, h', h⟩
  · exact bd_gl a ⟨r, h', h⟩

theorem bd_nil : ∀ a, Foot ([] : List Rgn) a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8 := by
  rintro a ⟨r, hr, -⟩; cases hr

/-- A variable of `d3` is not one of `_dl_aux_init`'s. -/
theorem d3_not_gl : ∀ a, Foot d3 a → ¬ Foot globals a := by
  rintro a ⟨r, hr, h1, h2⟩ ⟨r', hr', h1', h2'⟩
  simp only [d3, List.mem_cons, List.mem_nil_iff, or_false] at hr
  simp only [globals, List.mem_cons, List.mem_nil_iff, or_false] at hr'
  rcases hr with rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BitVec.reduceToNat] at h1 h2 h1' h2' <;> omega

theorem Clean.sub {a n a' n' : Nat} (h : Clean K a n) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Clean K a' n' := by
  simp only [Clean] at h ⊢; omega

/-- A piece of the image below the variables. -/
theorem clean_img (hK : K.Ok) {a n : Nat} (h1 : 0x400000 ≤ a) (h2 : a + n ≤ 0x791ca0) : Clean K a n := by
  have := hK.himg
  simp only [Clean]; omega

/-- A piece of the image is apart from a callee's frame. -/
theorem off_img (hK : K.Ok) {a n : Nat} (h1 : 0x400000 ≤ a) (h2 : a + n ≤ 0x7a9000) :
    K.bp.toNat + 104 ≤ a ∨ a + n ≤ K.bp.toNat := by
  have := hK.himg
  omega

theorem Clean.off {a n : Nat} (h : Clean K a n) : K.bp.toNat + 104 ≤ a ∨ a + n ≤ K.bp.toNat := by
  simp only [Clean] at h; omega

/-! ## Loads -/

theorem Same.rd (hS : Same K D V) (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8) {a : Addr}
    {n : Nat} (hf : a.toNat + n ≤ 2 ^ 64) (hc : Clean K a.toNat n) :
    List.map V (byteAddrs a n) = List.map K.V0 (byteAddrs a n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits hj hf
  simp only [Clean] at hc
  refine hS _ (by simp only [InStk]; omega) fun hd => ?_
  have := hD _ hd
  omega

theorem Same.at1 (hS : Same K D V) (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8) {a : Addr}
    (hc : Clean K a.toNat 1) : V a = K.V0 a := by
  simp only [Clean] at hc
  refine hS _ (by simp only [InStk]; omega) fun hd => ?_
  have := hD _ hd
  omega

/-- A store into the stack. -/
theorem Same.st (hS : Same K D V) (hK : K.Ok) (c : Nat) {bs : List Byte} (hc : c + bs.length ≤ 376) :
    Same K D (Vst V (K.bp + BitVec.ofNat 64 c) bs) := by
  have := hK.hbp
  intro x hx hx'
  rw [Vst_out _ _ _ _ (by bv_omega) (by simp only [InStk] at hx; bv_omega)]
  exact hS x hx hx'

/-- A store into a variable. -/
theorem Same.stg (hS : Same K D V) (b : Nat) {bs : List Byte} (hm : (⟨BitVec.ofNat 64 b, bs.length⟩ : Rgn) ∈ D)
    (hb : b + bs.length ≤ 2 ^ 64) : Same K D (Vst V (BitVec.ofNat 64 b) bs) := by
  intro x hx hx'
  by_cases hl : bs.length = 0
  · rw [List.length_eq_zero_iff.1 hl]; exact hS x hx hx'
  have e : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  rw [Vst_out _ _ _ _ (by omega) (by
    rcases Nat.lt_or_ge x.toNat b with h | h
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge x.toNat (b + bs.length) with h' | h'
      · exact absurd ⟨_, hm, by simp only [Rgn.Mem]; omega⟩ hx'
      · exact Or.inr (by omega))]
  exact hS x hx hx'

theorem Same.mono {D' : List Rgn} (hS : Same K D V) (h : ∀ a, Foot D a → Foot D' a) : Same K D' V :=
  fun a ha hd => hS a ha fun hd' => hd (h a hd')

/-- A slot of the stack after a store into the stack. -/
theorem rd_ss (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 376)
    (h2 : c + n ≤ 392) (h : c' + bs.length ≤ c ∨ c + n ≤ c') :
    List.map (Vst V (K.bp + BitVec.ofNat 64 c') bs) (byteAddrs (K.bp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.bp + BitVec.ofNat 64 c) n) := by
  have := hK.hbp
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_sself (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (hn : bs.length = n) (h : c + n ≤ 376) :
    List.map (Vst V (K.bp + BitVec.ofNat 64 c) bs) (byteAddrs (K.bp + BitVec.ofNat 64 c) n) = bs := by
  have := hK.hbp
  exact rd_Vst_self _ _ _ hn (by bv_omega)

/-- A piece of the image after a store into the stack. -/
theorem rd_gs (hK : K.Ok) (V : Addr → Byte) (c' b n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 376)
    (hb : 0x400000 ≤ b ∧ b + n ≤ 0x7a9000) :
    List.map (Vst V (K.bp + BitVec.ofNat 64 c') bs) (byteAddrs (BitVec.ofNat 64 b) n) =
      List.map V (byteAddrs (BitVec.ofNat 64 b) n) := by
  have := hK.hbp
  have := hK.himg
  have e : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by omega) (by bv_omega)

/-- A slot of the stack after a store into the image. -/
theorem rd_sg (hK : K.Ok) (V : Addr → Byte) (b c n : Nat) (bs : List Byte) (h2 : c + n ≤ 376)
    (hb : 0x400000 ≤ b ∧ b + bs.length ≤ 0x7a9000) :
    List.map (Vst V (BitVec.ofNat 64 b) bs) (byteAddrs (K.bp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.bp + BitVec.ofNat 64 c) n) := by
  have := hK.hbp
  have := hK.himg
  have e : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  exact rd_Vst _ _ _ _ _ (by omega) (by bv_omega) (by bv_omega)

/-- Bytes that are the same. -/
theorem rd_congr {a : Addr} {n : Nat} (h : ∀ i, i < n → V' (a.add i) = V (a.add i)) :
    List.map V' (byteAddrs a n) = List.map V (byteAddrs a n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h j hj

/-- A slot of the function's frame, when the bytes outside a callee's frame and the variables `D` are the same. -/
theorem rdS (hK : K.Ok) (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8)
    (h : ∀ a, ¬ Low K a → ¬ Foot D a → V' a = V a) (c n : Nat) (hc : 112 ≤ c) (hn : c + n ≤ 392) :
    List.map V' (byteAddrs (K.bp + BitVec.ofNat 64 c) n) = List.map V (byteAddrs (K.bp + BitVec.ofNat 64 c) n) := by
  have := hK.himg
  refine rd_congr fun i hi => ?_
  have e := tn hK hi hn
  refine h _ (by simp only [Low]; omega) fun hd => ?_
  have := hD _ hd
  omega

/-- A piece of the image that is not of `D`. -/
theorem rdG (hK : K.Ok) (h : ∀ a, ¬ Low K a → ¬ Foot D a → V' a = V a) (b n : Nat)
    (hb : 0x400000 ≤ b ∧ b + n ≤ 0x7a9000) (hd : ∀ a : Addr, b ≤ a.toNat → a.toNat < b + n → ¬ Foot D a) :
    List.map V' (byteAddrs (BitVec.ofNat 64 b) n) = List.map V (byteAddrs (BitVec.ofNat 64 b) n) := by
  have := hK.himg
  refine rd_congr fun i hi => ?_
  have e := tg hi (b := b) (by omega)
  exact h _ (by simp only [Low]; omega) (hd _ (by omega) (by omega))

theorem Fr.congr (hF : Fr K V) (hK : K.Ok) (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8)
    (h : ∀ a, ¬ Low K a → ¬ Foot D a → V' a = V a) : Fr K V' :=
  ⟨by rw [rdS hK hD h 128 8 (by decide) (by decide)]; exact hF.argv,
   by rw [rdS hK hD h 136 8 (by decide) (by decide)]; exact hF.main,
   by rw [rdS hK hD h 124 4 (by decide) (by decide)]; exact hF.argc⟩

theorem Same.congr {D' : List Rgn} (hS : Same K D' V) (h : ∀ a, ¬ Low K a → ¬ Foot D a → V' a = V a)
    (hDD : ∀ a, Foot D a → Foot D' a) : Same K D' V' := by
  intro a ha hd
  rw [h a (by simp only [InStk] at ha; simp only [Low]; omega) fun hd' => hd (hDD a hd')]
  exact hS a ha hd

/-- A store of a return address. -/
theorem low_st (hK : K.Ok) (V : Addr → Byte) (bs : List Byte) (hb : bs.length = 8) :
    ∀ a, ¬ Low K a → ¬ Foot ([] : List Rgn) a → Vst V (K.bp + 104#64) bs a = V a := by
  have := hK.hbp
  intro a ha _
  exact Vst_out _ _ _ _ (by bv_omega) (by simp only [Low] at ha; bv_omega)

end FV7z.Start
