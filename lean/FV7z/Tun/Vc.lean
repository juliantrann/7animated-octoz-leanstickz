import FV7z.Tun.Inv
import FV7z.Lemmas.Wp
/-!
# The conditions of `__tunables_init`'s cut points (PLAN.md G3, startup)

For each of the 13 cut points: from its invariant (`Inv.lean`) the condition `W_*` of the code from it (`Cuts.lean`),
with at each exit the invariant there and a smaller measure, `Ret` at the `ret`, and at the three offsets the proof
does not go past (357: a string of the environment begins with an alias and `=`; 491: with `GLIBC_TUNABLES=`; 1326:
`__libc_enable_secure` is set) a contradiction with the precondition. `vcAll`: these together, for `Seg.cfg`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Tun
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-! ## Loads after stores into the frame -/

theorem rd_ff (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 104)
    (h2 : c + n ≤ 104) (h : c' + bs.length ≤ c ∨ c + n ≤ c') :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsp
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_fself (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (hn : bs.length = n) (h : c + n ≤ 104) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c) bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) = bs := by
  have := hK.hsp
  exact rd_Vst_self _ _ _ hn (by bv_omega)

theorem rd_fo (hK : K.Ok) (V : Addr → Byte) (c' : Nat) (bs : List Byte) (a : Addr) (n : Nat)
    (h1 : c' + bs.length ≤ 104) (hf : a.toNat + n ≤ 2 ^ 64) (h : Off K a.toNat n) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs a n) = List.map V (byteAddrs a n) := by
  have := hK.hsp
  simp only [Off] at h
  exact rd_Vst _ _ _ _ _ (by bv_omega) hf (by bv_omega)

theorem out_f (hK : K.Ok) (V : Addr → Byte) (c' : Nat) (bs : List Byte) (x : Addr) (h1 : c' + bs.length ≤ 104)
    (hx : ¬ InFr K x) : Vst V (K.sp + BitVec.ofNat 64 c') bs x = V x := by
  have := hK.hsp
  simp only [InFr] at hx
  exact Vst_out _ _ _ _ (by bv_omega) (by bv_omega)

/-- A store into the frame: where it may store. -/
theorem Env.wr (hE : Env K F Wl) (hK : K.Ok) (c n : Nat) (hc : c + n ≤ 104) :
    ∀ i, i < n → Foot Wl ((K.sp + BitVec.ofNat 64 c).add i) := by
  intro i hi
  have := hK.hsp
  have e := toNat_add_of_fits (a := K.sp + BitVec.ofNat 64 c) hi (by bv_omega)
  exact hE.fr _ (by bv_omega) (by bv_omega)

/-- The bytes the prologue leaves. -/
theorem mem_pro (hK : K.Ok) : Mem K (Vst (Vst (Vst (Vst (Vst (Vst K.V0 (K.sp + 96#64) (toBytesLE K.r15 8))
    (K.sp + 88#64) (toBytesLE K.r14 8)) (K.sp + 80#64) (toBytesLE K.r13 8)) (K.sp + 72#64) (toBytesLE K.r12 8))
    (K.sp + 64#64) (toBytesLE K.rbp 8)) (K.sp + 56#64) (toBytesLE K.rbx 8)) := by
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [out_f hK _ 56 _ _ (by simp [toBytesLE_length]) ha, out_f hK _ 64 _ _ (by simp [toBytesLE_length]) ha,
      out_f hK _ 72 _ _ (by simp [toBytesLE_length]) ha, out_f hK _ 80 _ _ (by simp [toBytesLE_length]) ha,
      out_f hK _ 88 _ _ (by simp [toBytesLE_length]) ha, out_f hK _ 96 _ _ (by simp [toBytesLE_length]) ha]
  all_goals simp only [rd_ff hK, rd_fself hK, toBytesLE_length, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff,
    true_or, ofBytesLE_toBytesLE]

/-! ## The entry -/

theorem vc_0 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : P0 K n g V)
    (h57 : ∀ n' g' fl V', n' < n → I57 K n' g' V' → Q 57 g' fl V')
    (h330 : ∀ n' g' fl V', n' < n → I330 K n' g' V' → Q 330 g' fl V') :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have e1 : K.sp + 104#64 - 8 = K.sp + 96#64 := by bv_omega
  have e2 : K.sp + 96#64 - 8 = K.sp + 88#64 := by bv_omega
  have e3 : K.sp + 88#64 - 8 = K.sp + 80#64 := by bv_omega
  have e4 : K.sp + 80#64 - 8 = K.sp + 72#64 := by bv_omega
  have e5 : K.sp + 72#64 - 8 = K.sp + 64#64 := by bv_omega
  have e6 : K.sp + 64#64 - 8 = K.sp + 56#64 := by bv_omega
  have e7 : K.sp + 56#64 - 56#64 = K.sp := by bv_omega
  have hsec := hK.hsec
  have ho : Off K (7937248#64).toNat 4 := hK.aSec
  wpx [W_0, o0, W_35, o1, W_48, o2, Op.lda, BitVec.reduceSetWidth, e1, e2, e3, e4, e5, e6, e7]
  have hM := mem_pro hK
  generalize Vst _ (K.sp + 56#64) _ = V' at hM ⊢
  rw [hM.rd (by decide) ho, hsec]
  refine ⟨hE.wr hK 96 8 (by decide), hE.wr hK 88 8 (by decide), hE.wr hK 80 8 (by decide), hE.wr hK 72 8 (by decide),
    hE.wr hK 64 8 (by decide), hE.wr hK 56 8 (by decide), fun i hi => ?_, fun af => ⟨fun h => absurd h (by decide),
      fun _ af' => ⟨fun _ => h330 0 _ _ _ (by omega) ⟨rfl, hM⟩,
        fun _ => h57 (K.N * K.B + K.B) _ _ _ (by omega) ⟨rfl, hM, 0, Nat.zero_le _, by simp, by simp⟩⟩⟩⟩
  have e : (Addr.add 7937248#64 i).toNat = 7937248 + i := toNat_add_of_fits (a := 7937248#64) hi (by decide)
  exact hE.sec _ (by omega) (by omega)

/-! ## The loop over the environment -/

/-- A byte of a string that is not 0 is before the string's end. -/
theorem Ctx.Ok.lt_len (hK : K.Ok) {i j : Nat} (hi : i < K.N) (hj : j ≤ K.len i) (h : K.ez i j ≠ 0) : j < K.len i := by
  rcases Nat.lt_or_eq_of_le hj with h' | rfl
  · exact h'
  · exact absurd (hK.hz i hi) h

/-- The address of a byte of the `i`-th string. -/
theorem Ctx.Ok.str_at (hK : K.Ok) {i j : Nat} (hi : i < K.N) (hj : j ≤ K.len i) :
    ((K.ptr i).add j).toNat = (K.ptr i).toNat + j :=
  toNat_add_of_fits (n := K.len i + 1) (by omega) (hK.sfit i hi)

/-- A byte of the `i`-th string, after the prologue. -/
theorem Mem.str (hM : Mem K V) (hK : K.Ok) {i j : Nat} (hi : i < K.N) (hj : j ≤ K.len i) :
    V ((K.ptr i).add j) = K.ez i j := by
  rw [hM.rd1 (hK.aStr i hi) (hK.str_at hi hj) (by omega)]
  exact hK.hstr i hi j hj

/-- A byte of the `i`-th string may be read. -/
theorem Env.rstr (hE : Env K F Wl) (hK : K.Ok) {i j : Nat} (hi : i < K.N) (hj : j ≤ K.len i) :
    ∀ k, k < 1 → Foot F.data (((K.ptr i).add j).add k) := by
  intro k hk
  obtain rfl : k = 0 := by omega
  rw [addr_add_zero]
  have := hK.str_at hi hj
  exact hE.str i hi _ (by omega) (by omega)

/-- A slot of the environment's array. -/
theorem Ctx.Ok.env_at (hK : K.Ok) {i : Nat} (hi : i ≤ K.N) : (K.envp.add (8 * i)).toNat = K.envp.toNat + 8 * i :=
  toNat_add_of_fits (n := 8 * (K.N + 1)) (by omega) hK.hfit

theorem Mem.env (hM : Mem K V) (hK : K.Ok) {i : Nat} (hi : i ≤ K.N) :
    List.map V (byteAddrs (K.envp.add (8 * i)) 8) = List.map K.V0 (byteAddrs (K.envp.add (8 * i)) 8) := by
  have e := hK.env_at hi
  have := hK.hfit; have h := hK.aEnv
  simp only [Off] at h
  exact hM.rd (by omega) (by simp only [Off]; omega)

theorem Env.renv (hE : Env K F Wl) (hK : K.Ok) {i : Nat} (hi : i ≤ K.N) :
    ∀ k, k < 8 → Foot F.data ((K.envp.add (8 * i)).add k) := by
  intro k hk
  have e := hK.env_at hi
  have := hK.hfit
  have e' := toNat_add_of_fits (a := K.envp.add (8 * i)) hk (by omega)
  exact hE.env _ (by omega) (by omega)

theorem env_next (a : Addr) (i : Nat) : a.add (8 * i) + 8#64 = a.add (8 * (i + 1)) := by
  simp only [Addr.add]; bv_omega

theorem vc_57 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I57 K n g V)
    (h104 : ∀ n' g' fl V', n' < n → I104 K n' g' V' → Q 104 g' fl V')
    (h330 : ∀ n' g' fl V', n' < n → I330 K n' g' V' → Q 330 g' fl V')
    (h1205 : ∀ n' g' fl V', n' < n → I1205 K n' g' V' → Q 1205 g' fl V') :
    W_57 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hM, i, hi, rfl, rfl⟩ := h
  have hB := hK.hB; have hC := hK.hC
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · have hw : rdq(V, K.envp.add (8 * i)) = K.ptr i := by rw [hM.env hK hi]; exact hK.henv i hlt
    have hb : ofBytesLE 8 (List.map V (byteAddrs (K.ptr i) 1)) = K.ez i 0 := by
      rw [rd1]; have := hM.str hK hlt (Nat.zero_le _); rwa [addr_add_zero] at this
    have hr := hE.rstr hK hlt (Nat.zero_le _)
    rw [addr_add_zero] at hr
    wpx [W_57, o3, W_70, o4, W_86, o5, W_94, o6, BitVec.reduceSetWidth, hw, hb, sw_8_32_8, BitVec.and_self,
      env_next]
    have hS : ∀ y, Str K ((K.N - i) * K.B + y) ⟨rax, rcx, BitVec.setWidth 64 (BitVec.setWidth 32 (K.ez i 0)),
        K.ptr i, K.sp, rbp, rsi, rdi, r8, r9, r10, r11, r12, K.envp.add (8 * i), r14, K.envp.add (8 * (i + 1))⟩ V i y :=
      fun y => ⟨rfl, hM, hlt, rfl, rfl, rfl⟩
    refine ⟨hE.renv hK hi, fun af => ⟨fun _ => h330 0 _ _ _ (by omega) ⟨rfl, hM⟩, fun _ => ⟨hr,
      fun _ => h1205 _ _ _ _ (by omega) ⟨i, hS _⟩, fun _ af' => ⟨fun _ => h1205 _ _ _ _ (by omega) ⟨i, hS _⟩,
        fun h0 => h104 _ _ _ _ ?_ ⟨i, 1, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, rfl, Nat.le_refl _, ?_⟩⟩⟩⟩⟩
    · omega
    · exact hK.lt_len hlt (Nat.zero_le _) (by simpa using h0)
  · have hw : rdq(V, K.envp.add (8 * K.N)) = 0 := by rw [hM.env hK hi]; exact hK.hend
    wpx [W_57, o3, W_70, o4, W_86, o5, W_94, o6, BitVec.reduceSetWidth, hw, BitVec.and_self]
    exact ⟨hE.renv hK hi, fun af => ⟨fun _ => h330 0 _ _ _ (by omega) ⟨rfl, hM⟩, fun h => absurd h (by decide)⟩⟩

theorem add_one (a : Addr) (j : Nat) : a.add j + 1#64 = a.add (j + 1) := by
  simp only [Addr.add]; bv_omega

theorem vc_104 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I104 K n g V)
    (h104 : ∀ n' g' fl V', n' < n → I104 K n' g' V' → Q 104 g' fl V')
    (h128 : ∀ n' g' fl V', n' < n → I128 K n' g' V' → Q 128 g' fl V')
    (h318 : ∀ n' g' fl V', n' < n → I318 K n' g' V' → Q 318 g' fl V') :
    W_104 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, j, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, rfl, hj1, hj⟩ := h
  have hB := hK.hB; have hC := hK.hC; have hl := hK.hlen i hlt
  have ha : K.ptr i + BitVec.ofNat 64 j = (K.ptr i).add j := rfl
  have hb : ofBytesLE 8 (List.map V (byteAddrs ((K.ptr i).add j) 1)) = K.ez i j := by
    rw [rd1]; exact hM.str hK hlt hj
  have e1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by bv_omega
  wpx [W_104, o7, W_123, o8, BitVec.reduceSetWidth, ha, hb, sw_8_32_8, BitVec.and_self, e1]
  refine ⟨hE.rstr hK hlt hj, fun af => ⟨fun _ => h318 _ _ _ _ ?_ ⟨rfl, hM, i, hlt, rfl, rfl⟩, fun h0 =>
    ⟨fun _ => h104 _ _ _ _ ?_ ⟨i, j + 1, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, rfl, by omega,
      hK.lt_len hlt hj (by simpa using h0)⟩, fun _ => h128 _ _ _ _ ?_ ⟨i, rfl, hM, hlt, rfl, rfl, rfl⟩⟩⟩⟩
  all_goals omega

theorem vc_1205 {Q : Post} (h : I1205 K n g V)
    (h128 : ∀ n' g' fl V', n' < n → I128 K n' g' V' → Q 128 g' fl V') :
    W_1205 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, rfl, hM, hlt, rfl, rfl, rfl⟩ := h
  wpx [W_1205, o27, BitVec.reduceSetWidth, BitVec.xor_self]
  exact fun af => h128 _ _ _ _ (by omega) ⟨i, rfl, hM, hlt, rfl, rfl, rfl⟩

/-! ## `GLIBC_TUNABLES` -/

theorem gz_nz : ∀ k, k < 14 → gz k ≠ 0 := by decide
theorem gz_14 : gz 14 = 0 := by decide

theorem gz_at {k : Nat} (hk : k < 15) : (Addr.add 0x6f32b3#64 k).toNat = 0x6f32b3 + k :=
  toNat_add_of_fits (a := 0x6f32b3#64) hk (by decide)

theorem Mem.gz (hM : Mem K V) (hK : K.Ok) {k : Nat} (hk : k < 15) : V (Addr.add 0x6f32b3#64 k) = gz k := by
  rw [hM.rd1 (b := 0x6f32b3) hK.aG (gz_at hk) hk]
  exact hK.hG k hk

theorem Env.rgz (hE : Env K F Wl) {k : Nat} (hk : k < 15) :
    ∀ x, x < 1 → Foot F.data ((Addr.add 0x6f32b3#64 k).add x) := by
  intro x hx
  obtain rfl : x = 0 := by omega
  rw [addr_add_zero]
  have e := gz_at hk
  exact hE.nm _ (by omega) (by omega)

theorem vc_128 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I128 K n g V)
    (h203 : ∀ n' g' fl V', n' < n → I203 K n' g' V' → Q 203 g' fl V')
    (h318 : ∀ n' g' fl V', n' < n → I318 K n' g' V' → Q 318 g' fl V') :
    W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, rfl, hM, hlt, rfl, rfl, rfl⟩ := h
  wpx [W_128, o5, W_136, o9, BitVec.reduceSetWidth, BitVec.and_self]
  have hsp := hK.hsp
  refine fun af => ⟨fun _ => h318 _ _ _ _ (by omega) ⟨rfl, hM, i, hlt, rfl, rfl⟩, fun _ => ⟨hE.wr hK 8 8 (by decide),
    h203 _ _ _ _ (by omega) ⟨i, 0, ⟨rfl, hM.st hK 8 (by bv_omega) (by simp), hlt, rfl, rfl, rfl⟩, Nat.zero_le _,
      by simp, by simp, by show BitVec.setWidth 8 71#64 = gz 0; decide, fun k hk => absurd hk (by omega),
      Nat.zero_le _⟩⟩⟩

theorem vc_203 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I203 K n g V)
    (h203 : ∀ n' g' fl V', n' < n → I203 K n' g' V' → Q 203 g' fl V')
    (h210 : ∀ n' g' fl V', n' < n → I210 K n' g' V' → Q 210 g' fl V')
    (h491 : ∀ g' fl V', False → Q 491 g' fl V') :
    W_203 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, j, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, hj13, rfl, rfl, hdx, hpre, hj⟩ := h
  dsimp only at hdx
  have hB := hK.hB; have hC := hK.hC; have hl := hK.hlen i hlt
  have hb := hM.str hK hlt hj
  have hg := hM.gz hK (k := j + 1) (by omega)
  wpx [W_203, o13, W_176, o10, W_180, o11, W_200, o12, W_481, o26, Op.cmpmi, BitVec.reduceSetWidth, BitVec.and_self,
    add_one, rd1, hb, hg, hdx, sw_8_32_8]
  have h210' : ∀ g' fl, g'.rsp = K.sp → g'.rbx = K.ptr i → g'.r15 = K.envp.add (8 * (i + 1)) → Q 210 g' fl V :=
    fun g' fl e1 e2 e3 => h210 _ _ _ _ (by omega) ⟨i, e1, hM, hlt, e2, e3, rfl⟩
  refine ⟨hE.rstr hK hlt hj, fun he af => ⟨fun _ => h210' _ _ rfl rfl rfl, fun h0 => ?_⟩, fun _ => h210' _ _ rfl rfl rfl⟩
  have he' : K.ez i j = gz j := by simpa using he
  have hj1 : j + 1 ≤ K.len i := hK.lt_len hlt hj (by simpa using h0)
  refine ⟨hE.rgz (by omega), fun af' => ⟨fun hz => ?_, fun hnz => ?_⟩⟩
  · have e13 : j = 13 := by
      rcases Nat.lt_or_ge j 13 with h | h
      · exact absurd (by simpa using hz) (gz_nz (j + 1) (by omega))
      · omega
    subst e13
    rw [hM.str hK hlt hj1]
    refine ⟨hE.rstr hK hlt hj1, fun _ => h210' _ _ rfl rfl rfl, fun h61 => h491 _ _ _ ?_⟩
    refine hK.noG i hlt (fun k hk => ?_) (by simpa using h61)
    rcases Nat.lt_or_ge k 13 with h | h
    · exact hpre k h
    · obtain rfl : k = 13 := by omega
      exact he'
  · have h13 : j + 1 ≤ 13 := by
      rcases Nat.lt_or_ge j 13 with h | h
      · omega
      · obtain rfl : j = 13 := by omega
        exact absurd gz_14 (by simpa using hnz)
    refine h203 _ _ _ _ (by omega) ⟨i, j + 1, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, h13, rfl, rfl, sw_8_32_64_8 _, fun k hk => ?_, hj1⟩
    rcases Nat.lt_or_ge k j with h | h
    · exact hpre k h
    · obtain rfl : k = j := by omega
      exact he'

/-! ## The loop over the tunables -/

theorem Env.rsec (hE : Env K F Wl) : ∀ i, i < 4 → Foot F.data (Addr.add 7937248#64 i) := by
  intro i hi
  have e : (Addr.add 7937248#64 i).toNat = 7937248 + i := toNat_add_of_fits (a := 7937248#64) hi (by decide)
  exact hE.sec _ (by omega) (by omega)

/-- Bytes of the list of tunables may be read. -/
theorem Env.rlst (hE : Env K F Wl) {a : Addr} {c n : Nat} (ha : a.toNat = 0x791660 + c) (hc : c + n ≤ 1456) :
    ∀ x, x < n → Foot F.data (a.add x) := by
  intro x hx
  have e := toNat_add_of_fits (a := a) hx (by omega)
  exact hE.lst _ (by omega) (by omega)

/-- The `t`-th tunable's alias, after the prologue. -/
theorem Mem.aq (hM : Mem K V) (hK : K.Ok) {t : Nat} (ht : t < 26) :
    rdq(V, BitVec.ofNat 64 (0x791690 + 56 * t)) = K.aq t := by
  have e : (BitVec.ofNat 64 (0x791690 + 56 * t)).toNat = 0x791690 + 56 * t := by
    simp only [BitVec.toNat_ofNat]; omega
  have h := hK.aList
  simp only [Off] at h
  rw [hM.rd (by omega) (by simp only [Off]; omega)]
  exact hK.hal t ht

theorem Ctx.Ok.al_at (hK : K.Ok) {t k : Nat} (ht : t < 26) (hq : K.aq t ≠ 0) (hk : k ≤ K.alen t) :
    ((K.aq t).add k).toNat = (K.aq t).toNat + k :=
  toNat_add_of_fits (n := K.alen t + 1) (by omega) (hK.afit t ht hq)

/-- A byte of the `t`-th tunable's alias, after the prologue. -/
theorem Mem.al (hM : Mem K V) (hK : K.Ok) {t k : Nat} (ht : t < 26) (hq : K.aq t ≠ 0) (hk : k ≤ K.alen t) :
    V ((K.aq t).add k) = K.az t k := by
  rw [hM.rd1 (hK.aAl t ht hq) (hK.al_at ht hq hk) (by omega)]
  exact hK.hastr t ht hq k hk

theorem Env.ral (hE : Env K F Wl) (hK : K.Ok) {t k : Nat} (ht : t < 26) (hq : K.aq t ≠ 0) (hk : k ≤ K.alen t) :
    ∀ x, x < 1 → Foot F.data (((K.aq t).add k).add x) := by
  intro x hx
  obtain rfl : x = 0 := by omega
  rw [addr_add_zero]
  have := hK.al_at ht hq hk
  exact hE.al t ht hq _ (by omega) (by omega)

theorem Ctx.Ok.lt_alen (hK : K.Ok) {t k : Nat} (ht : t < 26) (hq : K.aq t ≠ 0) (hk : k ≤ K.alen t)
    (h : K.az t k ≠ 0) : k < K.alen t := by
  rcases Nat.lt_or_eq_of_le hk with h' | rfl
  · exact h'
  · exact absurd (hK.haz t ht hq) h

theorem Ctx.Ok.eq_alen (hK : K.Ok) {t k : Nat} (ht : t < 26) (hq : K.aq t ≠ 0) (hk : k ≤ K.alen t)
    (h : K.az t k = 0) : k = K.alen t := by
  rcases Nat.lt_or_eq_of_le hk with h' | rfl
  · exact absurd h (hK.hanz t ht hq k h')
  · rfl

theorem vc_210 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I210 K n g V)
    (h232 : ∀ n' g' fl V', n' < n → I232 K n' g' V' → Q 232 g' fl V') :
    W_210 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, rfl, hM, hlt, rfl, rfl, rfl⟩ := h
  have hC := hK.hC
  wpx [W_210, o14, Op.lda, BitVec.reduceSetWidth, BitVec.and_self, BitVec.xor_self]
  refine ⟨hE.rsec, fun af => h232 _ _ _ _ ?_ ⟨i, 0, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, by decide, rfl, rfl⟩⟩
  omega

theorem vc_232 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I232 K n g V)
    (h292 : ∀ n' g' fl V', n' < n → I292 K n' g' V' → Q 292 g' fl V')
    (h304 : ∀ n' g' fl V', n' < n → I304 K n' g' V' → Q 304 g' fl V')
    (h352 : ∀ n' g' fl V', n' < n → I352 K n' g' V' → Q 352 g' fl V') :
    W_232 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, t, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩⟩ := h
  have hC := hK.hC
  have e8 : BitVec.ofNat 64 (0x791688 + 56 * t) + 8#64 = BitVec.ofNat 64 (0x791690 + 56 * t) := by bv_omega
  have hq := hM.aq hK ht
  wpx [W_232, o15, W_238, o16, W_247, o17, W_264, Op.cmpmi, BitVec.reduceSetWidth, BitVec.and_self, e8, hq, rd1,
    sw_8_32_8]
  have a1 : (BitVec.ofNat 64 (0x791688 + 56 * t)).toNat = 0x791660 + (40 + 56 * t) := by
    simp only [BitVec.toNat_ofNat]; omega
  have a2 : (BitVec.ofNat 64 (0x791690 + 56 * t)).toNat = 0x791660 + (48 + 56 * t) := by
    simp only [BitVec.toNat_ofNat]; omega
  have h304' : ∀ g' fl, g'.rsp = K.sp → g'.rbx = K.ptr i → g'.r15 = K.envp.add (8 * (i + 1)) →
      g'.r8 = BitVec.ofNat 64 (0x791688 + 56 * t) → g'.r9 = BitVec.ofNat 64 t → Q 304 g' fl V :=
    fun g' fl e1 e2 e3 e4 e5 => h304 _ _ _ _ (by omega) ⟨i, t, ⟨e1, hM, hlt, e2, e3, rfl⟩, ht, e4, e5⟩
  refine ⟨hE.rlst a1 (by omega), fun _ => h304' _ _ rfl rfl rfl rfl rfl, fun _ => ⟨hE.rlst a2 (by omega), fun af =>
    ⟨fun _ => h304' _ _ rfl rfl rfl rfl rfl, fun hq0 => ?_⟩⟩⟩
  have hq0 : K.aq t ≠ 0 := by simpa using hq0
  have h0 := hM.al hK ht hq0 (Nat.zero_le _)
  rw [addr_add_zero] at h0
  rw [h0]
  refine ⟨fun x hx => ?_, fun af' => ⟨fun hnz => ?_, fun hz => ?_⟩⟩
  · have := hE.ral hK ht hq0 (Nat.zero_le _) x hx
    rwa [addr_add_zero] at this
  · have : 0 < K.alen t := hK.lt_alen ht hq0 (Nat.zero_le _) (by simpa using hnz)
    exact h292 _ _ _ _ (by omega) ⟨i, t, 0, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, by simp, by simp,
      sw_8_32_64_8 _, this, fun k hk => absurd hk (by omega), Nat.zero_le _⟩
  · have e0 : 0 = K.alen t := hK.eq_alen ht hq0 (Nat.zero_le _) (by simpa using hz)
    exact h352 _ _ _ _ (by omega) ⟨i, t, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, by simp [← e0],
      fun k hk => absurd hk (by omega), by omega⟩

theorem vc_292 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I292 K n g V)
    (h292 : ∀ n' g' fl V', n' < n → I292 K n' g' V' → Q 292 g' fl V')
    (h304 : ∀ n' g' fl V', n' < n → I304 K n' g' V' → Q 304 g' fl V')
    (h352 : ∀ n' g' fl V', n' < n → I352 K n' g' V' → Q 352 g' fl V') :
    W_292 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, t, m, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, rfl, rfl, hcx, hm, hpre, hml⟩ := h
  dsimp only at hcx
  have hC := hK.hC; have hl := hK.hlen i hlt
  have hb := hM.str hK hlt hml
  have ha := hM.al hK ht hq0 (k := m + 1) (by omega)
  wpx [W_292, o20, W_272, o18, W_276, o19, W_299, o21, BitVec.reduceSetWidth, BitVec.and_self, add_one, rd1, hb, ha,
    hcx, sw_8_32_8]
  have h304' : ∀ g' fl, g'.rsp = K.sp → g'.rbx = K.ptr i → g'.r15 = K.envp.add (8 * (i + 1)) →
      g'.r8 = BitVec.ofNat 64 (0x791688 + 56 * t) → g'.r9 = BitVec.ofNat 64 t → Q 304 g' fl V :=
    fun g' fl e1 e2 e3 e4 e5 => h304 _ _ _ _ (by omega) ⟨i, t, ⟨e1, hM, hlt, e2, e3, rfl⟩, ht, e4, e5⟩
  refine ⟨hE.rstr hK hlt hml, fun af => ⟨fun hnz => ⟨fun _ => h304' _ _ rfl rfl rfl rfl rfl, fun heq => ?_⟩,
    fun _ => h304' _ _ rfl rfl rfl rfl rfl⟩⟩
  have hnz' : K.ez i m ≠ 0 := by simpa using hnz
  have heq' : K.ez i m = K.az t m := by simpa using heq
  have hm1 : m + 1 ≤ K.len i := hK.lt_len hlt hml hnz'
  have hp : ∀ k : Nat, k < m + 1 → K.ez i k = K.az t k := by
    intro k hk
    rcases Nat.lt_or_ge k m with h | h
    · exact hpre k h
    · obtain rfl : k = m := by omega
      exact heq'
  refine ⟨hE.ral hK ht hq0 (by omega), fun af' => ⟨fun hz => ?_, fun hnz2 => ?_⟩⟩
  · have e := hK.eq_alen ht hq0 (k := m + 1) (by omega) (by simpa using hz)
    exact h352 _ _ _ _ (by omega) ⟨i, t, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, by rw [← e],
      by rw [← e]; exact hp, by omega⟩
  · have := hK.lt_alen ht hq0 (k := m + 1) (by omega) (by simpa using hnz2)
    exact h292 _ _ _ _ (by omega) ⟨i, t, m + 1, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, rfl, rfl,
      sw_8_32_64_8 _, this, hp, hm1⟩

theorem vc_352 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I352 K n g V)
    (h304 : ∀ n' g' fl V', n' < n → I304 K n' g' V' → Q 304 g' fl V')
    (h357 : ∀ g' fl V', False → Q 357 g' fl V') :
    W_352 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, t, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩, hq0, rfl, hpre, hal⟩ := h
  have hb := hM.str hK hlt hal
  wpx [W_352, o25, Op.cmpmi, rd1, hb]
  exact ⟨hE.rstr hK hlt hal, fun _ => h304 _ _ _ _ (by omega) ⟨i, t, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩,
    fun h61 => h357 _ _ _ (hK.noA i hlt t ht hq0 hpre (by simpa using h61))⟩

theorem vc_304 (hK : K.Ok) {Q : Post} (h : I304 K n g V)
    (h232 : ∀ n' g' fl V', n' < n → I232 K n' g' V' → Q 232 g' fl V')
    (h318 : ∀ n' g' fl V', n' < n → I318 K n' g' V' → Q 318 g' fl V') :
    W_304 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨i, t, ⟨⟨rfl, hM, hlt, rfl, rfl, rfl⟩, ht, rfl, rfl⟩⟩ := h
  have hC := hK.hC
  have e9 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 t) + 1#32) = BitVec.ofNat 64 (t + 1) := by
    bv_omega
  have e8 : BitVec.ofNat 64 (0x791688 + 56 * t) + 56#64 = BitVec.ofNat 64 (0x791688 + 56 * (t + 1)) := by bv_omega
  have e26 : (BitVec.setWidth 32 (BitVec.ofNat 64 (t + 1)) = 26#32) ↔ t + 1 = 26 := by
    constructor <;> intro h <;> bv_omega
  wpx [W_304, o22, e8, e9, e26]
  refine ⟨fun h26 => ?_, fun _ => h318 _ _ _ _ (by omega) ⟨rfl, hM, i, hlt, rfl, rfl⟩⟩
  have h25 : t < 25 := by
    have : t + 1 ≠ 26 := by simpa using h26
    omega
  have := mul_step (B := K.C) h25
  exact h232 _ _ _ _ (by omega) ⟨i, t + 1, ⟨rfl, hM, hlt, rfl, rfl, rfl⟩, by omega, rfl, rfl⟩

theorem vc_318 {Q : Post} (h : I318 K n g V)
    (h57 : ∀ n' g' fl V', n' < n → I57 K n' g' V' → Q 57 g' fl V')
    (h330 : ∀ n' g' fl V', n' < n → I330 K n' g' V' → Q 330 g' fl V') :
    W_318 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hM, i, hlt, rfl, rfl⟩ := h
  have := mul_step (B := K.B) hlt
  wpx [W_318, o23, BitVec.and_self]
  exact fun af => ⟨fun _ => h57 _ _ _ _ (by omega) ⟨rfl, hM, i + 1, hlt, rfl, rfl⟩,
    fun _ => h330 0 _ _ _ (by omega) ⟨rfl, hM⟩⟩

theorem vc_330 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I330 K n g V)
    (h344 : ∀ g' fl V', Ret K g' V' → Q 344 g' fl V') :
    W_330 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hM⟩ := h
  have e1 : K.sp + 56#64 + 8 = K.sp + 64#64 := by bv_omega
  have e2 : K.sp + 64#64 + 8 = K.sp + 72#64 := by bv_omega
  have e3 : K.sp + 72#64 + 8 = K.sp + 80#64 := by bv_omega
  have e4 : K.sp + 80#64 + 8 = K.sp + 88#64 := by bv_omega
  have e5 : K.sp + 88#64 + 8 = K.sp + 96#64 := by bv_omega
  have e6 : K.sp + 96#64 + 8 = K.sp + 104#64 := by bv_omega
  wpx [W_330, o24, e1, e2, e3, e4, e5, e6, hM.v0, hM.v1, hM.v2, hM.v3, hM.v4, hM.v5]
  exact ⟨fun i hi => hE.ws _ (hE.wr hK 56 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 64 8 (by decide) i hi),
    fun i hi => hE.ws _ (hE.wr hK 72 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 80 8 (by decide) i hi),
    fun i hi => hE.ws _ (hE.wr hK 88 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 96 8 (by decide) i hi),
    h344 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM.out⟩⟩

/-! ## The conditions together -/

/-- One more cut point of the table. -/
theorem vcT {ℓ k : Nat} {I I' : Nat → Gprs → (Addr → Byte) → Prop} {W W' : Wpt}
    (h : ∀ n g f V, I n g V → W F Wl (Nx K n) g f V) (h' : ∀ n g f V, I' n g V → W' F Wl (Nx K n) g f V) :
    ∀ n g f V, (if ℓ = k then I else I') n g V → (if ℓ = k then W else W') F Wl (Nx K n) g f V := by
  split
  · exact h
  · exact h'

/-- The conditions of all the cut points: from the invariant at `ℓ`, the condition `Wt ℓ` of the code from `ℓ`, with
at each exit the invariant there and a smaller measure, or `Ret` at the `ret`. The three stops are not reached. -/
theorem vcAll (hK : K.Ok) (hE : Env K F Wl) (ℓ : Nat) :
    ∀ n g f V, InvT K ℓ n g V → Wt ℓ F Wl (Nx K n) g f V :=
  vcT (k := 0) (fun _ _ _ _ h => vc_0 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 57) (fun _ _ _ _ h => vc_57 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 104) (fun _ _ _ _ h => vc_104 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 128) (fun _ _ _ _ h => vc_128 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 203) (fun _ _ _ _ h => vc_203 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ h' => h'.elim)) <|
  vcT (k := 210) (fun _ _ _ _ h => vc_210 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 232) (fun _ _ _ _ h => vc_232 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 292) (fun _ _ _ _ h => vc_292 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 304) (fun _ _ _ _ h => vc_304 hK h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 318) (fun _ _ _ _ h => vc_318 h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 330) (fun _ _ _ _ h => vc_330 hK hE h (fun _ _ _ h' => Or.inr ⟨rfl, h'⟩)) <|
  vcT (k := 352) (fun _ _ _ _ h => vc_352 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ h' => h'.elim)) <|
  vcT (k := 1205) (fun _ _ _ _ h => vc_1205 h (fun _ _ _ _ hn h' => nx hn h')) <|
  fun _ _ _ _ h => h.elim

end FV7z.Tun
