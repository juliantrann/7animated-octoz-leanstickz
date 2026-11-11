import FV7z.Start.Inv
import FV7z.Lemmas.Wp
/-!
# The conditions of the cut points of `__libc_start_main`'s start (PLAN.md G3, startup)

For each of the ten cut points (`Inv.lean`): from its invariant the condition of the code from it, with at each exit
the invariant there and a smaller measure, and `FinP` at offset 211. At a `call` the condition is the callee's
(`CallW`): its context (`Auxv.Ctx.Ok`, `Tun.Ctx.Ok`) from what the launch gives, the bytes being those at the entry
where the function has not stored (`Same`), and at its `ret` the return address and the frame as before, by what the
callee keeps (`MA.congr`, `MB.congr`, `MB.of_aux`). The offset the proof does not go past (146: `_dl_phdr` null) is
excluded by the vector's `AT_PHDR`. `vcAll`: these together, for `cfgAt`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out gz)
open FV7z.AuxInit (Vars step globals)
open FV7z.Auxv (Gl)
namespace FV7z.Start
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}

macro "ln" : tactic => `(tactic| (simp only [toBytesLE_length]; decide))

theorem Env.wstk (hE : Env K F Wl) (hK : K.Ok) (c n : Nat) (h : c + n ≤ 376) :
    ∀ i, i < n → Foot Wl ((K.bp + BitVec.ofNat 64 c).add i) := by
  intro i hi
  have e := tn hK hi (c := c) (n := n) (by omega)
  exact hE.stk _ (by omega) (by omega)

theorem Env.wgl (hE : Env K F Wl) (a n : Nat) (hm : (⟨BitVec.ofNat 64 a, n⟩ : Rgn) ∈ d3 ++ globals)
    (ha : a + n ≤ 2 ^ 64) : ∀ i, i < n → Foot Wl (Addr.add (BitVec.ofNat 64 a) i) := by
  intro i hi
  have e := tg hi ha
  have e0 := tg (b := a) (i := 0) (n := n) (by omega) ha
  simp only [addr_add_zero] at e0
  exact hE.gl _ hm _ (by simp only [Rgn.Mem]; omega)

theorem same0 (K : Ctx) (D : List Rgn) : Same K D K.V0 := fun _ _ _ => rfl

theorem vc_0 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I0 K n g V)
    (h65 : ∀ n' g' fl V', n' < n → I65 K n' g' V' → Q 65 g' fl V') :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, rfl, hsi, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have e1 : K.bp + 376#64 - 8 = K.bp + 368#64 := by bv_omega
  have e2 : K.bp + 368#64 - 8 = K.bp + 360#64 := by bv_omega
  have e3 : K.bp + 360#64 - 8 = K.bp + 352#64 := by bv_omega
  have e4 : K.bp + 352#64 - 8 = K.bp + 344#64 := by bv_omega
  have e5 : K.bp + 344#64 - 8 = K.bp + 336#64 := by bv_omega
  have e6 : K.bp + 336#64 - 224#64 = K.bp + 112#64 := by bv_omega
  have e7 : K.bp + 112#64 + 16#64 = K.bp + 128#64 := by bv_omega
  have e8 : K.bp + 112#64 + 24#64 = K.bp + 136#64 := by bv_omega
  have e9 : K.bp + 112#64 + 12#64 = K.bp + 124#64 := by bv_omega
  have hw := hE.wstk hK
  wpx [W_0, o0, W_56, o1, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  refine ⟨hw 368 8 (by decide), fun af => ⟨hw 360 8 (by decide), hw 352 8 (by decide), hw 344 8 (by decide),
    hw 336 8 (by decide), hw 128 8 (by decide), hw 136 8 (by decide), hw 124 4 (by decide), fun af1 =>
    ⟨fun _ => h65 _ _ _ _ (Nat.lt_succ_self _) ⟨⟨rfl, rfl, rfl, rfl⟩, by simp, ?_, ?_, rfl⟩,
      fun hc => absurd hc (by decide)⟩⟩⟩
  · exact ((((((((same0 K d3).st hK 368 (by ln)).st hK 360 (by ln)).st hK 352 (by ln)).st hK 344 (by ln)).st hK 336
      (by ln)).st hK 128 (by ln)).st hK 136 (by ln)).st hK 124 (by ln)
  · refine ⟨?_, ?_, ?_⟩
    · rw [rd_ss hK _ 124 128 8 _ (by ln) (by decide) (by ln), rd_ss hK _ 136 128 8 _ (by ln) (by decide) (by ln),
        rd_sself hK _ 128 8 _ (by simp only [toBytesLE_length]) (by decide)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [rd_ss hK _ 124 136 8 _ (by ln) (by decide) (by ln), rd_sself hK _ 136 8 _ (by simp only [toBytesLE_length]) (by decide)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [rd_sself hK _ 124 4 _ (by simp only [toBytesLE_length]) (by decide), ofBytesLE_toBytesLE (n := 4) rfl _]; exact hsi

theorem Fr.stg (hF : Fr K V) (hK : K.Ok) (b : Nat) (bs : List Byte) (hb : 0x400000 ≤ b ∧ b + bs.length ≤ 0x7a9000) :
    Fr K (Vst V (BitVec.ofNat 64 b) bs) :=
  ⟨by rw [rd_sg hK _ b 128 8 _ (by decide) hb]; exact hF.argv,
   by rw [rd_sg hK _ b 136 8 _ (by decide) hb]; exact hF.main,
   by rw [rd_sg hK _ b 124 4 _ (by decide) hb]; exact hF.argc⟩

theorem Env.rstk (hE : Env K F Wl) (hK : K.Ok) (c n : Nat) (h : c + n ≤ 376) :
    ∀ i, i < n → Foot F.data ((K.bp + BitVec.ofNat 64 c).add i) :=
  fun i hi => hE.ws _ (hE.wstk hK c n h i hi)

theorem Env.rgl (hE : Env K F Wl) (a n : Nat) (hm : (⟨BitVec.ofNat 64 a, n⟩ : Rgn) ∈ d3 ++ globals)
    (ha : a + n ≤ 2 ^ 64) : ∀ i, i < n → Foot F.data (Addr.add (BitVec.ofNat 64 a) i) :=
  fun i hi => hE.ws _ (hE.wgl a n hm ha i hi)

theorem Env.rarg (hE : Env K F Wl) (hK : K.Ok) : ∀ i, i < 8 → Foot F.data ((K.bp + 384#64).add i) := by
  intro i hi
  have e := tn hK hi (c := 384) (n := 8) (by decide)
  exact hE.arg _ (by omega) (by omega)

/-- A piece of the environment's array and the vector. -/
theorem env_tn (hK : K.Ok) {o i n : Nat} (hi : i < n) (h : o + n ≤ 8 * (K.N + 1) + 16 * K.M + 8) :
    ((K.envp.add o).add i).toNat = K.envp.toNat + o + i := by
  have := hK.hfit
  simp only [Addr.add]; bv_omega

theorem Env.renv (hE : Env K F Wl) (hK : K.Ok) (o n : Nat) (h : o + n ≤ 8 * (K.N + 1) + 16 * K.M + 8) :
    ∀ i, i < n → Foot F.data ((K.envp.add o).add i) := by
  intro i hi
  have e := env_tn hK hi h
  exact hE.env _ (by omega) (by omega)

theorem Same.envrd {D : List Rgn} (hS : Same K D V) (hK : K.Ok)
    (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8) (o n : Nat)
    (h : o + n ≤ 8 * (K.N + 1) + 16 * K.M + 8) :
    List.map V (byteAddrs (K.envp.add o) n) = List.map K.V0 (byteAddrs (K.envp.add o) n) := by
  by_cases hn : n = 0
  · subst hn; rfl
  have e := env_tn hK (i := 0) (n := n) (by omega) h
  simp only [addr_add_zero, Nat.add_zero] at e
  have := hK.hfit
  exact hS.rd hD (by omega) (hK.cEnv.sub (by omega) (by omega))

/-! ## The variables after the vector -/

theorem step_secure_ne (v : Vars) (e : BitVec 64 × BitVec 64) (h : e.1 ≠ 23) :
    (AuxInit.step v e).secure = v.secure ∧ (AuxInit.step v e).decided = v.decided := by
  simp only [AuxInit.step, apply_ite Vars.secure, apply_ite Vars.decided, h, ↓reduceIte, ite_self, and_self]

theorem step_phdr_ne (v : Vars) (e : BitVec 64 × BitVec 64) (h : e.1 ≠ 3) : (AuxInit.step v e).phdr = v.phdr := by
  simp only [AuxInit.step, apply_ite Vars.phdr, h, ↓reduceIte, ite_self]

theorem vs_secure (hK : K.Ok) : ∀ n, n ≤ K.M → (∃ k, k < n ∧ K.ty k = 23) →
    (K.vs n).secure = 0#32 ∧ (K.vs n).decided = 1#32 := by
  intro n
  induction n with
  | zero => rintro - ⟨k, hk, -⟩; omega
  | succ n ih =>
    rintro hn ⟨k, hk, hk23⟩
    by_cases h : K.ty n = 23
    · have := hK.hsec0 n (by omega) h
      simp [Ctx.vs, vsOf, AuxInit.step, h, this]
    · have h1 := step_secure_ne (K.vs n) (K.ty n, K.val n) h
      have h2 := ih (by omega) ⟨k, by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h' | h'
        · exact h'
        · subst h'; exact absurd hk23 h, hk23⟩
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem vs_phdr (hK : K.Ok) : ∀ n, n ≤ K.M → (∃ k, k < n ∧ K.ty k = 3) → (K.vs n).phdr ≠ 0#64 := by
  intro n
  induction n with
  | zero => rintro - ⟨k, hk, -⟩; omega
  | succ n ih =>
    rintro hn ⟨k, hk, hk3⟩
    by_cases h : K.ty n = 3
    · have := hK.hph0 n (by omega) h
      simpa [Ctx.vs, vsOf, AuxInit.step, h] using this
    · have h1 := step_phdr_ne (K.vs n) (K.ty n, K.val n) h
      have h2 := ih (by omega) ⟨k, by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h' | h'
        · exact h'
        · subst h'; exact absurd hk3 h, hk3⟩
      exact fun h0 => h2 (h1.symm.trans h0)

/-! ## The bytes across a call -/

theorem nf (b n : Nat) : ∀ a : Addr, b ≤ a.toNat → a.toNat < b + n → ¬ Foot ([] : List Rgn) a :=
  fun _ _ _ ⟨_, hr, _⟩ => nomatch hr

theorem ng (b n : Nat) (hm : (⟨BitVec.ofNat 64 b, n⟩ : Rgn) ∈ d3) (hb : b + n ≤ 2 ^ 64) :
    ∀ a : Addr, b ≤ a.toNat → a.toNat < b + n → ¬ Foot globals a :=
  fun a h1 h2 => d3_not_gl a ⟨_, hm, by simp only [Rgn.Mem, BitVec.toNat_ofNat]; omega⟩

variable {V' : Addr → Byte}

theorem gl_congr {w : Vars} (hG : Gl V w) (hK : K.Ok)
    (h : ∀ a, ¬ Low K a → ¬ Foot ([] : List Rgn) a → V' a = V a) : Gl V' w :=
  ⟨by rw [rdG hK h 0x7933d8 8 (by decide) (nf _ _)]; exact hG.pagesize,
   by rw [rdG hK h 0x7a85c0 4 (by decide) (nf _ _)]; exact hG.clktck,
   by rw [rdG hK h 0x7a8580 8 (by decide) (nf _ _)]; exact hG.phdr,
   by rw [rdG hK h 0x7a8598 8 (by decide) (nf _ _)]; exact hG.phnum,
   by rw [rdG hK h 0x7a8548 8 (by decide) (nf _ _)]; exact hG.platform,
   by rw [rdG hK h 0x7a4ac8 8 (by decide) (nf _ _)]; exact hG.hwcap,
   by rw [rdG hK h 0x7a4ac0 8 (by decide) (nf _ _)]; exact hG.hwcap2,
   by rw [rdG hK h 0x7a8508 8 (by decide) (nf _ _)]; exact hG.sysinfoDso,
   by rw [rdG hK h 0x7933cc 2 (by decide) (nf _ _)]; exact hG.fpuControl,
   by rw [rdG hK h 0x791ce0 4 (by decide) (nf _ _)]; exact hG.secure,
   by rw [rdG hK h 0x7a85c4 4 (by decide) (nf _ _)]; exact hG.decided,
   by rw [rdG hK h 0x791ca0 8 (by decide) (nf _ _)]; exact hG.random⟩

theorem MA.congr (hM : MA K V) (hK : K.Ok) (h : ∀ a, ¬ Low K a → ¬ Foot ([] : List Rgn) a → V' a = V a) :
    MA K V' :=
  ⟨hM.same.congr h (fun _ ⟨_, hr, _⟩ => nomatch hr), hM.fr.congr hK bd_nil h,
   by rw [rdG hK h 7944640 4 (by decide) (nf _ _)]; exact hM.mlibs,
   by rw [rdG hK h 8013720 8 (by decide) (nf _ _)]; exact hM.env,
   by rw [rdG hK h 7937200 8 (by decide) (nf _ _)]; exact hM.se⟩

theorem MB.congr (hM : MB K V) (hK : K.Ok) (h : ∀ a, ¬ Low K a → ¬ Foot ([] : List Rgn) a → V' a = V a) :
    MB K V' :=
  ⟨hM.same.congr h (fun _ ⟨_, hr, _⟩ => nomatch hr), hM.fr.congr hK bd_nil h,
   by rw [rdG hK h 7944640 4 (by decide) (nf _ _)]; exact hM.mlibs,
   by rw [rdG hK h 8013720 8 (by decide) (nf _ _)]; exact hM.env,
   by rw [rdG hK h 7937200 8 (by decide) (nf _ _)]; exact hM.se,
   gl_congr hM.gl hK h,
   by rw [rdG hK h 0x7a8540 8 (by decide) (nf _ _)]; exact hM.auxv⟩

/-- After `_dl_aux_init`. -/
theorem MB.of_aux (hM : MA K V) (hK : K.Ok) (h : ∀ a, ¬ Low K a → ¬ Foot globals a → V' a = V a)
    (hgl : Gl V' (K.vs K.M)) (hax : rdq(V', 0x7a8540#64) = K.av) : MB K V' := by
  refine ⟨fun a ha hd => ?_, hM.fr.congr hK bd_gl h, ?_, ?_, ?_, hgl, hax⟩
  · rw [h a (by simp only [InStk] at ha; simp only [Low]; omega)
      fun hg => hd (by obtain ⟨r, hr, hm⟩ := hg; exact ⟨r, List.mem_append_right _ hr, hm⟩)]
    exact hM.same a ha fun h3 => hd (by obtain ⟨r, hr, hm⟩ := h3; exact ⟨r, List.mem_append_left _ hr, hm⟩)
  · rw [rdG hK h 7944640 4 (by decide) (ng _ _ (by simp [d3]) (by decide))]; exact hM.mlibs
  · rw [rdG hK h 8013720 8 (by decide) (ng _ _ (by simp [d3]) (by decide))]; exact hM.env
  · rw [rdG hK h 7937200 8 (by decide) (ng _ _ (by simp [d3]) (by decide))]; exact hM.se

theorem fg (b n : Nat) (hm : (⟨BitVec.ofNat 64 b, n⟩ : Rgn) ∈ globals) (hb : b + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    Foot globals (Addr.add (BitVec.ofNat 64 b) i) :=
  ⟨_, hm, by have e := tg hi hb; simp only [Rgn.Mem, BitVec.toNat_ofNat]; omega⟩

/-- `_dl_aux_init`'s variables, not set before it. -/
theorem gl_of_same (hS : Same K d3 V) (hK : K.Ok) {w : Vars} (hG : Gl K.V0 w) : Gl V w := by
  have h : ∀ a, Foot globals a → V a = K.V0 a := fun a ha =>
    hS a (fun hs => by have := bd_gl a ha; have := hK.himg; simp only [InStk] at hs; omega)
      fun h3 => d3_not_gl a h3 ha
  exact
   ⟨by rw [rd_congr fun i hi => h _ (fg 0x7933d8 8 (by simp [globals]) (by decide) hi)]; exact hG.pagesize,
    by rw [rd_congr fun i hi => h _ (fg 0x7a85c0 4 (by simp [globals]) (by decide) hi)]; exact hG.clktck,
    by rw [rd_congr fun i hi => h _ (fg 0x7a8580 8 (by simp [globals]) (by decide) hi)]; exact hG.phdr,
    by rw [rd_congr fun i hi => h _ (fg 0x7a8598 8 (by simp [globals]) (by decide) hi)]; exact hG.phnum,
    by rw [rd_congr fun i hi => h _ (fg 0x7a8548 8 (by simp [globals]) (by decide) hi)]; exact hG.platform,
    by rw [rd_congr fun i hi => h _ (fg 0x7a4ac8 8 (by simp [globals]) (by decide) hi)]; exact hG.hwcap,
    by rw [rd_congr fun i hi => h _ (fg 0x7a4ac0 8 (by simp [globals]) (by decide) hi)]; exact hG.hwcap2,
    by rw [rd_congr fun i hi => h _ (fg 0x7a8508 8 (by simp [globals]) (by decide) hi)]; exact hG.sysinfoDso,
    by rw [rd_congr fun i hi => h _ (fg 0x7933cc 2 (by simp [globals]) (by decide) hi)]; exact hG.fpuControl,
    by rw [rd_congr fun i hi => h _ (fg 0x791ce0 4 (by simp [globals]) (by decide) hi)]; exact hG.secure,
    by rw [rd_congr fun i hi => h _ (fg 0x7a85c4 4 (by simp [globals]) (by decide) hi)]; exact hG.decided,
    by rw [rd_congr fun i hi => h _ (fg 0x791ca0 8 (by simp [globals]) (by decide) hi)]; exact hG.random⟩

theorem av_tn (hK : K.Ok) : K.av.toNat = K.envp.toNat + 8 * (K.N + 1) := by
  have e := env_tn hK (o := 8 * (K.N + 1)) (i := 0) (n := 1) (by omega) (by omega)
  simpa only [addr_add_zero, Nat.add_zero, Ctx.av] using e

theorem Same.avrd {D : List Rgn} (hS : Same K D V) (hK : K.Ok)
    (hD : ∀ a, Foot D a → 0x791ca0 ≤ a.toNat ∧ a.toNat < 0x7a85c8) (o n : Nat) (h : o + n ≤ 16 * K.M + 8) :
    List.map V (byteAddrs (K.av.add o) n) = List.map K.V0 (byteAddrs (K.av.add o) n) := by
  have e : K.av.add o = K.envp.add (8 * (K.N + 1) + o) := by simp only [Ctx.av, Addr.add]; bv_omega
  rw [e]; exact hS.envrd hK hD _ _ (by omega)

theorem sk0' (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 0 v =
      Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl

/-! ## The conditions -/

theorem vc_65 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I65 K n g V)
    (h71 : ∀ n' g' fl V', n' < n → I71 K 18 n' g' V' → Q 71 g' fl V') :
    W_65 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hS, hF, rfl⟩ := h
  wpx [W_65, o2, Op.sta]
  refine ⟨hE.wgl 7944640 4 (by simp [d3]) (by decide), h71 _ _ _ _ (Nat.lt_succ_self _)
    ⟨⟨rfl, rfl, rfl, rfl⟩, hS.stg 7944640 (by simp [d3, toBytesLE_length]) (by ln), hF.stg hK 7944640 _ (by ln), ?_,
      rfl⟩⟩
  rw [Auxv.rd_cs V 7944640 4 _ (by simp only [toBytesLE_length]) (by decide), ofBytesLE_toBytesLE (n := 4) rfl _]
  rfl

theorem vc_76 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I71 K 17 n g V)
    (h120 : ∀ n' g' fl V', n' < n → I120 K n' g' V' → Q 120 g' fl V') :
    W_76 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, hS, hF, hm, rfl⟩ := h
  have e7 : K.bp + 112#64 + 16#64 = K.bp + 128#64 := by bv_omega
  have e9 : K.bp + 112#64 + 12#64 = K.bp + 124#64 := by bv_omega
  have e10 : K.bp + 112#64 + 272#64 = K.bp + 384#64 := by bv_omega
  have hse : rdq(V, K.bp + 384#64) = K.stackEnd := by
    have := hK.hbp
    have := hK.himg
    rw [hS.rd bd_d3 (a := K.bp + 384#64) (n := 8) (by bv_omega) (by simp only [Clean]; bv_omega)]
    exact hK.hse
  wpx [W_76, o3, Op.sta, Op.ldsx, e7, e9, e10, hF.argv, hF.argc, hse, hK.henvp]
  refine ⟨hE.rstk hK 124 4 (by decide), hE.rstk hK 128 8 (by decide), hE.rarg hK,
    hE.wgl 8013720 8 (by simp [d3]) (by decide), hE.wgl 7937200 8 (by simp [d3]) (by decide),
    h120 _ _ _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl⟩, rfl,
      ⟨(hS.stg 8013720 (by simp [d3, toBytesLE_length]) (by ln)).stg 7937200 (by simp [d3, toBytesLE_length]) (by ln),
        (hF.stg hK 8013720 _ (by ln)).stg hK 7937200 _ (by ln), ?_, ?_, ?_⟩, 0, Nat.zero_le _, by simp, rfl⟩⟩
  · rw [Auxv.rd_cc _ 7937200 7944640 4 _ (by ln), Auxv.rd_cc _ 8013720 7944640 4 _ (by ln)]; exact hm
  · rw [Auxv.rd_cc _ 7937200 8013720 8 _ (by ln), Auxv.rd_cs _ 8013720 8 _ (by simp only [toBytesLE_length]) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [Auxv.rd_cs _ 7937200 8 _ (by simp only [toBytesLE_length]) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem env_prev (a : Addr) (i : Nat) : a.add (8 * (i + 1)) + 18446744073709551608#64 = a.add (8 * i) := by
  simp only [Addr.add]; bv_omega

theorem vc_120 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I120 K n g V)
    (h120 : ∀ n' g' fl V', n' < n → I120 K n' g' V' → Q 120 g' fl V')
    (h131 : ∀ n' g' fl V', n' < n → I131 K n' g' V' → Q 131 g' fl V') :
    W_120 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, i, hi, rfl, rfl⟩ := h
  have hr := hM.same.envrd hK bd_d3 (8 * i) 8 (by omega)
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · have hw : rdq(V, K.envp.add (8 * i)) = K.ptr i := by rw [hr]; exact hK.henv i hlt
    have hz := hK.hnz i hlt
    wpx [W_120, o4, Op.cmpmi, Tun.env_next, env_prev, hw]
    exact ⟨hE.renv hK (8 * i) 8 (by omega), fun _ => h120 _ _ _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, i + 1,
      hlt, rfl, rfl⟩, fun hc => absurd hc (by simpa using hz)⟩
  · have hw : rdq(V, K.envp.add (8 * K.N)) = 0#64 := by rw [hr]; exact hK.hend
    wpx [W_120, o4, Op.cmpmi, Tun.env_next, env_prev, hw]
    exact ⟨hE.renv hK (8 * K.N) 8 (by omega), fun hc => absurd hc (by simp),
      fun _ => h131 _ _ _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl, rfl⟩⟩

theorem vc_136 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I136 K 7 n g V)
    (h194 : ∀ n' g' fl V', n' < n → I136 K 6 n' g' V' → Q 194 g' fl V') :
    W_136 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl⟩ := h
  have hp := vs_phdr hK K.M (Nat.le_refl _) hK.hph
  wpx [W_136, o5, Op.cmpmia, hM.gl.phdr, hp]
  exact ⟨hE.rgl 8029568 8 (by simp [globals]) (by decide), fun _ => h194 _ _ _ _ (by decide)
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl⟩, fun hc => absurd hc (by simp)⟩

theorem vc_199 (hE : Env K F Wl) {Q : Post} (h : I136 K 5 n g V)
    (h206 : ∀ n' g' fl V', n' < n → I206 K n' g' V' → Q 206 g' fl V') :
    W_199 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl⟩ := h
  wpx [W_199, o6, Op.lda, hM.env]
  exact ⟨hE.rgl 8013720 8 (by simp [d3]) (by decide), h206 _ _ _ _ (by decide)
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl, rfl⟩⟩

theorem vc_71 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I71 K 18 n g V)
    (h76 : ∀ n' g' fl V', n' < n → I71 K 17 n' g' V' → Q 76 g' fl V') :
    CallW F Wl lsm_at 76 (fun R g V => R g V) Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, hS, hF, hm, rfl⟩ := h
  have e : K.bp + 112#64 - 8 = K.bp + 104#64 := by bv_omega
  have e' : K.bp + 104#64 + 8 = K.bp + 112#64 := by bv_omega
  wpx [CallW, e, e']
  have hl := low_st hK V (toBytesLE (lsm_at.add 76) 8) (by simp only [toBytesLE_length])
  refine ⟨hE.wstk hK 104 8 (by decide), hE.rstk hK 104 8 (by decide), ?_, fun fl => h76 _ _ _ _ (Nat.lt_succ_self _)
    ⟨⟨rfl, rfl, rfl, rfl⟩, hS.st hK 104 (by ln), hF.congr hK bd_nil hl, ?_, rfl⟩⟩
  · rw [rd_sself hK _ 104 8 _ (by simp only [toBytesLE_length]) (by decide)]; exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_gs hK _ 104 7944640 4 _ (by ln) (by decide)]; exact hm

theorem vc_194 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I136 K 6 n g V)
    (h199 : ∀ n' g' fl V', n' < n → I136 K 5 n' g' V' → Q 199 g' fl V') :
    CallW F Wl lsm_at 199 (Tsec F) Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl⟩ := h
  have e : K.bp + 112#64 - 8 = K.bp + 104#64 := by bv_omega
  have e' : K.bp + 104#64 + 8 = K.bp + 112#64 := by bv_omega
  have hl := low_st hK V (toBytesLE (lsm_at.add 199) 8) (by simp only [toBytesLE_length])
  have hM' := hM.congr hK hl
  have hd : rdd(Vst V (K.bp + 104#64) (toBytesLE (lsm_at.add 199) 8), 0x7a85c4#64) ≠ 0 := by
    rw [hM'.gl.decided, (vs_secure hK K.M (Nat.le_refl _) ⟨K.sn, hK.hsn, hK.hsec⟩).2]; decide
  wpx [CallW, e, e', Tsec, sk0']
  refine ⟨hE.wstk hK 104 8 (by decide), hE.rgl 8029636 4 (by simp [globals]) (by decide), hd, fun a =>
    ⟨hE.rstk hK 104 8 (by decide), ?_, fun fl => h199 _ _ _ _ (by decide) ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM', rfl⟩⟩⟩
  rw [rd_sself hK _ 104 8 _ (by simp only [toBytesLE_length]) (by decide)]; exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem vc_131 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I131 K n g V)
    (h136 : ∀ n' g' fl V', n' < n → I136 K 7 n' g' V' → Q 136 g' fl V') :
    CallW F Wl lsm_at 136 (Taux F Wl) Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl, rfl⟩ := h
  have e : K.bp + 112#64 - 8 = K.bp + 104#64 := by bv_omega
  have e' : K.bp + 104#64 + 8 = K.bp + 112#64 := by bv_omega
  have hl := low_st hK V (toBytesLE (lsm_at.add 136) 8) (by simp only [toBytesLE_length])
  have hM' := hM.congr hK hl
  have hS' := hM'.same
  have hbp := hK.hbp
  have himg := hK.himg
  have hfit := hK.hfit
  have hav := av_tn hK
  have hce := hK.cEnv
  wpx [CallW, e, e', Taux]
  refine ⟨hE.wstk hK 104 8 (by decide), ⟨K.bp, K.argv, K.init, K.fini, K.rtld, r14, r15, K.av, K.M, K.ty, K.val, K.sn,
    K.vs, Vst V (K.bp + 104#64) (toBytesLE (lsm_at.add 136) 8)⟩, ⟨?_, ?_⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · exact {
      hsp := by show K.bp.toNat + 112 ≤ 2 ^ 64; omega
      hfit := by show K.av.toNat + (16 * K.M + 8) ≤ 2 ^ 64; omega
      aAv := by
        show K.bp.toNat + 104 ≤ K.av.toNat ∨ K.av.toNat + (16 * K.M + 8) ≤ K.bp.toNat
        simp only [Clean] at hce; omega
      xAv := by
        show K.av.toNat + (16 * K.M + 8) ≤ 0x7a8540 ∨ 0x7a8548 ≤ K.av.toNat
        simp only [Clean] at hce; omega
      hty := fun n (hn : n < K.M) => by
        show rdq(_, K.av.add (16 * n)) = K.ty n
        rw [hS'.avrd hK bd_d3 (16 * n) 8 (by omega)]; exact hK.hty n hn
      hval := fun n (hn : n < K.M) => by
        show rdq(_, K.av.add (16 * n + 8)) = K.val n
        rw [hS'.avrd hK bd_d3 (16 * n + 8) 8 (by omega)]; exact hK.hval n hn
      hnz := hK.hnzT
      hend := by
        show rdq(_, K.av.add (16 * K.M)) = 0
        rw [hS'.avrd hK bd_d3 (16 * K.M) 8 (by omega)]; exact hK.hendT
      hsn := hK.hsn
      hsec := hK.hsec
      aJt := off_img hK (by decide) (by decide)
      hjt := fun k hk => by
        have e := tg (b := 0x6f3660) (i := 4 * k) (n := 124) (by omega) (by decide)
        simp only [Addr.add] at e
        show rdd(_, Addr.add 0x6f3660#64 (4 * k)) = Auxv.jt k
        rw [hS'.rd bd_d3 (by simp only [Addr.add]; omega)
          (clean_img hK (by simp only [Addr.add]; omega) (by simp only [Addr.add]; omega))]
        exact hK.hjt k hk
      hvs := fun _ _ => rfl
      hgl := gl_of_same hS' hK hK.hgl
      oAx := off_img hK (by decide) (by decide)
      oPs := off_img hK (by decide) (by decide)
      oCk := off_img hK (by decide) (by decide)
      oPh := off_img hK (by decide) (by decide)
      oPn := off_img hK (by decide) (by decide)
      oPl := off_img hK (by decide) (by decide)
      oHw := off_img hK (by decide) (by decide)
      oH2 := off_img hK (by decide) (by decide)
      oSy := off_img hK (by decide) (by decide)
      oFp := off_img hK (by decide) (by decide)
      oSe := off_img hK (by decide) (by decide)
      oDe := off_img hK (by decide) (by decide)
      oRa := off_img hK (by decide) (by decide) }
  · exact ⟨hE.ws, fun y (h1 : K.bp.toNat ≤ y.toNat) (h2 : y.toNat < K.bp.toNat + 104) => hE.stk y h1 (by omega),
      fun r hr y hy => hE.gl r (List.mem_append_right _ hr) y hy,
      hE.tab, fun y h1 h2 => hE.env y (by show K.envp.toNat ≤ y.toNat; have : K.av.toNat ≤ y.toNat := h1; omega)
        (by have : y.toNat < K.av.toNat + (16 * K.M + 8) := h2; omega)⟩
  · rintro ⟨rax', rcx', rdx', rbx', rsp', rbp', rsi', rdi', r8', r9', r10', r11', r12', r13', r14', r15'⟩ V'
      ⟨hsp, hbx, hbp', h12, h13, -, -, hG, hax, hO⟩
    obtain rfl : rsp' = K.bp + 104#64 := hsp
    obtain rfl : rbx' = K.argv := hbx
    obtain rfl : rbp' = K.init := hbp'
    obtain rfl : r12' = K.fini := h12
    obtain rfl : r13' = K.rtld := h13
    simp only [sk4', e']
    have hO' : ∀ a, ¬ Low K a → ¬ Foot globals a → V' a = Vst V (K.bp + 104#64) (toBytesLE (lsm_at.add 136) 8) a :=
      fun a hl hg => hO a (fun hf => hl ⟨hf.1, by have h2 : a.toNat < K.bp.toNat + 104 := hf.2; omega⟩) hg
    refine ⟨hE.rstk hK 104 8 (by decide), ?_, fun fl => h136 _ _ _ _ (by decide)
      ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, MB.of_aux hM' hK hO' hG hax, rfl⟩⟩
    rw [rd_congr (a := K.bp + 104#64) (n := 8) fun i hi => hO _ (fun hf => by
        have e := tn hK hi (c := 104) (n := 8) (by decide)
        have h2 : ((K.bp + 104#64).add i).toNat < K.bp.toNat + 104 := hf.2
        omega) (fun hg => by
        have e := tn hK hi (c := 104) (n := 8) (by decide)
        have := bd_gl _ hg; omega),
      rd_sself hK _ 104 8 _ (by simp only [toBytesLE_length]) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem vc_206 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I206 K n g V)
    (h211 : ∀ g' fl V', FinP K g' V' → Q 211 g' fl V') :
    CallW F Wl lsm_at 211 (Ttin F Wl) Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM, rfl, rfl⟩ := h
  have e : K.bp + 112#64 - 8 = K.bp + 104#64 := by bv_omega
  have e' : K.bp + 104#64 + 8 = K.bp + 112#64 := by bv_omega
  have hl := low_st hK V (toBytesLE (lsm_at.add 211) 8) (by simp only [toBytesLE_length])
  have hM' := hM.congr hK hl
  have hS' := hM'.same
  have hbp := hK.hbp
  have himg := hK.himg
  have hfit := hK.hfit
  have hce := hK.cEnv
  wpx [CallW, e, e', Ttin]
  refine ⟨hE.wstk hK 104 8 (by decide), ⟨K.bp, K.argv, K.init, K.fini, K.rtld, r14, r15, K.envp, K.N, K.ptr, K.ez,
    K.len, K.lmax, K.aq, K.az, K.alen, 26 * (K.lmax + 10) + 30 + K.lmax, K.lmax + 10,
    Vst V (K.bp + 104#64) (toBytesLE (lsm_at.add 211) 8)⟩, ⟨?_, ?_⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · exact {
      hsp := by show K.bp.toNat + 112 ≤ 2 ^ 64; omega
      hC := rfl
      hB := rfl
      hsec := by
        show rdd(_, 0x791ce0#64) = 0
        rw [hM'.gl.secure]; exact (vs_secure hK K.M (Nat.le_refl _) ⟨K.sn, hK.hsn, hK.hsec⟩).1
      aSec := off_img hK (by decide) (by decide)
      hG := fun k hk => by
        have e := tg (b := 0x6f32b3) (i := k) (n := 15) hk (by decide)
        simp only [Addr.add] at e
        show Vst V _ _ (Addr.add 0x6f32b3#64 k) = gz k
        rw [hS'.at1 bd_dg (clean_img hK (by simp only [Addr.add]; omega) (by simp only [Addr.add]; omega))]
        exact hK.hG k hk
      aG := off_img hK (by decide) (by decide)
      hfit := by show K.envp.toNat + 8 * (K.N + 1) ≤ 2 ^ 64; omega
      aEnv := by
        show K.bp.toNat + 104 ≤ K.envp.toNat ∨ K.envp.toNat + 8 * (K.N + 1) ≤ K.bp.toNat
        simp only [Clean] at hce; omega
      henv := fun i (hi : i < K.N) => by
        show rdq(_, K.envp.add (8 * i)) = K.ptr i
        rw [hS'.envrd hK bd_dg (8 * i) 8 (by omega)]; exact hK.henv i hi
      hend := by
        show rdq(_, K.envp.add (8 * K.N)) = 0
        rw [hS'.envrd hK bd_dg (8 * K.N) 8 (by omega)]; exact hK.hend
      hnz := hK.hnz
      sfit := hK.sfit
      aStr := fun i (hi : i < K.N) => (hK.cStr i hi).off
      hstr := fun i (hi : i < K.N) k (hk : k ≤ K.len i) => by
        have e := toNat_add_of_fits (a := K.ptr i) (i := k) (n := K.len i + 1) (by omega) (hK.sfit i hi)
        show Vst V _ _ ((K.ptr i).add k) = K.ez i k
        rw [hS'.at1 bd_dg ((hK.cStr i hi).sub (by omega) (by omega))]
        exact hK.hstr i hi k hk
      hz := hK.hz
      hlen := hK.hlen
      aList := off_img hK (by decide) (by decide)
      hal := fun t ht => by
        have e : (BitVec.ofNat 64 (0x791690 + 56 * t)).toNat = 0x791690 + 56 * t := by
          rw [BitVec.toNat_ofNat]; omega
        show rdq(_, BitVec.ofNat 64 (0x791690 + 56 * t)) = K.aq t
        rw [hS'.rd bd_dg (by omega) (clean_img hK (by omega) (by omega))]
        exact hK.hal t ht
      afit := hK.afit
      aAl := fun t ht (h : K.aq t ≠ 0) => (hK.cAl t ht h).off
      hastr := fun t ht (h : K.aq t ≠ 0) k (hk : k ≤ K.alen t) => by
        have e := toNat_add_of_fits (a := K.aq t) (i := k) (n := K.alen t + 1) (by omega) (hK.afit t ht h)
        show Vst V _ _ ((K.aq t).add k) = K.az t k
        rw [hS'.at1 bd_dg ((hK.cAl t ht h).sub (by omega) (by omega))]
        exact hK.hastr t ht h k hk
      haz := hK.haz
      hanz := hK.hanz
      noG := hK.noG
      noA := hK.noA }
  · exact ⟨hE.ws, fun y (h1 : K.bp.toNat ≤ y.toNat) (h2 : y.toNat < K.bp.toNat + 104) => hE.stk y h1 (by omega),
      fun y h1 h2 => hE.ws _ (hE.gl ⟨0x791ce0, 4⟩ (by simp [d3, globals]) y ⟨h1, h2⟩), hE.nm, hE.lst,
      fun y h1 h2 => hE.env y h1 (by have : y.toNat < K.envp.toNat + 8 * (K.N + 1) := h2; omega), hE.str, hE.al⟩
  · rintro ⟨rax', rcx', rdx', rbx', rsp', rbp', rsi', rdi', r8', r9', r10', r11', r12', r13', r14', r15'⟩ V'
      ⟨hsp, hbx, hbp', h12, h13, -, -, hO⟩
    obtain rfl : rsp' = K.bp + 104#64 := hsp
    obtain rfl : rbx' = K.argv := hbx
    obtain rfl : rbp' = K.init := hbp'
    obtain rfl : r12' = K.fini := h12
    obtain rfl : r13' = K.rtld := h13
    simp only [sk4', e']
    have hO' : ∀ a, ¬ Low K a → ¬ Foot ([] : List Rgn) a →
        V' a = Vst V (K.bp + 104#64) (toBytesLE (lsm_at.add 211) 8) a :=
      fun a hl _ => hO a (fun hf => hl ⟨hf.1, by have h2 : a.toNat < K.bp.toNat + 104 := hf.2; omega⟩)
    refine ⟨hE.rstk hK 104 8 (by decide), ?_, fun fl => h211 _ _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hM'.congr hK hO'⟩⟩
    rw [rd_congr (a := K.bp + 104#64) (n := 8) fun i hi => hO _ (fun hf => by
        have e := tn hK hi (c := 104) (n := 8) (by decide)
        have h2 : ((K.bp + 104#64).add i).toNat < K.bp.toNat + 104 := hf.2
        omega),
      rd_sself hK _ 104 8 _ (by simp only [toBytesLE_length]) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## Together -/

/-- At an exit: the invariant there with a smaller measure, or `FinP` at offset 211. -/
def Nx (K : Ctx) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ InvT K j' n' g' V') ∨ (j' = 211 ∧ FinP K g' V')

theorem nx {ℓ n n' : Nat} {g' : Gprs} {fl : Rflags} {V' : Addr → Byte} (hn : n' < n) (h : InvT K ℓ n' g' V') :
    Nx K n ℓ g' fl V' := Or.inl ⟨n', hn, h⟩

theorem vcAll (hK : K.Ok) (hE : Env K F Wl) (ℓ : Nat) :
    ∀ n g f V, InvT K ℓ n g V → WtC F Wl ℓ (Nx K n) g f V := by
  intro n g f V h
  by_cases h0 : ℓ = 0
  · subst h0; exact vc_0 hK hE h fun _ _ _ _ hn h' => nx (ℓ := 65) hn h'
  by_cases h65 : ℓ = 65
  · subst h65; exact vc_65 hK hE h fun _ _ _ _ hn h' => nx (ℓ := 71) hn h'
  by_cases h71 : ℓ = 71
  · subst h71; exact vc_71 (f := f) hK hE h fun _ _ _ _ hn h' => nx (ℓ := 76) hn h'
  by_cases h76 : ℓ = 76
  · subst h76; exact vc_76 hK hE h fun _ _ _ _ hn h' => nx (ℓ := 120) hn h'
  by_cases h120 : ℓ = 120
  · subst h120
    exact vc_120 hK hE h (fun _ _ _ _ hn h' => nx (ℓ := 120) hn h') fun _ _ _ _ hn h' => nx (ℓ := 131) hn h'
  by_cases h131 : ℓ = 131
  · subst h131; exact vc_131 (f := f) hK hE h fun _ _ _ _ hn h' => nx (ℓ := 136) hn h'
  by_cases h136 : ℓ = 136
  · subst h136; exact vc_136 hK hE h fun _ _ _ _ hn h' => nx (ℓ := 194) hn h'
  by_cases h194 : ℓ = 194
  · subst h194; exact vc_194 (f := f) hK hE h fun _ _ _ _ hn h' => nx (ℓ := 199) hn h'
  by_cases h199 : ℓ = 199
  · subst h199; exact vc_199 hE h fun _ _ _ _ hn h' => nx (ℓ := 206) hn h'
  by_cases h206 : ℓ = 206
  · subst h206; exact vc_206 (f := f) hK hE h fun _ _ _ h' => Or.inr ⟨rfl, h'⟩
  · simp only [InvT, h0, h65, h71, h76, h120, h131, h136, h194, h199, h206, ↓reduceIte] at h

end FV7z.Start
