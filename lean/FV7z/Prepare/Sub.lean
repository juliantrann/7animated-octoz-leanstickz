import FV7z.Lemmas.FnSteps
import FV7z.Prepare.Decode
/-!
# 7-Zip's CPU feature tests, as callees (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

Each of `z7_x86_cpuid`, `z7_x86_cpuid_GetMaxFunc`, `CPU_IsSupported_SSE41`, `CPU_IsSupported_AVX`,
`CPU_IsSupported_AVX2`, called inside the run of a function with a stack frame (`Fn.Call`): from its first byte, with
its return address at `rsp`, the run goes on from its return, where the registers the System V convention saves are
as at the call, the bytes of the footprint are as at the call outside its frame, and what it returns (or stores) is
what the processor's `CPUID` (and `XGETBV`) report, on some CPU of the profile.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-! ## Registers -/

@[simp] theorem set_r0 (g : Gprs) (v : BitVec 64) : g.set (regOf 0) v = { g with rax := v } := rfl
@[simp] theorem set_r1 (g : Gprs) (v : BitVec 64) : g.set (regOf 1) v = { g with rcx := v } := rfl
@[simp] theorem set_r2 (g : Gprs) (v : BitVec 64) : g.set (regOf 2) v = { g with rdx := v } := rfl
@[simp] theorem set_r3 (g : Gprs) (v : BitVec 64) : g.set (regOf 3) v = { g with rbx := v } := rfl
@[simp] theorem set_r4 (g : Gprs) (v : BitVec 64) : g.set (regOf 4) v = { g with rsp := v } := rfl
@[simp] theorem set_r6 (g : Gprs) (v : BitVec 64) : g.set (regOf 6) v = { g with rsi := v } := rfl
@[simp] theorem set_r7 (g : Gprs) (v : BitVec 64) : g.set (regOf 7) v = { g with rdi := v } := rfl
@[simp] theorem set_r8 (g : Gprs) (v : BitVec 64) : g.set (regOf 8) v = { g with r8 := v } := rfl
@[simp] theorem set_4 (g : Gprs) (v : BitVec 64) : g.set 4 v = { g with rsp := v } := rfl
@[simp] theorem set_0 (g : Gprs) (v : BitVec 64) : g.set 0 v = { g with rax := v } := rfl
@[simp] theorem set_1 (g : Gprs) (v : BitVec 64) : g.set 1 v = { g with rcx := v } := rfl
@[simp] theorem set_2 (g : Gprs) (v : BitVec 64) : g.set 2 v = { g with rdx := v } := rfl
@[simp] theorem set_3 (g : Gprs) (v : BitVec 64) : g.set 3 v = { g with rbx := v } := rfl
@[simp] theorem get_r0 (g : Gprs) : g.get (regOf 0) = g.rax := rfl
@[simp] theorem get_r1 (g : Gprs) : g.get (regOf 1) = g.rcx := rfl
@[simp] theorem get_r2 (g : Gprs) : g.get (regOf 2) = g.rdx := rfl
@[simp] theorem get_r3 (g : Gprs) : g.get (regOf 3) = g.rbx := rfl
@[simp] theorem get_r4 (g : Gprs) : g.get (regOf 4) = g.rsp := rfl
@[simp] theorem get_r6 (g : Gprs) : g.get (regOf 6) = g.rsi := rfl
@[simp] theorem get_r7 (g : Gprs) : g.get (regOf 7) = g.rdi := rfl
@[simp] theorem get_r8 (g : Gprs) : g.get (regOf 8) = g.r8 := rfl

@[simp] theorem sw_sw (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

/-- The registers the System V convention saves, as in `X`. -/
def Saved (X Y : State) : Prop :=
  Y.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
    Y.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y.cpu.gpr.r15 = X.cpu.gpr.r15

/-! ## Addresses -/

theorem toNat_sub8 {a : Addr} (h : 8 ≤ a.toNat) : (a - 8).toNat = a.toNat - 8 := by
  rw [BitVec.toNat_sub]; simp; omega

theorem toNat_addn {a : Addr} {i n : Nat} (hi : i < n) (hf : a.toNat + n ≤ 2 ^ 64) : (a.add i).toNat = a.toNat + i :=
  toNat_add_of_fits hi hf

/-- Bytes of two ranges apart. -/
theorem add_ne_add {a b : Addr} {i j n m : Nat} (hi : i < n) (hj : j < m) (ha : a.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + m ≤ 2 ^ 64) (h : a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat) : a.add i ≠ b.add j := by
  intro e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hi ha, toNat_add_of_fits hj hb] at this
  omega

/-- A store's bytes apart from a range leave its bytes as they were. -/
theorem map_Vst_apart {V : Addr → Byte} {a b : Addr} {bs : List Byte} {n : Nat} (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hb : b.toNat + n ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ b.toNat ∨ b.toNat + n ≤ a.toNat) :
    (byteAddrs b n).map (Vst V a bs) = (byteAddrs b n).map V := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hx
  exact Vst_apart bs V a _ fun i hi => (add_ne_add hi hj ha hb h).symm

/-- A store of a word read back. -/
theorem read_Vst_self {V : Addr → Byte} {a : Addr} {w n : Nat} (hw : w = 8 * n) (v : BitVec w)
    (hf : a.toNat + n ≤ 2 ^ 64) : ofBytesLE w ((byteAddrs a n).map (Vst V a (toBytesLE v n))) = v := by
  have := Vst_self (toBytesLE v n) V a (by simpa using hf)
  rw [toBytesLE_length] at this
  rw [this, ofBytesLE_toBytesLE hw]

/-- `Vst` at `a + i` with `a + d`, for `i < n`, inside `a`'s `m` bytes. -/
theorem Vst_off {V : Addr → Byte} {a x : Addr} {d : Nat} {bs : List Byte} {m : Nat} (hm : d + bs.length ≤ m)
    (hx : ∀ i < m, x ≠ a.add i) : Vst V (a.add d) bs x = V x :=
  Vst_apart bs V _ x fun i hi => by rw [addr_add_add]; exact hx (d + i) (by omega)

theorem add_sub_lit (a : Addr) {n d : Nat} (h : d ≤ n) : a.add n - BitVec.ofNat 64 d = a.add (n - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem add_sub8 (a : Addr) {n m : Nat} (h : n = m + 8) : a.add n - 8 = a.add m := by
  subst h; have := add_sub_lit a (n := m + 8) (d := 8) (by omega); rwa [Nat.add_sub_cancel] at this

theorem sub_add_self (a : Addr) (n : Nat) : a = (a - BitVec.ofNat 64 n).add n := by
  simp [Addr.add, BitVec.sub_add_cancel]

theorem add_add8 (a : Addr) (n : Nat) : a.add n + 8 = a.add (n + 8) := by
  rw [← addr_add_add]; rfl

theorem add_ne_same {p : Addr} {n a b : Nat} (hf : p.toNat + n ≤ 2 ^ 64) (ha : a < n) (hb : b < n) (h : a ≠ b) :
    p.add a ≠ p.add b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits ha hf, toNat_add_of_fits hb hf] at this
  omega

/-- Bit `n` of `x` is set, if `(x >> n) & 1` is not 0. -/
theorem bit_of (x : BitVec 32) {n : Nat} (h : (x >>> n &&& 1#32) ≠ 0) : x.getLsbD n = true := by
  cases hb : x.getLsbD n
  case true => rfl
  exfalso; apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  rcases i with _ | i
  · simp [hb]
  · simp

theorem bits_and (a b : BitVec 32) (h : (a &&& b &&& 1#32) ≠ 0) : a.getLsbD 0 = true ∧ b.getLsbD 0 = true := by
  have := bit_of (a &&& b) (n := 0) (by simpa using h)
  simpa [BitVec.getLsbD_and] using this

/-- Bits 1 and 2 of `x` (SSE and AVX state) are set, if `((x >> 2) & (x >> 1)) & 1` is not 0. -/
theorem enabled_of (x : BitVec 64) (h : (x.setWidth 32 >>> 2 &&& x.setWidth 32 >>> 1 &&& 1#32) ≠ 0) :
    x &&& 6 = 6 := by
  have ⟨h2, h1⟩ := bits_and _ _ h
  simp at h1 h2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  rcases i with _ | _ | _ | i
  · simp
  · simp [h1]
  · simp [h2]
  · have : (6#64).getLsbD (i + 3) = false := by
      rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 6 < 2 ^ 3)
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp
    simp [this]

theorem Saved.trans {X Y Z : State} (h₁ : Saved X Y) (h₂ : Saved Y Z) : Saved X Z := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h₂
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- What `CPUID` reports, leaf `a`, subleaf 0, on CPU `cpu`, in the four words at `p` of `V`. -/
def Reports (prof : Profile) (cpu : Nat) (a : BitVec 32) (V : Addr → Byte) (p : Addr) : Prop :=
  let r := prof.cpuid cpu a 0
  ofBytesLE 32 ((byteAddrs p 4).map V) = r.eax ∧ ofBytesLE 32 ((byteAddrs (Addr.add p 4) 4).map V) = r.ebx ∧
    ofBytesLE 32 ((byteAddrs (Addr.add p 8) 4).map V) = r.ecx ∧ ofBytesLE 32 ((byteAddrs (Addr.add p 12) 4).map V) = r.edx

/-- `z7_x86_cpuid(p, func)`: `CPUID` leaf `func`, subleaf 0, into the 16 bytes at `p`. -/
theorem sub_cpuid (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V) {e₁ : Addr}
    (hin : CodeIn L e₁ cpuid) (hrip : X.cpu.rip = e₁)
    (hsl : ∀ i < 8, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hbuf : ∀ i < 16, Foot (ws k W s₀) (Addr.add X.cpu.gpr.rdi i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (h8 : 8 ≤ X.cpu.gpr.rsp.toNat) (hap : X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdf : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte,
      (∀ x, (∀ i < 8, x ≠ Addr.add (X.cpu.gpr.rsp - 8) i) → (∀ i < 16, x ≠ Addr.add X.cpu.gpr.rdi i) → V' x = V x) →
      (∃ cpu, cpu < max prof.cpus 1 ∧ Reports prof cpu (X.cpu.gpr.rsi.setWidth 32) V' X.cpu.gpr.rdi) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : cpuid.length = 24 := cpuid_length
  have hr0 : X.cpu.rip = e₁.add 0 := by rw [addr_add_zero]; exact hrip
  refine c.s_endbr hK hA hin (by omega) hr0 (cpuid_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_push hK1 hA1 hin (by omega) hr1 (cpuid_4 _) (by simpa [hg1] using hsl) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_mov_rr32 hK2 hA2 hin (by omega) hr2 (cpuid_5 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_xor_rr32 hK3 hA3 hin (by omega) hr3 (cpuid_7 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  refine c.s_cpuid hK4 hA4 hin (by omega) hr4 (cpuid_9 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, cpu, hcpu, hg5⟩
  have ha4 : Y4.cpu.gpr.rax.setWidth 32 = X.cpu.gpr.rsi.setWidth 32 := by simp [hg4, hg3, hg2, hg1, rv]
  have hc4 : Y4.cpu.gpr.rcx.setWidth 32 = 0 := by simp [hg4, rv]
  simp only [ha4, hc4] at hg5
  -- the words `CPUID` reported
  generalize hq : prof.cpuid cpu (X.cpu.gpr.rsi.setWidth 32) 0 = q at hg5
  have g5 : Y5.cpu.gpr = { X.cpu.gpr with
      rsp := X.cpu.gpr.rsp - 8, rax := q.eax.setWidth 64, rbx := q.ebx.setWidth 64, rcx := q.ecx.setWidth 64,
      rdx := q.edx.setWidth 64 } := by
    rw [hg5, hg4, hg3, hg2, hg1]; simp [rv]
  clear hg5 hg4 hg3 hg2 ha4 hc4
  -- `mov [rdi + 4], ebx`
  refine c.s_mov_mr hK5 hA5 hin (by omega) hr5 (Or.inl rfl) (cpuid_11 _) (fun i hi => by
    show Foot _ (Addr.add (Addr.add Y5.cpu.gpr.rdi 4) i)
    rw [g5, addr_add_add]; exact hbuf _ (by omega)) ?_
  rw [show eaD Y5 7 4 = Addr.add X.cpu.gpr.rdi 4 by simp [eaD, g5]; rfl,
    show rv Y5 32 3 = q.ebx by simp [rv, g5]]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  -- `pop rbx`
  refine c.s_pop hK6 hA6 hin (by omega) hr6 (cpuid_14 _) (fun i hi => by
    rw [hg6, g5]; exact c.hws _ (hsl i hi)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hsp8 := toNat_sub8 h8
  have hd4 : (Addr.add X.cpu.gpr.rdi 4).toNat = X.cpu.gpr.rdi.toNat + 4 := toNat_addn (by omega) hdf
  have hd8 : (Addr.add X.cpu.gpr.rdi 8).toNat = X.cpu.gpr.rdi.toNat + 8 := toNat_addn (by omega) hdf
  have hd12 : (Addr.add X.cpu.gpr.rdi 12).toNat = X.cpu.gpr.rdi.toNat + 12 := toNat_addn (by omega) hdf
  have hbx : ofBytesLE 64 ((byteAddrs Y6.cpu.gpr.rsp 8).map (Vst (Vst V (Y1.cpu.gpr.rsp - 8)
      (toBytesLE (Y1.cpu.gpr.get (regOf 3)) 8)) (Addr.add X.cpu.gpr.rdi 4) (toBytesLE q.ebx (32 / 8)))) =
      X.cpu.gpr.rbx := by
    rw [show Y6.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 by rw [hg6, g5], hg1,
      map_Vst_apart (by simp; omega) (by omega) (by simp; omega), get_r3,
      read_Vst_self (by rfl) _ (by omega)]
  rw [hbx] at hg7
  have g7 : Y7.cpu.gpr = { X.cpu.gpr with
      rax := q.eax.setWidth 64, rcx := q.ecx.setWidth 64, rdx := q.edx.setWidth 64 } := by
    rw [hg7, hg6, g5]; simp [BitVec.sub_add_cancel]
  clear hg7 hg6 hbx
  -- `mov [rdi], eax`
  refine c.s_mov_mr hK7 hA7 hin (by omega) hr7 (Or.inl rfl) (cpuid_15 _) (fun i hi => by
    show Foot _ (Addr.add (Y7.cpu.gpr.rdi + BitVec.ofNat 64 0) i)
    rw [g7]; simpa using hbuf i (by omega)) ?_
  rw [show eaD Y7 7 0 = X.cpu.gpr.rdi by simp [eaD, g7], show rv Y7 32 0 = q.eax by simp [rv, g7]]
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  -- `mov [rdi + 8], ecx`
  refine c.s_mov_mr hK8 hA8 hin (by omega) hr8 (Or.inl rfl) (cpuid_17 _) (fun i hi => by
    show Foot _ (Addr.add (Addr.add Y8.cpu.gpr.rdi 8) i)
    rw [hg8, g7, addr_add_add]; exact hbuf _ (by omega)) ?_
  rw [show eaD Y8 7 8 = Addr.add X.cpu.gpr.rdi 8 by simp [eaD, hg8, g7]; rfl,
    show rv Y8 32 1 = q.ecx by simp [rv, hg8, g7]]
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  -- `mov [rdi + 12], edx`
  refine c.s_mov_mr hK9 hA9 hin (by omega) hr9 (Or.inl rfl) (cpuid_20 _) (fun i hi => by
    show Foot _ (Addr.add (Addr.add Y9.cpu.gpr.rdi 12) i)
    rw [hg9, hg8, g7, addr_add_add]; exact hbuf _ (by omega)) ?_
  rw [show eaD Y9 7 12 = Addr.add X.cpu.gpr.rdi 12 by simp [eaD, hg9, hg8, g7]; rfl,
    show rv Y9 32 2 = q.edx by simp [rv, hg9, hg8, g7]]
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have g10 : Y10.cpu.gpr = Y7.cpu.gpr := by rw [hg10, hg9, hg8]
  clear hg10 hg9 hg8
  -- the bytes as they are now
  generalize hV1 : Vst V (Y1.cpu.gpr.rsp - 8) (toBytesLE (Y1.cpu.gpr.get (regOf 3)) 8) = V1 at hA10
  have hfr : ∀ x, (∀ i < 8, x ≠ Addr.add (X.cpu.gpr.rsp - 8) i) → (∀ i < 16, x ≠ Addr.add X.cpu.gpr.rdi i) →
      Vst (Vst (Vst (Vst V1 (Addr.add X.cpu.gpr.rdi 4) (toBytesLE q.ebx (32 / 8))) X.cpu.gpr.rdi
        (toBytesLE q.eax (32 / 8))) (Addr.add X.cpu.gpr.rdi 8) (toBytesLE q.ecx (32 / 8)))
        (Addr.add X.cpu.gpr.rdi 12) (toBytesLE q.edx (32 / 8)) x = V x := by
    intro x hx hy
    rw [Vst_off (by simp) hy, Vst_off (by simp) hy, Vst_apart _ _ _ x fun i hi => hy i (by simp at hi; omega),
      Vst_off (by simp) hy, ← hV1, hg1]
    exact Vst_apart _ _ _ x fun i hi => hx i (by simpa using hi)
  -- `ret`
  have hsp10 : Y10.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [g10, g7]
  refine c.s_ret hK10 hA10 hin (by omega) hr10 (cpuid_23 _) (fun i hi => by
    rw [hsp10]; exact hrd i hi) hin₂ h₂ (by
      rw [hsp10, ← hret]
      congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      refine hfr _ (fun i' hi' => add_ne_add hi hi' (by omega) (by omega) (by omega))
        (fun i' hi' => add_ne_add hi hi' (by omega) hdf (by omega))) ?_
  intro Y t' hKY hAY ⟨hrY, hgY⟩
  refine k' _ hfr ⟨cpu, hcpu, ?_⟩ Y t' hKY hAY ⟨hrY, by rw [hgY, hsp10]; rfl, ?_⟩
  · simp only [Reports, hq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_Vst_apart (by simp; omega) (by omega) (by simp; omega),
        map_Vst_apart (by simp; omega) (by omega) (by simp; omega), read_Vst_self (by rfl) _ (by omega)]
    · rw [map_Vst_apart (by simp; omega) (by simp; omega) (by simp; omega),
        map_Vst_apart (by simp; omega) (by simp; omega) (by simp; omega),
        map_Vst_apart (by simp; omega) (by simp; omega) (by simp; omega), read_Vst_self (by rfl) _ (by simp; omega)]
    · rw [map_Vst_apart (by simp; omega) (by simp; omega) (by simp; omega), read_Vst_self (by rfl) _ (by simp; omega)]
    · rw [read_Vst_self (by rfl) _ (by simp; omega)]
  · simp [Saved, hgY, g10, g7]


/-- The shape of `CPU_IsSupported_SSE41`, `CPU_IsSupported_SSSE3`, `CPU_IsSupported_AES` (`C/CpuArch.c`), at `e`: a
call of `z7_x86_cpuid(p, 1)` into a 16-byte buffer on the stack, a test of bit `n` of `ECX`, the canary checked. The
three are the same bytes but for the bit and the calls' displacements. -/
structure BitShape (code : List Byte) (e : Addr) (n : Nat) : Prop where
  len : code.length = 73
  n_ok : n ∈ [1, 2, 5, 9, 19, 25, 27, 28, 29]
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .sub 64 [gr 64 4, .imm 64 40] 4)
  d8 : ∀ feat, Dec feat code 8 (FV7z.mk .mov 32 [gr 32 6, .imm 32 1] 5)
  d13 : ∀ feat, Dec feat code 13 (FV7z.mk .mov 64 [gr 64 0, .mem (mfs 40 64)] 9)
  d22 : ∀ feat, Dec feat code 22 (FV7z.mk .mov 64 [.mem (mbd 4 24 64), gr 64 0] 5)
  d27 : ∀ feat, Dec feat code 27 (FV7z.mk .xor 32 [gr 32 0, gr 32 0] 2)
  d29 : ∀ feat, Dec feat code 29 (FV7z.mk .mov 64 [gr 64 7, gr 64 4] 3)
  d32 : ∃ rel, (∀ feat, Dec feat code 32 (FV7z.mk .call 64 [.rel rel] 5)) ∧
    e.add (32 + 5) + BitVec.ofNat 64 rel = 0x424290
  d37 : ∀ feat, Dec feat code 37 (FV7z.mk .mov 32 [gr 32 0, .mem (mbd 4 8 32)] 4)
  d41 : ∀ feat, Dec feat code 41 (FV7z.mk .shr 32 [gr 32 0, .imm 8 n] 3)
  d44 : ∀ feat, Dec feat code 44 (FV7z.mk .and 32 [gr 32 0, .imm 32 1] 3)
  d47 : ∀ feat, Dec feat code 47 (FV7z.mk .mov 64 [gr 64 2, .mem (mbd 4 24 64)] 5)
  d52 : ∀ feat, Dec feat code 52 (FV7z.mk .xor 64 [gr 64 2, .mem (mfs 40 64)] 9)
  d61 : ∀ feat, Dec feat code 61 (FV7z.mk (.jcc 5) 64 [.rel 5] 2)
  d63 : ∀ feat, Dec feat code 63 (FV7z.mk .add 64 [gr 64 4, .imm 64 40] 4)
  d67 : ∀ feat, Dec feat code 67 (FV7z.mk .ret 64 [] 1)

/-- A function of the shape `BitShape code eb n` (`CPU_IsSupported_SSE41()`, …): not 0 only if some CPU reports bit
`n` of `CPUID.01H:ECX`. Its frame and its callee's are the 56 bytes below `rsp`; the canary `fs:[40]` lies apart from
them. -/
theorem sub_bit (c : Call prof k W R pre post e L s₀ ra o) {code : List Byte} {eb : Addr} {n : Nat}
    (sh : BitShape code eb n) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L eb code) (hinC : CodeIn L 0x424290 cpuid) (hrip : X.cpu.rip = eb)
    (hws : ∀ i < 56, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 56) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h56 : 56 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 56 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 56, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 56) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y ∧
        (Y.cpu.gpr.rax.setWidth 32 ≠ 0 → prof.reports 1 0 (·.ecx) n)) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : code.length = 73 := sh.len
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 56 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 56 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 56 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 64 ≤ 2 ^ 64 := by omega
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 56 ≤ cn.toNat := by omega
  -- `endbr64`, `sub rsp, 40`, `mov esi, 1`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (sh.d0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (sh.d4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 16 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  refine c.s_mov_ri32 hK2 hA2 hin (by omega) hr2 (sh.d8 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  -- `mov rax, fs:[40]`
  have hc3 : eaF Y3 40 = cn := by rw [← hcd]; simp only [eaF, hK3.seg]; rfl
  refine c.s_mov_fs hK3 hA3 hin (by omega) hr3 (sh.d13 _) (fun i hi => by rw [hc3]; exact hcn i hi) ?_
  rw [hc3]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg4
  have hsp4 : Y4.cpu.gpr.rsp = Addr.add p 16 := by simp [hg4, hg3, hsp2]
  -- `mov [rsp + 24], rax`
  have e4 : eaD Y4 4 24 = Addr.add p 40 := by simp only [eaD, get_r4, hsp4]; exact addr_add_add p 16 24
  refine c.s_mov_mr hK4 hA4 hin (by omega) hr4 (Or.inr rfl) (sh.d22 _) (fun i hi => by
    rw [e4, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e4, show rv Y4 64 0 = cv by simp [rv, hg4]]
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  -- `xor eax, eax`, `mov rdi, rsp`
  refine c.s_xor_rr32 hK5 hA5 hin (by omega) hr5 (sh.d27 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_mov_rr64 hK6 hA6 hin (by omega) hr6 (sh.d29 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 16 := by simp [hg7, hg6, hg5, hsp4]
  -- `call z7_x86_cpuid`
  obtain ⟨rel, hd32, hc32⟩ := sh.d32
  refine c.s_call hK7 hA7 hin (by omega) hr7 (hd32 _) hinC (by rw [cpuid_length]; omega) hc32
    (fun i hi => by rw [hsp7, add_sub8 p (m := 8) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp7, add_sub8 p (m := 8) rfl]
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 8 := by rw [hg8, set_4]
  have hdi8 : Y8.cpu.gpr.rdi = Addr.add p 16 := by simp [hg8, hg7, hg6, hg5, hsp4]
  have hsi8 : Y8.cpu.gpr.rsi.setWidth 32 = 1 := by simp [hg8, hg7, hg6, hg5, hg4, hg3]
  have hp8 : (Addr.add p 8).toNat = p.toNat + 8 := toNat_addn (by omega) hfit
  have hp16 : (Addr.add p 16).toNat = p.toNat + 16 := toNat_addn (by omega) hfit
  refine sub_cpuid c hK8 hA8 hinC (by rw [hr8]) (fun i hi => by
      rw [hsp8, add_sub8 p (m := 0) rfl, addr_add_zero]; exact hws i (by omega))
    (fun i hi => by rw [hdi8, addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp8, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [hsp8]; omega) (by rw [hsp8, hdi8]; omega) (by rw [hdi8]; omega) hin (j₂ := 37) (by omega)
    (by rw [hsp8]; exact read_Vst_self (by rfl) _ (by omega)) ?_
  intro V9 hfr9 ⟨cpu, hcpu, hrep⟩ Y9 t9 hK9 hA9 ⟨hr9, hsp9, hsv9⟩
  rw [hsi8, hdi8] at hrep
  rw [hsp8, add_add8] at hsp9
  rw [hsp8, add_sub8 p (m := 0) rfl, addr_add_zero, hdi8] at hfr9
  -- the bytes now and at the call
  have hfrV : ∀ x, (∀ i < 56, x ≠ Addr.add p i) → V9 x = V x := by
    intro x hx
    rw [hfr9 x (fun i hi => by simpa using hx i (by omega)) (fun i hi => by
      rw [addr_add_add]; exact hx _ (by omega))]
    rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  -- `mov eax, [rsp + 8]`
  have e9 : eaD Y9 4 8 = Addr.add (Addr.add p 16) 8 := by simp only [eaD, get_r4, hsp9]; rfl
  refine c.s_mov_rm hK9 hA9 hin (by omega) hr9 (Or.inl rfl) (sh.d37 _) (fun i hi => by
    rw [e9, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
  rw [e9, hrep.2.2.1]
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  -- `shr eax, n`, `and eax, 1`
  refine c.s_shr_ri32 hK10 hA10 hin (by omega) hr10 sh.n_ok (sh.d41 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  refine c.s_and_ri32 hK11 hA11 hin (by omega) hr11 (sh.d44 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
  have hax12 : Y12.cpu.gpr.rax.setWidth 32 = ((prof.cpuid cpu 1 0).ecx >>> n) &&& 1#32 := by
    simp only [hg12, hg11, hg10, rv, set_r0, get_r0, sw_sw]
  have hsp12 : Y12.cpu.gpr.rsp = Addr.add p 16 := by simp [hg12, hg11, hg10, hsp9]
  -- `mov rdx, [rsp + 24]`: the canary as stored
  have e12 : eaD Y12 4 24 = Addr.add p 40 := by simp only [eaD, get_r4, hsp12]; exact addr_add_add p 16 24
  refine c.s_mov_rm hK12 hA12 hin (by omega) hr12 (Or.inr rfl) (sh.d47 _) (fun i hi => by
    rw [e12, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
  have hcs : ofBytesLE 64 ((byteAddrs (Addr.add p 40) 8).map V9) = cv := by
    rw [show (byteAddrs (Addr.add p 40) 8).map V9 = (byteAddrs (Addr.add p 40) 8).map
        (Vst V (Addr.add p 40) (toBytesLE cv (64 / 8))) from List.map_congr_left fun x hx => by
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      rw [addr_add_add]
      rw [hfr9 _ (fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) (fun i' hi' => by
        rw [addr_add_add]; exact add_ne_same hfit (by omega) (by omega) (by omega))]
      exact Vst_apart _ _ _ _ fun i' hi' => by
        rw [addr_add_add]; exact add_ne_same hfit (by omega) (by simp at hi'; omega) (by simp at hi'; omega)]
    exact read_Vst_self (by rfl) _ (by rw [toNat_addn (n := 64) (by omega) hfit]; omega)
  rw [e12, hcs]
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  -- `xor rdx, fs:[40]`: 0
  have hc13 : eaF Y13 40 = cn := by rw [← hcd]; simp only [eaF, hK13.seg]; rfl
  refine c.s_xor_fs hK13 hA13 hin (by omega) hr13 (sh.d52 _) (fun i hi => by rw [hc13]; exact hcn i hi) ?_
  have hcr : ofBytesLE 64 ((byteAddrs cn 8).map V9) = cv := by
    rw [← hcv]; congr 1
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact hfrV _ fun i' hi' => add_ne_add hi hi' hcf (by omega) (by omega)
  rw [hc13, hcr]
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, hz14⟩
  have hzf : Y14.cpu.rflags.zf = true := by rw [hz14, hg13]; simp [BitVec.setWidth_eq]
  -- `jne` not taken
  refine c.s_jcc hK14 hA14 hin (by omega) hr14 (sh.d61 _) (tgt := 68) rfl (by omega)
    (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  -- `add rsp, 40`, `ret`
  refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (sh.d63 _) ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    simp only [hg16, hg15, hg14, hg13, set_r4, get_r4, set_r2]
    rw [hsp12, hsp]; exact addr_add_add p 16 40
  refine c.s_ret hK16 hA16 hin (by omega) hr16 (sh.d67 _) (fun i hi => by rw [hsp16]; exact hrd i hi) hin₂ h₂
    (by
      rw [hsp16, ← hret]; congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      rw [hsp, addr_add_add]
      exact hfrV _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) ?_
  rintro Y t' hKY hAY ⟨hrY, hgY⟩
  refine k' V9 (fun x hx => hfrV x hx) Y t' hKY hAY ⟨hrY, by rw [hgY, set_4, hsp16], ?_, fun h => ?_⟩
  · refine Saved.trans ?_ (Saved.trans hsv9 ?_)
    · simp [Saved, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]
    · simp [Saved, hgY, hg16, hg15, hg14, hg13, hg12, hg11, hg10]
  · have hax : Y.cpu.gpr.rax.setWidth 32 = Y12.cpu.gpr.rax.setWidth 32 := by
      simp [hgY, hg16, hg15, hg14, hg13]
    rw [hax, hax12] at h
    exact ⟨cpu, hcpu, bit_of _ h⟩

theorem sse41_shape : BitShape sse41 0x424390 19 :=
  ⟨sse41_length, by decide, sse41_0, sse41_4, sse41_8, sse41_13, sse41_22, sse41_27, sse41_29, ⟨_, sse41_32, by decide⟩, sse41_37, sse41_41, sse41_44, sse41_47, sse41_52, sse41_61, sse41_63, sse41_67⟩
theorem ssse3_shape : BitShape ssse3 0x424340 9 :=
  ⟨ssse3_length, by decide, ssse3_0, ssse3_4, ssse3_8, ssse3_13, ssse3_22, ssse3_27, ssse3_29, ⟨_, ssse3_32, by decide⟩, ssse3_37, ssse3_41, ssse3_44, ssse3_47, ssse3_52, ssse3_61, ssse3_63, ssse3_67⟩
theorem aes_shape : BitShape aes 0x4242f0 25 :=
  ⟨aes_length, by decide, aes_0, aes_4, aes_8, aes_13, aes_22, aes_27, aes_29, ⟨_, aes_32, by decide⟩, aes_37, aes_41, aes_44, aes_47, aes_52, aes_61, aes_63, aes_67⟩


/-- `CPU_IsSupported_AVX()`: not 0 only if some CPU reports `CPUID.01H:ECX.AVX[28]` and `OSXSAVE[27]` and the kernel
enabled the SSE and AVX state in `XCR0` (`XGETBV` runs only after `OSXSAVE`, so it does not fault). -/
theorem sub_avx (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hpc : prof.Consistent) (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L 0x424440 avx) (hinC : CodeIn L 0x424290 cpuid) (hrip : X.cpu.rip = 0x424440)
    (hws : ∀ i < 56, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 56) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h56 : 56 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 56 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 56, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 56) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y ∧
        (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
          prof.reports 1 0 (·.ecx) 28 ∧ prof.reports 1 0 (·.ecx) 27 ∧ prof.enabled xcr0Avx)) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : avx.length = 101 := avx_length
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 56 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 56 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 56 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 64 ≤ 2 ^ 64 := by omega
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 56 ≤ cn.toNat := by omega
  -- `endbr64`, `sub rsp, 40`, `mov esi, 1`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (avx_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (avx_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 16 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  refine c.s_mov_ri32 hK2 hA2 hin (by omega) hr2 (avx_8 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  -- `mov rax, fs:[40]`
  have hc3 : eaF Y3 40 = cn := by rw [← hcd]; simp only [eaF, hK3.seg]; rfl
  refine c.s_mov_fs hK3 hA3 hin (by omega) hr3 (avx_13 _) (fun i hi => by rw [hc3]; exact hcn i hi) ?_
  rw [hc3]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg4
  have hsp4 : Y4.cpu.gpr.rsp = Addr.add p 16 := by simp [hg4, hg3, hsp2]
  -- `mov [rsp + 24], rax`
  have e4 : eaD Y4 4 24 = Addr.add p 40 := by simp only [eaD, get_r4, hsp4]; exact addr_add_add p 16 24
  refine c.s_mov_mr hK4 hA4 hin (by omega) hr4 (Or.inr rfl) (avx_22 _) (fun i hi => by
    rw [e4, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e4, show rv Y4 64 0 = cv by simp [rv, hg4]]
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  -- `xor eax, eax`, `mov rdi, rsp`
  refine c.s_xor_rr32 hK5 hA5 hin (by omega) hr5 (avx_27 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_mov_rr64 hK6 hA6 hin (by omega) hr6 (avx_29 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 16 := by simp [hg7, hg6, hg5, hsp4]
  -- `call z7_x86_cpuid`
  refine c.s_call hK7 hA7 hin (by omega) hr7 (avx_32 _) hinC (by rw [cpuid_length]; omega) (by decide)
    (fun i hi => by rw [hsp7, add_sub8 p (m := 8) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp7, add_sub8 p (m := 8) rfl]
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 8 := by rw [hg8, set_4]
  have hdi8 : Y8.cpu.gpr.rdi = Addr.add p 16 := by simp [hg8, hg7, hg6, hg5, hsp4]
  have hsi8 : Y8.cpu.gpr.rsi.setWidth 32 = 1 := by simp [hg8, hg7, hg6, hg5, hg4, hg3]
  have hp8 : (Addr.add p 8).toNat = p.toNat + 8 := toNat_addn (by omega) hfit
  have hp16 : (Addr.add p 16).toNat = p.toNat + 16 := toNat_addn (by omega) hfit
  refine sub_cpuid c hK8 hA8 hinC (by rw [hr8]) (fun i hi => by
      rw [hsp8, add_sub8 p (m := 0) rfl, addr_add_zero]; exact hws i (by omega))
    (fun i hi => by rw [hdi8, addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp8, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [hsp8]; omega) (by rw [hsp8, hdi8]; omega) (by rw [hdi8]; omega) hin (j₂ := 37) (by omega)
    (by rw [hsp8]; exact read_Vst_self (by rfl) _ (by omega)) ?_
  intro V9 hfr9 ⟨cpu, hcpu, hrep⟩ Y9 t9 hK9 hA9 ⟨hr9, hsp9, hsv9⟩
  rw [hsi8, hdi8] at hrep
  rw [hsp8, add_add8] at hsp9
  rw [hsp8, add_sub8 p (m := 0) rfl, addr_add_zero, hdi8] at hfr9
  -- the bytes now and at the call
  have hfrV : ∀ x, (∀ i < 56, x ≠ Addr.add p i) → V9 x = V x := by
    intro x hx
    rw [hfr9 x (fun i hi => by simpa using hx i (by omega)) (fun i hi => by
      rw [addr_add_add]; exact hx _ (by omega))]
    rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  -- the canary check and the return, from both paths
  have hsv8 : Saved X Y8 := by simp [Saved, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]
  have tail : ∀ Y t', KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V9 →
      Y.cpu.rip = (0x424440 : Addr).add 75 → Y.cpu.gpr.rsp = Addr.add p 16 → Saved Y9 Y →
      (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
        prof.reports 1 0 (·.ecx) 28 ∧ prof.reports 1 0 (·.ecx) 27 ∧ prof.enabled xcr0Avx) →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro Y12 t12 hK12 hA12 hr12 hsp12 hsv12 hax12
    -- `mov rsi, [rsp + 24]`: the canary as stored
    have e12 : eaD Y12 4 24 = Addr.add p 40 := by simp only [eaD, get_r4, hsp12]; exact addr_add_add p 16 24
    refine c.s_mov_rm hK12 hA12 hin (by omega) hr12 (Or.inr rfl) (avx_75 _) (fun i hi => by
      rw [e12, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    have hcs : ofBytesLE 64 ((byteAddrs (Addr.add p 40) 8).map V9) = cv := by
      rw [show (byteAddrs (Addr.add p 40) 8).map V9 = (byteAddrs (Addr.add p 40) 8).map
          (Vst V (Addr.add p 40) (toBytesLE cv (64 / 8))) from List.map_congr_left fun x hx => by
        obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
        rw [addr_add_add]
        rw [hfr9 _ (fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) (fun i' hi' => by
          rw [addr_add_add]; exact add_ne_same hfit (by omega) (by omega) (by omega))]
        exact Vst_apart _ _ _ _ fun i' hi' => by
          rw [addr_add_add]; exact add_ne_same hfit (by omega) (by simp at hi'; omega) (by simp at hi'; omega)]
      exact read_Vst_self (by rfl) _ (by rw [toNat_addn (n := 64) (by omega) hfit]; omega)
    rw [e12, hcs]
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    -- `xor rsi, fs:[40]`: 0
    have hc13 : eaF Y13 40 = cn := by rw [← hcd]; simp only [eaF, hK13.seg]; rfl
    refine c.s_xor_fs hK13 hA13 hin (by omega) hr13 (avx_80 _) (fun i hi => by rw [hc13]; exact hcn i hi) ?_
    have hcr : ofBytesLE 64 ((byteAddrs cn 8).map V9) = cv := by
      rw [← hcv]; congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      exact hfrV _ fun i' hi' => add_ne_add hi hi' hcf (by omega) (by omega)
    rw [hc13, hcr]
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, hz14⟩
    have hzf : Y14.cpu.rflags.zf = true := by rw [hz14, hg13]; simp [BitVec.setWidth_eq]
    -- `jne` not taken
    refine c.s_jcc hK14 hA14 hin (by omega) hr14 (avx_89 _) (tgt := 96) rfl (by omega)
      (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    -- `add rsp, 40`, `ret`
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (avx_91 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      simp only [hg16, hg15, hg14, hg13, set_r4, get_r4, set_r6]
      rw [hsp12, hsp]; exact addr_add_add p 16 40
    refine c.s_ret hK16 hA16 hin (by omega) hr16 (avx_95 _) (fun i hi => by rw [hsp16]; exact hrd i hi) hin₂ h₂
      (by
        rw [hsp16, ← hret]; congr 1
        apply List.map_congr_left
        intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
        rw [hsp, addr_add_add]
        exact hfrV _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    refine k' V9 (fun x hx => hfrV x hx) Y t' hKY hAY ⟨hrY, by rw [hgY, set_4, hsp16], ?_, fun h => ?_⟩
    · refine Saved.trans hsv8 (Saved.trans hsv9 (Saved.trans hsv12 ?_))
      simp [Saved, hgY, hg16, hg15, hg14, hg13]
    · have hax : Y.cpu.gpr.rax.setWidth 32 = Y12.cpu.gpr.rax.setWidth 32 := by
        simp [hgY, hg16, hg15, hg14, hg13]
      rw [hax] at h
      exact hax12 h
  -- `mov eax, [rsp + 8]`: `ECX` of leaf 1
  have e9 : eaD Y9 4 8 = Addr.add (Addr.add p 16) 8 := by simp only [eaD, get_r4, hsp9]; rfl
  refine c.s_mov_rm hK9 hA9 hin (by omega) hr9 (Or.inl rfl) (avx_37 _) (fun i hi => by
    rw [e9, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
  rw [e9, hrep.2.2.1]
  generalize hq : prof.cpuid cpu 1 0 = q
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  -- `mov edx, eax`, `shr eax, 27`, `shr edx, 28`, `and edx, eax`, `xor eax, eax`, `and edx, 1`
  refine c.s_mov_rr32 hK10 hA10 hin (by omega) hr10 (avx_41 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  refine c.s_shr_ri32 hK11 hA11 hin (by omega) hr11 (by decide) (avx_43 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  refine c.s_shr_ri32 hK12 hA12 hin (by omega) hr12 (by decide) (avx_46 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  refine c.s_and_rr32 hK13 hA13 hin (by omega) hr13 (avx_49 _) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  refine c.s_xor_rr32 hK14 hA14 hin (by omega) hr14 (avx_51 _) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  refine c.s_and_ri32 hK15 hA15 hin (by omega) hr15 (avx_53 _) ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16, hz16⟩
  have hdx : rv Y15 32 2 = (q.ecx >>> 28) &&& (q.ecx >>> 27) := by
    simp only [hg15, hg14, hg13, hg12, hg11, hg10, rv, set_r0, set_r2, get_r0, get_r2, sw_sw]
  have hsp16 : Y16.cpu.gpr.rsp = Addr.add p 16 := by
    simp only [hg16, hg15, hg14, hg13, hg12, hg11, hg10, set_r0, set_r2, hsp9]
  have hsv16 : Saved Y9 Y16 := by simp [Saved, hg16, hg15, hg14, hg13, hg12, hg11, hg10]
  refine c.s_jcc hK16 hA16 hin (by omega) hr16 (avx_56 _) (tgt := 75) rfl (by omega) (fun h => ?_) fun h => ?_
  · -- `je`: 0
    rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
    refine tail Y17 t17 hK17 hA17 hr17 (by rw [hg17, hsp16]) (by rw [Saved, hg17]; exact hsv16) fun h0 => ?_
    exfalso; apply h0
    simp [hg17, hg16, hg15]
  · -- bits 28 and 27 set: `XGETBV`
    have hb : (q.ecx >>> 28 &&& q.ecx >>> 27 &&& 1#32) ≠ 0 := by
      intro h0
      simp only [Rflags.cond, hz16, hdx, h0] at h
      simp at h
    obtain ⟨b28, b27⟩ := bits_and _ _ hb
    simp only [BitVec.getLsbD_ushiftRight, Nat.add_zero] at b28 b27
    have r28 : prof.reports 1 0 (·.ecx) 28 := ⟨cpu, hcpu, by rw [hq]; simpa using b28⟩
    have r27 : prof.reports 1 0 (·.ecx) 27 := ⟨cpu, hcpu, by rw [hq]; simpa using b27⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hpc.osxsave r27)
    rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
    refine c.s_mov_rr32 hK17 hA17 hin (by omega) hr17 (avx_58 _) ?_
    rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
    refine c.s_xgetbv hK18 hA18 hin (by omega) hr18 (avx_60 _) hx (by simp [hg18, hg17, hg16, hg15, rv]) ?_
    rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
    refine c.s_mov_rr32 hK19 hA19 hin (by omega) hr19 (avx_63 _) ?_
    rintro Y20 t20 hK20 hA20 ⟨hr20, hg20⟩
    refine c.s_shr_ri32 hK20 hA20 hin (by omega) hr20 (by decide) (avx_65 _) ?_
    rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
    refine c.s_shr_ri32 hK21 hA21 hin (by omega) hr21 (by decide) (avx_68 _) ?_
    rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
    refine c.s_and_rr32 hK22 hA22 hin (by omega) hr22 (avx_70 _) ?_
    rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
    refine c.s_and_ri32 hK23 hA23 hin (by omega) hr23 (avx_72 _) ?_
    rintro Y24 t24 hK24 hA24 ⟨hr24, hg24, -⟩
    refine tail Y24 t24 hK24 hA24 hr24 ?_ ?_ fun h0 => ⟨r28, r27, ?_⟩
    · simp only [hg24, hg23, hg22, hg21, hg20, hg19, hg18, hg17, set_r0, set_r1, set_0, set_2, hsp16]
    · refine Saved.trans hsv16 ?_
      simp [Saved, hg24, hg23, hg22, hg21, hg20, hg19, hg18, hg17]
    · have hax : Y24.cpu.gpr.rax.setWidth 32 =
          x.setWidth 32 >>> 2 &&& x.setWidth 32 >>> 1 &&& 1#32 := by
        simp only [hg24, hg23, hg22, hg21, hg20, hg19, rv, set_r0, set_r1, set_0, set_2, get_r0, get_r1, sw_sw]
      rw [hax] at h0
      show prof.xcr0.getD 0 &&& xcr0Avx = xcr0Avx
      rw [hx]; exact enabled_of x h0

/-- `z7_x86_cpuid_GetMaxFunc()`: it returns, its frame the 24 bytes below `rsp`, the canary `fs:[40]` apart from them.
What it returns (`CPUID.00H:EAX`) a proof that a feature is reported does not need. -/
theorem sub_maxf (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L 0x4242b0 maxf) (hrip : X.cpu.rip = 0x4242b0)
    (hws : ∀ i < 24, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 24) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h24 : 24 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 24 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 24, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 24) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : maxf.length = 56 := maxf_length
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 24 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 24 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 32 ≤ 2 ^ 64 := by omega
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 24 ≤ cn.toNat := by omega
  -- `endbr64`, `push rbx`, `sub rsp, 16`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (maxf_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_push hK1 hA1 hin (by omega) hr1 (maxf_4 _) (fun i hi => by
    rw [hg1, hsp, add_sub8 p (m := 16) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hg1, hsp, add_sub8 p (m := 16) rfl, get_r3]
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_sub_ri64 hK2 hA2 hin (by omega) hr2 (maxf_5 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hsp3 : Y3.cpu.gpr.rsp = p := by
    rw [hg3, hg2, set_r4, get_r4, set_4]
    show Addr.add p 16 - BitVec.ofNat 64 16 = p
    rw [add_sub_lit p (Nat.le_refl 16), Nat.sub_self, addr_add_zero]
  -- `mov rax, fs:[40]`, `mov [rsp + 8], rax`
  have hc3 : eaF Y3 40 = cn := by rw [← hcd]; simp only [eaF, hK3.seg]; rfl
  refine c.s_mov_fs hK3 hA3 hin (by omega) hr3 (maxf_9 _) (fun i hi => by rw [hc3]; exact hcn i hi) ?_
  rw [hc3]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hcv1 : ofBytesLE 64 ((byteAddrs cn 8).map (Vst V (Addr.add p 16) (toBytesLE X.cpu.gpr.rbx 8))) =
      ofBytesLE 64 ((byteAddrs cn 8).map V) := by
    rw [map_Vst_apart (by simp; rw [toNat_addn (n := 32) (by omega) hfit]; omega) hcf
      (by simp; rw [toNat_addn (n := 32) (by omega) hfit]; omega)]
  rw [hcv1] at hg4
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg4
  have hsp4 : Y4.cpu.gpr.rsp = p := by simp [hg4, hsp3]
  have e4 : eaD Y4 4 8 = Addr.add p 8 := by simp only [eaD, get_r4, hsp4]; rfl
  refine c.s_mov_mr hK4 hA4 hin (by omega) hr4 (Or.inr rfl) (maxf_18 _) (fun i hi => by
    rw [e4, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e4, show rv Y4 64 0 = cv by simp [rv, hg4]]
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  -- `xor eax, eax`, `mov ecx, eax`, `cpuid`
  refine c.s_xor_rr32 hK5 hA5 hin (by omega) hr5 (maxf_23 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_mov_rr32 hK6 hA6 hin (by omega) hr6 (maxf_25 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_cpuid hK7 hA7 hin (by omega) hr7 (maxf_27 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, cpu, -, hg8⟩
  have hsp8 : Y8.cpu.gpr.rsp = p := by simp [hg8, hg7, hg6, hg5, hsp4]
  have hfr : ∀ x, (∀ i < 24, x ≠ Addr.add p i) →
      Vst (Vst V (Addr.add p 16) (toBytesLE X.cpu.gpr.rbx 8)) (Addr.add p 8) (toBytesLE cv (64 / 8)) x = V x := by
    intro x hx
    rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  -- `mov rsi, [rsp + 8]`, `xor rsi, fs:[40]`: 0
  have e8 : eaD Y8 4 8 = Addr.add p 8 := by simp only [eaD, get_r4, hsp8]; rfl
  refine c.s_mov_rm hK8 hA8 hin (by omega) hr8 (Or.inr rfl) (maxf_29 _) (fun i hi => by
    rw [e8, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
  rw [e8, read_Vst_self (by rfl) _ (by rw [toNat_addn (n := 32) (by omega) hfit]; omega)]
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hc9 : eaF Y9 40 = cn := by rw [← hcd]; simp only [eaF, hK9.seg]; rfl
  refine c.s_xor_fs hK9 hA9 hin (by omega) hr9 (maxf_34 _) (fun i hi => by rw [hc9]; exact hcn i hi) ?_
  have hcr : ofBytesLE 64 ((byteAddrs cn 8).map
      (Vst (Vst V (Addr.add p 16) (toBytesLE X.cpu.gpr.rbx 8)) (Addr.add p 8) (toBytesLE cv (64 / 8)))) = cv := by
    refine Eq.trans ?_ hcv
    congr 1
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact hfr _ fun i' hi' => add_ne_add hi hi' hcf (by omega) (by omega)
  rw [hc9, hcr]
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10, hz10⟩
  have hzf : Y10.cpu.rflags.zf = true := by rw [hz10, hg9]; simp [BitVec.setWidth_eq]
  refine c.s_jcc hK10 hA10 hin (by omega) hr10 (maxf_43 _) (tgt := 51) rfl (by omega)
    (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  -- `add rsp, 16`, `pop rbx`, `ret`
  refine c.s_add_ri64 hK11 hA11 hin (by omega) hr11 (maxf_45 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hsp12 : Y12.cpu.gpr.rsp = Addr.add p 16 := by
    simp only [hg12, hg11, hg10, hg9, set_r4, get_r4, set_r6, hsp8]; rfl
  refine c.s_pop hK12 hA12 hin (by omega) hr12 (maxf_49 _) (fun i hi => by
    rw [hsp12, addr_add_add]; exact c.hws _ (hws _ (by omega))) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  have hbx : ofBytesLE 64 ((byteAddrs Y12.cpu.gpr.rsp 8).map
      (Vst (Vst V (Addr.add p 16) (toBytesLE X.cpu.gpr.rbx 8)) (Addr.add p 8) (toBytesLE cv (64 / 8)))) =
      X.cpu.gpr.rbx := by
    have h8 := toNat_addn (i := 8) (n := 32) (by omega) hfit
    have h16 := toNat_addn (i := 16) (n := 32) (by omega) hfit
    rw [hsp12, map_Vst_apart (by simp; omega) (by omega) (by simp; omega), read_Vst_self (by rfl) _ (by omega)]
  rw [hbx] at hg13
  have hsp13 : Y13.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    simp only [hg13, set_r3, set_4, hsp12, hsp]; exact add_add8 p 16
  refine c.s_ret hK13 hA13 hin (by omega) hr13 (maxf_50 _) (fun i hi => by rw [hsp13]; exact hrd i hi) hin₂ h₂
    (by
      rw [hsp13, ← hret]; congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      rw [hsp, addr_add_add]
      exact hfr _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) ?_
  rintro Y t' hKY hAY ⟨hrY, hgY⟩
  refine k' _ hfr Y t' hKY hAY ⟨hrY, by rw [hgY, set_4, hsp13], ?_⟩
  simp [Saved, hgY, hg13, hg12, hg11, hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2]

/-- `CPU_IsSupported_AVX2()`: not 0 only if some CPU reports `CPUID.07H.0H:EBX.AVX2[5]`, some CPU reports
`CPUID.01H:ECX.AVX[28]` and the kernel enabled the SSE and AVX state in `XCR0`. Its frame and its callees' are the
104 bytes below `rsp`; the canary `fs:[40]` lies apart from them. -/
theorem sub_avx2 (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hpc : prof.Consistent) (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) (hrip : X.cpu.rip = 0x4244b0)
    (hws : ∀ i < 104, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 104) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h104 : 104 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 104 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 104, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 104) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y ∧
        (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
          prof.reports 7 0 (·.ebx) 5 ∧ prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx)) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : avx2.length = 104 := avx2_length
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 104 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 104 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 104 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 112 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 112 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 104 ≤ cn.toNat := by omega
  -- `endbr64`, `sub rsp, 40`, `mov rax, fs:[40]`, `mov [rsp + 24], rax`, `xor eax, eax`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (avx2_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (avx2_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 64 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  have hc2 : eaF Y2 40 = cn := by rw [← hcd]; simp only [eaF, hK2.seg]; rfl
  refine c.s_mov_fs hK2 hA2 hin (by omega) hr2 (avx2_8 _) (fun i hi => by rw [hc2]; exact hcn i hi) ?_
  rw [hc2]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg3
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 64 := by simp [hg3, hsp2]
  have e3 : eaD Y3 4 24 = Addr.add p 88 := by simp only [eaD, get_r4, hsp3]; exact addr_add_add p 64 24
  refine c.s_mov_mr hK3 hA3 hin (by omega) hr3 (Or.inr rfl) (avx2_17 _) (fun i hi => by
    rw [e3, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e3, show rv Y3 64 0 = cv by simp [rv, hg3]]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  generalize hV1 : Vst V (Addr.add p 88) (toBytesLE cv (64 / 8)) = V1 at hA4
  refine c.s_xor_rr32 hK4 hA4 hin (by omega) hr4 (avx2_22 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 64 := by simp [hg5, hg4, hsp3]
  have hsv5 : Saved X Y5 := by simp [Saved, hg5, hg4, hg3, hg2, hg1]
  -- the canary check and the return, from the three paths
  have tail : ∀ (V' : Addr → Byte) Y t', (∀ x, (∀ i < 88, x ≠ Addr.add p i) → V' x = V1 x) →
      KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x4244b0 : Addr).add 35 → Y.cpu.gpr.rsp = Addr.add p 64 → Saved X Y →
      (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
        prof.reports 7 0 (·.ebx) 5 ∧ prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx) →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro V' Y12 t12 hV' hK12 hA12 hr12 hsp12 hsv12 hax12
    have hfrV : ∀ x, (∀ i < 104, x ≠ Addr.add p i) → V' x = V x := by
      intro x hx
      rw [hV' x fun i hi => hx i (by omega), ← hV1]
      exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
    -- `mov rdx, [rsp + 24]`: the canary as stored
    have e12 : eaD Y12 4 24 = Addr.add p 88 := by simp only [eaD, get_r4, hsp12]; exact addr_add_add p 64 24
    refine c.s_mov_rm hK12 hA12 hin (by omega) hr12 (Or.inr rfl) (avx2_35 _) (fun i hi => by
      rw [e12, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    have hcs : ofBytesLE 64 ((byteAddrs (Addr.add p 88) 8).map V') = cv := by
      rw [show (byteAddrs (Addr.add p 88) 8).map V' = (byteAddrs (Addr.add p 88) 8).map V1 from
        List.map_congr_left fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
          rw [addr_add_add]
          exact hV' _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega), ← hV1]
      exact read_Vst_self (by rfl) _ (by rw [hpn 88 (by omega)]; omega)
    rw [e12, hcs]
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    -- `xor rdx, fs:[40]`: 0
    have hc13 : eaF Y13 40 = cn := by rw [← hcd]; simp only [eaF, hK13.seg]; rfl
    refine c.s_xor_fs hK13 hA13 hin (by omega) hr13 (avx2_40 _) (fun i hi => by rw [hc13]; exact hcn i hi) ?_
    have hcr : ofBytesLE 64 ((byteAddrs cn 8).map V') = cv := by
      refine Eq.trans ?_ hcv
      congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      exact hfrV _ fun i' hi' => add_ne_add hi hi' hcf (by omega) (by omega)
    rw [hc13, hcr]
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, hz14⟩
    have hzf : Y14.cpu.rflags.zf = true := by rw [hz14, hg13]; simp [BitVec.setWidth_eq]
    refine c.s_jcc hK14 hA14 hin (by omega) hr14 (avx2_49 _) (tgt := 99) rfl (by omega)
      (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    -- `add rsp, 40`, `ret`
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (avx2_51 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      simp only [hg16, hg15, hg14, hg13, set_r4, get_r4, set_r2]
      rw [hsp12, hsp]; exact addr_add_add p 64 40
    refine c.s_ret hK16 hA16 hin (by omega) hr16 (avx2_55 _) (fun i hi => by rw [hsp16]; exact hrd i hi) hin₂ h₂
      (by
        rw [hsp16, ← hret]; congr 1
        apply List.map_congr_left
        intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
        rw [hsp, addr_add_add]
        exact hfrV _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    refine k' V' (fun x hx => hfrV x hx) Y t' hKY hAY ⟨hrY, by rw [hgY, set_4, hsp16], ?_, fun h => ?_⟩
    · refine Saved.trans hsv12 ?_
      simp [Saved, hgY, hg16, hg15, hg14, hg13]
    · have hax : Y.cpu.gpr.rax.setWidth 32 = Y12.cpu.gpr.rax.setWidth 32 := by
        simp [hgY, hg16, hg15, hg14, hg13]
      rw [hax] at h
      exact hax12 h
  -- `xor eax, eax` (offset 33), then the tail with 0
  have tail0 : ∀ (V' : Addr → Byte) Y t', (∀ x, (∀ i < 88, x ≠ Addr.add p i) → V' x = V1 x) →
      KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x4244b0 : Addr).add 33 → Y.cpu.gpr.rsp = Addr.add p 64 → Saved X Y →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro V' Y t' hV' hKY hAY hrY hspY hsvY
    refine c.s_xor_rr32 hKY hAY hin (by omega) hrY (avx2_33 _) ?_
    rintro Z tz hKZ hAZ ⟨hrZ, hgZ⟩
    refine tail V' Z tz hV' hKZ hAZ hrZ (by rw [hgZ, set_r0, hspY]) (by rw [Saved, hgZ]; exact hsvY)
      fun h => absurd (by simp [hgZ]) h
  -- `call CPU_IsSupported_AVX`
  refine c.s_call hK5 hA5 hin (by omega) hr5 (avx2_24 _) hinA (by rw [avx_length]; omega) (by decide)
    (fun i hi => by rw [hsp5, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp5, add_sub8 p (m := 56) rfl]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hsp6 : Y6.cpu.gpr.rsp = Addr.add p 56 := by rw [hg6, set_4]
  have hs56 : Y6.cpu.gpr.rsp - BitVec.ofNat 64 56 = p := by
    rw [hsp6, add_sub_lit p (Nat.le_refl 56), Nat.sub_self, addr_add_zero]
  refine sub_avx c hpc hK6 hA6 hinA hinC (by rw [hr6]) (fun i hi => by rw [hs56]; exact hws i (by omega))
    (fun i hi => by rw [hsp6, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [← hcd] at hcn; exact hcn) (by rw [hsp6, hpn 56 (by omega)]; omega)
    (by rw [hsp6, hpn 56 (by omega)]; omega) (by rw [← hcd] at hcf; exact hcf)
    (by rw [hsp6, hpn 56 (by omega), ← hcd] at *; omega) hin (j₂ := 29) (by omega)
    (by rw [hsp6]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
  intro V3 hfr3 Y7 t7 hK7 hA7 ⟨hr7, hsp7, hsv7, hax7⟩
  rw [hs56] at hfr3
  rw [hsp6, add_add8] at hsp7
  have hV3 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V3 x = V1 x := by
    intro x hx
    rw [hfr3 x fun i hi => hx i (by omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  have hsv7' : Saved X Y7 := Saved.trans hsv5 (Saved.trans (by simp [Saved, hg6]) hsv7)
  -- `test eax, eax`, `jne`
  refine c.s_test_rr32 hK7 hA7 hin (by omega) hr7 (avx2_29 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hz8⟩
  have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 64 := by rw [hg8, hsp7]
  have hsv8 : Saved X Y8 := by rw [Saved, hg8]; exact hsv7'
  refine c.s_jcc hK8 hA8 hin (by omega) hr8 (avx2_31 _) (tgt := 64) rfl (by omega) (fun h => ?_) fun h => ?_
  · -- AVX: `call z7_x86_cpuid_GetMaxFunc`
    have hav := hax7 fun h0 => by
      simp only [Rflags.cond, hz8, Bool.not_eq_true'] at h
      simp [rv, h0] at h
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_call hK9 hA9 hin (by omega) hr9 (avx2_64 _) hinM (by rw [maxf_length]; omega) (by decide)
      (fun i hi => by rw [hg9, hsp8, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hg9, hsp8, add_sub8 p (m := 56) rfl]
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    have hsp10 : Y10.cpu.gpr.rsp = Addr.add p 56 := by rw [hg10, set_4]
    have hs24 : Y10.cpu.gpr.rsp - BitVec.ofNat 64 24 = Addr.add p 32 := by
      rw [hsp10, add_sub_lit p (by omega : 24 ≤ 56)]
    refine sub_maxf c hK10 hA10 hinM (by rw [hr10])
      (fun i hi => by rw [hs24, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp10, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      (by rw [← hcd] at hcn; exact hcn) (by rw [hsp10, hpn 56 (by omega)]; omega)
      (by rw [hsp10, hpn 56 (by omega)]; omega) (by rw [← hcd] at hcf; exact hcf)
      (by rw [hsp10, hpn 56 (by omega), ← hcd] at *; omega) hin (j₂ := 69) (by omega)
      (by rw [hsp10]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
    intro V5 hfr5 Y11 t11 hK11 hA11 ⟨hr11, hsp11, hsv11⟩
    rw [hs24] at hfr5
    rw [hsp10, add_add8] at hsp11
    have hV5 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V5 x = V1 x := by
      intro x hx
      rw [hfr5 x fun i hi => by rw [addr_add_add]; exact hx _ (by omega)]
      rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
      exact hV3 x hx
    have hsv11' : Saved X Y11 := Saved.trans hsv8 (Saved.trans (by simp [Saved, hg10]) hsv11)
    -- `cmp eax, 6`, `jbe`
    refine c.s_cmp_ri32 hK11 hA11 hin (by omega) hr11 (avx2_69 _) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
    have hsp12 : Y12.cpu.gpr.rsp = Addr.add p 64 := by rw [hg12, hsp11]
    have hsv12 : Saved X Y12 := by rw [Saved, hg12]; exact hsv11'
    refine c.s_jcc hK12 hA12 hin (by omega) hr12 (avx2_72 _) (tgt := 33) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
      exact tail0 V5 Y13 t13 hV5 hK13 hA13 hr13 (by rw [hg13, hsp12]) (by rw [Saved, hg13]; exact hsv12)
    -- `mov rdi, rsp`, `mov esi, 7`, `call z7_x86_cpuid`
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    refine c.s_mov_rr64 hK13 hA13 hin (by omega) hr13 (avx2_74 _) ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    refine c.s_mov_ri32 hK14 hA14 hin (by omega) hr14 (avx2_77 _) ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    have hsp15 : Y15.cpu.gpr.rsp = Addr.add p 64 := by simp [hg15, hg14, hg13, hsp12]
    refine c.s_call hK15 hA15 hin (by omega) hr15 (avx2_82 _) hinC (by rw [cpuid_length]; omega) (by decide)
      (fun i hi => by rw [hsp15, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp15, add_sub8 p (m := 56) rfl]
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = Addr.add p 56 := by rw [hg16, set_4]
    have hdi16 : Y16.cpu.gpr.rdi = Addr.add p 64 := by simp [hg16, hg15, hg14, hg13, hsp12]
    have hsi16 : Y16.cpu.gpr.rsi.setWidth 32 = 7 := by simp [hg16, hg15]
    refine sub_cpuid c hK16 hA16 hinC (by rw [hr16]) (fun i hi => by
        rw [hsp16, add_sub8 p (m := 48) rfl, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hdi16, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp16, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      (by rw [hsp16, hpn 56 (by omega)]; omega) (by rw [hsp16, hdi16, hpn 56 (by omega), hpn 64 (by omega)]; omega)
      (by rw [hdi16, hpn 64 (by omega)]; omega) hin (j₂ := 87) (by omega)
      (by rw [hsp16]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
    intro V7 hfr7 ⟨cpu, hcpu, hrep⟩ Y17 t17 hK17 hA17 ⟨hr17, hsp17, hsv17⟩
    rw [hsi16, hdi16] at hrep
    rw [hsp16, add_add8] at hsp17
    rw [hsp16, add_sub8 p (m := 48) rfl, hdi16] at hfr7
    have hV7 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V7 x = V1 x := by
      intro x hx
      rw [hfr7 x (fun i hi => by rw [addr_add_add]; exact hx _ (by omega)) (fun i hi => by
        rw [addr_add_add]; exact hx _ (by omega))]
      rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
      exact hV5 x hx
    have hsv17' : Saved X Y17 := Saved.trans hsv12 (Saved.trans (by simp [Saved, hg16, hg15, hg14, hg13]) hsv17)
    -- `mov eax, [rsp + 4]`, `shr eax, 5`, `and eax, 1`, `jmp`
    have e17 : eaD Y17 4 4 = Addr.add (Addr.add p 64) 4 := by simp only [eaD, get_r4, hsp17]; rfl
    refine c.s_mov_rm hK17 hA17 hin (by omega) hr17 (Or.inl rfl) (avx2_87 _) (fun i hi => by
      rw [e17, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    rw [e17, hrep.2.1]
    rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
    refine c.s_shr_ri32 hK18 hA18 hin (by omega) hr18 (by decide) (avx2_91 _) ?_
    rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
    refine c.s_and_ri32 hK19 hA19 hin (by omega) hr19 (avx2_94 _) ?_
    rintro Y20 t20 hK20 hA20 ⟨hr20, hg20, -⟩
    refine c.s_jmp hK20 hA20 hin (by omega) hr20 (avx2_97 _) (tgt := 35) rfl (by omega) ?_
    rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
    refine tail V7 Y21 t21 hV7 hK21 hA21 hr21 (by simp [hg21, hg20, hg19, hg18, hsp17])
      (by refine Saved.trans hsv17' ?_; simp [Saved, hg21, hg20, hg19, hg18]) fun h0 => ⟨?_, hav.1, hav.2.2⟩
    have hax : Y21.cpu.gpr.rax.setWidth 32 = (prof.cpuid cpu 7 0).ebx >>> 5 &&& 1#32 := by
      simp only [hg21, hg20, hg19, hg18, rv, set_r0, get_r0, sw_sw]
    rw [hax] at h0
    exact ⟨cpu, hcpu, bit_of _ h0⟩
  · -- not AVX: 0
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    exact tail0 V3 Y9 t9 hV3 hK9 hA9 hr9 (by rw [hg9, hsp8]) (by rw [Saved, hg9]; exact hsv8)

end FV7z.Prepare
