import FV7z.CpuFeat.Decode
import FV7z.Lemmas.FnSib
import FV7z.Prepare.AesGen
/-!
# `__tunable_get_val` of a tunable not set (PLAN.md G2, "Dispatch theo CPUID", glibc `init_cpu_features`)

`__tunable_get_val (id, valp, callback)` (glibc 2.31 `elf/dl-tunables.c`, at `0x66f3a0` in `7zzs` 26.06) copies the
value of `tunable_list[id]` (at `0x791660`, 56 bytes an entry) to `*valp`: 4 bytes if its type is `TUNABLE_TYPE_INT_32`
(0), else 8; then, if the tunable was set (`initialized`, the byte at offset 40) and `callback` is not `NULL`, it
tail-calls `callback (&cur->val)`. Here: a tunable not set, so it returns. `Seg.s_tgv` runs a `call` of it inside a
caller's run, from the `call` to the return: the entry's bytes read are the footprint's and not written by the run,
`*valp` 8 bytes it may write; the caller goes on with `*valp` holding 4 or 8 bytes (which, not followed), `rsp` and
the registers a callee keeps as they were.
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare

/-- The entry of tunable `d`, as `lea rax, [rdi·8]; sub rax, rdi; lea rax, [rcx + rax·8]` computes it. -/
def tgvEnt (d : Addr) : Addr := 0x791660 + (0 + d * 8 + 0 - d) * 8 + 0

/-- Its `initialized` byte, as `cmp byte [rcx + rax·8 + 40], 0` reads it. -/
def tgvInit (d : Addr) : Addr := 0x791660 + (0 + d * 8 + 0 - d) * 8 + 40

/-- What a caller keeps: `rsp` and the registers a callee keeps. -/
structure TK (g g' : Gprs) : Prop where
  sp : g'.rsp = g.rsp
  rbx : g'.rbx = g.rbx
  rbp : g'.rbp = g.rbp
  r12 : g'.r12 = g.r12
  r13 : g'.r13 = g.r13
  r14 : g'.r14 = g.r14
  r15 : g'.r15 = g.r15

/-- Inside, from `lea rcx`: `rsp` below the return address, `rcx` the list, `rdi` the id. -/
structure TI (g₀ : Gprs) (d : Addr) (g : Gprs) : Prop where
  sp : g.rsp = g₀.rsp - 8
  rbx : g.rbx = g₀.rbx
  rbp : g.rbp = g₀.rbp
  r12 : g.r12 = g₀.r12
  r13 : g.r13 = g₀.r13
  r14 : g.r14 = g₀.r14
  r15 : g.r15 = g₀.r15
  rcx : g.rcx = 0x791660
  rdi : g.rdi = d

theorem TI.set {g₀ g : Gprs} {d : Addr} (h : TI g₀ d g) {r : Nat} (hr : r = 0 ∨ r = 6 ∨ r = 8) (v : BitVec 64) :
    TI g₀ d (g.set (regOf r) v) := by
  rcases hr with rfl | rfl | rfl <;> exact ⟨h.sp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15, h.rcx, h.rdi⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From the test of `initialized` (`49`) to the return. -/
theorem tgvTail (c : Seg prof F Wl L s₀ o) (hinT : CodeIn L 0x66f3a0 tgv) {g₀ : Gprs} {d : Addr}
    {e' : Addr} {code : List Byte} {j₂ : Nat} (hin : CodeIn L e' code) (hj₂ : j₂ < code.length)
    {V₁ : Addr → Byte} (hra : ofBytesLE 64 ((byteAddrs (g₀.rsp - 8) 8).map V₁) = e'.add j₂)
    (hsl : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp - 8) i))
    (hin0 : Foot F.data (tgvInit d)) (hz : V₁ (tgvInit d) = 0)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V₁)
    (hr : X.cpu.rip = (0x66f3a0 : Addr).add 49) (hI : TI g₀ d X.cpu.gpr)
    (k' : ContG prof F Wl L s₀ o gev gP gE V₁ fun Y => Y.cpu.rip = e'.add j₂ ∧ TK g₀ Y.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  have hl : tgv.length = 109 := tgv_length
  refine c.s_lea_si hK hA hinT (by omega) hr (tgv_49 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  refine c.s_sub_rr64 hK1 hA1 hinT (by omega) hr1 (tgv_57 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hI2 : TI g₀ d Y2.cpu.gpr := by rw [hg2, hg1]; exact (hI.set (by omega) _).set (by omega) _
  have he : eaS Y2 (some 1) 0 8 40 = tgvInit d := by
    simp only [eaS, baseV, hg2, hg1, get_regOf_0, get_regOf_1, get_regOf_7, set_rax, hI.rcx, hI.rdi]
    rfl
  refine c.s_cmp_m8i_si hK2 hA2 hinT (by omega) hr2 (tgv_60 _) (by rw [he]; exact hin0) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hf3⟩
  refine c.s_lea_si hK3 hA3 hinT (by omega) hr3 (tgv_65 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hf4⟩
  have hI4 : TI g₀ d Y4.cpu.gpr := by rw [hg4, hg3]; exact hI2.set (by omega) _
  refine c.s_jcc hK4 hA4 hinT (by omega) hr4 (tgv_73 _) (tgt := 96) (by decide) (by omega) ?_ ?_
  · intro _
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    refine c.s_ret hK5 hA5 hinT (by omega) hr5 (tgv_96 _)
      (fun i hi => by rw [hg5, hI4.sp]; exact hsl i hi) hin hj₂ (by rw [hg5, hI4.sp]; exact hra) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    refine k' Y6 t6 hK6 hA6 ⟨hr6, ?_⟩
    rw [hg6, hg5]
    exact ⟨by simp only [set_4]; rw [hI4.sp, BitVec.sub_add_cancel], hI4.rbx, hI4.rbp, hI4.r12, hI4.r13, hI4.r14,
      hI4.r15⟩
  · intro hc
    exfalso
    have : Y4.cpu.rflags.cond 4 = true := by
      rw [hf4, cond_rf0, hf3]
      simp [Rflags.cond, he, hz]
    rw [this] at hc
    exact Bool.noConfusion hc

/-- `call __tunable_get_val` for a tunable not set: from the `call` to the return, with `*rsi` 4 or 8 bytes. -/
theorem _root_.FV7z.Fn.Seg.s_tgv (c : Seg prof F Wl L s₀ o) (hinT : CodeIn L 0x66f3a0 tgv) {X : State} {t j : Nat}
    {e' : Addr} {code : List Byte} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {rel len : Nat} (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len))
    (hjl : j + len < code.length) (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = 0x66f3a0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (hfit : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (hp : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (hpa : ∀ i < 8, ∀ k < 8, Addr.add (X.cpu.gpr.rsp - 8) i ≠ Addr.add X.cpu.gpr.rsi k)
    {d : Addr} (hdv : (rv X 32 7).setWidth 64 = d)
    (hty : ∀ i < 4, Foot F.data (Addr.add (tgvEnt d + BitVec.ofNat 64 8) i))
    (hva : ∀ i < 8, Foot F.data (Addr.add (tgvEnt d + BitVec.ofNat 64 32) i))
    (hin0 : Foot F.data (tgvInit d)) (hnw : ¬ Foot Wl (tgvInit d)) (hz : V (tgvInit d) = 0)
    (k' : ∀ bs : List Byte, bs.length = 4 ∨ bs.length = 8 →
      ContG prof F Wl L s₀ o gev gP gE
        (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) X.cpu.gpr.rsi bs)
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ TK X.cpu.gpr Y.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  have hl : tgv.length = 109 := tgv_length
  have hsl : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hst i hi)
  refine c.s_call hK hA hin hj hrip hd hinT (by omega) htgt hst ?_
  rintro Y0 t0 hK0 hA0 ⟨hr0, hg0⟩
  refine c.s_endbr hK0 hA0 hinT (by omega) (by rw [hr0, addr_add_zero]) (tgv_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_rr32 hK1 hA1 hinT (by omega) hr1 (tgv_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_lea_rip hK2 hA2 hinT (by omega) hr2 (tgv_6 _) (v := 0x791660) (by decide) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, -⟩
  have hI3 : TI X.cpu.gpr d Y3.cpu.gpr := by
    rw [hg3, hg2, hg1, hg0]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show BitVec.setWidth 64 (rv Y1 32 7) = d
    rw [← hdv]; simp only [rv, hg1, hg0]; rfl
  have hsi3 : Y3.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg3, hg2, hg1, hg0]; rfl
  refine c.s_lea_si hK3 hA3 hinT (by omega) hr3 (tgv_13 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, -⟩
  refine c.s_sub_rr64 hK4 hA4 hinT (by omega) hr4 (tgv_21 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_lea_si hK5 hA5 hinT (by omega) hr5 (tgv_24 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, -⟩
  have hI6 : TI X.cpu.gpr d Y6.cpu.gpr := by
    rw [hg6, hg5, hg4]; exact ((hI3.set (by omega) _).set (by omega) _).set (by omega) _
  have hx6 : Y6.cpu.gpr.rax = tgvEnt d := by
    rw [hg6]
    simp only [set_rax, eaS, baseV, hg5, hg4, get_regOf_0, get_regOf_1, get_regOf_7, hI3.rcx, hI3.rdi]
    rfl
  have hsi6 : Y6.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg6, hg5, hg4]; exact hsi3
  refine c.s_mov_rm hK6 hA6 hinT (by omega) hr6 (Or.inl rfl) (tgv_28 _)
    (fun i hi => by simp only [eaD, get_regOf_0, hx6]; exact hty i hi) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hx7 : Y7.cpu.gpr.rax = tgvEnt d := by rw [hg7]; exact hx6
  refine c.s_mov_rm hK7 hA7 hinT (by omega) hr7 (Or.inr rfl) (tgv_32 _)
    (fun i hi => by simp only [eaD, get_regOf_0, hx7]; exact hva i hi) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hI8 : TI X.cpu.gpr d Y8.cpu.gpr := by rw [hg8, hg7]; exact (hI6.set (by omega) _).set (by omega) _
  have hsi8 : Y8.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg8, hg7]; exact hsi6
  have hV : ∀ (V₁ : Addr → Byte) (bs : List Byte), bs.length = 4 ∨ bs.length = 8 →
      V₁ = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) X.cpu.gpr.rsi bs →
      ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp - 8) 8).map V₁) = e'.add (j + len) ∧ V₁ (tgvInit d) = 0 := by
    rintro V₁ bs hb rfl
    have hb8 : bs.length ≤ 8 := by omega
    refine ⟨?_, ?_⟩
    · rw [List.map_congr_left (g := Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
          exact Vst_apart bs _ _ _ fun k hk => hpa i hi k (by omega)]
      have := Vst_self (toBytesLE (e'.add (j + len)) 8) V (X.cpu.gpr.rsp - 8) (by simpa using hfit)
      rw [toBytesLE_length] at this
      rw [this, ofBytesLE_toBytesLE (n := 8) rfl]
    · rw [Vst_apart bs _ _ _ fun k hk h => hnw (by rw [h]; exact hp k (by omega)),
        Vst_apart _ _ _ _ fun i hi h => hnw (by rw [h]; exact hst i (by simpa using hi))]
      exact hz
  -- the store, then `49`
  have st : ∀ (Z : State) (tz : Nat) (bs : List Byte), bs.length = 4 ∨ bs.length = 8 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) X.cpu.gpr.rsi bs) →
      Z.cpu.rip = (0x66f3a0 : Addr).add 49 → TI X.cpu.gpr d Z.cpu.gpr → GoG prof L o gev gP gE Z tz := by
    intro Z tz bs hb hKZ hAZ hrZ hIZ
    obtain ⟨h1, h2⟩ := hV _ bs hb rfl
    exact tgvTail c hinT hin hjl h1 hsl hin0 h2 hKZ hAZ hrZ hIZ (k' bs hb)
  have hpz : ∀ Z : State, Z.cpu.gpr.rsi = X.cpu.gpr.rsi → eaD Z 6 0 = X.cpu.gpr.rsi := fun Z h => by
    simp only [eaD, get_regOf_6, h]; exact BitVec.add_zero _
  -- `*valp` 8 bytes
  have pB : ∀ (Z : State) (tz : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) →
      Z.cpu.rip = (0x66f3a0 : Addr).add 104 → TI X.cpu.gpr d Z.cpu.gpr → Z.cpu.gpr.rsi = X.cpu.gpr.rsi →
      GoG prof L o gev gP gE Z tz := by
    intro Z tz hKZ hAZ hrZ hIZ hsZ
    refine c.s_mov_mr hKZ hAZ hinT (by omega) hrZ (Or.inr rfl) (tgv_104 _)
      (fun i hi => by rw [hpz Z hsZ]; exact hp i (by omega)) ?_
    rw [hpz Z hsZ]
    rintro Z1 tz1 hKZ1 hAZ1 ⟨hrZ1, hgZ1⟩
    refine c.s_jmp hKZ1 hAZ1 hinT (by omega) hrZ1 (tgv_107 _) (tgt := 49) (by decide) (by omega) ?_
    rintro Z2 tz2 hKZ2 hAZ2 ⟨hrZ2, hgZ2⟩
    exact st Z2 tz2 _ (Or.inr (toBytesLE_length _ _)) hKZ2 hAZ2 hrZ2 (by rw [hgZ2, hgZ1]; exact hIZ)
  refine c.s_cmp_ri32 hK8 hA8 hinT (by omega) hr8 (tgv_36 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9, -⟩
  have hI9 : TI X.cpu.gpr d Y9.cpu.gpr := by rw [hg9]; exact hI8
  have hsi9 : Y9.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg9]; exact hsi8
  refine c.s_jcc hK9 hA9 hinT (by omega) hr9 (tgv_40 _) (tgt := 104) (by decide) (by omega) ?_ ?_
  · intro _
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    exact pB Y10 t10 hK10 hA10 hr10 (by rw [hg10]; exact hI9) (by rw [hg10]; exact hsi9)
  intro _
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  refine c.s_test_rr32 hK10 hA10 hinT (by omega) hr10 (tgv_42 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
  have hI11 : TI X.cpu.gpr d Y11.cpu.gpr := by rw [hg11, hg10]; exact hI9
  have hsi11 : Y11.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg11, hg10]; exact hsi9
  refine c.s_jcc hK11 hA11 hinT (by omega) hr11 (tgv_45 _) (tgt := 104) (by decide) (by omega) ?_ ?_
  · intro _
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
    exact pB Y12 t12 hK12 hA12 hr12 (by rw [hg12]; exact hI11) (by rw [hg12]; exact hsi11)
  intro _
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hsi12 : Y12.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg12]; exact hsi11
  -- `*valp` 4 bytes
  refine c.s_mov_mr hK12 hA12 hinT (by omega) hr12 (Or.inl rfl) (tgv_47 _)
    (fun i hi => by rw [hpz Y12 hsi12]; exact hp i (by omega)) ?_
  rw [hpz Y12 hsi12]
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  exact st Y13 t13 _ (Or.inl (toBytesLE_length _ _)) hK13 hA13 hr13 (by rw [hg13, hg12]; exact hI11)

end FV7z.CpuFeat
