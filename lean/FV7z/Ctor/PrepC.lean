import FV7z.Ctor.Prep
import FV7z.Prepare.K
/-!
# `csuTg 5`, `7`, `9`, `92`: `endbr64; jmp` to a `*Prepare` function (PLAN.md §M, constructors)

`csuTg 5` (offset 32 of `sti`) jumps to `LzFindPrepare`, `csuTg 7` (64) to `Sha1Prepare`, `csuTg 9` (96) to
`Sha256Prepare`, `csuTg 92` (2608) to `AesGenTables`. Each is `jmp_runs` of `prepK_runs` with the function's
contract by `fnK` (`Prepare/K.lean`); its spec is `wrSpec` of the globals the function writes, and `G` goes from `m`
to `m + 1` by what the function leaves there (`lzOk`, `shOk`, `agOk`).
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Prepare

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 5`: `endbr64; jmp 0x427de0`. -/
def jp5 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x77, 0xbc, 0x00, 0x00]
theorem jp5_0 : ∀ feat, Dec feat jp5 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem jp5_4 : ∀ feat, Dec feat jp5 4 (FV7z.mk .jmp 64 [.rel 48247] 5) := by dec_rfl
theorem vp5 : jp5 <+: sti.drop 32 := by decide +kernel
theorem tg5 : csuTg 5 = sti_at.add 32 := by decide +kernel
theorem calls5 : calls 5 = [] := by decide +kernel

/-- `csuTg 7`: `endbr64; jmp 0x43a740`. -/
def jp7 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xb7, 0xe5, 0x01, 0x00]
theorem jp7_0 : ∀ feat, Dec feat jp7 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem jp7_4 : ∀ feat, Dec feat jp7 4 (FV7z.mk .jmp 64 [.rel 124343] 5) := by dec_rfl
theorem vp7 : jp7 <+: sti.drop 64 := by decide +kernel
theorem tg7 : csuTg 7 = sti_at.add 64 := by decide +kernel
theorem calls7 : calls 7 = [] := by decide +kernel

/-- `csuTg 9`: `endbr64; jmp 0x43b3e0`. -/
def jp9 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x37, 0xf2, 0x01, 0x00]
theorem jp9_0 : ∀ feat, Dec feat jp9 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem jp9_4 : ∀ feat, Dec feat jp9 4 (FV7z.mk .jmp 64 [.rel 127543] 5) := by dec_rfl
theorem vp9 : jp9 <+: sti.drop 96 := by decide +kernel
theorem tg9 : csuTg 9 = sti_at.add 96 := by decide +kernel
theorem calls9 : calls 9 = [] := by decide +kernel

/-- `csuTg 92`: `endbr64; jmp 0x41e540`. -/
def jp92 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xc7, 0x19, 0x00, 0x00]
theorem jp92_0 : ∀ feat, Dec feat jp92 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem jp92_4 : ∀ feat, Dec feat jp92 4 (FV7z.mk .jmp 64 [.rel 6599] 5) := by dec_rfl
theorem vp92 : jp92 <+: sti.drop 2608 := by decide +kernel
theorem tg92 : csuTg 92 = sti_at.add 2608 := by decide +kernel
theorem calls92 : calls 92 = [] := by decide +kernel

/-- What `LzFindPrepare` writes: `g_LzFind_SaturSub`. -/
def w5 : List Rgn := [⟨0x7967a0, 8⟩]
/-- What `Sha1Prepare` writes: its two pointers. -/
def w7 : List Rgn := [⟨0x792150, 8⟩, ⟨0x7967a8, 8⟩]
/-- What `Sha256Prepare` writes: its two pointers. -/
def w9 : List Rgn := [⟨0x792160, 8⟩, ⟨0x7967b0, 8⟩]
/-- What `AesGenTables` writes: the tables and its four globals. -/
def w92 : List Rgn := [⟨0x794680, 0x2100⟩, ⟨0x7a7e00, 28⟩]

theorem wrT5 : ∀ x ∈ wrOf w5, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem wrT7 : ∀ x ∈ wrOf w7, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem wrT9 : ∀ x ∈ wrOf w9, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem wrT92 : ∀ x ∈ wrOf w92, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem wrA5 : ∀ x ∈ wrOf w5, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel
theorem wrA7 : ∀ x ∈ wrOf w7, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel
theorem wrA9 : ∀ x ∈ wrOf w9, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel
theorem wrA92 : ∀ x ∈ wrOf w92, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1 := by decide +kernel

/-- What the four constructors ask of the run: the processor's profile consistent, the frame's call as `sysv` asks,
`sp` above the globals, the stack's window in `Wl`, the canary below the window and in the footprint. -/
structure PEnv (prof : Profile) (F : Footprint) (Wl : List Rgn) (s₀ : State) (sp : Addr) : Prop where
  pc : prof.Consistent
  df : s₀.cpu.rflags.df = false
  x87 : s₀.cpu.x87.full = 0
  al : (sp - 64#64 + 8).toNat % 16 = 0
  hi : 7991300 + 1024 ≤ sp.toNat
  stk : ∀ y : Addr, sp.toNat - 1024 ≤ y.toNat → y.toNat < sp.toNat - 56 → Foot Wl y
  can : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ sp.toNat - 1024
  canF : ∀ y, (canary s₀).Mem y → Foot F.writes y ∨ Foot F.reads y

/-- The canary at the frame's call, from `s₀`'s. -/
theorem PEnv.can' {sp : Addr} (h : PEnv prof F Wl s₀ sp) {Y : State} (hs : Y.cpu.seg = s₀.cpu.seg)
    (hr : Y.cpu.gpr.rsp = sp - 64#64) :
    (Addr.add Y.cpu.seg.fsBase 40).toNat + 8 ≤ Y.cpu.gpr.rsp.toNat - 960 ∧
      Y.cpu.gpr.rsp.toNat = sp.toNat - 64 := by
  have := h.can
  have h1 := h.hi
  rw [hs, hr, Csu.sp_n (by omega)]
  omega

/-- `[canary s₀]` in the footprint. -/
theorem PEnv.rf1 {sp : Addr} (h : PEnv prof F Wl s₀ sp) :
    ∀ y, Foot [canary s₀] y → Foot F.writes y ∨ Foot F.reads y := fun y ⟨r, hr, hm⟩ => by
  rw [List.mem_singleton] at hr
  subst hr
  exact h.canF y hm

/-- `csuTg 5` for `Jg`, its spec `wrSpec (wrOf w5)`. -/
theorem runs5_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti) (hinE : CodeIn L 0x427de0 lz)
    (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (hWl : ∀ y, Foot w5 y → Foot Wl y)
    (hspec : spec 5 = wrSpec (wrOf w5)) (hD : ∀ k, (spec k).Dep) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 5 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w5, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W W' : Addr → Byte), lzOk prof Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w5 y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → G 5 W → G 6 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 5 (csuTg 5) :=
  jmp_runs (j := 32) (rel := 48247) c hin hinE (by decide) tg5
    (Dec.shift (j := 32) (k := 0) (jp5_0 _) vp5 (by decide))
    (Dec.shift (j := 32) (k := 4) (jp5_4 _) vp5 (by decide))
    (sti_lt (by decide)) (by decide)
    (prepK_runs (k := 120) (Wc := w5) (Rc := []) c hC (lzFindPrepareK prof hP.pc hinE hinS hinA2 hinA hinM hinC)
      hP.df hP.x87 hP.al (by decide) hP.hi hP.stk hWl (lo_canary hP.can) hP.rf1
      (fun Y hs hr => by
        obtain ⟨h1, h2⟩ := hP.can' hs hr
        have := hP.hi
        unfold lzPre
        omega)
      (by decide) calls5 hspec hD wrT5 wrA5 hB hXw (fun _ Z W W' hp => hG Z W W' hp))

/-- `csuTg 7` for `Jg`, its spec `wrSpec (wrOf w7)`. -/
theorem runs7_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti) (hinE : CodeIn L 0x43a740 sha1p)
    (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) (hWl : ∀ y, Foot w7 y → Foot Wl y)
    (hspec : spec 7 = wrSpec (wrOf w7)) (hD : ∀ k, (spec k).Dep) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 7 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w7, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W W' : Addr → Byte), shOk prof 0x439b70 0x43a790 0x792150 0x7967a8 Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w7 y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → G 7 W → G 8 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 7 (csuTg 7) :=
  jmp_runs (j := 64) (rel := 124343) c hin hinE (by decide) tg7
    (Dec.shift (j := 64) (k := 0) (jp7_0 _) vp7 (by decide))
    (Dec.shift (j := 64) (k := 4) (jp7_4 _) vp7 (by decide))
    (sti_lt (by decide)) (by decide)
    (prepK_runs (k := 88) (Wc := w7) (Rc := []) c hC (sha1PrepareK prof hP.pc hinE hinH hinS hinM hinC)
      hP.df hP.x87 hP.al (by decide) hP.hi hP.stk hWl (lo_canary hP.can) hP.rf1
      (fun Y hs hr => by
        obtain ⟨h1, h2⟩ := hP.can' hs hr
        have := hP.hi
        have e1 : (0x792150 : Addr).toNat = 0x792150 := rfl
        have e2 : (0x7967a8 : Addr).toNat = 0x7967a8 := rfl
        unfold shPre
        rw [e1, e2]
        omega)
      (by decide) calls7 hspec hD wrT7 wrA7 hB hXw (fun _ Z W W' hp => hG Z W W' hp))

/-- `csuTg 9` for `Jg`, its spec `wrSpec (wrOf w9)`. -/
theorem runs9_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti) (hinE : CodeIn L 0x43b3e0 sha256p)
    (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) (hWl : ∀ y, Foot w9 y → Foot Wl y)
    (hspec : spec 9 = wrSpec (wrOf w9)) (hD : ∀ k, (spec k).Dep) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 9 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w9, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W W' : Addr → Byte), shOk prof 0x43a9f0 0x43b430 0x792160 0x7967b0 Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w9 y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → G 9 W → G 10 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 9 (csuTg 9) :=
  jmp_runs (j := 96) (rel := 127543) c hin hinE (by decide) tg9
    (Dec.shift (j := 96) (k := 0) (jp9_0 _) vp9 (by decide))
    (Dec.shift (j := 96) (k := 4) (jp9_4 _) vp9 (by decide))
    (sti_lt (by decide)) (by decide)
    (prepK_runs (k := 88) (Wc := w9) (Rc := []) c hC (sha256PrepareK prof hP.pc hinE hinH hinS hinM hinC)
      hP.df hP.x87 hP.al (by decide) hP.hi hP.stk hWl (lo_canary hP.can) hP.rf1
      (fun Y hs hr => by
        obtain ⟨h1, h2⟩ := hP.can' hs hr
        have := hP.hi
        have e1 : (0x792160 : Addr).toNat = 0x792160 := rfl
        have e2 : (0x7967b0 : Addr).toNat = 0x7967b0 := rfl
        unfold shPre
        rw [e1, e2]
        omega)
      (by decide) calls9 hspec hD wrT9 wrA9 hB hXw (fun _ Z W W' hp => hG Z W W' hp))

/-- `AesGenTables` reads `Sbox`, below the window. -/
theorem lo92 {sp : Addr} (hs : 7991300 + 1024 ≤ sp.toNat) {s : State}
    (h : (Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ sp.toNat - 1024) :
    Lo (sp.toNat - 1024) (canary s :: [⟨0x6d8040, 256⟩]) := fun r hr => by
  rcases List.mem_cons.1 hr with rfl | hr
  · exact h
  · rw [List.mem_singleton] at hr
    subst hr
    show 0x6d8040 + 256 ≤ sp.toNat - 1024
    omega

/-- `csuTg 92` for `Jg`, its spec `wrSpec (wrOf w92)`. -/
theorem runs92_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hP : PEnv prof F Wl s₀ sp) (hin : CodeIn L sti_at sti) (hinE : CodeIn L 0x41e540 aesg)
    (hinA : CodeIn L 0x4242f0 aes) (hinV : CodeIn L 0x4245a0 vaes) (hinX : CodeIn L 0x424440 avx)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (hWl : ∀ y, Foot w92 y → Foot Wl y)
    (hSb : ∀ y, Foot [canary s₀, ⟨0x6d8040, 256⟩] y → Foot F.writes y ∨ Foot F.reads y)
    (hspec : spec 92 = wrSpec (wrOf w92)) (hD : ∀ k, (spec k).Dep)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 92 → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf w92, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Z : State) (W W' : Addr → Byte), agOk prof Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w92 y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → G 92 W → G 93 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 92 (csuTg 92) :=
  jmp_runs (j := 2608) (rel := 6599) c hin hinE (by decide) tg92
    (Dec.shift (j := 2608) (k := 0) (jp92_0 _) vp92 (by decide))
    (Dec.shift (j := 2608) (k := 4) (jp92_4 _) vp92 (by decide))
    (sti_lt (by decide)) (by decide)
    (prepK_runs (k := 136) (Wc := w92) (Rc := [⟨0x6d8040, 256⟩]) c hC
      (aesGenTablesK prof hP.pc hinE hinA hinV hinX hinM hinC)
      hP.df hP.x87 hP.al (by decide) hP.hi hP.stk hWl (lo92 hP.hi hP.can) hSb
      (fun Y hs hr => by
        obtain ⟨h1, h2⟩ := hP.can' hs hr
        have := hP.hi
        unfold agPre
        omega)
      (by decide) calls92 hspec hD wrT92 wrA92 hB hXw (fun _ Z W W' hp => hG Z W W' hp))

end FV7z.Ctor
