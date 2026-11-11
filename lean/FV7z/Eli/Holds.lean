import FV7z.Eli.Cuts
import FV7z.Tgv.Holds
/-!
# `elision_init` (PLAN.md G3, startup)

glibc 2.31's `elision_init` at `0x5ffc50` in `7zzs` (`sysdeps/unix/sysv/linux/x86/elision-conf.c`), the one entry of
`.preinit_array` and so the first function `__libc_csu_init` calls: five `__tunable_get_val (id, &v, callback)` for
the `glibc.elision.*` tunables (ids 5, 7, 17, 4, 13 of `tunable_list`), with `v` 4 bytes of the frame, between the
stack guard's copy and its check; then, with `__pthread_force_elision` (`0x79f14c`) 0, the store of 0 into
`__elision_aconf.retry_try_xbegin` (`0x792288`). With the tunables not set (`Tgv.tgv32_ok`) no callback runs.

- `call_45` … `call_125`, `ret_171`: the instructions outside the blocks; `vc_*`: the verification conditions.
- `Env`: what the code, the frame and the two words need; `Inv`: the frame between the calls; `Fin`: at the check.
- `tcall`: one call of `__tunable_get_val` and its return, the frame kept.
- `eli_ok`: called with the five tunables not set, the run reaches the return address, the registers a call keeps
  as at the entry (`Osv.Back`), the bytes outside the 32 below the stack pointer and the 4 at `0x792288` as they were,
  these 4 holding 0 if `__pthread_force_elision` was 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Eli

/-! ## The instructions outside the blocks -/

def pc0 : List Byte := [0xe8, 0x1e, 0xf7, 0x06, 0x00]
theorem pc0_0 : ∀ feat, Dec feat pc0 0 (FV7z.mk .call 64 [.rel 456478] 5) := by dec_rfl
theorem w_45 : pc0 <+: eli.drop 45 := by decide +kernel
theorem call_45 (feat : Features) : Dec feat eli 45 (FV7z.mk .call 64 [.rel 456478] 5) :=
  Dec.shift (j := 45) (k := 0) (pc0_0 feat) w_45 (Nat.zero_le _)

def pc1 : List Byte := [0xe8, 0x0a, 0xf7, 0x06, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 456458] 5) := by dec_rfl
theorem w_65 : pc1 <+: eli.drop 65 := by decide +kernel
theorem call_65 (feat : Features) : Dec feat eli 65 (FV7z.mk .call 64 [.rel 456458] 5) :=
  Dec.shift (j := 65) (k := 0) (pc1_0 feat) w_65 (Nat.zero_le _)

def pc2 : List Byte := [0xe8, 0xf6, 0xf6, 0x06, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 456438] 5) := by dec_rfl
theorem w_85 : pc2 <+: eli.drop 85 := by decide +kernel
theorem call_85 (feat : Features) : Dec feat eli 85 (FV7z.mk .call 64 [.rel 456438] 5) :=
  Dec.shift (j := 85) (k := 0) (pc2_0 feat) w_85 (Nat.zero_le _)

def pc3 : List Byte := [0xe8, 0xe2, 0xf6, 0x06, 0x00]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 456418] 5) := by dec_rfl
theorem w_105 : pc3 <+: eli.drop 105 := by decide +kernel
theorem call_105 (feat : Features) : Dec feat eli 105 (FV7z.mk .call 64 [.rel 456418] 5) :=
  Dec.shift (j := 105) (k := 0) (pc3_0 feat) w_105 (Nat.zero_le _)

def pc4 : List Byte := [0xe8, 0xce, 0xf6, 0x06, 0x00]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 456398] 5) := by dec_rfl
theorem w_125 : pc4 <+: eli.drop 125 := by decide +kernel
theorem call_125 (feat : Features) : Dec feat eli 125 (FV7z.mk .call 64 [.rel 456398] 5) :=
  Dec.shift (j := 125) (k := 0) (pc4_0 feat) w_125 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_171 : pret <+: eli.drop 171 := by decide +kernel
theorem ret_171 (feat : Features) : Dec feat eli 171 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 171) (k := 0) (pret_0 feat) w_171 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- To the first call: `rbp` pushed, the stack guard's copy, the arguments `(5, &v, callback)`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hbp : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 16#64 + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 45 ∧
      g' = { g with rsp := g.rsp - 8 - 16#64, rdx := 6290704#64, rdi := 5, rax := 0,
                    rbp := g.rsp - 8 - 16#64 + 4#64, rsi := g.rsp - 8 - 16#64 + 4#64 } ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 16#64 + 8#64)
        (toBytesLE rdq(Vst V (g.rsp - 8) (toBytesLE g.rbp 8), fb + 40#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp hst
  wpx [W_0, o0, Op.ldf, BitVec.xor_self]
  exact ⟨hbp, hfl, hst, rfl⟩

/-- The arguments `(7, &v, callback)`. -/
theorem vc_50 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_50 fb F Wl (fun j' g' _ V' => j' = 65 ∧ g' = { g with rdx := 6290448#64, rsi := g.rbp, rdi := 7 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_50, o1]
  rfl

/-- The arguments `(17, &v, callback)`. -/
theorem vc_70 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_70 fb F Wl (fun j' g' _ V' => j' = 85 ∧ g' = { g with rdx := 6290464#64, rsi := g.rbp, rdi := 17 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_70, o2]
  rfl

/-- The arguments `(4, &v, callback)`. -/
theorem vc_90 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_90 fb F Wl (fun j' g' _ V' => j' = 105 ∧ g' = { g with rdx := 6290480#64, rsi := g.rbp, rdi := 4 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_90, o3]
  rfl

/-- The arguments `(13, &v, callback)`. -/
theorem vc_110 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_110 fb F Wl (fun j' g' _ V' => j' = 125 ∧ g' = { g with rdx := 6290496#64, rsi := g.rbp, rdi := 13 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_110, o4]
  rfl

/-- `__pthread_force_elision`: not 0, nothing; 0, `__elision_aconf.retry_try_xbegin := 0`. -/
theorem vc_130 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfe : ∀ i < 4, Foot F.data (Addr.add 7991628#64 i)) (hrt : ∀ i < 4, Foot Wl (Addr.add 7938696#64 i)) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 150 ∧ g' = { g with rax := BitVec.setWidth 64 rdd(V, 7991628#64) } ∧
      (rdd(V, 7991628#64) ≠ 0 ∧ V' = V ∨
        rdd(V, 7991628#64) = 0 ∧ V' = Vst V 7938696#64 (toBytesLE (0 : BitVec 32) 4))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_130, W_140, o5, o6, Op.lda, Op.stia, BitVec.and_self]
  refine ⟨hfe, fun h => .inl ?_, fun h => ⟨hrt, .inr ⟨?_, rfl⟩⟩⟩
  · simpa using h
  · simpa using h

/-- The check of the stack guard, to the `ret`. -/
theorem vc_150 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (hp : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_150 fb F Wl (fun j' g' _ V' => j' = 171 ∧
      g' = { g with rax := 0, rsp := g.rsp + 16#64 + 8, rbp := rdq(V, g.rsp + 16#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc hp
  wpx [W_150, W_166, o7, o8, Op.xormf, hc, BitVec.xor_self]
  exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => ⟨hp, rfl⟩⟩

/-! ## The frame -/

theorem a_sp (S : Addr) : S - 8 - 16#64 = S - 24#64 := by bv_omega
theorem a_can (S : Addr) : S - 8 - 16#64 + 8#64 = S - 16#64 := by bv_omega
theorem a_v (S : Addr) : S - 8 - 16#64 + 4#64 = S - 20#64 := by bv_omega
theorem a_ra (S : Addr) : S - 24#64 - 8 = S - 32#64 := by bv_omega
theorem a_bk (S : Addr) : S - 32#64 + 8#64 = S - 24#64 := by bv_omega
theorem b_ra (S : Addr) : S - 32#64 = S - 32#64 + BitVec.ofNat 64 0 := by bv_omega
theorem b_v (S : Addr) : S - 20#64 = S - 32#64 + BitVec.ofNat 64 12 := by bv_omega
theorem b_can (S : Addr) : S - 16#64 = S - 32#64 + BitVec.ofNat 64 16 := by bv_omega
theorem b_bp (S : Addr) : S - 8#64 = S - 32#64 + BitVec.ofNat 64 24 := by bv_omega
theorem e_can (S : Addr) : S - 24#64 + 8#64 = S - 16#64 := by bv_omega
theorem e_bp (S : Addr) : S - 24#64 + 16#64 = S - 8#64 := by bv_omega
theorem e_sp (S : Addr) : S - 8#64 + 8 = S := by bv_omega

/-- The frame's addresses as numbers. -/
theorem tn {S : Addr} (h : 32 < S.toNat) : (S - 32#64).toNat = S.toNat - 32 ∧ (S - 20#64).toNat = S.toNat - 20 ∧
    (S - 16#64).toNat = S.toNat - 16 ∧ (S - 8#64).toNat = S.toNat - 8 := by bv_omega

/-- A tunable's two bytes' addresses as numbers. -/
theorem en {d : Addr} (h : (Tgv.ent d).toNat + 48 ≤ 7991632) :
    (Tgv.ent d + 40#64).toNat = (Tgv.ent d).toNat + 40 := by bv_omega

/-- What `elision_init` needs of the code, of the 32 bytes below the stack pointer `S` at its entry, of the stack
guard at `fs:0x28` and of the two words: the frame in what the run may store into, above the data (to
`__pthread_force_elision`'s end), the guard apart from the frame and from `retry_try_xbegin`. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb S : Addr) : Prop where
  code : CodeIn L eli_at eli
  tcode : CodeIn L Tgv.tgv_at Tgv.tgv
  s0 : 32 < S.toNat
  s8 : S.toNat + 8 ≤ 2 ^ 64
  hi : 7991632 ≤ S.toNat - 32
  st : ∀ i < 32, Foot Wl (Addr.add (S - 32#64) i)
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  fl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fb8 : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  fd : (fb + 40#64).toNat + 8 ≤ S.toNat - 32 ∨ S.toNat ≤ (fb + 40#64).toNat
  fg : (fb + 40#64).toNat + 8 ≤ 7938696 ∨ 7938700 ≤ (fb + 40#64).toNat
  fe : ∀ i < 4, Foot F.data (Addr.add 7991628#64 i)
  rt : ∀ i < 4, Foot Wl (Addr.add 7938696#64 i)

/-- The frame between the calls: the bytes outside it as at the entry (`V₀`), the stack guard's copy, the saved
`rbp`. -/
structure Inv (fb S rb : Addr) (V₀ V : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 32 ≤ a.toNat ∧ a.toNat < S.toNat) → V a = V₀ a
  can : rdq(V, S - 16#64) = rdq(V₀, fb + 40#64)
  bp : rdq(V, S - 8#64) = rb

/-- After the prologue. -/
theorem inv0 {fb S rb : Addr} {V : Addr → Byte} (hs : 32 < S.toNat) (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ S.toNat - 32 ∨ S.toNat ≤ (fb + 40#64).toNat) :
    Inv fb S rb V (Vst (Vst V (S - 8#64) (toBytesLE rb 8)) (S - 16#64)
      (toBytesLE rdq(Vst V (S - 8#64) (toBytesLE rb 8), fb + 40#64) 8)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · pv
    pv
  · rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]
    pv
  · pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- A return address pushed: outside the frame nothing. -/
theorem Inv.push {fb S rb : Addr} {V₀ V : Addr → Byte} (hs : 32 < S.toNat) (h : Inv fb S rb V₀ V) (x : BitVec 64) :
    ∀ a : Addr, ¬ (S.toNat - 32 ≤ a.toNat ∧ a.toNat < S.toNat) → Vst V (S - 32#64) (toBytesLE x 8) a = V₀ a := by
  intro a ha
  pv
  exact h.out a ha

/-- The return address pushed. -/
theorem rd_ra {S : Addr} {V : Addr → Byte} (hs : 32 < S.toNat) (x : BitVec 64) :
    rdq(Vst V (S - 32#64) (toBytesLE x 8), S - 32#64) = x := by
  rw [vs (by ln) (by bv_omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- A return address pushed and `v` stored: the frame as it was. -/
theorem Inv.step {fb S rb : Addr} {V₀ V : Addr → Byte} (hs : 32 < S.toNat) (h : Inv fb S rb V₀ V) (x : BitVec 64)
    (w : BitVec 32) : Inv fb S rb V₀ (Vst (Vst V (S - 32#64) (toBytesLE x 8)) (S - 20#64) (toBytesLE w 4)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · pv
    pv
    exact h.out a ha
  · pv
    pv
    exact h.can
  · pv
    pv
    exact h.bp

/-- At the stack guard's check: the bytes outside the frame and `retry_try_xbegin` as at the entry, the guard's copy
the guard, the saved `rbp`, the return address, `retry_try_xbegin` 0 if `__pthread_force_elision` was. -/
structure Fin (fb S rb : Addr) (V₀ V : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 32 ≤ a.toNat ∧ a.toNat < S.toNat) → ¬ (7938696 ≤ a.toNat ∧ a.toNat < 7938700) →
    V a = V₀ a
  can : rdq(V, S - 16#64) = rdq(V, fb + 40#64)
  bp : rdq(V, S - 8#64) = rb
  ra : rdq(V, S) = rdq(V₀, S)
  z : rdd(V₀, 7991628#64) = 0 → rdd(V, 7938696#64) = 0

/-- `__pthread_force_elision` not 0. -/
theorem Inv.fin_same {fb S rb : Addr} {V₀ V : Addr → Byte} {L : List (Addr × List Byte)} (hE : Env F Wl L fb S)
    (h : Inv fb S rb V₀ V) (hne : rdd(V, 7991628#64) ≠ 0) : Fin fb S rb V₀ V := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hhi := hE.hi
  refine ⟨fun a ha _ => h.out a ha, ?_, h.bp, ?_, fun hz => absurd ?_ hne⟩
  · rw [h.can]
    exact (congrArg (ofBytesLE 64) (rd_out h.out hE.fb8 hE.fd)).symm
  · exact congrArg (ofBytesLE 64) (rd_out h.out hs8 (by omega))
  · rw [← hz]
    exact congrArg (ofBytesLE 32) (rd_out h.out (by decide) (.inl (by show 7991628 + 4 ≤ _; omega)))

/-- `__pthread_force_elision` 0: after the store. -/
theorem Inv.fin_st {fb S rb : Addr} {V₀ V : Addr → Byte} {L : List (Addr × List Byte)} (hE : Env F Wl L fb S)
    (h : Inv fb S rb V₀ V) : Fin fb S rb V₀ (Vst V 7938696#64 (toBytesLE (0 : BitVec 32) 4)) := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hhi := hE.hi
  have hfb := hE.fb8
  have hfg := hE.fg
  obtain ⟨n32, n20, n16, n8⟩ := tn hs0
  refine ⟨fun a ha hb => ?_, ?_, ?_, ?_, fun _ => ?_⟩
  · rw [vo (by ln) (by decide) (by show a.toNat < 7938696 ∨ 7938696 + 4 ≤ a.toNat; omega)]
    exact h.out a ha
  · rw [vr (by ln) (by decide) (by omega) (by show 7938696 + 4 ≤ _ ∨ _ + 8 ≤ 7938696; omega),
      vr (by ln) (by decide) hfb (by show 7938696 + 4 ≤ _ ∨ _ + 8 ≤ 7938696; omega), h.can]
    exact (congrArg (ofBytesLE 64) (rd_out h.out hfb hE.fd)).symm
  · rw [vr (by ln) (by decide) (by omega) (by show 7938696 + 4 ≤ _ ∨ _ + 8 ≤ 7938696; omega)]
    exact h.bp
  · rw [vr (by ln) (by decide) (by omega) (by show 7938696 + 4 ≤ _ ∨ _ + 8 ≤ 7938696; omega)]
    exact congrArg (ofBytesLE 64) (rd_out h.out hs8 (by omega))
  · rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _

/-- The registers `elision_init` does not use. -/
def Sv (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Sv.trans {g g' g'' : Gprs} (h : Sv g g') (h' : Sv g' g'') : Sv g g'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-! ## The calls -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- One call `__tunable_get_val (d, &v, callback)` for a tunable not set, from the `call` at `jc` to the instruction
after it: the frame kept. -/
theorem tcall {fb S rb d : Addr} {V₀ V₁ : Addr → Byte} {Y : State} {jc r : Nat} (c : Seg prof F Wl L s₀ o)
    (hE : Env F Wl L fb S) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hI : Inv fb S rb V₀ V₁)
    (hU : Tgv.Unset F V₀ d) (hdl : (Tgv.ent d).toNat + 48 ≤ 7991632) (hjc : jc + 5 < 177)
    (hr : Y.cpu.rip = eli_at.add jc) (hdec : Dec prof.feat eli jc (FV7z.mk .call 64 [.rel r] 5))
    (htgt : eli_at.add (jc + 5) + BitVec.ofNat 64 r = Tgv.tgv_at)
    (hsp : Y.cpu.gpr.rsp = S - 24#64) (hsi : Y.cpu.gpr.rsi = S - 20#64) (hbp : Y.cpu.gpr.rbp = S - 20#64)
    (hdi : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rdi) = d)
    (k : ∀ V₂ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Inv fb S rb V₀ V₂ → Z.cpu.rip = eli_at.add (jc + 5) →
      Z.cpu.gpr.rsp = S - 24#64 → Z.cpu.gpr.rbp = S - 20#64 → Sv Y.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') : GoG prof L o gev gP gE Y t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hhi := hE.hi
  obtain ⟨n32, n20, n16, n8⟩ := tn hs0
  have n40 := en hdl
  refine c.s_call hK hA hE.code (lt_len (by omega)) hr hdec hE.tcode (Tgv.lt_len (by decide)) htgt
    (fun i hi => ?_) ?_
  · rw [hsp, a_ra]
    exact off_ft hE.st 0 (b_ra S) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp, a_ra] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = S - 32#64 := by rw [hg₂]; rfl
  have hsi₂ : Y₂.cpu.gpr.rsi = S - 20#64 := by rw [hg₂]; exact hsi
  have hU₁ := hU.out (lo := S.toNat - 32) (hi := S.toNat) (by omega) (by omega) (hI.push hs0 (eli_at.add (jc + 5)))
  refine Tgv.tgv32_ok (d := d) c hE.tcode hK₂ hA₂ hr₂ (by rw [hg₂]; exact hdi) hU₁.ty hU₁.va hU₁.ini hU₁.t0 hU₁.z
    (fun i hi => ?_) (by rw [hsi₂]; omega) (by rw [hsi₂]; omega) (fun i hi => ?_) hE.code (j₂ := jc + 5)
    (lt_len hjc) (by rw [hsp₂]; exact rd_ra hs0 _) (by rw [hsp₂]; omega) (by rw [hsp₂, hsi₂]; omega) ?_
  · rw [hsi₂]
    exact off_ft hE.st 12 (b_v S) (by decide) i hi
  · rw [hsp₂]
    exact c.hws _ (off_ft hE.st 0 (b_ra S) (by decide) i hi)
  intro g₃ Z t₃ hK₃ hA₃ hr₃ hg₃ hbk₃
  rw [hsi₂] at hA₃
  refine k _ Z t₃ hK₃ hA₃ (hI.step hs0 _ _) hr₃ ?_ ?_ ?_
  · rw [hg₃, hbk₃.1, hsp₂]
    exact a_bk S
  · rw [hg₃, hbk₃.2.2.1, hg₂]
    exact hbp
  · rw [hg₃]
    obtain ⟨-, k1, -, k3, k4, k5, k6⟩ := hbk₃
    rw [hg₂] at k1 k3 k4 k5 k6
    exact ⟨k1, k3, k4, k5, k6⟩

/-- `elision_init` with the five `glibc.elision.*` tunables not set: the run reaches the return address, the
registers a call keeps as at the entry, the bytes outside its 32 and `retry_try_xbegin` as they were. -/
theorem eli_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hE : Env F Wl L fb X.cpu.gpr.rsp) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = eli_at) (h5 : Tgv.Unset F V 5) (h7 : Tgv.Unset F V 7) (h17 : Tgv.Unset F V 17)
    (h4 : Tgv.Unset F V 4) (h13 : Tgv.Unset F V 13)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (7938696 ≤ a.toNat ∧ a.toNat < 7938700) → V' a = V a) →
      (rdd(V, 7991628#64) = 0 → rdd(V', 7938696#64) = 0) →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs0 := hE.s0
  -- the prologue
  refine (c_0 prof fb).run c hfs hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (off_ft hE.st 24 (b_bp _) (by decide)) hE.fl (by rw [a_can]; exact off_ft hE.st 16 (b_can _) (by decide)))
    ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [a_can, show X.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 from rfl] at hA₁
  have hI₁ : Inv fb X.cpu.gpr.rsp X.cpu.gpr.rbp V _ := inv0 hs0 hE.fb8 hE.fd
  have s₁ : Sv X.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- `glibc.elision.enable`
  refine tcall (d := 5) c hE hK₁ hA₁ hI₁ h5 (by decide) (by decide) hr₁ (call_45 _) (by decide)
    (by rw [hg₁]; exact a_sp _) (by rw [hg₁]; exact a_v _) (by rw [hg₁]; exact a_v _) (by rw [hg₁]; rfl) ?_
  intro V₂ Y₂ t₂ hK₂ hA₂ hI₂ hr₂ hsp₂ hbp₂ s₂
  refine (c_50 prof fb).run c hfs hE.code _ hK₂ hA₂ hr₂ vc_50 ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have s₃ : Sv X.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact s₁.trans s₂
  -- `glibc.elision.skip_lock_busy`
  refine tcall (d := 7) c hE hK₃ hA₃ hI₂ h7 (by decide) (by decide) hr₃ (call_65 _) (by decide)
    (by rw [hg₃]; exact hsp₂) (by rw [hg₃]; exact hbp₂) (by rw [hg₃]; exact hbp₂) (by rw [hg₃]; rfl) ?_
  intro V₄ Y₄ t₄ hK₄ hA₄ hI₄ hr₄ hsp₄ hbp₄ s₄
  refine (c_70 prof fb).run c hfs hE.code _ hK₄ hA₄ hr₄ vc_70 ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have s₅ : Sv X.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact s₃.trans s₄
  -- `glibc.elision.skip_lock_internal_abort`
  refine tcall (d := 17) c hE hK₅ hA₅ hI₄ h17 (by decide) (by decide) hr₅ (call_85 _) (by decide)
    (by rw [hg₅]; exact hsp₄) (by rw [hg₅]; exact hbp₄) (by rw [hg₅]; exact hbp₄) (by rw [hg₅]; rfl) ?_
  intro V₆ Y₆ t₆ hK₆ hA₆ hI₆ hr₆ hsp₆ hbp₆ s₆
  refine (c_90 prof fb).run c hfs hE.code _ hK₆ hA₆ hr₆ vc_90 ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have s₇ : Sv X.cpu.gpr Y₇.cpu.gpr := by rw [hg₇]; exact s₅.trans s₆
  -- `glibc.elision.tries`
  refine tcall (d := 4) c hE hK₇ hA₇ hI₆ h4 (by decide) (by decide) hr₇ (call_105 _) (by decide)
    (by rw [hg₇]; exact hsp₆) (by rw [hg₇]; exact hbp₆) (by rw [hg₇]; exact hbp₆) (by rw [hg₇]; rfl) ?_
  intro V₈ Y₈ t₈ hK₈ hA₈ hI₈ hr₈ hsp₈ hbp₈ s₈
  refine (c_110 prof fb).run c hfs hE.code _ hK₈ hA₈ hr₈ vc_110 ?_
  rintro j' g fl V₉ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  have s₉ : Sv X.cpu.gpr Y₉.cpu.gpr := by rw [hg₉]; exact s₇.trans s₈
  -- `glibc.elision.skip_trylock_internal_abort`
  refine tcall (d := 13) c hE hK₉ hA₉ hI₈ h13 (by decide) (by decide) hr₉ (call_125 _) (by decide)
    (by rw [hg₉]; exact hsp₈) (by rw [hg₉]; exact hbp₈) (by rw [hg₉]; exact hbp₈) (by rw [hg₉]; rfl) ?_
  intro Va Ya ta hKa hAa hIa hra' hspa hbpa sa
  -- `__pthread_force_elision`
  refine (c_130 prof fb).run c hfs hE.code _ hKa hAa hra' (vc_130 hE.fe hE.rt) ?_
  rintro j' g fl Vb ⟨rfl, rfl, hVb⟩ Yb tb hKb hAb hrb hgb -
  have hF : Fin fb X.cpu.gpr.rsp X.cpu.gpr.rbp V Vb := by
    rcases hVb with ⟨hne, rfl⟩ | ⟨-, rfl⟩
    · exact hIa.fin_same hE hne
    · exact hIa.fin_st hE
  have hspb : Yb.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hgb]; exact hspa
  have sb : Sv X.cpu.gpr Yb.cpu.gpr := by rw [hgb]; exact s₉.trans sa
  -- the stack guard's check, the epilogue
  refine (c_150 prof fb).run c hfs hE.code _ hKb hAb hrb (vc_150 (fun i hi => ?_) hE.fl ?_ (fun i hi => ?_)) ?_
  · rw [hspb, e_can]
    exact c.hws _ (off_ft hE.st 16 (b_can _) (by decide) i hi)
  · rw [hspb, e_can]
    exact hF.can
  · rw [hspb, e_bp]
    exact c.hws _ (off_ft hE.st 24 (b_bp _) (by decide) i hi)
  rintro j' g fl Vc ⟨rfl, rfl, rfl⟩ Yc tc hKc hAc hrc hgc -
  have hspc : Yc.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hgc]
    show Yb.cpu.gpr.rsp + 16#64 + 8 = _
    rw [hspb, e_bp]
    exact e_sp _
  have hbpc : Yc.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hgc]
    show rdq(Vc, Yb.cpu.gpr.rsp + 16#64) = _
    rw [hspb, e_bp]
    exact hF.bp
  have sc : Sv X.cpu.gpr Yc.cpu.gpr := by rw [hgc]; exact sb
  refine c.s_ret hKc hAc hE.code (lt_len (by decide)) hrc (ret_171 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hspc]
    exact hE.lr i hi
  · rw [hspc, hF.ra]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Vc Z t' hKZ hAZ hF.out hF.z hrZ ?_
  rw [hgZ]
  refine ⟨?_, sc.1, hbpc, sc.2.1, sc.2.2.1, sc.2.2.2.1, sc.2.2.2.2⟩
  show Yc.cpu.gpr.rsp + 8 = _
  rw [hspc]
  rfl

end FV7z.Eli
