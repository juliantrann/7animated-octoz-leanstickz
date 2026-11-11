import FV7z.Ssj.Cuts
import FV7z.Sjp.Cuts
import FV7z.Lemmas.Ssp
import FV7z.Nef.Holds
import FV7z.Pim.Frame
/-!
# `_setjmp` fills the buffer and returns 0 (PLAN.md G3, startup)

glibc 2.31's `_setjmp (env)` at `0x622340` in `7zzs`, as `__libc_start_main` calls it before `main`: `esi` 0 (no
signal mask to save) and a jump to `__sigsetjmp` at `0x67e040`, which stores into `env` the registers a call keeps
(`rbx`, `r12` to `r15` as they are; `rbp`, the caller's stack pointer and the return address mangled with the pointer
guard at `fs:0x30`: xor, then rotate left by 17) and the shadow stack pointer (`rdsspq` after `xor eax, eax`: 0, the
thread has no shadow stack), then jumps to `__sigjmp_save`, which sets `mask_was_saved` 0 and returns 0.

- `jmp_6`, `ss_89`, `ret_130`: the instructions outside the blocks.
- `jbV`, `endV`, `Jb`, `end_rd`: the buffer's bytes after the stores.
- `vc_p`, `vc_0`, `vc_94`: the verification conditions of the pieces.
- `setjmp_ok`: the run reaches the return address with `rax` 0, the registers a call keeps as at the entry, the
  buffer filled (`Jb`), the bytes outside it and the 8 bytes under the stack pointer as they were.

The way with a signal mask to save (`__sigprocmask`) is not one of this call.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out sk0')
open FV7z.Raf (Out off_ft rd_out2)
namespace FV7z.Ssj

/-- `jmp __sigsetjmp` of `_setjmp`. -/
def pjm : List Byte := [0xe9, 0xf5, 0xbc, 0x05, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 376053] 5) := by dec_rfl
theorem w_6 : pjm <+: Sjp.sjp.drop 6 := by decide +kernel
theorem jmp_6 (feat : Features) : Dec feat Sjp.sjp 6 (FV7z.mk .jmp 64 [.rel 376053] 5) :=
  Dec.shift (j := 6) (k := 0) (pjm_0 feat) w_6 (Nat.zero_le _)

/-- `rdsspq rax`. -/
def pss : List Byte := [0xf3, 0x48, 0x0f, 0x1e, 0xc8]
theorem pss_0 : ∀ feat, Dec feat pss 0 (FV7z.mk .rdssp 64 [gr 64 0] 5) := by dec_rfl
theorem w_89 : pss <+: ssj.drop 89 := by decide +kernel
theorem ss_89 (feat : Features) : Dec feat ssj 89 (FV7z.mk .rdssp 64 [gr 64 0] 5) :=
  Dec.shift (j := 89) (k := 0) (pss_0 feat) w_89 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_130 : pret <+: ssj.drop 130 := by decide +kernel
theorem ret_130 (feat : Features) : Dec feat ssj 130 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 130) (k := 0) (pret_0 feat) w_130 (Nat.zero_le _)

/-! ## The buffer's bytes -/

/-- The bytes after the first six stores into the buffer at `b`. -/
abbrev jb6 (V : Addr → Byte) (b : Addr) (w0 w1 w2 w3 w4 w5 : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V b (toBytesLE w0 8)) (b + 8#64) (toBytesLE w1 8)) (b + 16#64) (toBytesLE w2 8))
    (b + 24#64) (toBytesLE w3 8)) (b + 32#64) (toBytesLE w4 8)) (b + 40#64) (toBytesLE w5 8)

/-- The bytes after the eight stores of `__sigsetjmp`'s registers into the buffer at `b`. -/
abbrev jbV (V : Addr → Byte) (b : Addr) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : Addr → Byte :=
  Vst (Vst (jb6 V b w0 w1 w2 w3 w4 w5) (b + 48#64) (toBytesLE w6 8)) (b + 56#64) (toBytesLE w7 8)

/-- The bytes at the `ret`: after those, the shadow stack pointer 0, the push of `rbx` under the stack pointer
`sp` and `mask_was_saved` 0. -/
abbrev endV (V : Addr → Byte) (b sp : Addr) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (jbV V b w0 w1 w2 w3 w4 w5 w6 w7) (b + 88#64) (toBytesLE (0#64) 8)) (sp - 8) (toBytesLE w0 8))
    (b + 64#64) (toBytesLE (0#32) 4)

/-- What the bytes `V'` at the return have of the bytes `V` at the entry, the stack pointer `sp` there, the buffer
`b`: all outside the buffer's 96 bytes and the 8 bytes under `sp`; in the buffer the eight words, `mask_was_saved`
0 and the shadow stack pointer 0. -/
structure Jb (V V' : Addr → Byte) (sp b : Addr) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : Prop where
  out : ∀ a : Addr, ¬ (sp.toNat - 8 ≤ a.toNat ∧ a.toNat < sp.toNat) →
    ¬ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 96) → V' a = V a
  w0 : rdq(V', b) = w0
  w1 : rdq(V', b + 8#64) = w1
  w2 : rdq(V', b + 16#64) = w2
  w3 : rdq(V', b + 24#64) = w3
  w4 : rdq(V', b + 32#64) = w4
  w5 : rdq(V', b + 40#64) = w5
  w6 : rdq(V', b + 48#64) = w6
  w7 : rdq(V', b + 56#64) = w7
  msk : rdd(V', b + 64#64) = 0
  ssp : rdq(V', b + 88#64) = 0

/-- The bytes at the `ret` are as `Jb` says. -/
theorem end_rd (V : Addr → Byte) (b sp : Addr) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (hb : b.toNat + 96 ≤ 2 ^ 64)
    (hs : 8 ≤ sp.toNat) (hd : b.toNat + 96 ≤ sp.toNat - 8 ∨ sp.toNat ≤ b.toNat) :
    Jb V (endV V b sp w0 w1 w2 w3 w4 w5 w6 w7) sp b w0 w1 w2 w3 w4 w5 w6 w7 := by
  refine ⟨fun a h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold endV jbV jb6
  · repeat pv
  all_goals
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    first | exact ofBytesLE_toBytesLE (n := 8) rfl _ | exact ofBytesLE_toBytesLE (n := 4) rfl _

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- The registers of `g` that the function reads or a call keeps are those of `g₀`. -/
def Sg (g₀ g : Gprs) : Prop := g.rsp = g₀.rsp ∧ g.rdi = g₀.rdi ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧
  g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- `_setjmp`: no signal mask to save. -/
theorem vc_p {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    Sjp.W_0 F Wl (fun j' g' _ V' => j' = 6 ∧ g' = { g with rsi := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Sjp.W_0, Sjp.o0]
  rw [BitVec.xor_self]
  rfl

/-- `__sigsetjmp` to its `rdsspq`: the eight words of the buffer, with the pointer guard `pg` and the return
address `ra`. -/
theorem vc_0 {fb : Addr} {g g₀ : Gprs} {f : Rflags} {V : Addr → Byte} {pg ra : BitVec 64} (hg : Sg g₀ g)
    (hw : ∀ i < 64, Foot Wl (Addr.add g₀.rdi i)) (hb : g₀.rdi.toNat + 64 ≤ 2 ^ 64)
    (hgf : ∀ i < 8, Foot F.data ((fb + 48#64).add i)) (hfb : (fb + 48#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 48#64).toNat + 8 ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + 64 ≤ (fb + 48#64).toNat)
    (hpg : rdq(V, fb + 48#64) = pg)
    (hsr : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) (hsp : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsd : g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + 64 ≤ g₀.rsp.toNat) (hra : rdq(V, g₀.rsp) = ra) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 89 ∧
      g' = { g with rax := 0, rdx := (g₀.rsp + 8#64 ^^^ pg).rotateLeft 17 } ∧
      V' = jbV V g₀.rdi g₀.rbx ((g₀.rbp ^^^ pg).rotateLeft 17) g₀.r12 g₀.r13 g₀.r14 g₀.r15
        ((g₀.rsp + 8#64 ^^^ pg).rotateLeft 17) ((ra ^^^ pg).rotateLeft 17)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rax0, rcx0, rdx0, rbx0, rsp0, rbp0, rsi0, rdi0, r80, r90, r100, r110, r120, r130, r140, r150⟩ := g₀
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hg
  dsimp only at hw hb hfd hsr hsp hsd hra
  have e1 : rdq(Vst V rdi (toBytesLE rbx 8), fb + 48#64) = pg := by
    pv
    exact hpg
  have e2 : rdq(jb6 V rdi rbx ((rbp ^^^ pg).rotateLeft 17) r12 r13 r14 r15, fb + 48#64) = pg := by
    repeat pv
    exact hpg
  have e3 : rdq(Vst (jb6 V rdi rbx ((rbp ^^^ pg).rotateLeft 17) r12 r13 r14 r15) (rdi + 48#64)
      (toBytesLE ((rsp + 8#64 ^^^ pg).rotateLeft 17) 8), rsp) = ra := by
    repeat pv
    exact hra
  have e4 : rdq(Vst (jb6 V rdi rbx ((rbp ^^^ pg).rotateLeft 17) r12 r13 r14 r15) (rdi + 48#64)
      (toBytesLE ((rsp + 8#64 ^^^ pg).rotateLeft 17) 8), fb + 48#64) = pg := by
    repeat pv
    exact hpg
  wpx [W_0, o0, Op.xormf, Op.rol64]
  simp only [e1]
  simp only [e2]
  simp only [e3, e4, BitVec.xor_self]
  exact ⟨off_ft hw 0 (by simp) (by decide), hgf, fun _ => ⟨off_ft hw 8 rfl (by decide),
    off_ft hw 16 rfl (by decide), off_ft hw 24 rfl (by decide), off_ft hw 32 rfl (by decide),
    off_ft hw 40 rfl (by decide), hgf, fun _ => ⟨off_ft hw 48 rfl (by decide), hsr, hgf,
    fun _ => ⟨off_ft hw 56 rfl (by decide), rfl, trivial⟩⟩⟩⟩

/-- From the `rdsspq` to the `ret`, no signal mask to save: the shadow stack pointer, `mask_was_saved`, the
answer 0. -/
theorem vc_94 {fb : Addr} {g g₀ : Gprs} {f : Rflags} {V : Addr → Byte} (hg : Sg g₀ g) (hax : g.rax = 0)
    (hsi : g.rsi = 0) (hw : ∀ i < 8, Foot Wl (Addr.add (g₀.rdi + 88#64) i))
    (hm : ∀ i < 4, Foot Wl (Addr.add (g₀.rdi + 64#64) i)) (hst : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i))
    (hstd : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp - 8) i)) (hsp : 8 ≤ g₀.rsp.toNat)
    (hb : g₀.rdi.toNat + 96 ≤ 2 ^ 64) (hd : g₀.rdi.toNat + 96 ≤ g₀.rsp.toNat - 8 ∨ g₀.rsp.toNat ≤ g₀.rdi.toNat) :
    W_94 fb F Wl (fun j' g' _ V' => j' = 130 ∧ g' = g ∧
      V' = Vst (Vst (Vst V (g₀.rdi + 88#64) (toBytesLE (0#64) 8)) (g₀.rsp - 8) (toBytesLE g₀.rbx 8))
        (g₀.rdi + 64#64) (toBytesLE (0#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rax0, rcx0, rdx0, rbx0, rsp0, rbp0, rsi0, rdi0, r80, r90, r100, r110, r120, r130, r140, r150⟩ := g₀
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hg
  dsimp only at hax hsi hw hm hst hstd hsp hb hd
  subst hax hsi
  have e : rdq(Vst (Vst (Vst V (rdi + 88#64) (toBytesLE (0 : BitVec 64) 8)) (rsp - 8) (toBytesLE rbx 8))
      (rdi + 64#64) (toBytesLE (0#32) 4), rsp - 8) = rbx := by
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have e8 : rsp - 8 + 8 = rsp := by bv_omega
  wpx [W_94, W_112, W_124, o1, o2, o3]
  refine ⟨hw, hst, fun h => absurd h (by decide), fun _ => ⟨hm, hstd, ?_⟩⟩
  rw [show BitVec.setWidth 32 (0 : BitVec 64) = 0#32 from rfl, e, e8, BitVec.xor_self]
  exact ⟨rfl, rfl⟩

/-! ## The call -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `_setjmp (env)`: the run reaches the return address with `rax` 0, the registers a call keeps as at the entry,
the buffer filled (`Jb`: the registers, `rbp`, the caller's stack pointer and the return address mangled with the
pointer guard, no mask saved, no shadow stack). -/
theorem setjmp_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hinp : CodeIn L Sjp.sjp_at Sjp.sjp) (hin : CodeIn L ssj_at ssj)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = Sjp.sjp_at)
    (hbw : ∀ i < 96, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hbn : X.cpu.gpr.rdi.toNat + 96 ≤ 2 ^ 64)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (hs0 : 8 ≤ X.cpu.gpr.rsp.toNat)
    (hlr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hbd : X.cpu.gpr.rdi.toNat + 96 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfd : fb.toNat + 56 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 96 ≤ fb.toNat)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Jb V V' X.cpu.gpr.rsp X.cpu.gpr.rdi X.cpu.gpr.rbx ((X.cpu.gpr.rbp ^^^ rdq(V, fb + 48#64)).rotateLeft 17)
        X.cpu.gpr.r12 X.cpu.gpr.r13 X.cpu.gpr.r14 X.cpu.gpr.r15
        ((X.cpu.gpr.rsp + 8#64 ^^^ rdq(V, fb + 48#64)).rotateLeft 17)
        ((e₂.add j₂ ^^^ rdq(V, fb + 48#64)).rotateLeft 17) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = 0 → Osv.Back X.cpu.gpr g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have f48 : (fb + 48#64).toNat = fb.toNat + 48 := by bv_omega
  have s8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have hf48 : ∀ i < 8, Foot F.data ((fb + 48#64).add i) := off_ft hft 48 rfl (by decide)
  -- `_setjmp`
  refine (Sjp.c_0 prof).run c hinp _ hK hA (by rw [addr_add_zero]; exact hrip) vc_p ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hS₁ : Sg X.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsi₁ : Y₁.cpu.gpr.rsi = 0 := by rw [hg₁]
  refine c.s_jmp_x hK₁ hA₁ hinp (Sjp.lt_len (by decide)) hr₁ (jmp_6 _) hin (lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hS₂ : Sg X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact hS₁
  have hsi₂ : Y₂.cpu.gpr.rsi = 0 := by rw [hg₂]; exact hsi₁
  -- the registers
  refine (c_0 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_0 (pg := rdq(V₁, fb + 48#64)) (ra := e₂.add j₂) hS₂
    (fun i hi => hbw i (by omega)) (by omega) hf48 (by omega) (by omega) rfl hlr hs8 (by omega) hra) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hS₃ : Sg X.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact hS₂
  have hsi₃ : Y₃.cpu.gpr.rsi = 0 := by rw [hg₃]; exact hsi₂
  have hax₃ : Y₃.cpu.gpr.rax = 0 := by rw [hg₃]
  -- the shadow stack pointer: none
  refine c.s_rdssp hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ss_89 _) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  have hS₄ : Sg X.cpu.gpr Y₄.cpu.gpr := by rw [hg₄]; exact hS₃
  -- `__sigjmp_save`
  refine (c_94 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_94 hS₄ (by rw [hg₄]; exact hax₃)
    (by rw [hg₄]; exact hsi₃) (off_ft hbw 88 rfl (by decide)) (off_ft hbw 64 rfl (by decide)) hst
    (fun i hi => c.hws _ (hst i hi)) hs0 hbn (by omega)) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hS₅ : Sg X.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact hS₄
  have hax₅ : Y₅.cpu.gpr.rax = 0 := by rw [hg₅, hg₄]; exact hax₃
  have hJ := end_rd V₁ X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr.rbx
    ((X.cpu.gpr.rbp ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) X.cpu.gpr.r12 X.cpu.gpr.r13 X.cpu.gpr.r14
    X.cpu.gpr.r15 ((X.cpu.gpr.rsp + 8#64 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17)
    ((e₂.add j₂ ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) hbn hs0 (by omega)
  -- the `ret`
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_130 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hS₅.1]
    exact hlr i hi
  · rw [hS₅.1]
    exact (congrArg (ofBytesLE 64) (rd_out2 hJ.out hs8 (by omega) (by omega))).trans hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ _ Z t' hKZ hAZ hJ hrZ hgZ hax₅
    ⟨?_, hS₅.2.2.1, hS₅.2.2.2.1, hS₅.2.2.2.2.1, hS₅.2.2.2.2.2.1, hS₅.2.2.2.2.2.2.1, hS₅.2.2.2.2.2.2.2⟩
  show Y₅.cpu.gpr.rsp + 8 = _
  rw [hS₅.1]
  rfl

end FV7z.Ssj
