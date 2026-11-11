import FV7z.Raf.Cuts
import FV7z.Lemmas.Rmw2
import FV7z.Sga.Holds
/-!
# `__register_atfork` adds the first fork handler (PLAN.md G3, startup)

glibc 2.31's `__register_atfork (prepare, parent, child, dso_handle)` at `0x62da60` in `7zzs`, as
`__libc_pthread_init` calls it before any other thread exists and before any handler is there: the lock at `0x7a3f20`
is taken with an unlocked `cmpxchg` and given back with `sub`, the list of handlers at `0x7a3f40` is set up (its flag
at `0x7a3f24`, its array the 48 places at `0x7a3f58`), the first place gets the four words. The words that go through
`xmm` registers (the list's `used` and `allocated`, the place's `prepare` and `parent`) are not followed: of the 88
bytes from `0x7a3f20` the theorem says nothing after the call.

- `cx_43`, `sb_170`, `ret_191`: the instructions outside the blocks.
- `Out`: bytes that differ only in a range; `rd_out2`: bytes apart from two ranges. `vc_*`: the verification
  conditions of the pieces.
- `raf_ok`: called with `fs:0x18` 0 (one thread), the lock's word 0 and the list's flag 0, the frame's 40 bytes and
  the 88 bytes in what the run may store into, the run reaches the return address with `rax` 0, the registers a call
  keeps as at the entry (`Osv.Back`), the bytes outside the frame and the 88 as they were.

The ways with more threads, a lock that is held, and a list set up before are not ones of this run.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out sk0')
namespace FV7z.Raf

/-- `cmpxchg [0x7a3f20], edx`, not locked. -/
def pcx : List Byte := [0x0f, 0xb1, 0x15, 0x8e, 0x64, 0x17, 0x00]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (FV7z.mk .cmpxchg 32 [.mem (mrip 1533070 32), gr 32 2] 7) := by dec_rfl
theorem w_43 : pcx <+: raf.drop 43 := by decide +kernel
theorem cx_43 (feat : Features) : Dec feat raf 43 (FV7z.mk .cmpxchg 32 [.mem (mrip 1533070 32), gr 32 2] 7) :=
  Dec.shift (j := 43) (k := 0) (pcx_0 feat) w_43 (Nat.zero_le _)

/-- `sub dword [0x7a3f20], 1`. -/
def psb : List Byte := [0x83, 0x2d, 0x0f, 0x64, 0x17, 0x00, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mrip 1532943 32), .imm 32 1] 7) := by dec_rfl
theorem w_170 : psb <+: raf.drop 170 := by decide +kernel
theorem sb_170 (feat : Features) : Dec feat raf 170 (FV7z.mk .sub 32 [.mem (mrip 1532943 32), .imm 32 1] 7) :=
  Dec.shift (j := 170) (k := 0) (psb_0 feat) w_170 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_191 : pret <+: raf.drop 191 := by decide +kernel
theorem ret_191 (feat : Features) : Dec feat raf 191 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 191) (k := 0) (pret_0 feat) w_191 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-! ## Bytes that differ only in a range -/

/-- `V'` is `V` outside the addresses from `lo` up to `hi`. -/
def Out (lo hi : Nat) (V V' : Addr → Byte) : Prop := ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → V' a = V a

theorem Out.mono {lo hi lo' hi' : Nat} {V V' : Addr → Byte} (h : Out lo hi V V') (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    Out lo' hi' V V' := fun a ha => h a fun hh => ha ⟨Nat.le_trans h1 hh.1, Nat.lt_of_lt_of_le hh.2 h2⟩

theorem Out.trans {lo hi : Nat} {V V' V'' : Addr → Byte} (h : Out lo hi V V') (h' : Out lo hi V' V'') :
    Out lo hi V V'' := fun a ha => (h' a ha).trans (h a ha)

/-- A store differs in its bytes. -/
theorem Out.vst {V : Addr → Byte} {a : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) : Out a.toNat (a.toNat + n) V (Vst V a bs) := fun x hx =>
  vo hn ha (by omega)

/-- Bytes apart from the range. -/
theorem Out.rd {lo hi : Nat} {V V' : Addr → Byte} (h : Out lo hi V V') {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ lo ∨ hi ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := rd_out h hx hd

/-- Bytes apart from the two ranges where `V'` is not `V`. -/
theorem rd_out2 {V V' : Addr → Byte} {lo hi lo' hi' : Nat}
    (h : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → ¬ (lo' ≤ a.toNat ∧ a.toNat < hi') → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ lo ∨ hi ≤ x.toNat)
    (hd' : x.toNat + n ≤ lo' ∨ hi' ≤ x.toNat) : List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ <;> (rw [toNat_add_of_fits hj hx]; omega)

/-- `n` bytes at `d` in `m` bytes of a list of regions. -/
theorem off_ft {R : List Rgn} {a : Addr} {m : Nat} (h : ∀ i < m, Foot R (Addr.add a i)) (d : Nat) {n : Nat} {x : Addr}
    (hx : x = a + BitVec.ofNat 64 d) (hd : d + n ≤ m) : ∀ i < n, Foot R (x.add i) := fun i hi => by
  subst hx
  have := h (d + i) (by omega)
  rwa [show Addr.add a (d + i) = (a + BitVec.ofNat 64 d).add i from by simp only [Addr.add]; bv_omega] at this

/-! ## The pieces -/

/-- The blocks from the list's flag to its first place, each a piece of its own. -/
def W50 : Wpt := fun F Wl Q => wp F Wl o2 fun g f V =>
  (f.cond 5 = true → Q 192 g (rfz f) V) ∧ (f.cond 5 = false → Q 63 g (rfz f) V)
def W63 : Wpt := fun F Wl Q => wp F Wl o3 (Q 101)
def W101 : Wpt := fun F Wl Q => wp F Wl o4 fun g f V =>
  (f.cond 4 = true → Q 154 g (rfz f) V) ∧ (f.cond 4 = false → Q 131 g (rfz f) V)
def W131 : Wpt := fun F Wl Q => wp F Wl o5 (Q 154)
theorem c50 (prof : Profile) (fb : Addr) : SpF prof raf raf_at fb 50 W50 := sp_50 prof fb
theorem c63 (prof : Profile) (fb : Addr) : SpF prof raf raf_at fb 63 W63 := sp_63 prof fb
theorem c101 (prof : Profile) (fb : Addr) : SpF prof raf raf_at fb 101 W101 := sp_101 prof fb
theorem c131 (prof : Profile) (fb : Addr) : SpF prof raf raf_at fb 131 W131 := sp_131 prof fb

/-- What the bytes `V'` at the lock have of the bytes `V` at the entry, the stack pointer `sp` and `rbx` there: all
outside the frame, in the frame `rbx`. -/
structure F0 (V V' : Addr → Byte) (sp : Addr) (rbx : BitVec 64) : Prop where
  out : Out (sp.toNat - 40) sp.toNat V V'
  sav : rdq(V', sp - 8) = rbx

/-- From the entry to the lock, one thread: the frame, `eax` 0 and `edx` 1 for the `cmpxchg`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hsp : 40 < g.rsp.toNat)
    (hst : ∀ i < 40, Foot Wl (Addr.add (g.rsp - 40#64) i)) (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i))
    (hfb : (fb + 24#64).toNat + 4 ≤ 2 ^ 64)
    (hfd : (fb + 24#64).toNat + 4 ≤ g.rsp.toNat - 40 ∨ g.rsp.toNat ≤ (fb + 24#64).toNat)
    (hmt : rdd(V, fb + 24#64) = 0) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 43 ∧
      g' = { g with rax := 0, rdx := 1, rbx := g.rdx, rsp := g.rsp - 40#64 } ∧ F0 V V' g.rsp g.rbx) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst hfd
  wpx [W_0, W_38, o0, o1, Op.ldf]
  have e : rdd(Vst (Vst (Vst V (rsp - 8) (toBytesLE rbx 8)) (rsp - 8 - 32#64 + 8#64) (toBytesLE rdi 8))
      (rsp - 8 - 32#64 + 16#64) (toBytesLE rsi 8), fb + 24#64) = 0 := by
    repeat pv
    exact hmt
  rw [e]
  refine ⟨off_ft hst 32 (by bv_omega) (by decide), off_ft hst 8 (by bv_omega) (by decide),
    off_ft hst 16 (by bv_omega) (by decide), hfl, fun h => absurd h (by decide), fun _ => ⟨?_, fun a ha => ?_, ?_⟩⟩
  · rw [show rsp - 8 - 32#64 = rsp - 40#64 from by bv_omega]
    rfl
  · repeat pv
  · repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The list's flag: not set up. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbd : ∀ i < 88, Foot F.data (Addr.add 8011552#64 i))
    (hflag : rdb(V, 8011556#64) = 0) :
    W50 F Wl (fun j' g' _ V' => j' = 63 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W50, o2, Op.cmpmia]
  refine ⟨off_ft hbd 4 (by decide) (by decide), fun h => ?_, fun _ => trivial⟩
  rw [hflag] at h
  exact absurd h (by decide)

/-- What the bytes have after the list is set up: its flag, its array's address; its two counts any. -/
structure M3 (V V' : Addr → Byte) : Prop where
  out : Out 8011556 8011608 V V'
  arr : rdq(V', 8011600#64) = 8011608#64

/-- The list set up. -/
theorem vc_63 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i))
    (hbw : ∀ i < 88, Foot Wl (Addr.add 8011552#64 i)) :
    W63 F Wl (fun j' g' _ V' => j' = 101 ∧ g' = { g with rax := 0 } ∧ M3 V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W63, o3, Op.vla, Op.vsa, Op.stia, Op.sta, BitVec.xor_self]
  refine ⟨hro, off_ft hbw 4 (by decide) (by decide), off_ft hbw 48 (by decide) (by decide),
    off_ft hbw 32 (by decide) (by decide), fun bs hbs => ⟨rfl, fun a ha => ?_, ?_⟩⟩
  · repeat pv
  · pv
    rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The first place of the array, the list's count 1. -/
theorem vc_101 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) (h50 : rdq(V, 8011600#64) = 8011608#64)
    (hbd : ∀ i < 88, Foot F.data (Addr.add 8011552#64 i)) (hbw : ∀ i < 88, Foot Wl (Addr.add 8011552#64 i)) :
    W101 F Wl (fun j' g' _ V' => j' = 131 ∧ g' = { g with rax := 1, r8 := 8011608#64 } ∧
      Out 8011584 8011592 V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0
  subst h0
  wpx [W101, o4, Op.addma, Op.sta, Op.shl64, h50]
  intro fl
  refine ⟨off_ft hbd 48 (by decide) (by decide), off_ft hbw 32 (by decide) (by decide),
    fun h => absurd h (by decide), fun _ => ⟨rfl, fun a ha => ?_⟩⟩
  pv

/-- The place's four words. -/
theorem vc_131 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : g.r8 = 8011608#64)
    (hs : ∀ i < 40, Foot F.data (Addr.add g.rsp i)) (hbw : ∀ i < 88, Foot Wl (Addr.add 8011552#64 i)) :
    W131 F Wl (fun j' g' _ V' => j' = 154 ∧ g' = g ∧ Out 8011608 8011640 V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hs
  subst h8
  wpx [W131, o5, Op.vl, Op.vs, BitVec.reduceAdd]
  refine ⟨off_ft hs 8 rfl (by decide), off_ft hbw 72 (by decide) (by decide), off_ft hbw 80 (by decide) (by decide),
    off_ft hs 16 rfl (by decide), off_ft hbw 56 (by decide) (by decide), fun bs hbs a ha => ?_⟩
  repeat pv

/-- One thread still: to the lock's `sub`. -/
theorem vc_154 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) (hmt : rdd(V, fb + 24#64) = 0) :
    W_154 fb F Wl (fun j' g' _ V' => j' = 170 ∧ g' = { g with rax := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_154, o6, Op.ldf, hmt]
  exact ⟨hfl, fun h => absurd h (by decide), fun _ => rfl⟩

/-- The answer 0 and the frame given back, to the `ret`. -/
theorem vc_177 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : g.r8 = 8011608#64)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i)) :
    W_177 fb F Wl (fun j' g' _ V' => j' = 191 ∧
      g' = { g with rax := 0, rsp := g.rsp + 40#64, rbx := rdq(V, g.rsp + 32#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hl
  subst h8
  wpx [W_177, o7, BitVec.sub_self]
  intro fl
  refine ⟨hl, ?_⟩
  rw [show rsp + 32#64 + 8 = rsp + 40#64 from by bv_omega]
  rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__register_atfork` with one thread, the lock free and the list of handlers not set up: the run reaches the
return address with `rax` 0, the bytes outside the frame and the 88 bytes of the lock and the list as they were. -/
theorem raf_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L raf_at raf)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = raf_at) (hsp : 40 < X.cpu.gpr.rsp.toNat)
    (hst : ∀ i < 40, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hbw : ∀ i < 88, Foot Wl (Addr.add 8011552#64 i)) (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i))
    (hsb : 8011640 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ 8011552)
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) (hfb : (fb + 24#64).toNat + 4 ≤ 2 ^ 64)
    (hfd : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 24#64).toNat)
    (hfbs : (fb + 24#64).toNat + 4 ≤ 8011552 ∨ 8011640 ≤ (fb + 24#64).toNat)
    (hmt : rdd(V, fb + 24#64) = 0) (hlock : rdd(V, 8011552#64) = 0) (hflag : rdb(V, 8011556#64) = 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → V' a = V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = 0 → Osv.Back X.cpu.gpr g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbd : ∀ i < 88, Foot F.data (Addr.add 8011552#64 i) := fun i hi => c.hws _ (hbw i hi)
  -- to the lock
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hsp hst hfl hfb hfd hmt) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_cmpxchg_rip32 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (cx_43 _) (g := 8011552#64) (by decide)
    (fun i hi => hbw i (by omega)) ?_ ?_
  · rw [show rv Y₁ 32 0 = 0 from by show (Y₁.cpu.gpr.get (regOf 0)).setWidth 32 = 0; rw [hg₁]; rfl, ← hlock]
    exact congrArg (ofBytesLE 32) (hF.out.rd (by decide) (by bv_omega))
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
  obtain ⟨V₂, o2, hA₂⟩ : ∃ V₂, Out 8011552 8011556 V₁ V₂ ∧ Agree F Y₂.proc.mm.mem V₂ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by decide)).mono (by decide) (by decide), hA₂⟩
  -- the list of handlers
  have hfg : rdb(V₂, 8011556#64) = 0 := by
    rw [← hflag]
    exact congrArg (ofBytesLE 8) ((o2.rd (by decide) (by decide)).trans (hF.out.rd (by decide) (by bv_omega)))
  refine (c50 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_50 hbd hfg) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  refine (c63 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ (vc_63 hro hbw) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hM⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  refine (c101 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_101 (by rw [hg₄]) hM.arr hbd hbw) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, o5⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hg₅, hg₄, hg₃, hg₂, hg₁]
  refine (c131 prof fb).run c hfs hin _ hK₅ hA₅ hr₅
    (vc_131 (by rw [hg₅]) (by rw [hsp₅]; exact fun i hi => c.hws _ (hst i hi)) hbw) ?_
  rintro j' g fl V₆ ⟨rfl, rfl, o6⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  have hb : Out 8011552 8011640 V₁ V₆ :=
    (((o2.mono (by decide) (by decide)).trans (hM.out.mono (by decide) (by decide))).trans
      (o5.mono (by decide) (by decide))).trans (o6.mono (by decide) (by decide))
  -- the lock given back
  have hz : rdd(V₆, fb + 24#64) = 0 := by
    rw [← hmt]
    exact congrArg (ofBytesLE 32) ((hb.rd hfb hfbs).trans (hF.out.rd hfb hfd))
  refine (c_154 prof fb).run c hfs hin _ hK₆ hA₆ hr₆ (vc_154 hfl hz) ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  refine c.s_sub_rip32 hK₇ hA₇ hin (lt_len (by decide)) hr₇ (sb_170 _) (g := 8011552#64) (by decide)
    (fun i hi => hbw i (by omega)) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  obtain ⟨V₈, o8, hA₈⟩ : ∃ V₈, Out 8011552 8011640 V₇ V₈ ∧ Agree F Y₈.proc.mm.mem V₈ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by decide)).mono (by decide) (by decide), hA₈⟩
  have hb8 := hb.trans o8
  have hg₈' : Y₈.cpu.gpr =
      { X.cpu.gpr with rax := 0, rdx := 1, rbx := X.cpu.gpr.rdx, rsp := X.cpu.gpr.rsp - 40#64, r8 := 8011608#64 } := by
    rw [hg₈, hg₇, hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]
  have hsp₈ : Y₈.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hg₈']
  have e8 : X.cpu.gpr.rsp - 40#64 + 32#64 = X.cpu.gpr.rsp - 8 := by bv_omega
  -- to the `ret`
  refine (c_177 prof fb).run c hfs hin _ hK₈ hA₈ hr₈ (vc_177 (by rw [hg₈']) fun i hi => ?_) ?_
  · rw [hsp₈]
    exact c.hws _ (off_ft hst 32 rfl (by decide) i hi)
  rintro j' g fl V₉ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  have hsp₉ : Y₉.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₉]
    show Y₈.cpu.gpr.rsp + 40#64 = _
    rw [hsp₈]
    bv_omega
  refine c.s_ret hK₉ hA₉ hin (lt_len (by decide)) hr₉ (ret_191 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₉]
    exact hl i hi
  · rw [hsp₉, ← hra]
    exact congrArg (ofBytesLE 64) ((hb8.rd hs8 (by omega)).trans (hF.out.rd hs8 (by omega)))
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have hbx : Y₉.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₉]
    show rdq(V₉, Y₈.cpu.gpr.rsp + 32#64) = _
    rw [hsp₈, e8, ← hF.sav]
    exact congrArg (ofBytesLE 64) (hb8.rd (by bv_omega) (by bv_omega))
  have keep : Y₉.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₉.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y₉.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₉.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₉.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₉, hg₈']
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine k V₉ _ Z t' hKZ hAZ (fun a h1 h2 => (hb8 a h2).trans (hF.out a h1)) hrZ hgZ ?_
    ⟨?_, hbx, keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1, keep.2.2.2.2⟩
  · rw [hg₉]
    rfl
  · show Y₉.cpu.gpr.rsp + 8 = _
    rw [hsp₉]
    rfl

end FV7z.Raf
