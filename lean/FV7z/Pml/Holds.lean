import FV7z.Pml.Cuts
import FV7z.Lemmas.Lock2
import FV7z.Osv.Holds
import FV7z.Raf.Holds
/-!
# `pthread_mutex_lock`, the plain way (PLAN.md G3, pthread)

glibc 2.31's `__pthread_mutex_lock` at `0x5fc450` in `7zzs` (`nptl/pthread_mutex_lock.c`) on a mutex of the plain
kind (`__kind` 0) that nobody holds, `__pthread_force_elision` 0: `lock cmpxchg` takes the lock word from 0 to 1,
`__owner := THREAD_SELF->tid` (`fs:0x2d0`), `__nusers += 1`, the answer 0. The other ways (another kind, elision,
the lock held: `__lll_lock_wait`) are outside this unit.

- `cx_47`, `add_79`, `ret_91`: the instructions outside the blocks; `vc_0`, `vc_51`, `vc_83`: the verification
  conditions.
- `Env`: what the code, the 8 bytes of the frame, the mutex's 20 bytes and the two words read need; `M1`, `M2`: the
  memory after the lock is taken and at the end; `Dat`: what the caller gets.
- `pml_ok`: called on such a mutex, the run reaches the return address with `rax = 0`, the registers a call keeps
  as at the entry (`Osv.Back`), the lock word 1, the owner the thread's id, one more user, the other bytes outside
  the 8 below the stack pointer as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Pml

/-! ## The instructions outside the blocks -/

def pcx : List Byte := [0xf0, 0x0f, 0xb1, 0x17]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (lockCmpxchgB32 7 0 2 4) := by dec_rfl
theorem w_47 : pcx <+: pml.drop 47 := by decide +kernel
/-- `lock cmpxchg dword [rdi], edx`. -/
theorem cx_47 (feat : Features) : Dec feat pml 47 (lockCmpxchgB32 7 0 2 4) :=
  Dec.shift (j := 47) (k := 0) (pcx_0 feat) w_47 (Nat.zero_le _)

def pad : List Byte := [0x83, 0x47, 0x0c, 0x01]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 7 12 32), .imm 32 1] 4) := by dec_rfl
theorem w_79 : pad <+: pml.drop 79 := by decide +kernel
/-- `add dword [rdi + 12], 1`. -/
theorem add_79 (feat : Features) : Dec feat pml 79 (FV7z.mk .add 32 [.mem (mbd 7 12 32), .imm 32 1] 4) :=
  Dec.shift (j := 79) (k := 0) (pad_0 feat) w_79 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_91 : pret <+: pml.drop 91 := by decide +kernel
theorem ret_91 (feat : Features) : Dec feat pml 91 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 91) (k := 0) (pret_0 feat) w_91 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `lock cmpxchg`: the kind plain, no elision. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hk : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 16#64) i)) (hkd : rdd(V, g.rdi + 16#64) = 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hf : ∀ i < 4, Foot F.data (Addr.add (7991628#64) i))
    (hfe : rdd(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), 7991628#64) = 0) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 47 ∧
      g' = { g with rax := 0, rcx := 0, rdx := 1, rsp := g.rsp - 8 - 16#64 } ∧
      V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hk hkd hst hf hfe
  wpx [W_0, W_21, W_30, W_40, o0, o1, o2, o3, Op.lda, hkd, hfe, BitVec.xor_self, BitVec.and_self, BitVec.zero_and]
  exact ⟨hk, fun h => absurd h (by decide), fun _ => ⟨hst, fun h => absurd h (by decide), fun _ =>
    ⟨hf, fun h => absurd h (by decide), fun _ => rfl⟩⟩⟩

/-- From the lock taken to the count of users: nobody owned the mutex. -/
theorem vc_51 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : f.zf = true)
    (ho : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (how : rdd(V, g.rdi + 8#64) = 0)
    (ht : ∀ i < 4, Foot F.data (Addr.add (fb + 720#64) i)) (hw : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i)) :
    W_51 fb F Wl (fun j' g' _ V' => j' = 79 ∧
      g' = { g with rax := BitVec.setWidth 64 rdd(V, fb + 720#64), rdx := 0 } ∧
      V' = Vst V (g.rdi + 8#64) (toBytesLE rdd(V, fb + 720#64) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ho how ht hw
  wpx [W_51, W_57, W_68, o4, o5, Op.ldf, hz, how, BitVec.and_self]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨ho, fun h => absurd h (by decide), fun _ => ⟨ht, hw, rfl⟩⟩⟩

/-- The epilogue. -/
theorem vc_83 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_83 fb F Wl (fun j' g' _ V' => j' = 91 ∧
      g' = { g with rax := 0, rbx := rdq(V, g.rsp + 16#64), rsp := g.rsp + 16#64 + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb
  wpx [W_83, W_86, o6, o7, BitVec.xor_self]
  exact ⟨hb, rfl⟩

/-! ## The memory -/

/-- What `pthread_mutex_lock` on the mutex at `m`, called with the stack pointer `S` in the thread whose block is at
`fb`, needs of the code and the memory: the 8 bytes below `S` and the mutex's 20 for the run to store into, apart
from each other; the return address, the thread's id and `__pthread_force_elision` to read; the lock word within
one cache line. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb S m : Addr) : Prop where
  code : CodeIn L pml_at pml
  s0 : 7991632 + 24 ≤ S.toNat
  s8 : S.toNat + 8 ≤ 2 ^ 64
  m0 : m.toNat + 20 ≤ S.toNat - 24 ∨ S.toNat + 8 ≤ m.toNat
  m8 : m.toNat + 20 ≤ 2 ^ 64
  ml : m.toNat % 64 + 4 ≤ 64
  f0 : fb.toNat + 724 ≤ 2 ^ 64
  f1 : fb.toNat + 724 ≤ S.toNat - 8 ∨ S.toNat ≤ fb.toNat + 720
  f2 : fb.toNat + 724 ≤ m.toNat ∨ m.toNat + 4 ≤ fb.toNat + 720
  st : ∀ i < 8, Foot Wl (Addr.add (S - 8#64) i)
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  mu : ∀ i < 20, Foot Wl (Addr.add m i)
  tid : ∀ i < 4, Foot F.data (Addr.add (fb + 720#64) i)
  fe : ∀ i < 4, Foot F.data (Addr.add (7991628#64) i)

/-- The memory once `rbx` is pushed and the lock taken. -/
abbrev M1 (V : Addr → Byte) (S m : Addr) (rb : BitVec 64) : Addr → Byte :=
  Vst (Vst V (S - 8#64) (toBytesLE rb 8)) m (toBytesLE (1#32) 4)

/-- The memory at the end: the owner `tid`, one more user. -/
abbrev M2 (V : Addr → Byte) (S m : Addr) (rb : BitVec 64) (tid : BitVec 32) : Addr → Byte :=
  Vst (Vst (M1 V S m rb) (m + 8#64) (toBytesLE tid 4)) (m + 12#64)
    (toBytesLE (rdd(Vst (M1 V S m rb) (m + 8#64) (toBytesLE tid 4), m + 12#64) + 1#32) 4)

/-- What the caller gets: the bytes outside the 8 below `S`, the lock word and the owner and the count of users as
they were; the lock word 1, the owner `tid`, one more user. -/
structure Dat (S m : Addr) (tid : BitVec 32) (V V' : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 8 ≤ a.toNat ∧ a.toNat < S.toNat) → ¬ (m.toNat ≤ a.toNat ∧ a.toNat < m.toNat + 4) →
    ¬ (m.toNat + 8 ≤ a.toNat ∧ a.toNat < m.toNat + 16) → V' a = V a
  lock : rdd(V', m) = 1
  own : rdd(V', m + 8#64) = tid
  nus : rdd(V', m + 12#64) = rdd(V, m + 12#64) + 1

section
variable {fb S m : Addr} {V : Addr → Byte} (rb : BitVec 64)

/-- `__pthread_force_elision` is not the pushed `rbx`. -/
theorem m0_fe (hs0 : 7991632 + 24 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) :
    rdd(Vst V (S - 8#64) (toBytesLE rb 8), 7991628#64) = rdd(V, 7991628#64) := by
  pv

/-- The lock word is not the pushed `rbx`. -/
theorem m0_lk (hs0 : 7991632 + 24 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hm0 : m.toNat + 20 ≤ S.toNat - 24 ∨ S.toNat + 8 ≤ m.toNat) (hm8 : m.toNat + 20 ≤ 2 ^ 64) :
    rdd(Vst V (S - 8#64) (toBytesLE rb 8), m) = rdd(V, m) := by
  pv

/-- The owner once the lock is taken. -/
theorem m1_own (hs0 : 7991632 + 24 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hm0 : m.toNat + 20 ≤ S.toNat - 24 ∨ S.toNat + 8 ≤ m.toNat) (hm8 : m.toNat + 20 ≤ 2 ^ 64) :
    rdd(M1 V S m rb, m + 8#64) = rdd(V, m + 8#64) := by
  unfold M1
  pv
  pv

/-- The thread's id once the lock is taken. -/
theorem m1_tid (hs0 : 7991632 + 24 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) (hm8 : m.toNat + 20 ≤ 2 ^ 64)
    (hf0 : fb.toNat + 724 ≤ 2 ^ 64) (hf1 : fb.toNat + 724 ≤ S.toNat - 8 ∨ S.toNat ≤ fb.toNat + 720)
    (hf2 : fb.toNat + 724 ≤ m.toNat ∨ m.toNat + 4 ≤ fb.toNat + 720) :
    rdd(M1 V S m rb, fb + 720#64) = rdd(V, fb + 720#64) := by
  unfold M1
  pv
  pv

/-- The memory at the end. -/
theorem m2_dat (tid : BitVec 32) (hs0 : 7991632 + 24 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hm0 : m.toNat + 20 ≤ S.toNat - 24 ∨ S.toNat + 8 ≤ m.toNat) (hm8 : m.toNat + 20 ≤ 2 ^ 64) :
    Dat S m tid V (M2 V S m rb tid) ∧ rdq(M2 V S m rb tid, S - 8#64) = rb ∧
      rdq(M2 V S m rb tid, S) = rdq(V, S) := by
  refine ⟨⟨fun a h1 h2 h3 => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold M2 M1
    repeat pv
  · unfold M2 M1
    pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · unfold M2
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · unfold M2
    rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 4) rfl _]
    unfold M1
    repeat pv
    rfl
  · unfold M2 M1
    pv
    pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · unfold M2 M1
    repeat pv

end

/-! ## The whole -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

theorem a_sp (S : Addr) : S - 8 - 16#64 + 16#64 = S - 8#64 := by bv_omega
theorem a_bk (S : Addr) : S - 8 - 16#64 + 16#64 + 8 = S := by bv_omega

/-- `pthread_mutex_lock (m)` on a mutex of the plain kind that nobody holds, no elision: the run reaches the return
address with `rax = 0`, the registers a call keeps as at the entry, the mutex taken by this thread (`Dat`). -/
theorem pml_ok {fb : Addr} {tid : BitVec 32} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hE : Env F Wl L fb X.cpu.gpr.rsp X.cpu.gpr.rdi) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pml_at) (hkd : rdd(V, X.cpu.gpr.rdi + 16#64) = 0) (hfe : rdd(V, 7991628#64) = 0)
    (hlk : rdd(V, X.cpu.gpr.rdi) = 0) (how : rdd(V, X.cpu.gpr.rdi + 8#64) = 0) (htid : rdd(V, fb + 720#64) = tid)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat X.cpu.gpr.rsp X.cpu.gpr.rdi tid V V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hm0 := hE.m0
  have hm8 := hE.m8
  -- to the `lock cmpxchg`
  refine (c_0 prof fb).run c hfs hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (fun i hi => c.hws _ (off_ft hE.mu 16 rfl (by decide) i hi)) hkd hE.st hE.fe
      ((m0_fe _ hs0 hs8).trans hfe)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [show X.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 from rfl] at hA₁
  have e0 : eaD Y₁ 7 0 = X.cpu.gpr.rdi := by
    show Y₁.cpu.gpr.rdi + 0#64 = _
    rw [hg₁]
    exact BitVec.add_zero _
  refine c.s_lock_cmpxchg_bd32 hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (cx_47 _) (by rw [e0]; exact hE.ml)
    (by rw [e0]; exact fun i hi => hE.mu i (by omega)) ?_ ?_
  · rw [e0, show rv Y₁ 32 0 = 0#32 from by show Y₁.cpu.gpr.rax.setWidth 32 = _; rw [hg₁]; rfl]
    exact (m0_lk _ hs0 hs8 hm0 hm8).trans hlk
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hz₂⟩
  rw [e0, show rv Y₁ 32 2 = 1#32 from by show Y₁.cpu.gpr.rdx.setWidth 32 = _; rw [hg₁]; rfl] at hA₂
  have hd₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁]
  -- the owner
  refine (c_51 prof fb).run c hfs hE.code _ hK₂ hA₂ hr₂
    (vc_51 hz₂ (fun i hi => ?_) ?_ hE.tid (fun i hi => ?_)) ?_
  · rw [hd₂]
    exact c.hws _ (off_ft hE.mu 8 rfl (by decide) i hi)
  · rw [hd₂]
    exact (m1_own _ hs0 hs8 hm0 hm8).trans how
  · rw [hd₂]
    exact off_ft hE.mu 8 rfl (by decide) i hi
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hd₂, show rdd(_, fb + 720#64) = tid from
    (m1_tid (V := V) X.cpu.gpr.rbx hs0 hs8 hm8 hE.f0 hE.f1 hE.f2).trans htid] at hA₃
  have hd₃ : Y₃.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₃]; exact hd₂
  have e12 : eaD Y₃ 7 12 = X.cpu.gpr.rdi + 12#64 := by
    show Y₃.cpu.gpr.rdi + 12#64 = _
    rw [hd₃]
  -- one more user
  refine c.s_add_mi32 hK₃ hA₃ hE.code (lt_len (by decide)) hr₃ (add_79 _)
    (by rw [e12]; exact off_ft hE.mu 12 rfl (by decide)) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [e12] at hA₄
  obtain ⟨hD, hbx, hrq⟩ := m2_dat (V := V) X.cpu.gpr.rbx tid hs0 hs8 hm0 hm8
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 16#64 := by rw [hg₄, hg₃, hg₂, hg₁]
  -- the epilogue
  refine (c_83 prof fb).run c hfs hE.code _ hK₄ hA₄ hr₄ (vc_83 (fun i hi => ?_)) ?_
  · rw [hsp₄, a_sp]
    exact c.hws _ (hE.st i hi)
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₅]
    show Y₄.cpu.gpr.rsp + 16#64 + 8 = _
    rw [hsp₄]
    exact a_bk _
  have hbx₅ : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₅]
    show rdq(_, Y₄.cpu.gpr.rsp + 16#64) = _
    rw [hsp₄, a_sp]
    exact hbx
  have sv : Y₅.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₅.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y₅.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₅.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₅.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₅, hg₄, hg₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine c.s_ret hK₅ hA₅ hE.code (lt_len (by decide)) hr₅ (ret_91 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₅]
    exact hE.lr i hi
  · rw [hsp₅]
    exact hrq.trans hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hD hrZ (by rw [hgZ, hg₅]; rfl) ?_
  rw [hgZ]
  refine ⟨?_, hbx₅, sv⟩
  show Y₅.cpu.gpr.rsp + 8 = _
  rw [hsp₅]
  rfl

end FV7z.Pml
