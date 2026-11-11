import FV7z.Pmu.Cuts
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.Signed
import FV7z.Osv.Holds
import FV7z.Raf.Holds
/-!
# `pthread_mutex_unlock`, the plain way (PLAN.md G3, pthread)

glibc 2.31's `__pthread_mutex_unlock` at `0x5fd1d0` in `7zzs` (`nptl/pthread_mutex_unlock.c`,
`__pthread_mutex_unlock_usercnt` inlined) on a mutex of the plain kind (`__kind` 0) held with nobody waiting (the
lock word 1): `__nusers -= 1`, `__owner := 0`, `xchg` takes the lock word to 0, the answer 0. The other ways (another
kind, elision, somebody waiting: `futex`) are outside this unit.

- `sub_27`, `xc_43`, `ret_54`: the instructions outside the blocks; `vc_0`, `vc_31`, `vc_45`: the verification
  conditions.
- `Env`: what the code, the mutex's 20 bytes and the return address need; `M`: the memory at the end; `Dat`: what
  the caller gets.
- `pmu_ok`: called on such a mutex, the run reaches the return address with `rax = 0`, the registers a call keeps
  as at the entry (`Osv.Back`), the lock word 0, the owner 0, one user fewer, the other bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Pmu

/-! ## The instructions outside the blocks -/

def psb : List Byte := [0x83, 0x6f, 0x0c, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mbd 7 12 32), .imm 32 1] 4) := by dec_rfl
theorem w_27 : psb <+: pmu.drop 27 := by decide +kernel
/-- `sub dword [rdi + 12], 1`. -/
theorem sub_27 (feat : Features) : Dec feat pmu 27 (FV7z.mk .sub 32 [.mem (mbd 7 12 32), .imm 32 1] 4) :=
  Dec.shift (j := 27) (k := 0) (psb_0 feat) w_27 (Nat.zero_le _)

def pxc : List Byte := [0x87, 0x07]
theorem pxc_0 : ∀ feat, Dec feat pxc 0 (FV7z.mk .xchg 32 [.mem (mbd 7 0 32), gr 32 0] 2) := by dec_rfl
theorem w_43 : pxc <+: pmu.drop 43 := by decide +kernel
/-- `xchg dword [rdi], eax`. -/
theorem xc_43 (feat : Features) : Dec feat pmu 43 (FV7z.mk .xchg 32 [.mem (mbd 7 0 32), gr 32 0] 2) :=
  Dec.shift (j := 43) (k := 0) (pxc_0 feat) w_43 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_54 : pret <+: pmu.drop 54 := by decide +kernel
theorem ret_54 (feat : Features) : Dec feat pmu 54 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 54) (k := 0) (pret_0 feat) w_54 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the count of users: the kind plain. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hk : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 16#64) i)) (hkd : rdd(V, g.rdi + 16#64) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 27 ∧ g' = { g with rax := 0, rdx := 0, r8 := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hk hkd
  wpx [W_0, W_20, o0, o1, hkd, BitVec.zero_and]
  exact ⟨hk, fun h => absurd h (by decide), fun _ => ⟨fun h => absurd h (by decide), fun _ => rfl⟩⟩

/-- The owner cleared. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i)) (hk : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 16#64) i)) :
    W_31 F Wl (fun j' g' _ V' => j' = 43 ∧
      g' = { g with rax := 0,
                    rsi := BitVec.setWidth 64 rdd(Vst V (g.rdi + 8#64) (toBytesLE (0#32) 4), g.rdi + 16#64) } ∧
      V' = Vst V (g.rdi + 8#64) (toBytesLE (0#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hk
  wpx [W_31, o2, BitVec.xor_self]
  exact ⟨hw, hk, rfl⟩

/-- From the lock released to the `ret`: nobody waited. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : g.rax = 1) (h8 : g.r8 = 0) :
    W_45 F Wl (fun j' g' _ V' => j' = 54 ∧ g' = { g with rax := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h8
  subst h1 h8
  wpx [W_45, W_50, o3, o4, subF_g32]
  exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩

/-! ## The memory -/

/-- What `pthread_mutex_unlock` on the mutex at `m`, called with the stack pointer `S`, needs of the code and the
memory: the mutex's 20 bytes for the run to store into, apart from the return address; the lock word within one
cache line. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (S m : Addr) : Prop where
  code : CodeIn L pmu_at pmu
  s8 : S.toNat + 8 ≤ 2 ^ 64
  m0 : m.toNat + 20 ≤ S.toNat ∨ S.toNat + 8 ≤ m.toNat
  m8 : m.toNat + 20 ≤ 2 ^ 64
  ml : m.toNat % 64 + 4 ≤ 64
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  mu : ∀ i < 20, Foot Wl (Addr.add m i)

/-- The memory once there is one user fewer and no owner. -/
abbrev M1 (V : Addr → Byte) (m : Addr) : Addr → Byte :=
  Vst (Vst V (m + 12#64) (toBytesLE (rdd(V, m + 12#64) - 1#32) 4)) (m + 8#64) (toBytesLE (0#32) 4)

/-- The memory at the end: the lock word 0. -/
abbrev M (V : Addr → Byte) (m : Addr) : Addr → Byte := Vst (M1 V m) m (toBytesLE (0#32) 4)

/-- What the caller gets: the bytes outside the lock word, the owner and the count of users as they were; the lock
word 0, the owner 0, one user fewer. -/
structure Dat (m : Addr) (V V' : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (m.toNat ≤ a.toNat ∧ a.toNat < m.toNat + 4) →
    ¬ (m.toNat + 8 ≤ a.toNat ∧ a.toNat < m.toNat + 16) → V' a = V a
  lock : rdd(V', m) = 0
  own : rdd(V', m + 8#64) = 0
  nus : rdd(V', m + 12#64) = rdd(V, m + 12#64) - 1

section
variable {S m : Addr} {V : Addr → Byte}

/-- The kind and the lock word once there is one user fewer and no owner. -/
theorem m1_rd (hm8 : m.toNat + 20 ≤ 2 ^ 64) :
    rdd(M1 V m, m + 16#64) = rdd(V, m + 16#64) ∧ rdd(M1 V m, m) = rdd(V, m) := by
  refine ⟨?_, ?_⟩
  · unfold M1
    pv
    pv
  · unfold M1
    pv
    pv

/-- The memory at the end. -/
theorem m_dat (hs8 : S.toNat + 8 ≤ 2 ^ 64) (hm0 : m.toNat + 20 ≤ S.toNat ∨ S.toNat + 8 ≤ m.toNat)
    (hm8 : m.toNat + 20 ≤ 2 ^ 64) : Dat m V (M V m) ∧ rdq(M V m, S) = rdq(V, S) := by
  refine ⟨⟨fun a h1 h2 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold M M1
    repeat pv
  · unfold M
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · unfold M M1
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · unfold M M1
    pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · unfold M M1
    repeat pv

end

/-! ## The whole -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `pthread_mutex_unlock (m)` on a mutex of the plain kind held with nobody waiting: the run reaches the return
address with `rax = 0`, the registers a call keeps as at the entry, the mutex free (`Dat`). -/
theorem pmu_ok (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L X.cpu.gpr.rsp X.cpu.gpr.rdi) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pmu_at) (hkd : rdd(V, X.cpu.gpr.rdi + 16#64) = 0)
    (hlk : rdd(V, X.cpu.gpr.rdi) = 1)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat X.cpu.gpr.rdi V V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs8 := hE.s8
  have hm0 := hE.m0
  have hm8 := hE.m8
  have hk16 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i) := off_ft hE.mu 16 rfl (by decide)
  -- to the count of users
  refine (c_0 prof).run c hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (fun i hi => c.hws _ (hk16 i hi)) hkd) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have e12 : eaD Y₁ 7 12 = X.cpu.gpr.rdi + 12#64 := by
    show Y₁.cpu.gpr.rdi + 12#64 = _
    rw [hg₁]
  refine c.s_sub_mi32 hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (sub_27 _)
    (by rw [e12]; exact off_ft hE.mu 12 rfl (by decide)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [e12] at hA₂
  have hd₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁]
  -- the owner
  refine (c_31 prof).run c hE.code _ hK₂ hA₂ hr₂ (vc_31 (fun i hi => ?_) (fun i hi => ?_)) ?_
  · rw [hd₂]
    exact off_ft hE.mu 8 rfl (by decide) i hi
  · rw [hd₂]
    exact c.hws _ (hk16 i hi)
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hd₂] at hA₃
  have e0 : eaD Y₃ 7 0 = X.cpu.gpr.rdi := by
    show Y₃.cpu.gpr.rdi + 0#64 = _
    rw [hg₃]
    exact (BitVec.add_zero _).trans hd₂
  -- the lock word
  refine c.s_xchg_bd32 hK₃ hA₃ hE.code (lt_len (by decide)) hr₃ (xc_43 _) (by rw [e0]; exact hE.ml)
    (by rw [e0]; exact fun i hi => hE.mu i (by omega)) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [e0, show rv Y₃ 32 0 = 0#32 from by show Y₃.cpu.gpr.rax.setWidth 32 = _; rw [hg₃]; rfl] at hA₄
  rw [e0, (m1_rd (V := V) hm8).2, hlk] at hg₄
  obtain ⟨hD, hrq⟩ := m_dat (V := V) hs8 hm0 hm8
  have sv : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp ∧ Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₄.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
      Y₄.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y₄.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₄.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
      Y₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₄, hg₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- nobody waited
  refine (c_45 prof).run c hE.code _ hK₄ hA₄ hr₄
    (vc_45 (by rw [hg₄]; rfl) (by rw [hg₄, hg₃, hg₂, hg₁]; rfl)) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₅]; exact sv.1
  refine c.s_ret hK₅ hA₅ hE.code (lt_len (by decide)) hr₅ (ret_54 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₅]
    exact hE.lr i hi
  · rw [hsp₅]
    exact hrq.trans hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hD hrZ (by rw [hgZ, hg₅]; rfl) ?_
  rw [hgZ]
  refine ⟨?_, ?_⟩
  · show Y₅.cpu.gpr.rsp + 8 = _
    rw [hsp₅]
    rfl
  · show Y₅.cpu.gpr.rbx = _ ∧ Y₅.cpu.gpr.rbp = _ ∧ Y₅.cpu.gpr.r12 = _ ∧ Y₅.cpu.gpr.r13 = _ ∧ Y₅.cpu.gpr.r14 = _ ∧
      Y₅.cpu.gpr.r15 = _
    rw [hg₅]
    exact sv.2

end FV7z.Pmu
