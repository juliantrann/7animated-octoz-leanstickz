import FV7z.Pmd.Cuts
import FV7z.Close.Holds
/-!
# `__pthread_mutex_destroy` marks a free mutex invalid (PLAN.md §M, M1)

glibc 2.31's `__pthread_mutex_destroy (mutex)` at `0x5fbd00` in `7zzs`: if the mutex is not robust (bit 4 of the low
byte of `__kind`, the 4 bytes at `mutex + 0x10`) and has users (`__nusers`, the 4 bytes at `mutex + 0xc`), `EBUSY`
(16) in `eax`; else `__kind` = -1 and 0 in `eax`. Two pieces of the code: from the entry (0) to the `ret` (33) or to
the store (24), and from 24 to the `ret`.

- `Busy`: the mutex not robust and with users.
- `pmd_ok`: called with `__kind` and `__nusers` readable and `__kind` in what the run may store into, the run reaches
  the return address with `EBUSY` in `rax` (`Busy`) or `__kind` = -1 and `rax` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Pmd

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: pmd.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat pmd 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)

/-- The mutex's `__kind`. -/
abbrev kd (V : Addr → Byte) (p : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs (p + 16#64) 4).map V)
/-- The mutex's `__nusers`. -/
abbrev nu (V : Addr → Byte) (p : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs (p + 12#64) 4).map V)
/-- Not robust (`PTHREAD_MUTEX_ROBUST_NORMAL_NP`, bit 4 of `__kind`'s low byte) and with users. -/
def Busy (V : Addr → Byte) (p : Addr) : Prop := (kd V p).setWidth 8 &&& 16#8 = 0 ∧ nu V p ≠ 0
/-- `__kind` = -1 as bytes. -/
abbrev kinv : List Byte := toBytesLE (4294967295#32) 4

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `ret`, the mutex busy: `EBUSY`. -/
theorem vc_busy {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fk : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 16) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 12) i)) (h : Busy V g.rdi) :
    W_0 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = { g with rax := 16#64, rdx := BitVec.setWidth 64 (nu V g.rdi) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2⟩ := h
  dsimp only at fk fn h1 h2 ⊢
  wpx [W_0, W_12, o0, o1, Op.ld, sw_64_8, BitVec.and_self]
  refine ⟨fk, fun hc => ?_, fun _ => ⟨fn, fun _ => ?_, fun hc => ?_⟩⟩
  · first
    | exact absurd h1 (by simpa using hc)
    | simp [h1] at hc
  · first
    | rfl
    | rw [show BitVec.setWidth 64 16#32 = 16#64 by decide]
  · first
    | exact absurd (by simpa using hc) h2
    | simp [h2] at hc

/-- From the entry to the store, the mutex not busy. -/
theorem vc_free {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fk : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 16) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 12) i)) (h : ¬ Busy V g.rdi) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧ (∃ a d, g' = { g with rax := a, rdx := d }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold Busy at h
  dsimp only at fk fn h ⊢
  wpx [W_0, W_12, o0, o1, Op.ld, sw_64_8, BitVec.and_self]
  refine ⟨fk, fun _ => ⟨_, _, rfl⟩, fun hc0 => ⟨fn, fun hc => (h ⟨?_, ?_⟩).elim,
    fun _ => ⟨_, _, rfl⟩⟩⟩
  · first
    | simpa using hc0
    | exact Classical.byContradiction fun e => by simp [e] at hc0
  · first
    | simpa using hc
    | exact fun e => by simp [e] at hc

/-- The store: `__kind` = -1, `eax` 0. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fw : ∀ i < 4, Foot Wl (Addr.add (Addr.add g.rdi 16) i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = { g with rax := 0#64 } ∧ V' = Vst V (Addr.add g.rdi 16) kinv)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [W_24, o2, Op.sti, BitVec.xor_self]
  first
  | exact ⟨fw, rfl⟩
  | exact ⟨fw, by simp⟩
  | exact ⟨fw, rfl, rfl, rfl⟩
  | exact ⟨fw, rfl, by simp, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__pthread_mutex_destroy (mutex)` from its entry to the return address, the return address popped: `EBUSY` in
`rax` if the mutex is busy (`Busy`); else `__kind` = -1 and `rax` 0 (`rdx` left to the path). -/
theorem pmd_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pmd_at pmd) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pmd_at)
    (fk : ∀ i < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi 16) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi 12) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (Addr.add X.cpu.gpr.rdi 16) i))
    (hfw : (Addr.add X.cpu.gpr.rdi 16).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (Addr.add X.cpu.gpr.rdi 16).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (Addr.add X.cpu.gpr.rdi 16).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (Busy V X.cpu.gpr.rdi → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = { X.cpu.gpr with rax := 16#64, rdx := BitVec.setWidth 64 (nu V X.cpu.gpr.rdi) }.set 4
          (X.cpu.gpr.rsp + 8)) →
      (¬ Busy V X.cpu.gpr.rdi → ∃ d, Agree F Z.proc.mm.mem (Vst V (Addr.add X.cpu.gpr.rdi 16) kinv) ∧
        Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rdx := d }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases hb : Busy V X.cpu.gpr.rdi
  · refine (c_0 prof).run c hin
      (fun j' g' _ V' => j' = 33 ∧
        g' = { X.cpu.gpr with rax := 16#64, rdx := BitVec.setWidth 64 (nu V X.cpu.gpr.rdi) } ∧ V' = V)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_busy fk fn hb) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY] <;> rfl
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_33 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k Z t₂ hKZ hrZ (fun _ => ⟨hAZ, ?_⟩) fun h => absurd hb h
    rw [hgZ, hgY] <;> rfl
  · refine (c_0 prof).run c hin
      (fun j' g' _ V' => j' = 24 ∧ (∃ a d, g' = { X.cpu.gpr with rax := a, rdx := d }) ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_free fk fn hb) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, d, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY] <;> rfl
    refine (c_24 prof).run c hin
      (fun j' g' _ V' => j' = 33 ∧ g' = { Y.cpu.gpr with rax := 0#64 } ∧
        V' = Vst V (Addr.add X.cpu.gpr.rdi 16) kinv)
      hKY hAY hrY (by rw [← hdi]; exact vc_24 (by rw [hdi]; exact fw)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hgY] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_33 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb4 : kinv.length = 4 := toBytesLE_length _ _
      have h1 : (Addr.add X.cpu.gpr.rdi 16).toNat + kinv.length ≤ 2 ^ 64 := by rw [hb4]; exact hfw
      have h2 : (Addr.add X.cpu.gpr.rdi 16).toNat + kinv.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (Addr.add X.cpu.gpr.rdi 16).toNat := by rw [hb4]; exact hsa
      rw [hspZ, Tun.rd_Vst V (Addr.add X.cpu.gpr.rdi 16) kinv X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₃ hKZ' hrZ' (fun h => absurd h hb) fun _ => ⟨d, hAZ', ?_⟩
    rw [hgZ', hgZ, hgY] <;> rfl

end FV7z.Pmd
