import FV7z.Mmp.Holds
import FV7z.Start.Mmap
import FV7z.Start.Cpu
/-!
# `__mmap` from its entry to its return, the kernel's `mmap` included (PLAN.md §M, M1)

`Mmp/Holds.lean`'s pieces around `Seg.s_mmap_anon` (`Start/Mmap.lean`), for private anonymous memory that may be
read and written. `mmp_pre` reaches the `syscall`; the kernel answers an error with nothing changed (the run goes on
in the same `Fn.Seg`, seen from the state after the `syscall` by `Seg.rebase`), or maps new zero pages at `a` (the
run goes on from the state after as a new start, the region `[a, a + len)` among what it may store into);
`mmp_post` returns from either.

- `mmG`: the registers after the `syscall`; `Ret`: what the return leaves of the registers.
- `mmp_ok`: from the entry to the return address, every outcome of the kernel's `mmap` the model has for these
  arguments.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Mmp

/-- The registers after `__mmap`'s `syscall`, from `g` at the entry: those at the `syscall` (`mg1`), `rcx` the
address after it, `r11` the flags `f`, `rax` the answer `r`. -/
abbrev mmG (g : Gprs) (f r : BitVec 64) : Gprs := (((mg1 g).set 1 (mmp_at.add 38)).set 11 f).set 0 r

/-- What `__mmap`'s return leaves of the registers, from `X` at the entry and the bytes `W` after the `syscall`:
`rsp` past the return address, `rbx` and `rbp` popped, `r12`–`r15` as at the entry. -/
def Ret (X Z : State) (W : Addr → Byte) : Prop :=
  Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 + 8 + 8 + 8 ∧ Z.cpu.gpr.rbx = rdq(W, X.cpu.gpr.rsp - 8 - 8) ∧
    Z.cpu.gpr.rbp = rdq(W, X.cpu.gpr.rsp - 8 - 8 + 8) ∧ Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
    Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15

theorem ret_of {X Y Z : State} {W : Addr → Byte} {f r : BitVec 64} (hY : Y.cpu.gpr = mmG X.cpu.gpr f r)
    (hzs : Z.cpu.gpr.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8) (hzb : Z.cpu.gpr.rbx = rdq(W, Y.cpu.gpr.rsp))
    (hzp : Z.cpu.gpr.rbp = rdq(W, Y.cpu.gpr.rsp + 8))
    (hz : Z.cpu.gpr.r12 = Y.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = Y.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = Y.cpu.gpr.r14 ∧
      Z.cpu.gpr.r15 = Y.cpu.gpr.r15) : Ret X Z W := by
  have hs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := (congrArg Gprs.rsp hY).trans rfl
  have h12 : Y.cpu.gpr.r12 = X.cpu.gpr.r12 := (congrArg Gprs.r12 hY).trans rfl
  have h13 : Y.cpu.gpr.r13 = X.cpu.gpr.r13 := (congrArg Gprs.r13 hY).trans rfl
  have h14 : Y.cpu.gpr.r14 = X.cpu.gpr.r14 := (congrArg Gprs.r14 hY).trans rfl
  have h15 : Y.cpu.gpr.r15 = X.cpu.gpr.r15 := (congrArg Gprs.r15 hY).trans rfl
  exact ⟨by rw [hzs, hs], by rw [hzb, hs], by rw [hzp, hs], hz.1.trans h12, hz.2.1.trans h13, hz.2.2.1.trans h14,
    hz.2.2.2.trans h15⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__mmap (addr, len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, fd, 0)` from its entry to the return
address at `rsp`, `len` not 0, without 5-level paging, the 16 bytes below `rsp` in what the run may store into and
the 24 from `rsp - 16` in the footprint. The kernel's answer `r` an error, nothing changed: the run goes on in the
same `Fn.Seg`, `errno` = `-r`, `rax` = -1 (`k`). New zero pages mapped at `a`: from the state `S` after the
`syscall`, a new start whose footprint has the region `[a, a + len)` among what it may store into, its bytes 0 and
the others as before, `rax` = `a` (`k₁`). The event is `mmap`'s, from the registers at the `syscall` (`mg1`). -/
theorem mmp_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mmp_at mmp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mmp_at)
    (hfl : X.cpu.gpr.rcx.toNat % 2 ^ 32 = 34) (hpr : X.cpu.gpr.rdx = 3#64) (h9 : X.cpu.gpr.r9 = 0#64)
    (hl0 : 0 < X.cpu.gpr.rsi.toNat) (hla : prof.feat.la57 = false) (hrs : s₀.thread.rseq = none)
    (hp0 : s₀.cpu.pkru &&& 3 = 0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hsp : (X.cpu.gpr.rsp - 8 - 8).toNat + 24 ≤ 2 ^ 64)
    (hl : ∀ i < 24, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ (X.cpu.gpr.rsp - 8 - 8).toNat ∨
      (X.cpu.gpr.rsp - 8 - 8).toNat + 24 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(mV V X.cpu.gpr, X.cpu.gpr.rsp - 8 - 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ (r : BitVec 64) (Z : State) (t' : Nat), WrErr r → KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst (mV V X.cpu.gpr) (errnoAt fb) (errnoB r)) →
      Z.cpu.gpr.rax = 18446744073709551615#64 → Ret X Z (mV V X.cpu.gpr) →
      GoG prof L o (gev ++ [tcEv (mg1 X.cpu.gpr) r []]) gP gE Z t')
    (k₁ : ∀ (a : Nat) (V' : Addr → Byte) (S Z : State) (t' : Nat), a % 4096 = 0 → 4096 ≤ a →
      a + pageUp X.cpu.gpr.rsi.toNat ≤ 2 ^ 47 - 4096 → (∀ y, Foot (mmN X a) y → V' y = 0) →
      (∀ y, Foot F.data y → V' y = mV V X.cpu.gpr y) →
      Seg prof (Start.withNew F (mmN X a)) (mmN X a ++ Wl) L S o → KeptW (mmN X a ++ Wl) S Z →
      Z.cpu.rip = e₂.add j₂ → Agree (Start.withNew F (mmN X a)) Z.proc.mm.mem V' →
      Z.cpu.gpr.rax = BitVec.ofNat 64 a → Ret X Z V' →
      GoG prof L o (gev ++ [tcEv (mg1 X.cpu.gpr) (BitVec.ofNat 64 a) []]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h9' : BitVec.setWidth 32 X.cpu.gpr.r9 &&& 4095#32 = 0 := by
    rw [h9]
    all_goals decide
  have hx : X.cpu.gpr.rdi ≠ 0 ∨ BitVec.setWidth 8 X.cpu.gpr.rdx &&& 4#8 = 0 := .inr (by
    rw [hpr]
    all_goals decide)
  refine mmp_pre c hfs hin hK hA hrip h9' hx hs1 hs2 fun Y0 t₀ hK0 hA0 hr0 hg0 => ?_
  have hnr : Y0.cpu.gpr.rax.toNat % 2 ^ 32 = 9 := by rw [hg0]; first | rfl | decide
  have hfl0 : Y0.cpu.gpr.r10.toNat = 34 := by
    rw [hg0, mg1_r10, BitVec.toNat_setWidth, BitVec.toNat_setWidth, hfl]
    all_goals decide
  have hpr0 : Y0.cpu.gpr.rdx.toNat = 3 := by
    rw [hg0]
    show X.cpu.gpr.rdx.toNat = 3
    rw [hpr]
    all_goals decide
  have h90 : Y0.cpu.gpr.r9.toNat % 4096 = 0 := by
    rw [hg0]
    show X.cpu.gpr.r9.toNat % 4096 = 0
    rw [h9]
    all_goals decide
  have hsi : Y0.cpu.gpr.rsi = X.cpu.gpr.rsi := (congrArg Gprs.rsi hg0).trans rfl
  have hl00 : 0 < Y0.cpu.gpr.rsi.toNat := by rw [hsi]; exact hl0
  -- the registers after the `syscall`
  have hYg : ∀ (Y : State) (r : BitVec 64), Y.cpu.gpr = (sysGpr Y0 2).set 0 r →
      Y.cpu.gpr = mmG X.cpu.gpr (rf0 Y0).toBits r := by
    intro Y r hgY
    rw [hgY]
    show ((Y0.cpu.gpr.set 1 (Y0.cpu.rip.add 2)).set 11 (rf0 Y0).toBits).set 0 r = _
    rw [hg0, hr0, addr_add_add]
    try rfl
  refine c.s_mmap_anon hK0 hA0 hin (lt_len (by decide)) hr0 (sys_36 _) hnr hfl0 hpr0 h90 hl00 hla hrs hp0 ?_ ?_
  · intro r hr Y t₁ hKY hAY ⟨hrY, hgY⟩
    rw [hg0]
    have hY := hYg Y r hgY
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := (congrArg Gprs.rsp hY).trans rfl
    have hax : Y.cpu.gpr.rax = r := (congrArg Gprs.rax hY).trans rfl
    refine mmp_post (c.rebase hKY fun _ h => h) (by rw [hKY.seg]; exact hfs) hin hAY (hrY.trans rfl)
      (by rw [hsY]; exact hsp) (fun i hi => by rw [hsY]; exact hl i hi) fe hfe (by rw [hsY]; exact hed) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    intro Z t₂ hKZ hrZ hzs hzb hzp hz _ herr
    obtain ⟨hAZ, hgZ⟩ := herr (by rw [hax]; exact hr)
    rw [hax] at hAZ
    exact k r Z t₂ hr (hKY.trans hKZ fun _ h => h) hrZ hAZ hgZ (ret_of hY hzs hzb hzp hz)
  · intro a V' Y t₁ ha1 ha2 ha3 hz0 hfv c₁ hAY hrY hgY hsgY
    rw [hg0]
    have eN : mmN Y0 a = mmN X a := by simp only [mmN, hsi]
    rw [hsi] at ha3
    rw [eN] at hz0 c₁ hAY
    have hY := hYg Y _ hgY
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := (congrArg Gprs.rsp hY).trans rfl
    have hax : Y.cpu.gpr.rax = BitVec.ofNat 64 a := (congrArg Gprs.rax hY).trans rfl
    have hb : (BitVec.ofNat 64 a).toNat = a := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    -- the return address is in the footprint, whose bytes the new pages leave as they were
    have a16 : ∀ i < 8, Addr.add (X.cpu.gpr.rsp - 8 - 8 + 8 + 8) i = Addr.add (X.cpu.gpr.rsp - 8 - 8) (16 + i) :=
      fun i _ => by
        have h2 := addr_add_add' (Addr.add (X.cpu.gpr.rsp - 8 - 8) 8) 8 i
        have h3 := addr_add_add' (X.cpu.gpr.rsp - 8 - 8) 8 (8 + i)
        have h4 : 8 + (8 + i) = 16 + i := by omega
        exact h2.trans (h3.trans (by rw [h4]))
    have hra' : rdq(V', X.cpu.gpr.rsp - 8 - 8 + 8 + 8) = e₂.add j₂ := by
      rw [← hra]
      congr 1
      apply List.map_congr_left
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
      rw [a16 i hi]
      exact hfv _ (hl (16 + i) (by omega))
    refine mmp_post c₁ (by rw [hsgY, hK0.seg]; exact hfs) hin hAY (hrY.trans rfl) (by rw [hsY]; exact hsp)
      (fun i hi => by rw [hsY]; exact Start.withNew_data c.own (hl i hi))
      (fun i hi => foot_append_iff.2 (.inr (fe i hi))) hfe (by rw [hsY]; exact hed) hin₂ h₂
      (by rw [hsY]; exact hra') ?_
    intro Z t₂ hKZ hrZ hzs hzb hzp hz hok _
    have hn : ¬ WrErr Y.cpu.gpr.rax := by
      rw [hax]
      unfold WrErr
      rw [hb]
      omega
    obtain ⟨hAZ, hgZ⟩ := hok hn
    exact k₁ a V' Y Z t₂ ha1 ha2 ha3 hz0 hfv c₁ hKZ hrZ hAZ (hgZ.trans hax) (ret_of hY hzs hzb hzp hz)

end FV7z.Mmp
