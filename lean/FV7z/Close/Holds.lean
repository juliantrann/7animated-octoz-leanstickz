import FV7z.Close.Cuts
import FV7z.Lemmas.SysClose
import FV7z.Tun.Inv
/-!
# `__close` closes a descriptor (PLAN.md §M, M1)

glibc 2.31's `__close (fd)` at `0x5ff3b0` in `7zzs`: in a process of one thread (`multiple_threads`, `fs:0x18`, is 0)
the `syscall` `close`, then the result returned, or `errno` (`fs:-0x48`) set to the error and -1 returned. Two pieces of
the code: to the `syscall` (21) and from after it (23) to one of the two `ret`s (31, 113); the `syscall` itself is
`Seg.s_close_re` (`Lemmas/SysClose.lean`), after which the run goes on from its own start.

- `CloseErr r`: the kernel's answer `r` is an error (`-4095 ≤ r < 0`, as `cmp rax, -4096; ja` reads it).
- `errG`, `errnoB`: the registers and the bytes of `errno` after the error path.
- `close_ok`: called with `multiple_threads` 0, `errno`'s 4 bytes in what the run may store into, the run reaches the
  return address with the descriptor closed and either the answer in `rax` or `errno` set and `eax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Close

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_21 : psys <+: cls.drop 21 := by decide +kernel
theorem sys_21 (feat : Features) : Dec feat cls 21 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 21) (k := 0) (psys_0 feat) w_21 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_31 : pret <+: cls.drop 31 := by decide +kernel
theorem ret_31 (feat : Features) : Dec feat cls 31 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 31) (k := 0) (pret_0 feat) w_31 (Nat.zero_le _)
theorem w_113 : pret <+: cls.drop 113 := by decide +kernel
theorem ret_113 (feat : Features) : Dec feat cls 113 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 113) (k := 0) (pret_0 feat) w_113 (Nat.zero_le _)

/-- The kernel's answer is an error: above `-4096` as an unsigned number. -/
def CloseErr (r : BitVec 64) : Prop := 18446744073709547520 < r.toNat

instance (r : BitVec 64) : Decidable (CloseErr r) := inferInstanceAs (Decidable (_ < _))

/-- `errno`'s place: `fs:-0x48`. -/
abbrev errnoAt (fb : Addr) : Addr := fb + 18446744073709551544#64

/-- The bytes of `errno` after the error `r`: its negation, 32 bits. -/
abbrev errnoB (r : BitVec 64) : List Byte := toBytesLE (0 - r.setWidth 32) 4

/-- The registers after the error path: `rdx` is `-0x48`, `eax` is -1. -/
def errG (g : Gprs) : Gprs := (g.set 2 18446744073709551544#64).set 0 4294967295#64

theorem errG_rsp (g : Gprs) : (errG g).rsp = g.rsp := by cases g; rfl

/-- The event of `close` from `__close` called with registers `g`, the kernel's answer `r`. -/
abbrev clsEv (g : Gprs) (r : BitVec 64) : Event := ⟨3, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r, [], []⟩

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `multiple_threads` is 0, so no jump; `eax` is 3. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hmt : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map V) = 0) (fm : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 21 ∧ g' = g.set 0 3 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_16, o0, o1, Op.ldf, hmt]
  refine ⟨fm, fun h => absurd h (by decide), fun _ => ?_⟩
  rfl

/-- How `cmp rax, -4096; ja` reads the kernel's answer. -/
theorem ja_cmp (x : BitVec 64) :
    (!(decide (x.toNat < 18446744073709547520) || decide (x = 18446744073709547520#64))) = decide (CloseErr x) := by
  by_cases h1 : x.toNat < 18446744073709547520
  · have h3 : ¬ CloseErr x := by unfold CloseErr; omega
    rw [decide_eq_true h1, decide_eq_false h3]
    rfl
  · by_cases h2 : x = 18446744073709547520#64
    · have h3 : ¬ CloseErr x := by unfold CloseErr; rw [h2]; decide
      rw [decide_eq_false h1, decide_eq_true h2, decide_eq_false h3]
      rfl
    · have h3 : CloseErr x := by
        unfold CloseErr
        have : x.toNat ≠ 18446744073709547520 := fun e => h2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
        omega
      rw [decide_eq_false h1, decide_eq_false h2, decide_eq_true h3]
      rfl

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_23_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ CloseErr g.rax) :
    W_23 fb F Wl (fun j' g' _ V' => j' = 31 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = false := decide_eq_false he
  wpx [W_23, W_96, o2, o3, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `eax` -1. -/
theorem vc_23_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : CloseErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_23 fb F Wl (fun j' g' _ V' => j' = 113 ∧ g' = errG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = true := decide_eq_true he
  wpx [W_23, W_96, o2, o3, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__close (fd)` from its entry to the return address, in a process of one thread (`multiple_threads` 0): the
`syscall` `close` from `Y` (the registers at the entry with `eax` 3) answers `r`, `closeRes` of some point of the
stream; the run goes on from the state after it, `S`, its own start (`Seg`), to the return address with the return
address popped and, if `r` is not an error, `rax` = `r`; if it is, `errno` = `-r` and `eax` = -1 (`errG`). -/
theorem close_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L cls_at cls) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = cls_at)
    (hmt : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map V) = 0) (fm : ∀ i < 4, Foot F.data ((fb + 24#64).add i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Y S Z : State) (r : BitVec 64) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.gpr = X.cpu.gpr.set 0 3 → Y.cpu.rip = cls_at.add 21 → (∃ t₁, (closeRes o t₁ Y).1 = r) →
      S = sysSt (closeSt Y) 2 r → Seg prof F Wl L S o → KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr r → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 r).set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr r → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB r)) ∧
        Z.cpu.gpr = (errG ((sysGpr Y 2).set 0 r)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [clsEv X.cpu.gpr r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 21 ∧ g' = X.cpu.gpr.set 0 3 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hmt fm) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_close_re hrs hKY hAY hin (lt_len (by decide)) hrY (sys_21 _) (by rw [hgY]; rfl) ?_
  intro M t₂ t₃ hKm c₁ hAm
  have hev : sysEv Y (closeRes o t₂ (Y.withMem M)).1 = clsEv X.cpu.gpr (closeRes o t₂ (Y.withMem M)).1 := by
    simp only [sysEv, hgY]
    rfl
  rw [hev]
  generalize hrm : (closeRes o t₂ (Y.withMem M)).1 = r at c₁ ⊢
  have hfs₁ : (sysSt (closeSt (Y.withMem M)) 2 r).cpu.seg.fsBase = fb := by
    show Y.cpu.seg.fsBase = fb
    rw [hKY.seg]
    exact hfs
  have hrS : (sysSt (closeSt (Y.withMem M)) 2 r).cpu.rip = cls_at.add 23 := by
    show Y.cpu.rip.add 2 = _
    rw [hrY]
    exact addr_add_add _ _ _
  have hgS : (sysSt (closeSt (Y.withMem M)) 2 r).cpu.gpr = (sysGpr Y 2).set 0 r := rfl
  have hspY : ((sysGpr Y 2).set 0 r).rsp = X.cpu.gpr.rsp := by
    show Y.cpu.gpr.rsp = _
    rw [hgY]
    rfl
  have hY : (Y.withMem M).cpu.gpr = X.cpu.gpr.set 0 3 := hgY
  have kk := fun Z t' => k (Y.withMem M) _ Z r t' hKm hAm hY hrY ⟨t₂, hrm⟩ rfl c₁
  have hr0 : ((sysGpr Y 2).set 0 r).rax = r := rfl
  by_cases he : CloseErr r
  · refine (c_23 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 113 ∧ g' = errG ((sysGpr Y 2).set 0 r) ∧
        V' = Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax))
      (KeptW.refl _ _) hAm hrS (by rw [hgS]; exact vc_23_err (by rw [hr0]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, errG_rsp, hspY]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_113 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : (errnoB ((sysGpr Y 2).set 0 r).rax).length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r).rax).length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r).rax).length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax) X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    rw [hr0] at hAZ'
    refine kk Z' t₅ hKZ' hrZ' (fun h => absurd he h) fun _ => ⟨hAZ', ?_⟩
    rw [hgZ', hgZ, errG_rsp, hspY]
    rfl
  · refine (c_23 prof fb).run c₁ hfs₁ hin (fun j' g' _ V' => j' = 31 ∧ g' = (sysGpr Y 2).set 0 r ∧ V' = V)
      (KeptW.refl _ _) hAm hrS (by rw [hgS]; exact vc_23_ok (by rw [hr0]; exact he)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₄ hKZ hAZ hrZ hgZ -
    subst V₂
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hspY]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_31 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ (by rw [hspZ]; exact hra) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kk Z' t₅ hKZ' hrZ' (fun _ => ⟨hAZ', ?_⟩) fun h => absurd h he
    rw [hgZ', hgZ, hspY]
    rfl

end FV7z.Close
