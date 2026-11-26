import FV7z.Lseek.Cuts
import FV7z.Lemmas.SysLseek
import FV7z.Close.Holds
/-!
# `__libc_lseek` moves a file's position (PLAN.md §M, M1)

glibc 2.31's `__libc_lseek (fd, off, whence)` at `0x5ff440` in `7zzs`: the `syscall` `lseek`, then the answer
returned, or `errno` (`fs:-0x48`) set to the error and -1 returned. Two pieces of the code: to the `syscall` (9) and
from after it (11) to one of the two `ret`s (19, 43); the `syscall` itself is `Seg.s_lseek_re`
(`Lemmas/SysLseek.lean`), after which the run goes on from its own start. The answer is told apart as `__close`'s
(`Close.CloseErr`, `cmp rax, -4096; ja`).

- `lsErrG`: the registers after the error path (`rax` -1, 64 bits).
- `lseek_ok`: called with `whence` at most `SEEK_END` and `errno`'s 4 bytes in what the run may store into, the run
  reaches the return address with the address space and descriptor table of before and either the answer in `rax`
  or `errno` set and `rax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Lseek

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: lsk.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat lsk 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: lsk.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat lsk 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)
theorem w_43 : pret <+: lsk.drop 43 := by decide +kernel
theorem ret_43 (feat : Features) : Dec feat lsk 43 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 43) (k := 0) (pret_0 feat) w_43 (Nat.zero_le _)

/-- The registers after the error path: `rdx` is `-0x48`, `rax` is -1. -/
def lsErrG (g : Gprs) : Gprs := (g.set 2 18446744073709551544#64).set 0 18446744073709551615#64

theorem lsErrG_rsp (g : Gprs) : (lsErrG g).rsp = g.rsp := by cases g; rfl

/-- The event of `lseek` from `__libc_lseek` called with registers `g`, the kernel's answer `r`. -/
abbrev lsEv (g : Gprs) (r : BitVec 64) : Event := ⟨8, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r, [], []⟩

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 8. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 8 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_11_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ CloseErr g.rax) :
    W_11 fb F Wl (fun j' g' _ V' => j' = 19 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = false := decide_eq_false he
  wpx [W_11, W_24, o1, o2, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `rax` -1. -/
theorem vc_11_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : CloseErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_11 fb F Wl (fun j' g' _ V' => j' = 43 ∧ g' = lsErrG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = true := decide_eq_true he
  wpx [W_11, W_24, o1, o2, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__libc_lseek (fd, off, whence)` from its entry to the return address, `whence` at most `SEEK_END`: the
`syscall` `lseek` from `Y` (the registers at the entry with `eax` 8) answers some `r`; the run goes on from the state
after it, `S` (the processor after the `syscall`, the address space and descriptor table of `Y`), its own start
(`Seg`), to the return address with the return address popped and, if `r` is not an error, `rax` = `r`; if it is,
`errno` = `-r` and `rax` = -1 (`lsErrG`). -/
theorem lseek_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L lsk_at lsk) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsk_at) (hw : arg32 X.cpu.gpr.rdx ≤ 2)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Y S Z : State) (r : BitVec 64) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.gpr = X.cpu.gpr.set 0 8 → Y.cpu.rip = lsk_at.add 9 →
      S.cpu = (sysSt Y 2 r).cpu → S.proc.mm = Y.proc.mm → S.proc.files = Y.proc.files →
      Seg prof F Wl L S o → KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr r → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 r).set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr r → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB r)) ∧
        Z.cpu.gpr = (lsErrG ((sysGpr Y 2).set 0 r)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [lsEv X.cpu.gpr r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 8 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hwY : arg32 Y.cpu.gpr.rdx ≤ 2 := by rw [hgY]; exact hw
  refine c.s_lseek_re hrs hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl) hwY ?_
  intro M S r t₂ hKm hcS hmmS hfsS c₁ hAS
  have hev : sysEv Y r = lsEv X.cpu.gpr r := by
    simp only [sysEv, hgY]
    rfl
  rw [hev]
  have hfs₁ : S.cpu.seg.fsBase = fb :=
    (congrArg (·.seg.fsBase) hcS).trans (by show Y.cpu.seg.fsBase = fb; rw [hKY.seg]; exact hfs)
  have hrS : S.cpu.rip = lsk_at.add 11 :=
    (congrArg (·.rip) hcS).trans (by show Y.cpu.rip.add 2 = _; rw [hrY]; exact addr_add_add _ _ _)
  have hgS : S.cpu.gpr = (sysGpr Y 2).set 0 r := (congrArg (·.gpr) hcS).trans rfl
  have hspY : ((sysGpr Y 2).set 0 r).rsp = X.cpu.gpr.rsp := by
    show Y.cpu.gpr.rsp = _
    rw [hgY]
    rfl
  have hY : (Y.withMem M).cpu.gpr = X.cpu.gpr.set 0 8 := hgY
  have hAm : Agree F (Y.withMem M).proc.mm.mem V := by rw [← hmmS]; exact hAS
  have kk := fun Z t' => k (Y.withMem M) S Z r t' hKm hAm hY hrY hcS hmmS hfsS c₁
  have hr0 : ((sysGpr Y 2).set 0 r).rax = r := rfl
  by_cases he : CloseErr r
  · refine (c_11 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 43 ∧ g' = lsErrG ((sysGpr Y 2).set 0 r) ∧
        V' = Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax))
      (KeptW.refl _ _) hAS hrS (by rw [hgS]; exact vc_11_err (by rw [hr0]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, lsErrG_rsp, hspY]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_43 _) (fun i hi => by rw [hspZ]; exact hl i hi)
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
    rw [hgZ', hgZ, lsErrG_rsp, hspY]
    rfl
  · refine (c_11 prof fb).run c₁ hfs₁ hin (fun j' g' _ V' => j' = 19 ∧ g' = (sysGpr Y 2).set 0 r ∧ V' = V)
      (KeptW.refl _ _) hAS hrS (by rw [hgS]; exact vc_11_ok (by rw [hr0]; exact he)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₄ hKZ hAZ hrZ hgZ -
    subst V₂
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hspY]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_19 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ (by rw [hspZ]; exact hra) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kk Z' t₅ hKZ' hrZ' (fun _ => ⟨hAZ', ?_⟩) fun h => absurd h he
    rw [hgZ', hgZ, hspY]
    rfl

end FV7z.Lseek
