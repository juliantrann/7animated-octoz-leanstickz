import FV7z.Mun.Cuts
import FV7z.Write.Holds
/-!
# `__munmap`, around the kernel's `munmap` (PLAN.md §M, M1)

glibc 2.31's `__munmap (addr, len)` at `0x6665d0` in `7zzs` (`syscall-template.S`): `munmap (addr, len)`; the kernel's
answer `r` is returned if it is not an error (`Write.WrErr`, `jae` after `cmp rax, -4095`); if it is, `errno`
(`fs:-0x48`) is set to `-r` and `rax` to -1. Two pieces of the code (`Mun/Cuts.lean`): from the entry (0) to the
`syscall` (9), from after it (11) to the `ret` (19, or 36 on the error path).

Zellic's model has `munmap` (`sysMunmap`): it may take pages out of the address space (or stop, for special
mappings), which `Fn.Seg` (a footprint over a fixed address space) does not follow: so the step of the `syscall` is
not part of these contracts. `mun_pre` ends at the `syscall`; `mun_post` starts after it, from a run's start (a new
`Seg`) whose processor is the one after the `syscall`, any answer in `rax`.

- `vc_0`, `vc_11_ok`, `vc_11_err`: the verification conditions of the pieces.
- `mun_pre`: from the entry to the `syscall`: `eax` 11 (`munmap`), the arguments as at the entry.
- `mun_post`: from after the `syscall` to the return address, the return address popped.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Mun

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: mun.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat mun 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: mun.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat mun 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)
theorem w_36 : pret <+: mun.drop 36 := by decide +kernel
theorem ret_36 (feat : Features) : Dec feat mun 36 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)

/-- `jae` after `cmp rax, -4095`: the answer is an error. -/
theorem jae_cmp (x : BitVec 64) : (!decide (x.toNat < 18446744073709547521)) = decide (WrErr x) := by
  unfold WrErr
  by_cases h : x.toNat < 18446744073709547521
  · rw [decide_eq_true h, decide_eq_false (by omega)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]
    rfl

/-- `or rax, -1`. -/
theorem or_m1 (x : BitVec 64) : x ||| 18446744073709551615#64 = 18446744073709551615#64 := by
  have h : (18446744073709551615#64) = BitVec.allOnes 64 := by decide
  rw [h]
  exact BitVec.or_allOnes

/-- The registers after the error path: `rcx` is `-0x48`, `rax` is -1. -/
def mErr (g : Gprs) : Gprs := { g with rax := 18446744073709551615#64, rcx := 18446744073709551544#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- To the `syscall`: `eax` is 11. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 11 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals vc_fin

/-- From the `syscall` to the `ret`, the kernel's answer `rax` not an error. -/
theorem vc_11_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ WrErr g.rax) :
    W_11 fb F Wl (fun j' g' _ V' => j' = 19 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = false := decide_eq_false he
  wpx [W_11, W_20, o1, o2, Op.stf, jae_cmp, he', or_m1]
  all_goals vc_fin

/-- From the `syscall` to the `ret`, the kernel's answer `rax` an error: `errno` set, `rax` -1. -/
theorem vc_11_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : WrErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_11 fb F Wl (fun j' g' _ V' => j' = 36 ∧ g' = mErr g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = true := decide_eq_true he
  wpx [W_11, W_20, o1, o2, Op.stf, jae_cmp, he', or_m1]
  all_goals first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, rfl, rfl⟩
  | vc_fin

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte} {S : State}

/-- `__munmap (addr, len)` from its entry to its `syscall`: the run goes on from a state at the `syscall` with
`eax` 11 (`munmap`), the other registers and the bytes as at the entry. -/
theorem mun_pre {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mun_at mun)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mun_at)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = mun_at.add 9 →
      Y.cpu.gpr = X.cpu.gpr.set 0 11 → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 11 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY hgY

/-- `__munmap` from after its `syscall` (a run's start `S`, the kernel's answer in `rax`) to the return address at
`rsp`, `errno` apart from it: the run goes on with the return address popped; if the answer is not an error, the
registers are `S`'s and the bytes are as at `S`; if it is, `errno` = `-r`, `rax` = -1 and `rcx` = `-0x48`. -/
theorem mun_post {fb : Addr} (c₁ : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hin : CodeIn L mun_at mun)
    (hA : Agree F S.proc.mm.mem V) (hrip : S.cpu.rip = mun_at.add 11)
    (hsp : S.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64) (hl : ∀ i < 8, Foot F.data (Addr.add S.cpu.gpr.rsp i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ S.cpu.gpr.rsp.toNat ∨ S.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      (¬ WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = S.cpu.gpr.set 4 (S.cpu.gpr.rsp + 8)) →
      (WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax)) ∧
        Z.cpu.gpr = (mErr S.cpu.gpr).set 4 (S.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE S t := by
  by_cases he : WrErr S.cpu.gpr.rax
  · refine (c_11 prof fb).run c₁ hfs hin
      (fun j' g' _ V' => j' = 36 ∧ g' = mErr S.cpu.gpr ∧ V' = Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax))
      (KeptW.refl _ _) hA hrip (vc_11_err he fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hspZ : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]; try rfl
    have heb : (errnoB S.cpu.gpr.rax).length = 4 := toBytesLE_length _ _
    refine c₁.s_ret hKZ₁ hAZ₁ hin (lt_len (by decide)) hrZ₁ (ret_36 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have h1 : (errnoAt fb).toNat + (errnoB S.cpu.gpr.rax).length ≤ 2 ^ 64 := by rw [heb]; exact hfe
      have h2 : (errnoAt fb).toNat + (errnoB S.cpu.gpr.rax).length ≤ S.cpu.gpr.rsp.toNat ∨
          S.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [heb]; exact hed
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) _ S.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z₂ t₂ hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
    refine k Z₂ t₂ hKZ₂ hrZ₂ (fun h => absurd he h) fun _ => ⟨hAZ₂, ?_⟩
    rw [hgZ₂, hgZ₁]
    try rfl
  · refine (c_11 prof fb).run c₁ hfs hin (fun j' g' _ V' => j' = 19 ∧ g' = S.cpu.gpr ∧ V' = V)
      (KeptW.refl _ _) hA hrip (vc_11_ok he) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hspZ : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]
    refine c₁.s_ret hKZ₁ hAZ₁ hin (lt_len (by decide)) hrZ₁ (ret_19 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ (by rw [hspZ]; exact hra) ?_
    rintro Z₂ t₂ hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
    refine k Z₂ t₂ hKZ₂ hrZ₂ (fun _ => ⟨hAZ₂, ?_⟩) fun h => absurd h he
    rw [hgZ₂, hgZ₁]

end FV7z.Mun
