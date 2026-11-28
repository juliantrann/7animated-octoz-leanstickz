import FV7z.Rnc.Cuts
import FV7z.Lemmas.SysRead
/-!
# `__read_nocancel` reads from a file (PLAN.md §M, M1)

glibc 2.31's `__read_nocancel (fd, buf, count)` at `0x6661e0` in `7zzs`: it asks `read (fd, buf, count)` (the
`syscall` at 6, `eax` 0 from `xor eax, eax`), and returns the kernel's answer (the `ret` at 16), or for an error (an
answer above `-4096`) sets `errno` (`fs:-72`) to the error and returns -1 (the `ret` at 43). Two pieces of the code,
to the `syscall` and from after it (8) to one of the `ret`s, around the kernel's `read` of `Lemmas/SysRead.lean`.

- `vc_0`, `vc_8_ok`, `vc_8_err`: the verification conditions of the pieces (`Rnc/Cuts.lean`).
- `rnc_ok`: called from a start with no `rseq` area, `buf`'s `count` bytes and `errno`'s 4 in what the run may store
  into, the run reaches a `ret` with `readRes`'s bytes in `buf`: at 16 with the kernel's answer in `rax` (not an
  error), at 43 with `rax` -1 and `errno` the error (an error); the registers else are as after the `syscall`. The
  run goes on from the state after the `syscall`, its own start (`Seg.s_read_re`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rnc

set_option linter.unusedSimpArgs false

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_6 : psys <+: rnc.drop 6 := by decide +kernel
theorem sys_6 (feat : Features) : Dec feat rnc 6 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 6) (k := 0) (psys_0 feat) w_6 (Nat.zero_le _)

/-- The state after the `syscall` of `read` from the state `S` at it, the kernel's result `r`. -/
abbrev rdS (S : State) (r : RdOut) : State := sysSt (rdSt S r) 2 r.ret

/-- The event of `read` from `__read_nocancel` called with registers `g`, the kernel's result `r`. -/
abbrev rdE (g : Gprs) (r : RdOut) : Event := ⟨0, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r.ret, [], r.bs⟩

/-- The registers at the `ret` after an error, from `g` after the `syscall`: `rax` -1, `rdx` `errno`'s offset from the
`fs` base. -/
abbrev errG (g : Gprs) : Gprs := { g with rax := 18446744073709551615#64, rdx := 18446744073709551544#64 }

/-- The bytes at the `ret` after an error, from `V` after the `syscall`, the kernel's answer `ret`: `errno` (at
`fs:-72`, the `fs` base `fb`) is the answer negated, its low 32 bits. -/
abbrev errV (fb : Addr) (V : Addr → Byte) (ret : BitVec 64) : Addr → Byte :=
  Vst V (fb + 18446744073709551544#64) (toBytesLE (0 - ret.setWidth 32) 4)

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 0, `read`'s number. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => j' = 6 ∧ g' = g.set 0 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have xz : ∀ x : BitVec 32, BitVec.setWidth 64 (x ^^^ x) = 0#64 := fun x => by simp
  wpx [W_0, o0, xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals first | rfl | exact ⟨rfl, rfl, rfl⟩

/-- From after the `syscall` to the `ret` at 16, the kernel's answer not an error. -/
theorem vc_8_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.toNat ≤ 18446744073709547520) :
    W_8 fb F Wl (fun j' g' _ V' => j' = 16 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h' : rax.toNat ≤ 18446744073709547520 := h
  have hc : (decide (rax.toNat < 18446744073709547520) || decide (rax = 18446744073709547520#64)) = true := by
    rcases Nat.lt_or_eq_of_le h' with h1 | h1
    · simp only [decide_eq_true h1, Bool.true_or]
    · simp only [decide_eq_true (BitVec.eq_of_toNat_eq h1 : rax = 18446744073709547520#64), Bool.or_true]
  wpx [W_8, o1, hc, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    implies_true, eq_self_iff_true, and_self]
  all_goals first | rfl | trivial | exact ⟨rfl, rfl, rfl⟩

/-- From after the `syscall` to the `ret` at 43, the kernel's answer an error: `errno` set, `rax` -1. -/
theorem vc_8_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : 18446744073709547520 < g.rax.toNat)
    (hfe : ∀ i < 4, Foot Wl ((fb + 18446744073709551544#64).add i)) :
    W_8 fb F Wl (fun j' g' _ V' => j' = 43 ∧ g' = errG g ∧ V' = errV fb V g.rax) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h' : 18446744073709547520 < rax.toNat := h
  have hc : (decide (rax.toNat < 18446744073709547520) || decide (rax = 18446744073709547520#64)) = false := by
    have h1 : ¬ rax.toNat < 18446744073709547520 := by omega
    have h2 : ¬ rax = 18446744073709547520#64 := fun e => by
      rw [e] at h'
      exact absurd h' (by decide)
    simp only [decide_eq_false h1, decide_eq_false h2, Bool.or_false]
  wpx [W_8, W_24, o1, o2, Op.stf, hc, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, implies_true, eq_self_iff_true, and_self, BitVec.reduceAdd, BitVec.reduceMul]
  all_goals first | exact hfe | exact ⟨hfe, rfl⟩ | exact ⟨rfl, hfe⟩ | rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__read_nocancel (fd, buf, count)` from a start with no `rseq` area, `buf`'s `count` bytes and `errno`'s 4
(`fs:-72`) in what the run may store into, from its entry to a `ret`. The run goes on from `S₁`, the state after the
`syscall` (`rdS`), a new start: from `S`, the state at the `syscall` (`rax` 0, the registers else as at the entry,
the bytes as at the entry), the kernel's `read` with result `r` (`readRes`, the stream of answers at some `t₁`). It
reaches the `ret` at 16 with the bytes `r.bs` in `buf` and the registers as in `S₁` when the answer is not an error
(`r.ret` at most `-4096`), else the `ret` at 43 with `errno` set (`errV`), `rax` -1 and `rdx` `errno`'s offset
(`errG`). -/
theorem rnc_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rnc_at rnc) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rnc_at)
    (hfe : ∀ i < 4, Foot Wl ((fb + 18446744073709551544#64).add i))
    (hst : ∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (X.cpu.gpr.rsi.add i))
    (k : ∀ (S : State) (t₁ : Nat) (r : RdOut), r = readRes prof o t₁ S → KeptW Wl s₀ S →
      Agree F S.proc.mm.mem V → S.cpu.gpr = X.cpu.gpr.set 0 0 → Seg prof F Wl L (rdS S r) o →
      ∀ Z t', KeptW Wl (rdS S r) Z →
      (r.ret.toNat ≤ 18446744073709547520 ∧ Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rsi r.bs) ∧
          Z.cpu.rip = rnc_at.add 16 ∧ Z.cpu.gpr = (rdS S r).cpu.gpr) ∨
        (18446744073709547520 < r.ret.toNat ∧ Agree F Z.proc.mm.mem (errV fb (Vst V X.cpu.gpr.rsi r.bs) r.ret) ∧
          Z.cpu.rip = rnc_at.add 43 ∧ Z.cpu.gpr = errG (rdS S r).cpu.gpr) →
      GoG prof L o (gev ++ [rdE X.cpu.gpr r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to the `syscall`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 6 ∧ g' = X.cpu.gpr.set 0 0 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hgY]; rfl
  have hdx : Y.cpu.gpr.rdx = X.cpu.gpr.rdx := by rw [hgY]; rfl
  -- `read`
  refine c.s_read_re hrs hKY hAY hin (lt_len (by decide)) hrY (sys_6 _) (by rw [hgY]; rfl)
    (by rw [hsi, hdx]; exact hst) ?_
  intro M t₂ t₃ hKM hAM c₁ hA₁
  have hev : rdEv Y.cpu.gpr (readRes prof o t₂ (Y.withMem M)) =
      rdE X.cpu.gpr (readRes prof o t₂ (Y.withMem M)) := by
    rw [hgY]; rfl
  rw [hev]
  rw [hsi] at hA₁
  generalize hr : readRes prof o t₂ (Y.withMem M) = r at c₁ hA₁ ⊢
  have hfs₁ : (rdS (Y.withMem M) r).cpu.seg.fsBase = fb := by
    show Y.cpu.seg.fsBase = fb
    rw [hKY.seg]
    exact hfs
  have hrip₁ : (rdS (Y.withMem M) r).cpu.rip = rnc_at.add 8 := rip_add hrY M 2
  have hgS : (Y.withMem M).cpu.gpr = X.cpu.gpr.set 0 0 := hgY
  -- to a `ret`
  by_cases hok : r.ret.toNat ≤ 18446744073709547520
  · refine (c_8 prof fb).run c₁ hfs₁ hin _ (KeptW.refl _ _) hA₁ hrip₁
      (vc_8_ok (g := (rdS (Y.withMem M) r).cpu.gpr) hok) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
    exact k (Y.withMem M) t₂ r hr.symm hKM hAM hgS c₁ Z t₄ hKZ (.inl ⟨hok, hAZ, hrZ, hgZ⟩)
  · have hlt : 18446744073709547520 < r.ret.toNat := by omega
    refine (c_8 prof fb).run c₁ hfs₁ hin _ (KeptW.refl _ _) hA₁ hrip₁
      (vc_8_err (g := (rdS (Y.withMem M) r).cpu.gpr) hlt hfe) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
    exact k (Y.withMem M) t₂ r hr.symm hKM hAM hgS c₁ Z t₄ hKZ (.inr ⟨hlt, hAZ, hrZ, hgZ⟩)

end FV7z.Rnc
