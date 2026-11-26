import FV7z.Lemmas.SysMunmap
/-!
# `mmap` of private anonymous memory: what the instruction `syscall` leaves (PLAN.md §M, M1)

What the instruction `syscall` leaves for `mmap (rdi, rsi, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, r8,
r9)` on Zellic's model (`sysMmap`), `r9` a page's multiple, `rsi` not 0: an error, nothing changed; or the address `a`
the kernel chose (`Request.place`), page-aligned, at or above the first page, the range below `TASK_SIZE` and free,
the pages new zero pages that may be read and written (`Memory.mapAnon`).

- `fixed_of_free`: a free range has no special page and not the initial stack's first page (which is mapped).
- `rs_bind_any`: a property of every answer of the first part of a request is one of the whole.
- `mmN`: the region `[a, a + rsi)` of the new pages.
- `syscall_mmap_anon`: the instruction, its two kinds of outcome.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Write

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A range of free pages has no special page, nor the initial stack's first page if that is mapped. -/
theorem fixed_of_free {m : Memory} {P n : Nat} (hf : m.free P n = true)
    (hgd : ∀ g ∈ m.growsDown, m.map g ≠ none) : m.touchesFixed P n = false := by
  unfold Memory.touchesFixed
  rw [List.any_eq_false]
  intro k hk h
  have hn : (m.mapAt (P + k)).isNone = true := List.all_eq_true.1 hf k hk
  rw [Option.isNone_iff_eq_none] at hn
  dsimp only at h
  simp only [hn, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨g, hg, he⟩ := h
  apply hgd g hg
  rw [← he] at hn
  have e : BitVec.ofNat 52 g.toNat = g := BitVec.eq_of_toNat_eq (by simp)
  simpa [Memory.mapAt, g.isLt, e] using hn

/-- What holds of the rest of a request for every answer of its first part holds of the whole. -/
theorem rs_bind_any {α β : Type} {P : β × Nat → Prop} (x : Req α) (f : α → Req β)
    (h : ∀ (a : α) (t' : Nat), P ((f a).runStream o t')) : P ((x >>= f).runStream o t) := by
  show P ((x.bind f).runStream o t)
  rw [Req.runStream_bind]
  exact h _ _

/-- The region of the pages `mmap (rdi, rsi, …)` maps at `a`: `rsi` bytes from `a`. -/
abbrev mmN (s : State) (a : Nat) : List Rgn := [⟨BitVec.ofNat 64 a, s.cpu.gpr.rsi.toNat⟩]

/-- `syscall` for `mmap (rdi, rsi, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, r8, r9)`, `r9` a page's
multiple, `rsi` not 0, the initial stack's first page mapped if there is one: an error, nothing changed; or the
kernel's address `a`, page-aligned, at or above the first page, `a + rsi` rounded up to pages below `TASK_SIZE`,
the range free before, mapped to new zero pages that may be read and written, `rax` = `a`. -/
theorem syscall_mmap_anon {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 9) (hfl : s.cpu.gpr.r10.toNat = 34) (hpr : s.cpu.gpr.rdx.toNat = 3)
    (h9 : s.cpu.gpr.r9.toNat % 4096 = 0) (hl0 : 0 < s.cpu.gpr.rsi.toNat)
    (hgd : ∀ g ∈ s.proc.mm.mem.growsDown, s.proc.mm.mem.map g ≠ none) {P : StepResult × Nat → Prop}
    (h0 : ∀ (r : BitVec 64) (t' : Nat), WrErr r → P (.running (sysSt s len r) (some (sysEv s r)), t'))
    (h2 : ∀ (a t' : Nat), a % 4096 = 0 → 4096 ≤ a → a + pageUp s.cpu.gpr.rsi.toNat ≤ taskSize prof.feat →
      s.proc.mm.mem.free (a / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096) = true →
      P (.running (sysSt (s.withMem (s.proc.mm.mem.mapAnon (a / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096)
        ⟨true, true, false⟩)) len (BitVec.ofNat 64 a)) (some (sysEv s (BitVec.ofNat 64 a))), t')) :
    P ((instruction prof s).runStream o t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hr10 : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.r10.toNat = 34 := hfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx.toNat = 3 := hpr
  have hr9 : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.r9.toNat % 4096 = 0 := h9
  have hme : (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem = s.proc.mm.mem := rfl
  have hl0' : ¬ s.cpu.gpr.rsi.toNat = 0 := by omega
  have mm_b5 : bitSet 34 5 = true := by decide
  have mm_huge : anyBits 34 MAP_HUGETLB = false := by decide
  have mm_fixed : anyBits 34 (MAP_FIXED ||| MAP_FIXED_NOREPLACE) = false := by decide
  have mm_32 : anyBits 34 MAP_32BIT = false := by decide
  have mm_nore : anyBits 34 MAP_FIXED_NOREPLACE = false := by decide
  have mm_lock : anyBits 34 MAP_LOCKED = false := by decide
  have mm_gd : anyBits 34 MAP_GROWSDOWN = false := by decide
  have mm_ty : 34 % 16 = 2 := by decide
  have mm_drop : ¬ (2 = MAP_DROPPABLE) := by decide
  have mm_priv : (2 = MAP_PRIVATE) = True := eq_true (by decide)
  have mm_shared : ¬ (2 = MAP_SHARED) := by decide
  have mm_p4 : ¬ (3 = 4) := by decide
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (9 ≥ 2 ^ 31) by decide, show ¬ (9 ≥ x32Bit) by decide, show ¬ (9 ≥ nrSyscalls) by decide,
    show niSyscall 9 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show P ((sysMmap prof (nx s len (sysGpr s len) (rf0 s))).runStream o t)
  dsimp only [sysMmap]
  simp only [hrsi, hr10, hrdx, hr9, hme, hl0', mm_b5, mm_huge, mm_fixed, mm_32, mm_nore, mm_lock, mm_gd, mm_ty,
    mm_drop, mm_priv, mm_shared, mm_p4, ne_eq, eq_self_iff_true, not_true_eq_false, not_false_eq_true,
    ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.and_true, Option.map, Option.isNone, decide_false, decide_true, Bool.or_false,
    Bool.false_or]
  split
  · exact h0 (errRet ENOMEM) t (errRet_err (by decide) (by decide))
  · split
    · exact h0 (errRet ENOMEM) t (errRet_err (by decide) (by decide))
    · refine rs_bind_any _ _ fun a t₁ => ?_
      dsimp only
      split
      · exact h0 (errRet ENOMEM) t₁ (errRet_err (by decide) (by decide))
      · rename_i hc
        have ha1 : a % 4096 = 0 := by
          by_contra h
          exact hc (by simp [h])
        have ha2 : 4096 ≤ a := by
          by_contra h
          exact hc (by simp [h])
        have ha3 : a + pageUp s.cpu.gpr.rsi.toNat ≤ taskSize prof.feat := by
          by_contra h
          exact hc (by simp [h])
        have hfr : s.proc.mm.mem.free (a / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096) = true := by
          cases h : s.proc.mm.mem.free (a / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096)
          · exact absurd (by simp [h]) hc
          · rfl
        have htx := fixed_of_free hfr hgd
        simp only [htx, Bool.false_eq_true, ↓reduceIte]
        refine rs_bind_any _ _ fun b t₂ => ?_
        dsimp only
        cases b
        · simp only [Bool.not_false, ↓reduceIte]
          exact h0 (errRet ENOMEM) t₂ (errRet_err (by decide) (by decide))
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [runStream_req_bind]
          split
          · rename_i e _ _
            exact h0 (errRet e.val) (t₂ + 1) (errRet_err e.property.1 e.property.2)
          · exact h2 a (t₂ + 1) ha1 ha2 ha3 hfr

end FV7z
