import FV7z.Fre.Cuts
import FV7z.Ifr.Code
import FV7z.Tun.Inv
/-!
# `free` of a chunk of the main arena reaches `_int_free` (PLAN.md G3, `free`)

glibc 2.31's `__libc_free (mem)` at `0x633750` in `7zzs`, with `__free_hook` (`0x7a4568`) null: `free (0)` returns at
once (the `ret`, 148); else, for a chunk not mmapped (bit 1 of its size word, the 8 bytes below `mem`) nor of another
arena (bit 2), with the thread's tcache (`fs:-0x28`) made, a tail jump to `_int_free (&main_arena, p, 0)`
(`0x62f990`, `Ifr.ifr_at`) with `p = mem - 16`. Three pieces of the code to the jump: from the entry (0) to the
arena (57), from 57 to 80, from 80 to the jump (86).

- `szw`: the size word of the chunk of `mem`.
- `FreeOk`: the chunk not mmapped nor of another arena, the tcache made, and the reads' footprint.
- `fre_ok`: with the hook null, `free (0)` at the return address with the return address popped and `rax` 0;
  `free (mem)` with `FreeOk` at `_int_free`'s entry with `rax` the size word, `rsi` = `mem - 16`, `rdi` =
  `&main_arena` (`0x792a40`) and `rdx` 0.

Out of scope here (left out by `FreeOk`): the hook set, mmapped chunks (`munmap_chunk`), the tcache not yet made
(`tcache_init`), chunks of other arenas.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fre

/-- The tail jump to `_int_free`. -/
def pjm : List Byte := [0xe9, 0xe5, 0xc1, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709535717] 5) := by dec_rfl
theorem wj_86 : pjm <+: fre.drop 86 := by decide +kernel
theorem jmp_86 (feat : Features) : Dec feat fre 86 (FV7z.mk .jmp 64 [.rel 18446744073709535717] 5) :=
  Dec.shift (j := 86) (k := 0) (pjm_0 feat) wj_86 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_148 : pret <+: fre.drop 148 := by decide +kernel
theorem ret_148 (feat : Features) : Dec feat fre 148 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 148) (k := 0) (pret_0 feat) w_148 (Nat.zero_le _)

/-- The size word of the chunk of `mem`, the 8 bytes at `mem - 8`. -/
abbrev szw (V : Addr → Byte) (p : Addr) : BitVec 64 := rdq(V, p + 18446744073709551608#64)

/-- The chunk of `mem` not mmapped (bit 1 of the size word clear) nor of another arena (bit 2), the thread's tcache
made (`fs:-0x28` not 0), and the footprint of the size word and of the tcache's word. -/
def FreeOk (F : Footprint) (V : Addr → Byte) (fb p : Addr) : Prop :=
  (BitVec.setWidth 8 (szw V p) &&& 2#8 == 0) = true ∧ (BitVec.setWidth 8 (szw V p) &&& 4#8 == 0) = true ∧
    rdq(V, fb + 18446744073709551576#64) ≠ 0#64 ∧
    (∀ i < 8, Foot F.data (Addr.add (p + 18446744073709551608#64) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `ret`: `free (0)`. -/
theorem vc_null {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfk : rdq(V, 8013160#64) = 0#64)
    (fh : ∀ i < 8, Foot F.data (Addr.add 8013160#64 i)) (h0 : g.rdi = 0#64) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 148 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0 ⊢
  subst h0
  wpx [W_0, W_24, W_144, o0, o1, o11, Op.lda, BitVec.and_self, hfk, BitVec.sub_add_cancel,
      BitVec.reduceBEq, BitVec.reduceAnd, decide_false, decide_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' first | assumption | rfl | trivial | apply And.intro | intro _

/-- From the entry to the arena: `free (mem)`, `mem` not 0, with `FreeOk`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfk : rdq(V, 8013160#64) = 0#64)
    (fh : ∀ i < 8, Foot F.data (Addr.add 8013160#64 i)) (h0 : g.rdi ≠ 0#64) (h : FreeOk F V fb g.rdi) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 57 ∧
      g' = { g with rax := szw V g.rdi, rsi := g.rdi + 18446744073709551600#64, rsp := g.rsp - 24#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hm2, -, htc, fsz, ftc⟩ := h
  dsimp only [szw] at h0 hm2 htc fsz ftc ⊢
  have hz : (rdi == 0) = false := beq_eq_false_iff_ne.2 h0
  have hd : decide (rdq(V, fb + 18446744073709551576#64) = 0#64) = false := decide_eq_false htc
  wpx [W_0, W_24, W_29, W_41, o0, o1, o2, o3, Op.lda, Op.cmpmif, BitVec.and_self, hfk, hz, hd, hm2,
      BitVec.reduceBEq, BitVec.reduceAnd, decide_false, decide_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  first
  | exact ⟨fh, fsz, ftc⟩
  | exact ⟨fh, fun _ _ => ⟨fsz, ftc⟩⟩
  | exact ⟨fh, fun _ _ => ⟨fun h => absurd h (by simp), fun _ => ⟨fsz, ftc⟩⟩⟩

/-- From the arena to 80: a chunk of the main arena (bit 2 of the size word, in `al`, clear). -/
theorem vc_57 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm4 : (BitVec.setWidth 8 g.rax &&& 4#8 == 0) = true) :
    W_57 fb F Wl (fun j' g' _ V' => j' = 80 ∧ g' = { g with rdi := 7940672#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm4 ⊢
  wpx [W_57, o4, hm4, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' first | assumption | rfl | trivial | apply And.intro | intro _

/-- From 80 to the jump: `edx` 0, the frame dropped. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_80 fb F Wl (fun j' g' _ V' => j' = 86 ∧ g' = { g with rdx := 0#64, rsp := g.rsp + 24#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_80, o6, BitVec.xor_self, BitVec.reduceSetWidth]
  all_goals repeat' first | assumption | rfl | trivial | apply And.intro | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `free (mem)` from its entry, `__free_hook` null: `free (0)` at the return address, the return address popped and
`rax` 0 (`k0`); `free (mem)` with `FreeOk` at `_int_free`'s entry, as `_int_free (&main_arena, mem - 16, 0)`, `rax`
the size word (`kf`). -/
theorem fre_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fre_at fre)
    (hinI : CodeIn L Ifr.ifr_at Ifr.ifr) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = fre_at)
    (hfk : rdq(V, 8013160#64) = 0#64) (fh : ∀ i < 8, Foot F.data (Addr.add 8013160#64 i))
    (hok : X.cpu.gpr.rdi ≠ 0#64 → FreeOk F V fb X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : X.cpu.gpr.rdi = 0#64 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rax := 0#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (kf : X.cpu.gpr.rdi ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Ifr.ifr_at →
      Y.cpu.gpr =
        { X.cpu.gpr with
          rax := szw V X.cpu.gpr.rdi, rsi := X.cpu.gpr.rdi + 18446744073709551600#64, rdi := 7940672#64,
          rdx := 0#64 } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases h0 : X.cpu.gpr.rdi = 0#64
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 148 ∧ g' = { X.cpu.gpr with rax := 0#64 } ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_null hfk fh h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY] <;> rfl
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_148 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k0 h0 Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY] <;> rfl
  · have h := hok h0
    obtain ⟨-, hm4, -⟩ := hok h0
    refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 57 ∧
        g' = { X.cpu.gpr with
               rax := szw V X.cpu.gpr.rdi, rsi := X.cpu.gpr.rdi + 18446744073709551600#64,
               rsp := X.cpu.gpr.rsp - 24#64 } ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0 hfk fh h0 h) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine (c_57 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 80 ∧ g' = { Y.cpu.gpr with rdi := 7940672#64 } ∧ V' = V) hKY hAY hrY
      (vc_57 (by rw [hgY]; exact hm4)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V₂
    refine (c_80 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 86 ∧ g' = { Z.cpu.gpr with rdx := 0#64, rsp := Z.cpu.gpr.rsp + 24#64 } ∧ V' = V)
      hKZ hAZ hrZ vc_80 ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ W t₃ hKW hAW hrW hgW -
    subst V₃
    refine c.s_jmp_x hKW hAW hin (lt_len (by decide)) hrW (jmp_86 _) hinI (tgt := 0) (by decide) (by decide) ?_
    rintro Y₂ t₄ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine kf h0 Y₂ t₄ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) ?_
    rw [hg₂, hgW, hgZ, hgY]
    (try simp only [BitVec.sub_add_cancel]) <;> rfl

end FV7z.Fre
