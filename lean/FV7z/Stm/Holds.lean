import FV7z.Stm.Vc
import FV7z.Cal.Holds
import FV7z.Tls.Mem
/-!
# `systrim` gives the top of the heap back (PLAN.md §M, M1)

glibc 2.31's `systrim (pad, &main_arena)` (`systrim.isra.0.constprop.0`, at `0x62f8e0` in `7zzs`): with `ts` the top
chunk's size and `extra = ALIGN_DOWN (ts - MINSIZE - 1 - pad, pagesize)` (`stmE`), when `extra` is not 0 and
`MORECORE (0)` gives the top chunk's end, it calls `MORECORE (-extra)`, then (`__after_morecore_hook` null)
`MORECORE (0)` again for the new break, and when that moved it takes `released` from `main_arena.system_mem`, sets
the top chunk's size to `ts - released` and returns 1; on the other ways it returns 0.

The model's `Seg` has no step that moves the break down, so the proof stops at the `call` of `MORECORE (-extra)`
(94) and starts again at its return (100):

- `stm_pre`: from the entry, to the caller with `eax` 0 or to the `call` at 94 (`rdi = -extra`, the break the top
  chunk's end).
- `stm_post`: from 100 with the break `b` (`Base`): to the caller with `eax` 0, or with `eax` 1, `released` not 0
  and the bytes `stmV`.
- `ret75`, `ret77`: the way out (`eax` 0 at 75; the three pops and the `ret`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Stm

/-- A bound on a literal address. -/
macro "tn" : tactic => `(tactic| (simp only [BitVec.toNat_ofNat]; omega))

/-- The registers a call keeps. -/
abbrev Km (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The bytes after `systrim` released `rel` bytes: `main_arena.system_mem` (`sm` before) and the top chunk `T`'s
size word (`ts` the size before). -/
def stmV (V : Addr → Byte) (T sm rel ts : Addr) : Addr → Byte :=
  Vst (Vst V 7942856#64 (toBytesLE (sm - rel) 8)) (T + 8#64) (toBytesLE (ts - rel ||| 1#64) 8)

/-! ## Addresses and bytes -/

theorem ta8 {a : Addr} (h : a.toNat + 8 < 2 ^ 64) : (a + 8).toNat = a.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl]
  omega

/-- `n` bytes from `b` in `[lo, up)`. -/
theorem stk {R : List Rgn} {lo up : Nat} (h : ∀ a : Addr, lo ≤ a.toNat → a.toNat < up → Foot R a) {b : Addr}
    {n : Nat} (h1 : lo ≤ b.toNat) (h2 : b.toNat + n ≤ up) (h3 : up ≤ 2 ^ 64) : ∀ i < n, Foot R (Addr.add b i) :=
  fun i hi => by
    have e := toNat_add_of_fits (a := b) hi (by omega)
    exact h _ (by omega) (by omega)

/-- Bytes in `[lo, up)`, read where two memories agree there. -/
theorem rd_in {V V' : Addr → Byte} {lo up : Nat} (h : ∀ a : Addr, lo ≤ a.toNat → a.toNat < up → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ up) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Cal.rd_eq (P := fun a => lo ≤ a.toNat ∧ a.toNat < up) (fun a ha => h a ha.1 ha.2) fun i hi => by
    have e := toNat_add_of_fits (a := x) hi hx
    exact ⟨by omega, by omega⟩

theorem fr3_out (V : Addr → Byte) (S : Addr) (a b c : BitVec 64) (hS : 32 ≤ S.toNat) (x : Addr)
    (hx : ¬ (S.toNat - 24 ≤ x.toNat ∧ x.toNat < S.toNat)) : fr3 V S a b c x = V x := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  unfold fr3
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- The three saved registers read back. -/
theorem fr3_slots (V : Addr → Byte) (S : Addr) (a b c : BitVec 64) (hS : 32 ≤ S.toNat) :
    rdq(fr3 V S a b c, S - 8 - 8 - 8) = c ∧ rdq(fr3 V S a b c, S - 8 - 8) = b ∧ rdq(fr3 V S a b c, S - 8) = a := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  unfold fr3
  refine ⟨?_, ?_, ?_⟩
  · rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e3]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [e2]; omega)
        (by rw [toBytesLE_length, e3, e2]; omega),
      rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e2]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [e1]; omega)
        (by rw [toBytesLE_length, e3, e1]; omega),
      rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [e1]; omega)
        (by rw [toBytesLE_length, e2, e1]; omega),
      rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e1]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The frame read back where the bytes `W` are the pushes' from `S - 24` to `S + 8`. -/
theorem frame {V W : Addr → Byte} {S ra a b c : Addr} (hS : 32 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64)
    (hra : rdq(V, S) = ra) (h : ∀ x : Addr, S.toNat - 24 ≤ x.toNat → x.toNat < S.toNat + 8 → W x = fr3 V S a b c x) :
    rdq(W, S - 8 - 8 - 8) = c ∧ rdq(W, S - 8 - 8) = b ∧ rdq(W, S - 8) = a ∧ rdq(W, S) = ra := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  obtain ⟨s3, s2, s1⟩ := fr3_slots V S a b c hS
  rw [rd_in (x := S - 8 - 8 - 8) (n := 8) h (by rw [e3]; omega) (by rw [e3]; omega) (by rw [e3]; omega),
    rd_in (x := S - 8 - 8) (n := 8) h (by rw [e2]; omega) (by rw [e2]; omega) (by rw [e2]; omega),
    rd_in (x := S - 8) (n := 8) h (by rw [e1]; omega) (by rw [e1]; omega) (by rw [e1]; omega),
    rd_in (x := S) (n := 8) h hS8 (by omega) (by omega)]
  refine ⟨s3, s2, s1, ?_⟩
  unfold fr3
  rw [fr3_rd V S a b c hS hS8 (.inr (Nat.le_refl _))]
  exact hra

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The way out -/

/-- From 77: the three pops and the `ret` to the return address above them. -/
theorem ret77 {fb : Addr} {X : State} {t : Nat} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L stm_at stm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = stm_at.add 77)
    (q0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (q1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8) i))
    (q2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8) i))
    (q3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8 + 8) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rax = X.cpu.gpr.rax →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 → Y.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp) →
      Y.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 8) → Y.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8 + 8) →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_77 prof fb).run c hfs hin _ hK hA hrip (vc_77 q0 q1 q2) ?_
  rintro j' g fl V' ⟨rfl, hVV, hsp, hax, hbx, hbp, h12, h13, h14, h15⟩ Y t₁ hK₁ hA₁ hr₁ hg -
  subst V'
  subst hg
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_81 _) (by rw [hsp]; exact q3) hin₂ h₂
    (by rw [hsp]; exact hra) ?_
  rintro Z t' hKz hAz ⟨hrz, hgz⟩
  refine k Z t' hKz hAz hrz (by rw [hgz]; exact hax) ?_ (by rw [hgz]; exact hbx) (by rw [hgz]; exact hbp)
    (by rw [hgz]; exact h12) (by rw [hgz]; exact h13) (by rw [hgz]; exact h14) (by rw [hgz]; exact h15)
  rw [hgz]
  show Y.cpu.gpr.rsp + 8 = _
  rw [hsp]

/-- From 75: `eax = 0`, the three pops and the `ret`. -/
theorem ret75 {fb : Addr} {X : State} {t : Nat} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L stm_at stm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = stm_at.add 75)
    (q0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (q1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8) i))
    (q2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8) i))
    (q3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8 + 8) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rax = 0#64 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 → Y.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp) →
      Y.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 8) → Y.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8 + 8) →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_75 prof fb).run c hfs hin _ hK hA hrip vc_75 ?_
  rintro j' g fl V' ⟨rfl, hVV, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg -
  subst V'
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg] <;> rfl
  refine ret77 c hfs hin hK₁ hA₁ hr₁ (by rw [hsp]; exact q0) (by rw [hsp]; exact q1) (by rw [hsp]; exact q2)
    (by rw [hsp]; exact q3) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  intro Z t' hKz hAz hrz hax hspz hbx hbp h12 h13 h14 h15
  rw [hsp] at hspz hbx hbp h12
  exact k Z t' hKz hAz hrz (hax.trans (by rw [hg] <;> rfl)) hspz hbx hbp h12 (h13.trans (by rw [hg] <;> rfl))
    (h14.trans (by rw [hg] <;> rfl)) (h15.trans (by rw [hg] <;> rfl))

/-! ## To `MORECORE (-extra)` -/

set_option maxHeartbeats 4000000 in
/-- `systrim (pad, &main_arena)` from the entry (`rdi = pad`), the break `b` known, `__morecore` the default: the run
reaches the caller with `eax` 0, the registers a call keeps as at the entry and the bytes as at the entry but for
the 80 below the stack pointer (`k0`); or, `extra` not 0 and the break the top chunk's end, the `call` of
`MORECORE (-extra)` (94) with `rdi = -extra`, `rbx = ts`, `rbp` the break, `r12 = extra`, the frame of the three
pushes (`k1`). -/
theorem stm_pre {fb : Addr} {lim : Nat} {b fsb : Addr} {ks : Kst} {T Z ps : Addr} {X : State} {t : Nat}
    {V : Addr → Byte} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L stm_at stm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stm_at)
    (hsp : 0x7a4c40 + 80 ≤ X.cpu.gpr.rsp.toNat) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hstk : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hlr : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot F.data a)
    (hT : rdq(V, 7940768#64) = T) (hZ : rdq(V, T + 8#64) = Z) (hps : rdq(V, 7943128#64) = ps)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at) (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hT8 : (T + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 80)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (f4 : ∀ i < 8, Foot F.data (Addr.add 7942872#64 i))
    (hcurD : ∀ i < 8, Foot F.data (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : ∀ V' Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rax = 0#64 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Km X.cpu.gpr Y.cpu.gpr →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = V a) →
      GoG prof L o gev gP gE Y t')
    (k1 : ∀ V' Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = stm_at.add 94 →
      b = T + (Z &&& 18446744073709551608#64) →
      Y.cpu.gpr.rdi = 0 - stmE (Z &&& 18446744073709551608#64) X.cpu.gpr.rdi ps →
      (stmE (Z &&& 18446744073709551608#64) X.cpu.gpr.rdi ps == 0) = false →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Y.cpu.gpr.rbx = Z &&& 18446744073709551608#64 →
      Y.cpu.gpr.rbp = b → Y.cpu.gpr.r12 = stmE (Z &&& 18446744073709551608#64) X.cpu.gpr.rdi ps →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      rdq(V', X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp →
      rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = V a) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := X.cpu.gpr.rsp.isLt
  have hcu : curbrk.toNat = 8014904 := by decide
  obtain ⟨e1, e2, e3, e4⟩ := Cal.fr_e (S := X.cpu.gpr.rsp) (by omega)
  have e5 : (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 48).toNat = X.cpu.gpr.rsp.toNat - 80 := by
    rw [BitVec.toNat_sub, e4, show (48 : Addr).toNat = 48 from rfl]
    omega
  have hfd : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (Nat.lt_or_ge a.toNat X.cpu.gpr.rsp.toNat).elim (fun h => c.hws _ (hstk a h1 h))
      (fun h => hlr a h h2)
  -- the pushes, to 75 or to `MORECORE (0)`
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (Z := Z) (ps := ps) (by omega) hT hZ hps (by omega) (by omega)
      (stk hstk (by rw [e1]; omega) (by rw [e1]; omega) (by omega))
      (stk hstk (by rw [e2]; omega) (by rw [e2]; omega) (by omega))
      (stk hstk (by rw [e3]; omega) (by rw [e3]; omega) (by omega)) f1 f2 f3) ?_
  rintro j' g₁ fl V₁ ⟨rfl, hsp₁, hbx₁, h13₁, h14₁, h15₁, hj⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  have o₁ : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx a = V a :=
    fun a ha => fr3_out _ _ _ _ _ (by omega) a (by omega)
  rcases hj with rfl | ⟨rfl, hdi₁, h12₁, hex⟩
  · -- `return 0`
    obtain ⟨r3, r2, r1, r0⟩ := frame (W := fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx)
      (by omega) hsp8 hra (fun _ _ _ => rfl)
    refine ret75 c hfs hin hK₁ hA₁ hr₁ ?_ ?_ ?_ ?_ hin₂ h₂ ?_ ?_
    · rw [hsp₁]; exact stk hfd (by rw [e3]; omega) (by rw [e3]; omega) (by omega)
    · rw [hsp₁, Cal.a3s]; exact stk hfd (by rw [e2]; omega) (by rw [e2]; omega) (by omega)
    · rw [hsp₁, Cal.a3s, Cal.a2s]; exact stk hfd (by rw [e1]; omega) (by rw [e1]; omega) (by omega)
    · rw [hsp₁, Cal.a3s, Cal.a2s, Cal.a1s]; exact stk hfd (by omega) (by omega) (by omega)
    · rw [hsp₁, Cal.a3s, Cal.a2s, Cal.a1s]; exact r0
    intro Z' t' hKz hAz hrz hax hspz hbx hbp h12 h13 h14 h15
    rw [hsp₁, Cal.a3s, Cal.a2s, Cal.a1s] at hspz
    rw [hsp₁] at hbx hbp h12
    rw [Cal.a3s] at hbp
    rw [Cal.a3s, Cal.a2s] at h12
    exact k0 _ Z' t' hKz hAz hrz hax hspz ⟨hbx.trans r3, hbp.trans r2, h12.trans r1, h13.trans h13₁,
      h14.trans h14₁, h15.trans h15₁⟩ o₁
  -- `MORECORE (0)`
  refine c.s_callR hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_51 _) (by rw [mc_51]; exact f4) hinD
    (Dmc.lt_len (j := 0) (by decide)) ?_ (by rw [hsp₁]; exact stk hstk (by rw [e4]; omega) (by rw [e4]; omega)
      (by omega)) ?_
  · rw [mc_51, Cal.rd_out (x := 7942872#64) (n := 8) o₁ (by tn) (.inl (by tn))]
    exact hmc
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 := by
    rw [hg₂]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hsp₁]
  have o₂ : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      Vst (fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8)
        (toBytesLE (stm_at.add (51 + 6)) 8) a = V a := fun a ha => by
    rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega)]
    exact o₁ a ha
  have u₂ : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 24 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      Vst (fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8)
        (toBytesLE (stm_at.add (51 + 6)) 8) a = fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx a :=
    fun a h1 h2 => Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega)
  refine Dmc.dmc_zero c hB hinD hinS hK₂ hA₂ hr₂ hcurD hml
    (by rw [hsp₂]; exact stk hstk (by omega) (by omega) (by omega))
    (by rw [hsp₂]; exact stk hstk (by rw [e4]; omega) (by rw [e4]; omega) (by omega))
    (by rw [hsp₂, e4]; omega) (by rw [hsp₂, e4]; omega) ?_ ?_ (by rw [hg₂]; exact hdi₁) hin (j₂ := 57)
    (lt_len (by decide)) ?_ ?_
  · rw [Cal.rd_out (x := curbrk) (n := 8) o₂ (by omega) (.inl (by omega))]; exact hcb
  · rw [Cal.rd_out (x := 7944640#64) (n := 4) o₂ (by tn) (.inl (by tn))]
    exact hm0
  · rw [hsp₂, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e4]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
  intro V₃ Z' t₃ hKz hAz hrz hax hdx ⟨s1, s2, s3, s4, s5, s6, s7⟩ hfr
  rw [hsp₂, e4] at hfr
  have o₃ : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 80 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₃ a = V a :=
    fun a ha => (hfr a (by omega)).trans (o₂ a ha)
  have u₃ : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 24 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V₃ a = fr3 V X.cpu.gpr.rsp X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx a :=
    fun a h1 h2 => (hfr a (by omega)).trans (u₂ a h1 h2)
  obtain ⟨r3, r2, r1, r0⟩ := frame (W := V₃) (by omega) hsp8 hra u₃
  have hspZ : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by
    rw [s1, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hbxZ : Z'.cpu.gpr.rbx = Z &&& 18446744073709551608#64 := s2.trans (by rw [hg₂]; exact hbx₁)
  have h12Z : Z'.cpu.gpr.r12 = stmE (Z &&& 18446744073709551608#64) X.cpu.gpr.rdi ps :=
    s4.trans (by rw [hg₂]; exact h12₁)
  have h13Z : Z'.cpu.gpr.r13 = X.cpu.gpr.r13 := s5.trans (by rw [hg₂]; exact h13₁)
  have h14Z : Z'.cpu.gpr.r14 = X.cpu.gpr.r14 := s6.trans (by rw [hg₂]; exact h14₁)
  have h15Z : Z'.cpu.gpr.r15 = X.cpu.gpr.r15 := s7.trans (by rw [hg₂]; exact h15₁)
  -- the break against the top chunk's end
  refine (c_57 prof fb).run c hfs hin _ hKz hAz hrz
    (vc_57 (T := T) (by rw [Cal.rd_out (x := 7940768#64) (n := 8) o₃ (by tn)
      (.inl (by tn))]; exact hT) f1) ?_
  rintro j' g₄ fl V₄ ⟨hVV, hsp₄, hbx₄, h12₄, h13₄, h14₄, h15₄, hj⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst V₄
  subst hg₄
  rcases hj with rfl | ⟨rfl, hb, hbp₄, hdi₄⟩
  · -- `return 0`
    have hsp₄' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hsp₄.trans hspZ
    refine ret75 c hfs hin hK₄ hA₄ hr₄ ?_ ?_ ?_ ?_ hin₂ h₂ ?_ ?_
    · rw [hsp₄']; exact stk hfd (by rw [e3]; omega) (by rw [e3]; omega) (by omega)
    · rw [hsp₄', Cal.a3s]; exact stk hfd (by rw [e2]; omega) (by rw [e2]; omega) (by omega)
    · rw [hsp₄', Cal.a3s, Cal.a2s]; exact stk hfd (by rw [e1]; omega) (by rw [e1]; omega) (by omega)
    · rw [hsp₄', Cal.a3s, Cal.a2s, Cal.a1s]; exact stk hfd (by omega) (by omega) (by omega)
    · rw [hsp₄', Cal.a3s, Cal.a2s, Cal.a1s]; exact r0
    intro Z₅ t' hKz₅ hAz₅ hrz₅ hax₅ hspz hbx hbp h12 h13 h14 h15
    rw [hsp₄', Cal.a3s, Cal.a2s, Cal.a1s] at hspz
    rw [hsp₄'] at hbx hbp h12
    rw [Cal.a3s] at hbp
    rw [Cal.a3s, Cal.a2s] at h12
    exact k0 _ Z₅ t' hKz₅ hAz₅ hrz₅ hax₅ hspz ⟨hbx.trans r3, hbp.trans r2, h12.trans r1,
      h13.trans (h13₄.trans h13Z), h14.trans (h14₄.trans h14Z), h15.trans (h15₄.trans h15Z)⟩ o₃
  -- `MORECORE (-extra)`
  refine k1 V₃ Y₄ t₄ hK₄ hA₄ hr₄ ?_ (hdi₄.trans (by rw [h12Z])) hex (hsp₄.trans hspZ) (hbx₄.trans hbxZ)
    (hbp₄.trans hax) (h12₄.trans h12Z) (h13₄.trans h13Z) (h14₄.trans h14Z) (h15₄.trans h15Z) r3 r2 r1 r0 o₃
  rw [← hax, hb, hbxZ]

/-! ## From `MORECORE (-extra)`'s return -/

set_option maxHeartbeats 4000000 in
/-- `systrim` from the return of `MORECORE (-extra)` (100), `rsp` the frame of the three pushes, `rbx = ts`, `rbp`
the break before, `__after_morecore_hook` null, the break now `b`: the run reaches the caller with the registers a
call keeps those the frame held, and either `eax` 0 and the bytes as at 100 but for the 56 below the stack pointer
(`k0`), or (`released = rbp - b` not 0) `eax` 1 and the bytes `stmV` there (`k1`). -/
theorem stm_post {fb : Addr} {lim : Nat} {b fsb : Addr} {ks : Kst} {T sm : Addr} {X : State} {t : Nat}
    {V : Addr → Byte} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L stm_at stm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stm_at.add 100)
    (hsp : 0x7a4c40 + 56 ≤ X.cpu.gpr.rsp.toNat) (hsp8 : X.cpu.gpr.rsp.toNat + 32 ≤ 2 ^ 64)
    (hstk : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hfr : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 32 → Foot F.data a)
    (hhk : rdq(V, 8013152#64) = 0#64) (hT : rdq(V, 7940768#64) = T) (hsm : rdq(V, 7942856#64) = sm)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at) (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hT8 : (T + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 56)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 8013152#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add 7942872#64 i))
    (hcurD : ∀ i < 8, Foot F.data (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add 7942856#64 i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k0 : ∀ V' Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rax = 0#64 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 → Y.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp) →
      Y.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 8) → Y.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8 + 8) →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = V a) →
      GoG prof L o gev gP gE Y t')
    (k1 : ∀ V' Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rax = 1#64 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 → Y.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp) →
      Y.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 8) → Y.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 8 + 8) →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      X.cpu.gpr.rbp ≠ b →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        V' a = stmV V T sm (X.cpu.gpr.rbp - b) X.cpu.gpr.rbx a) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := X.cpu.gpr.rsp.isLt
  have hcu : curbrk.toNat = 8014904 := by decide
  have e8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := Prepare.toNat_sub8 (by omega)
  have e56 : (X.cpu.gpr.rsp - 8 - 48).toNat = X.cpu.gpr.rsp.toNat - 56 := by
    rw [BitVec.toNat_sub, e8, show (48 : Addr).toNat = 48 from rfl]
    omega
  have a1 : (X.cpu.gpr.rsp + 8).toNat = X.cpu.gpr.rsp.toNat + 8 := ta8 (by omega)
  have a2 : (X.cpu.gpr.rsp + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 16 := by rw [ta8 (by rw [a1]; omega), a1]
  have a3 : (X.cpu.gpr.rsp + 8 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 24 := by
    rw [ta8 (by rw [a2]; omega), a2]
  -- the hook, `rdi = 0`
  refine (c_100 prof fb).run c hfs hin _ hK hA hrip (vc_100 hhk f1) ?_
  rintro j' g₁ fl V₁ ⟨rfl, hVV, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  refine (c_112 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ vc_112 ?_
  rintro j' g₂ fl V₂ ⟨rfl, hVV, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hg₁] <;> rfl
  -- `MORECORE (0)`
  refine c.s_callR hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_114 _) (by rw [mc_114]; exact f4) hinD
    (Dmc.lt_len (j := 0) (by decide)) (by rw [mc_114]; exact hmc)
    (by rw [hsp₂]; exact stk hstk (by rw [e8]; omega) (by rw [e8]; omega) (by omega)) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsp₂] at hA₃
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by
    rw [hg₃]; show Y₂.cpu.gpr.rsp - 8 = _; rw [hsp₂]
  have o₂ : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (stm_at.add (114 + 6)) 8) a = V a := fun a ha =>
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)
  have u₂ : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 32 →
      Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (stm_at.add (114 + 6)) 8) a = V a := fun a h1 h2 =>
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)
  refine Dmc.dmc_zero c hB hinD hinS hK₃ hA₃ hr₃ hcurD hml
    (by rw [hsp₃]; exact stk hstk (by omega) (by omega) (by omega))
    (by rw [hsp₃]; exact stk hstk (by rw [e8]; omega) (by rw [e8]; omega) (by omega))
    (by rw [hsp₃, e8]; omega) (by rw [hsp₃, e8]; omega) ?_ ?_ (by rw [hg₃, hg₂] <;> rfl) hin (j₂ := 120)
    (lt_len (by decide)) ?_ ?_
  · rw [Cal.rd_out (x := curbrk) (n := 8) o₂ (by omega) (.inl (by omega))]; exact hcb
  · rw [Cal.rd_out (x := 7944640#64) (n := 4) o₂ (by tn) (.inl (by tn))]
    exact hm0
  · rw [hsp₃, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
  intro V₃ Z t₄ hKz hAz hrz hax hdx ⟨s1, s2, s3, s4, s5, s6, s7⟩ hfz
  rw [hsp₃, e8] at hfz
  have o₃ : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₃ a = V a :=
    fun a ha => (hfz a (by omega)).trans (o₂ a ha)
  have u₃ : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 32 → V₃ a = V a :=
    fun a h1 h2 => (hfz a (by omega)).trans (u₂ a h1 h2)
  have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [s1, hsp₃]; exact BitVec.sub_add_cancel _ _
  have hbxZ : Z.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [s2, hg₃, hg₂, hg₁] <;> rfl
  have hbpZ : Z.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [s3, hg₃, hg₂, hg₁] <;> rfl
  have h12Z : Z.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [s4, hg₃, hg₂, hg₁] <;> rfl
  have h13Z : Z.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [s5, hg₃, hg₂, hg₁] <;> rfl
  have h14Z : Z.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [s6, hg₃, hg₂, hg₁] <;> rfl
  have h15Z : Z.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [s7, hg₃, hg₂, hg₁] <;> rfl
  have q0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i) := stk hfr (by omega) (by omega) (by omega)
  have q1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8) i) :=
    stk hfr (by rw [a1]; omega) (by rw [a1]; omega) (by omega)
  have q2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8) i) :=
    stk hfr (by rw [a2]; omega) (by rw [a2]; omega) (by omega)
  have q3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8 + 8 + 8) i) :=
    stk hfr (by omega) (by omega) (by omega)
  -- the new break
  refine (c_120 prof fb).run c hfs hin _ hKz hAz hrz
    (vc_120 (T := T) (by rw [Cal.rd_out (x := 7940768#64) (n := 8) o₃ (by tn)
      (.inl (by tn))]; exact hT) f2) ?_
  rintro j' g₄ fl V₄ ⟨hVV, hsp₄, h13₄, h14₄, h15₄, hj⟩ Y₄ t₅ hK₄ hA₄ hr₄ hg₄ -
  subst V₄
  subst hg₄
  have hsp₄' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := hsp₄.trans hspZ
  have hb0 : rdq(V₃, X.cpu.gpr.rsp) = rdq(V, X.cpu.gpr.rsp) := by
    rw [rd_in (x := X.cpu.gpr.rsp) (n := 8) u₃ (by omega) (by omega) (by omega)]
  have hb1 : rdq(V₃, X.cpu.gpr.rsp + 8) = rdq(V, X.cpu.gpr.rsp + 8) := by
    rw [rd_in (x := X.cpu.gpr.rsp + 8) (n := 8) u₃ (by rw [a1]; omega) (by rw [a1]; omega) (by rw [a1]; omega)]
  have hb2 : rdq(V₃, X.cpu.gpr.rsp + 8 + 8) = rdq(V, X.cpu.gpr.rsp + 8 + 8) := by
    rw [rd_in (x := X.cpu.gpr.rsp + 8 + 8) (n := 8) u₃ (by rw [a2]; omega) (by rw [a2]; omega) (by rw [a2]; omega)]
  have hb3 : rdq(V₃, X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂ := by
    rw [rd_in (x := X.cpu.gpr.rsp + 8 + 8 + 8) (n := 8) u₃ (by omega) (by omega) (by omega)]; exact hra
  rcases hj with rfl | ⟨rfl, hne, hbp₄, hax₄, hbx₄, h12₄⟩
  · -- `return 0`
    refine ret75 c hfs hin hK₄ hA₄ hr₄ (by rw [hsp₄']; exact q0) (by rw [hsp₄']; exact q1)
      (by rw [hsp₄']; exact q2) (by rw [hsp₄']; exact q3) hin₂ h₂ (by rw [hsp₄']; exact hb3) ?_
    intro Y t' hKy hAy hry hay hspy hbx hbp h12 h13 h14 h15
    rw [hsp₄'] at hspy hbx hbp h12
    exact k0 V₃ Y t' hKy hAy hry hay hspy (hbx.trans hb0) (hbp.trans hb1) (h12.trans hb2)
      (h13.trans (h13₄.trans h13Z)) (h14.trans (h14₄.trans h14Z)) (h15.trans (h15₄.trans h15Z)) o₃
  -- `main_arena.system_mem -= released`
  refine c.s_sub_rip64r hK₄ hA₄ hin (lt_len (by decide)) hr₄ (sub_141 _) sm_141 w1 ?_
  rintro Y₅ t₆ hK₅ hA₅ ⟨hr₅, hg₅⟩
  have hrv : rv Y₄ 64 5 = X.cpu.gpr.rbp - b := by
    show (Y₄.cpu.gpr.get (regOf 5)).setWidth 64 = _
    rw [BitVec.setWidth_eq]
    show Y₄.cpu.gpr.rbp = _
    rw [hbp₄, hax, hbpZ]
  have hsmv : rdq(V₃, 7942856#64) = sm := by
    rw [Cal.rd_out (x := 7942856#64) (n := 8) o₃ (by tn)
      (.inl (by tn))]
    exact hsm
  rw [hrv, hsmv] at hA₅
  have hax₅ : Y₅.cpu.gpr.rax = T := by rw [hg₅]; exact hax₄
  have hbx₅ : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx - (X.cpu.gpr.rbp - b) := by rw [hg₅, hbx₄, hbxZ, hbpZ, hax]
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₅]; exact hsp₄'
  -- `set_head`, `eax = 1`
  refine (c_148 prof fb).run c hfs hin _ hK₅ hA₅ (by rw [hr₅] <;> rfl) (vc_148 (by rw [hax₅]; exact w2)) ?_
  rintro j' g₆ fl V₆ ⟨rfl, hVV, rfl⟩ Y₆ t₇ hK₆ hA₆ hr₆ hg₆ -
  subst V₆
  rw [hax₅, hbx₅] at hA₆
  have hsp₆ : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₆]; exact hsp₅
  have u₆ : ∀ a : Addr, X.cpu.gpr.rsp.toNat ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 32 →
      Vst (Vst V₃ 7942856#64 (toBytesLE (sm - (X.cpu.gpr.rbp - b)) 8)) (T + 8#64)
        (toBytesLE (X.cpu.gpr.rbx - (X.cpu.gpr.rbp - b) ||| 1#64) 8) a = V a := fun a h1 h2 => by
    rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
      Vst_out _ _ _ _ (by rw [toBytesLE_length]; simp only [BitVec.toNat_ofNat]; omega)
        (by rw [toBytesLE_length]; simp only [BitVec.toNat_ofNat]; omega)]
    exact u₃ a h1 h2
  refine ret77 c hfs hin hK₆ hA₆ hr₆ (by rw [hsp₆]; exact q0) (by rw [hsp₆]; exact q1)
    (by rw [hsp₆]; exact q2) (by rw [hsp₆]; exact q3) hin₂ h₂
    (by rw [hsp₆, rd_in (x := X.cpu.gpr.rsp + 8 + 8 + 8) (n := 8) u₆ (by omega) (by omega) (by omega)]; exact hra) ?_
  intro Y t' hKy hAy hry hay hspy hbx hbp h12 h13 h14 h15
  rw [hsp₆] at hspy hbx hbp h12
  rw [rd_in (x := X.cpu.gpr.rsp) (n := 8) u₆ (by omega) (by omega) (by omega)] at hbx
  rw [rd_in (x := X.cpu.gpr.rsp + 8) (n := 8) u₆ (by rw [a1]; omega) (by rw [a1]; omega) (by rw [a1]; omega)] at hbp
  rw [rd_in (x := X.cpu.gpr.rsp + 8 + 8) (n := 8) u₆ (by rw [a2]; omega) (by rw [a2]; omega) (by rw [a2]; omega)] at h12
  refine k1 _ Y t' hKy hAy hry (hay.trans (by rw [hg₆] <;> rfl)) hspy hbx hbp h12
    (h13.trans (by rw [hg₆, hg₅]; exact h13₄.trans h13Z)) (h14.trans (by rw [hg₆, hg₅]; exact h14₄.trans h14Z))
    (h15.trans (by rw [hg₆, hg₅]; exact h15₄.trans h15Z)) ?_ ?_
  · intro h
    exact hne (hbpZ.trans (h.trans hax.symm))
  · intro a ha
    exact Tls.Vst_congr _ _ _ _ _ (Tls.Vst_congr _ _ _ _ _ (o₃ a ha))

end

end FV7z.Stm
