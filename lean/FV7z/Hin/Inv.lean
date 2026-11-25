import FV7z.Hin.Cuts
import FV7z.Icw.Holds
import FV7z.Lemmas.SpCallKx
/-!
# `handle_intel`: the contract and the invariants of its cut points (PLAN.md M, ctor 103)

glibc's `handle_intel (name, cpu_features)` at `0x65d010` in `7zzs` (offset 1280 of the `Hca` code,
`sysdeps/x86/dl-cacheinfo.h`), for `name` one of 188, 191, 194. Its frame (`fr`, 88 bytes below the return address):
the six saved registers above `fr + 40`, the stack protector's canary at `fr + 24` (from `fs:0x28`), the two flags
`has_level_2` and `no_level_2_or_3` at `fr + 23` and `fr + 22`, `maxidx` at `fr + 12`, a saved `edx` at `fr + 8`.

The loop: `cpuid(2)`, then `intel_check_word` (`Icw`) on `eax`, `ebx`, `ecx`, `edx` (each call may end the loop with a
result), while `maxidx` (the low byte of `eax` on the first round) is above the round's count `r14`. The measure is
`100 · (256 - r14) + c`: `r14` stays at most 255, `maxidx` too.

`Te` is what it needs at its entry, `Rh` what holds at its return address: `rsp` 8 up, `rbx`, `rbp`, `r12`–`r15` as at
the entry, the bytes as at the entry but for the 128 bytes below the return address (its frame, `intel_check_word`'s
frame and its return address's slot).
-/
namespace FV7z.Hin
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length pcp pcp_0 prt prt_0)
open FV7z.Icw (icw_at icw_at_eq)

/-! ## The code: `cpuid`, the four calls of `intel_check_word`, the `ret` -/

def pc1422 : List Byte := [0xe8, 0x3d, 0xfc, 0xff, 0xff]
def pc1457 : List Byte := [0xe8, 0x1a, 0xfc, 0xff, 0xff]
def pc1489 : List Byte := [0xe8, 0xfa, 0xfb, 0xff, 0xff]
def pc1522 : List Byte := [0xe8, 0xd9, 0xfb, 0xff, 0xff]
theorem pc1422_0 : ∀ feat, Dec feat pc1422 0 (FV7z.mk .call 64 [.rel 18446744073709550653] 5) := by dec_rfl
theorem pc1457_0 : ∀ feat, Dec feat pc1457 0 (FV7z.mk .call 64 [.rel 18446744073709550618] 5) := by dec_rfl
theorem pc1489_0 : ∀ feat, Dec feat pc1489 0 (FV7z.mk .call 64 [.rel 18446744073709550586] 5) := by dec_rfl
theorem pc1522_0 : ∀ feat, Dec feat pc1522 0 (FV7z.mk .call 64 [.rel 18446744073709550553] 5) := by dec_rfl
set_option maxRecDepth 100000 in
theorem wc1422 : pc1422 <+: hca.drop 1422 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc1457 : pc1457 <+: hca.drop 1457 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc1489 : pc1489 <+: hca.drop 1489 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc1522 : pc1522 <+: hca.drop 1522 := by decide +kernel
theorem call_1422 (feat : Features) : Dec feat hca 1422 (FV7z.mk .call 64 [.rel 18446744073709550653] 5) :=
  Dec.shift (j := 1422) (k := 0) (pc1422_0 feat) wc1422 (Nat.zero_le _)
theorem call_1457 (feat : Features) : Dec feat hca 1457 (FV7z.mk .call 64 [.rel 18446744073709550618] 5) :=
  Dec.shift (j := 1457) (k := 0) (pc1457_0 feat) wc1457 (Nat.zero_le _)
theorem call_1489 (feat : Features) : Dec feat hca 1489 (FV7z.mk .call 64 [.rel 18446744073709550586] 5) :=
  Dec.shift (j := 1489) (k := 0) (pc1489_0 feat) wc1489 (Nat.zero_le _)
theorem call_1522 (feat : Features) : Dec feat hca 1522 (FV7z.mk .call 64 [.rel 18446744073709550553] 5) :=
  Dec.shift (j := 1522) (k := 0) (pc1522_0 feat) wc1522 (Nat.zero_le _)

theorem wcp1376 : pcp <+: hca.drop 1376 := by decide +kernel
theorem cpuid_1376 (feat : Features) : Dec feat hca 1376 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 1376) (k := 0) (pcp_0 feat) wcp1376 (Nat.zero_le _)
theorem wr1598 : prt <+: hca.drop 1598 := by decide +kernel
theorem ret_1598 (feat : Features) : Dec feat hca 1598 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 1598) (k := 0) (prt_0 feat) wr1598 (Nat.zero_le _)

/-- The entry. -/
abbrev hin_at : Addr := 0x65d010
theorem hin_at_eq : Addr.add hca_at 1280 = hin_at := by decide

/-! ## The contract -/

/-- What `handle_intel` needs at its entry (`rsp` at the return address, `fb` the `fs` base). -/
structure Te (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb : Addr) (g : Gprs)
    (V : Addr → Byte) : Prop where
  rdi : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64
  /-- The saved registers, the frame, `intel_check_word`'s frame and the return address's slot. -/
  st : ∀ i < 128, Foot Wl (Addr.add (g.rsp - 128#64) i)
  /-- The same and the return address. -/
  ld : ∀ i < 136, Foot F.data (Addr.add (g.rsp - 128#64) i)
  lo : 128 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  /-- The canary at `fs:0x28`, apart from the stack. -/
  cn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  cnf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  cna : (fb + 40#64).toNat + 8 + 128 ≤ g.rsp.toNat ∨ g.rsp.toNat ≤ (fb + 40#64).toNat
  /-- `cpu_features->basic.max_cpuid`, the family and the model. -/
  mx : ∀ i < 4, Foot F.data (Addr.add 8014668#64 i)
  fam : ∀ i < 4, Foot F.data (Addr.add 8014672#64 i)
  mdl : ∀ i < 4, Foot F.data (Addr.add 8014676#64 i)
  /-- `intel_02_known`. -/
  tab : ∀ x : Addr, 7283008 ≤ x.toNat → x.toNat < 7283008 + 544 → Foot F.data x
  ret : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
    ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)) = e₂.add j₂

/-- The frame's base: `rsp` after the six `push`es and `sub rsp, 0x28`. -/
abbrev fr (s : Addr) : Addr := s - 8 - 8 - 8 - 8 - 8 - 8 - 40#64

/-- The bytes after the six `push`es. -/
abbrev P6 (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r15 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.r14 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.r13 8)) (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.r12 8))
    (g₀.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g₀.rbp 8)) (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- The bytes after the canary's store. -/
abbrev Vh (fb : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (P6 g₀ V₀) (fr g₀.rsp + 24#64)
    (toBytesLE (ofBytesLE 64 (List.map (P6 g₀ V₀) (byteAddrs (fb + 40#64) 8))) 8)

/-- Not in `intel_check_word`'s frame or its return address's slot (`fr - 40` to `fr`), not `fr + 8` to `fr + 16`,
not one of the two flags: on offsets, `s` the entry's `rsp`. -/
def On (s y : Nat) : Prop :=
  (y + 128 < s ∨ s ≤ y + 88) ∧ (y + 80 < s ∨ s ≤ y + 72) ∧ y + 66 ≠ s ∧ y + 65 ≠ s

/-- The bytes that stay as after the canary's store. -/
def Out (s a : Addr) : Prop := On s.toNat a.toNat

/-- The bytes as at the entry but for the 128 below the return address. -/
def KeepH (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ a : Addr, (a.toNat + 128 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) → V a = V₀ a

/-- At the return address. -/
def Rh (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15 ∧ KeepH g₀ V₀ V

/-! ## The invariants -/

/-- In the frame. -/
def Mf (fb : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = fr g₀.rsp ∧ ∀ a, Out g₀.rsp a → V a = Vh fb g₀ V₀ a

/-- In the loop: `name`, the flags' addresses, the round's count and `maxidx` at most 255. -/
def Lp (fb : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  Mf fb g₀ V₀ g V ∧ (g.rbp = 188#64 ∨ g.rbp = 191#64 ∨ g.rbp = 194#64) ∧ g.r12 = fr g₀.rsp + 23#64 ∧
    g.r13 = fr g₀.rsp + 22#64 ∧ g.r14.toNat ≤ 255 ∧
    (ofBytesLE 32 (List.map V (byteAddrs (fr g₀.rsp + 12#64) 4))).toNat ≤ 255

/-- At a call of `intel_check_word`: its arguments. -/
def Ca (g₀ g : Gprs) : Prop :=
  (g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64) ∧ g.rcx = fr g₀.rsp + 22#64 ∧ g.rdx = fr g₀.rsp + 23#64 ∧
    g.r8 = 8014676#64 + 18446744073709551612#64 ∧ g.r9 = 8014676#64

/-- The invariants of the cut points (and of the `cpuid` and the calls), with the measure `n`. -/
def Ih (fb : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  if ℓ = 1280 then n = 25700 ∧ g = g₀ ∧ V = V₀ else
  if ℓ = 1371 then n = 100 * (256 - g.r14.toNat) + 90 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1376 then n = 100 * (256 - g.r14.toNat) + 85 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1378 then n = 100 * (256 - g.r14.toNat) + 80 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1403 then n = 100 * (256 - g.r14.toNat) + 70 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1422 then n = 100 * (256 - g.r14.toNat) + 60 ∧ Lp fb g₀ V₀ g V ∧ Ca g₀ g else
  if ℓ = 1427 then n = 100 * (256 - g.r14.toNat) + 50 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1457 then n = 100 * (256 - g.r14.toNat) + 45 ∧ Lp fb g₀ V₀ g V ∧ Ca g₀ g else
  if ℓ = 1462 then n = 100 * (256 - g.r14.toNat) + 40 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1489 then n = 100 * (256 - g.r14.toNat) + 35 ∧ Lp fb g₀ V₀ g V ∧ Ca g₀ g else
  if ℓ = 1494 then n = 100 * (256 - g.r14.toNat) + 30 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1522 then n = 100 * (256 - g.r14.toNat) + 25 ∧ Lp fb g₀ V₀ g V ∧ Ca g₀ g else
  if ℓ = 1527 then n = 100 * (256 - g.r14.toNat) + 20 ∧ Lp fb g₀ V₀ g V else
  if ℓ = 1568 then n = 2 ∧ Mf fb g₀ V₀ g V else
  False

/-- At the `ret`. -/
def Fh (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 1598 ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧
    g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧ KeepH g₀ V₀ V

/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (fb : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ Ih fb g₀ V₀ j' n' g' V') ∨ Fh g₀ V₀ j' g' V'

/-- What the code from a cut point needs for `Q` at the next ones: at the `cpuid`, `Q` after it on every CPU; at a call
of `intel_check_word`, its contract. -/
def WtC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb : Addr) (ℓ : Nat) :
    Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 1376 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 1378 (cpuidG prof cpu g) fl V else
  if ℓ = 1422 then CallK Wl hca_at 1427 (Icw.Te F Wl L) Icw.Rh else
  if ℓ = 1457 then CallK Wl hca_at 1462 (Icw.Te F Wl L) Icw.Rh else
  if ℓ = 1489 then CallK Wl hca_at 1494 (Icw.Te F Wl L) Icw.Rh else
  if ℓ = 1522 then CallK Wl hca_at 1527 (Icw.Te F Wl L) Icw.Rh else
  Wt fb ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-- The cut points' pieces in a run with the code, the `fs` base and `intel_check_word`. -/
theorem spC (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hca_at hca)
    (hi : FnK prof F Wl L s₀ o icw_at (Icw.Te F Wl L) Icw.Rh) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o hca_at ℓ (WtC prof F Wl L fb ℓ) := by
  unfold WtC
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_1376 _)
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_1422 _) hin (lt_len (by decide)) (by decide) icw_at_eq hi
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_1457 _) hin (lt_len (by decide)) (by decide) icw_at_eq hi
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_1489 _) hin (lt_len (by decide)) (by decide) icw_at_eq hi
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_1522 _) hin (lt_len (by decide)) (by decide) icw_at_eq hi
  exact (spAll prof fb ℓ).at c hfs hin

/-! ## Arithmetic -/

theorem t128 (s : Addr) (h : 128 ≤ s.toNat) : (s - 128#64).toNat = s.toNat - 128 := by bv_omega
theorem t_fr (s : Addr) (h : 128 ≤ s.toNat) : (fr s).toNat = s.toNat - 88 := by unfold fr; bv_omega
theorem tc {x : Addr} {m : Nat} (c : Nat) (hx : x.toNat = m) (h : m + c < 2 ^ 64) :
    (x + BitVec.ofNat 64 c).toNat = m + c := by
  subst hx; bv_omega
theorem ts8 {x : Addr} {m : Nat} (hx : x.toNat = m) (h : 8 ≤ m) : (x - 8).toNat = m - 8 := by subst hx; bv_omega
theorem sa8 (x : Addr) : x - 8 + 8 = x := by bv_omega

theorem p_1 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem p_2 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem p_3 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem p_4 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega
theorem p_5 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 40 := by bv_omega
theorem p_6 (s : Addr) (h : 128 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 48 := by bv_omega

theorem t8 {x : Addr} {m : Nat} (hx : x.toNat = m) (h : m + 8 < 2 ^ 64) : (x + 8).toNat = m + 8 := by
  subst hx; bv_omega

/-- The `pop`s' slots are the `push`es'. -/
theorem q_all (s : Addr) (h : 128 ≤ s.toNat) :
    fr s + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 = s ∧ fr s + 40#64 + 8 + 8 + 8 + 8 + 8 = s - 8 ∧
    fr s + 40#64 + 8 + 8 + 8 + 8 = s - 8 - 8 ∧ fr s + 40#64 + 8 + 8 + 8 = s - 8 - 8 - 8 ∧
    fr s + 40#64 + 8 + 8 = s - 8 - 8 - 8 - 8 ∧ fr s + 40#64 + 8 = s - 8 - 8 - 8 - 8 - 8 ∧
    fr s + 40#64 = s - 8 - 8 - 8 - 8 - 8 - 8 := by
  have hi := s.isLt
  have a0 := tc 40 (t_fr s h) (by omega)
  have a1 := t8 a0 (by omega)
  have a2 := t8 a1 (by omega)
  have a3 := t8 a2 (by omega)
  have a4 := t8 a3 (by omega)
  have a5 := t8 a4 (by omega)
  have a6 := t8 a5 (by omega)
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [a6]; omega
  · rw [a5, p_1 s h]; omega
  · rw [a4, p_2 s h]; omega
  · rw [a3, p_3 s h]; omega
  · rw [a2, p_4 s h]; omega
  · rw [a1, p_5 s h]; omega
  · rw [a0, p_6 s h]; omega

theorem r8e : (8014676#64 + 18446744073709551612#64 : BitVec 64) = 8014672#64 := by decide

/-- The measure, from a round's count to one with the same or a larger count. -/
theorem mlt {a b : BitVec 64} (e : a = b) {c d : Nat} (h : c < d) :
    100 * (256 - a.toNat) + c < 100 * (256 - b.toNat) + d := by
  subst e; omega

theorem m1280 : 100 * (256 - (BitVec.setWidth 64 1#32).toNat) + 90 < 25700 := by decide
theorem r1 : (BitVec.setWidth 64 1#32).toNat ≤ 255 := by decide
theorem sw8_le (x : BitVec 64) : (BitVec.setWidth 32 (BitVec.setWidth 8 x)).toNat ≤ 255 := by bv_omega
theorem sw32n (r : BitVec 64) (h : r.toNat ≤ 255) : (BitVec.setWidth 32 r).toNat = r.toNat := by bv_omega
theorem inc8 (r : BitVec 64) (h : r.toNat < 255) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (r + 1#64))).toNat = r.toNat + 1 := by bv_omega

/-- `ja`: above. -/
theorem orfw {w : Nat} {a b : BitVec w} (h : (decide (a.toNat < b.toNat) || decide (a = b)) = false) :
    b.toNat < a.toNat := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨h1, h2⟩ := h
  have : a.toNat ≠ b.toNat := fun e => h2 (BitVec.eq_of_toNat_eq e)
  omega

/-- `name`, through `ebp`. -/
theorem rd_of {d : BitVec 64} (h : d = 188#64 ∨ d = 191#64 ∨ d = 194#64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 d) = 188#64 ∨ BitVec.setWidth 64 (BitVec.setWidth 32 d) = 191#64 ∨
      BitVec.setWidth 64 (BitVec.setWidth 32 d) = 194#64 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- A measure goal: the registers' literal projected out, then `omega`. -/
macro "hin_om" : tactic => `(tactic| ((try dsimp only) <;> omega))

/-! ## The footprint -/

theorem fsub {R : List Rgn} {b x : Addr} {m k n : Nat} (h : ∀ i < m, Foot R (Addr.add b i))
    (hb : b.toNat + m ≤ 2 ^ 64) (hx : x.toNat = b.toNat + k) (hk : k + n ≤ m) :
    ∀ i < n, Foot R (Addr.add x i) := by
  intro i hi
  have e : Addr.add x i = Addr.add b (k + i) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_of_fits hi (by omega), toNat_add_of_fits (by omega : k + i < m) hb]
    omega
  rw [e]
  exact h _ (by omega)

/-- Bytes the run may store into: the 128 below the return address. -/
theorem fW (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : g₀.rsp.toNat ≤ x.toNat + 128)
    (h2 : x.toNat + n ≤ g₀.rsp.toNat) : ∀ i < n, Foot Wl (Addr.add x i) := by
  have e := t128 _ hT.lo
  have lo := hT.lo
  have hi := hT.hi
  exact fsub (k := x.toNat + 128 - g₀.rsp.toNat) hT.st (by omega) (by omega) (by omega)

/-- Bytes the run may load: the same and the return address. -/
theorem fD (hT : Te F Wl L fb g₀ V₀) {x : Addr} {n : Nat} (h1 : g₀.rsp.toNat ≤ x.toNat + 128)
    (h2 : x.toNat + n ≤ g₀.rsp.toNat + 8) : ∀ i < n, Foot F.data (Addr.add x i) := by
  have e := t128 _ hT.lo
  have lo := hT.lo
  have hi := hT.hi
  exact fsub (k := x.toNat + 128 - g₀.rsp.toNat) hT.ld (by omega) (by omega) (by omega)

/-- What the entry's piece needs of the footprint. -/
theorem ent_foot (hT : Te F Wl L fb g₀ V₀) :
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot Wl (Addr.add (fr g₀.rsp + 24#64) i)) ∧ (∀ i < 1, Foot Wl (Addr.add (fr g₀.rsp + 22#64) i)) ∧
    (∀ i < 1, Foot Wl (Addr.add (fr g₀.rsp + 23#64) i)) ∧ (∀ i < 4, Foot Wl (Addr.add (fr g₀.rsp + 12#64) i)) := by
  have lo := hT.lo
  have hi := hT.hi
  have e1 := p_1 _ lo
  have e2 := p_2 _ lo
  have e3 := p_3 _ lo
  have e4 := p_4 _ lo
  have e5 := p_5 _ lo
  have e6 := p_6 _ lo
  have e0 := t_fr _ lo
  have e24 := tc 24 e0 (by omega)
  have e22 := tc 22 e0 (by omega)
  have e23 := tc 23 e0 (by omega)
  have e12 := tc 12 e0 (by omega)
  exact ⟨fW hT (by omega) (by omega), fW hT (by omega) (by omega), fW hT (by omega) (by omega),
    fW hT (by omega) (by omega), fW hT (by omega) (by omega), fW hT (by omega) (by omega),
    fW hT (by omega) (by omega), fW hT (by omega) (by omega), fW hT (by omega) (by omega),
    fW hT (by omega) (by omega)⟩

/-! ## Bytes -/

/-- A store apart from the bytes that stay. -/
theorem mf_st {S : Addr} {V W : Addr → Byte} (hm : ∀ a, Out S a → V a = W a) (x : Addr) (bs : List Byte)
    (hx : x.toNat + bs.length ≤ 2 ^ 64)
    (hO : ∀ a : Addr, Out S a → a.toNat < x.toNat ∨ x.toNat + bs.length ≤ a.toNat) :
    ∀ a, Out S a → Vst V x bs a = W a :=
  fun a ha => (Tun.Vst_out _ _ _ _ hx (hO a ha)).trans (hm a ha)

/-- A load of bytes that stay. -/
theorem rdM {S : Addr} {V W : Addr → Byte} (hm : ∀ a, Out S a → V a = W a) (x : Addr) (n : Nat)
    (hx : x.toNat + n ≤ 2 ^ 64) (hO : ∀ y, x.toNat ≤ y → y < x.toNat + n → On S.toNat y) :
    List.map V (byteAddrs x n) = List.map W (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits (a := x) hj hx
  refine hm _ ?_
  unfold Out
  rw [e]
  exact hO _ (by omega) (by omega)

/-- Out of the frame, the bytes after the canary's store are those at the entry. -/
theorem Vh_out (hT : Te F Wl L fb g₀ V₀) (a : Addr)
    (h : a.toNat + 128 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) : Vh fb g₀ V₀ a = V₀ a := by
  have lo := hT.lo
  have hi := hT.hi
  have e1 := p_1 _ lo
  have e2 := p_2 _ lo
  have e3 := p_3 _ lo
  have e4 := p_4 _ lo
  have e5 := p_5 _ lo
  have e6 := p_6 _ lo
  have e24 := tc 24 (t_fr _ lo) (by omega)
  dsimp only [Vh, P6]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e24]; omega) (by rw [toBytesLE_length, e24]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e5]; omega) (by rw [toBytesLE_length, e5]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- From the frame's bytes to `KeepH`. -/
theorem keepH_of (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = Vh fb g₀ V₀ a) : KeepH g₀ V₀ V := by
  intro a h
  rw [hm a (by unfold Out On; omega)]
  exact Vh_out hT a h

/-- The return address after the run. -/
theorem rd_keepH (hT : Te F Wl L fb g₀ V₀) (hK : KeepH g₀ V₀ V) :
    List.map V (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have hi := hT.hi
  have e := toNat_add_of_fits (a := g₀.rsp) hj (by omega)
  exact hK _ (Or.inr (by omega))

/-- The entry's stores: the two flags and `maxidx`. -/
theorem ent_mf (hT : Te F Wl L fb g₀ V₀) : ∀ a, Out g₀.rsp a →
    Vst (Vst (Vst (Vh fb g₀ V₀) (fr g₀.rsp + 22#64) (toBytesLE (0#8) 1)) (fr g₀.rsp + 23#64) (toBytesLE (0#8) 1))
      (fr g₀.rsp + 12#64) (toBytesLE (1#32) 4) a = Vh fb g₀ V₀ a := by
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e22 := tc 22 e0 (by omega)
  have e23 := tc 23 e0 (by omega)
  have e12 := tc 12 e0 (by omega)
  refine mf_st (mf_st (mf_st (fun _ _ => rfl) _ _ ?_ ?_) _ _ ?_ ?_) _ _ ?_ ?_ <;>
    first
    | (simp only [toBytesLE_length]; omega)
    | (intro a ha; simp only [Out, On, toBytesLE_length] at ha ⊢; omega)

/-- `maxidx` after the entry's stores. -/
theorem ent_m (hT : Te F Wl L fb g₀ V₀) {W : Addr → Byte} :
    (ofBytesLE 32 (List.map (Vst W (fr g₀.rsp + 12#64) (toBytesLE (1#32) 4))
      (byteAddrs (fr g₀.rsp + 12#64) 4))).toNat ≤ 255 := by
  have lo := hT.lo
  have hi := hT.hi
  have e12 := tc 12 (t_fr _ lo) (by omega)
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (w := 32) (n := 4) rfl]
  decide

/-- The canary at the end is the one at the start. -/
theorem canary (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = Vh fb g₀ V₀ a) :
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 24#64) 8)) =
      ofBytesLE 64 (List.map V (byteAddrs (fb + 40#64) 8)) := by
  have lo := hT.lo
  have hi := hT.hi
  have cf := hT.cnf
  have ca := hT.cna
  have e24 := tc 24 (t_fr _ lo) (by omega)
  rw [rdM hm (fr g₀.rsp + 24#64) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (fb + 40#64) 8 cf (fun y h1 h2 => by unfold On; omega)]
  dsimp only [Vh]
  rw [Tun.rd_Vst_self _ (fr g₀.rsp + 24#64) _ (toBytesLE_length _ _) (by omega),
    ofBytesLE_toBytesLE (w := 64) (n := 8) rfl,
    Tun.rd_Vst _ (fr g₀.rsp + 24#64) _ (fb + 40#64) 8 (by rw [toBytesLE_length]; omega) cf
      (by rw [toBytesLE_length]; omega)]

/-- The six `pop`s. -/
theorem pops (hT : Te F Wl L fb g₀ V₀) (hm : ∀ a, Out g₀.rsp a → V a = Vh fb g₀ V₀ a) :
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64) 8)) = g₀.rbx ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64 + 8) 8)) = g₀.rbp ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64 + 8 + 8) 8)) = g₀.r12 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64 + 8 + 8 + 8) 8)) = g₀.r13 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64 + 8 + 8 + 8 + 8) 8)) = g₀.r14 ∧
    ofBytesLE 64 (List.map V (byteAddrs (fr g₀.rsp + 40#64 + 8 + 8 + 8 + 8 + 8) 8)) = g₀.r15 := by
  have lo := hT.lo
  have hi := hT.hi
  have e1 := p_1 _ lo
  have e2 := p_2 _ lo
  have e3 := p_3 _ lo
  have e4 := p_4 _ lo
  have e5 := p_5 _ lo
  have e6 := p_6 _ lo
  have e24 := tc 24 (t_fr _ lo) (by omega)
  have b := fun k => ofBytesLE_toBytesLE (w := 64) (n := 8) rfl k
  have hv : ∀ x : Addr, (fr g₀.rsp + 24#64).toNat + 8 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
      List.map (Vh fb g₀ V₀) (byteAddrs x 8) = List.map (P6 g₀ V₀) (byteAddrs x 8) := fun x h1 h2 =>
    Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) h2 (Or.inl (by rw [toBytesLE_length]; exact h1))
  obtain ⟨-, q6, q5, q4, q3, q2, q1⟩ := q_all _ lo
  rw [q6, q5, q4, q3, q2, q1]
  rw [rdM hm (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8 - 8 - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8 - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (g₀.rsp - 8 - 8 - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (g₀.rsp - 8 - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    rdM hm (g₀.rsp - 8) 8 (by omega) (fun y h1 h2 => by unfold On; omega),
    hv (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (by omega) (by omega), hv (g₀.rsp - 8 - 8 - 8 - 8 - 8) (by omega) (by omega),
    hv (g₀.rsp - 8 - 8 - 8 - 8) (by omega) (by omega), hv (g₀.rsp - 8 - 8 - 8) (by omega) (by omega),
    hv (g₀.rsp - 8 - 8) (by omega) (by omega), hv (g₀.rsp - 8) (by omega) (by omega)]
  dsimp only [P6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact b _

/-! ## The calls of `intel_check_word` -/

/-- `intel_check_word`'s contract at a call: its frame and return address's slot are the 40 bytes below `fr`. -/
theorem te_mk (hT : Te F Wl L fb g₀ V₀) {g : Gprs} {W : Addr → Byte}
    (hd : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64) (hs : g.rsp = fr g₀.rsp - 8)
    (hcx : g.rcx = fr g₀.rsp + 22#64) (hdx : g.rdx = fr g₀.rsp + 23#64)
    (h8 : g.r8 = 8014676#64 + 18446744073709551612#64) (h9 : g.r9 = 8014676#64)
    (hr : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
      ofBytesLE 64 (List.map W (byteAddrs (fr g₀.rsp - 8) 8)) = e₂.add j₂) :
    Icw.Te F Wl L g W := by
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e1 := ts8 e0 (by omega)
  have e2 := ts8 e1 (by omega)
  have e3 := ts8 e2 (by omega)
  have e4 := ts8 e3 (by omega)
  have e5 := ts8 e4 (by omega)
  have e22 := tc 22 e0 (by omega)
  have e23 := tc 23 e0 (by omega)
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT.tab, ?_⟩
  · rw [hs]; exact fW hT (by omega) (by omega)
  · rw [hs]; exact fD hT (by omega) (by omega)
  · rw [hs]; omega
  · rw [hs]; omega
  · rw [hdx]; exact fW hT (by omega) (by omega)
  · rw [hcx]; exact fW hT (by omega) (by omega)
  · rw [hs, hdx]; omega
  · rw [hs, hcx]; omega
  · rw [h8, r8e]; exact hT.fam
  · rw [h9]; exact hT.mdl
  · rw [hs]; exact hr

/-- After `intel_check_word`: the bytes out of its frame and return address's slot, but for the two flags. -/
theorem keep_v {g' : Gprs} {V V' : Addr → Byte} {S : Addr} (h128 : 128 ≤ S.toNat) (hs : g'.rsp = fr S - 8)
    (hdx : g'.rdx = fr S + 23#64) (hcx : g'.rcx = fr S + 22#64) (bs : List Byte) (hb : bs.length = 8)
    (hK : Icw.Keep g' (Vst V (fr S - 8) bs) V') (a : Addr)
    (h1 : a.toNat + 128 < S.toNat ∨ S.toNat ≤ a.toNat + 88) (h2 : a.toNat + 66 ≠ S.toNat)
    (h3 : a.toNat + 65 ≠ S.toNat) : V' a = V a := by
  have hi := S.isLt
  have e0 := t_fr _ h128
  have e1 := ts8 e0 (by omega)
  have e22 := tc 22 e0 (by omega)
  have e23 := tc 23 e0 (by omega)
  rw [hK a (by rw [hs]; omega) (fun e => by rw [hdx] at e; have := congrArg BitVec.toNat e; omega)
      (fun e => by rw [hcx] at e; have := congrArg BitVec.toNat e; omega),
    Tun.Vst_out _ _ _ _ (by rw [hb]; omega) (by rw [hb]; omega)]

/-- A call of `intel_check_word` from the loop, to the instruction after it. -/
theorem call_vc (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) {j : Nat} (hj : j < hca.length)
    (h : Lp fb g₀ V₀ g V) (hc : Ca g₀ g) {Q : Post}
    (hQ : ∀ g' V', Lp fb g₀ V₀ g' V' → g'.r14 = g.r14 → ∀ fl, Q j g' fl V') :
    CallK Wl hca_at j (Icw.Te F Wl L) Icw.Rh Q g f V := by
  obtain ⟨⟨hs, hm⟩, hb, h12, h13, h14, hM⟩ := h
  obtain ⟨hd, hcx, hdx, h8, h9⟩ := hc
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr _ lo
  have e1 := ts8 e0 (by omega)
  have e12 := tc 12 e0 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs]; exact fW hT (by omega) (by omega)
  · rw [hs]; omega
  · rw [hs]
    refine te_mk hT hd rfl hcx hdx h8 h9 ⟨hca_at, hca, j, hin, hj, ?_⟩
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hs]
    intro g' V' hR fl
    obtain ⟨hs', -, hp', h12', h13', h14', -, hK⟩ := hR
    have kv := keep_v (g' := g.set 4 (fr g₀.rsp - 8)) lo rfl hdx hcx _ (toBytesLE_length _ _) hK
    refine hQ g' V' ⟨⟨hs'.trans (sa8 _), fun a ha => ?_⟩, by rw [hp']; exact hb, h12'.trans h12, h13'.trans h13,
      by rw [h14']; exact h14, ?_⟩ h14' fl
    · have ha' := ha
      unfold Out On at ha'
      exact (kv a (by omega) (by omega) (by omega)).trans (hm a ha)
    · rw [show List.map V' (byteAddrs (fr g₀.rsp + 12#64) 4) = List.map V (byteAddrs (fr g₀.rsp + 12#64) 4) from
        List.map_congr_left fun y hy => by
          obtain ⟨k, hk, rfl⟩ := mem_byteAddrs.1 hy
          have e := toNat_add_of_fits (a := fr g₀.rsp + 12#64) hk (by omega)
          exact kv _ (by omega) (by omega) (by omega)]
      exact hM

/-! ## After `cpuid` -/

theorem cp_r14 {cpu : Nat} : (cpuidG prof cpu g).r14 = g.r14 := by cases g; rfl
theorem cp_lp {cpu : Nat} (h : Lp fb g₀ V₀ g V) : Lp fb g₀ V₀ (cpuidG prof cpu g) V := by cases g; exact h

end FV7z.Hin
