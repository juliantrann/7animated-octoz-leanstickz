import FV7z.Icw.Cuts
import FV7z.Hca.Holds
import FV7z.Spec.Cache
/-!
# `intel_check_word`: the contract and the invariants of its cut points (PLAN.md M, ctor 103)

glibc's `intel_check_word (name, value, &has_level_2, &no_level_2_or_3, cpu_features)` at `0x65cce0` in `7zzs`
(offset 464 of the `Hca` code, `sysdeps/x86/cacheinfo.c`), as `handle_intel` calls it: `name` one of
`_SC_LEVEL1_DCACHE_SIZE` (188), `_SC_LEVEL2_CACHE_SIZE` (191), `_SC_LEVEL3_CACHE_SIZE` (194), `value` (`esi`) a
register of `cpuid(2)`, `rdx` and `rcx` the two flags, `r8` and `r9` the processor's family and model (the compiler
passes their addresses). It walks the bytes of `value`: a byte `0xff` sends it to `cpuid` leaf 4, whose subleaves it
walks until one has type 0; other bytes are looked up (binary search) in `intel_02_known` (`0x6f2140`, 68 entries of
8 bytes).

`Te` is what it needs at its entry, `Rh` what holds at its return address: `rsp` 8 up, `rbx`, `rbp`, `r12`–`r15` as at
the entry, and the bytes as at the entry but for its frame (32 bytes below the return address) and the two flags.

The invariants (`Ih`), with a measure that goes down along every edge:

- the byte loop (567, 558, 630, 752, 682): `1000 · (value + 1) + c`; `shr esi, 8` with `ZF` clear makes `value`
  smaller (`Op.shr32z`);
- the binary search (640, 656): `8 · (rdx - r10)`, with `r10 ≤ rax < rdx ≤ 68`;
- leaf 4 (821–1260): `10 · (64 - subleaf) + c`; the subleaf stays below 64 by H-CPU-cache (`Glibc.CacheEnds`): a
  subleaf from 64 on has type 0.

`name` and the folded name (`r9`) are one of three pairs (`RD`), so the offset `name - folded` is 0 and the two
`__assert_fail` calls (1085, 1116) and the instruction-cache path (`r9 = 0`, 1152) are not reached.
-/
namespace FV7z.Icw
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length lt_len pcp pcp_0 prt prt_0 ad8)

/-! ## The `cpuid`s and `ret`s -/

theorem wcp773 : pcp <+: hca.drop 773 := by decide +kernel
theorem wcp829 : pcp <+: hca.drop 829 := by decide +kernel
theorem wcp1258 : pcp <+: hca.drop 1258 := by decide +kernel
theorem cpuid_773 (feat : Features) : Dec feat hca 773 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 773) (k := 0) (pcp_0 feat) wcp773 (Nat.zero_le _)
theorem cpuid_829 (feat : Features) : Dec feat hca 829 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 829) (k := 0) (pcp_0 feat) wcp829 (Nat.zero_le _)
theorem cpuid_1258 (feat : Features) : Dec feat hca 1258 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 1258) (k := 0) (pcp_0 feat) wcp1258 (Nat.zero_le _)

theorem wr729 : prt <+: hca.drop 729 := by decide +kernel
theorem wr765 : prt <+: hca.drop 765 := by decide +kernel

/-- The two `ret`s. -/
theorem ret_at (feat : Features) {j : Nat} (hj : j = 729 ∨ j = 765) :
    j < hca.length ∧ Dec feat hca j (FV7z.mk .ret 64 [] 1) := by
  rcases hj with rfl | rfl
  · exact ⟨lt_len (by decide), Dec.shift (j := 729) (k := 0) (prt_0 feat) wr729 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 765) (k := 0) (prt_0 feat) wr765 (Nat.zero_le _)⟩

/-- The entry. -/
abbrev icw_at : Addr := 0x65cce0
theorem icw_at_eq : Addr.add hca_at 464 = icw_at := by decide

/-! ## The contract -/

/-- What `intel_check_word` needs at its entry (`rsp` at the return address). -/
structure Te (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (g : Gprs) (V : Addr → Byte) : Prop where
  rdi : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64
  /-- The four saved registers' slots. -/
  st : ∀ i < 32, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)
  /-- The saved registers' slots and the return address. -/
  ld : ∀ i < 40, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)
  lo : 32 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  /-- `has_level_2` and `no_level_2_or_3`: one byte each, above the return address. -/
  p2 : ∀ i < 1, Foot Wl (Addr.add g.rdx i)
  p3 : ∀ i < 1, Foot Wl (Addr.add g.rcx i)
  p2a : g.rsp.toNat + 8 ≤ g.rdx.toNat
  p3a : g.rsp.toNat + 8 ≤ g.rcx.toNat
  /-- The family and the model. -/
  fam : ∀ i < 4, Foot F.data (Addr.add g.r8 i)
  mdl : ∀ i < 4, Foot F.data (Addr.add g.r9 i)
  /-- `intel_02_known`. -/
  tab : ∀ x : Addr, 7283008 ≤ x.toNat → x.toNat < 7283008 + 544 → Foot F.data x
  ret : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
    ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)) = e₂.add j₂

/-- The bytes after the four `push`es. -/
abbrev Vp (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r13 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.r12 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8)) (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- The bytes as at the entry but for the frame and the two flags. -/
def Keep (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ a : Addr, (a.toNat + 32 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) → a ≠ g₀.rdx → a ≠ g₀.rcx → V a = V₀ a

/-- At the return address. -/
def Rh (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15 ∧ Keep g₀ V₀ V

/-! ## The invariants -/

/-- Between the `push`es and the `pop`s. -/
def Mid (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8#64 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧
    ∀ a, a ≠ g₀.rdx → a ≠ g₀.rcx → V a = Vp g₀ V₀ a

/-- The byte loop's registers: the flags' addresses, the family's and model's, the table. -/
def Bq (g₀ g : Gprs) : Prop :=
  g.rbx = g₀.rdx ∧ g.rbp = g₀.rcx ∧ g.r12 = g₀.r8 ∧ g.r13 = g₀.r9 ∧ g.r8 = 7283008#64

/-- `name` and the folded name. -/
abbrev RD (d r : BitVec 64) : Prop := d = 188#64 ∧ r = 3#64 ∨ d = 191#64 ∧ r = 6#64 ∨ d = 194#64 ∧ r = 9#64

/-- In the byte loop. -/
def By (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  Mid g₀ V₀ g V ∧ Bq g₀ g ∧ RD g.rdi g.r9

/-- In leaf 4's loop for `r9` 6 or 9 (`r10d` the leaf). -/
def Lk (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  Mid g₀ V₀ g V ∧ RD g.rdi g.r9 ∧ g.r10.setWidth 32 = 4#32

/-- In leaf 4's loop for `r9` 3 (`r8d` the leaf). -/
def Lt (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  Mid g₀ V₀ g V ∧ RD g.rdi g.r9 ∧ g.r8.setWidth 32 = 4#32

/-- The invariants of the cut points, with the measure `n`. -/
def Ih (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  if ℓ = 464 then n = 1000 * 4294967296 + 2000 ∧ g = g₀ ∧ V = V₀ else
  if ℓ = 567 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 900 ∧ By g₀ V₀ g V else
  if ℓ = 752 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 800 ∧ By g₀ V₀ g V ∧ g.rdi = 194#64 else
  if ℓ = 630 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 700 ∧ By g₀ V₀ g V else
  if ℓ = 640 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 14 + 8 * (g.rdx.toNat - g.r10.toNat) ∧
    By g₀ V₀ g V ∧ g.r10.toNat < g.rdx.toNat ∧ g.rdx.toNat ≤ 68 else
  if ℓ = 656 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 10 + 8 * (g.rdx.toNat - g.r10.toNat) ∧
    By g₀ V₀ g V ∧ g.r10.toNat ≤ g.rax.toNat ∧ g.rax.toNat < g.rdx.toNat ∧ g.rdx.toNat ≤ 68 else
  if ℓ = 682 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 5 ∧ By g₀ V₀ g V ∧
    ∃ k, k < 68 ∧ g.r11.toNat = 7283008 + 8 * k else
  if ℓ = 558 then n = 1000 * ((g.rsi.setWidth 32).toNat + 1) + 1 ∧ By g₀ V₀ g V else
  if ℓ = 773 then n = 995 ∧ Mid g₀ V₀ g V ∧ RD g.rdi g.r9 else
  if ℓ = 775 then n = 990 ∧ Mid g₀ V₀ g V ∧ RD g.rdi g.r9 else
  if ℓ = 829 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 9 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat ≤ 64 ∧
    g.rax.setWidth 32 = 4#32 ∧ g.rcx.setWidth 32 = g.rsi.setWidth 32 else
  if ℓ = 831 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 8 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat ≤ 64 ∧
    ((g.rax.setWidth 32 &&& 31#32 == 0) = false → (g.rsi.setWidth 32).toNat < 64) else
  if ℓ = 838 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 7 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 856 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 6 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 866 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 5 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 1033 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 4 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 1048 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 3 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 821 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 1 ∧ Lk g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 885 then n = 3 ∧ Mid g₀ V₀ g V ∧ RD g.rdi g.r9 else
  if ℓ = 1258 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 9 ∧ Lt g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat ≤ 64 ∧
    g.rax.setWidth 32 = 4#32 ∧ g.rcx.setWidth 32 = g.rsi.setWidth 32 else
  if ℓ = 1260 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 8 ∧ Lt g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat ≤ 64 ∧
    ((!(g.rax.setWidth 32 &&& 31#32 == 0)) = true → (g.rsi.setWidth 32).toNat < 64) else
  if ℓ = 1230 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 7 ∧ Lt g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 1250 then n = 10 * (64 - (g.rsi.setWidth 32).toNat) + 6 ∧ Lt g₀ V₀ g V ∧ (g.rsi.setWidth 32).toNat < 64 else
  if ℓ = 717 then n = 2 ∧ Mid g₀ V₀ g V else
  if ℓ = 719 then n = 1 ∧ Mid g₀ V₀ g V else
  False

/-- At a `ret`. -/
def Fh (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (j = 729 ∨ j = 765) ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧
    g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧ Keep g₀ V₀ V

/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ Ih g₀ V₀ j' n' g' V') ∨ Fh g₀ V₀ j' g' V'

/-- What the code from a cut point needs for `Q` at the next ones: at a `cpuid`, `Q` after it on every CPU. -/
def WtC (prof : Profile) (F : Footprint) (Wl : List Rgn) (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 773 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 775 (cpuidG prof cpu g) fl V else
  if ℓ = 829 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 831 (cpuidG prof cpu g) fl V else
  if ℓ = 1258 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 1260 (cpuidG prof cpu g) fl V else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-- The cut points' pieces in a run with the code. -/
theorem spC (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hca_at hca) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o hca_at ℓ (WtC prof F Wl ℓ) := by
  unfold WtC
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_773 _)
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_829 _)
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_1258 _)
  exact (spAll prof ℓ).at c hin

/-! ## Arithmetic -/

theorem ad_8 (s : Addr) (i : Nat) : Addr.add (s - 8 - 8 - 8 - 8) (8 + i) = Addr.add (s - 8 - 8 - 8) i := ad8 _ _
theorem ad_16 (s : Addr) (i : Nat) : Addr.add (s - 8 - 8 - 8 - 8) (8 + (8 + i)) = Addr.add (s - 8 - 8) i := by
  rw [ad8, ad8]
theorem ad_24 (s : Addr) (i : Nat) : Addr.add (s - 8 - 8 - 8 - 8) (8 + (8 + (8 + i))) = Addr.add (s - 8) i := by
  rw [ad8, ad8, ad8]
theorem ad_32 (s : Addr) (i : Nat) : Addr.add (s - 8 - 8 - 8 - 8) (8 + (8 + (8 + (8 + i)))) = Addr.add s i := by
  rw [ad8, ad8, ad8, ad8]

/-- The four saved registers' slots, one by one. -/
theorem st4 {R : List Rgn} {s : Addr} (h : ∀ i < 32, Foot R (Addr.add (s - 8 - 8 - 8 - 8) i)) :
    (∀ i < 8, Foot R (Addr.add (s - 8) i)) ∧ (∀ i < 8, Foot R (Addr.add (s - 8 - 8) i)) ∧
      (∀ i < 8, Foot R (Addr.add (s - 8 - 8 - 8) i)) ∧ (∀ i < 8, Foot R (Addr.add (s - 8 - 8 - 8 - 8) i)) :=
  ⟨fun i hi => by have := h (8 + (8 + (8 + i))) (by omega); rwa [ad_24] at this,
   fun i hi => by have := h (8 + (8 + i)) (by omega); rwa [ad_16] at this,
   fun i hi => by have := h (8 + i) (by omega); rwa [ad_8] at this,
   fun i hi => h i (by omega)⟩

/-- The saved registers' slots and the return address, one by one. -/
theorem ld5 {R : List Rgn} {s : Addr} (h : ∀ i < 40, Foot R (Addr.add (s - 8 - 8 - 8 - 8) i)) :
    (∀ i < 8, Foot R (Addr.add (s - 8 - 8 - 8 - 8) i)) ∧ (∀ i < 8, Foot R (Addr.add (s - 8 - 8 - 8) i)) ∧
      (∀ i < 8, Foot R (Addr.add (s - 8 - 8) i)) ∧ (∀ i < 8, Foot R (Addr.add (s - 8) i)) ∧
        (∀ i < 8, Foot R (Addr.add s i)) :=
  ⟨fun i hi => h i (by omega),
   fun i hi => by have := h (8 + i) (by omega); rwa [ad_8] at this,
   fun i hi => by have := h (8 + (8 + i)) (by omega); rwa [ad_16] at this,
   fun i hi => by have := h (8 + (8 + (8 + i))) (by omega); rwa [ad_24] at this,
   fun i hi => by have := h (8 + (8 + (8 + (8 + i)))) (by omega); rwa [ad_32] at this⟩

theorem s_1 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem s_2 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem s_3 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem s_4 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega

theorem xs (x : BitVec 32) : (BitVec.setWidth 32 (BitVec.setWidth 64 (x ^^^ x))).toNat = 0 := by simp
theorem xz (x : BitVec 32) : (BitVec.setWidth 64 (x ^^^ x)).toNat = 0 := by simp
theorem x68 : (BitVec.setWidth 64 68#32).toNat = 68 := by decide
theorem inc32 (x : BitVec 32) (h : x.toNat < 64) : (x + 1#32).toNat = x.toNat + 1 := by bv_omega
theorem inc64 (x : BitVec 64) (h : x.toNat < 68) : (x + 1#64).toNat = x.toNat + 1 := by bv_omega

theorem xx (x : BitVec 32) : (x ^^^ x).toNat = 0 := by simp
theorem sw9 : BitVec.setWidth 64 9#32 = 9#64 := by decide

/-- The measure at the entry is above the byte loop's. -/
theorem m464 (x : BitVec 32) : 1000 * (x.toNat + 1) + 900 < 1000 * 4294967296 + 2000 := by
  have h : x.toNat < 4294967296 := x.isLt
  omega

/-- `(!b) = true`. -/
theorem nt {b : Bool} (h : (!b) = true) : b = false := by
  revert h
  cases b <;> decide

/-- A measure goal: the registers' literal projected out, then `omega`. -/
macro "icw_om" : tactic =>
  `(tactic| ((try dsimp only) <;> (try simp only [sw_64_32, xx, xz, x68]) <;> omega))

/-- `name` and the folded name: `r9` 9 means `name` 194. -/
theorem r194 {d r : BitVec 64} (h : RD d r) (h9 : (!decide (BitVec.setWidth 32 r = 9#32)) = false) : d = 194#64 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | rfl | exact absurd h9 (by decide)

/-- At `621` (`sub edi, 3; mov r9d, 6`) from `r9` 9. -/
theorem r621 {d r : BitVec 64} (h : RD d r) (h9 : (!decide (BitVec.setWidth 32 r = 9#32)) = false) :
    RD (BitVec.setWidth 64 (BitVec.setWidth 32 d - 3#32)) (BitVec.setWidth 64 6#32) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact absurd h9 (by decide) | decide

/-- `(name - 185) / 3`, as the code computes it (`imul` by `0x55555556`, the high half, the sign). -/
def q3 (d : BitVec 64) : BitVec 32 :=
  BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 128
      (BitVec.signExtend 64 (BitVec.setWidth 32 (d + 18446744073709551431#64))) *
    BitVec.signExtend 128 1431655766#64) >>> 32) -
  (BitVec.setWidth 32 (d + 18446744073709551431#64)).sshiftRight 31

/-- The folded name: `3 · q3`. -/
def fold3 (d : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (q3 d) + BitVec.setWidth 64 (q3 d) * 2#64))

theorem rd464 {d : BitVec 64} (h : d = 188#64 ∨ d = 191#64 ∨ d = 194#64) : RD d (fold3 d) := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- The binary search's middle. -/
theorem mid1 (a b : BitVec 64) (ha : a.toNat < b.toNat) (hb : b.toNat ≤ 68) :
    a.toNat ≤ ((a + b) >>> 1).toNat ∧ ((a + b) >>> 1).toNat < b.toNat := by
  constructor <;> bv_omega

/-- An entry of the table. -/
theorem ix1 (y : BitVec 64) (hy : y.toNat < 68) : (7283008#64 + y * 8#64).toNat = 7283008 + 8 * y.toNat := by
  bv_omega

theorem ixc (r : BitVec 64) (c : Nat) (hc : c < 8) (hr : r.toNat < 4294967296) :
    (r + BitVec.ofNat 64 c).toNat = r.toNat + c := by
  bv_omega

theorem orf {a b : BitVec 64} (h : (decide (a.toNat < b.toNat) || decide (a = b)) = false) : b.toNat < a.toNat := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨h1, h2⟩ := h
  have : a.toNat ≠ b.toNat := fun e => h2 (BitVec.eq_of_toNat_eq e)
  omega

/-- `shr x, 8` with `ZF` clear: smaller. -/
theorem shr8_lt {fl : Rflags} (x : BitVec 32) (hz : fl.zf = (x >>> 8 == 0)) (h : fl.zf = false) :
    (x >>> 8).toNat < x.toNat := by
  rw [h] at hz
  have hne : x >>> 8 ≠ 0#32 := by
    intro e
    rw [e] at hz
    exact absurd hz (by decide)
  have e8 : (x >>> 8).toNat = x.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    try rfl
  have h1 : (x >>> 8).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq (e.trans rfl))
  omega

/-- The byte loop's measure after `shr esi, 8` with `ZF` clear. -/
theorem m_shr {fl : Rflags} (x : BitVec 32) (hz : fl.zf = (x >>> 8 == 0)) (h : fl.zf = false) (c d : Nat)
    (hc : c < 1000 + d) :
    1000 * ((BitVec.setWidth 32 (BitVec.setWidth 64 (x >>> 8))).toNat + 1) + c < 1000 * (x.toNat + 1) + d := by
  rw [sw_64_32]
  have := shr8_lt x hz h
  omega

/-- Below 64 when leaf 4 reports a cache (H-CPU-cache). -/
theorem cache_lt (hC : Glibc.CacheEnds prof) {cpu : Nat} (hc : cpu < max prof.cpus 1) (sub : BitVec 32)
    (h : (prof.cpuid cpu 4#32 sub).eax &&& 31#32 ≠ 0#32) : sub.toNat < 64 := by
  apply Classical.byContradiction
  intro h'
  exact h (hC.leaf4 cpu hc sub (by omega))

/-! ## Bytes -/

theorem st1 {p q b : Addr} {V W : Addr → Byte} (hV : ∀ a, a ≠ p → a ≠ q → V a = W a) (hb : b = p ∨ b = q)
    (x : BitVec 8) : ∀ a, a ≠ p → a ≠ q → Vst V b (toBytesLE x 1) a = W a := by
  intro a h1 h2
  rw [Vst_apart _ _ _ _ fun i hi e => ?_]
  · exact hV a h1 h2
  · have hi0 : i = 0 := by simp [toBytesLE_length] at hi; omega
    subst hi0
    rw [addr_add_zero] at e
    rcases hb with rfl | rfl
    · exact h1 e
    · exact h2 e

/-- The bytes of `Vp` outside the frame are those at the entry. -/
theorem Vp_out (hT : Te F Wl L g₀ V₀) (a : Addr) (h : a.toNat + 32 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ a.toNat) :
    Vp g₀ V₀ a = V₀ a := by
  have lo := hT.lo
  have hi := hT.hi
  have e1 := s_1 _ lo
  have e2 := s_2 _ lo
  have e3 := s_3 _ lo
  have e4 := s_4 _ lo
  dsimp only [Vp]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- A load in the frame or of the return address: the flags are not there. -/
theorem rd_np (hT : Te F Wl L g₀ V₀) {V W : Addr → Byte} (hV : ∀ a, a ≠ g₀.rdx → a ≠ g₀.rcx → V a = W a)
    (x : Addr) (hx : x.toNat ≤ g₀.rsp.toNat) : List.map V (byteAddrs x 8) = List.map W (byteAddrs x 8) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have p2 := hT.p2a
  have p3 := hT.p3a
  have hi := hT.hi
  have e := toNat_add_of_fits (a := x) hj (by omega)
  refine hV _ (fun h => ?_) (fun h => ?_)
  · have := congrArg BitVec.toNat h; omega
  · have := congrArg BitVec.toNat h; omega

/-- The four `pop`s. -/
theorem pops (hT : Te F Wl L g₀ V₀) (hV : ∀ a, a ≠ g₀.rdx → a ≠ g₀.rcx → V a = Vp g₀ V₀ a) :
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8 - 8 - 8 - 8) 8)) = g₀.rbx ∧
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8 - 8 - 8) 8)) = g₀.rbp ∧
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8 - 8) 8)) = g₀.r12 ∧
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8) 8)) = g₀.r13 := by
  have lo := hT.lo
  have hi := hT.hi
  have e1 := s_1 _ lo
  have e2 := s_2 _ lo
  have e3 := s_3 _ lo
  have e4 := s_4 _ lo
  have b := fun k => ofBytesLE_toBytesLE (w := 64) (n := 8) rfl k
  have hV' : ∀ x : Addr, x.toNat ≤ g₀.rsp.toNat →
      List.map V (byteAddrs x 8) = List.map (Vp g₀ V₀) (byteAddrs x 8) := rd_np hT hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hV' _ (by omega)]
    dsimp only [Vp]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e4]; omega)]
    exact b _
  · rw [hV' _ (by omega)]
    dsimp only [Vp]
    rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [e3]; omega)
        (Or.inl (by rw [toBytesLE_length, e4, e3]; omega)),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e3]; omega)]
    exact b _
  · rw [hV' _ (by omega)]
    dsimp only [Vp]
    rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [e2]; omega)
        (Or.inl (by rw [toBytesLE_length, e4, e2]; omega)),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [e2]; omega)
        (Or.inl (by rw [toBytesLE_length, e3, e2]; omega)),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e2]; omega)]
    exact b _
  · rw [hV' _ (by omega)]
    dsimp only [Vp]
    rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [e1]; omega)
        (Or.inl (by rw [toBytesLE_length, e4, e1]; omega)),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [e1]; omega)
        (Or.inl (by rw [toBytesLE_length, e3, e1]; omega)),
      Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [e1]; omega)
        (Or.inl (by rw [toBytesLE_length, e2, e1]; omega)),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e1]; omega)]
    exact b _

/-- From `Mid`'s bytes to `Keep`. -/
theorem keep_of (hT : Te F Wl L g₀ V₀) (hV : ∀ a, a ≠ g₀.rdx → a ≠ g₀.rcx → V a = Vp g₀ V₀ a) : Keep g₀ V₀ V :=
  fun a h h2 h3 => (hV a h2 h3).trans (Vp_out hT a h)

/-- The return address after the run. -/
theorem rd_keep (hT : Te F Wl L g₀ V₀) (hK : Keep g₀ V₀ V) :
    List.map V (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have p2 := hT.p2a
  have p3 := hT.p3a
  have hi := hT.hi
  have e := toNat_add_of_fits (a := g₀.rsp) hj (by omega)
  refine hK _ (Or.inr (by omega)) (fun h => ?_) (fun h => ?_)
  · have := congrArg BitVec.toNat h; omega
  · have := congrArg BitVec.toNat h; omega

/-- The table's bytes may be read. -/
theorem tabB (hT : Te F Wl L g₀ V₀) (x : Addr) (m : Nat) (h1 : 7283008 ≤ x.toNat) (h2 : x.toNat + m ≤ 7283008 + 544) :
    ∀ i < m, Foot F.data (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact hT.tab _ (by omega) (by omega)

/-! ## After `cpuid` -/

theorem cp_rsi {cpu : Nat} : (cpuidG prof cpu g).rsi = g.rsi := by cases g; rfl
theorem cp_rax {cpu : Nat} :
    (cpuidG prof cpu g).rax = (prof.cpuid cpu (g.rax.setWidth 32) (g.rcx.setWidth 32)).eax.setWidth 64 := by
  cases g; rfl
theorem cp_mid {cpu : Nat} (h : Mid g₀ V₀ g V) : Mid g₀ V₀ (cpuidG prof cpu g) V := by cases g; exact h
theorem cp_rd {cpu : Nat} (h : RD g.rdi g.r9) : RD (cpuidG prof cpu g).rdi (cpuidG prof cpu g).r9 := by
  cases g; exact h
theorem cp_lk {cpu : Nat} (h : Lk g₀ V₀ g V) : Lk g₀ V₀ (cpuidG prof cpu g) V := by cases g; exact h
theorem cp_lt {cpu : Nat} (h : Lt g₀ V₀ g V) : Lt g₀ V₀ (cpuidG prof cpu g) V := by cases g; exact h

/-- Leaf 4's type after `cpuid` with `eax` 4 and `ecx` the subleaf. -/
theorem cp_type (hC : Glibc.CacheEnds prof) {cpu : Nat} (hc : cpu < max prof.cpus 1)
    (hax : g.rax.setWidth 32 = 4#32) (hcx : g.rcx.setWidth 32 = g.rsi.setWidth 32) :
    (cpuidG prof cpu g).rax.setWidth 32 &&& 31#32 ≠ 0#32 → (g.rsi.setWidth 32).toNat < 64 := by
  rw [cp_rax, sw_64_32, hax, hcx]
  exact cache_lt hC hc _

end FV7z.Icw
