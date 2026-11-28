import FV7z.Av2.Cuts
import FV7z.Gdt.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
/-!
# `CPU_IsSupported_AVX2 ()` (PLAN.md §M, M1)

7-Zip 26.06's `CPU_IsSupported_AVX2 ()` at `0x4244b0` in `7zzs` (`C/CpuArch.c`), `S` the entry's `rsp`: a frame of
40 bytes with the stack guard (`fs:0x28`) at `S - 16` (as `FV7z/Gdt/Holds.lean`: `Gdt.dV1`), the OS test (`call` at
24 to `0x424440`); back at 29, if its `eax` is 0, `eax` = 0 (33); else `z7_x86_cpuid_GetMaxFunc ()` (`call` at 64
to `0x4242b0`), back at 69 `cmp eax, 6; jbe` to 33; else `z7_x86_cpuid (a, 7)` (`call` at 82 to `0x424290`, `rdi`
the frame, `esi` 7), back at 87 `eax` = bit 5 of `a[1]` (the 4 bytes at `S - 36`), `jmp` to 35. At 35 the guard's
check (`jne` to the `call __stack_chk_fail` at 99), `add rsp, 40`, the `ret` (55).

The callees are hypotheses, as in `FV7z/Sse/Holds.lean` (`kf1`, `kf2`, `kf3`): each a continuation at its entry,
given the run from its return (`rsp` as at the `call`, the guard and the return address left as they were, its own
post `Pc1`, `Pc2`, `Pc3`); the run reaches the return address with `rax` 0 (`kr1`, `kr2`) or `abit` (`kr3`).

- `ag1`, `ag3`: the registers at the first and the third `call` (the second's are the first's return's); `abit`:
  the answer of the third, from the bytes at the frame `s`.
- `le_jbe`, `gt_jbe`: the flags of `cmp eax, 6` for the `jbe`.
- `vc_0`, `vc_29z`, `vc_29n`, `vc_33`, `vc_35`, `vc_69`, `vc_87`: the pieces from their offsets.
- `fin35`, `fin33`: from 35 (from 33, `eax` 0) to the return address.
- `av2_ok`: through the callees to the return address, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Av2

/-- The OS test. -/
abbrev os_at : Addr := 0x424440

/-- `z7_x86_cpuid_GetMaxFunc`. -/
abbrev max_at : Addr := 0x4242b0

/-- `z7_x86_cpuid`. -/
abbrev cpuid_at : Addr := 0x424290

/-- The first `call`. -/
def pc1 : List Byte := [0xe8, 0x73, 0xff, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709551475] 5) := by dec_rfl
theorem wc_24 : pc1 <+: av2.drop 24 := by decide +kernel
theorem call_24 (feat : Features) : Dec feat av2 24 (FV7z.mk .call 64 [.rel 18446744073709551475] 5) :=
  Dec.shift (j := 24) (k := 0) (pc1_0 feat) wc_24 (Nat.zero_le _)
theorem tgt_24 : av2_at.add (24 + 5) + BitVec.ofNat 64 18446744073709551475 = os_at := by decide

/-- The second `call`. -/
def pc2 : List Byte := [0xe8, 0xbb, 0xfd, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709551035] 5) := by dec_rfl
theorem wc_64 : pc2 <+: av2.drop 64 := by decide +kernel
theorem call_64 (feat : Features) : Dec feat av2 64 (FV7z.mk .call 64 [.rel 18446744073709551035] 5) :=
  Dec.shift (j := 64) (k := 0) (pc2_0 feat) wc_64 (Nat.zero_le _)
theorem tgt_64 : av2_at.add (64 + 5) + BitVec.ofNat 64 18446744073709551035 = max_at := by decide

/-- The third `call`. -/
def pc3 : List Byte := [0xe8, 0x89, 0xfd, 0xff, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073709550985] 5) := by dec_rfl
theorem wc_82 : pc3 <+: av2.drop 82 := by decide +kernel
theorem call_82 (feat : Features) : Dec feat av2 82 (FV7z.mk .call 64 [.rel 18446744073709550985] 5) :=
  Dec.shift (j := 82) (k := 0) (pc3_0 feat) wc_82 (Nat.zero_le _)
theorem tgt_82 : av2_at.add (82 + 5) + BitVec.ofNat 64 18446744073709550985 = cpuid_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_55 : pret <+: av2.drop 55 := by decide +kernel
theorem ret_55 (feat : Features) : Dec feat av2 55 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 55) (k := 0) (pret_0 feat) w_55 (Nat.zero_le _)

/-! ## The frame -/

/-- The registers at the first `call`, the function called with registers `g` and the stack guard `c`. -/
def ag1 (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 c ^^^ BitVec.setWidth 32 c)
    rsp := g.rsp - 40#64 }

/-- The registers at the third `call`: `rdi` the frame, `esi` 7. -/
abbrev ag3 (g : Gprs) : Gprs :=
  { g with
    rsi := BitVec.setWidth 64 7#32
    rdi := g.rsp }

/-- The answer: bit 5 of the 4 bytes at `s + 4` (`a[1]`, `ebx` of leaf 7), zero-extended. -/
abbrev abit (V : Addr → Byte) (s : Addr) : BitVec 64 :=
  BitVec.setWidth 64 ((ofBytesLE 32 (List.map V (byteAddrs (s + 4#64) 4)) >>> 5) &&& 1#32)

theorem t36 {rs : Addr} (h : 48 ≤ rs.toNat) : (rs - 40#64 + 4#64).toNat = rs.toNat - 36 := by
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem s40 (s : Addr) : s - 40#64 + 40#64 = s := BitVec.sub_add_cancel _ _

/-- `jbe` taken: `eax` not above 6. -/
theorem le_jbe {s : BitVec 32} (h : (decide (s.toNat < 6) || decide (s = 6#32)) = true) : s.toNat ≤ 6 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · subst h; decide

/-- `jbe` not taken: `eax` above 6. -/
theorem gt_jbe {s : BitVec 32} (h : (decide (s.toNat < 6) || decide (s = 6#32)) = false) : 6 < s.toNat := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : s.toNat ≠ 6 := fun e => h2 (BitVec.eq_of_toNat_eq (e.trans rfl))
  omega

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to the first `call`: the stack guard stored in the frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 24 ∧ g' = ag1 g rdq(V, fb + 40#64) ∧ V' = Gdt.dV1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw
  wpx [W_0, o0, Op.ldf]
  all_goals vc_fin

/-- Back from the OS test with `eax` 0: to 33. -/
theorem vc_29z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 = 0#32)
    (h : ∀ fl, Q 33 g fl V) : W_29 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_29, o1, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact trivial | apply And.intro | intro _)

/-- Back from the OS test with `eax` not 0: to the second `call` at 64. -/
theorem vc_29n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 ≠ 0#32)
    (h : ∀ fl, Q 64 g fl V) : W_29 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_29, o1, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax` to 35. -/
theorem vc_33 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 35 { g with rax := 0#64 } fl V) : W_33 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_33, o2, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- From 35: the stack guard checked, the frame dropped, to the `ret` at 55. -/
theorem vc_35 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64))
    (h : ∀ fl, Q 55 { g with rdx := 0#64, rsp := g.rsp + 40#64 } fl V) :
    W_35 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl24 hc h
  wpx [W_35, W_51, o3, o4, Op.xormf, hc, BitVec.xor_self]
  all_goals repeat' (first
    | exact h _
    | rfl
    | assumption
    | (intro hh; exact absurd hh (by decide))
    | constructor
    | intro _)

/-- Back from `z7_x86_cpuid_GetMaxFunc`: `cmp eax, 6; jbe` to 33, else to the third `call` at 82. -/
theorem vc_69 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : (g.rax.setWidth 32).toNat ≤ 6 → ∀ fl, Q 33 g fl V)
    (h2 : 6 < (g.rax.setWidth 32).toNat → ∀ fl, Q 82 (ag3 g) fl V) : W_69 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ag3] at h1 h2 ⊢
  wpx [W_69, W_74, o5, o6]
  all_goals repeat' (first | apply And.intro | intro _)
  all_goals first
    | exact h1 (le_jbe (by assumption)) _
    | exact h2 (gt_jbe (by assumption)) _

/-- Back from `z7_x86_cpuid`: `eax` = `abit`, to 35. -/
theorem vc_87 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ fl, Q 35 { g with rax := abit V g.rsp } fl V) : W_87 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl4 h
  wpx [W_87, o7]
  all_goals repeat' (first | exact h _ | assumption | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 35, `rsp` = `S - 40`, the stack guard and the return address in place: to the return address. -/
theorem fin35 {fb S : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L av2_at av2)
    {Z : State} {V' : Addr → Byte} (hKZ : KeptW Wl s₀ Z) (hAZ : Agree F Z.proc.mm.mem V')
    (hrZ : Z.cpu.rip = av2_at.add 35) (hzs : Z.cpu.gpr.rsp = S - 40#64)
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (S - 40#64 + 24#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcan : rdq(V', S - 40#64 + 24#64) = rdq(V', fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V', S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rdx := 0#64, rsp := S + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  refine (c_35 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 55 ∧
      g' = { Z.cpu.gpr with rdx := 0#64, rsp := S } ∧ V'' = V') hKZ hAZ hrZ
    (vc_35 (by rw [hzs]; exact hl24) hcl (by rw [hzs]; exact hcan) fun _ => ⟨rfl, by rw [hzs, s40], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = S := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_55 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₄ hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

/-- From 33: `eax` = 0, then as `fin35`. -/
theorem fin33 {fb S : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L av2_at av2)
    {Z : State} {V' : Addr → Byte} (hKZ : KeptW Wl s₀ Z) (hAZ : Agree F Z.proc.mm.mem V')
    (hrZ : Z.cpu.rip = av2_at.add 33) (hzs : Z.cpu.gpr.rsp = S - 40#64)
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (S - 40#64 + 24#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcan : rdq(V', S - 40#64 + 24#64) = rdq(V', fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V', S) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rdx := 0#64, rsp := S + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  refine (c_33 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 35 ∧ g' = { Z.cpu.gpr with rax := 0#64 } ∧
      V'' = V') hKZ hAZ hrZ (vc_33 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  refine fin35 (S := S) c hfs hin hKU hAU hrU (by rw [hgU]; exact hzs) hl24 hl hcl hcan hin₂ h₂ hra ?_
  intro Z' t' hK' hA' hr' hg'
  refine k Z' t' hK' hA' hr' ?_
  rw [hg', hgU]
  try rfl

/-- `CPU_IsSupported_AVX2 ()` from its entry, the three callees as hypotheses (`kf1`, `kf2`, `kf3`, each with the
return into `CPU_IsSupported_AVX2` pushed at `S - 48`). If the OS test's `eax` is 0, or `GetMaxFunc`'s is not above
6, the run reaches the return address with `rax` 0 (`kr1`, `kr2`); else, through `z7_x86_cpuid (a, 7)`, with `rax`
= `abit` of the bytes it left (`kr3`); `rsp` = `S + 8`. -/
theorem av2_ok {fb : Addr} {Pc1 Pc2 Pc3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L av2_at av2)
    {code1 : List Byte} (hin1 : CodeIn L os_at code1) (hC1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L max_at code2) (hC2 : 0 < code2.length)
    {code3 : List Byte} (hin3 : CodeIn L cpuid_at code3) (hC3 : 0 < code3.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = av2_at)
    (h48 : 48 ≤ X.cpu.gpr.rsp.toNat)
    (hfw : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hfd : ∀ i < 48, Foot F.data (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Gdt.dV1 V X.cpu.gpr fb) (X.cpu.gpr.rsp - 48#64) (toBytesLE (av2_at.add 29) 8)) →
      Y.cpu.rip = os_at → Y.cpu.gpr = (ag1 X.cpu.gpr rdq(V, fb + 40#64)).set 4 (X.cpu.gpr.rsp - 48#64) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = av2_at.add 29 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 →
        rdq(V', X.cpu.gpr.rsp - 40#64 + 24#64) = rdq(V', fb + 40#64) →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 → Pc1 Z V' →
      Z.cpu.gpr.rax.setWidth 32 ≠ 0#32 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48#64) (toBytesLE (av2_at.add 69) 8)) →
      Y.cpu.rip = max_at → Y.cpu.gpr = Z.cpu.gpr.set 4 (X.cpu.gpr.rsp - 48#64) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = av2_at.add 69 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 →
        rdq(V₂, X.cpu.gpr.rsp - 40#64 + 24#64) = rdq(V₂, fb + 40#64) →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kf3 : ∀ (Z₂ : State) (V₂ : Addr → Byte), Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 → Pc2 Z₂ V₂ →
      6 < (Z₂.cpu.gpr.rax.setWidth 32).toNat →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₂ (X.cpu.gpr.rsp - 48#64) (toBytesLE (av2_at.add 87) 8)) →
      Y.cpu.rip = cpuid_at → Y.cpu.gpr = (ag3 Z₂.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48#64) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = av2_at.add 87 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 →
        rdq(V₃, X.cpu.gpr.rsp - 40#64 + 24#64) = rdq(V₃, fb + 40#64) →
        rdq(V₃, X.cpu.gpr.rsp) = e₂.add j₂ → Pc3 Z₃ V₃ → GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc1 Z V' →
      Z.cpu.gpr.rax.setWidth 32 = 0#32 → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr2 : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z₂ V₂ →
      (Z₂.cpu.gpr.rax.setWidth 32).toNat ≤ 6 → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V₂ →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rax := 0#64, rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr3 : ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), Pc3 Z₃ V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₃ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₃.cpu.gpr with
        rax := abit V₃ (X.cpu.gpr.rsp - 40#64), rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have a16 := Gdt.t16 h48
  have a36 := t36 h48
  have hl24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40#64 + 24#64) i) :=
    Gdt.fr hfd (Gdt.fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide)
  have hw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64 + 24#64) i) :=
    Gdt.fr hfw (Gdt.fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide)
  have hl4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40#64 + 4#64) i) :=
    Gdt.fr hfd (Gdt.fa h48 (d := 12) (by decide) (by rw [a36]; omega)) (by decide)
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48#64) i) := fun i hi => hfw i (by omega)
  -- to the first `call`
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 24 ∧ g' = ag1 X.cpu.gpr rdq(V, fb + 40#64) ∧ V' = Gdt.dV1 V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hcl hw24) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hgY]; try rfl
  have hcs : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 48#64 := by rw [hYsp]; exact Gdt.e48 h48
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_24 _) hin1 hC1 tgt_24 (by rw [hcs]; exact hst) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hcs] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hcs, hgY]) ?_
  -- back from the OS test, at 29
  intro Z V' t'' hKZ hAZ hrZ hzs hcan hra hP1
  by_cases hz : Z.cpu.gpr.rax.setWidth 32 = 0#32
  · refine (c_29 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 33 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_29z hz fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    refine fin33 (S := X.cpu.gpr.rsp) c hfs hin hKU hAU hrU (by rw [hgU]; exact hzs) hl24 hl hcl hcan hin₂ h₂ hra ?_
    intro Z' t' hK' hA' hr' hg'
    exact kr1 Z _ Z' t' hP1 hz hK' hA' hr' (by rw [hg', hgU])
  -- to the second `call`
  refine (c_29 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 64 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
    (vc_29n hz fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 48#64 := by rw [hgU, hzs]; exact Gdt.e48 h48
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_64 _) hin2 hC2 tgt_64 (by rw [hsU]; exact hst) ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsU] at hA₄
  refine kf2 Z V' hzs hP1 hz U₂ t₄ hK₄ hA₄ hr₄ (by rw [hg₄, hsU, hgU]) ?_
  -- back from `GetMaxFunc`, at 69
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hcan₂ hra₂ hP2
  by_cases h6 : (Z₂.cpu.gpr.rax.setWidth 32).toNat ≤ 6
  · refine (c_69 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 33 ∧ g' = Z₂.cpu.gpr ∧ V'' = V₂) hKZ₂ hAZ₂ hrZ₂
      (vc_69 (fun _ _ => ⟨rfl, rfl, rfl⟩) fun h => absurd h (by omega)) ?_
    rintro j' g fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
    subst V₃
    refine fin33 (S := X.cpu.gpr.rsp) c hfs hin hKU₃ hAU₃ hrU₃ (by rw [hgU₃]; exact hz2s) hl24 hl hcl hcan₂ hin₂ h₂
      hra₂ ?_
    intro Z' t' hK' hA' hr' hg'
    exact kr2 Z₂ _ Z' t' hP2 h6 hK' hA' hr' (by rw [hg', hgU₃])
  -- to the third `call`
  refine (c_69 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 82 ∧ g' = ag3 Z₂.cpu.gpr ∧ V'' = V₂) hKZ₂ hAZ₂
    hrZ₂ (vc_69 (fun h => absurd h h6) fun _ _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst V₃
  have hsU₃ : U₃.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 48#64 := by
    rw [hgU₃]
    show Z₂.cpu.gpr.rsp - 8 = _
    rw [hz2s]
    exact Gdt.e48 h48
  refine c.s_call hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (call_82 _) hin3 hC3 tgt_82 (by rw [hsU₃]; exact hst) ?_
  rintro U₄ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
  rw [hsU₃] at hA₇
  refine kf3 Z₂ V₂ hz2s hP2 (by omega) U₄ t₇ hK₇ hA₇ hr₇ (by rw [hg₇, hsU₃, hgU₃]) ?_
  -- back from `z7_x86_cpuid`, at 87: the answer, then from 35
  intro Z₃ V₃ t₈ hKZ₃ hAZ₃ hrZ₃ hz3s hcan₃ hra₃ hP3
  refine (c_87 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 35 ∧
      g' = { Z₃.cpu.gpr with rax := abit V₃ (X.cpu.gpr.rsp - 40#64) } ∧ V'' = V₃) hKZ₃ hAZ₃ hrZ₃
    (vc_87 (by rw [hz3s]; exact hl4) fun _ => ⟨rfl, by rw [hz3s], rfl⟩) ?_
  rintro j' g fl₄ V₄ ⟨rfl, rfl, hV₄⟩ U₅ t₉ hKU₅ hAU₅ hrU₅ hgU₅ -
  subst V₄
  refine fin35 (S := X.cpu.gpr.rsp) c hfs hin hKU₅ hAU₅ hrU₅ (by rw [hgU₅]; exact hz3s) hl24 hl hcl hcan₃ hin₂ h₂
    hra₃ ?_
  intro Z' t' hK' hA' hr' hg'
  exact kr3 Z₃ _ Z' t' hP3 hK' hA' hr' (by rw [hg', hgU₅]; try rfl)

end FV7z.Av2
