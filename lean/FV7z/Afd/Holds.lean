import FV7z.Afd.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `AString::Find (s, startIndex)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Find (const char *s, unsigned startIndex)` at `0x44cae0` in `7zzs`
(`CPP/Common/MyString.cpp`), `this` = `rdi`, `s` = `rsi`, `startIndex` = `edx`, `S` the entry's `rsp`: `push rbx`
(`V1`), `rbx` = `_chars` (`[rdi]`), `rdi` = `_chars + startIndex` (`gC`), `strstr (rdi, s)` (`call` at 13 to the PLT's
entry `0x401038`); back at 18 `test rax, rax; je`: found, `eax -= ebx` (the index), `pop rbx`, the `ret` (26); none,
`eax` = -1, `pop rbx`, the `ret` (33).

`strstr` is a hypothesis, as the callees in `FV7z/Ain/Holds.lean`: a continuation at its entry (`kf`), given the run
from its return, which keeps `rbx`, the frame's `rsp`, the saved `rbx` and the return address in the bytes it leaves;
`Pc` is what it leaves.

- `V1`, `gC`: the bytes with `rbx` pushed; the registers at the `call`.
- `hxp`: `_chars` in `V1`, as in `V`.
- `vc_0`: the piece from the entry to the `call`; `vc_18z`, `vc_18n`: from 18, none found and found.
- `afd_ok`: through `strstr` to the return address, `eax` = -1 (`kn`) or the found pointer's low half minus
  `_chars`'s (`ky`), `rbx`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Afd

/-- The PLT's entry for `strstr`. -/
abbrev plt_strstr : Addr := 0x401038

/-- The `call` to `strstr`. -/
def pcs : List Byte := [0xe8, 0x46, 0x45, 0xfb, 0xff]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 18446744073709241670] 5) := by dec_rfl
theorem wc_13 : pcs <+: afd.drop 13 := by decide +kernel
theorem call_13 (feat : Features) : Dec feat afd 13 (FV7z.mk .call 64 [.rel 18446744073709241670] 5) :=
  Dec.shift (j := 13) (k := 0) (pcs_0 feat) wc_13 (Nat.zero_le _)
theorem tgt_13 : afd_at.add (13 + 5) + BitVec.ofNat 64 18446744073709241670 = plt_strstr := by decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_26 : pret <+: afd.drop 26 := by decide +kernel
theorem ret_26 (feat : Features) : Dec feat afd 26 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 26) (k := 0) (pret_0 feat) w_26 (Nat.zero_le _)
theorem w_33 : pret <+: afd.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat afd 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)

/-! ## The frame -/

/-- The bytes with `rbx` pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call` of `strstr`: `rbx` = `_chars`, `rdi` = `_chars + startIndex`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := rdq(V, g.rdi),
      rsp := g.rsp - 8,
      rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) + rdq(V, g.rdi) }

theorem aE4 (s : Addr) : s - 8 + 8 = s := BitVec.sub_add_cancel _ _

theorem aT8 (s : BitVec 64) (h : 8 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega

/-- `_chars` in `V1`: as in `V`, `this`'s 8 bytes apart from the push. -/
theorem hxp (V : Addr → Byte) (g : Gprs) (hp : 8 ≤ g.rsp.toNat) (hq : g.rdi.toNat + 8 ≤ 2 ^ 64)
    (hd : g.rdi.toNat + 8 ≤ g.rsp.toNat - 8 ∨ g.rsp.toNat ≤ g.rdi.toNat) :
    rdq(V1 V g, g.rdi) = rdq(V, g.rdi) := by
  have hlt := g.rsp.isLt
  have t8 := aT8 g.rsp hp
  dsimp only [V1]
  rw [Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.rbx 8) g.rdi 8 (by rw [toBytesLE_length, t8]; omega) hq
    (by rw [toBytesLE_length, t8]; omega)]

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry's code: `push rbx`, the loads, up to the `call` at 13. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fc : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hx : rdq(V1 V g, g.rdi) = rdq(V, g.rdi))
    (h : ∀ fl, Q 13 (gC V g) fl (V1 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, V1] at hs1 fc hx h ⊢
  wpx [W_0, o0, hx]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- From 18, `strstr` found nothing (`rax` 0): `mov eax, -1; pop rbx` to the `ret` at 33. -/
theorem vc_18z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (g.rax == 0) = true)
    (l1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 33
      { g with rax := BitVec.setWidth 64 (BitVec.ofNat 32 4294967295), rbx := rdq(V, g.rsp), rsp := g.rsp + 8 }
      fl V) :
    W_18 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz l1 h ⊢
  wpx [W_18, W_23, W_27, o1, o2, o3, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- From 18, `strstr` found `s` (`rax` not 0): `sub eax, ebx; pop rbx` to the `ret` at 26. -/
theorem vc_18n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (g.rax == 0) = false)
    (l1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 26
      { g with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax - BitVec.setWidth 32 g.rbx),
          rbx := rdq(V, g.rsp),
          rsp := g.rsp + 8 } fl V) :
    W_18 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz l1 h ⊢
  wpx [W_18, W_23, W_27, o1, o2, o3, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Find (s, startIndex)` (`this` = `rdi`, `s` = `rsi`, `startIndex` = `edx`) from its entry, `S` = `rsp`:
at `strstr`'s PLT entry with the registers `gC`, the bytes `V1` and the return address `afd_at + 18` at `S - 16`
(`kf`); from its return (`rsp` = `S - 8`, `rbx` = `_chars`, the saved `rbx` and the return address in its bytes, the
post `Pc`) to the return address with `rbx`, `rsp` restored: `rax` 0, `eax` = -1 (`kn`); else `eax` = `eax - ebx`
with `ebx` the low half of `_chars` (`ky`). -/
theorem afd_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L afd_at afd)
    {codeP : List Byte} (hinP : CodeIn L plt_strstr codeP) (hP : 0 < codeP.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = afd_at)
    (hp : 8 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 8 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (afd_at.add 18) 8)) →
      Y.cpu.rip = plt_strstr → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = afd_at.add 18 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rdi) →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kn : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → Z.cpu.gpr.rax = 0 →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := BitVec.setWidth 64 (BitVec.ofNat 32 4294967295), rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (ky : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → Z.cpu.gpr.rax ≠ 0 →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax - BitVec.setWidth 32 rdq(V, X.cpu.gpr.rdi)),
        rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hx := hxp V X.cpu.gpr hp hq hd
  have hrip' : X.cpu.rip = afd_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the entry's code, to the `call` of `strstr`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 13 ∧ g' = gC V X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 fc hx fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_13 _) hinP hP tgt_13 (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8) := by rw [hg₂, hsY, hgY]
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `strstr`, at 18
  intro Z V' t'' hKZ hAZ hrZ hzs hzb q1 qr hPc
  by_cases h0 : Z.cpu.gpr.rax = 0
  · -- none found: to the `ret` at 33
    have hz : (Z.cpu.gpr.rax == 0) = true := beq_iff_eq.2 h0
    refine (c_18 prof).run c hin (fun j' g' _ V'' => j' = 33 ∧
        g' = { Z.cpu.gpr with
          rax := BitVec.setWidth 64 (BitVec.ofNat 32 4294967295), rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V'' = V') hKZ hAZ hrZ
      (vc_18z hz (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, aE4, q1], rfl⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_33 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact qr) ?_
    rintro Z' t' hK' hA' ⟨hr', hg'⟩
    refine kn Z V' Z' t' hPc h0 hK' hA' hr' ?_
    rw [hg', hgU]
    try rfl
  · -- found: to the `ret` at 26
    have hz : (Z.cpu.gpr.rax == 0) = false := beq_eq_false_iff_ne.2 h0
    refine (c_18 prof).run c hin (fun j' g' _ V'' => j' = 26 ∧
        g' = { Z.cpu.gpr with
          rax := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax - BitVec.setWidth 32 rdq(V, X.cpu.gpr.rdi)),
          rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V'' = V') hKZ hAZ hrZ
      (vc_18n hz (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, hzb, aE4, q1], rfl⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_26 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact qr) ?_
    rintro Z' t' hK' hA' ⟨hr', hg'⟩
    refine ky Z V' Z' t' hPc h0 hK' hA' hr' ?_
    rw [hg', hgU]
    try rfl

end FV7z.Afd
