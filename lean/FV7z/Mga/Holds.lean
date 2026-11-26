import FV7z.Mga.Spec
import FV7z.Imm.Blocks1
import FV7z.Ifr.Blocks1
/-!
# `_int_memalign` (PLAN.md §M, M1)

glibc 2.31's `_int_memalign (av, alignment, bytes)` at `0x631bc0` in `7zzs`, one thread, in pieces between its calls:
the calls of `_int_malloc` (58) and of `_int_free` (216, 336) are continuation hypotheses, as are the returns. `S` is
the entry `rsp`, `bS S` the body's; `Fr V S g ra`: the six saved registers of `g` in their slots, the return address
`ra` at `S`.

- `ret341`: from 341 (also where the second `_int_free` returns): `rax = r12`, the pops, the `ret`.
- `mga_e`: from the entry: `bytes` too big (`errno = ENOMEM`, return 0), or to `_int_malloc (av, nb + alignment +
  MINSIZE)`.
- `mga_z`: `_int_malloc` gave 0: return 0.
- `mga_254`: from 254 (`rsi` the chunk `q`, `r12` the result): mmapped or no room for a remainder (return), or the
  remainder split off and to `_int_free (av, q + nb, 1)`.
- `mga_a`: `_int_malloc` gave `m` aligned: to `mga_254` with `q = m - 16`.
- `mga_f1`: where the first `_int_free` returns (221): `newsize ≥ nb` and `newp + 16` aligned (the asserts), to
  `mga_254` with `q = newp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6 fr_e6 rdo)
open FV7z.Stm (Km stk)
namespace FV7z.Mga

/-- The saved registers of `g` in the six slots under `S`, the return address `ra` at `S`. -/
abbrev Fr (V : Addr → Byte) (S : Addr) (g : Gprs) (ra : Addr) : Prop :=
  rdq(V, S - 8 - 8 - 8 - 8 - 8 - 8) = g.rbx ∧ rdq(V, S - 8 - 8 - 8 - 8 - 8) = g.rbp ∧
    rdq(V, S - 8 - 8 - 8 - 8) = g.r12 ∧ rdq(V, S - 8 - 8 - 8) = g.r13 ∧ rdq(V, S - 8 - 8) = g.r14 ∧
    rdq(V, S - 8) = g.r15 ∧ rdq(V, S) = ra

/-- `n` bytes from `a`, not wrapping, apart from the slots and the return address `[S - 48, S + 8)`. -/
abbrev Oa (S a : Addr) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ (a.toNat + n ≤ S.toNat - 48 ∨ S.toNat + 8 ≤ a.toNat)

/-- The frame's bytes `[S - 64, S)` writable. -/
abbrev Stk (Wl : List Rgn) (S : Addr) : Prop :=
  ∀ a : Addr, S.toNat - 64 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a

/-- The bytes after the remainder `q + nb` of the chunk `q` (size word `Z`) is split off. -/
abbrev rV (V : Addr → Byte) (q nb av Z : Addr) : Addr → Byte :=
  Vst (Vst V (q + nb + 8#64) (toBytesLE ((Z &&& 18446744073709551608#64) - nb ||| nmf av ||| 1#64) 8)) (q + 8#64)
    (toBytesLE (nb ||| (Z.setWidth 32 &&& 7#32).setWidth 64) 8)

/-- The return to `ra` with the bytes `V` and `rax = r`, `rsp = S + 8`, the registers a call keeps those of `g₀`. -/
abbrev KR (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ra : Addr) (g₀ : Gprs) (V : Addr → Byte) (r : Addr) : Prop :=
  ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = ra → Y.cpu.gpr.rsp = S + 8 → Y.cpu.gpr.rax = r →
    Km g₀ Y.cpu.gpr → GoG prof L o gev gP gE Y t'

theorem Fr_st {V : Addr → Byte} {S ra a : Addr} {g : Gprs} {w n : Nat} {v : BitVec w} (hS : 80 ≤ S.toNat)
    (hS8 : S.toNat + 8 ≤ 2 ^ 64) (ho : Oa S a n) (h : Fr V S g ra) : Fr (Vst V a (toBytesLE v n)) S g ra := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨o1, o2⟩ := ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [rdo o1] <;> first | assumption | omega

theorem Fr_fr6 (V : Addr → Byte) (S : Addr) (g : Gprs) (hS : 80 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64) :
    Fr (fr6 V S g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx) S g (rdq(V, S)) := by
  obtain ⟨r6, r5, r4, r3, r2, r1⟩ := Mcn.fr6_rd V S g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx hS
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  refine ⟨r6, r5, r4, r3, r2, r1, ?_⟩
  unfold fr6
  rw [rdo, rdo, rdo, rdo, rdo, rdo] <;> omega

/-- The slots from the body's stack pointer. -/
theorem up_b {S : Addr} (hS : 80 ≤ S.toNat) :
    bS S + 8#64 = S - 8 - 8 - 8 - 8 - 8 - 8 ∧ bS S + 8#64 + 8 = S - 8 - 8 - 8 - 8 - 8 ∧
    bS S + 8#64 + 8 + 8 = S - 8 - 8 - 8 - 8 ∧ bS S + 8#64 + 8 + 8 + 8 = S - 8 - 8 - 8 ∧
    bS S + 8#64 + 8 + 8 + 8 + 8 = S - 8 - 8 ∧ bS S + 8#64 + 8 + 8 + 8 + 8 + 8 = S - 8 ∧
    bS S + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  have eb := bS_toNat hS
  have u0 : (bS S + 8#64).toNat = S.toNat - 48 := by
    rw [BitVec.toNat_add, eb, show (8#64).toNat = 8 from rfl]
    omega
  have u1 := Stm.ta8 (a := bS S + 8#64) (by omega)
  have u2 := Stm.ta8 (a := bS S + 8#64 + 8) (by omega)
  have u3 := Stm.ta8 (a := bS S + 8#64 + 8 + 8) (by omega)
  have u4 := Stm.ta8 (a := bS S + 8#64 + 8 + 8 + 8) (by omega)
  have u5 := Stm.ta8 (a := bS S + 8#64 + 8 + 8 + 8 + 8) (by omega)
  have u6 := Stm.ta8 (a := bS S + 8#64 + 8 + 8 + 8 + 8 + 8) (by omega)
  exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega),
    BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega),
    BitVec.eq_of_toNat_eq (by omega)⟩

theorem rv3 (Y : State) : rv Y 64 3 = Y.cpu.gpr.rbx := by
  show (Y.cpu.gpr.get (regOf 3)).setWidth 64 = _
  rw [BitVec.setWidth_eq]
  rfl

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 1000000 in
/-- From 341: `rax = r12`, the pops, the `ret` to `ra`. -/
theorem ret341 {fb S r : Addr} {g₀ : Gprs} {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mga_at mga) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hS : 80 ≤ S.toNat)
    (hstk : Stk Wl S) (hlr : ∀ i < 8, Foot F.data (Addr.add S i))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mga_at.add 341)
    (hsp : X.cpu.gpr.rsp = bS S) (h12 : X.cpu.gpr.r12 = r) (hfr : Fr V S g₀ (e₂.add j₂))
    (k : KR prof F Wl L s₀ o gev gP gE S (e₂.add j₂) g₀ V r) : GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := up_b hS
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  have fp : ∀ x : Addr, S.toNat - 64 ≤ x.toNat → x.toNat + 8 ≤ S.toNat → ∀ i < 8, Foot F.data (Addr.add x i) :=
    fun x h1 h2 i hi => c.hws _ (stk hstk h1 h2 (by omega) i hi)
  refine (c_341 prof fb).run c hfs hin _ hK hA hrip
    (vc_341 (by rw [hsp, q0]; exact fp _ (by omega) (by omega)) (by rw [hsp, q1]; exact fp _ (by omega) (by omega))
      (by rw [hsp, q2]; exact fp _ (by omega) (by omega)) (by rw [hsp, q3]; exact fp _ (by omega) (by omega))
      (by rw [hsp, q4]; exact fp _ (by omega) (by omega)) (by rw [hsp, q5]; exact fp _ (by omega) (by omega))) ?_
  rintro j' g₂ fl V' ⟨rfl, rfl, hsp₂, hax₂, hbx₂, hbp₂, h12₂, h13₂, h14₂, h15₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst hg₂
  rw [hsp] at hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  rw [q6] at hsp₂
  rw [q0] at hbx₂
  rw [q1] at hbp₂
  rw [q2] at h12₂
  rw [q3] at h13₂
  rw [q4] at h14₂
  rw [q5] at h15₂
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_358 _) (by rw [hsp₂]; exact hlr) hin₂ h₂
    (by rw [hsp₂]; exact hfr.2.2.2.2.2.2) ?_
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ := hfr
  refine k Z t'' hKZ hAZ hrZ (by rw [hgZ]; show Y₂.cpu.gpr.rsp + 8 = _; rw [hsp₂])
    (by rw [hgZ]; show Y₂.cpu.gpr.rax = _; rw [hax₂, h12]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgZ]; show Y₂.cpu.gpr.rbx = _; rw [hbx₂]; exact r1
  · rw [hgZ]; show Y₂.cpu.gpr.rbp = _; rw [hbp₂]; exact r2
  · rw [hgZ]; show Y₂.cpu.gpr.r12 = _; rw [h12₂]; exact r3
  · rw [hgZ]; show Y₂.cpu.gpr.r13 = _; rw [h13₂]; exact r4
  · rw [hgZ]; show Y₂.cpu.gpr.r14 = _; rw [h14₂]; exact r5
  · rw [hgZ]; show Y₂.cpu.gpr.r15 = _; rw [h15₂]; exact r6

set_option maxHeartbeats 1000000 in
/-- From the entry (`rsp = S`, `rdi = av`, `rsi = alignment`, `rdx = bytes`): `bytes` above `PTRDIFF_MAX`
(`errno = ENOMEM`, return 0), or the call of `_int_malloc (av, nb + alignment + MINSIZE)` with `rbx = alignment`,
`rbp = av`, `r15 = nb`. -/
theorem mga_e {fb S : Addr} {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mga_at mga)
    (hinI : CodeIn L Imm.imm_at Imm.imm) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hS : 80 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64) (hstk : Stk Wl S) (hlr : ∀ i < 8, Foot F.data (Addr.add S i))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mga_at) (hsp : X.cpu.gpr.rsp = S)
    (hra : rdq(V, S) = e₂.add j₂) (we : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i))
    (hoe : Oa S (fb + 18446744073709551544#64) 4)
    (kE : X.cpu.gpr.rdx.msb = true → KR prof F Wl L s₀ o gev gP gE S (e₂.add j₂) X.cpu.gpr
      (Vst (fr6 V S X.cpu.gpr.r15 X.cpu.gpr.r14 X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx)
        (fb + 18446744073709551544#64) (toBytesLE 12#32 4)) 0#64)
    (kM : X.cpu.gpr.rdx.msb = false → ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (fr6 V S X.cpu.gpr.r15 X.cpu.gpr.r14 X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp
        X.cpu.gpr.rbx) (bS S - 8) (toBytesLE (mga_at.add (58 + 5)) 8)) →
      Y.cpu.rip = Imm.imm_at → Y.cpu.gpr.rsp = bS S - 8 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = nbv X.cpu.gpr.rdx + X.cpu.gpr.rsi + 32#64 → Y.cpu.gpr.rbx = X.cpu.gpr.rsi →
      Y.cpu.gpr.rbp = X.cpu.gpr.rdi → Y.cpu.gpr.r15 = nbv X.cpu.gpr.rdx → Y.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  have eb := bS_toNat hS
  have w : ∀ x : Addr, S.toNat - 64 ≤ x.toNat → x.toNat + 8 ≤ S.toNat → ∀ i < 8, Foot Wl (Addr.add x i) :=
    fun x h1 h2 => stk hstk h1 h2 (by omega)
  have hr0 : X.cpu.rip = mga_at.add 0 := by rw [addr_add_zero]; exact hrip
  cases hms : X.cpu.gpr.rdx.msb
  · refine (c_0 prof fb).run c hfs hin _ hK hA hr0
      (vc_0n (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega))
        (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega))
        (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega)) hms) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hsp₁, hdi₁, hsi₁, hbx₁, hbp₁, h15₁, h12₁, h13₁, h14₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    rw [hsp] at hA₁ hsp₁
    have esp : Y₁.cpu.gpr.rsp = bS S := hsp₁
    have e8 : (bS S - 8).toNat = S.toNat - 64 := by
      rw [Prepare.toNat_sub8 (a := bS S) (by omega), eb]
      omega
    refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_58 _) hinI (Imm.lt_len (j := 0) (by decide)) im_58
      (by rw [esp]; exact w _ (by omega) (by omega)) ?_
    rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
    rw [esp] at hA₀
    exact kM hms Z₀ t₀ hK₀ hA₀ hr₀ (by rw [hg₀]; show Y₁.cpu.gpr.rsp - 8 = _; rw [esp])
      (by rw [hg₀]; exact hdi₁) (by rw [hg₀]; exact hsi₁) (by rw [hg₀]; exact hbx₁) (by rw [hg₀]; exact hbp₁)
      (by rw [hg₀]; exact h15₁) (by rw [hg₀]; exact h12₁) (by rw [hg₀]; exact h13₁) (by rw [hg₀]; exact h14₁)
  · refine (c_0 prof fb).run c hfs hin _ hK hA hr0
      (vc_0e (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega))
        (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega))
        (by rw [hsp]; exact w _ (by omega) (by omega)) (by rw [hsp]; exact w _ (by omega) (by omega)) we hms) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hsp₁, h12₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    rw [hsp] at hA₁ hsp₁
    have hf := Fr_fr6 V S X.cpu.gpr hS hS8
    rw [hra] at hf
    exact ret341 c hfs hin hin₂ h₂ hS hstk hlr hK₁ hA₁ hr₁ hsp₁ h12₁ (Fr_st hS hS8 hoe hf) (kE hms)

/-- `_int_malloc` gave 0 (at 63, `rsp = bS S`): return 0. -/
theorem mga_z {fb S : Addr} {g₀ : Gprs} {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mga_at mga) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hS : 80 ≤ S.toNat)
    (hstk : Stk Wl S) (hlr : ∀ i < 8, Foot F.data (Addr.add S i))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mga_at.add 63)
    (hsp : X.cpu.gpr.rsp = bS S) (hax : X.cpu.gpr.rax = 0#64) (hfr : Fr V S g₀ (e₂.add j₂))
    (k : KR prof F Wl L s₀ o gev gP gE S (e₂.add j₂) g₀ V 0#64) : GoG prof L o gev gP gE X t := by
  refine (c_63 prof fb).run c hfs hin _ hK hA hrip (vc_63z hax) ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  exact ret341 c hfs hin hin₂ h₂ hS hstk hlr hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]) hfr k

set_option maxHeartbeats 1000000 in
/-- From 254 (`rsi` the chunk `q` with size word `Z`, `r12 = r` the result, `r15 = nb`, `rbp = av`): `q` mmapped or
no room for a remainder (return `r`), or the remainder `q + nb` split off (`rV`) and the call of
`_int_free (av, q + nb, 1)`, to return to 341. -/
theorem mga_254 {fb S q r nb av Z : Addr} {g₀ : Gprs} {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mga_at mga) (hinF : CodeIn L Ifr.ifr_at Ifr.ifr) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hS : 80 ≤ S.toNat) (hstk : Stk Wl S) (hlr : ∀ i < 8, Foot F.data (Addr.add S i))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mga_at.add 254)
    (hsp : X.cpu.gpr.rsp = bS S) (hsi : X.cpu.gpr.rsi = q) (h12 : X.cpu.gpr.r12 = r) (h15 : X.cpu.gpr.r15 = nb)
    (hbp : X.cpu.gpr.rbp = av) (hfr : Fr V S g₀ (e₂.add j₂)) (hZ : rdq(V, q + 8#64) = Z)
    (hq : q.toNat + (Z &&& 18446744073709551608#64).toNat ≤ 2 ^ 64)
    (hq16 : 16 ≤ (Z &&& 18446744073709551608#64).toNat)
    (hW : ∀ a : Addr, q.toNat ≤ a.toNat → a.toNat < q.toNat + (Z &&& 18446744073709551608#64).toNat → Foot Wl a)
    (hnb : 8 ≤ nb.toNat) (hnb' : nb.toNat + 32 < 2 ^ 64)
    (kR : KR prof F Wl L s₀ o gev gP gE S (e₂.add j₂) g₀ V r)
    (kF2 : (Z.setWidth 8 &&& 2#8 == 0) = true → nb.toNat + 32 < (Z &&& 18446744073709551608#64).toNat →
      ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst (rV V q nb av Z) (bS S - 8)
        (toBytesLE (mga_at.add (336 + 5)) 8)) →
      Y.cpu.rip = Ifr.ifr_at → Y.cpu.gpr.rsp = bS S - 8 → Y.cpu.gpr.rdi = av → Y.cpu.gpr.rsi = q + nb →
      Y.cpu.gpr.rdx = 1#64 → Y.cpu.gpr.rbx = X.cpu.gpr.rbx → Y.cpu.gpr.rbp = av → Y.cpu.gpr.r12 = r →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  have eb := bS_toNat hS
  have hql := q.isLt
  have e8 : (q + 8#64).toNat = q.toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have f1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i) := fun i hi => by
    rw [hsi]; exact c.hws _ (stk hW (by omega) (by omega) hq i hi)
  have hZ₀ : rdq(V, X.cpu.gpr.rsi + 8#64) = Z := by rw [hsi]; exact hZ
  cases hb : (Z.setWidth 8 &&& 2#8 == 0)
  · refine (c_254 prof fb).run c hfs hin _ hK hA hrip (vc_254m hZ₀ hb f1) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    exact ret341 c hfs hin hin₂ h₂ hS hstk hlr hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h12) hfr kR
  have e32 : (nb + 32#64).toNat = nb.toNat + 32 := by
    rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl]
    exact Nat.mod_eq_of_lt hnb'
  by_cases hs : nb.toNat + 32 < (Z &&& 18446744073709551608#64).toNat
  · have e1 : (q + nb).toNat = q.toNat + nb.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (q + nb + 8#64).toNat = q.toNat + nb.toNat + 8 := by
      rw [BitVec.toNat_add, e1, show (8#64).toNat = 8 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hZ' : rdq(Vst V (X.cpu.gpr.rsi + X.cpu.gpr.r15 + 8#64)
        (toBytesLE ((Z &&& 18446744073709551608#64) - X.cpu.gpr.r15 ||| nmf X.cpu.gpr.rbp ||| 1#64) 8),
        X.cpu.gpr.rsi + 8#64) = Z := by
      rw [hsi, h15, hbp, rdo]
      · exact hZ
      all_goals omega
    refine (c_254 prof fb).run c hfs hin _ hK hA hrip
      (vc_254s hZ₀ hb (by rw [h15, e32]; exact hs) hZ' f1 (fun i hi => by rw [hsi]; exact stk hW (by omega)
        (by omega) hq i hi) (fun i hi => by rw [hsi, h15]; exact stk hW (by omega) (by omega) hq i hi)) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hsi₁, hdi₁, hdx₁, hbx₁, hbp₁, h12₁, hsp₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    rw [hsi, h15, hbp] at hA₁
    rw [hsp] at hsp₁
    have e8' : (bS S - 8).toNat = S.toNat - 64 := by
      rw [Prepare.toNat_sub8 (a := bS S) (by omega), eb]
      omega
    refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_336 _) hinF (Ifr.lt_len (j := 0) (by decide))
      if_336 (by rw [hsp₁]; exact stk hstk (by omega) (by omega) (by omega)) ?_
    rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
    rw [hsp₁] at hA₀
    exact kF2 hb hs Z₀ t₀ hK₀ hA₀ hr₀ (by rw [hg₀]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hsp₁])
      (by rw [hg₀]; show Y₁.cpu.gpr.rdi = _; rw [hdi₁, hbp]) (by rw [hg₀]; show Y₁.cpu.gpr.rsi = _; rw [hsi₁, hsi, h15])
      (by rw [hg₀]; exact hdx₁) (by rw [hg₀]; exact hbx₁) (by rw [hg₀]; show Y₁.cpu.gpr.rbp = _; rw [hbp₁, hbp])
      (by rw [hg₀]; show Y₁.cpu.gpr.r12 = _; rw [h12₁, h12])
  · refine (c_254 prof fb).run c hfs hin _ hK hA hrip (vc_254k hZ₀ hb (by rw [h15, e32]; omega) f1) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    exact ret341 c hfs hin hin₂ h₂ hS hstk hlr hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h12) hfr kR

/-- `_int_malloc` gave `m ≠ 0` aligned to `alignment` (at 63: `rax = m`, `rbx = alignment`): to `mga_254` with
`q = m - 16`, `r12 = m`. -/
theorem mga_a {fb S m al : Addr} {X : State} {t : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mga_at mga) {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mga_at.add 63) (hax : X.cpu.gpr.rax = m) (hbx : X.cpu.gpr.rbx = al) (hm : m ≠ 0#64)
    (hal : al ≠ 0#64) (hdv : m % al = 0#64)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = mga_at.add 254 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp → Y.cpu.gpr.rsi = m + 18446744073709551600#64 → Y.cpu.gpr.r12 = m →
      Y.cpu.gpr.r15 = X.cpu.gpr.r15 → Y.cpu.gpr.rbp = X.cpu.gpr.rbp → Y.cpu.gpr.rbx = al →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_63 prof fb).run c hfs hin _ hK hA hrip (vc_63n (by rw [hax]; exact beq_eq_false_iff_ne.mpr hm)) ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_div64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (div_81 _) (by rw [hg₁])
    (by rw [rv3, hg₁]; show X.cpu.gpr.rbx ≠ 0; rw [hbx]; exact hal) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hdx : Y₂.cpu.gpr.rdx = 0#64 := by
    rw [hg₂, rv3, hg₁]
    show X.cpu.gpr.rax % X.cpu.gpr.rbx = _
    rw [hax, hbx, hdv]
  refine (c_84 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_84a hdx) ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  exact k Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃, hg₂, hg₁] <;> rfl)
    (by rw [hg₃, hg₂, hg₁]; show X.cpu.gpr.rax + _ = _; rw [hax])
    (by rw [hg₃, hg₂, hg₁]; exact hax) (by rw [hg₃, hg₂, hg₁] <;> rfl) (by rw [hg₃, hg₂, hg₁] <;> rfl)
    (by rw [hg₃, hg₂, hg₁]; exact hbx)

/-- Where the first `_int_free` returns (221: `r13 = newp`, `r14 = newsize`, `r15 = nb`, `rbx = alignment`):
`newsize ≥ nb` and `newp + 16` aligned, to `mga_254` with `q = newp`, `r12 = newp + 16`. -/
theorem mga_f1 {fb n ns nb al : Addr} {X : State} {t : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mga_at mga) {V : Addr → Byte} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mga_at.add 221) (h13 : X.cpu.gpr.r13 = n)
    (h14 : X.cpu.gpr.r14 = ns) (h15 : X.cpu.gpr.r15 = nb) (hbx : X.cpu.gpr.rbx = al) (hge : nb.toNat ≤ ns.toNat)
    (hal : al ≠ 0#64) (hdv : (n + 16#64) % al = 0#64)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = mga_at.add 254 →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp → Y.cpu.gpr.rsi = n → Y.cpu.gpr.r12 = n + 16#64 → Y.cpu.gpr.r15 = nb →
      Y.cpu.gpr.rbp = X.cpu.gpr.rbp → Y.cpu.gpr.rbx = al → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_221 prof fb).run c hfs hin _ hK hA hrip (vc_221 (by rw [h15, h14]; exact hge)) ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_div64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (div_239 _) (by rw [hg₁])
    (by rw [rv3, hg₁]; show X.cpu.gpr.rbx ≠ 0; rw [hbx]; exact hal) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hdx : Y₂.cpu.gpr.rdx = 0#64 := by
    rw [hg₂, rv3, hg₁]
    show (X.cpu.gpr.r13 + 16#64) % X.cpu.gpr.rbx = _
    rw [h13, hbx, hdv]
  refine (c_242 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_242 hdx) ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  exact k Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃, hg₂, hg₁] <;> rfl) (by rw [hg₃, hg₂, hg₁]; exact h13)
    (by rw [hg₃, hg₂, hg₁]; show X.cpu.gpr.r13 + _ = _; rw [h13]) (by rw [hg₃, hg₂, hg₁]; exact h15)
    (by rw [hg₃, hg₂, hg₁] <;> rfl) (by rw [hg₃, hg₂, hg₁]; exact hbx)

end

end FV7z.Mga
