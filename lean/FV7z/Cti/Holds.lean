import FV7z.Cti.Cuts
import FV7z.Tun.Inv
import FV7z.Sga.Holds
/-!
# `__ctype_init` (PLAN.md G3, startup)

glibc 2.31's `__ctype_init` at `0x6160e0` in `7zzs`: from the thread's locale (`fs:-0x70`) the `LC_CTYPE` data's
three tables (class, upper, lower: the values at `+0x40`, `+0x48`, `+0x58`), which it stores, moved by 256, 512 and
512, in the thread's `__libc_tsd_CTYPE_B`, `__libc_tsd_CTYPE_TOUPPER`, `__libc_tsd_CTYPE_TOLOWER` (`fs:-0x30`,
`fs:-0x38`, `fs:-0x40`). One stretch of code, then the `ret` (83).

- `CtMem V fb a b c`: the bytes after the three stores.
- `cti_ok`: called with the locale's pointers readable and apart from the 24 bytes stored to, the run reaches the
  return address with the three pointers stored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Cti

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_83 : pret <+: cti.drop 83 := by decide +kernel
theorem ret_83 (feat : Features) : Dec feat cti 83 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 83) (k := 0) (pret_0 feat) w_83 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the three stores in the thread's block. -/
def CtMem (V : Addr → Byte) (fb : Addr) (a b c : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (fb - 48#64) (toBytesLE (a + 256#64) 8)) (fb - 56#64) (toBytesLE (b + 512#64) 8)) (fb - 64#64)
    (toBytesLE (c + 512#64) 8)

/-- The registers at the `ret`. -/
def ctG (g : Gprs) (a b c : BitVec 64) : Gprs :=
  ((((g.set 0 (c + 512#64)).set 1 18446744073709551560#64).set 2 18446744073709551552#64).set 6 a).set 7 b

theorem ctG_rsp (g : Gprs) (a b c : BitVec 64) : (ctG g a b c).rsp = g.rsp := by cases g; rfl

theorem vc_0 {fb lp ct : Addr} {a b cc : BitVec 64} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hlp : rdq(V, fb + 18446744073709551504#64) = lp) (hct : rdq(V, lp) = ct) (ha : rdq(V, ct + 64#64) = a)
    (hb : rdq(V, ct + 72#64) = b) (hc : rdq(V, ct + 88#64) = cc)
    (f1 : ∀ i < 8, Foot F.data ((fb + 18446744073709551504#64).add i)) (f2 : ∀ i < 8, Foot F.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot F.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl ((fb - 64#64).add i))
    (hfb : 64 ≤ fb.toNat) (hcn : ct.toNat + 96 ≤ 2 ^ 64)
    (hap : ct.toNat + 96 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ ct.toNat + 64) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 83 ∧ g' = ctG g a b cc ∧ V' = CtMem V fb a b cc) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hlt := fb.isLt
  have e1 : fb + 18446744073709551568#64 = fb - 48#64 := by bv_omega
  have e2 : fb + 18446744073709551560#64 = fb - 56#64 := by bv_omega
  have e3 : fb + 18446744073709551552#64 = fb - 64#64 := by bv_omega
  have q1 : ∀ i < 8, Foot F.data ((ct + 64#64).add i) := fun i hi => f3 i (by omega)
  have q2 : ∀ i < 8, Foot F.data ((ct + 72#64).add i) := fun i hi => by
    have := f3 (8 + i) (by omega)
    rwa [show (ct + 64#64).add (8 + i) = (ct + 72#64).add i by simp only [Addr.add]; bv_omega] at this
  have q3 : ∀ i < 8, Foot F.data ((ct + 88#64).add i) := fun i hi => by
    have := f3 (24 + i) (by omega)
    rwa [show (ct + 64#64).add (24 + i) = (ct + 88#64).add i by simp only [Addr.add]; bv_omega] at this
  have w1 : ∀ i < 8, Foot Wl ((fb - 48#64).add i) := fun i hi => by
    have := fw (16 + i) (by omega)
    rwa [show (fb - 64#64).add (16 + i) = (fb - 48#64).add i by simp only [Addr.add]; bv_omega] at this
  have w2 : ∀ i < 8, Foot Wl ((fb - 56#64).add i) := fun i hi => by
    have := fw (8 + i) (by omega)
    rwa [show (fb - 64#64).add (8 + i) = (fb - 56#64).add i by simp only [Addr.add]; bv_omega] at this
  have w3 : ∀ i < 8, Foot Wl ((fb - 64#64).add i) := fun i hi => fw i (by omega)
  have r2 : rdq(Vst V (fb - 48#64) (toBytesLE (a + 256#64) 8), ct + 72#64) = b := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hb
  have r3 : rdq(Vst (Vst V (fb - 48#64) (toBytesLE (a + 256#64) 8)) (fb - 56#64) (toBytesLE (b + 512#64) 8),
      ct + 88#64) = cc := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hc
  wpx [W_0, o0, Op.ldf, Op.ld, Op.stf, Op.lea, Op.add]
  rw [hlp, hct, ha, e1, e2, e3, r2, r3]
  exact ⟨f1, f2, q1, w1, q2, w2, q3, w3, rfl, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__ctype_init ()` from its entry to the return address: with `lp` the thread's locale (`fs:-0x70`), `ct` its
`LC_CTYPE` data and `a`, `b`, `cc` the three tables there, the thread's three pointers are stored (`CtMem`); the
registers are `ctG`'s with the return address popped. -/
theorem cti_ok {fb lp ct : Addr} {a b cc : BitVec 64} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L cti_at cti) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cti_at)
    (hlp : rdq(V, fb - 112#64) = lp) (hct : rdq(V, lp) = ct) (ha : rdq(V, ct + 64#64) = a)
    (hb : rdq(V, ct + 72#64) = b) (hc : rdq(V, ct + 88#64) = cc)
    (f1 : ∀ i < 8, Foot F.data ((fb - 112#64).add i)) (f2 : ∀ i < 8, Foot F.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot F.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl ((fb - 64#64).add i))
    (hfb : 64 ≤ fb.toNat) (hcn : ct.toNat + 96 ≤ 2 ^ 64)
    (hap : ct.toNat + 96 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ ct.toNat + 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : X.cpu.gpr.rsp.toNat + 8 ≤ fb.toNat - 64 ∨ fb.toNat - 40 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (CtMem V fb a b cc) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (ctG X.cpu.gpr a b cc).set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := fb.isLt
  have e0 : fb - 112#64 = fb + 18446744073709551504#64 := by bv_omega
  rw [e0] at hlp f1
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hlp hct ha hb hc f1 f2 f3 fw hfb hcn hap) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY, ctG_rsp]
  refine c.s_ret hKY hAY hin (lt_len (by omega)) hrY (ret_83 _) (fun i hi => by rw [hspY]; exact hl i hi) hin₂ h₂
    ?_ ?_
  · rw [hspY, ← hra]
    unfold CtMem
    rw [vr (toBytesLE_length _ _) (by bv_omega) hsp (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) hsp (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) hsp (by bv_omega)]
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hspY, hgY]

end FV7z.Cti
