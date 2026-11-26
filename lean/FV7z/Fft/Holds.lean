import FV7z.Fft.Cuts
import FV7z.Utf.Holds
import FV7z.Sga.Holds
import FV7z.Lemmas.BlkOps17
/-!
# `FiTime_To_FILETIME_ns100` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NTime::FiTime_To_FILETIME_ns100 (const CFiTime &ts, FILETIME &ft, unsigned &ns100)` at
`0x458db0` in `7zzs` (`CPP/Windows/TimeUtils.cpp`; `objdump -d`): `r12`, `rbp`, `rbx` saved below the stack pointer,
`UnixTime64_To_FileTime64 (ts.tv_sec)` called (`Utf.utf_ok`), then `tv_nsec` (`ts + 8`) divided by 100 by a multiply
by `C` = `⌈2^66 / 25⌉` (`mh`, `m100`): the remainder in the 4 bytes at `ns100`, the quotient plus the call's answer in
the 8 bytes at `ft`; the saved registers back; `ret` at 95. The call at 20 and the `ret` lie outside the blocks.

- `mh_toNat`, `q_toNat`, `m100_eq`: the division by 100, on `toNat` (`omega`).
- `vc_0`, `vc_25`: from the entry to the call, from the return address to the `ret`.
- `fft_ok`: from the entry to the return address: the frame, the 8 bytes at `ft`, the 4 at `ns100`, the registers
  a call keeps (`Osv.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Utf (ftV)
namespace FV7z.Fft

/-- The call of `UnixTime64_To_FileTime64`. -/
def pcall : List Byte := [0xe8, 0xb7, 0xfa, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709550263] 5) := by dec_rfl
theorem w_20 : pcall <+: fft.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat fft 20 (FV7z.mk .call 64 [.rel 18446744073709550263] 5) :=
  Dec.shift (j := 20) (k := 0) (pcall_0 feat) w_20 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_95 : pret <+: fft.drop 95 := by decide +kernel
theorem ret_95 (feat : Features) : Dec feat fft 95 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 95) (k := 0) (pret_0 feat) w_95 (Nat.zero_le _)

/-! ## The division by 100 -/

/-- The high half of `(x >>> 2) * C`. -/
abbrev mh (x : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (x >>> 2) * BitVec.setWidth 128 2951479051793528259#64)

/-- `100 * (x / 100)` as the code computes it. -/
abbrev m100 (x : BitVec 64) : BitVec 64 :=
  ((mh x &&& 18446744073709551612#64) + mh x >>> 2 + ((mh x &&& 18446744073709551612#64) + mh x >>> 2) * 4#64) <<< 2

theorem mh1 (x : BitVec 64) : x.toNat / 4 < 4611686018427387904 := by
  have hx := x.isLt
  omega

theorem mh2 {y : Nat} (h : y < 4611686018427387904) :
    y * 2951479051793528259 < 340282366920938463463374607431768211456 := by
  omega

theorem mh3 {y : Nat} (h : y < 340282366920938463463374607431768211456) :
    y / 18446744073709551616 < 18446744073709551616 := by
  omega

theorem mh_toNat (x : BitVec 64) : (mh x).toNat = x.toNat / 4 * 2951479051793528259 / 2 ^ 64 := by
  have h1 : x.toNat / 4 < 340282366920938463463374607431768211456 := Nat.lt_trans (mh1 x) (by decide)
  have h2 := mh2 (mh1 x)
  simp -implicitDefEqProofs only [mh, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (mh3 h2)]

/-- `C` = `(2^66 + 11) / 25`: for `y` < `2^62`, `y * C / 2^66` = `y / 25`. -/
theorem div25 (y : Nat) (hy : y < 4611686018427387904) :
    y * 2951479051793528259 / 73786976294838206464 = y / 25 := by
  apply Nat.div_eq_of_lt_le <;> omega

theorem q_toNat (x : BitVec 64) : (mh x >>> 2).toNat = x.toNat / 100 := by
  have hx := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, mh_toNat, Nat.div_div_eq_div_mul,
    show (2 : Nat) ^ 64 * 2 ^ 2 = 73786976294838206464 from rfl, div25 _ (by omega)]
  omega

theorem and_m4 (h : BitVec 64) : h &&& 18446744073709551612#64 = h >>> 2 <<< 2 := by
  rw [BitVec.shiftLeft_ushiftRight, show BitVec.allOnes 64 <<< 2 = 18446744073709551612#64 by decide]

theorem q_eq (x : BitVec 64) : mh x >>> 2 = x / 100#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [q_toNat, BitVec.toNat_udiv]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

theorem m100_mul (x : BitVec 64) : m100 x = x / 100#64 * 100#64 := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [m100, and_m4, q_eq, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
  omega

theorem m100_eq (x : BitVec 64) : x - m100 x = x % 100#64 ∧ mh x >>> 2 = x / 100#64 := by
  refine ⟨?_, q_eq x⟩
  have hx := x.isLt
  rw [m100_mul]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  omega

/-! ## Addresses -/

theorem tsubc {a : Addr} {c : Nat} (hc : c < 2 ^ 64) (h : c ≤ a.toNat) :
    (a - BitVec.ofNat 64 c).toNat = a.toNat - c := by
  have ha := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  omega

theorem taddc {a : Addr} {c : Nat} (hc : c < 2 ^ 64) (h : a.toNat + c < 2 ^ 64) :
    (a + BitVec.ofNat 64 c).toNat = a.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  omega

/-- A disjunction `omega` does not split unless asked (`unfold Sep at h`). -/
def Sep (p q : Prop) : Prop := p ∨ q

theorem tsub8 {a : Addr} (h : 8 ≤ a.toNat) : (a - 8).toNat = a.toNat - 8 := by
  have ha := a.isLt
  rw [BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem tadd8 {a : Addr} (h : a.toNat + 8 < 2 ^ 64) : (a + 8).toNat = a.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

/-- `n` bytes at `a` among the `m` at `b`, `a` = `b + d`. -/
theorem offF {R : List Rgn} {b a : Addr} {m d n : Nat} (h : ∀ i < m, Foot R (Addr.add b i))
    (ha : a.toNat = b.toNat + d) (hd : d + n ≤ m) : ∀ i < n, Foot R (Addr.add a i) := fun i hi => by
  have e : Addr.add b (d + i) = Addr.add a i := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, ha]
    omega
  exact e ▸ h (d + i) (by omega)

/-! ## The blocks -/

/-- The bytes after the three pushes. -/
abbrev V3 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers at the call: `tv_sec` in `rdi`. -/
abbrev G20 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8, rbp := g.rsi, rdi := rdq(V3 g V, g.rdi), r12 := g.rdx }

/-- At the call. -/
def P20 (g₀ : Gprs) (V₀ : Addr → Byte) : Post := fun j g _ V => j = 20 ∧ g = G20 g₀ V₀ ∧ V = V3 g₀ V₀

theorem x20 {g₀ : Gprs} {V₀ : Addr → Byte} {g : Gprs} {fl : Rflags} {V : Addr → Byte} (hg : g = G20 g₀ V₀)
    (hV : V = V3 g₀ V₀) : P20 g₀ V₀ 20 g fl V :=
  ⟨rfl, hg, hV⟩

/-- The bytes after the stores into `ns100` (`r12`) and `ft` (`rbp`). -/
abbrev V5 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst V g.r12 (toBytesLE (BitVec.setWidth 32 (rdq(V, g.rbx + 8#64) - m100 rdq(V, g.rbx + 8#64))) 4)) g.rbp
    (toBytesLE (mh rdq(V, g.rbx + 8#64) >>> 2 + g.rax) 8)

/-- `tv_nsec`. -/
abbrev nsec (g : Gprs) (V : Addr → Byte) : BitVec 64 := rdq(V, g.rbx + 8#64)
/-- The registers after the division. -/
abbrev G95a (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rax := mh (nsec g V) >>> 2 + g.rax, rcx := nsec g V - m100 (nsec g V), rdx := m100 (nsec g V) }
/-- The registers after the first pop. -/
abbrev G95b (g : Gprs) (V : Addr → Byte) : Gprs :=
  { G95a g V with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 + 8 + 8, rsi := 2951479051793528259#64, r8 := g.rax }
/-- The registers at the `ret`. -/
abbrev G95 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { G95b g V with rbp := rdq(V5 g V, g.rsp + 8), r12 := rdq(V5 g V, g.rsp + 8 + 8) }

/-- At the `ret`. -/
def P95 (g₀ : Gprs) (V₀ : Addr → Byte) : Post := fun j g _ V => j = 95 ∧ g = G95 g₀ V₀ ∧ V = V5 g₀ V₀

theorem x95 {g₀ : Gprs} {V₀ : Addr → Byte} {g : Gprs} {fl : Rflags} {V : Addr → Byte} (hg : g = G95 g₀ V₀)
    (hV : V = V5 g₀ V₀) : P95 g₀ V₀ 95 g fl V :=
  ⟨rfl, hg, hV⟩

variable {F : Footprint} {Wl : List Rgn}

/-- To the call: the pushes, `tv_sec`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (h16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) (h24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (ht : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) : W_0 F Wl (P20 g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 h16 h24 ht ⊢
  wpx [W_0, o0]
  exact ⟨h8, h16, h24, ht, x20 rfl rfl⟩

/-- From the return address to the `ret`: `tv_nsec`, the division, the stores, the pops. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hb : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h12 : ∀ i < 4, Foot Wl (Addr.add g.r12 i))
    (hbp : ∀ i < 8, Foot Wl (Addr.add g.rbp i)) (h8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (h16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) : W_25 F Wl (P95 g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb h0 h12 hbp h8 h16 ⊢
  wpx [W_25, o1, Op.mul64, Op.mulp, Op.shr64, Op.shl64]
  exact ⟨hb, h0, fun _ _ _ _ _ _ => ⟨h12, hbp, h8, h16, x95 rfl rfl⟩⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `FiTime_To_FILETIME_ns100 (ts, ft, ns100)` from its entry to the return address, `ts` = `rdi`, `ft` = `rsi`,
`ns100` = `rdx`, 32 bytes below the stack pointer in what the run may store into, `ts`'s 16 bytes apart from them,
`ft`'s 8 and `ns100`'s 4 apart from the saved `rbp`, `r12` and the return address and from each other: the bytes but
the 32, `ft`'s and `ns100`'s as they were, `ft` = `ftV tv_sec + tv_nsec / 100`, `ns100` = `tv_nsec % 100`, the
registers a call keeps as at the entry. -/
theorem fft_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fft_at fft) (hinu : CodeIn L Utf.utf_at Utf.utf)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fft_at)
    (hs : 32 ≤ X.cpu.gpr.rsp.toNat) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hts : ∀ i < 16, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (htb : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (htd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hft : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i)) (hfb : X.cpu.gpr.rsi.toNat + 8 ≤ 2 ^ 64)
    (hfd : X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hns : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdx i)) (hnb : X.cpu.gpr.rdx.toNat + 4 ≤ 2 ^ 64)
    (hnd : X.cpu.gpr.rdx.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdx.toNat)
    (hnf : X.cpu.gpr.rdx.toNat + 4 ≤ X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rdx.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (X.cpu.gpr.rdx.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdx.toNat + 4) →
        ¬ (X.cpu.gpr.rsi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsi.toNat + 8) → V' a = V a) →
      rdq(V', X.cpu.gpr.rsi) = ftV rdq(V, X.cpu.gpr.rdi) + rdq(V, X.cpu.gpr.rdi + 8#64) / 100#64 →
      rdd(V', X.cpu.gpr.rdx) = (rdq(V, X.cpu.gpr.rdi + 8#64) % 100#64).setWidth 32 →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  replace htd : Sep _ _ := htd
  replace hfd : Sep _ _ := hfd
  replace hnd : Sep _ _ := hnd
  replace hnf : Sep _ _ := hnf
  have t8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := tsub8 (by omega)
  have t16 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    have := tsub8 (a := X.cpu.gpr.rsp - 8) (by omega)
    omega
  have t24 : (X.cpu.gpr.rsp - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 24 := by
    have := tsub8 (a := X.cpu.gpr.rsp - 8 - 8) (by omega)
    omega
  have t32 : (X.cpu.gpr.rsp - 8 - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 32 := by
    have := tsub8 (a := X.cpu.gpr.rsp - 8 - 8 - 8) (by omega)
    omega
  have t32' : (X.cpu.gpr.rsp - 32#64).toNat = X.cpu.gpr.rsp.toNat - 32 := tsubc (by omega) (by omega)
  have tt8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := taddc (by omega) (by omega)
  -- to the call
  refine (c_0 prof).run c hin (P20 X.cpu.gpr V) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (offF (d := 24) hst (by omega) (by omega)) (offF (d := 16) hst (by omega) (by omega))
      (offF (d := 8) hst (by omega) (by omega)) (fun i hi => hts i (by omega))) ?_
  rintro j g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hR1 : rdq(V3 X.cpu.gpr V, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by
    unfold Sep at htd
    dsimp only [V3]
    rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vr (by ln) (by omega) (by omega) (by omega)]
  dsimp only [V3] at hA₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hg₁]
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_20 _) hinu (Utf.lt_len (by decide)) (by decide)
    (by rw [hsp₁]; exact offF (d := 0) hst (by omega) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 := by
    rw [hg₂]
    show Y₁.cpu.gpr.rsp - 8 = _
    rw [hsp₁]
  obtain ⟨V₂, hA₂, h2o, h2r, h2b, h2p, h2c⟩ : ∃ V₂, Agree F Y₂.proc.mm.mem V₂ ∧
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₂ a = V a) ∧
      rdq(V₂, X.cpu.gpr.rsp - 8 - 8 - 8 - 8) = fft_at.add 25 ∧
      rdq(V₂, X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx ∧ rdq(V₂, X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp ∧
      rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
    refine ⟨_, hA₂, fun a h => ?_, ?_, ?_, ?_, ?_⟩
    · rw [vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega),
        vo (by ln) (by omega) (by omega)]
    · rw [vs (by ln) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
        vs (by ln) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
        vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  -- `UnixTime64_To_FileTime64 (tv_sec)`
  refine Utf.utf_ok c hinu hK₂ hA₂ hr₂
    (by rw [hsp₂]; exact fun i hi => c.hws _ (offF (d := 0) hst (by omega) (by omega) i hi)) hin (j₂ := 25)
    (lt_len (by decide)) (by rw [hsp₂]; exact h2r) ?_
  intro Z t₃ hK₃ hA₃ hr₃ hg₃
  have zb : Z.cpu.gpr.rbx = X.cpu.gpr.rdi :=
    (congrArg Gprs.rbx hg₃).trans ((congrArg Gprs.rbx hg₂).trans (congrArg Gprs.rbx hg₁))
  have zr12 : Z.cpu.gpr.r12 = X.cpu.gpr.rdx :=
    (congrArg Gprs.r12 hg₃).trans ((congrArg Gprs.r12 hg₂).trans (congrArg Gprs.r12 hg₁))
  have zbp : Z.cpu.gpr.rbp = X.cpu.gpr.rsi :=
    (congrArg Gprs.rbp hg₃).trans ((congrArg Gprs.rbp hg₂).trans (congrArg Gprs.rbp hg₁))
  have zax : Z.cpu.gpr.rax = ftV rdq(V3 X.cpu.gpr V, X.cpu.gpr.rdi) :=
    (congrArg Gprs.rax hg₃).trans (congrArg ftV ((congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hg₁)))
  have zsp : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 :=
    (congrArg Gprs.rsp hg₃).trans (by rw [hsp₂]; exact BitVec.sub_add_cancel _ _)
  have g1k : Y₁.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₁.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₁]
    exact ⟨rfl, rfl, rfl⟩
  have zk : Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15 :=
    ⟨(congrArg Gprs.r13 hg₃).trans ((congrArg Gprs.r13 hg₂).trans g1k.1),
      (congrArg Gprs.r14 hg₃).trans ((congrArg Gprs.r14 hg₂).trans g1k.2.1),
      (congrArg Gprs.r15 hg₃).trans ((congrArg Gprs.r15 hg₂).trans g1k.2.2)⟩
  have ta1 : (X.cpu.gpr.rsp - 8 - 8 - 8 + 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    have := tadd8 (a := X.cpu.gpr.rsp - 8 - 8 - 8) (by omega)
    omega
  have ta2 : (X.cpu.gpr.rsp - 8 - 8 - 8 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by
    have := tadd8 (a := X.cpu.gpr.rsp - 8 - 8 - 8 + 8) (by omega)
    omega
  have hx2 : rdq(V₂, X.cpu.gpr.rdi + 8#64) = rdq(V, X.cpu.gpr.rdi + 8#64) :=
    congrArg (ofBytesLE 64) (rd_out h2o (by omega) (by unfold Sep at htd; omega))
  -- to the `ret`
  refine (c_25 prof).run c hin (P95 Z.cpu.gpr V₂) hK₃ hA₃ hr₃
    (vc_25 (by rw [zb]; exact offF (d := 8) hts (by omega) (by omega))
      (by rw [zsp]; exact fun i hi => c.hws _ (offF (d := 8) hst (by omega) (by omega) i hi))
      (by rw [zr12]; exact hns) (by rw [zbp]; exact hft)
      (by rw [zsp]; exact fun i hi => c.hws _ (offF (d := 16) hst (by omega) (by omega) i hi))
      (by rw [zsp]; exact fun i hi => c.hws _ (offF (d := 24) hst (by omega) (by omega) i hi))) ?_
  rintro j g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₅]
    show Z.cpu.gpr.rsp + 8 + 8 + 8 = _
    rw [zsp]
    simp only [BitVec.sub_add_cancel]
  have g5b : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₅]
    show rdq(V₂, Z.cpu.gpr.rsp) = _
    rw [zsp]
    exact h2b
  have g5p : Y₅.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hg₅]
    show rdq(V5 Z.cpu.gpr V₂, Z.cpu.gpr.rsp + 8) = _
    unfold Sep at hfd hnd
    rw [zsp, BitVec.sub_add_cancel]
    simp only [V5, zr12, zbp]
    rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega)]
    exact h2p
  have g5c : Y₅.cpu.gpr.r12 = X.cpu.gpr.r12 := by
    rw [hg₅]
    show rdq(V5 Z.cpu.gpr V₂, Z.cpu.gpr.rsp + 8 + 8) = _
    unfold Sep at hfd hnd
    rw [zsp]
    simp only [BitVec.sub_add_cancel, V5, zr12, zbp]
    rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega)]
    exact h2c
  have hret : rdq(V5 Z.cpu.gpr V₂, X.cpu.gpr.rsp) = e₂.add j₂ := by
    unfold Sep at hfd hnd
    simp only [V5, zr12, zbp]
    rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega), ← hra]
    exact congrArg (ofBytesLE 64) (rd_out h2o (by omega) (by omega))
  have hfr : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      ¬ (X.cpu.gpr.rdx.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdx.toNat + 4) →
      ¬ (X.cpu.gpr.rsi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsi.toNat + 8) → V5 Z.cpu.gpr V₂ a = V a := by
    intro a h1 h2 h3
    simp only [V5, zr12, zbp]
    rw [vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega)]
    exact h2o a h1
  have hftv : rdq(V5 Z.cpu.gpr V₂, X.cpu.gpr.rsi) =
      ftV rdq(V, X.cpu.gpr.rdi) + rdq(V, X.cpu.gpr.rdi + 8#64) / 100#64 := by
    simp only [V5, zr12, zbp, zb, zax, hR1, hx2]
    rw [vs (by ln) (by omega), ofBytesLE_toBytesLE (n := 8) rfl, (m100_eq _).2]
    exact BitVec.add_comm _ _
  have hnsv : rdd(V5 Z.cpu.gpr V₂, X.cpu.gpr.rdx) = (rdq(V, X.cpu.gpr.rdi + 8#64) % 100#64).setWidth 32 := by
    unfold Sep at hnf
    simp only [V5, zr12, zbp, zb, hx2]
    rw [vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega), ofBytesLE_toBytesLE (n := 4) rfl,
      (m100_eq _).1]
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_95 _) (by rw [hsp₅]; exact hl) hin₂ h₂
    (by rw [hsp₅]; exact hret) ?_
  rintro Z' t₆ hKZ hAZ ⟨hrZ, hgZ⟩
  have g5k : Y₅.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₅.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₅.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₅]
    exact zk
  refine k _ Z' t₆ hKZ hAZ hfr hftv hnsv hrZ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgZ]
    show Y₅.cpu.gpr.rsp + 8 = _
    rw [hsp₅]
    rfl
  · rw [hgZ]
    exact g5b
  · rw [hgZ]
    exact g5p
  · rw [hgZ]
    exact g5c
  · rw [hgZ]
    exact g5k.1
  · rw [hgZ]
    exact g5k.2.1
  · rw [hgZ]
    exact g5k.2.2

end FV7z.Fft
