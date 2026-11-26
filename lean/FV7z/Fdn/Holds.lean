import FV7z.Fdn.Cuts
import FV7z.Mls.Blocks1
import FV7z.Sst.Holds
import FV7z.Raf.Holds
/-!
# `NWindows::NFile::NFind::CFileInfo::Find_DontFill_Name` (PLAN.md §M, M1)

7-Zip 26.06's `CFileInfo::Find_DontFill_Name (path, followLink)` at `0x455b00` in `7zzs`
(`CPP/Windows/FileFind.cpp`; `objdump -d`), `this` = `rdi`, `S` the stack pointer at the entry: two pushes (`r12`,
`rbp`, `P2`), `rbp` = `this`, a frame of 168 bytes (`aQ S` = `S - 184`) with the stack guard (`fs:0x28`) at
`aQ S + 152` (`Vo`), the `struct stat` at `aQ S` (`r12`); `MY_lstat (path, &st, followLink)` (`Mls.mls_at`, call
at 48, registers `aG`); back at 53 (`R` the stack pointer there): when its answer (`eax`) is not 0, `eax` = 0; else
`SetFrom_stat (st)` on `this` (`Sst.sst_ok`, call at 69, back at 74) and `eax` = 1; the stack guard checked, the
frame dropped, the two pops, the `ret` (108).

- `M_out`: `SetFrom_stat`'s stores stay in the object's 104 bytes;
- `fdn_call`: from the entry to `MY_lstat`'s entry, the return address `fdn_at + 53` below the frame;
- `fdn_ret`: from 53 to the return address: `rax` 0 (`k0`) or, `SetFrom_stat` run, 1 (`k1`).

Not covered: the stack guard failing (`__stack_chk_fail`, 109).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fdn

theorem fdn_48 : ∀ feat, Dec feat fdn 48 (FV7z.mk .call 64 [.rel 18446744073709550955] 5) := by intro feat f; rfl
theorem fdn_69 : ∀ feat, Dec feat fdn 69 (FV7z.mk .call 64 [.rel 18446744073709551238] 5) := by intro feat f; rfl
theorem fdn_108 : ∀ feat, Dec feat fdn 108 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-! ## `SetFrom_stat`'s stores -/

/-- The stores of `Sst.M` stay in the 104 bytes at `p`. -/
theorem M_out {V : Addr → Byte} {s p z : BitVec 64} {m : BitVec 32} {b1 b2 b3 : List Byte} (h1 : b1.length = 16)
    (h2 : b2.length = 16) (h3 : b3.length = 16) (hp : p.toNat + 104 ≤ 2 ^ 64) :
    Raf.Out p.toNat (p.toNat + 104) V (Sst.M V s p z m b1 b2 b3) := by
  have w : ∀ {U : Addr → Byte} {k n : Nat} {bs : List Byte}, bs.length = n → k < 104 ∧ k + n ≤ 104 →
      Raf.Out p.toNat (p.toNat + 104) U (Vst U (p + BitVec.ofNat 64 k) bs) := by
    intro U k n bs hn ⟨hk, hkn⟩
    have q : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact (Raf.Out.vst hn (by omega)).mono (by omega) (by omega)
  have w0 : ∀ {U : Addr → Byte} {bs : List Byte}, bs.length = 8 →
      Raf.Out p.toNat (p.toNat + 104) U (Vst U p bs) := fun hn =>
    (Raf.Out.vst hn (by omega)).mono (Nat.le_refl _) (by omega)
  dsimp only [Sst.M]
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w h3 (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w h2 (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w (toBytesLE_length _ _) (by decide))
  refine Raf.Out.trans ?_ (w h1 (by decide))
  exact w0 (toBytesLE_length _ _)

/-! ## The frame -/

/-- The stack pointer after the two pushes and `sub rsp, 168`. -/
abbrev aQ (S : Addr) : Addr := S - 8 - 8 - 168#64

/-- The bytes after the two `push`es. -/
abbrev P2 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)

/-- The bytes at `MY_lstat`'s call: the stack guard `cn` stored at `aQ S + 152`. -/
abbrev Vo (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (P2 V g) (aQ g.rsp + 152#64) (toBytesLE cn 8)

/-- At `MY_lstat`'s call: `rax` 0, `edx` the byte `followLink` (`dl`), `rbp` = `this`, `rdi` = `path`, `rsi` and
`r12` the `struct stat` (`rsp`). -/
abbrev aG (g : Gprs) : Gprs :=
  { g with
    rax := 0#64
    rdx := ((g.rdx.setWidth 8).setWidth 32).setWidth 64
    rsp := aQ g.rsp
    rbp := g.rdi
    rsi := aQ g.rsp
    rdi := g.rsi
    r12 := aQ g.rsp }

/-- The bytes at `SetFrom_stat`'s entry, from those at 53: the return address `fdn_at + 74` below `rsp`. -/
abbrev V74 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE (fdn_at.add 74) 8)

/-- The bytes after `SetFrom_stat (st)` on `this` (`rbp`), `st` at `r12`, from those at 53. -/
abbrev Mf (V : Addr → Byte) (g : Gprs) (b1 b2 b3 : List Byte) : Addr → Byte :=
  Sst.M (V74 V g) g.r12 g.rbp (Sst.sz (V74 V g) g.r12) rdd(V74 V g, g.r12 + 24#64) b1 b2 b3

/-- The registers kept from `g` to `g'`. -/
def K4 (g g' : Gprs) : Prop := g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem s1 : BitVec.setWidth 64 1#32 = 1#64 := by decide
theorem pa2 (S : Addr) : S + 168#64 + 8 + 8 = S + 184#64 := by bv_omega
theorem pa3 (S : Addr) : S + 168#64 + 8 + 8 + 8 = S + 192#64 := by bv_omega
theorem pa1 (S : Addr) : S + 168#64 + 8 = S + 176#64 := by bv_omega

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry to the first call: the pushes, the frame, the stack guard stored. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64}
    (hcn : rdq(P2 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aQ g.rsp + 152#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 48 ∧ g' = aG g ∧ V' = Vo V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vo, P2, aQ, aG] at hcn w1 w2 wc ⊢
  wpx [W_0, o0, Op.ldf, Op.zxr, hcn, xz, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies,
    implies_true]
  all_goals vfin

/-- From 53, `MY_lstat`'s answer not 0: `eax` 0, to 79. -/
theorem vc_53n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_53 fb F Wl (fun j' g' _ V' => j' = 79 ∧ (∃ rr, g' = { g with rax := 0#64, r8 := rr }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_53, W_63, o1, o2, xz, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-- From 53, `MY_lstat`'s answer 0: `rsi` the `struct stat` (`r12`), `rdi` = `this` (`rbp`), to the call at 69. -/
theorem vc_53z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 = 0#32) :
    W_53 fb F Wl (fun j' g' _ V' => j' = 69 ∧
      (∃ rr, g' = { g with rax := 0#64, rsi := g.r12, rdi := g.rbp, r8 := rr }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_53, W_63, o1, o2, xz, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-- 74: `eax` = 1, to 79. -/
theorem vc_74 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_74 fb F Wl (fun j' g' _ V' => j' = 79 ∧ g' = { g with rax := 1#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_74, o3, s1]
  all_goals vfin

/-- From 79: the stack guard checked, the frame dropped, the two pops, to the `ret` (108). -/
theorem vc_79 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 152#64) = rdq(V, fb + 40#64)) (f152 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 152#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64 + 8) i)) :
    W_79 fb F Wl (fun j' g' _ V' => j' = 108 ∧
      (∃ rc, g' = { g with
        rcx := rc
        rbp := rdq(V, g.rsp + 168#64)
        r12 := rdq(V, g.rsp + 168#64 + 8)
        rsp := g.rsp + 168#64 + 8 + 8 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f152 p1 p2 ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_79, W_98, o4, o5, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `Find_DontFill_Name (path, followLink)` from its entry, the stack guard's 8 bytes at `fs:0x28` readable, the
pushes' slots, the guard's slot and the call's return address's slot in what the run may store into: at
`MY_lstat`'s entry with the registers `aG`, the pushes and the stack guard (as read after the pushes) stored (`Vo`)
and the return address `fdn_at + 53` below the frame. -/
theorem fdn_call {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fdn_at fdn)
    (hinM : CodeIn L Mls.mls_at Mls.mls) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = fdn_at) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 152#64) i))
    (wr : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (fdn_at.add 53) 8)) →
      Y.cpu.rip = Mls.mls_at → Y.cpu.gpr = (aG X.cpu.gpr).set 4 (aQ X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 48 ∧ g' = aG X.cpu.gpr ∧
      V' = Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl w1 w2 hcl wc) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (fdn_48 _) hinM (Mls.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact wr) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From 79 to the return address (at `rsp + 184`): `rbp`, `r12` popped from `rsp + 168`, `rsp + 176`, `rax` and the
registers `K4` as at 79, `rsp` 192 above. -/
theorem fdn_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fdn_at fdn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fdn_at.add 79)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f152 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 152#64) i))
    (f168 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 168#64) i))
    (f176 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 176#64) i))
    (f184 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 184#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 184#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 192#64 → Z.cpu.gpr.rax = X.cpu.gpr.rax →
      Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 168#64) → Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 176#64) →
      K4 X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_79 prof fb).run c hfs hin _ hK hA hrip
    (vc_79 (g := X.cpu.gpr) hc f152 hcl f168 (by rw [pa1]; exact f176)) ?_
  rintro j' g fl V₃ ⟨rfl, ⟨rc, rfl⟩, rfl⟩ Y t₃ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 168#64 + 8 + 8 := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (fdn_108 _) (by rw [hsY, pa2]; exact f184) hin₂ h₂
    (by rw [hsY, pa2]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₄ hKZ hAZ hrZ (by rw [hgZ]; show Y.cpu.gpr.rsp + 8 = _; rw [hsY, pa3]) (by rw [hgZ, hgY]; try rfl)
    (by rw [hgZ, hgY]; try rfl) (by rw [hgZ, hgY, ← pa1]; try rfl) ?_
  rw [hgZ, hgY]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem tA (x : Addr) (k : Nat) (hk : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tS (x : Addr) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega

/-- `Find_DontFill_Name` from the return of `MY_lstat` (53), `R` = `rsp`: the stack guard at `R + 152` the one at
`fs:0x28`, the return address at `R + 184`; the `struct stat` (`r12`) and `this` (`rbp`, its 104 bytes apart from
`R - 8` … `R + 192` and from the stack guard) as `Sst.sst_ok` needs them. At the return address with `rsp` = `R + 192`,
`rbp`, `r12` popped, the registers `K4` as they were: `MY_lstat`'s answer not 0, `rax` 0 and the bytes as at 53
(`k0`); else `rax` 1 and the bytes after `SetFrom_stat` (`Mf`, for some times' bytes `b1`, `b2`, `b3`; `k1`). -/
theorem fdn_ret {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fdn_at fdn)
    (hinS : CodeIn L Sst.sst_at Sst.sst) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = fdn_at.add 53) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64) (hR : 8 ≤ X.cpu.gpr.rsp.toNat)
    (hRb : X.cpu.gpr.rsp.toNat + 192 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (w8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (l8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i))
    (f152 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 152#64) i))
    (f168 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 168#64) i))
    (f176 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 176#64) i))
    (f184 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 184#64) i))
    (hr : Sst.Rs F X.cpu.gpr.r12) (hw : Sst.Ws Wl X.cpu.gpr.rbp) (hp : X.cpu.gpr.rbp.toNat + 104 ≤ 2 ^ 64)
    (hpd : X.cpu.gpr.rbp.toNat + 104 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 192 ≤ X.cpu.gpr.rbp.toNat)
    (hpc : X.cpu.gpr.rbp.toNat + 104 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rbp.toNat)
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 184#64) = e₂.add j₂)
    (k0 : X.cpu.gpr.rax.setWidth 32 ≠ 0#32 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 192#64 →
      Z.cpu.gpr.rax = 0#64 → Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 168#64) →
      Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 176#64) → K4 X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t')
    (k1 : X.cpu.gpr.rax.setWidth 32 = 0#32 → ∀ (b1 b2 b3 : List Byte), b1.length = 16 → b2.length = 16 →
      b3.length = 16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Mf V X.cpu.gpr b1 b2 b3) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 192#64 → Z.cpu.gpr.rax = 1#64 →
      Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 168#64) → Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 176#64) →
      K4 X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have q152 : (X.cpu.gpr.rsp + 152#64).toNat = X.cpu.gpr.rsp.toNat + 152 := tA _ 152 (by omega)
  have q168 : (X.cpu.gpr.rsp + 168#64).toNat = X.cpu.gpr.rsp.toNat + 168 := tA _ 168 (by omega)
  have q176 : (X.cpu.gpr.rsp + 176#64).toNat = X.cpu.gpr.rsp.toNat + 176 := tA _ 176 (by omega)
  have q184 : (X.cpu.gpr.rsp + 184#64).toNat = X.cpu.gpr.rsp.toNat + 184 := tA _ 184 (by omega)
  have qm8 := tS _ hR
  by_cases hz : X.cpu.gpr.rax.setWidth 32 = 0#32
  · -- `SetFrom_stat`
    refine (c_53 prof fb).run c hfs hin _ hK hA hrip (vc_53z hz) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨rr, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (fdn_69 _) hinS (Sst.lt_len (j := 0) (by decide))
      (by decide) (by rw [hsY]; exact w8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    have hs2 : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₂, hsY]; rfl
    have hi2 : Y₂.cpu.gpr.rsi = X.cpu.gpr.r12 := by rw [hg₂, hgY]; rfl
    have hd2 : Y₂.cpu.gpr.rdi = X.cpu.gpr.rbp := by rw [hg₂, hgY]; rfl
    -- reads apart from the object and from the return address's slot
    have rdM : ∀ (b1 b2 b3 : List Byte), b1.length = 16 → b2.length = 16 → b3.length = 16 → ∀ (x : Addr),
        x.toNat + 8 ≤ 2 ^ 64 →
        x.toNat + 8 ≤ X.cpu.gpr.rbp.toNat ∨ X.cpu.gpr.rbp.toNat + 104 ≤ x.toNat →
        rdq(Mf V X.cpu.gpr b1 b2 b3, x) = rdq(V74 V X.cpu.gpr, x) := fun b1 b2 b3 h1 h2 h3 x hx hd =>
      congrArg (ofBytesLE 64) ((M_out h1 h2 h3 hp).rd hx hd)
    have rdV : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
        X.cpu.gpr.rsp.toNat ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 →
        rdq(V74 V X.cpu.gpr, x) = rdq(V, x) := fun x hx hd =>
      congrArg (ofBytesLE 64) (Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (fdn_at.add 74) 8) x 8
        (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega))
    have hMs : ∀ (b1 b2 b3 : List Byte), Sst.Ms (V74 V X.cpu.gpr) Y₂.cpu.gpr b1 b2 b3 = Mf V X.cpu.gpr b1 b2 b3 := by
      intro b1 b2 b3
      dsimp only [Sst.Ms, Mf]
      rw [hi2, hd2]
    refine Sst.sst_ok (j₂ := 74) c hinS hK₂ hA₂ hr₂ (by rw [hi2]; exact hr) (by rw [hd2]; exact hw)
      (by rw [hs2]; exact l8) hin (lt_len (by decide)) ?_ ?_
    · intro b1 b2 b3 h1 h2 h3
      rw [hMs, hs2, rdM b1 b2 b3 h1 h2 h3 (X.cpu.gpr.rsp - 8) (by omega) (by omega)]
      dsimp only [V74]
      rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE (fdn_at.add 74) 8) (toBytesLE_length _ _) (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
    rintro Z t₃ b1 b2 b3 h1 h2 h3 hKZ hAZ hrZ ⟨a, c', d, hgZ⟩
    rw [hMs] at hAZ
    refine (c_74 prof fb).run c hfs hin _ hKZ hAZ hrZ vc_74 ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ W t₄ hKW hAW hrW hgW -
    have hsW : W.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      rw [hgW, hgZ]
      show Y₂.cpu.gpr.rsp + 8 = _
      rw [hs2]
      exact BitVec.sub_add_cancel _ _
    have rd2 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
        x.toNat + 8 ≤ X.cpu.gpr.rbp.toNat ∨ X.cpu.gpr.rbp.toNat + 104 ≤ x.toNat →
        X.cpu.gpr.rsp.toNat ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 →
        rdq(Mf V X.cpu.gpr b1 b2 b3, x) = rdq(V, x) := fun x hx hd hd' =>
      (rdM b1 b2 b3 h1 h2 h3 x hx hd).trans (rdV x hx hd')
    refine fdn_tail c hfs hin hKW hAW hrW hcl (by rw [hsW]; exact f152) (by rw [hsW]; exact f168)
      (by rw [hsW]; exact f176) (by rw [hsW]; exact f184) ?_ hin₂ h₂ ?_ ?_
    · rw [hsW, rd2 (X.cpu.gpr.rsp + 152#64) (by omega) (by omega) (by omega),
        rd2 (fb + 40#64) hcb (by omega) (by omega), hc]
    · rw [hsW, rd2 (X.cpu.gpr.rsp + 184#64) (by omega) (by omega) (by omega)]
      exact hra
    intro Z' t' hKZ' hAZ' hrZ' hsZ' haZ' hbZ' h12' hkZ'
    refine k1 hz b1 b2 b3 h1 h2 h3 Z' t' hKZ' hAZ' hrZ' (by rw [hsZ', hsW]) (by rw [haZ', hgW]; try rfl) ?_ ?_ ?_
    · rw [hbZ', hsW, rd2 (X.cpu.gpr.rsp + 168#64) (by omega) (by omega) (by omega)]
    · rw [h12', hsW, rd2 (X.cpu.gpr.rsp + 176#64) (by omega) (by omega) (by omega)]
    · obtain ⟨k1', k2', k3', k4'⟩ := hkZ'
      rw [hgW, hgZ, hg₂, hgY] at k1' k2' k3' k4'
      exact ⟨k1', k2', k3', k4'⟩
  · -- the answer not 0
    refine (c_53 prof fb).run c hfs hin _ hK hA hrip (vc_53n hz) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨rr, rfl⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine fdn_tail c hfs hin hKY hAY hrY hcl (by rw [hsY]; exact f152) (by rw [hsY]; exact f168)
      (by rw [hsY]; exact f176) (by rw [hsY]; exact f184) (by rw [hsY]; exact hc) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    intro Z t' hKZ hAZ hrZ hsZ haZ hbZ h12 hkZ
    refine k0 hz Z t' hKZ hAZ hrZ (by rw [hsZ, hsY]) (by rw [haZ, hgY]) (by rw [hbZ, hsY]) (by rw [h12, hsY]) ?_
    obtain ⟨k1', k2', k3', k4'⟩ := hkZ
    rw [hgY] at k1' k2' k3' k4'
    exact ⟨k1', k2', k3', k4'⟩

end FV7z.Fdn
