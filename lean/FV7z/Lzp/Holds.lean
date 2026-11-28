import FV7z.Lzp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `LzFindPrepare ()` (PLAN.md §M, M1)

7-Zip 26.06's `LzFindPrepare ()` at `0x427de0` in `7zzs` (`C/LzFind.c`; `objdump -d`), `S` the entry's `rsp`:
`sub rsp, 8`, the first CPU test (`call` at 8 to `0x424390`); back at 13 `mov r8d, eax; xor eax, eax;
test r8d, r8d; jne`: if its `eax` is 0, `g_LzFind_GetMatchesSpec` (`0x7967a0`) = 0, `add rsp, 8`, the `ret` (34);
else the second CPU test (`call` at 40 to `0x4244b0`), and back at 45 the pointer = `0x425150` if its `eax` is not 0,
else `0x4251b0` (`lea; test; lea; cmovne`), `add rsp, 8`, the `ret` (76).

The callees are hypotheses, as in `FV7z/Aui/Holds.lean`: each a continuation at its entry (`kf1`, `kf2`), given the
run from its return, `rsp` 8 below the entry's and the return address left as it was; `Pc1`, `Pc2` are what they
leave. The store is to a fixed address apart from the return address (`hd`).

- `gC`, `g40`: the registers at the two `call`s; `fsel`: the pointer stored after the second test.
- `vc_0`, `vc_13z`, `vc_13n`, `vc_45z`, `vc_45n`: the pieces from the entry, from 13 and from 45 (`eax` 0 or not).
- `lzp_ok`: through the first test, the store of 0 to the return address (`kr1`), or through both tests and the
  store of `fsel` (`kr2`), `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lzp

/-- The first CPU test. -/
abbrev cpu1_at : Addr := 0x424390

/-- The second CPU test. -/
abbrev cpu2_at : Addr := 0x4244b0

/-- The first `call`. -/
def pc1 : List Byte := [0xe8, 0xa3, 0xc5, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709536675] 5) := by dec_rfl
theorem wc_8 : pc1 <+: lzp.drop 8 := by decide +kernel
theorem call_8 (feat : Features) : Dec feat lzp 8 (FV7z.mk .call 64 [.rel 18446744073709536675] 5) :=
  Dec.shift (j := 8) (k := 0) (pc1_0 feat) wc_8 (Nat.zero_le _)
theorem tgt_8 : lzp_at.add (8 + 5) + BitVec.ofNat 64 18446744073709536675 = cpu1_at := by decide

/-- The second `call`. -/
def pc2 : List Byte := [0xe8, 0xa3, 0xc6, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709536931] 5) := by dec_rfl
theorem wc_40 : pc2 <+: lzp.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat lzp 40 (FV7z.mk .call 64 [.rel 18446744073709536931] 5) :=
  Dec.shift (j := 40) (k := 0) (pc2_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : lzp_at.add (40 + 5) + BitVec.ofNat 64 18446744073709536931 = cpu2_at := by decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_34 : pret <+: lzp.drop 34 := by decide +kernel
theorem ret_34 (feat : Features) : Dec feat lzp 34 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 34) (k := 0) (pret_0 feat) w_34 (Nat.zero_le _)
theorem w_76 : pret <+: lzp.drop 76 := by decide +kernel
theorem ret_76 (feat : Features) : Dec feat lzp 76 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 76) (k := 0) (pret_0 feat) w_76 (Nat.zero_le _)

/-! ## The frame -/

/-- The registers at the first `call`: `rsp` 8 lower. -/
abbrev gC (g : Gprs) : Gprs := { g with rsp := g.rsp - 8#64 }

/-- The registers at the second `call`: `r8d` = the first test's `eax`, `rax` = 0. -/
abbrev g40 (g : Gprs) : Gprs := { g with r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax), rax := 0#64 }

/-- The pointer stored after the second test (its `eax` in `r`). -/
def fsel (r : BitVec 64) : BitVec 64 := if r.setWidth 32 = 0#32 then 4346288#64 else 4346192#64

theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := BitVec.sub_add_cancel _ _
theorem gT : (7956384#64 : Addr).toNat = 7956384 := by decide

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 8 (gC g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC] at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

/-- Back from the first test with `eax` 0: the pointer = 0, `add rsp, 8`, to the `ret` at 34. -/
theorem vc_13z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 = 0#32)
    (hw : ∀ i < 8, Foot Wl (Addr.add 7956384#64 i))
    (h : ∀ fl, Q 34 { g with
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax), rax := 0#64, rsp := g.rsp + 8#64 } fl
      (Vst V 7956384#64 (toBytesLE 0#64 8))) :
    W_13 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_13, W_23, o1, o2, Op.sta, e, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact hw | exact trivial | apply And.intro | intro _)

/-- Back from the first test with `eax` not 0: to the second `call` at 40. -/
theorem vc_13n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 ≠ 0#32)
    (h : ∀ fl, Q 40 (g40 g) fl V) : W_13 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g40] at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_13, o1, e, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact trivial | apply And.intro | intro _)

/-- Back from the second test with `eax` 0: the pointer = `0x4251b0`, `add rsp, 8`, to the `ret` at 76. -/
theorem vc_45z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 = 0#32)
    (hw : ∀ i < 8, Foot Wl (Addr.add 7956384#64 i))
    (h : ∀ fl, Q 76 { g with rdx := 4346192#64, rax := 4346288#64, rsp := g.rsp + 8#64 } fl
      (Vst V 7956384#64 (toBytesLE 4346288#64 8))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_45, o3, Op.cmov64, Op.sta, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact hw | exact trivial | apply And.intro | intro _)

/-- Back from the second test with `eax` not 0: the pointer = `0x425150`, `add rsp, 8`, to the `ret` at 76. -/
theorem vc_45n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : g.rax.setWidth 32 ≠ 0#32)
    (hw : ∀ i < 8, Foot Wl (Addr.add 7956384#64 i))
    (h : ∀ fl, Q 76 { g with rdx := 4346192#64, rax := 4346192#64, rsp := g.rsp + 8#64 } fl
      (Vst V 7956384#64 (toBytesLE 4346192#64 8))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_45, o3, Op.cmov64, Op.sta, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, false_implies, true_implies, implies_true]
  all_goals repeat' (first | exact h _ | exact hw | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzFindPrepare ()` from its entry, the two CPU tests as hypotheses (`kf1`, `kf2`, each with the return into
`LzFindPrepare` pushed at `S - 16`). If the first's `eax` is 0, the run reaches the return address with 0 stored at
`0x7967a0` (`kr1`); else, through the second, with `fsel` of its `rax` stored (`kr2`); `rsp` = `S + 8`. -/
theorem lzp_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lzp_at lzp)
    {code1 : List Byte} (hin1 : CodeIn L cpu1_at code1) (h1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L cpu2_at code2) (h2 : 0 < code2.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lzp_at)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsp.toNat + 8 ≤ 7956384 ∨ 7956392 ≤ X.cpu.gpr.rsp.toNat)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ i < 8, Foot Wl (Addr.add 7956384#64 i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (lzp_at.add 13) 8)) →
      Y.cpu.rip = cpu1_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = lzp_at.add 13 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 → Pc1 Z V' →
      Z.cpu.gpr.rax.setWidth 32 ≠ 0#32 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 16) (toBytesLE (lzp_at.add 45) 8)) →
      Y.cpu.rip = cpu2_at → Y.cpu.gpr = (g40 Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = lzp_at.add 45 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc1 Z V' →
      Z.cpu.gpr.rax.setWidth 32 = 0#32 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' 7956384#64 (toBytesLE 0#64 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax), rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr2 : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ 7956384#64 (toBytesLE (fsel Z₂.cpu.gpr.rax) 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rdx := 4346192#64, rax := fsel Z₂.cpu.gpr.rax, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have mG : ∀ (W : Addr → Byte) (v : BitVec 64),
      (byteAddrs X.cpu.gpr.rsp 8).map (Vst W 7956384#64 (toBytesLE v 8)) = (byteAddrs X.cpu.gpr.rsp 8).map W :=
    fun W v => Tun.rd_Vst W 7956384#64 (toBytesLE v 8) X.cpu.gpr.rsp 8 (by rw [toBytesLE_length, gT]; omega) hp8
      (by rw [toBytesLE_length, gT]; omega)
  have hrip' : X.cpu.rip = lzp_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 8 ∧ g' = gC X.cpu.gpr ∧ V' = V) hK hA hrip'
    (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hgY]; exact q16 _
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_8 _) hin1 h1 tgt_8 (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from the first test, at 13
  intro Z V' t'' hKZ hAZ hrZ hzs hr' hP1
  by_cases hz : Z.cpu.gpr.rax.setWidth 32 = 0#32
  · -- the pointer = 0, the `ret` at 34
    refine (c_13 prof).run c hin (fun j' g' _ V'' => j' = 34 ∧
        g' = { Z.cpu.gpr with
          r8 := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax), rax := 0#64, rsp := X.cpu.gpr.rsp } ∧
        V'' = Vst V' 7956384#64 (toBytesLE 0#64 8)) hKZ hAZ hrZ
      (vc_13z hz hw fun _ => ⟨rfl, by rw [hzs, sa8], rfl⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_34 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU, mG]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr1 Z V' Z' t₄ hP1 hz hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl
  -- to the second `call`
  refine (c_13 prof).run c hin (fun j' g' _ V'' => j' = 40 ∧ g' = g40 Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
    (vc_13n hz fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by
    rw [hgU]
    show Z.cpu.gpr.rsp - 8 = _
    rw [hzs]
    exact q16 _
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_40 _) hin2 h2 tgt_40 (by rw [hsU]; exact hs2) ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsU] at hA₄
  refine kf2 Z V' hzs hP1 hz U₂ t₄ hK₄ hA₄ hr₄ (by rw [hg₄, hsU, hgU]) ?_
  -- back from the second test, at 45: the pointer, the `ret` at 76
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s qr hP2
  by_cases hz2 : Z₂.cpu.gpr.rax.setWidth 32 = 0#32
  · have hf : fsel Z₂.cpu.gpr.rax = 4346288#64 := by unfold fsel; rw [if_pos hz2]
    refine (c_45 prof).run c hin (fun j' g' _ V₃ => j' = 76 ∧
        g' = { Z₂.cpu.gpr with rdx := 4346192#64, rax := 4346288#64, rsp := X.cpu.gpr.rsp } ∧
        V₃ = Vst V₂ 7956384#64 (toBytesLE 4346288#64 8)) hKZ₂ hAZ₂ hrZ₂
      (vc_45z hz2 hw fun _ => ⟨rfl, by rw [hz2s, sa8], rfl⟩) ?_
    rintro j' g fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
    subst V₃
    have hsU₃ : U₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₃]
    refine c.s_ret hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (ret_76 _) (by rw [hsU₃]; exact hl) hin₂ h₂
      (by rw [hsU₃, mG]; exact qr) ?_
    rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr2 Z₂ V₂ Z' t₇ hP2 hKZ' (by rw [hf]; exact hAZ') hrZ' ?_
    rw [hf, hgZ', hgU₃]
    try rfl
  · have hf : fsel Z₂.cpu.gpr.rax = 4346192#64 := by unfold fsel; rw [if_neg hz2]
    refine (c_45 prof).run c hin (fun j' g' _ V₃ => j' = 76 ∧
        g' = { Z₂.cpu.gpr with rdx := 4346192#64, rax := 4346192#64, rsp := X.cpu.gpr.rsp } ∧
        V₃ = Vst V₂ 7956384#64 (toBytesLE 4346192#64 8)) hKZ₂ hAZ₂ hrZ₂
      (vc_45n hz2 hw fun _ => ⟨rfl, by rw [hz2s, sa8], rfl⟩) ?_
    rintro j' g fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
    subst V₃
    have hsU₃ : U₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₃]
    refine c.s_ret hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (ret_76 _) (by rw [hsU₃]; exact hl) hin₂ h₂
      (by rw [hsU₃, mG]; exact qr) ?_
    rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr2 Z₂ V₂ Z' t₇ hP2 hKZ' (by rw [hf]; exact hAZ') hrZ' ?_
    rw [hf, hgZ', hgU₃]
    try rfl

end FV7z.Lzp
