import FV7z.Fni.Cuts
import FV7z.Lemmas.RepCmpsb
import FV7z.Fre.Blocks
/-!
# `fini` of `dlerror.c` (PLAN.md §M, M1)

glibc 2.31's `fini` at `0x41c0f0` in `7zzs` (`dlfcn/dlerror.c`, `check_free (&last_result)`; `objdump -d`): the
message of the last error, `last_result.errstring` (the qword at `0x7a4c18`, `ers`), is freed and cleared unless it
is null or the static "out of memory" (the 14 bytes at `0x6d945c`, `oom`). The strings are compared by
`repz cmpsb` (31, `Seg.s_repz_cmpsb`): a byte of the message is read only while the earlier ones agree.

- `vc_0z`, `vc_0nz`, `vc_33e`, `vc_33n`, `vc_52`: the verification conditions of the pieces;
- `fni_ok`: from the entry to the return address, the bytes as they were (`k0`, null or "out of memory"), or to
  `free`'s entry (`Fre.fre_at`) with `rdi` the message, the return address 52 pushed (`kf`);
- `fni_ret`: from 52, after `free`, to the return address with `errstring` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fni

/-- `repz cmps byte [rsi], byte es:[rdi]`. -/
def pcmps : List Byte := [0xf3, 0xa6]
theorem pcmps_0 : ∀ feat, Dec feat pcmps 0 (repzCmpsb 2) := by dec_rfl
theorem w_31 : pcmps <+: fni.drop 31 := by decide +kernel
theorem cmps_31 (feat : Features) : Dec feat fni 31 (repzCmpsb 2) :=
  Dec.shift (j := 31) (k := 0) (pcmps_0 feat) w_31 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_42 : pret <+: fni.drop 42 := by decide +kernel
theorem ret_42 (feat : Features) : Dec feat fni 42 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 42) (k := 0) (pret_0 feat) w_42 (Nat.zero_le _)
theorem w_64 : pret <+: fni.drop 64 := by decide +kernel
theorem ret_64 (feat : Features) : Dec feat fni 64 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 64) (k := 0) (pret_0 feat) w_64 (Nat.zero_le _)

/-- The call of `free`. -/
def pcall : List Byte := [0xe8, 0x2c, 0x76, 0x21, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 2193964] 5) := by dec_rfl
theorem w_47 : pcall <+: fni.drop 47 := by decide +kernel
theorem call_47 (feat : Features) : Dec feat fni 47 (FV7z.mk .call 64 [.rel 2193964] 5) :=
  Dec.shift (j := 47) (k := 0) (pcall_0 feat) w_47 (Nat.zero_le _)

/-- `last_result.errstring`. -/
abbrev ers (V : Addr → Byte) : Addr := ofBytesLE 64 ((byteAddrs 8014872#64 8).map V)
/-- The static "out of memory". -/
abbrev oom : Addr := 7181404#64

/-- The registers a call keeps. -/
abbrev Keep (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15
/-- Returned: the return address popped, the registers a call keeps as they were. -/
abbrev Back (g g' : Gprs) : Prop := g'.rsp = g.rsp + 8#64 ∧ Keep g g'

/-- `setcc r8` or `sbb r8, x` and then the low byte read back. -/
theorem lo8_wr (x : BitVec 64) (v : BitVec 8) :
    BitVec.setWidth 8 (x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| BitVec.setWidth 64 v <<< 0) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- `seta al; sbb al, 0` after equal bytes, a first byte above and below. -/
theorem sb_e : BitVec.setWidth 8 (BitVec.ofBool false) - BitVec.ofNat 8 0 - BitVec.setWidth 8 (BitVec.ofBool false) =
    0#8 := by decide
theorem sb_gt : BitVec.setWidth 8 (BitVec.ofBool true) - BitVec.ofNat 8 0 - BitVec.setWidth 8 (BitVec.ofBool false) =
    1#8 := by decide
theorem sb_lt : BitVec.setWidth 8 (BitVec.ofBool false) - BitVec.ofNat 8 0 - BitVec.setWidth 8 (BitVec.ofBool true) =
    255#8 := by decide

theorem sub8_8 (a : Addr) : a - 8#64 - 8 = a - 16#64 := by bv_omega
theorem add8_8 (a : Addr) : a + 8#64 + 8 = a + 16#64 := by bv_omega
theorem add8_add (a : Addr) (i : Nat) : Addr.add (a + 8#64) i = Addr.add a (8 + i) := by
  simp only [Addr.add]
  bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- A null message: `r8` = 0, to the `ret` (42). -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 8, Foot F.data (Addr.add 8014872#64 i))
    (h : ofBytesLE 64 ((byteAddrs 8014872#64 8).map V) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 42 ∧ g' = { g with r8 := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only
  wpx [W_0, W_16, o0, o1, Op.lda, BitVec.and_self, h, beq_self_eq_true, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true]
  all_goals repeat' (first | exact rfl | exact trivial | exact hl | apply And.intro | intro _)

/-- Not null: `rcx` = 14, `rsi` = `r8` = the message, `rdi` = "out of memory", to the `repz cmpsb` (31). -/
theorem vc_0nz {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 8, Foot F.data (Addr.add 8014872#64 i))
    (h : ofBytesLE 64 ((byteAddrs 8014872#64 8).map V) ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 31 ∧
      g' = { g with rcx := 14#64, rsi := ofBytesLE 64 ((byteAddrs 8014872#64 8).map V), rdi := 7181404#64,
        r8 := ofBytesLE 64 ((byteAddrs 8014872#64 8).map V) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only
  have hz : (ofBytesLE 64 ((byteAddrs 8014872#64 8).map V) == 0) = false := beq_eq_false_iff_ne.2 h
  wpx [W_0, W_16, o0, o1, Op.lda, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies,
    implies_true, show BitVec.setWidth 64 14#32 = 14#64 from by decide]
  all_goals repeat' (first | exact rfl | exact trivial | exact hl | apply And.intro | intro _)

/-- After the `repz cmpsb`, the strings equal: `al` 0, to the `ret` (42). -/
theorem vc_33e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : f.zf = true) (hc : f.cf = false) :
    W_33 F Wl (fun j' g' _ V' => j' = 42 ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only
  wpx [W_33, W_43, o2, o3, Op.setcc, Op.sbb8, lo8_wr, BitVec.and_self, hz, hc, Bool.or_true, Bool.true_or,
    Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, sb_e, sb_gt, sb_lt]
  all_goals repeat' (first | exact rfl | exact trivial | exact ⟨_, rfl⟩ | (intro h; exact absurd h (by decide)) |
    apply And.intro | intro _)

/-- After the `repz cmpsb`, a byte that differs: `al` not 0, `rax` pushed, `rdi` = the message, to the call of
`free` (47). -/
theorem vc_33n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : f.zf = false)
    (hpw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8#64) i)) :
    W_33 F Wl (fun j' g' _ V' => j' = 47 ∧ ∃ a, g' = { g with rax := a, rsp := g.rsp - 8#64, rdi := g.r8 } ∧
      V' = Vst V (g.rsp - 8#64) (toBytesLE a 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hpw ⊢
  cases hc : f.cf
  all_goals wpx [W_33, W_43, o2, o3, Op.setcc, Op.sbb8, lo8_wr, BitVec.and_self, hz, hc, Bool.or_true,
    Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, sb_e, sb_gt, sb_lt]
  all_goals repeat' (first | exact rfl | exact trivial | exact hpw | exact ⟨_, rfl, rfl⟩ |
    (intro h; exact absurd h (by decide)) | apply And.intro | intro _)

/-- After `free`: `errstring` = 0, `pop rdx`, to the `ret` (64). -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hpw : ∀ i < 8, Foot Wl (Addr.add 8014872#64 i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_52 F Wl (fun j' g' _ V' => j' = 64 ∧ (∃ d, g' = { g with rsp := g.rsp + 8#64, rdx := d }) ∧
      V' = Vst V 8014872#64 (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  wpx [W_52, o4, Op.stia]
  all_goals repeat' (first | exact rfl | exact trivial | exact hpw | exact hl | exact ⟨_, rfl⟩ | apply And.intro |
    intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `fini ()` from its entry: a null message or "out of memory" (the first 14 bytes equal), at the return address with
the bytes as they were (`k0`); else at `free`'s entry with `rdi` the message, `rax` pushed and the return address 52
below it (`kf`). A byte of the message is read only while the earlier ones are those of "out of memory". -/
theorem fni_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fni_at fni) (hinF : CodeIn L Fre.fre_at Fre.fre)
    (hdf : s₀.cpu.rflags.df = false) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = fni_at) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (hle : ∀ i < 8, Foot F.data (Addr.add 8014872#64 i)) (hlm : ∀ i < 14, Foot F.data (Addr.add oom i))
    (hls : ers V ≠ 0 → ∀ i < 14, SameB V (ers V) oom i → Foot F.data ((ers V).add i))
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8#64) i))
    (hs16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16#64) i))
    (k0 : (ers V = 0 ∨ SameB V (ers V) oom 14) → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t')
    (kf : ers V ≠ 0 → ¬ SameB V (ers V) oom 14 → ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8#64) (toBytesLE a 8)) (X.cpu.gpr.rsp - 16#64)
        (toBytesLE (fni_at.add (47 + 5)) 8)) →
      Y.cpu.rip = Fre.fre_at → Y.cpu.gpr.rdi = ers V → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 →
      Keep X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = fni_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hz : ers V = 0
  · -- null: the `ret`
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hle hz) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; all_goals rfl
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_42 _) (fun i hi => by rw [hsp]; exact hl i hi) hin₂ h₂
      (by rw [hsp]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k0 (Or.inl hz) Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  -- not null: the `repz cmpsb`
  refine (c_0 prof).run c hin _ hK hA hrip' (vc_0nz hle hz) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsi : Y₁.cpu.gpr.rsi = ers V := by rw [hg₁]; all_goals rfl
  have hdi : Y₁.cpu.gpr.rdi = oom := by rw [hg₁]; all_goals rfl
  refine c.s_repz_cmpsb hdf hin (lt_len (by decide)) (cmps_31 _) 13 hK₁ hA₁ hr₁ (by rw [hg₁]; all_goals rfl)
    (fun i hi hs => ?_) (fun i hi hs hend => ?_)
  · rw [hsi, hdi] at hs ⊢
    exact ⟨hls hz i hi hs, hlm i hi⟩
  rw [hsi, hdi] at hs hend
  rintro Z t₂ hK₂ hA₂ ⟨hr₂, hg₂, hf₂⟩
  rw [hsi, hdi] at hf₂
  have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hg₁]; all_goals rfl
  have hr8Z : Z.cpu.gpr.r8 = ers V := by rw [hg₂, hg₁]; all_goals rfl
  have hkZ : Keep X.cpu.gpr Z.cpu.gpr := by rw [hg₂, hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hxy : V ((ers V).add i) = V (oom.add i)
  · -- the 14 bytes equal: the `ret`
    have hi13 : i = 13 := hend.resolve_right fun h => h hxy
    subst hi13
    have hS : SameB V (ers V) oom 14 := fun k hk => by
      by_cases hk' : k < 13
      · exact hs k hk'
      · obtain rfl : k = 13 := by omega
        exact hxy
    refine (c_33 prof).run c hin _ hK₂ hA₂ hr₂
      (vc_33e (by rw [hf₂, subF_zf]; exact decide_eq_true hxy)
        (by rw [hf₂, subF_cf, hxy]; exact decide_eq_false (Nat.lt_irrefl _))) ?_
    rintro j' g₃ fl₃ V₃ ⟨rfl, ⟨a, rfl⟩, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hgY₃ -
    have hsp : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY₃]; exact hspZ
    refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_42 _) (fun i hi => by rw [hsp]; exact hl i hi) hin₂ h₂
      (by rw [hsp]; exact hra) ?_
    rintro Z' t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k0 (Or.inr hS) Z' t₄ hKZ hAZ hrZ ⟨?_, ?_⟩
    · rw [hgZ]
      show Y₃.cpu.gpr.rsp + 8 = _
      rw [hsp]
      all_goals rfl
    · rw [hgZ, hgY₃]
      exact hkZ
  · -- a byte differs: the call of `free`
    refine (c_33 prof).run c hin _ hK₂ hA₂ hr₂
      (vc_33n (by rw [hf₂, subF_zf]; exact decide_eq_false hxy) fun i hi => by rw [hspZ]; exact hs8 i hi) ?_
    rintro j' g₃ fl₃ V₃ ⟨rfl, a, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hgY₃ -
    rw [hspZ] at hA₃
    have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY₃]; exact congrArg (· - 8#64) hspZ
    have hdi₃ : Y₃.cpu.gpr.rdi = ers V := by rw [hgY₃]; exact hr8Z
    refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_47 _) hinF (Fre.lt_len (j := 0) (by decide))
      (by decide) (fun i hi => by rw [hsp₃, sub8_8]; exact hs16 i hi) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hsp₃, sub8_8] at hA₄
    refine kf hz (fun h => hxy (h i (by omega))) a Y₄ t₄ hK₄ hA₄ hr₄ ?_ ?_ ?_
    · rw [hg₄]
      exact hdi₃
    · rw [hg₄]
      show Y₃.cpu.gpr.rsp - 8 = _
      rw [hsp₃, sub8_8]
    · rw [hg₄, hgY₃]
      exact hkZ

/-- `fini` from 52, after `free` returned: `errstring` 0, `pop rdx` and the `ret`, at the return address 16 bytes up,
the registers a call keeps as they were. -/
theorem fni_ret (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fni_at fni) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fni_at.add 52)
    (hpw : ∀ i < 8, Foot Wl (Addr.add 8014872#64 i)) (hl : ∀ i < 16, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp + 8#64) 8).map (Vst V 8014872#64 (toBytesLE 0#64 8))) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vst V 8014872#64 (toBytesLE 0#64 8)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 16#64 → Keep X.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_52 prof).run c hin _ hK hA hrip (vc_52 hpw fun i hi => hl i (by omega)) ?_
  rintro j' g fl V' ⟨rfl, ⟨d, rfl⟩, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 := by rw [hg₁]; all_goals rfl
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_64 _) (fun i hi => ?_) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  · rw [hsp, add8_add]
    exact hl (8 + i) (by omega)
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₂ hKZ hAZ hrZ ?_ ?_
  · rw [hgZ]
    show Y₁.cpu.gpr.rsp + 8 = _
    rw [hsp, add8_8]
  · rw [hgZ, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.Fni
