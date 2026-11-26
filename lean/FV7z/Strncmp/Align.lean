import FV7z.Strncmp.Head
import FV7z.Strlen.Entry
/-!
# `__strncmp_sse2`: the alignment (PLAN.md G3, `strncmp`)

From `128` (`align`): both strings' addresses down to 16 bytes, `edx = 0xffff`, `r8d = 0`, `ecx` and `eax` the
offsets of `rsi`'s and `rdi`'s strings in their 16 bytes. The same offsets go on to `192`, the loop of `ashr_0`;
otherwise the strings are swapped when `rsi`'s offset is the smaller (`r8d = 0xffff` then, for the end to swap the
result back), and from `163` (`at163`) the jump by the table at `0x6f0df0` (`ntgt_eq`) goes to the loop at
`400 + 384·j`, `j = 15 - (rsi's offset - rdi's offset)`. `AtL` is what each loop starts from.

- `al_down`, `and15`, `sw3264`, `r9_val`: `and r, -16`, `and r32, 15`, a 32-bit write, the table's index.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem get_r8n (g : Gprs) : g.get (regOf 8) = g.r8 := rfl
theorem get_r9n (g : Gprs) : g.get (regOf 9) = g.r9 := rfl
theorem get_r10n (g : Gprs) : g.get (regOf 10) = g.r10 := rfl
theorem set_r9n (g : Gprs) (v : BitVec 64) : g.set (regOf 9) v = { g with r9 := v } := rfl
theorem set_r10n (g : Gprs) (v : BitVec 64) : g.set (regOf 10) v = { g with r10 := v } := rfl

/-! ## Numbers -/

/-- `and r, -16` of `x + q`, `q` a multiple of 16: aligned, `x`'s offset in its 16 bytes below `x + q`. -/
theorem al_down (x : Addr) {q : Nat} (hq : q % 16 = 0) :
    (x.add q &&& BitVec.ofNat 64 18446744073709551600).toNat % 16 = 0 ∧
      Addr.add (x.add q &&& BitVec.ofNat 64 18446744073709551600) (x.toNat % 16) = x.add q := by
  have h := and_m16' (x.add q)
  have hx := x.isLt
  have e : (x.add q).toNat = (x.toNat + q) % 2 ^ 64 := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  generalize x.add q = s at h e ⊢
  have hs := s.isLt
  generalize s &&& BitVec.ofNat 64 18446744073709551600 = m at h ⊢
  refine ⟨by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `and ecx, 15` of an offset in 64 bytes: the offset in 16 bytes. -/
theorem and15 (b : Addr) :
    ((BitVec.ofNat 64 (b.toNat % 64)).setWidth 32 &&& BitVec.ofNat 32 15).setWidth 64 =
      BitVec.ofNat 64 (b.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have e : ∀ m : Nat, m &&& 15 = m % 16 := fun m => Nat.and_two_pow_sub_one_eq_mod m 4
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, e]
  omega

/-- A 32-bit write of a 32-bit number. -/
theorem sw3264 {v : Nat} (h : v < 2 ^ 32) : ((BitVec.ofNat 64 v).setWidth 32).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem off16_lt (a : Addr) : a.toNat % 16 < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-! ## The table -/

/-- A load of `n` bytes at `a` into a register (as `Memcpy.wpV_ldA`). -/
theorem wpV_ldT {F : Footprint} {Wl : List Rgn} {n : Nat} {ea : Gprs → Addr} {h : Gprs → Rflags → List Byte → Gprs}
    {P : Gprs → Rflags → List Byte → Rflags → Prop} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    {a : Addr} (he : ea g = a) (hf : ∀ i < n, Foot F.data (a.add i))
    (k : ∀ fl, P g f ((byteAddrs a n).map V) fl → wpV F Wl ops Q (h g f ((byteAddrs a n).map V)) fl x V) :
    wpV F Wl (.op (.load n ea h P) :: ops) Q g f x V := by
  subst he; exact ⟨rfl, hf, k⟩

/-- The target of the table's entry `m`: `movsxd r9, dword [r10 + r9·4]; lea r10, [r10 + r9]`. -/
def ntgt (m : Nat) : Addr :=
  (0x6f0df0 : Addr) + (ofBytesLE 32 ((List.range 4).map fun k => ncmpTab.getD (4 * m + k) 0)).signExtend 64 *
    BitVec.ofNat 64 1 + BitVec.ofNat 64 0

/-- Entry `m < 15` goes to the loop at `400 + 384·m`. -/
theorem ntgt_eq : ∀ m < 15, ntgt m = (0x63a420 : Addr).add (400 + 384 * m) := by decide +kernel

theorem tab_ea (m : Nat) :
    (0x6f0df0 : Addr) + BitVec.ofNat 64 m * BitVec.ofNat 64 4 + BitVec.ofNat 64 0 =
      (0x6f0df0 : Addr).add (4 * m) := by
  apply BitVec.eq_of_toNat_eq
  have e : (0x6f0df0 : Addr).toNat = 0x6f0df0 := rfl
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, e]
  omega

theorem tab_bytes {V : Addr → Byte} (hT : NcmpTabV V) {m : Nat} (hm : m < 16) :
    (byteAddrs ((0x6f0df0 : Addr).add (4 * m)) 4).map V =
      (List.range 4).map fun k => ncmpTab.getD (4 * m + k) 0 := by
  simp only [byteAddrs, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  show V (((0x6f0df0 : Addr).add (4 * m)).add i) = _
  rw [addr_add_add, hT _ (by omega)]

/-! ## At a loop -/

/-- At a loop: `rdi` and `rsi` the strings `x` and `y`, `q` bytes in, down to 16 bytes, `rax` and `rcx` their
offsets in their 16 bytes, `r11` the bytes left, `edx = 0xffff`, `r8` `0xffff` just when the strings were
swapped. -/
def AtL (g₀ g : Gprs) (x y : Addr) (n q : Nat) (sw : Bool) : Prop :=
  KpN g₀ g ∧ g.rdi.toNat % 16 = 0 ∧ Addr.add g.rdi (x.toNat % 16) = x.add q ∧ g.rsi.toNat % 16 = 0 ∧
    Addr.add g.rsi (y.toNat % 16) = y.add q ∧ g.r11 = BitVec.ofNat 64 (n - q) ∧
    g.rcx = BitVec.ofNat 64 (y.toNat % 16) ∧ g.rax = BitVec.ofNat 64 (x.toNat % 16) ∧
    g.rdx = BitVec.ofNat 64 65535 ∧ g.r8 = if sw then BitVec.ofNat 64 65535 else 0

theorem AtL.r9 {g₀ g : Gprs} {x y : Addr} {n q : Nat} {sw : Bool} (h : AtL g₀ g x y n q sw) (v : BitVec 64) :
    AtL g₀ (g.set (regOf 9) v) x y n q sw := h

theorem AtL.r10 {g₀ g : Gprs} {x y : Addr} {n q : Nat} {sw : Bool} (h : AtL g₀ g x y n q sw) (v : BitVec 64) :
    AtL g₀ (g.set (regOf 10) v) x y n q sw := h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `163`, `rsi`'s offset the greater: `lea r9, [rax + 15]; sub r9, rcx; lea r10, [rip + table];
movsxd r9, [r10 + r9·4]; lea r10, [r10 + r9]; jmp r10`. -/
theorem at163 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) (he : e' = 0x63a420) (hT : NcmpTabV V)
    (hTf : ∀ i < 64, Foot F.data ((0x6f0df0 : Addr).add i)) {Y : State} {t : Nat} {g₀ : Gprs}
    {x y : Addr} {n q : Nat} {sw : Bool}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 163)
    (hg : AtL g₀ Y.cpu.gpr x y n q sw) (hlt : x.toNat % 16 < y.toNat % 16)
    (K : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e'.add (400 + 384 * (15 + x.toNat % 16 - y.toNat % 16)) → AtL g₀ Z.cpu.gpr x y n q sw →
      GoG prof L o gev gP gE Z t') : GoG prof L o gev gP gE Y t := by
  subst he
  have hX : x.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hY : y.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hcx := hg.2.2.2.2.2.2.1
  have hax := hg.2.2.2.2.2.2.2.1
  -- `lea r9, [rax + 15]; sub r9, rcx`
  refine c.s_blkV hin (b163 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have h9₁ : Y₁.cpu.gpr.r9 = BitVec.ofNat 64 (15 + x.toNat % 16 - y.toNat % 16) := by
    simp only [hg₁, wr, gv, Src.val, eaG, optV, get0, get1, get_r9n, set_r9n, BitVec.setWidth_eq, subR_eq, hax,
      hcx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
      Nat.reducePow, Nat.reduceMod, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    omega
  -- `lea r10, [rip + 0xb691f]`: the table
  refine c.s_lea_rip hK₁ hA₁ hin (lt_scm (by decide)) hr₁ (d170 prof.feat) (v := 0x6f0df0) (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
  have h10₂ : Y₂.cpu.gpr.r10 = 0x6f0df0 := by rw [hg₂]; rfl
  have h9₂ : Y₂.cpu.gpr.r9 = BitVec.ofNat 64 (15 + x.toNat % 16 - y.toNat % 16) := by rw [hg₂]; exact h9₁
  have hm : 15 + x.toNat % 16 - y.toNat % 16 < 15 := by omega
  generalize 15 + x.toNat % 16 - y.toNat % 16 = m at hm h9₂ K
  -- `movsxd r9, dword [r10 + r9·4]; lea r10, [r10 + r9]`
  refine c.s_blkV hin (b177 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_ldT (a := (0x6f0df0 : Addr).add (4 * m)) ?_ (fun i hi => ?_)
    fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  · show Y₂.cpu.gpr.get (regOf 10) + Y₂.cpu.gpr.get (regOf 9) * BitVec.ofNat 64 4 + BitVec.ofNat 64 0 = _
    rw [get_r10n, get_r9n, h10₂, h9₂]
    exact tab_ea m
  · rw [addr_add_add]
    exact hTf _ (by omega)
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
  have h10₃ : Y₃.cpu.gpr.get (regOf 10) = (0x63a420 : Addr).add (400 + 384 * m) := by
    rw [← ntgt_eq m hm, hg₃]
    simp only [wr, eaG, optV, set_r9n, set_r10n, get_r9n, get_r10n, BitVec.setWidth_eq, h10₂,
      tab_bytes hT (by omega : m < 16)]
    rfl
  -- `jmp r10`
  refine c.s_jmp_rx hK₃ hA₃ hin (lt_scm (by decide)) hr₃ (d185 prof.feat) hin (lt_scm (by omega)) h10₃ ?_
  rintro Z tZ hKZ hAZ ⟨hrZ, hgZ⟩
  refine K Z tZ hKZ hAZ hrZ ?_
  rw [hgZ, hg₃, hg₂, hg₁]
  exact AtL.r10 (AtL.r9 (AtL.r10 (AtL.r9 (AtL.r9 hg _) _) _) _) _

/-- From `128`, `rdi` and `rsi` `q` bytes (a multiple of 16) into the strings `a` and `b`: to `192` when their
offsets in 16 bytes are the same, else to a loop, `rsi`'s offset the greater after a swap (`sw`). -/
theorem align (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) (he : e' = 0x63a420) (hT : NcmpTabV V)
    (hTf : ∀ i < 64, Foot F.data ((0x6f0df0 : Addr).add i)) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b : Addr} {n q : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 128)
    (hg : At128 g₀ Y.cpu.gpr a b n q) (hq : q % 16 = 0)
    (K0 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add 192 →
      a.toNat % 16 = b.toNat % 16 → AtL g₀ Z.cpu.gpr a b n q false → GoG prof L o gev gP gE Z t')
    (KL : ∀ Z t' (sw : Bool) (x y : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      (sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a) → x.toNat % 16 < y.toNat % 16 →
      Z.cpu.rip = e'.add (400 + 384 * (15 + x.toNat % 16 - y.toNat % 16)) → AtL g₀ Z.cpu.gpr x y n q sw →
      GoG prof L o gev gP gE Z t') : GoG prof L o gev gP gE Y t := by
  obtain ⟨hkp, hdi, hsi, h11, hcx, hax⟩ := hg
  -- `and rsi, -16; and rdi, -16; mov edx, 0xffff; xor r8d, r8d; and ecx, 15; and eax, 15`
  refine c.s_blkV hin (b128 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rsi, set_rdi, set_rdx, set_r8, set_rcx, set_rax, get0, get1, get6, get7,
    get_r8n, BitVec.setWidth_eq, BitVec.xor_self] at hg₁
  obtain ⟨ha1, ha2⟩ := al_down a hq
  obtain ⟨hb1, hb2⟩ := al_down b hq
  have hL : AtL g₀ Y₁.cpu.gpr a b n q false := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [KpN, hg₁]
      exact hkp
    · simp only [hg₁, hdi]
      exact ha1
    · simp only [hg₁, hdi]
      exact ha2
    · simp only [hg₁, hsi]
      exact hb1
    · simp only [hg₁, hsi]
      exact hb2
    · simp only [hg₁]
      exact h11
    · simp only [hg₁, hcx]
      exact and15 b
    · simp only [hg₁, hax]
      exact and15 a
    · simp only [hg₁]
      all_goals decide
    · simp only [hg₁]
      all_goals decide
  have hcx₁ := hL.2.2.2.2.2.2.1
  have hax₁ := hL.2.2.2.2.2.2.2.1
  -- `cmp ecx, eax`
  refine c.s_blkV hin (b150 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  have hz : Y₂.cpu.rflags.cond 4 = decide (b.toNat % 16 = a.toNat % 16) := by
    rw [hf₂, hfl, cond_4, subF_zf]
    simp only [gv, Src.val, get0, get1, hcx₁, hax₁, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    exact decide_eq_decide.mpr (ofNat_inj (off16_lt b) (off16_lt a))
  have hja : Y₂.cpu.rflags.cond 7 = !decide (b.toNat % 16 ≤ a.toNat % 16) := by
    rw [hf₂, hfl, cond_7, subF_cf, subF_zf]
    simp only [gv, Src.val, get0, get1, hcx₁, hax₁, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rw [be_ofNat (off16_lt b) (off16_lt a)]
  have hL₂ : AtL g₀ Y₂.cpu.gpr a b n q false := by rw [hg₂]; exact hL
  -- `je 192`
  refine c.s_jccF (tgt := 192) hK₂ hA₂ hin (lt_scm (by decide)) hr₂ (d152 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · intro hcc
    have heq : b.toNat % 16 = a.toNat % 16 := by
      rw [hz] at hcc
      exact of_decide_eq_true hcc
    rintro Z tZ hKZ hAZ ⟨hrZ, hgZ, -⟩
    exact K0 Z tZ hKZ hAZ hrZ heq.symm (by rw [hgZ]; exact hL₂)
  intro hcc
  have hne : b.toNat % 16 ≠ a.toNat % 16 := by
    rw [hz] at hcc
    exact of_decide_eq_false hcc
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, -, hf₃⟩
  have h7 : Y₃.cpu.rflags.cond 7 = Y₂.cpu.rflags.cond 7 := by rw [hf₃]; rfl
  have hL₃ : AtL g₀ Y₃.cpu.gpr a b n q false := by rw [hg₃]; exact hL₂
  -- `ja 163`
  refine c.s_jcc (tgt := 163) hK₃ hA₃ hin (lt_scm (by decide)) hr₃ (d154 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · intro hcc'
    rw [h7, hja] at hcc'
    have hlt : a.toNat % 16 < b.toNat % 16 := by
      simp at hcc'
      omega
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    exact at163 c hin he hT hTf hK₄ hA₄ hr₄ (by rw [hg₄]; exact hL₃) hlt
      fun Z tZ hKZ hAZ hrZ hLZ => KL Z tZ false a b hKZ hAZ (Or.inl ⟨rfl, rfl, rfl⟩) hlt hrZ hLZ
  intro hcc'
  rw [h7, hja] at hcc'
  have hlt : b.toNat % 16 < a.toNat % 16 := by
    simp at hcc'
    omega
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  obtain ⟨hkp₄, hd1, hd2, hs1, hs2, h11₄, hcx₄, hax₄, hdx₄, -⟩ : AtL g₀ Y₄.cpu.gpr a b n q false := by
    rw [hg₄]; exact hL₃
  -- `mov r8d, edx; xchg ecx, eax; xchg rdi, rsi`
  refine c.s_blkV hin (b156 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ _
  simp only [wr, gv, Src.val, set_r8, set_rcx, set_rax, set_rdi, set_rsi, get0, get1, get2, get6, get7,
    BitVec.setWidth_eq] at hg₅
  have hL₅ : AtL g₀ Y₅.cpu.gpr b a n q true := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [KpN, hg₅]
      exact hkp₄
    · simp only [hg₅]
      exact hs1
    · simp only [hg₅]
      exact hs2
    · simp only [hg₅]
      exact hd1
    · simp only [hg₅]
      exact hd2
    · simp only [hg₅]
      exact h11₄
    · simp only [hg₅, hax₄]
      exact sw3264 (off16_lt a)
    · simp only [hg₅, hcx₄]
      exact sw3264 (off16_lt b)
    · simp only [hg₅]
      exact hdx₄
    · simp only [hg₅, hdx₄]
      exact sw3264 (by decide)
  exact at163 c hin he hT hTf hK₅ hA₅ hr₅ hL₅ hlt
    fun Z tZ hKZ hAZ hrZ hLZ => KL Z tZ true b a hKZ hAZ (Or.inr ⟨rfl, rfl, rfl⟩) hlt hrZ hLZ

end FV7z.Strncmp
