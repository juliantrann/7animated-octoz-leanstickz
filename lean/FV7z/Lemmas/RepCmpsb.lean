import FV7z.Lemmas.RepMovsb
import FV7z.Lemmas.BlkOps
/-!
# `repz cmps byte [rsi], byte es:[rdi]`, `sbb r8, x` (PLAN.md §M, M1)

glibc 2.31's `dlerror.c` `fini` compares the message of the last error with the static "out of memory" by
`repz cmpsb; seta al; sbb al, 0`.

- `repzCmpsb`, `repz_cmpsb_exec`, `Seg.s_repz_cmpsb`: `repz cmpsb` as `Lemmas/RepMovsb.lean`'s `rep movsb`, a step of
  the model for each byte, with the direction flag clear. It stops after the first byte that differs or when `rcx`
  reaches 0; a byte from each string is read only while the earlier ones agree (`SameB`), and the flags at the end
  are those of the last compare.
- `Op.sbb8`: `sbb r8, x`, as `Op.sbb` (`FV7z/Lemmas/BlkOps.lean`) with the low byte written.
-/
namespace FV7z
open ZellicX86 Decode

/-- `sbb r8, x`: the low byte written; the flags are not tracked (a `test` follows). -/
def Op.sbb8 (r : Nat) (x : Src) : Op :=
  .reg (fun g f => wrLo g r (gv g 8 r - x.val 8 g - (BitVec.ofBool f.cf).setWidth 8)) fun _ _ _ => True

section
set_option linter.unusedSimpArgs false
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem OpI.sbb8 {r len : Nat} (x : Src) :
    OpI prof (mk .sbb 8 [gr 8 r, x.opd 8] len) (Op.sbb8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

/-- `repz cmps byte [rsi], byte es:[rdi]` as the decoder gives it. -/
abbrev repzCmpsb (len : Nat) : Inst :=
  { mn := .str .cmps, opsz := 8, len, rep := some .rep, lock := false, mask := none, zero := false, fop := 0,
    ops := [.mem ⟨none, some 6, none, 1, 0, false, false, 8⟩, .mem ⟨some .es, some 7, none, 1, 0, false, false, 8⟩] }

/-- The byte at `a` of the bytes `V`, read as one byte. -/
theorem ofBytesLE_map1 (V : Addr → Byte) (a : Addr) : ofBytesLE 8 ((byteAddrs a 1).map V) = V a := by
  simp [byteAddrs, ofBytesLE, Addr.add]

/-- The flags of a compare after the flags of another: those of the last. -/
theorem subF_rfz_subF {w : Nat} (f : Rflags) (a b x y : BitVec w) :
    subF (rfz (subF (rfz f) a b)) x y = subF (rfz f) x y := by
  cases f
  rfl

theorem add_one_ofNat (a : Addr) (i : Nat) : a + 1 + BitVec.ofNat 64 (i + 1) = a + BitVec.ofNat 64 (i + 1 + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]
  omega

theorem sub_one_ofNat (a : Addr) (i : Nat) : a - 1 - BitVec.ofNat 64 (i + 1) = a - BitVec.ofNat 64 (i + 1 + 1) := by
  bv_omega

/-- One iteration of `repz cmpsb` with `rcx` not 0: the flags of `[rsi] - [rdi]`, `rsi` and `rdi` one up, `rcx` one
down; again unless `rcx` is then 0 or the bytes differ. -/
theorem repz_cmpsb_exec {len : Nat} (hac : s.cpu.rflags.ac = false) (hdf : s.cpu.rflags.df = false)
    (hc : s.cpu.gpr.rcx ≠ 0) (hr6 : Readable prof s s.cpu.gpr.rsi 1) (hr7 : Readable prof s s.cpu.gpr.rdi 1) :
    ((exec prof (repzCmpsb len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok (if s.cpu.gpr.rcx - 1 = 0 then .next else
          if (subF (rf0 s) (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rsi 1))
            (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rdi 1))).zf then .again else .next)
        (s.modCpu fun c =>
          { c with rip := c.rip.add len,
                   rflags := subF (rf0 s) (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rsi 1))
                     (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rdi 1)),
                   gpr := ((s.cpu.gpr.set 6 (s.cpu.gpr.rsi + 1)).set 7 (s.cpu.gpr.rdi + 1)).set 1
                     (s.cpu.gpr.rcx - 1) }), t) := by
  simp only [exec, execString, stringOp, repzCmpsb, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, writeOp, Prog.readFlags, Prog.writeFlags, subOp, strAccess,
    Prog.checkAccesses, BitVec.mul_one, readAddrReg, writeAddrReg, Inst.addr32, List.any, ZellicX86.advance,
    Prog.writeReg]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have hc' : (advance s len).cpu.gpr.get 1 ≠ 0 := hc
  have hdf' : (advance s len).cpu.rflags.df = false := hdf
  simp only [hc', hdf', Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have ha7 : (advance s len).cpu.gpr.get (regOf 7) + 0 + 0#64 = s.cpu.gpr.rdi := by
    show s.cpu.gpr.rdi + 0 + 0#64 = _
    simp
  have ha6 : (advance s len).cpu.gpr.get (regOf 6) + 0 + 0#64 = s.cpu.gpr.rsi := by
    show s.cpu.gpr.rsi + 0 + 0#64 = _
    simp
  have hk6 : ∀ b : Bool, checkAccess prof.feat (advance s len) ⟨s.cpu.gpr.rsi, b⟩ .read 1 = Pure.pure none :=
    fun _ => checkAccess_ok hac hr6
  have hk7 : ∀ b : Bool, checkAccess prof.feat (advance s len) ⟨s.cpu.gpr.rdi, b⟩ .read 1 = Pure.pure none :=
    fun _ => checkAccess_ok hac hr7
  simp only [ha6, ha7, Nat.reduceDiv, checkEach, hk6, hk7]
  have e1 : (advance s len).cpu.gpr.get 1 = s.cpu.gpr.rcx := rfl
  rw [e1]
  by_cases h : s.cpu.gpr.rcx - 1 = 0
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    by_cases hz : (subF (rf0 s) (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rsi 1))
        (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rdi 1))).zf = true
    · rw [if_pos hz]
      first
        | rfl
        | split
          · rfl
          · rename_i hn
            exact absurd hz hn
    · rw [if_neg hz]
      first
        | rfl
        | split
          · rename_i hp
            exact absurd hp hz
          · rfl

end

/-- The bytes `V` from `a` on and from `b` on agree before the `i`-th. -/
abbrev SameB (V : Addr → Byte) (a b : Addr) (i : Nat) : Prop := ∀ k < i, V (a.add k) = V (b.add k)

/-- `SameB` one further on, from the first byte. -/
theorem sameB_succ {V : Addr → Byte} {a b : Addr} {i : Nat} (h0 : V a = V b) (h : SameB V (a + 1) (b + 1) i) :
    SameB V a b (i + 1) := fun k hk => by
  rcases k with _ | k
  · rw [addr_add_zero, addr_add_zero]
    exact h0
  · have := h k (by omega)
    rw [addr_one_add, addr_one_add] at this
    exact this

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `repz cmps byte [rsi], byte es:[rdi]` with `rcx` `n + 1` and the direction flag clear: the `i`-th bytes from
`rsi` and `rdi` on, data of the footprint while the earlier ones agree, are compared until the first that differ or
the last; after the `i`-th, `rsi`, `rdi` are `i + 1` up, `rcx` `i + 1` down and the flags those of its compare. -/
theorem s_repz_cmpsb (c : Seg prof F Wl L s₀ o) (hdf : s₀.cpu.rflags.df = false) (hin : CodeIn L e' code)
    {len : Nat} (hj : j < code.length) (hd : Dec prof.feat code j (repzCmpsb len)) :
    ∀ (n : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → X.cpu.gpr.rcx.toNat = n + 1 →
      (∀ i < n + 1, SameB V X.cpu.gpr.rsi X.cpu.gpr.rdi i →
        Foot F.data (X.cpu.gpr.rsi.add i) ∧ Foot F.data (X.cpu.gpr.rdi.add i)) →
      (∀ i ≤ n, SameB V X.cpu.gpr.rsi X.cpu.gpr.rdi i →
        (i = n ∨ V (X.cpu.gpr.rsi.add i) ≠ V (X.cpu.gpr.rdi.add i)) →
        ContG prof F Wl L s₀ o gev gP gE V (fun Y => Y.cpu.rip = e'.add (j + len) ∧
          Y.cpu.gpr = ((X.cpu.gpr.set 6 (X.cpu.gpr.rsi + BitVec.ofNat 64 (i + 1))).set 7
            (X.cpu.gpr.rdi + BitVec.ofNat 64 (i + 1))).set 1 (X.cpu.gpr.rcx - BitVec.ofNat 64 (i + 1)) ∧
          Y.cpu.rflags = subF (rfz X.cpu.rflags) (V (X.cpu.gpr.rsi.add i)) (V (X.cpu.gpr.rdi.add i)))) →
      GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero =>
    intro X t V hK hA hrip hc hft k'
    have hc1 : X.cpu.gpr.rcx = 1 := BitVec.eq_of_toNat_eq hc
    obtain ⟨h6, h7⟩ := hft 0 (by omega) fun k hk => absurd hk (Nat.not_lt_zero _)
    rw [addr_add_zero] at h6 h7
    refine c.next hK hA hin hj hrip (fun M hK' hA' htf hac => ?_)
      (k' 0 (Nat.le_refl 0) (fun k hk => absurd hk (Nat.not_lt_zero _)) (Or.inl rfl))
    obtain ⟨hr6, hl6⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rsi) (n := 1) fun i hi => by
      rw [show i = 0 by omega, addr_add_zero]
      exact h6
    obtain ⟨hr7, hl7⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rdi) (n := 1) fun i hi => by
      rw [show i = 0 by omega, addr_add_zero]
      exact h7
    have hx := repz_cmpsb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
      (hK'.df.trans hdf) (by show X.cpu.gpr.rcx ≠ 0; rw [hc1]; decide) hr6 hr7
    have hxv : ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1) = V X.cpu.gpr.rsi := by
      rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1 =
        (byteAddrs X.cpu.gpr.rsi 1).map V from hl6]
      exact ofBytesLE_map1 V _
    have hyv : ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rdi 1) = V X.cpu.gpr.rdi := by
      rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rdi 1 =
        (byteAddrs X.cpu.gpr.rdi 1).map V from hl7]
      exact ofBytesLE_map1 V _
    have e0 : (X.withMem M).cpu.gpr.rcx - 1 = 0 := by show X.cpu.gpr.rcx - 1 = 0; rw [hc1]; decide
    rw [hxv, hyv, e0] at hx
    simp only [↓reduceIte] at hx
    refine ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) hx, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA',
      rip_add hrip M len, ?_, ?_⟩
    · rw [hc1]
      all_goals rfl
    · show subF (rfz X.cpu.rflags) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi) = _
      rw [addr_add_zero, addr_add_zero]
  | succ n ih =>
    intro X t V hK hA hrip hc hft k'
    have hne : X.cpu.gpr.rcx ≠ 0 := fun h => by rw [h] at hc; simp at hc
    have hc' : (X.cpu.gpr.rcx - 1).toNat = n + 1 := by
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hc, h1]
      omega
    have hne' : X.cpu.gpr.rcx - 1 ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    obtain ⟨h6, h7⟩ := hft 0 (by omega) fun k hk => absurd hk (Nat.not_lt_zero _)
    rw [addr_add_zero] at h6 h7
    -- the loads and the iteration, from the state the step starts from
    have hit : ∀ M, KeptW Wl s₀ (X.withMem M) → Agree F M V → X.cpu.rflags.ac = false →
        ((exec prof (repzCmpsb len)).run prof.feat prof.linux.splitLock (advance (X.withMem M) len)).runStream o
          (t + 1) =
        (.ok (if (subF (rf0 (X.withMem M)) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi)).zf then .again else .next)
          ((X.withMem M).modCpu fun c =>
            { c with rip := c.rip.add len, rflags := subF (rf0 (X.withMem M)) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi),
                     gpr := ((X.cpu.gpr.set 6 (X.cpu.gpr.rsi + 1)).set 7 (X.cpu.gpr.rdi + 1)).set 1
                       (X.cpu.gpr.rcx - 1) }), t + 1) := by
      intro M hK' hA' hac
      obtain ⟨hr6, hl6⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rsi) (n := 1) fun i hi => by
        rw [show i = 0 by omega, addr_add_zero]
        exact h6
      obtain ⟨hr7, hl7⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rdi) (n := 1) fun i hi => by
        rw [show i = 0 by omega, addr_add_zero]
        exact h7
      have hx := repz_cmpsb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
        (hK'.df.trans hdf) hne hr6 hr7
      have hxv : ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1) =
          V X.cpu.gpr.rsi := by
        rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1 =
          (byteAddrs X.cpu.gpr.rsi 1).map V from hl6]
        exact ofBytesLE_map1 V _
      have hyv : ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rdi 1) =
          V X.cpu.gpr.rdi := by
        rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rdi 1 =
          (byteAddrs X.cpu.gpr.rdi 1).map V from hl7]
        exact ofBytesLE_map1 V _
      have e0 : ¬ ((X.withMem M).cpu.gpr.rcx - 1 = 0) := hne'
      rw [hxv, hyv] at hx
      simp only [e0, ↓reduceIte] at hx
      exact hx
    by_cases hxy : V X.cpu.gpr.rsi = V X.cpu.gpr.rdi
    · -- the bytes agree: again, from the next ones
      have hz : ∀ M, (subF (rf0 (X.withMem M)) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi)).zf = true := fun M => by
        rw [subF_zf]
        exact decide_eq_true hxy
      refine c.next hK hA hin hj hrip (V' := V)
        (Pr := fun Y => Y.cpu.rip = e'.add j ∧
          Y.cpu.gpr = ((X.cpu.gpr.set 6 (X.cpu.gpr.rsi + 1)).set 7 (X.cpu.gpr.rdi + 1)).set 1 (X.cpu.gpr.rcx - 1) ∧
          Y.cpu.rflags = subF (rfz X.cpu.rflags) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi))
        (fun M hK' hA' htf hac => ?_) ?_
      · have hx := hit M hK' hA' hac
        simp only [hz, ↓reduceIte] at hx
        refine ⟨_, _, instruction_again htf (c.dec hK' hin hrip hd) hx rfl,
          (hK'.modCpu rfl rfl rfl rfl rfl rfl rfl).modCpu rfl rfl rfl rfl rfl rfl rfl, hA', hrip, rfl, rfl⟩
      · rintro Y t' hKY hAY ⟨hrY, hgY, hfY⟩
        have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi + 1 := by rw [hgY]; rfl
        have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi + 1 := by rw [hgY]; rfl
        have hcx : Y.cpu.gpr.rcx = X.cpu.gpr.rcx - 1 := by rw [hgY]; rfl
        refine ih hKY hAY hrY (by rw [hcx]; exact hc') (fun i hi hs => ?_) (fun i hi hs hend => ?_)
        · rw [hsi, hdi] at hs ⊢
          rw [addr_one_add, addr_one_add]
          exact hft (i + 1) (by omega) (sameB_succ hxy hs)
        · rw [hsi, hdi] at hs hend
          rintro Z t'' hKZ hAZ ⟨hrZ, hgZ, hfZ⟩
          refine k' (i + 1) (by omega) (sameB_succ hxy hs) ?_ Z t'' hKZ hAZ ⟨hrZ, ?_, ?_⟩
          · rcases hend with rfl | hd'
            · exact Or.inl rfl
            · right
              rw [addr_one_add, addr_one_add] at hd'
              exact hd'
          · rw [hgZ, hsi, hdi, hcx, hgY, add_one_ofNat, add_one_ofNat, sub_one_ofNat]
            all_goals rfl
          · rw [hfZ, hfY, hsi, hdi, addr_one_add, addr_one_add]
            exact subF_rfz_subF _ _ _ _ _
    · -- the bytes differ: the end, at the first
      have hz : ∀ M, (subF (rf0 (X.withMem M)) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi)).zf = false := fun M => by
        rw [subF_zf]
        exact decide_eq_false hxy
      refine c.next hK hA hin hj hrip (fun M hK' hA' htf hac => ?_)
        (k' 0 (by omega) (fun k hk => absurd hk (Nat.not_lt_zero _))
          (Or.inr (by rw [addr_add_zero, addr_add_zero]; exact hxy)))
      have hx := hit M hK' hA' hac
      simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
      refine ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) hx, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA',
        rip_add hrip M len, rfl, ?_⟩
      show subF (rfz X.cpu.rflags) (V X.cpu.gpr.rsi) (V X.cpu.gpr.rdi) = _
      rw [addr_add_zero, addr_add_zero]

end FV7z.Fn.Seg
