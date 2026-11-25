import FV7z.Lemmas.Rmw
/-!
# `rep stos byte [rdi], al` (PLAN.md M, `__memset_erms`)

`repStosb`, `rep_stosb_exec`, `Seg.s_rep_stosb`: `rep stosb` as `Lemmas/Rmw.lean`'s `rep stosq`, a step of the model
for each byte; `VfillB` is what the footprint's bytes are after (`VfillB_in`, `VfillB_out`).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `rep stos byte [rdi], al` as the decoder gives it. -/
abbrev repStosb (len : Nat) : Inst :=
  { mn := .str .stos, opsz := 8, len, rep := some .rep, lock := false, mask := none, zero := false, fop := 0,
    ops := [.mem ⟨some .es, some 7, none, 1, 0, false, false, 8⟩, .reg ⟨8, 0, false⟩] }

theorem rep_stosb_exec {len : Nat} (hac : s.cpu.rflags.ac = false) (hdf : s.cpu.rflags.df = false)
    (hc : s.cpu.gpr.rcx ≠ 0) (hwr : Writable prof s s.cpu.gpr.rdi 1) :
    ((exec prof (repStosb len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok (if s.cpu.gpr.rcx - 1 = 0 then .next else .again)
        ((st s s.cpu.gpr.rdi (toBytesLE (s.cpu.gpr.rax.setWidth 8) 1)).modCpu fun c =>
          { c with rip := c.rip.add len, rflags := rf0 s,
                   gpr := (s.cpu.gpr.set 7 (s.cpu.gpr.rdi + 1)).set 1 (s.cpu.gpr.rcx - 1) }), t) := by
  simp only [exec, execString, stringOp, repStosb, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, writeOp, Prog.readFlags,
    BitVec.mul_one, readAddrReg, writeAddrReg, Inst.addr32, List.any, ZellicX86.advance, Prog.writeReg]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have hc' : (advance s len).cpu.gpr.get 1 ≠ 0 := hc
  have hdf' : (advance s len).cpu.rflags.df = false := hdf
  simp only [hc', hdf', Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have ha : (advance s len).cpu.gpr.get (regOf 7) + 0 + 0#64 = s.cpu.gpr.rdi := by
    show s.cpu.gpr.rdi + 0 + 0#64 = _
    simp
  have hk := checkAccess_ok (feat := prof.feat) (s := advance s len)
    (m := ⟨s.cpu.gpr.rdi, (some 7 == some 4 || some 7 == some 5) && !false && !false⟩) (acc := .write) (n := 1)
    hac hwr
  simp only [ha, Nat.reduceDiv, hk]
  have e1 : (advance s len).cpu.gpr.get 1 = s.cpu.gpr.rcx := rfl
  rw [e1]
  by_cases h : s.cpu.gpr.rcx - 1 = 0
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

/-- `V` with `n` copies of the byte `v` from `a` on. -/
def VfillB (V : Addr → Byte) (a : Addr) (v : BitVec 8) : Nat → Addr → Byte
  | 0 => V
  | n + 1 => VfillB (Vst V a (toBytesLE v 1)) (a + 1) v n

theorem VfillB_succ (V : Addr → Byte) (a : Addr) (v : BitVec 8) (n : Nat) :
    VfillB V a v (n + 1) = VfillB (Vst V a (toBytesLE v 1)) (a + 1) v n := rfl

theorem toBytesLE_one8 (v : BitVec 8) : toBytesLE v 1 = [v] := by
  show [(v >>> (8 * 0)).setWidth 8] = [v]
  simp only [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.setWidth_eq]

theorem addr_one_add (a : Addr) (i : Nat) : (a + 1).add i = a.add (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [h1]
  omega

/-- Outside the `n` bytes from `a`, `VfillB` is `V`. -/
theorem VfillB_out (v : BitVec 8) : ∀ (n : Nat) (V : Addr → Byte) (a x : Addr), (∀ i < n, x ≠ a.add i) →
    VfillB V a v n x = V x
  | 0, _, _, _, _ => rfl
  | n + 1, V, a, x, h => by
    rw [VfillB_succ, VfillB_out v n _ _ x fun i hi => by rw [addr_one_add]; exact h (i + 1) (by omega)]
    refine Vst_apart _ V a x fun i hi => ?_
    rw [toBytesLE_length] at hi
    rw [show i = 0 by omega]
    exact h 0 (by omega)

/-- The `n` bytes from `a` are `v`, if they do not wrap. -/
theorem VfillB_in (v : BitVec 8) : ∀ (n : Nat) (V : Addr → Byte) (a : Addr), a.toNat + n ≤ 2 ^ 64 →
    ∀ i < n, VfillB V a v n (a.add i) = v
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, V, a, hf, i, hi => by
    rw [VfillB_succ]
    rcases i with _ | i
    · rw [VfillB_out v n _ _ _ fun j hj => ?_]
      · rw [addr_add_zero, toBytesLE_one8]
        simp only [Vst, upd1, if_pos]
      · rw [addr_add_zero, addr_one_add]
        intro e
        have := congrArg BitVec.toNat e
        rw [toNat_add_of_fits (n := n + 1) (by omega) hf] at this
        omega
    · rw [← addr_one_add]
      have hf' : (a + 1).toNat + n ≤ 2 ^ 64 := by
        have h1 := toNat_add_of_fits (a := a) (i := 1) (n := n + 1) (by omega) hf
        rw [show a.add 1 = a + 1 from rfl] at h1
        omega
      exact VfillB_in v n _ (a + 1) hf' i (by omega)

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `rep stos byte [rdi], al` with `rcx` `n + 1` and the direction flag clear: `n + 1` bytes `al` from `rdi` on, into
bytes the run may store into; `rdi` is past them and `rcx` 0. -/
theorem s_rep_stosb (c : Seg prof F Wl L s₀ o) (hdf : s₀.cpu.rflags.df = false) (hin : CodeIn L e' code) {len : Nat}
    (hjl : j + len ≤ code.length) (hj : j < code.length) (hd : Dec prof.feat code j (repStosb len)) :
    ∀ (n : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → X.cpu.gpr.rcx.toNat = n + 1 → (∀ i < n + 1, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
      ContG prof F Wl L s₀ o gev gP gE (VfillB V X.cpu.gpr.rdi (X.cpu.gpr.rax.setWidth 8) (n + 1))
        (fun Y => Y.cpu.rip = e'.add (j + len) ∧
          Y.cpu.gpr = (X.cpu.gpr.set 7 (X.cpu.gpr.rdi + BitVec.ofNat 64 (n + 1))).set 1 0) →
      GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero =>
    intro X t V hK hA hrip hc hst k'
    have hc1 : X.cpu.gpr.rcx = 1 := BitVec.eq_of_toNat_eq hc
    refine c.next hK hA hin hj hrip (fun M hK' hA' htf hac => ?_) k'
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (X.cpu.gpr.rax.setWidth 8) 1) (a := X.cpu.gpr.rdi)
      (by intro i hi; rw [toBytesLE_length] at hi; exact hst i hi)
    rw [toBytesLE_length] at hwr
    have hx := rep_stosb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
      (hK'.df.trans hdf) (by show X.cpu.gpr.rcx ≠ 0; rw [hc1]; decide) hwr
    have e0 : (X.withMem M).cpu.gpr.rcx - 1 = 0 := by show X.cpu.gpr.rcx - 1 = 0; rw [hc1]; decide
    rw [e0] at hx
    simp only [↓reduceIte] at hx
    refine ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) hx, hKs.modCpu rfl rfl rfl rfl rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩
  | succ n ih =>
    intro X t V hK hA hrip hc hst k'
    have hne : X.cpu.gpr.rcx ≠ 0 := fun h => by rw [h] at hc; simp at hc
    have hc' : (X.cpu.gpr.rcx - 1).toNat = n + 1 := by
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hc, h1]
      omega
    have hne' : X.cpu.gpr.rcx - 1 ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    refine c.next hK hA hin hj hrip (V' := Vst V X.cpu.gpr.rdi (toBytesLE (X.cpu.gpr.rax.setWidth 8) 1))
      (Pr := fun Y => Y.cpu.rip = e'.add j ∧
        Y.cpu.gpr = (X.cpu.gpr.set 7 (X.cpu.gpr.rdi + 1)).set 1 (X.cpu.gpr.rcx - 1))
      (fun M hK' hA' htf hac => ?_) ?_
    · obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
        (bs := toBytesLE (X.cpu.gpr.rax.setWidth 8) 1) (a := X.cpu.gpr.rdi)
        (by intro i hi; rw [toBytesLE_length] at hi; exact hst i (by omega))
      rw [toBytesLE_length] at hwr
      have hx := rep_stosb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
        (hK'.df.trans hdf) hne hwr
      have e0 : ¬ ((X.withMem M).cpu.gpr.rcx - 1 = 0) := hne'
      simp only [e0, ↓reduceIte] at hx
      have hcA := c.codeAt hK' hin
      have hcB := c.codeAt hKs hin
      have hcode : readBytes (st (X.withMem M) X.cpu.gpr.rdi (toBytesLE (X.cpu.gpr.rax.setWidth 8) 1)).proc.mm.mem
          (X.withMem M).cpu.rip len = readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.rip len := by
        refine readBytes_congr len _ fun i hi => ?_
        rw [show (X.withMem M).cpu.rip = e'.add j from hrip, addr_add_add]
        obtain ⟨-, -, h1⟩ := hcA (j + i) (by omega)
        obtain ⟨-, -, h2⟩ := hcB (j + i) (by omega)
        rw [h1] at h2
        exact (Option.some.inj h2).symm
      refine ⟨_, _, instruction_again htf (c.dec hK' hin hrip hd) hx hcode,
        (hKs.modCpu rfl rfl rfl rfl rfl rfl rfl).modCpu rfl rfl rfl rfl rfl rfl rfl, hAs, hrip, rfl⟩
    · rintro Y t' hKY hAY ⟨hrY, hgY⟩
      have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi + 1 := by rw [hgY]; rfl
      have hax : Y.cpu.gpr.rax = X.cpu.gpr.rax := by rw [hgY]; rfl
      have hcx : Y.cpu.gpr.rcx = X.cpu.gpr.rcx - 1 := by rw [hgY]; rfl
      refine ih hKY hAY hrY (by rw [hcx]; exact hc') (fun i hi => ?_) ?_
      · rw [hdi, addr_one_add]
        exact hst (i + 1) (by omega)
      · rw [hdi, hax]
        intro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
        refine k' Z t'' hKZ (by rw [VfillB_succ]; exact hAZ) ⟨hrZ, ?_⟩
        rw [hgZ, hgY]
        have ea : X.cpu.gpr.rdi + 1 + BitVec.ofNat 64 (n + 1) = X.cpu.gpr.rdi + BitVec.ofNat 64 (n + 1 + 1) := by
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [Nat.add_mod]
          omega
        rw [ea]
        rfl

end FV7z.Fn.Seg
