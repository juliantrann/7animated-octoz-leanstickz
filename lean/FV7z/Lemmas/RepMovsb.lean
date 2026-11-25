import FV7z.Lemmas.RepStosb
/-!
# `rep movs byte [rdi], byte [rsi]` (PLAN.md M, `__memmove_erms` and the `erms` paths of `memcpy`/`mempcpy`)

`repMovsb`, `rep_movsb_exec`, `Seg.s_rep_movsb`: `rep movsb` as `Lemmas/RepStosb.lean`'s `rep stosb`, a step of the
model for each byte, with the direction flag clear. `VcopyB` is what the footprint's bytes are after: each byte read
from the bytes as the earlier steps left them (`VcopyB_out`; `VcopyB_in` when the two ranges are apart).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `rep movs byte [rdi], byte [rsi]` as the decoder gives it. -/
abbrev repMovsb (len : Nat) : Inst :=
  { mn := .str .movs, opsz := 8, len, rep := some .rep, lock := false, mask := none, zero := false, fop := 0,
    ops := [.mem ⟨some .es, some 7, none, 1, 0, false, false, 8⟩, .mem ⟨none, some 6, none, 1, 0, false, false, 8⟩] }

theorem rep_movsb_exec {len : Nat} (hac : s.cpu.rflags.ac = false) (hdf : s.cpu.rflags.df = false)
    (hc : s.cpu.gpr.rcx ≠ 0) (hrd : Readable prof s s.cpu.gpr.rsi 1) (hwr : Writable prof s s.cpu.gpr.rdi 1) :
    ((exec prof (repMovsb len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok (if s.cpu.gpr.rcx - 1 = 0 then .next else .again)
        ((st s s.cpu.gpr.rdi (toBytesLE (ofBytesLE 8 (readBytes s.proc.mm.mem s.cpu.gpr.rsi 1)) 1)).modCpu fun c =>
          { c with rip := c.rip.add len, rflags := rf0 s,
                   gpr := ((s.cpu.gpr.set 6 (s.cpu.gpr.rsi + 1)).set 7 (s.cpu.gpr.rdi + 1)).set 1
                     (s.cpu.gpr.rcx - 1) }), t) := by
  simp only [exec, execString, stringOp, repMovsb, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.read, writeOp, Prog.readFlags, strAccess,
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
    fun _ => checkAccess_ok hac hrd
  have hk7 : ∀ b : Bool, checkAccess prof.feat (advance s len) ⟨s.cpu.gpr.rdi, b⟩ .write 1 = Pure.pure none :=
    fun _ => checkAccess_ok hac hwr
  simp only [ha6, ha7, Nat.reduceDiv, checkEach, hk6, hk7]
  have e1 : (advance s len).cpu.gpr.get 1 = s.cpu.gpr.rcx := rfl
  rw [e1]
  by_cases h : s.cpu.gpr.rcx - 1 = 0
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

/-- `V` with the `n` bytes from `d` on copied, one by one, from those from `s` on (each read after the earlier
copies). -/
def VcopyB (V : Addr → Byte) (d s : Addr) : Nat → Addr → Byte
  | 0 => V
  | n + 1 => VcopyB (Vst V d [V s]) (d + 1) (s + 1) n

theorem VcopyB_succ (V : Addr → Byte) (d s : Addr) (n : Nat) :
    VcopyB V d s (n + 1) = VcopyB (Vst V d [V s]) (d + 1) (s + 1) n := rfl

/-- The byte a one-byte load reads, stored back as one byte. -/
theorem toBytesLE_ofBytesLE_one (V : Addr → Byte) (a : Addr) :
    toBytesLE (ofBytesLE 8 ((byteAddrs a 1).map V)) 1 = [V a] := by
  rw [toBytesLE_one8]
  show [(V (a.add 0)).setWidth 8 ||| ((0 : BitVec 8) <<< 8)] = [V a]
  rw [addr_add_zero]
  simp

/-- Outside the `n` bytes from `d`, `VcopyB` is `V`. -/
theorem VcopyB_out : ∀ (n : Nat) (V : Addr → Byte) (d s x : Addr), (∀ i < n, x ≠ d.add i) →
    VcopyB V d s n x = V x
  | 0, _, _, _, _, _ => rfl
  | n + 1, V, d, s, x, h => by
    rw [VcopyB_succ, VcopyB_out n _ _ _ x fun i hi => by rw [addr_one_add]; exact h (i + 1) (by omega)]
    refine Vst_apart _ V d x fun i hi => ?_
    rw [show i = 0 by simp at hi; omega]
    exact h 0 (by omega)

/-- The `n` bytes from `d` are those from `s`, if neither range wraps and the two are apart. -/
theorem VcopyB_in : ∀ (n : Nat) (V : Addr → Byte) (d s : Addr), d.toNat + n ≤ 2 ^ 64 → s.toNat + n ≤ 2 ^ 64 →
    (s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) → ∀ i < n, VcopyB V d s n (d.add i) = V (s.add i)
  | 0, _, _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, V, d, s, hd, hs, hap, i, hi => by
    rw [VcopyB_succ]
    rcases i with _ | i
    · rw [VcopyB_out n _ _ _ _ fun j hj => ?_]
      · rw [addr_add_zero, addr_add_zero]
        simp only [Vst, upd1, ite_eq_left]
        all_goals (intro hne; exact absurd rfl hne)
      · rw [addr_add_zero, addr_one_add]
        intro e
        have := congrArg BitVec.toNat e
        rw [toNat_add_of_fits (n := n + 1) (by omega) hd] at this
        omega
    · have hd1 : (d + 1).toNat = d.toNat + 1 := by
        have h1 := toNat_add_of_fits (a := d) (i := 1) (n := n + 1) (by omega) hd
        rw [show d.add 1 = d + 1 from rfl] at h1
        omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by
        have h1 := toNat_add_of_fits (a := s) (i := 1) (n := n + 1) (by omega) hs
        rw [show s.add 1 = s + 1 from rfl] at h1
        omega
      rw [← addr_one_add, ← addr_one_add]
      rw [VcopyB_in n _ (d + 1) (s + 1) (by omega) (by omega) (by omega) i (by omega)]
      refine Vst_apart _ V d _ fun k hk => ?_
      rw [show k = 0 by simp at hk; omega, addr_add_zero]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_add_of_fits (a := s + 1) (n := n) (by omega) (by omega)] at this
      omega

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `rep movs byte [rdi], byte [rsi]` with `rcx` `n + 1` and the direction flag clear: `n + 1` bytes from `rsi` on,
data of the footprint, copied to bytes from `rdi` on the run may store into; `rsi`, `rdi` are past them and `rcx` 0. -/
theorem s_rep_movsb (c : Seg prof F Wl L s₀ o) (hdf : s₀.cpu.rflags.df = false) (hin : CodeIn L e' code) {len : Nat}
    (hjl : j + len ≤ code.length) (hj : j < code.length) (hd : Dec prof.feat code j (repMovsb len)) :
    ∀ (n : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → X.cpu.gpr.rcx.toNat = n + 1 → (∀ i < n + 1, Foot F.data (Addr.add X.cpu.gpr.rsi i)) →
      (∀ i < n + 1, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
      ContG prof F Wl L s₀ o gev gP gE (VcopyB V X.cpu.gpr.rdi X.cpu.gpr.rsi (n + 1))
        (fun Y => Y.cpu.rip = e'.add (j + len) ∧
          Y.cpu.gpr = ((X.cpu.gpr.set 6 (X.cpu.gpr.rsi + BitVec.ofNat 64 (n + 1))).set 7
            (X.cpu.gpr.rdi + BitVec.ofNat 64 (n + 1))).set 1 0) →
      GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero =>
    intro X t V hK hA hrip hc hsrc hst k'
    have hc1 : X.cpu.gpr.rcx = 1 := BitVec.eq_of_toNat_eq hc
    refine c.next hK hA hin hj hrip (fun M hK' hA' htf hac => ?_) k'
    obtain ⟨hrd, hld⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rsi) (n := 1) hsrc
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := [V X.cpu.gpr.rsi]) (a := X.cpu.gpr.rdi) (fun i hi => hst i (by simp at hi; omega))
    have hx := rep_movsb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
      (hK'.df.trans hdf) (by show X.cpu.gpr.rcx ≠ 0; rw [hc1]; decide) hrd hwr
    have hv : toBytesLE (ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1)) 1 =
        [V X.cpu.gpr.rsi] := by
      rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1 =
        (byteAddrs X.cpu.gpr.rsi 1).map V from hld]
      exact toBytesLE_ofBytesLE_one V _
    have e0 : (X.withMem M).cpu.gpr.rcx - 1 = 0 := by show X.cpu.gpr.rcx - 1 = 0; rw [hc1]; decide
    rw [hv, e0] at hx
    simp only [↓reduceIte] at hx
    refine ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) hx, hKs.modCpu rfl rfl rfl rfl rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩
  | succ n ih =>
    intro X t V hK hA hrip hc hsrc hst k'
    have hne : X.cpu.gpr.rcx ≠ 0 := fun h => by rw [h] at hc; simp at hc
    have hc' : (X.cpu.gpr.rcx - 1).toNat = n + 1 := by
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hc, h1]
      omega
    have hne' : X.cpu.gpr.rcx - 1 ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    refine c.next hK hA hin hj hrip (V' := Vst V X.cpu.gpr.rdi [V X.cpu.gpr.rsi])
      (Pr := fun Y => Y.cpu.rip = e'.add j ∧
        Y.cpu.gpr = ((X.cpu.gpr.set 6 (X.cpu.gpr.rsi + 1)).set 7 (X.cpu.gpr.rdi + 1)).set 1 (X.cpu.gpr.rcx - 1))
      (fun M hK' hA' htf hac => ?_) ?_
    · obtain ⟨hrd, hld⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := X.cpu.gpr.rsi) (n := 1)
        (fun i hi => hsrc i (by omega))
      obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
        (bs := [V X.cpu.gpr.rsi]) (a := X.cpu.gpr.rdi) (fun i hi => hst i (by simp at hi; omega))
      have hx := rep_movsb_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
        (hK'.df.trans hdf) hne hrd hwr
      have hv : toBytesLE (ofBytesLE 8 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1)) 1 =
          [V X.cpu.gpr.rsi] := by
        rw [show readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi 1 =
          (byteAddrs X.cpu.gpr.rsi 1).map V from hld]
        exact toBytesLE_ofBytesLE_one V _
      have e0 : ¬ ((X.withMem M).cpu.gpr.rcx - 1 = 0) := hne'
      rw [hv] at hx
      simp only [e0, ↓reduceIte] at hx
      have hcA := c.codeAt hK' hin
      have hcB := c.codeAt hKs hin
      have hcode : readBytes (st (X.withMem M) X.cpu.gpr.rdi [V X.cpu.gpr.rsi]).proc.mm.mem
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
      have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi + 1 := by rw [hgY]; rfl
      have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi + 1 := by rw [hgY]; rfl
      have hcx : Y.cpu.gpr.rcx = X.cpu.gpr.rcx - 1 := by rw [hgY]; rfl
      refine ih hKY hAY hrY (by rw [hcx]; exact hc') (fun i hi => ?_) (fun i hi => ?_) ?_
      · rw [hsi, addr_one_add]
        exact hsrc (i + 1) (by omega)
      · rw [hdi, addr_one_add]
        exact hst (i + 1) (by omega)
      · rw [hsi, hdi]
        intro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
        refine k' Z t'' hKZ (by rw [VcopyB_succ]; exact hAZ) ⟨hrZ, ?_⟩
        rw [hgZ, hgY]
        have ea : ∀ a : Addr, a + 1 + BitVec.ofNat 64 (n + 1) = a + BitVec.ofNat 64 (n + 1 + 1) := by
          intro a
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [Nat.add_mod]
          omega
        rw [ea, ea]
        rfl

end FV7z.Fn.Seg
