import FV7z.Pim.Cuts
import FV7z.Pim.Dec
import FV7z.Lemmas.Xmm2
import FV7z.Lemmas.Rmw
import FV7z.Lemmas.Lock
import FV7z.Tls.Mem
import FV7z.Raf.Holds
/-!
# `__pthread_initialize_minimal_internal`: the frame and the bytes outside it (PLAN.md G3, startup)

The function at `0x6000b0` uses 216 bytes below the stack pointer `sp` of its entry and its callees up to 336 more.
Through its stretches the bytes are described in two parts:

- `Fr G V' sp r12 rbp cn`: outside the 552 bytes below `sp` the bytes `V'` are `G`, a chain of stores from the bytes
  of the entry (the thread's block and the variables); in the frame the two saved registers and the stack guard's
  copy are where the prologue put them.
- `Fr.lo` (a store in the 520 bytes below the three slots), `Fr.gl` (a store outside the 552 bytes: the same store
  in `G`), `Fr.rd` (bytes outside read as `G`'s), `Fr.of_out` (bytes that differ in the 520 bytes only), `Fr.fill`
  (`rep stos` there).
- `Seg.runV`: a stretch of `Op`s that keeps the vector registers (`Seg.s_blkF_v`), with a condition `Q` after it as
  `SpF.run` has.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)

namespace FV7z.Fn.Seg

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' fb : Addr} {code : List Byte} {X : State} {t : Nat} {V : Addr → Byte}

/-- A stretch that keeps the vector registers, with a condition after it. -/
theorem runV (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L e' code) {j j' : Nat}
    {ops : List Op} (hb : BlkF prof code e' fb j j' ops) (hkv : ops.all Op.kv = true)
    (Q : Gprs → Rflags → (Addr → Byte) → Prop) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = e'.add j) (vc : wp F Wl ops Q X.cpu.gpr X.cpu.rflags V)
    (k : ∀ g fl V', Q g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
      Y.cpu.gpr = g → Y.cpu.vec = X.cpu.vec → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.s_blkF_v hfs hin hb X.cpu.vec hK hA hrip rfl hkv
    (wp_mono ops (fun g fl V' hq Y t' hKY hAY hrY hg _ hv => k g fl V' hq Y t' hKY hAY hrY hg hv) vc)

end FV7z.Fn.Seg

namespace FV7z.Pim

/-- The bytes `V'` in the function: outside the 552 bytes below the entry's stack pointer `sp` they are `G`; in the
frame the saved `r12` and `rbp` and the stack guard's copy `cn`. -/
structure Fr (G V' : Addr → Byte) (sp : Addr) (r12 rbp cn : BitVec 64) : Prop where
  out : ∀ a : Addr, ¬ (sp.toNat - 552 ≤ a.toNat ∧ a.toNat < sp.toNat) → V' a = G a
  s12 : rdq(V', sp - 8#64) = r12
  sbp : rdq(V', sp - 16#64) = rbp
  can : rdq(V', sp - 32#64) = cn

variable {G V' V'' : Addr → Byte} {sp : Addr} {r12 rbp cn : BitVec 64}

/-- A store below the three slots. -/
theorem Fr.lo (h : Fr G V' sp r12 rbp cn) (hsp : 552 < sp.toNat) {x : Addr} {bs : List Byte} {n : Nat}
    (hn : bs.length = n) (h1 : sp.toNat - 552 ≤ x.toNat) (h2 : x.toNat + n ≤ sp.toNat - 32) :
    Fr G (Vst V' x bs) sp r12 rbp cn := by
  have hlt := sp.isLt
  have hx : x.toNat + n ≤ 2 ^ 64 := by omega
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · rw [vo hn hx (by omega)]
    exact h.out a ha
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.s12
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.sbp
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.can

/-- A store outside the 552 bytes. -/
theorem Fr.gl (h : Fr G V' sp r12 rbp cn) (hsp : 552 < sp.toNat) {x : Addr} {bs : List Byte} {n : Nat}
    (hn : bs.length = n) (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ sp.toNat - 552 ∨ sp.toNat ≤ x.toNat) :
    Fr (Vst G x bs) (Vst V' x bs) sp r12 rbp cn := by
  have hlt := sp.isLt
  refine ⟨fun a ha => Tls.Vst_congr bs V' G x a (h.out a ha), ?_, ?_, ?_⟩
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.s12
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.sbp
  · rw [vr hn hx (by bv_omega) (by bv_omega)]
    exact h.can

/-- Bytes outside the 552 bytes. -/
theorem Fr.rd (h : Fr G V' sp r12 rbp cn) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hd : x.toNat + n ≤ sp.toNat - 552 ∨ sp.toNat ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map G (byteAddrs x n) := Sga.rd_out h.out hx hd

/-- Bytes that differ below the three slots only. -/
theorem Fr.of_out (h : Fr G V' sp r12 rbp cn) (hsp : 552 < sp.toNat) {lo hi : Nat}
    (ho : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → V'' a = V' a) (h1 : sp.toNat - 552 ≤ lo)
    (h2 : hi ≤ sp.toNat - 32) : Fr G V'' sp r12 rbp cn := by
  have hlt := sp.isLt
  refine ⟨fun a ha => (ho a (by omega)).trans (h.out a ha), ?_, ?_, ?_⟩
  · rw [Sga.rd_out ho (by bv_omega) (by bv_omega)]
    exact h.s12
  · rw [Sga.rd_out ho (by bv_omega) (by bv_omega)]
    exact h.sbp
  · rw [Sga.rd_out ho (by bv_omega) (by bv_omega)]
    exact h.can

/-- `rep stos` below the three slots. -/
theorem Fr.fill (hsp : 552 < sp.toNat) (v : BitVec 64) : ∀ (n : Nat) {V' : Addr → Byte} {x : Addr},
    Fr G V' sp r12 rbp cn → sp.toNat - 552 ≤ x.toNat → x.toNat + 8 * n ≤ sp.toNat - 32 →
    Fr G (Vfill V' x v n) sp r12 rbp cn
  | 0, _, _, h, _, _ => h
  | n + 1, _, x, h, h1, h2 => by
    have hlt := sp.isLt
    rw [Vfill_succ]
    exact Fr.fill hsp v n (h.lo hsp (toBytesLE_length _ _) h1 (by omega)) (by bv_omega) (by bv_omega)

end FV7z.Pim
