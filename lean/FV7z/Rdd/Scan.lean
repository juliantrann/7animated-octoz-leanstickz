import FV7z.Rdd.Ok
/-!
# `__readdir`: one entry of the buffer (PLAN.md §M, M1)

From 80, the entry at offset `k` (`r8 + r14` = `p + 48 + k`): `d_reclen` added to the offset, `d_off` stored in
`filepos` (`VB`); `d_ino` 0 goes back to 109 with the offset `k + rl`, `d_ino` not 0 is the result (176, `fin176`).

- `LR`, `LM`: the registers and the bytes in the loop (at 80 and 109), the offset `k`, the size `n`.
- `dst`: a store into the `DIR`'s first 48 bytes keeps `RSv`, `RFr` and the buffer; `st80`: the two stores at 80.
- `bufR`, `rlB`, `Ch.inv`, `rcl_rl`: reads in the buffer, `d_reclen` through stores, a chain's first entry.
- `n80`: `d_ino` not 0, to `RddK`; `z80`: `d_ino` 0, to the state at 109 with the offset past the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}

/-- The registers in the loop: `rsp` after the pushes, `rbx` the buffer, `rbp` -72, `r14` the `DIR`, `r15`, `rax`
the size `n`. -/
structure LR (S p : Addr) (g0 : Gprs) (n : Nat) (g : Gprs) : Prop where
  sp : g.rsp = S - 8 - 8 - 8 - 8 - 8
  bx : g.rbx = p + 48#64
  bp : g.rbp = 18446744073709551544#64
  di : g.r14 = p
  r15 : g.r15 = g0.r15
  ax : g.rax.toNat = n

/-- The bytes in the loop: the saved registers, the rest as in `V₀`, the `DIR` locked, a chain from `k` to `n`. -/
structure LM (S p fb : Addr) (A : Nat) (g0 : Gprs) (V₀ W : Addr → Byte) (n k : Nat) : Prop where
  sv : RSv S g0 W
  fr : RFr S p fb A V₀ W
  dir : Dir W p A 1#32 n k
  ch : Ch W p n k

/-- A store into the `DIR`'s first 48 bytes keeps the saved registers, the bytes outside the `DIR`, the buffer. -/
theorem dst {g0 : Gprs} {V₀ W : Addr → Byte} (a : Addr) (bs : List Byte) (C : RdC F Wl S p fb A)
    (ha1 : p.toNat ≤ a.toNat) (ha2 : a.toNat + bs.length ≤ p.toNat + 48) (hsv : RSv S g0 W)
    (hfr : RFr S p fb A V₀ W) :
    RSv S g0 (Vst W a bs) ∧ RFr S p fb A V₀ (Vst W a bs) ∧
      ∀ i < A, Vst W a bs (p.add (48 + i)) = W (p.add (48 + i)) := by
  obtain ⟨b5, -, -, a1, a2, a3, a4⟩ := stR S C.h48
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have dS := C.dS
  have hal : a.toNat + bs.length ≤ 2 ^ 64 := by omega
  have sl : ∀ x : Addr, S.toNat - 40 ≤ x.toNat → x.toNat + 8 ≤ S.toNat → rdq(Vst W a bs, x) = rdq(W, x) :=
    fun x x1 x2 => by rw [rd_Vst W a bs x 8 hal (by omega) (by omega)]
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsv
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [sl (S - 8 - 8 - 8 - 8 - 8) (by omega) (by omega)]; exact s1
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8) (by omega) (by omega)]; exact s2
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) (by omega) (by omega)]; exact s3
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) (by omega) (by omega)]; exact s4
  · rw [sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) (by omega) (by omega)]; exact s5
  · intro x x1 x2 x3
    rw [Vst_out W a bs x hal (by omega)]
    exact hfr x x1 x2 x3
  · intro i hi
    have hx := toNat_add_of_fits (a := p) (i := 48 + i) (n := 48 + A) (by omega) (by omega)
    exact Vst_out W a bs _ hal (by omega)

/-- A read past a store of 8 bytes. -/
theorem rdS (w : Nat) (V : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr) (m : Nat)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + m ≤ 2 ^ 64)
    (h : a.toNat + 8 ≤ x.toNat ∨ x.toNat + m ≤ a.toNat) :
    ofBytesLE w (List.map (Vst V a (toBytesLE v 8)) (byteAddrs x m)) = ofBytesLE w (List.map V (byteAddrs x m)) := by
  rw [rd_Vst V a (toBytesLE v 8) x m (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h)]

/-- The two stores at 80 (the offset `v`, `filepos` `w`): the `DIR` with the offset `k'`. -/
theorem st80 {g0 : Gprs} {V₀ W : Addr → Byte} {n k k' : Nat} {v : BitVec 64} (w : BitVec 64)
    (C : RdC F Wl S p fb A) (hsv : RSv S g0 W) (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n k)
    (hv : v.toNat = k') :
    RSv S g0 (Vst (Vst W (p + 24#64) (toBytesLE v 8)) (p + 32#64) (toBytesLE w 8)) ∧
      RFr S p fb A V₀ (Vst (Vst W (p + 24#64) (toBytesLE v 8)) (p + 32#64) (toBytesLE w 8)) ∧
      Dir (Vst (Vst W (p + 24#64) (toBytesLE v 8)) (p + 32#64) (toBytesLE w 8)) p A 1#32 n k' ∧
      ∀ i < A, Vst (Vst W (p + 24#64) (toBytesLE v 8)) (p + 32#64) (toBytesLE w 8) (p.add (48 + i)) =
        W (p.add (48 + i)) := by
  have hpA := C.hpA
  have t4 : (p + 4#64).toNat = p.toNat + 4 := Opd.tAdd p 4 (by omega)
  have t8 : (p + 8#64).toNat = p.toNat + 8 := Opd.tAdd p 8 (by omega)
  have t16 : (p + 16#64).toNat = p.toNat + 16 := Opd.tAdd p 16 (by omega)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  have t32 : (p + 32#64).toNat = p.toNat + 32 := Opd.tAdd p 32 (by omega)
  obtain ⟨s1, r1, b1⟩ := dst (p + 24#64) (toBytesLE v 8) C (by omega) (by rw [toBytesLE_length]; omega) hsv hfr
  obtain ⟨s2, r2, b2⟩ := dst (p + 32#64) (toBytesLE w 8) C (by omega) (by rw [toBytesLE_length]; omega) s1 r1
  refine ⟨s2, r2, ⟨?_, ?_, ?_, hD.nA, ?_⟩, fun i hi => (b2 i hi).trans (b1 i hi)⟩
  · rw [rdS 32 _ (p + 32#64) w (p + 4#64) 4 (by omega) (by omega) (by omega),
      rdS 32 W (p + 24#64) v (p + 4#64) 4 (by omega) (by omega) (by omega)]
    exact hD.lk
  · rw [rdS 64 _ (p + 32#64) w (p + 8#64) 8 (by omega) (by omega) (by omega),
      rdS 64 W (p + 24#64) v (p + 8#64) 8 (by omega) (by omega) (by omega)]
    exact hD.al
  · rw [rdS 64 _ (p + 32#64) w (p + 16#64) 8 (by omega) (by omega) (by omega),
      rdS 64 W (p + 24#64) v (p + 16#64) 8 (by omega) (by omega) (by omega)]
    exact hD.sz
  · rw [rdS 64 _ (p + 32#64) w (p + 24#64) 8 (by omega) (by omega) (by omega),
      rd_Vst_self W (p + 24#64) (toBytesLE v 8) (toBytesLE_length v 8) (by omega),
      ofBytesLE_toBytesLE (by decide)]
    exact hv

/-- Bytes that agree on the buffer agree on a read inside it. -/
theorem bufR (w : Nat) {V V' : Addr → Byte} {j m : Nat} (hpA : p.toNat + 48 + A < 2 ^ 64)
    (hb : ∀ i < A, V' (p.add (48 + i)) = V (p.add (48 + i))) (hj : j + m ≤ A) :
    ofBytesLE w (List.map V' (byteAddrs (Addr.add p (48 + j)) m)) =
      ofBytesLE w (List.map V (byteAddrs (Addr.add p (48 + j)) m)) := by
  have hx := toNat_add_of_fits (a := p) (i := 48 + j) (n := 48 + j + 1) (by omega) (by omega)
  refine rdE w (by omega) fun a x1 x2 => ?_
  rw [Opd.fa (B := p) (d := 48 + (a.toNat - p.toNat - 48)) (by omega) (by omega)]
  exact hb _ (by omega)

/-- `d_reclen` through bytes that agree on the buffer. -/
theorem rlB {V V' : Addr → Byte} {k : Nat} (hb : ∀ i < A, V' (p.add (48 + i)) = V (p.add (48 + i)))
    (hk : k + 18 ≤ A) : rl V' p k = rl V p k :=
  rl_congr fun j hj => by
    rw [show k + 64 + j = 48 + (k + 16 + j) by omega]
    exact hb _ (by omega)

/-- A chain from `k < n`: its first entry. -/
theorem Ch.inv {V : Addr → Byte} {n k : Nat} (h : Ch V p n k) (hk : k < n) :
    Ent V p k ∧ k + rl V p k ≤ n ∧ Ch V p n (k + rl V p k) := by
  cases h with
  | fin => exact absurd hk (Nat.lt_irrefl _)
  | step a b c => exact ⟨a, b, c⟩

/-- `movzx ecx, word [r8 + 16]` loads `d_reclen`. -/
theorem rcl_rl {V : Addr → Byte} {g : Gprs} {k : Nat} (he : g.r8 + g.r14 = Addr.add p (48 + k)) :
    (rcl V g).toNat = rl V p k := by
  have ha : g.r8 + g.r14 + 16#64 = p.add (k + 64) := by
    rw [he]
    exact (addr_add_add' p (48 + k) 16).trans (by rw [show 48 + k + 16 = k + 64 by omega])
  unfold rcl rl
  rw [ha]
  generalize ofBytesLE 16 (List.map V (byteAddrs (p.add (k + 64)) 2)) = x
  have := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-! ## The entry at 80 -/

/-- The footprint facts of `vc_80z`, `vc_80n`. -/
theorem ft80 {g : Gprs} {k : Nat} (hws : ∀ y, Foot Wl y → Foot F.data y) (C : RdC F Wl S p fb A) (h14 : g.r14 = p)
    (he : g.r8 + g.r14 = Addr.add p (48 + k)) (hk : k + 18 ≤ A) :
    (∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14 + 8#64) i)) ∧
      (∀ i < 2, Foot F.data (Addr.add (g.r8 + g.r14 + 16#64) i)) ∧
      (∀ i < 8, Foot Wl (Addr.add (g.r14 + 24#64) i)) ∧
      (∀ i < 8, Foot Wl (Addr.add (g.r14 + 32#64) i)) := by
  have hpA := C.hpA
  have pd : ∀ i < 48 + A, Foot F.data (Addr.add p i) := fun i hi => hws _ (C.pw i hi)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  have t32 : (p + 32#64).toNat = p.toNat + 32 := Opd.tAdd p 32 (by omega)
  rw [he, h14]
  exact ⟨Opd.frw pd rfl (by omega), Opd.frw pd (addr_add_add' p (48 + k) 8) (by omega),
    Opd.frw pd (addr_add_add' p (48 + k) 16) (by omega),
    Opd.frw C.pw (Opd.fa (B := p) (d := 24) (by omega) t24) (by omega),
    Opd.frw C.pw (Opd.fa (B := p) (d := 32) (by omega) t32) (by omega)⟩

/-- After the stores at 80: the bytes with the offset past the entry, the buffer as before. -/
theorem post80 {g0 : Gprs} {V₀ W : Addr → Byte} {g : Gprs} {Z : State} {n k : Nat} (C : RdC F Wl S p fb A)
    (R : LR S p g0 n g) (M : LM S p fb A g0 V₀ W n k) (hk : k < n) (he : g.r8 + g.r14 = Addr.add p (48 + k))
    (hdx : g.rdx.toNat = k) (hA : Agree F Z.proc.mm.mem (VB W g)) :
    ∃ W' : Addr → Byte, Agree F Z.proc.mm.mem W' ∧ RSv S g0 W' ∧ RFr S p fb A V₀ W' ∧
      Dir W' p A 1#32 n (k + rl W p k) ∧ (∀ i < A, W' (p.add (48 + i)) = W (p.add (48 + i))) ∧
      (gB W g).rdx.toNat = k + rl W p k := by
  have hnA := M.dir.nA
  have hA31 := C.hA
  obtain ⟨-, hkn, -⟩ := M.ch.inv hk
  have hv : (g.rdx + rcl W g).toNat = k + rl W p k := by
    rw [BitVec.toNat_add, hdx, rcl_rl he]
    omega
  have e1 : VB W g = Vst (Vst W (p + 24#64) (toBytesLE (g.rdx + rcl W g) 8)) (p + 32#64)
      (toBytesLE rdq(W, g.r8 + g.r14 + 8#64) 8) := by
    show Vst (Vst W (g.r14 + 24#64) _) (g.r14 + 32#64) _ = _
    rw [R.di]
  obtain ⟨s1, r1, d1, b1⟩ := st80 rdq(W, g.r8 + g.r14 + 8#64) C M.sv M.fr M.dir hv
  refine ⟨_, ?_, s1, r1, d1, b1, hv⟩
  rw [← e1]
  exact hA

/-- The registers of the loop after 80. -/
theorem LR.gB {g0 : Gprs} {n : Nat} {g : Gprs} (V : Addr → Byte) (R : LR S p g0 n g) : LR S p g0 n (gB V g) :=
  ⟨R.sp, R.bx, R.bp, R.di, R.r15, R.ax⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 80, the entry at offset `k` with `d_ino` not 0: it is the result. -/
theorem n80 {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {tr : List Event} {n k : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = rdd_at.add 80) (R : LR S p g0 n Y.cpu.gpr) (M : LM S p fb A g0 V₀ W n k) (hk : k < n)
    (he : Y.cpu.gpr.r8 + Y.cpu.gpr.r14 = Addr.add p (48 + k)) (hdx : Y.cpu.gpr.rdx.toNat = k)
    (hnz : rdq(W, Addr.add p (48 + k)) ≠ 0#64) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Y t := by
  have hpA := C.hpA
  have hnA := M.dir.nA
  obtain ⟨⟨h18, -⟩, hkn, -⟩ := M.ch.inv hk
  obtain ⟨f0, f8, f16, w24, w32⟩ := ft80 c.hws C R.di he (by omega)
  refine (c_80 prof fb).run c hfs hin _ hK hA hrip
    (vc_80n (g := Y.cpu.gpr) (by rw [he]; exact hnz) f0 f8 f16 w24 w32) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨W', hA', s1, r1, d1, b1, -⟩ := post80 C R M hk he hdx hA₁
  have R₁ : LR S p g0 n Y₁.cpu.gpr := by rw [hg₁]; exact R.gB W
  have r8₁ : Y₁.cpu.gpr.r8 = Addr.add p (48 + k) := by rw [hg₁]; exact he
  refine fin176 c hfs hrs hin C hK₁ hA' hr₁ R₁.sp R₁.di R₁.r15 s1 r1 d1 ?_ hT hmt0 hin₂ h₂ hra K
  rw [r8₁]
  exact Or.inr ⟨k, Ch.congr (fun i hi => b1 i (by omega)) M.ch, hk, by rw [rlB (k := k) b1 (by omega)], rfl,
    by rw [bufR 64 (j := k) (m := 8) hpA b1 (by omega)]; exact hnz⟩

/-- From 80, the entry at offset `k` with `d_ino` 0: on to 109 with the offset past it. -/
theorem z80 {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {tr : List Event} {n k : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = rdd_at.add 80)
    (R : LR S p g0 n Y.cpu.gpr) (M : LM S p fb A g0 V₀ W n k) (hk : k < n)
    (he : Y.cpu.gpr.r8 + Y.cpu.gpr.r14 = Addr.add p (48 + k)) (hdx : Y.cpu.gpr.rdx.toNat = k)
    (hz : rdq(W, Addr.add p (48 + k)) = 0#64)
    (ih : ∀ (Y' : State) (W' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem W' →
      Y'.cpu.rip = rdd_at.add 109 → LR S p g0 n Y'.cpu.gpr → LM S p fb A g0 V₀ W' n (k + rl W p k) →
      Y'.cpu.gpr.rdx.toNat = k + rl W p k → GoG prof L o tr gP gE Y' t') :
    GoG prof L o tr gP gE Y t := by
  have hnA := M.dir.nA
  obtain ⟨⟨h18, -⟩, hkn, hch⟩ := M.ch.inv hk
  obtain ⟨f0, f8, f16, w24, w32⟩ := ft80 c.hws C R.di he (by omega)
  refine (c_80 prof fb).run c hfs hin _ hK hA hrip
    (vc_80z (g := Y.cpu.gpr) (by rw [he]; exact hz) f0 f8 f16 w24 w32) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨W', hA', s1, r1, d1, b1, hdx'⟩ := post80 C R M hk he hdx hA₁
  exact ih Y₁ W' t₁ hK₁ hA' hr₁ (by rw [hg₁]; exact R.gB W)
    ⟨s1, r1, d1, Ch.congr (fun i hi => b1 i (by omega)) hch⟩
    (by rw [hg₁]; exact hdx')

end FV7z.Rdd
