import FV7z.Rdd.Holds
import FV7z.Opd.Ok
/-!
# `__readdir` from its entry to its return (PLAN.md §M, M1)

The pieces of `Rdd.Holds` joined. Below, `S` is `rsp` at the entry, `p` the `DIR` (`rdi`), `A` its allocation,
`T` = `S - 8 - 8 - 8 - 8 - 8` (`rsp` after the five pushes), `g0` the registers at the entry, `V₀` the bytes there.

Assumptions: one thread (`fs:0x18` = 0, `rdd(V₀, fb + 24#64) = 0#32`), the lock 0 at the entry; `NzIno o` (the
kernel never gives `d_ino` 0, so after a `getdents` the first entry is returned and there is no second call);
`errno` may change.

- `Dir V p A w n k`: the lock word `w`, the allocation `A`, the size `n ≤ A`, the offset `k`.
- `RSv S g0 W`: the five saved registers at `T`, `T + 8`, ….
- `RFr S p fb A V₀ W`: all bytes but the frame `[S - 48, S)`, the `DIR` `[p, p + 48 + A)` and `errno` as in `V₀`.
- `RS W p n k r`: the result `r`: null with the buffer used up (`k = n`), or the entry at offset `k₀` of a chain
  (`Ch`) with `d_ino` not 0, the offset past it.
- `Res W p A r`: `W` is the bytes `RS` speaks of with the lock word stored back to 0.
- `RddK`: the run after the return.
- `fin176`: from 176 (the lock given back, the pops, the `ret`) to `RddK`.

The rest of the function is in the modules after this one: `n80`, `z80` (`Rdd.Scan`, from 80), `gd_err`, `gd_zero`,
`gd_pos` (`Rdd.Br`, after `getdents64`), `step109` and `scan` (`Rdd.Loop`, the loop at 109 by induction on `n - k`),
`rdd_gd` and `rdd_ok` (`Rdd.Main`, `__getdents` from 128, and the entry to 109).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}

/-! ## The invariants -/

/-- The `DIR` at `p`: the lock word `w`, the allocation `A`, the size `n ≤ A`, the offset `k`. -/
structure Dir (V : Addr → Byte) (p : Addr) (A : Nat) (w : BitVec 32) (n k : Nat) : Prop where
  lk : rdd(V, p + 4#64) = w
  al : (rdq(V, p + 8#64)).toNat = A
  sz : (rdq(V, p + 16#64)).toNat = n
  nA : n ≤ A
  of : (rdq(V, p + 24#64)).toNat = k

/-- The five registers saved by the pushes, where the pops read them. -/
def RSv (S : Addr) (g0 : Gprs) (W : Addr → Byte) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) = g0.r13 ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) = g0.r14

/-- All bytes but the frame `[S - 48, S)`, the `DIR` `[p, p + 48 + A)` and `errno` as in `V₀`. -/
def RFr (S p fb : Addr) (A : Nat) (V₀ W : Addr → Byte) : Prop :=
  ∀ a : Addr, (a.toNat < S.toNat - 48 ∨ S.toNat ≤ a.toNat) → (a.toNat < p.toNat ∨ p.toNat + 48 + A ≤ a.toNat) →
    ¬ Opd.ER fb a → W a = V₀ a

/-- The result `r` with the size `n` and the offset `k`: null with the buffer used up, or the entry at `k₀` of a
chain, `d_ino` not 0, the offset past it. -/
def RS (V : Addr → Byte) (p : Addr) (n k : Nat) (r : BitVec 64) : Prop :=
  (r = 0#64 ∧ k = n) ∨
    ∃ k₀, Ch V p n k₀ ∧ k₀ < n ∧ k = k₀ + rl V p k₀ ∧ r = Addr.add p (48 + k₀) ∧ rdq(V, r) ≠ 0#64

/-- The bytes at the end: those `RS` speaks of, the lock word stored back to 0. -/
def Res (W : Addr → Byte) (p : Addr) (A : Nat) (r : BitVec 64) : Prop :=
  ∃ (W₁ : Addr → Byte) (n k : Nat), W = Vst W₁ (p + 4#64) (toBytesLE 0#32 4) ∧ Dir W₁ p A 1#32 n k ∧ RS W₁ p n k r

/-- The events: none, or one `getdents64`. -/
def RdT (gev tr : List Event) : Prop := tr = gev ∨ ∃ G r, tr = gev ++ [Gdn.gdE G r]

/-- The kernel never gives `d_ino` 0. -/
def NzIno (o : Oracle) : Prop := ∀ t s, ∀ e ∈ (dentsRes o t s).es, e.ino ≠ 0#64

/-- What the run needs of the stack, the `DIR`, `errno` and `fs:0x18`. -/
structure RdC (F : Footprint) (Wl : List Rgn) (S p fb : Addr) (A : Nat) : Prop where
  h48 : 48 ≤ S.toNat
  hS8 : S.toNat + 8 ≤ 2 ^ 64
  sw : ∀ i < 48, Foot Wl (Addr.add (S - 48#64) i)
  sr : ∀ i < 8, Foot F.data (Addr.add S i)
  hA : A ≤ 2147483647
  hpA : p.toNat + 48 + A < 2 ^ 64
  pw : ∀ i < 48 + A, Foot Wl (Addr.add p i)
  fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)
  hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64
  fm : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)
  hfm : (fb + 24#64).toNat + 4 ≤ 2 ^ 64
  dS : p.toNat + 48 + A ≤ S.toNat - 48 ∨ S.toNat + 8 ≤ p.toNat
  eS : (errnoAt fb).toNat + 4 ≤ S.toNat - 48 ∨ S.toNat + 8 ≤ (errnoAt fb).toNat
  mS : (fb + 24#64).toNat + 4 ≤ S.toNat - 48 ∨ S.toNat + 8 ≤ (fb + 24#64).toNat
  eD : (errnoAt fb).toNat + 4 ≤ p.toNat ∨ p.toNat + 48 + A ≤ (errnoAt fb).toNat
  mD : (fb + 24#64).toNat + 4 ≤ p.toNat ∨ p.toNat + 48 + A ≤ (fb + 24#64).toNat
  mE : (errnoAt fb).toNat + 4 ≤ (fb + 24#64).toNat ∨ (fb + 24#64).toNat + 4 ≤ (errnoAt fb).toNat

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The run after `__readdir` (registers `g0`, bytes `V₀`, events `gev` before it), from its return to `e₂ + j₂`,
perhaps from a new start after `getdents64`. -/
def RddK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (S p fb : Addr) (A : Nat)
    (g0 : Gprs) (V₀ : Addr → Byte) (e₂ : Addr) (j₂ : Nat) (gev : List Event) : Prop :=
  ∀ (s Z : State) (tr : List Event) (W : Addr → Byte) (t' : Nat), Seg prof F Wl L s o → s.cpu.seg.fsBase = fb →
    s.thread.rseq = none → KeptW Wl s Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ →
    Z.cpu.gpr.rsp = S + 8#64 → Opd.Keeps g0 Z.cpu.gpr → RFr S p fb A V₀ W → RdT gev tr →
    Res W p A Z.cpu.gpr.rax → GoG prof L o tr gP gE Z t'

/-! ## Helpers -/

/-- The stack addresses. -/
theorem stR (S : Addr) (h : 48 ≤ S.toNat) :
    (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 ∧ (S - 8 - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 48 ∧
      (S - 48#64).toNat = S.toNat - 48 ∧ (S - 8 - 8 - 8 - 8 - 8 + 8).toNat = S.toNat - 32 ∧
      (S - 8 - 8 - 8 - 8 - 8 + 8 + 8).toNat = S.toNat - 24 ∧
      (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧
      (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 := by
  have hS := S.isLt
  have b1 : (S - 8).toNat = S.toNat - 8 := Opd.tSub S 8 (by omega)
  have b2 : (S - 8 - 8).toNat = S.toNat - 16 := (Opd.tSub (S - 8) 8 (by omega)).trans (by omega)
  have b3 : (S - 8 - 8 - 8).toNat = S.toNat - 24 := (Opd.tSub (S - 8 - 8) 8 (by omega)).trans (by omega)
  have b4 : (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 := (Opd.tSub (S - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b5 : (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 :=
    (Opd.tSub (S - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b6 : (S - 8 - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 48 :=
    (Opd.tSub (S - 8 - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b7 : (S - 48#64).toNat = S.toNat - 48 := Opd.tSub S 48 (by omega)
  have a1 : (S - 8 - 8 - 8 - 8 - 8 + 8).toNat = S.toNat - 32 :=
    (Opd.tAdd (S - 8 - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have a2 : (S - 8 - 8 - 8 - 8 - 8 + 8 + 8).toNat = S.toNat - 24 :=
    (Opd.tAdd (S - 8 - 8 - 8 - 8 - 8 + 8) 8 (by omega)).trans (by omega)
  have a3 : (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8).toNat = S.toNat - 16 :=
    (Opd.tAdd (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) 8 (by omega)).trans (by omega)
  have a4 : (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 :=
    (Opd.tAdd (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) 8 (by omega)).trans (by omega)
  exact ⟨b5, b6, b7, a1, a2, a3, a4⟩

/-- The pops undo the pushes (not `bv_omega`: ten wrapping atoms blow it up). -/
theorem pS5 (S : Addr) : S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8 + 8 = S := by
  rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel, BitVec.sub_add_cancel, BitVec.sub_add_cancel,
    BitVec.sub_add_cancel]

/-- A read through bytes that agree on it. -/
theorem rdE (w : Nat) {V V' : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → V' a = V a) :
    ofBytesLE w (List.map V' (byteAddrs x n)) = ofBytesLE w (List.map V (byteAddrs x n)) :=
  congrArg (ofBytesLE w) (Sbrk.rd_eq hx h)

/-- The registers after the pops and the `ret`. -/
theorem gP5s (V : Addr → Byte) (g : Gprs) (v : BitVec 64) :
    ((gP5 V g).set 4 v).rsp = v ∧ ((gP5 V g).set 4 v).rax = g.r8 ∧ ((gP5 V g).set 4 v).rbx = rdq(V, g.rsp) ∧
      ((gP5 V g).set 4 v).rbp = rdq(V, g.rsp + 8) ∧ ((gP5 V g).set 4 v).r12 = rdq(V, g.rsp + 8 + 8) ∧
      ((gP5 V g).set 4 v).r13 = rdq(V, g.rsp + 8 + 8 + 8) ∧
      ((gP5 V g).set 4 v).r14 = rdq(V, g.rsp + 8 + 8 + 8 + 8) ∧ ((gP5 V g).set 4 v).r15 = g.r15 := by
  cases g
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## From 176 to the return -/

/-- From 176 (one thread: the lock given back, the pops, the `ret`) to the run after the return. -/
theorem fin176 {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {tr : List Event} {n k : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (C : RdC F Wl S p fb A) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = rdd_at.add 176) (hsp : Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8) (h14 : Y.cpu.gpr.r14 = p)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hsv : RSv S g0 W) (hfr : RFr S p fb A V₀ W) (hD : Dir W p A 1#32 n k)
    (hR : RS W p n k Y.cpu.gpr.r8) (hT : RdT gev tr) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o tr gP gE Y t := by
  obtain ⟨b5, -, b7, a1, a2, a3, a4⟩ := stR S C.h48
  have hS := S.isLt
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have dS := C.dS
  have t4 : (p + 4#64).toNat = p.toNat + 4 := Opd.tAdd p 4 (by omega)
  have hmt : rdd(W, fb + 24#64) = 0#32 := by
    have mS := C.mS
    have mD := C.mD
    have mE := C.mE
    rw [rdE 32 (V := V₀) (V' := W) C.hfm fun a x1 x2 => hfr a (by omega) (by omega)
      fun he => by obtain ⟨e1, e2⟩ := he; omega]
    exact hmt0
  -- 176: `eax` 0
  refine (c_176 prof fb).run c hfs hin _ hK hA hrip (vc_176 (g := Y.cpu.gpr) hmt C.fm) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  -- 188: the lock given back
  have ea : eaD Y₁ 14 4 = p + 4#64 := by
    rw [eaD, hg₁]
    show Y.cpu.gpr.r14 + _ = _
    rw [h14]
  have pw4 : ∀ i < 4, Foot Wl (Addr.add (p + 4#64) i) :=
    Opd.frw C.pw (Opd.fa (B := p) (d := 4) (by omega) t4) (by omega)
  refine c.s_sub_mi32 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (sb_188 _) (by rw [ea]; exact pw4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea, hD.lk, show (1#32 : BitVec 32) - BitVec.ofNat 32 1 = 0#32 by decide] at hA₂
  have g2 : Y₂.cpu.gpr = { Y.cpu.gpr with rax := 0#64 } := hg₂.trans hg₁
  have sp2 : Y₂.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8 := (congrArg Gprs.rsp g2).trans hsp
  -- 193: the pops
  have swd : ∀ i < 48, Foot F.data (Addr.add (S - 48#64) i) := fun i hi => c.hws _ (C.sw i hi)
  have q : ∀ (x : Addr) (d : Nat), d + 8 ≤ 48 → x.toNat = S.toNat - 48 + d →
      ∀ i < 8, Foot F.data (Addr.add x i) := fun x d hd hx =>
    Opd.frw swd (Opd.fa (B := S - 48#64) (d := d) (by omega) (by rw [hx, b7])) (by omega)
  refine (c_193 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_193 (g := Y₂.cpu.gpr)
    (by rw [sp2]; exact q (S - 8 - 8 - 8 - 8 - 8) 8 (by omega) (by rw [b5]; omega))
    (by rw [sp2]; exact q (S - 8 - 8 - 8 - 8 - 8 + 8) 16 (by omega) (by rw [a1]; omega))
    (by rw [sp2]; exact q (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) 24 (by omega) (by rw [a2]; omega))
    (by rw [sp2]; exact q (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) 32 (by omega) (by rw [a3]; omega))
    (by rw [sp2]; exact q (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) 40 (by omega) (by rw [a4]; omega))) ?_
  rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  -- 204: the `ret`
  have sp3 : Y₃.cpu.gpr.rsp = S :=
    ((congrArg Gprs.rsp hg₃).trans (congrArg (fun x : Addr => x + 8 + 8 + 8 + 8 + 8) sp2)).trans (pS5 S)
  have rS : rdq(Vst W (p + 4#64) (toBytesLE 0#32 4), S) = e₂.add j₂ := by
    have eS := C.eS
    rw [rd_Vst W (p + 4#64) (toBytesLE 0#32 4) S 8 (by rw [toBytesLE_length]; omega) hS8
      (by rw [toBytesLE_length, t4]; omega),
      rdE 64 (V := V₀) (V' := W) hS8 fun a x1 x2 =>
        hfr a (Or.inr x1) (by omega) fun he => by obtain ⟨e1, e2⟩ := he; omega]
    exact hra
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_204 _) (by rw [sp3]; exact C.sr) hin₂ h₂
    (by rw [sp3]; exact rS) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have gZ : Z.cpu.gpr = (gP5 (Vst W (p + 4#64) (toBytesLE 0#32 4)) Y₂.cpu.gpr).set 4 (S + 8) := by
    rw [hgZ, sp3, hg₃]
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := gP5s (Vst W (p + 4#64) (toBytesLE 0#32 4)) Y₂.cpu.gpr (S + 8)
  have sl : ∀ (x : Addr) (d : Nat), d + 8 ≤ 40 → x.toNat = S.toNat - 40 + d →
      rdq(Vst W (p + 4#64) (toBytesLE 0#32 4), x) = rdq(W, x) := fun x d hd hx => by
    rw [rd_Vst W (p + 4#64) (toBytesLE 0#32 4) x 8 (by rw [toBytesLE_length]; omega) (by omega)
      (by rw [toBytesLE_length, t4, hx]; omega)]
  have r8e : Y₂.cpu.gpr.r8 = Y.cpu.gpr.r8 := by rw [g2]
  refine K s₀ Z tr _ t' c hfs hrs hKZ hAZ hrZ (by rw [gZ]; exact z1) (by
    unfold Opd.Keeps
    exact ⟨by rw [gZ, z3, sp2, sl (S - 8 - 8 - 8 - 8 - 8) 0 (by omega) (by rw [b5]; omega)]; exact hsv.1,
      by rw [gZ, z4, sp2, sl (S - 8 - 8 - 8 - 8 - 8 + 8) 8 (by omega) (by rw [a1]; omega)]; exact hsv.2.1,
      by rw [gZ, z5, sp2, sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) 16 (by omega) (by rw [a2]; omega)]; exact hsv.2.2.1,
      by rw [gZ, z6, sp2, sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) 24 (by omega) (by rw [a3]; omega)]
         exact hsv.2.2.2.1,
      by rw [gZ, z7, sp2, sl (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) 32 (by omega) (by rw [a4]; omega)]
         exact hsv.2.2.2.2,
      by rw [gZ, z8]; exact (congrArg Gprs.r15 g2).trans h15⟩)
    (by
      unfold RFr
      intro a x1 x2 x3
      rw [Vst_out W (p + 4#64) (toBytesLE 0#32 4) a (by rw [toBytesLE_length]; omega)
        (by rw [toBytesLE_length, t4]; omega)]
      exact hfr a x1 x2 x3) hT (by unfold Res; exact ⟨W, n, k, rfl, hD, by rw [gZ, z2, r8e]; exact hR⟩)

end FV7z.Rdd
