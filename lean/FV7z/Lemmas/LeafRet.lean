import FV7z.Lemmas.Wp
import FV7z.Lemmas.FnSteps
import FV7z.Tun.Inv
/-!
# Leaves of one stretch, then `ret` (PLAN.md §M, M1)

A function whose code from its entry is one stretch of straight-line code (`ops`, its `Sp` from the generator) to a
`ret` at `n`: what the stretch leaves (registers `G`, bytes `V'`, its verification condition `wp … ops`) is what the
caller finds at its return address, the return address popped (`leaf_ok`). 7-Zip has many such: `AddRef`s, counts of
properties, tests of a field.

- `leaf_ok`: the run from the entry to the return address.
- `arOps`, `arCnt`, `addref_vc`, `addref_ok`: `AddRef` (`++this->count` at `this + d`, the new count returned).
- `lf_xz`, `lf_setb`: `xor eax, eax` and `setcc al` after it.
-/
open ZellicX86 Decode FV7z.Leaf

namespace FV7z.Fn

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- From the entry of a leaf of one stretch `ops` to its `ret` at `n`, to the return address: the registers the
stretch leaves (`G`, the same `rsp`) with the return address popped, its bytes `V'`. -/
theorem leaf_ok {code : List Byte} {e : Addr} {ops : List Op} {n : Nat}
    (c0 : Sp prof code e 0 fun F Wl Q => wp F Wl ops (Q n)) (hd : Dec prof.feat code n (FV7z.mk .ret 64 [] 1))
    (hj : n < code.length) (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e code) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e) {G : Gprs} {V' : Addr → Byte}
    (vc : wp F Wl ops (fun g' _ V'' => g' = G ∧ V'' = V') X.cpu.gpr X.cpu.rflags V) (hsp' : G.rsp = X.cpu.gpr.rsp)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V') = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = G.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c0.run c hin (fun j' g' _ V'' => j' = n ∧ g' = G ∧ V'' = V') hK hA (by rw [addr_add_zero]; exact hrip)
    (wp_mono ops (fun _ _ _ h => ⟨rfl, h⟩) vc) ?_
  rintro j' g fl V₁ ⟨hj', hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  have hgY' : Y.cpu.gpr = G := hgY.trans hg
  have hAY' : Agree F Y.proc.mm.mem V' := hV ▸ hAY
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY']; exact hsp'
  have hrY' : Y.cpu.rip = e.add n := by rw [← hj']; exact hrY
  refine c.s_ret hKY hAY' hin hj hrY' hd (fun i hi => by rw [hspY]; exact hl i hi) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t' hKZ hAZ hrZ (by rw [hgZ, hspY, hgY'])

/-- `xor r32, r32`. -/
theorem lf_xz (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x) = 0 := by
  rw [BitVec.xor_self]
  decide

/-- `setcc al` after `xor eax, eax`: `rax` is the condition. -/
theorem lf_setb (g : Gprs) (c : Bool) :
    wrLo (g.set 0 0) 0 ((BitVec.ofBool c).setWidth 8) = g.set 0 ((BitVec.ofBool c).setWidth 64) := by
  cases g
  cases c <;> rfl

/-! ## `AddRef` -/

/-- `AddRef` with the count at `this + d`: `mov eax, [rdi + d]; add eax, 1; mov [rdi + d], eax` (after `endbr64`). -/
def arOps (d : Nat) : List Op :=
  [Op.nop, Op.ld 32 0 (some 7) none 1 d, Op.add 32 0 (.i 1), Op.st 32 (some 7) none 1 d 0]

/-- The count at `a`. -/
abbrev arCnt (V : Addr → Byte) (a : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs a 4).map V)

/-- `AddRef`'s stretch: the count one more, in `eax` and at `this + d`. -/
theorem addref_vc {d : Nat} {g : Gprs} {f : Rflags}
    (fa : ∀ i < 4, Foot F.data (Addr.add (g.rdi + BitVec.ofNat 64 d) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (g.rdi + BitVec.ofNat 64 d) i)) :
    wp F Wl (arOps d) (fun g' _ V' =>
      g' = g.set 0 ((arCnt V (g.rdi + BitVec.ofNat 64 d) + 1#32).setWidth 64) ∧
      V' = Vst V (g.rdi + BitVec.ofNat 64 d) (toBytesLE (arCnt V (g.rdi + BitVec.ofNat 64 d) + 1#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa fw ⊢
  wpx [arOps, arCnt]
  first
  | exact ⟨fa, fw⟩
  | exact ⟨fa, fw, rfl, rfl⟩
  | exact ⟨fa, fw, rfl⟩
  | exact ⟨fa, ⟨fw, rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => ⟨fw, rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => fw⟩

/-- `AddRef` (the count at `this + d`, `this` in `rdi`) from its entry to the return address: the count at
`this + d` one more, and in `eax`. -/
theorem addref_ok {code : List Byte} {e : Addr} {d : Nat}
    (c0 : Sp prof code e 0 fun F Wl Q => wp F Wl (arOps d) (Q 13))
    (hd : Dec prof.feat code 13 (FV7z.mk .ret 64 [] 1)) (hj : 13 < code.length)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e code) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = e)
    (fa : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 d) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 d) i))
    (hfa : (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rdi + BitVec.ofNat 64 d)
        (toBytesLE (arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 d) + 1#32) 4)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (X.cpu.gpr.set 0 ((arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 d) + 1#32).setWidth 64)).set 4
        (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hb : (toBytesLE (arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 d) + 1#32) 4).length = 4 := toBytesLE_length _ _
  have h1 : (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat +
      (toBytesLE (arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 d) + 1#32) 4).length ≤ 2 ^ 64 := by rw [hb]; exact hfa
  have h2 : (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat +
      (toBytesLE (arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 d) + 1#32) 4).length ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + BitVec.ofNat 64 d).toNat := by rw [hb]; exact hsa
  exact leaf_ok c0 hd hj c hin hK hA hrip (addref_vc fa fw) rfl hl hin₂ h₂
    (by rw [Tun.rd_Vst V _ _ X.cpu.gpr.rsp 8 h1 hsp h2]; exact hra) k

end FV7z.Fn
