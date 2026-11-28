import FV7z.Ecq.Loop2
import FV7z.Ecq.Loop3
import FV7z.Ecq.Loop45
import FV7z.Ecq.Tail
import FV7z.Lemmas.Env
/-!
# `CExtractCallbackConsole::QueryInterface`: the whole function (PLAN.md §M, M1)

- `rdq_Vst8`, `rdq_Vadd`: the return address read past a store apart from it.
- `Bk g₀ g`: back at the caller: `rsp` 8 up, the registers a call keeps as at `g₀`; `bk_set`.
- `ecq_ok`: from the entry, the run reaches the return address with `rax` = `S_OK` or `E_NOINTERFACE`, `rsp` 8 up
  and the registers a call keeps as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq

theorem rdq_apart {V : Addr → Byte} {a s : Addr} {bs : List Byte}
    (h : ∀ i < 8, ∀ k < bs.length, s.add i ≠ a.add k) :
    ofBytesLE 64 ((byteAddrs s 8).map (Vst V a bs)) = ofBytesLE 64 ((byteAddrs s 8).map V) := by
  congr 1
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.mp hx
  exact Vst_apart bs V a _ (h i hi)

theorem rdq_Vst8 {V : Addr → Byte} {a s : Addr} {x : BitVec 64} (h : ∀ i < 8, ∀ k < 8, s.add i ≠ a.add k) :
    ofBytesLE 64 ((byteAddrs s 8).map (Vst V a (toBytesLE x 8))) = ofBytesLE 64 ((byteAddrs s 8).map V) :=
  rdq_apart fun i hi k hk => h i hi k (by rw [toBytesLE_length] at hk; exact hk)

theorem rdq_Vadd {V : Addr → Byte} {a s : Addr} (h : ∀ i < 8, ∀ k < 4, s.add i ≠ a.add k) :
    ofBytesLE 64 ((byteAddrs s 8).map (Vadd V a)) = ofBytesLE 64 ((byteAddrs s 8).map V) :=
  rdq_apart fun i hi k hk => h i hi k (by rw [toBytesLE_length] at hk; exact hk)

/-- Back at the caller: `rsp` 8 up, the registers a call keeps as at `g₀`. -/
def Bk (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

theorem bk_set {g₀ g : Gprs} (hks : Kq g₀ g) (r : BitVec 64) :
    Bk g₀ (({ g with rax := r }).set 4 (g.rsp + 8)) := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, h10⟩ := hks
  exact ⟨by show g.rsp + 8 = _; rw [h4], h5, h6, h7, h8, h9, h10⟩

theorem bk_set' {g₀ g : Gprs} (hks : Kq g₀ g) : Bk g₀ (g.set 4 (g.rsp + 8)) := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, h10⟩ := hks
  exact ⟨by show g.rsp + 8 = _; rw [h4], h5, h6, h7, h8, h9, h10⟩

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `CExtractCallbackConsole::QueryInterface (iid, ppv)` from the entry, `ppv` (`rdx`, 8 bytes) and `this`'s
reference count (`rdi + 0x138`, 4 bytes) writable and apart from the return address, the 16 bytes of `iid` and of the
five IIDs readable: the run reaches the return address with `rax` = `S_OK` or `E_NOINTERFACE`, `rsp` 8 up and the
registers a call keeps as at the entry. -/
theorem ecq_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ecq_at)
    (fw : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (fr : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 312#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fi : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (X.cpu.gpr.rsi + BitVec.ofNat 64 j) i))
    (f1 : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7256432#64) i))
    (f2 : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255440#64) i))
    (f3 : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255424#64) i))
    (f4 : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255936#64) i))
    (f5 : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255952#64) i))
    (hd1 : ∀ i < 8, ∀ k < 8, X.cpu.gpr.rsp.add i ≠ X.cpu.gpr.rdx.add k)
    (hd2 : ∀ i < 8, ∀ k < 4, X.cpu.gpr.rsp.add i ≠ (X.cpu.gpr.rdi + 312#64).add k)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Bk X.cpu.gpr Z.cpu.gpr → (Z.cpu.gpr.rax = 0#64 ∨ Z.cpu.gpr.rax = 2147500034#64) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have f0 : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (0#64 + 7255440#64) i) := f2 0 (by decide)
  have fs : ∀ i : Nat, i < 1 → Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
    have := fi 0 (by decide) i hi
    rwa [show X.cpu.gpr.rsi + BitVec.ofNat 64 0 = X.cpu.gpr.rsi from BitVec.add_zero _] at this
  -- `*ppv = NULL`
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 24 ∧ g' = { X.cpu.gpr with rax := 0#64, rcx := 7256432#64 } ∧
      V' = Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8))
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fw fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  -- the return address past `*ppv = this + d` and the `AddRef`
  have ra : ∀ d : Addr, ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map
      (Vadd (Vst (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) X.cpu.gpr.rdx (toBytesLE d 8))
        (X.cpu.gpr.rdi + 312#64))) = e₂.add j₂ := fun d => by
    rw [rdq_Vadd hd2, rdq_Vst8 hd1, rdq_Vst8 hd1]
    exact hra
  -- from 48 with `*ppv = this + d`
  have k48 : ∀ (d : Addr) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) X.cpu.gpr.rdx (toBytesLE d 8)) →
      Y.cpu.rip = ecq_at.add 48 → Kq X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t' := by
    intro d Y t' hKY hAY hrY hks
    refine tail48 c hin hKY hAY hrY (by rw [hks.2.2.1]; exact fr) (by rw [hks.2.2.2.1]; exact hl) hin₂ h₂
      (by rw [hks.2.2.1, hks.2.2.2.1]; exact ra d) ?_
    intro Z t'' hKZ hAZ hrZ hgZ
    refine k _ Z t'' hKZ hAZ hrZ ?_ (Or.inl ?_)
    · rw [hgZ]; exact bk_set hks _
    · rw [hgZ]
      try rfl
  -- from 45: `*ppv = this`
  have k45 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) →
      Y.cpu.rip = ecq_at.add 45 → Kq X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hks
    refine (c_45 prof).run c hin
      (fun j' g' _ V' => j' = 48 ∧ g' = Y.cpu.gpr ∧
        V' = Vst (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) X.cpu.gpr.rdx (toBytesLE X.cpu.gpr.rdi 8))
      hKY hAY hrY (vc_45 (by rw [hks.1]; exact fw) fun _ => ⟨rfl, rfl, by rw [hks.1, hks.2.2.1]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    exact k48 X.cpu.gpr.rdi Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hks)
  -- from 278: `E_NOINTERFACE`
  have k278 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) →
      Y.cpu.rip = ecq_at.add 278 → Kq X.cpu.gpr Y.cpu.gpr → Y.cpu.gpr.rax = 2147500034#64 →
      GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hks hax
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_278 _) (by rw [hks.2.2.2.1]; exact hl) hin₂ h₂
      (by rw [hks.2.2.2.1, rdq_Vst8 hd1]; exact hra) ?_
    rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
    refine k _ Z t'' hKZ hAZ hrZ ?_ (Or.inr ?_)
    · rw [hgZ]; exact bk_set' hks
    · rw [hgZ]; exact hax
  -- the fifth loop
  have k240 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) →
      Y.cpu.rip = ecq_at.add 240 → Kq X.cpu.gpr Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 →
      Y.cpu.gpr.rcx = 7255952#64 → GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hks hax hcx
    refine loop5 (g₀ := X.cpu.gpr) c hin f5 (fun j hj => fi j hj) fw
      (fun Z t'' hKZ hAZ hrZ hksZ _ _ => k48 (X.cpu.gpr.rdi + 32#64) Z t'' hKZ hAZ hrZ hksZ)
      (fun Z t'' hKZ hAZ hrZ hksZ hax' _ => k278 Z t'' hKZ hAZ hrZ hksZ hax')
      15 0 rfl Y t' hKY hAY hrY hax hcx hks (fun i hi => absurd hi (Nat.not_lt_zero _))
  -- the fourth loop
  have k192 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) →
      Y.cpu.rip = ecq_at.add 192 → Kq X.cpu.gpr Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 →
      Y.cpu.gpr.rcx = 7255936#64 → GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hks hax hcx
    refine loop4 (g₀ := X.cpu.gpr) c hin f4 (fun j hj => fi j hj) fw
      (fun Z t'' hKZ hAZ hrZ hksZ _ _ => k48 (X.cpu.gpr.rdi + 24#64) Z t'' hKZ hAZ hrZ hksZ)
      (fun Z t'' hKZ hAZ hrZ hksZ hax' hcx' _ => k240 Z t'' hKZ hAZ hrZ hksZ hax' hcx')
      15 0 rfl Y t' hKY hAY hrY hax hcx hks (fun i hi => absurd hi (Nat.not_lt_zero _))
  -- the third loop, from 109
  have k109 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8)) →
      Y.cpu.rip = ecq_at.add 109 → Kq X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t' := by
    intro Y t' hKY hAY hrY hks
    refine (c_109 prof).run c hin
      (fun j' g' _ V' => j' = 128 ∧ g' = { Y.cpu.gpr with rax := 0#64, rcx := 7255424#64 } ∧
        V' = Vst V X.cpu.gpr.rdx (toBytesLE (0#64) 8))
      hKY hAY hrY (vc_109 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    refine loop3 (g₀ := X.cpu.gpr) c hin f3 (fun j hj => fi j hj) fw ?_
      (fun Z t'' hKZ hAZ hrZ hksZ hax' hcx' _ => k192 Z t'' hKZ hAZ hrZ hksZ hax' hcx')
      15 0 rfl Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; try rfl) (by rw [hg₂]) (by rw [hg₂]; exact hks)
      (fun i hi => absurd hi (Nat.not_lt_zero _))
    intro Z t'' hKZ hAZ hrZ hksZ hax' _
    refine tail158 c hin hKZ hAZ hrZ (by rw [hksZ.2.2.1]; exact fr) (by rw [hksZ.2.2.2.1]; exact hl) hin₂ h₂
      (by rw [hksZ.2.2.1, hksZ.2.2.2.1, rdq_Vadd hd2, rdq_Vst8 hd1, rdq_Vst8 hd1]; exact hra) ?_
    intro Z' t₃ hKZ' hAZ' hrZ' hgZ'
    refine k _ Z' t₃ hKZ' hAZ' hrZ' ?_ (Or.inl ?_)
    · rw [hgZ']; exact bk_set' hksZ
    · rw [hgZ']; exact hax'
  -- the first loop, and the second from its mismatch exit
  refine loop1 (g₀ := X.cpu.gpr) c hin f1 (fun j hj => fi j hj) f0 fs
    (fun Y t' hKY hAY hrY hks _ => k45 Y t' hKY hAY hrY hks) ?_
    (fun Y t' hKY hAY hrY hks _ _ => k109 Y t' hKY hAY hrY hks)
    15 0 rfl Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; try rfl) (by rw [hg₁])
    (by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (fun i hi => absurd hi (Nat.not_lt_zero _))
  intro Y t' hKY hAY hrY hks hax hcx _ he
  refine loop2 (g₀ := X.cpu.gpr) c hin f2 (fun j hj => fi j hj)
    (fun Z t'' hKZ hAZ hrZ hksZ _ => k45 Z t'' hKZ hAZ hrZ hksZ)
    (fun Z t'' hKZ hAZ hrZ hksZ _ => k109 Z t'' hKZ hAZ hrZ hksZ) 15 0 rfl Y t' hKY hAY hrY hax hcx hks ?_
  intro i hi
  obtain rfl : i = 0 := by omega
  show bq _ (X.cpu.gpr.rsi + BitVec.ofNat 64 0) = bq _ (BitVec.ofNat 64 0 + 7255440#64)
  rw [show X.cpu.gpr.rsi + BitVec.ofNat 64 0 = X.cpu.gpr.rsi from BitVec.add_zero _]
  exact he

end FV7z.Ecq
