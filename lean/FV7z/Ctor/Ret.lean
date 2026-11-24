import FV7z.Ctor.Inv
/-!
# A constructor that jumps to a function that only returns (PLAN.md §M, constructors)

`csuTg 12`, at `0x41c1d0`, is `endbr64; jmp f` with `f` at `0x43cd90` the function `endbr64; ret` (`nret`).

- `jret_runs`: such a constructor is a function as `Csu.csu_ok` asks, for an invariant the step from `m` to `m + 1`
  keeps the same bytes of.
- `Jc_nop`: `Jc` holds at `m + 1` with the same bytes when the constructor calls no registrar and stores nothing.
- `runs12`: `csuTg 12`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `endbr64; ret`. -/
def nret : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xc3]
/-- Where `nret` lies. -/
abbrev nret_at : Addr := 0x43cd90
theorem nret_0 : ∀ feat, Dec feat nret 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem nret_4 : ∀ feat, Dec feat nret 4 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- `endbr64; jmp e` at offset `j` of `sti`, `e` the function `endbr64; ret`: the run gets back to
`__libc_csu_init` with the bytes and the registers it keeps unchanged. -/
theorem jret_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j rel : Nat} {e : Addr} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinE : CodeIn L e nret) (htg : csuTg m = sti_at.add j)
    (hd0 : Dec prof.feat sti j (FV7z.mk .endbr64 32 [] 4))
    (hd1 : Dec prof.feat sti (j + 4) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : j + 4 < sti.length)
    (htgt : sti_at.add (j + 4 + 5) + BitVec.ofNat 64 rel = e.add 0) (hJ : ∀ V, J m V → J (m + 1) V) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs0 := hC.s0
  refine c.s_endbr hK hA hin (by omega) (hr.trans htg) hd0 ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine c.s_jmp_x hKY hAY hin hj hrY hd1 hinE (by decide) htgt ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine c.s_endbr hKZ hAZ hinE (by decide) hrZ (nret_0 _) ?_
  rintro W t₃ hKW hAW ⟨hrW, hgW⟩
  have hsW : W.cpu.gpr.rsp = sp - 64#64 := by rw [hgW, hgZ, hgY]; exact hsp
  have hl : ∀ i < 8, Foot F.data (Addr.add W.cpu.gpr.rsp i) := fun i hi => by
    rw [hsW]
    exact c.hws _ (hC.st i (by omega))
  refine c.s_ret hKW hAW hinE (by decide) hrW (nret_4 _) hl hC.code hj₂ (by rw [hsW]; exact hra) ?_
  rintro U t' hKU hAU ⟨hrU, hgU⟩
  refine k U t' V hKU hAU (hJ V hI) (fun _ _ => rfl) (fun _ _ => rfl) hrU ?_
  rw [hgU, hgW, hgZ, hgY]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Jc` at `m + 1` with the same bytes, for a constructor that calls no registrar and stores nothing. -/
theorem Jc_nop {V W : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} {S : Addr} (hm : 3 ≤ m)
    (hSn : S.toNat + 64 = sp) (hS : 7991300 + 136 ≤ sp) (hc : calls m = []) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 7981024 ∨ 7991300 ≤ x.1) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 136)
    (hs : ∀ W, (spec m).post W) (hJ : Jc V sp spec m W) : Jc V sp spec (m + 1) W :=
  Jc_chain hm hSn hS hc trivial hD hT hB hs hJ (show W = W from rfl)

/-- `csuTg 12`, at `0x41c1d0`: `endbr64; jmp nret_at`. -/
def c144 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xb7, 0x0b, 0x02, 0x00]
theorem c144_0 : ∀ feat, Dec feat c144 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c144_4 : ∀ feat, Dec feat c144 4 (FV7z.mk .jmp 64 [.rel 134071] 5) := by dec_rfl
theorem v144 : c144 <+: sti.drop 144 := by decide +kernel
theorem tg12 : csuTg 12 = sti_at.add 144 := by decide +kernel
theorem calls12 : calls 12 = [] := by decide +kernel

/-- `csuTg 12` is a function as `Csu.csu_ok` asks, for an invariant the step from `12` to `13` keeps the same
bytes of. -/
theorem runs12 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hinE : CodeIn L nret_at nret) (hJ : ∀ V, J 12 V → J 13 V) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 12 (csuTg 12) :=
  jret_runs (j := 144) (rel := 134071) c hC hin hinE tg12 (Dec.shift (j := 144) (k := 0) (c144_0 _) v144 (by decide))
    (Dec.shift (j := 144) (k := 4) (c144_4 _) v144 (by decide)) (sti_lt (by decide)) (by decide) hJ

end FV7z.Ctor
