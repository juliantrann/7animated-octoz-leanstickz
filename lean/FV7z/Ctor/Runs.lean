import FV7z.Ctor.Lea
import FV7z.Ctor.LeaJmp
import FV7z.Rga.Holds
import FV7z.Rgc.Holds
import FV7z.Rgh.Holds
import FV7z.Csu.Pre
import FV7z.Start.ArrRet
/-!
# The constructors that only call a registrar, as `__libc_csu_init` calls them (PLAN.md §M, constructors)

- `regCnt`, `regTab`, `regMax`, `regCode`: the three registrars by their number in `leas` (0 `RegisterArc`, 1
  `RegisterCodec`, 2 `RegisterHasher`): the count, the table, its size, the code.
- `reg_ok`: the registrar `r`'s contract (`Rga.rga_ok`, `Rgc.rgc_ok`, `Rgh.rgh_ok`).
- `leas_tg`: each constructor of `leas` is the entry of `.init_array` its number says (`csuTg`), in `sti`.
- `RegOut.out`: a byte apart from the table and its count is unchanged.
- `lea_runs`: `Csu.Runs` for a constructor of `leas`, for any invariant that `RegOut` of its argument takes from the
  constructor's number to the next.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- The count of the registrar `r`'s table. -/
def regCnt : Nat → Addr
  | 0 => 7991296#64
  | 1 => 7981824#64
  | _ => 7981280#64

/-- The registrar `r`'s table. -/
def regTab : Nat → Addr
  | 0 => 7990720#64
  | 1 => 7981312#64
  | _ => 7981024#64

/-- The entries of the registrar `r`'s table. -/
def regMax : Nat → Nat
  | 0 => 72
  | 1 => 64
  | _ => 32

/-- The registrar `r`'s code. -/
def regCode : Nat → List Byte
  | 0 => Rga.rga
  | 1 => Rgc.rgc
  | _ => Rgh.rgh

theorem reg_lay : ∀ r, Lay (regCnt r) (regTab r) (regMax r)
  | 0 => Rga.lay
  | 1 => Rgc.lay
  | _ + 2 => Rgh.lay

/-- The tables lie above the arrays of `__libc_csu_init`. -/
theorem reg_arr : ∀ r, 7830224 ≤ (regTab r).toNat
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => (by decide : 7830224 ≤ (7981024#64 : Addr).toNat)

theorem reg_len : ∀ r, 0 < (regCode r).length
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => (by decide : 0 < Rgh.rgh.length)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

/-- The registrar `r`'s contract, with its code in place and its count and table readable and writable. -/
theorem reg_ok (c : Seg prof F Wl L s₀ o) :
    ∀ r, CodeIn L (regAt r) (regCode r) → (∀ i < 4, Foot F.data (Addr.add (regCnt r) i)) →
      (∀ i < 4, Foot Wl (Addr.add (regCnt r) i)) → (∀ i < 8 * regMax r, Foot Wl (Addr.add (regTab r) i)) →
      RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r)
  | 0, hin, hc, hcw, ht => Rga.rga_ok c hin hc hcw ht
  | 1, hin, hc, hcw, ht => Rgc.rgc_ok c hin hc hcw ht
  | _ + 2, hin, hc, hcw, ht => Rgh.rgh_ok c hin hc hcw ht

/-- Each constructor of `leas` is the entry of `.init_array` its number says, and lies in `sti`. -/
theorem leas_tg : ∀ x ∈ leas, csuTg x.1 = sti_at.add x.2.1 ∧ x.2.1 + 16 ≤ 4624 := by decide +kernel

/-- A byte apart from the table and its count is as before the call. -/
theorem RegOut.out {cnt tab : Addr} {max : Nat} {p : BitVec 64} {V V' : Addr → Byte} (h : RegOut cnt tab max p V V')
    (hl : Lay cnt tab max) {a : Addr} (ha : a.toNat < tab.toNat ∨ cnt.toNat + 4 ≤ a.toNat) : V' a = V a := by
  unfold RegOut at h
  split at h
  · rename_i hm
    have ap := hl.ap
    exact h.2.2 a (by omega) (by omega)
  · rw [h]

/-- A constructor of `leas`, the `m`-th function `__libc_csu_init` calls, is a function as `Csu.csu_ok` asks, for an
invariant that `RegOut` of its argument takes from `m` to `m + 1`, with its registrar's contract and the frame of
`__libc_csu_init` apart from the registrar's table. -/
theorem lea_runs {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m j r A : Nat}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti) (hm : (m, j, r, A) ∈ leas)
    (hR : RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : CodeIn L (regAt r) (regCode r))
    (hfar : sp.toNat + 8 ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ sp.toNat - 64)
    (hJ : ∀ V V', J m V → RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) V V' → J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj hra k
  obtain ⟨rel, ⟨hb, hd⟩, htgt⟩ := lea_at prof hm
  obtain ⟨htg, hjl⟩ : csuTg m = sti_at.add j ∧ j + 16 ≤ 4624 := leas_tg _ hm
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have hL := reg_lay r
  have hA7 := reg_arr r
  have hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i) := fun i hi => by
    rw [hsp]
    exact c.hws _ (hC.st i (by omega))
  have h8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by rw [hsp, n]; omega
  have hap : X.cpu.gpr.rsp.toNat + 8 ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ X.cpu.gpr.rsp.toNat := by
    rw [hsp, n]
    omega
  have hra' : rdq(V, X.cpu.gpr.rsp) = Csu.csu_at.add j₂ := by rw [hsp]; exact hra
  refine lea_reg hb hd (sti_lt (by omega)) htgt c hin hinR (reg_len r) hR hK hA (hr.trans htg) hl h8 hap
    hC.code hj hra' ?_
  intro V' Z t' hKZ hAZ hO hrZ hbk
  have ap := hL.ap
  exact k Z t' V' hKZ hAZ (hJ V V' hI hO) (fun a ha => hO.out hL (by omega)) (fun a ha => hO.out hL (by omega))
    hrZ hbk

end FV7z.Ctor
