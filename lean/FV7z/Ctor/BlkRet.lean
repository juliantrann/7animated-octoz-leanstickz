import FV7z.Ctor.Ret
import FV7z.Lemmas.Wp
import FV7z.Lemmas.BlkOps2
/-!
# A constructor that is straight-line code, then `ret` (PLAN.md §M, constructors)

`blk_runs`: a constructor at offset `j` of `sti`, a stretch of straight-line code (`BlkA`) up to a `ret`, is a
function as `Csu.csu_ok` asks when the stretch keeps the registers a call keeps and leaves the bytes `st V`
(`wp`), `st` keeps the frame of `__libc_csu_init` and its arrays, and the invariant goes from `m` to `m + 1`
through `st`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- A constructor that is straight-line code up to a `ret`, its bytes after `st V`, is a function as `Csu.csu_ok`
asks. -/
theorem blk_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j j' : Nat} {ops : List Op} {st : (Addr → Byte) → Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti) (htg : csuTg m = sti_at.add j)
    (hb : BlkA prof sti sti_at j j' ops) (hd : Dec prof.feat sti j' (FV7z.mk .ret 64 [] 1)) (hj' : j' < sti.length)
    (hwp : ∀ (g : Gprs) (f : Rflags) (V : Addr → Byte), wp F Wl ops (fun g' _ V' => Kp g g' ∧ V' = st V) g f V)
    (hst : ∀ (V : Addr → Byte) (a : Addr), (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → st V a = V a)
    (hJ : ∀ V, J m V → J (m + 1) (st V)) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  refine (Sp.blkA hb).run c hin (fun j'' g' _ V' => j'' = j' ∧ Kp X.cpu.gpr g' ∧ V' = st V) hK hA
    (hr.trans htg) (wp_mono ops (fun g' _ V' h => ⟨rfl, h⟩) (hwp X.cpu.gpr X.cpu.rflags V)) ?_
  rintro j'' g fl V' ⟨rfl, hKp, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = sp - 64#64 := by rw [hgY, hKp.1]; exact hsp
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := fun i hi => by
    rw [hsY]
    exact c.hws _ (hC.st i (by omega))
  have hraY : rdq(st V, Y.cpu.gpr.rsp) = Csu.csu_at.add j₂ := by
    rw [hsY, ← hra]
    exact rdq_eq (by omega) fun a h1 h2 => hst V a (.inl ⟨by omega, by omega⟩)
  refine c.s_ret hKY hAY hin hj' hrY hd hl hC.code hj₂ hraY ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' (st V) hKZ hAZ (hJ V hI) (fun a ha => hst V a (.inl ⟨by omega, ha.2⟩))
    (fun a ha => hst V a (.inr ha)) hrZ ?_
  rw [hgZ, hgY]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKp
  exact ⟨by show g.rsp + 8 = _; rw [k1], k2, k3, k4, k5, k6, k7⟩

/-- A byte apart from a store at a fixed address is as before. -/
theorem vo {V : Addr → Byte} {x n w : Nat} {v : BitVec w} {a : Addr} (hx : x + n ≤ 2 ^ 64)
    (h : a.toNat < x ∨ x + n ≤ a.toNat) : Vst V (BitVec.ofNat 64 x) (toBytesLE v n) a = V a := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Tun.Vst_out V _ _ a (by rw [toBytesLE_length, e]; exact hx) (by rw [toBytesLE_length, e]; exact h)

/-- Bytes in `Wl` at a fixed address, from a larger stretch there. -/
theorem ft_in {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i)) {x n : Nat}
    (h1 : b ≤ x) (h2 : x + n ≤ b + m) (h3 : b + m ≤ 2 ^ 64) :
    ∀ i < n, Foot R (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have e : Addr.add (BitVec.ofNat 64 b) (x - b + i) = Addr.add (BitVec.ofNat 64 x) i := by
    simp only [Addr.add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← e]
  exact h _ (by omega)

end FV7z.Ctor
