import FV7z.Ctor.Ret
import FV7z.Lemmas.Wp
import FV7z.Lemmas.BlkOps2
/-!
# Constructors that end in `ret`: straight-line code or loops (PLAN.md §M, constructors)

- `ret_tail`: from the constructor's `ret` (in `sti`, or in a function it jumps to), back to `__libc_csu_init` as
  `Csu.Runs` asks.
- `blk_runs`: a constructor at offset `j` of `sti`, a stretch of straight-line code (`BlkA`) up to a `ret`, is a
  function as `Csu.csu_ok` asks when the stretch keeps the registers a call keeps and leaves the bytes `st V`
  (`wp`), `st` keeps the frame of `__libc_csu_init` and its arrays, and the invariant goes from `m` to `m + 1`
  through `st`.
- `cfg_runs`: the same for code with loops at `e.add j`, by `Seg.cfg` over its cut points: a constructor in `sti`
  (`e = sti_at`, `csuTg m = e.add j`), or a function a constructor jumps to (with `jmp_runs`).
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From the `ret` at offset `jr` of `code` (at `e`), with the registers a call keeps and bytes `V'` that keep the
frame of `__libc_csu_init` and its arrays, the run goes back to `__libc_csu_init` as `Csu.Runs` asks (its
continuation `k`). -/
theorem ret_tail {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {m jr j₂ t₁ : Nat} {X Y : State}
    {V V' : Addr → Byte} {e : Addr} {code : List Byte} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L e code) (hd : Dec prof.feat code jr (FV7z.mk .ret 64 [] 1)) (hjr : jr < code.length)
    (hsp : X.cpu.gpr.rsp = sp - 64#64) (hj₂ : j₂ < Csu.csu.length) (hra : rdq(V, sp - 64#64) = Csu.csu_at.add j₂)
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem V') (hrY : Y.cpu.rip = e.add jr) (hKp : Kp X.cpu.gpr Y.cpu.gpr)
    (hI : J (m + 1) V') (hst : ∀ a : Addr, (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → V' a = V a)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → J (m + 1) V' →
      (∀ a : Addr, sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat + 8 → V' a = V a) →
      (∀ a : Addr, 7829400 ≤ a.toNat ∧ a.toNat < 7830224 → V' a = V a) →
      Z.cpu.rip = Csu.csu_at.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have hsY : Y.cpu.gpr.rsp = sp - 64#64 := by rw [hKp.1]; exact hsp
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := fun i hi => by
    rw [hsY]
    exact c.hws _ (hC.st i (by omega))
  have hraY : rdq(V', Y.cpu.gpr.rsp) = Csu.csu_at.add j₂ := by
    rw [hsY, ← hra]
    exact rdq_eq (by omega) fun a h1 h2 => hst a (.inl ⟨by omega, by omega⟩)
  refine c.s_ret hKY hAY hin hjr hrY hd hl hC.code hj₂ hraY ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' V' hKZ hAZ hI (fun a ha => hst a (.inl ⟨by omega, ha.2⟩)) (fun a ha => hst a (.inr ha)) hrZ ?_
  rw [hgZ]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKp
  exact ⟨by show Y.cpu.gpr.rsp + 8#64 = _; rw [k1], k2, k3, k4, k5, k6, k7⟩

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
  refine (Sp.blkA hb).run c hin (fun j'' g' _ V' => j'' = j' ∧ Kp X.cpu.gpr g' ∧ V' = st V) hK hA
    (hr.trans htg) (wp_mono ops (fun g' _ V' h => ⟨rfl, h⟩) (hwp X.cpu.gpr X.cpu.rflags V)) ?_
  rintro j'' g fl V' ⟨rfl, hKp, rfl⟩ Y t₁ hKY hAY hrY rfl -
  exact ret_tail c hC hin hd hj' hsp hj₂ hra hKY hAY hrY hKp (hJ V hI) (hst V) k

/-- Code at offset `j` of `code` (at `e`) with loops, up to a `ret` at `jr`, is a function as `Csu.csu_ok` asks: by
`Seg.cfg` over cut points `W` with an invariant `Inv g₀ V₀` (the registers and bytes at the entry `g₀`, `V₀`) that
holds at the entry and reaches the `ret` with the registers a call keeps and bytes `R V₀`, `R` keeps the frame of
`__libc_csu_init` and its arrays, and the invariant goes from `m` to `m + 1` through `R`. -/
theorem cfg_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j jr : Nat} {W : Nat → Wpt} {a e : Addr} {code : List Byte} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L e code) (htg : a = e.add j) (hW : ∀ ℓ, Sp prof code e ℓ (W ℓ))
    (hd : Dec prof.feat code jr (FV7z.mk .ret 64 [] 1)) (hjr : jr < code.length)
    (R : (Addr → Byte) → (Addr → Byte) → Prop)
    (Inv : Gprs → (Addr → Byte) → Nat → Nat → Gprs → Rflags → (Addr → Byte) → Prop)
    (h0 : ∀ g f V, ∃ n, Inv g V j n g f V)
    (vc : ∀ g₀ V₀ ℓ n g f V, Inv g₀ V₀ ℓ n g f V → W ℓ F Wl (fun j' g' f' V' =>
      (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = jr ∧ Kp g₀ g' ∧ R V₀ V')) g f V)
    (hR : ∀ V V', R V V' → ∀ a : Addr, (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → V' a = V a)
    (hJ : ∀ V V', J m V → R V V' → J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m a := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  obtain ⟨n₀, h₀⟩ := h0 X.cpu.gpr X.cpu.rflags V
  refine c.cfg hin hW (Inv X.cpu.gpr V) (fun j' g' _ V' => j' = jr ∧ Kp X.cpu.gpr g' ∧ R V V')
    (vc X.cpu.gpr V) ?_ n₀ j hK hA (hr.trans htg) h₀
  rintro j' g fl V' ⟨rfl, hKp, hRV⟩ Y t₁ hKY hAY hrY rfl -
  exact ret_tail c hC hin hd hjr hsp hj₂ hra hKY hAY hrY hKp (hJ V V' hI hRV) (hR V V' hRV) k

/-- A byte apart from a store at a fixed address is as before. -/
theorem vo {V : Addr → Byte} {x n w : Nat} {v : BitVec w} {a : Addr} (hx : x + n < 2 ^ 64)
    (h : a.toNat < x ∨ x + n ≤ a.toNat) : Vst V (BitVec.ofNat 64 x) (toBytesLE v n) a = V a := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Tun.Vst_out V _ _ a (by rw [toBytesLE_length, e]; omega) (by rw [toBytesLE_length, e]; exact h)

/-- Bytes in `Wl` at a fixed address, from a larger stretch there. -/
theorem ft_in {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i)) {x n : Nat}
    (h1 : b ≤ x) (h2 : x + n ≤ b + m) (_h3 : b + m ≤ 2 ^ 64) :
    ∀ i < n, Foot R (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have e : Addr.add (BitVec.ofNat 64 b) (x - b + i) = Addr.add (BitVec.ofNat 64 x) i := by
    simp only [Addr.add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← e]
  exact h _ (by omega)

/-- Eight bytes at a fixed address where `V'` is `V`. -/
theorem rdq_at {V V' : Addr → Byte} {x : Nat} (hx : x + 8 < 2 ^ 64)
    (h : ∀ a : Addr, x ≤ a.toNat → a.toNat < x + 8 → V' a = V a) :
    rdq(V', BitVec.ofNat 64 x) = rdq(V, BitVec.ofNat 64 x) := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine rdq_eq (by rw [e]; omega) fun a h1 h2 => h a ?_ ?_
  · rw [e] at h1
    exact h1
  · rw [e] at h2
    exact h2

/-- Four bytes at a fixed address where `V'` is `V`. -/
theorem rdd_at {V V' : Addr → Byte} {x : Nat} (hx : x + 4 < 2 ^ 64)
    (h : ∀ a : Addr, x ≤ a.toNat → a.toNat < x + 4 → V' a = V a) :
    rdd(V', BitVec.ofNat 64 x) = rdd(V, BitVec.ofNat 64 x) := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine rdd_eq (by rw [e]; omega) fun a h1 h2 => h a ?_ ?_
  · rw [e] at h1
    exact h1
  · rw [e] at h2
    exact h2

/-- The value a store at a fixed address leaves there. -/
theorem rd_st {V : Addr → Byte} {x n w : Nat} (hw : w = 8 * n) (v : BitVec w) (hx : x + n < 2 ^ 64) :
    ofBytesLE w (List.map (Vst V (BitVec.ofNat 64 x) (toBytesLE v n)) (byteAddrs (BitVec.ofNat 64 x) n)) = v := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [Tun.rd_Vst_self V _ _ (toBytesLE_length v n) (by rw [e]; omega), ofBytesLE_toBytesLE hw]

end FV7z.Ctor
