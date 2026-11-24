import FV7z.Ctor.CfgReg
import FV7z.Lemmas.Rmw6
/-!
# `csuTg 61`: one off a byte of `.data`, then RegisterArc (PLAN.md §M, constructors)

`csuTg 61`, at `0x41c600` (offset 1216 of `sti`), takes one from the byte at `0x7921b0` and registers its handler
(`tails`):

```
endbr64; sub byte [rip + d], 1; lea rdi, [rip + d']; jmp RegisterArc
```

- `c61`, `c61_*`, `b1216`, `b1227`: its bytes, instructions and two straight-line stretches; `W61`, `c_1216`, `Wt`,
  `spAll`: the code as one piece for `Seg.cfg` (`Sp.sub_rip8_then` for the `sub`), up to the `jmp` at 1234.
- `st61 V`: the bytes after; `st61_out`: the same as `V` apart from the byte.
- `Inv`, `vc_1216`, `vc`: one cut point, the entry, from which the code reaches the `jmp` with `rdi` the handler's
  record.
- `runs61`: `csuTg 61` is a function as `Csu.csu_ok` asks (`cfg_reg_runs`), for an invariant that goes from `61` to
  `62` through `st61` and then `RegOut`; `runs61_jg`: for `Jg`, with `spec 61 = stSpec st61 V wr61` (`jg_streg`).
-/
namespace FV7z.C61
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 61`. -/
def c61 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x2d, 0xa5, 0x5b, 0x37, 0x00, 0x01, 0x48, 0x8d, 0x3d, 0x6e, 0x0b,
  0x36, 0x00, 0xe9, 0x09, 0x25, 0x1b, 0x00]
theorem c61_0 : ∀ feat, Dec feat c61 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c61_4 : ∀ feat, Dec feat c61 4 (FV7z.mk .sub 8 [.mem (mrip 3627941 8), .imm 8 1] 7) := by dec_rfl
theorem c61_11 : ∀ feat, Dec feat c61 11 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3541870 0)] 7) := by dec_rfl
theorem c61_18 : ∀ feat, Dec feat c61 18 (FV7z.mk .jmp 64 [.rel 1778953] 5) := by dec_rfl
theorem v61 : c61 <+: sti.drop 1216 := by decide +kernel
theorem tg61 : csuTg 61 = sti_at.add 1216 := by decide +kernel

theorem q1216 (prof : Profile) : BlkA prof c61 (0x41c600 : Addr) 0 4 [Op.nop] :=
  .cons (c61_0 _) ((OpI.endbr).at _) (by decide) <|
  .nil 4
theorem b1216 (prof : Profile) : BlkA prof sti sti_at 1216 1220 [Op.nop] :=
  (q1216 prof).shift (by decide) v61
theorem q1227 (prof : Profile) : BlkA prof c61 (0x41c600 : Addr) 11 18 [Op.mov 64 7 (.i 7852416)] :=
  .cons (c61_11 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 18
theorem b1227 (prof : Profile) : BlkA prof sti sti_at 1227 1234 [Op.mov 64 7 (.i 7852416)] :=
  (q1227 prof).shift (by decide) v61
theorem d1220 (feat : Features) : Dec feat sti 1220 (FV7z.mk .sub 8 [.mem (mrip 3627941 8), .imm 8 1] 7) :=
  Dec.shift (j := 1216) (k := 4) (c61_4 _) v61 (by decide)
theorem d1234 (feat : Features) : Dec feat sti 1234 (FV7z.mk .jmp 64 [.rel 1778953] 5) :=
  Dec.shift (j := 1216) (k := 18) (c61_18 _) v61 (by decide)
theorem g1220 : sti_at.add (1220 + 7) + BitVec.ofNat 64 3627941 = 7938480#64 := by decide
theorem htgt61 : sti_at.add (1234 + 5) + BitVec.ofNat 64 1778953 = (regAt 0).add 0 := by decide

/-- The bytes after the `sub`: the byte at `0x7921b0` one less. -/
def st61 (V : Addr → Byte) : Addr → Byte :=
  Vst V 7938480#64 (toBytesLE (ofBytesLE 8 ((byteAddrs 7938480#64 1).map V) - BitVec.ofNat 8 1) 1)

/-- What the code needs for `Q` at the `jmp`. -/
def W61 : Wpt := fun F Wl Q => wp F Wl [Op.nop] fun g _ V => (∀ i < 1, Foot Wl (Addr.add 7938480#64 i)) ∧
  ∀ fl, wp F Wl [Op.mov 64 7 (.i 7852416)] (Q 1234) g fl (st61 V)

theorem c_1216 (prof : Profile) : Sp prof sti sti_at 1216 W61 :=
  Sp.blkA_then (b1216 prof) (Sp.sub_rip8_then (d1220 _) (sti_lt (by decide)) g1220
    (Sp.blkA_then (b1227 prof) (Sp.skip 1234)))

/-- The one cut point. -/
def Wt (ℓ : Nat) : Wpt := if ℓ = 1216 then W61 else fun _ _ _ _ _ _ => False

theorem spAll (prof : Profile) (ℓ : Nat) : Sp prof sti sti_at ℓ (Wt ℓ) :=
  Sp.table (c_1216 prof) <| Sp.never ℓ

/-- The invariant: the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  ℓ = 1216 ∧ n = 0 ∧ g = g₀ ∧ V = V₀

/-- From the entry to the `jmp`: `rdi` the handler's record, the byte one less. -/
theorem vc_1216 (hw : ∀ i < 1, Foot Wl (Addr.add 7938480#64 i)) {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (Q : Post) (hQ : ∀ g' f', Kp g g' → g'.rdi = BitVec.ofNat 64 7852416 → Q 1234 g' f' (st61 V)) :
    W61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W61]
  intros
  refine ⟨hw, fun _ => ?_⟩
  intros
  exact hQ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- The code from the cut point reaches the `jmp` with the registers a call keeps, `rdi` the handler's record and
the bytes `st61` of those at the entry. -/
theorem vc (hw : ∀ i < 1, Foot Wl (Addr.add 7938480#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs)
    (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨
      (j' = 1234 ∧ Kp g₀ g' ∧ g'.rdi = BitVec.ofNat 64 7852416 ∧ V' = st61 V₀)) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  simp only [Wt, ↓reduceIte]
  exact vc_1216 hw _ fun g' f' h1 h2 => Or.inr ⟨rfl, h1, h2, rfl⟩

/-- `st61 V` is `V` apart from the byte. -/
theorem st61_out (V : Addr → Byte) (a : Addr) (h : a.toNat < 7938480 ∨ 7938481 ≤ a.toNat) : st61 V a = V a :=
  Tun.Vst_out V _ _ a (by rw [toBytesLE_length]; decide)
    (by rw [toBytesLE_length, show (7938480#64 : Addr).toNat = 7938480 from rfl]; omega)

/-- The byte `csuTg 61` stores and reads. -/
def wr61 : List (Nat × Nat) := [(7938480, 7938481)]

theorem calls61 : calls 61 = [(0, 7852416)] := by decide +kernel
theorem wrT61 : ∀ x ∈ wr61, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- RegisterArc's table has room for the call. -/
theorem fits61 : Fits (regsAt 61) [(0, 7852416)] := by
  have h := fits_all 61 (by decide)
  rw [calls61] at h
  exact fits_of h

theorem st61_kept (V : Addr → Byte) (a : Addr) (h : ¬ InR wr61 a.toNat) : st61 V a = V a := by
  simp only [wr61, InR, or_false] at h
  exact st61_out V a (by omega)

theorem st61_rd (V W : Addr → Byte) (h : ∀ a : Addr, InR wr61 a.toNat → W a = V a) (a : Addr)
    (ha : InR wr61 a.toNat) : st61 W a = st61 V a := by
  have hb := ha
  simp only [wr61, InR, or_false] at hb
  have ea : a = 7938480#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hg : W 7938480#64 = V 7938480#64 := by
    rw [← ea]
    exact h a ha
  unfold st61
  rw [Tun.rd1, Tun.rd1, hg]
  exact vin (by decide) (by omega) (by omega)

/-- `csuTg 61` is a function as `Csu.csu_ok` asks, for an invariant that goes from `61` to `62` through `st61` and
then `RegOut` of the handler's record, with RegisterArc's contract. -/
theorem runs61 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hw : ∀ i < 1, Foot Wl (Addr.add 7938480#64 i)) (hsp : 7991300 + 64 ≤ sp.toNat)
    (hR : RegSpec prof F Wl L s₀ o (regAt 0) (regCnt 0) (regTab 0) (regMax 0))
    (hinR : CodeIn L (regAt 0) (regCode 0))
    (hJ : ∀ V V'', J 61 V → RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7852416) (st61 V) V'' →
      J 62 V'') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 61 (csuTg 61) :=
  cfg_reg_runs c hC hin tg61 (spAll prof) (d1234 _) (sti_lt (by decide)) htgt61 hinR (reg_len 0) hR (reg_lay 0)
    (reg_arr 0) (.inr (by rw [show (regCnt 0).toNat = 7991296 from rfl]; omega)) (fun V V' => V' = st61 V) Inv
    (fun _ _ _ => ⟨0, And.intro rfl ⟨rfl, rfl, rfl⟩⟩) (vc hw)
    (fun V V' h a ha => by rw [h]; exact st61_out V a (by omega)) fun V V' V'' hI h hO => hJ V V'' hI (h ▸ hO)

/-- `csuTg 61` for `Jg`, its spec `stSpec st61 V wr61`. -/
theorem runs61_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hw : ∀ i < 1, Foot Wl (Addr.add 7938480#64 i)) (hsp : 7991300 + 136 ≤ sp.toNat)
    (hR : RegSpec prof F Wl L s₀ o (regAt 0) (regCnt 0) (regTab 0) (regMax 0))
    (hinR : CodeIn L (regAt 0) (regCode 0)) (hspec : spec 61 = stSpec st61 V wr61) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < 61 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr61, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W'', G 61 W → RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7852416) (st61 W) W'' →
      G 62 W'') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 61 (csuTg 61) :=
  runs61 c hC hin hw (by omega) hR hinR fun W W'' hJ hO =>
    jg_streg (rd := wr61) (by decide) calls61 fits61 hspec hD hT hXw hXw
      (fun n hn => by simp only [wr61, InR, or_false] at hn; unfold Pre; omega)
      (fun W h a ha => st61_rd V W h a ha) st61_kept hO (hG W W'' · hO) hJ

end FV7z.C61
