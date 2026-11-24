import FV7z.C87.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
import FV7z.Ctor.CfgJ
import FV7z.Ctor.Tab
/-!
# `csuTg 87`: three tables from the image's counts (PLAN.md §M, constructors)

`csuTg 87`, at offset 2160 of `sti`, fills three tables, all in `wr87` (`0x79db40` up to `0x79ebbc`):

- for each `d < 31`, the `t3 d` bytes from `0x79dc20 + S3 d` with `d` (`t3` at `0x6e69a0`), 799 bytes in all;
- the 799 words from `0x79df40`, each from the byte of the first table at its index;
- the 54 words from `0x79db40`, each from a byte of the image's table at `0x6e6960`;

and returns. It keeps the registers a call keeps and the stack; no later code takes the tables' bytes as an address,
so its spec says only where they lie (`wrSpec wr87`).

- `T3`: the image's table of counts; `fc`, `f8`: what the code needs of it, by the kernel.
- `Inv`: the invariant at the 7 cut points (`Cuts.lean`): the entry; the first loops' store (`2208`), head (`2233`)
  and step past a count 0 (`2250`); the start of the second loop (`2272`); the second and third loops (`2296`,
  `2364`).
- `vc_*`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the `ret`.
- `runs87`: `csuTg 87` is a function as `Csu.csu_ok` asks (`cfg_runsJ`: the entry needs the table of counts);
  `runs87_jg`: for `Jg` (`jg_wr`).
-/
namespace FV7z.C87
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The image's table -/

/-- The counts (`0x6e69a0`). -/
def t3 (d : Nat) : Nat :=
  [8, 0, 9, 7, 10, 15, 15, 20, 20, 30, 33, 40, 42, 45, 60, 73, 80, 85, 95, 105, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1].getD d 0

/-- Where the run `d` of the first table starts. -/
def S3 : Nat → Nat
  | 0 => 0
  | d + 1 => S3 d + t3 d

theorem fc : ∀ d < 31, t3 d < 256 ∧ S3 (d + 1) ≤ 799 := by decide +kernel

theorem f8 : t3 0 = 8 ∧ S3 0 = 0 ∧ S3 1 = 8 := by decide

/-- The image's table of counts in the bytes `V`. -/
def T3 (V : Addr → Byte) : Prop := ∀ d < 31, V (Addr.add 7236000#64 d) = BitVec.ofNat 8 (t3 d)

/-! ## The invariant -/

/-- The bytes outside the tables as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7985984 (7985984 + 4220) V V'

/-- The bytes outside the tables as at the entry, and the image's table there. -/
def Cv (V₀ V : Addr → Byte) : Prop := Out V₀ V ∧ T3 V₀

/-- The registers of the first loops: the table, the image's table. -/
def R1 (g : Gprs) : Prop := g.r8 = 7986208#64 ∧ g.r9 = 7236000#64

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 2160 ∧ n = 100000 ∧ g = g₀ ∧ V = V₀ ∧ T3 V₀) ∨
  (ℓ = 2208 ∧ ∃ d < 31, ∃ i, S3 d ≤ i ∧ i < S3 (d + 1) ∧ n = 3010 + 1000 * (31 - d) + (S3 (d + 1) - i) ∧
    g.rdx.toNat = d ∧ g.rsi.toNat = i ∧ g.rdi.toNat = S3 (d + 1) ∧ R1 g ∧ Kp g₀ g ∧ Cv V₀ V) ∨
  (ℓ = 2233 ∧ ∃ d < 31, n = 3500 + 1000 * (31 - d) ∧ g.rdx.toNat = d ∧ g.rcx.toNat = S3 d ∧ R1 g ∧ Kp g₀ g ∧
    Cv V₀ V) ∨
  (ℓ = 2250 ∧ ∃ d < 31, n = 3005 + 1000 * (31 - d) ∧ g.rdx.toNat = d ∧ g.rcx.toNat = S3 (d + 1) ∧ R1 g ∧
    Kp g₀ g ∧ Cv V₀ V) ∨
  (ℓ = 2272 ∧ n = 2000 ∧ g.r8 = 7986208#64 ∧ Kp g₀ g ∧ Cv V₀ V) ∨
  (ℓ = 2296 ∧ ∃ k < 799, n = 1000 + (799 - k) ∧ g.rax.toNat = k ∧ g.rdi = 7987008#64 ∧ g.r8 = 7986208#64 ∧
    Kp g₀ g ∧ Cv V₀ V) ∨
  (ℓ = 2364 ∧ ∃ k < 54, n = 100 + (54 - k) ∧ g.rax.toNat = k ∧ g.rsi = 7235936#64 ∧ g.r8 = 7985984#64 ∧
    Kp g₀ g ∧ Cv V₀ V)

/-- `edi` at the entry: `8 + 0`. -/
theorem e8 (x : BitVec 64) : (BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.setWidth 64 8#32 + BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x)))).toNat = 8 := by
  rw [BitVec.xor_self]; decide

/-- A count of the image's table, in the bytes at a cut point. -/
theorem tb3 {V₀ V : Addr → Byte} (hV : Cv V₀ V) {d : Nat} (h : d < 31) :
    V (Addr.add 7236000#64 d) = BitVec.ofNat 8 (t3 d) := by
  have e : (Addr.add 7236000#64 d).toNat = 7236000 + d := ta (by omega)
  exact (hV.1 _ (by omega)).trans (hV.2 d h)

/-! ## The code from each cut point -/

/-- The entry: the first run's count 8, on to the first loop's store with `d = 0`. -/
theorem vc_2160 {g₀ : Gprs} {f : Rflags} {V₀ : Addr → Byte} (hT : T3 V₀) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 100000, Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V') : W_2160 F Wl Q g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  wpx [W_2160, W_2199, o0, o1]
  intro _ _ _
  refine ⟨fun h => absurd h (by decide), fun _ => hQ _ _ _ _ ⟨_, by decide, Or.inr (Or.inl
    ⟨rfl, 0, by decide, 0, by decide, by decide, rfl, xz rdx, xz rcx, (e8 rcx).trans f8.2.2.symm,
      ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, hT⟩)⟩⟩

/-- The first loops' store: the byte `d` at `S3 d + i`, then on, or past the run's last byte to the next count, or
after the last count to the second loop. -/
theorem vc_2208 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d i : Nat}
    (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i)) (hd : d < 31) (hi1 : S3 d ≤ i) (hi2 : i < S3 (d + 1))
    (hdx : g.rdx.toNat = d) (hsi : g.rsi.toNat = i) (hdi : g.rdi.toNat = S3 (d + 1)) (hR : R1 g) (hK : Kp g₀ g)
    (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 3010 + 1000 * (31 - d) + (S3 (d + 1) - i), Inv g₀ V₀ j' n' g' f' V') →
      Q j' g' f' V') :
    W_2208 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, h9⟩ := hR
  dsimp only at hdx hsi hdi h8 h9
  subst h8
  obtain ⟨-, hc⟩ := fc d hd
  have hz := zw hsi (by omega)
  have ea : (7986208#64 + BitVec.setWidth 64 (BitVec.setWidth 32 rsi)).toNat = 7986208 + i := by
    rw [toNat_bx (b := 7986208) (x := BitVec.setWidth 64 (BitVec.setWidth 32 rsi)) (by omega), hz]
  have hV' : Cv V₀ (Vst V (7986208#64 + BitVec.setWidth 64 (BitVec.setWidth 32 rsi))
      (toBytesLE (BitVec.setWidth 8 r10) 1)) :=
    ⟨out_at hV.1 (toBytesLE_length _ _) (by omega) (by omega) (by omega), hV.2⟩
  wpx [W_2208, W_2221, o2, o3]
  refine ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun h => ⟨fun h' => ?_, fun h' => ?_⟩⟩
  · have hne := inc32r_ne hsi hdi (by omega) (by omega) h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inl ⟨rfl, d, hd, i + 1, by omega, by omega, rfl, hdx,
      inc32w hsi (by omega), hdi, ⟨rfl, h9⟩, hK, hV'⟩)⟩
  · have e := eqk_t hdx (by omega) (by omega) h'
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hK, hV'⟩))))⟩
  · have e := eqk_f hdx (by omega) (by omega) h'
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, d + 1, by omega, rfl, inc64 hdx (by omega),
      zw hdi (by omega), ⟨rfl, h9⟩, hK, hV'⟩))⟩

/-- The first loops' head: the count `t3 d` from the image's table; not 0, on to the store, else past it. -/
theorem vc_2233 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat}
    (hF3 : ∀ i < 31, Foot F.data (Addr.add 7236000#64 i)) (hd : d < 31) (hdx : g.rdx.toNat = d)
    (hcx : g.rcx.toNat = S3 d) (hR : R1 g) (hK : Kp g₀ g) (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 3500 + 1000 * (31 - d), Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_2233 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, h9⟩ := hR
  dsimp only at hdx hcx h8 h9
  subst h9
  obtain ⟨h3, hc⟩ := fc d hd
  have eS : S3 (d + 1) = S3 d + t3 d := rfl
  wpx [W_2233, o4]
  rw [ld0 hdx (by omega) (tb3 hV hd)]
  refine ⟨ft_bx hF3 (by omega) (by omega), fun _ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := nz8_t h3 h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inl ⟨rfl, d, hd, S3 d, Nat.le_refl _, by omega, rfl, hdx,
      zw hcx (by omega), (addv hcx h3 (by omega)).trans eS.symm, ⟨h8, rfl⟩, hK, hV⟩)⟩
  · have h0 := nz8_f h3 h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, d, hd, rfl, hdx, hcx.trans (by omega),
      ⟨h8, rfl⟩, hK, hV⟩)))⟩

/-- The first loops' step past a count 0: on to the next count, or after the last to the second loop. -/
theorem vc_2250 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat} (hd : d < 31) (hdx : g.rdx.toNat = d)
    (hcx : g.rcx.toNat = S3 (d + 1)) (hR : R1 g) (hK : Kp g₀ g) (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 3005 + 1000 * (31 - d), Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_2250 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, h9⟩ := hR
  dsimp only at hdx hcx h8 h9
  obtain ⟨-, hc⟩ := fc d hd
  wpx [W_2250, W_2264, o5, o6]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := eqk_ne hdx (by omega) (by omega) (bnot_t h)
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, d + 1, by omega, rfl, inc64 hdx (by omega),
      zw hcx (by omega), ⟨h8, h9⟩, hK, hV⟩))⟩
  · exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h8, hK, hV⟩))))⟩

/-- The start of the second loop. -/
theorem vc_2272 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (h8 : g.r8 = 7986208#64) (hK : Kp g₀ g)
    (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 2000, Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V') : W_2272 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2272, o7]
  intro _
  exact hQ _ _ _ _ ⟨_, by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, 0, by decide, rfl, xz rax,
    rfl, h8, hK, hV⟩)))))⟩

/-- The second loop: the word at index `k`, then on, or after the last to the third loop. -/
theorem vc_2296 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {k : Nat}
    (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i)) (hwD : ∀ i < 4220, Foot F.data (Addr.add 7985984#64 i))
    (hk : k < 799) (hax : g.rax.toNat = k) (hdi : g.rdi = 7987008#64) (h8 : g.r8 = 7986208#64) (hK : Kp g₀ g)
    (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 1000 + (799 - k), Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_2296 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hdi h8
  subst hdi h8
  have e1 : (7986208#64 + rax).toNat = 7986208 + k := by
    rw [toNat_bx (b := 7986208) (x := rax) (by omega), hax]
  have e4 : (7987008#64 + rax * 4#64).toNat = 7987008 + 4 * k := ea4 hax (by omega)
  have hV' : Cv V₀ (Vst V (7987008#64 + rax * 4#64) (toBytesLE (BitVec.setWidth 32 rdx) 4)) :=
    ⟨out_at hV.1 (toBytesLE_length _ _) (by omega) (by omega) (by omega), hV.2⟩
  wpx [W_2296, W_2325, o8, o9]
  refine ⟨ft_at hwD (by omega) (by omega) (by omega), ft_at hw (by omega) (by omega) (by omega),
    fun _ => ⟨fun h => ?_, fun h _ _ => ?_⟩⟩
  · have e := eqk_ne hax (by omega) (by omega) (bnot_t h)
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k + 1, by omega, rfl,
      inc64 hax (by omega), rfl, rfl, hK, hV'⟩)))))⟩
  · exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, 0, by decide, rfl, xz _,
      rfl, rfl, hK, hV'⟩)))))⟩

/-- The third loop: the word at index `k`, then the next shift from the image's table, or after the last the
`ret`. -/
theorem vc_2364 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {k : Nat}
    (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i)) (hF4 : ∀ i < 54, Foot F.data (Addr.add 7235936#64 i))
    (hk : k < 54) (hax : g.rax.toNat = k) (hsi : g.rsi = 7235936#64) (h8 : g.r8 = 7985984#64) (hK : Kp g₀ g)
    (hV : Cv V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 100 + (54 - k), Inv g₀ V₀ j' n' g' f' V') → Q j' g' f' V')
    (hQr : ∀ g' f' V', Kp g₀ g' → Out V₀ V' → Q 2387 g' f' V') : W_2364 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsi h8
  subst hsi h8
  have hV' : Cv V₀ (Vst V (7985984#64 + rax * 4#64) (toBytesLE (BitVec.setWidth 32 rdx) 4)) :=
    ⟨out_b4 (x := rax) hV.1 (by omega) (by omega) (toBytesLE_length _ _), hV.2⟩
  wpx [W_2364, W_2360, o10, o11]
  refine ⟨ft_b4 hw (by omega) (by omega), fun _ => ⟨fun h => ?_, fun _ => hQr _ _ _ hK hV'.1⟩⟩
  have e := eqk_ne hax (by omega) (by omega) (bnot_t h)
  have hx := inc64 hax (by omega)
  exact ⟨ft_bx hF4 (by omega) (by omega), hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨rfl, k + 1, by omega, rfl, hx, rfl, rfl, hK, hV'⟩)))))⟩⟩

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the tables as at the entry. -/
theorem vc (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i)) (hwD : ∀ i < 4220, Foot F.data (Addr.add 7985984#64 i))
    (hF3 : ∀ i < 31, Foot F.data (Addr.add 7236000#64 i)) (hF4 : ∀ i < 54, Foot F.data (Addr.add 7235936#64 i))
    (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 2387 ∧ Kp g₀ g' ∧ Out V₀ V')) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl, hT⟩ | ⟨rfl, d, hd, i, hi1, hi2, rfl, hdx, hsi, hdi, hR, hK, hV⟩ |
    ⟨rfl, d, hd, rfl, hdx, hcx, hR, hK, hV⟩ | ⟨rfl, d, hd, rfl, hdx, hcx, hR, hK, hV⟩ | ⟨rfl, rfl, h8, hK, hV⟩ |
    ⟨rfl, k, hk, rfl, hax, hdi, h8, hK, hV⟩ | ⟨rfl, k, hk, rfl, hax, hsi, h8, hK, hV⟩ <;>
    simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
  · exact vc_2160 hT _ fun _ _ _ _ h => Or.inl h
  · exact vc_2208 hw hd hi1 hi2 hdx hsi hdi hR hK hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2233 hF3 hd hdx hcx hR hK hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2250 hd hdx hcx hR hK hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2272 h8 hK hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2296 hw hwD hk hax hdi h8 hK hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2364 hw hF4 hk hax hsi h8 hK hV _ (fun _ _ _ _ h => Or.inl h) fun _ _ _ hK' hO => Or.inr ⟨rfl, hK', hO⟩

/-! ## The constructor -/

/-- The tables. -/
def wr87 : List (Nat × Nat) := [(7985984, 7990204)]

/-- `Out` says the bytes outside `wr87` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr87 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr87, InR, or_false]; omega)

/-- The image's table of counts in `W` when `W` holds the bytes of `V` below it. -/
theorem t3W {V W : Addr → Byte} (hT : T3 V) (h : ∀ a : Addr, a.toNat < 7236031 → W a = V a) : T3 W := fun d hd => by
  have e : (Addr.add 7236000#64 d).toNat = 7236000 + d := ta (by omega)
  exact (h _ (by omega)).trans (hT d hd)

/-- The `ret` at offset 2387 of `sti`. -/
def r2387 : List Byte := [0xc3]
theorem r2387_0 : ∀ feat, Dec feat r2387 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v2387 : r2387 <+: sti.drop 2387 := by decide +kernel
theorem tg87 : csuTg 87 = sti_at.add 2160 := by decide +kernel
theorem calls87 : calls 87 = [] := by decide +kernel
theorem wrT87 : ∀ x ∈ wr87, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- `csuTg 87` is a function as `Csu.csu_ok` asks, for an invariant whose bytes hold the image's table of counts and
that goes from `87` to `88` through `Out`. -/
theorem runs87 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hS : 7991300 + 1024 ≤ sp.toNat) (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i))
    (hF3 : ∀ i < 31, Foot F.data (Addr.add 7236000#64 i)) (hF4 : ∀ i < 54, Foot F.data (Addr.add 7235936#64 i))
    (hT : ∀ V, J 87 V → T3 V) (hJ : ∀ V V', J 87 V → Out V V' → J 88 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 87 (csuTg 87) :=
  cfg_runsJ c hC hin tg87 (spAll prof) (Dec.shift (j := 2387) (k := 0) (r2387_0 _) v2387 (by decide))
    (lt_len (by decide)) Out Inv (fun _ _ _ _ hJ0 => ⟨100000, Or.inl ⟨rfl, rfl, rfl, rfl, hT _ hJ0⟩⟩)
    (vc hw (fun i hi => c.hws _ (hw i hi)) hF3 hF4) (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 87` for `Jg`, its spec `wrSpec wr87`: the image's table of counts from `V`, which no store before
reaches. -/
theorem runs87_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hS : 7991300 + 1024 ≤ sp.toNat) (hw : ∀ i < 4220, Foot Wl (Addr.add 7985984#64 i))
    (hF3 : ∀ i < 31, Foot F.data (Addr.add 7236000#64 i)) (hF4 : ∀ i < 54, Foot F.data (Addr.add 7235936#64 i))
    (hTV : T3 V) (hspec : spec 87 = wrSpec wr87) (hD : ∀ k, (spec k).Dep)
    (hlo : ∀ k, ∀ x ∈ (spec k).wr, 7236031 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < 87 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr87, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 87 W → Out W W' → G 88 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 87 (csuTg 87) :=
  runs87 c hC hin hS hw hF3 hF4
    (fun W hJ => t3W hTV fun a ha => hJ.1.2.1 a (by omega) (by unfold Pre; omega) (by omega)
      fun k _ _ => InR_ge (hlo k) ha)
    fun W W' hJ hO => jg_wr (by decide) calls87 hspec hD wrT87 hXw (out_wr hO) (hG W W' · hO) hJ

end FV7z.C87
