import FV7z.C82.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
import FV7z.Ctor.CfgJ
import FV7z.Ctor.Prep
import FV7z.Ctor.Tab
/-!
# `csuTg 82`: two tables of indices from the image's counts (PLAN.md §M, constructors)

`csuTg 82`, at offset 1888 of `sti`, pushes `rbx` and fills two tables from tables of the image:

- for each `d < 29`, the `2 ^ t1s d` bytes from `0x79da40 + t1b d` with `d` (`t1b` at `0x6e6600`, `t1s` at
  `0x6e65c0`), 256 bytes in all;
- for each `d < 18`, the `2 ^ t2 d` bytes from `0x79d840 + S2 d` with `d` (`t2` at `0x6e6500`), 512 bytes in all;

then pops `rbx` and returns. Its stores lie in `wr82` and the slot of the push; no later code takes the tables' bytes
as an address, so its spec says only where they lie (`wrSpec wr82`).

- `Tb`: the image's three tables; `fa`, `fb`: what the code needs of them, by the kernel.
- `Inv`: the invariant at the 7 cut points (`Cuts.lean`): the entry; for the first loops the head (`1936`), the store
  (`1968`) and the step (`1979`); for the second the same (`2032`, `2048`, `2062`). The registers a call keeps are
  as at the entry but `rbx`, which the slot of the push holds (`Cv`), and `rsp`, 8 below.
- `vc_*`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the `ret`.
- `runs82`: `csuTg 82` is a function as `Csu.csu_ok` asks (`cfg_runsJ`: the entry needs `rsp` and the tables);
  `runs82_jg`: for `Jg` (`jg_wrk`: the push stores to the stack).
-/
namespace FV7z.C82
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The image's tables -/

/-- The first byte of each run of the first table (`0x6e6600`). -/
def t1b (d : Nat) : Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224,
    255].getD d 0

/-- The log of each run's length in the first table (`0x6e65c0`). -/
def t1s (d : Nat) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0].getD d 0

/-- The log of each run's length in the second table (`0x6e6500`). -/
def t2 (d : Nat) : Nat := [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7].getD d 0

def t1n (d : Nat) : Nat := 2 ^ t1s d
def t2n (d : Nat) : Nat := 2 ^ t2 d

/-- Where the run `d` of the second table starts. -/
def S2 : Nat → Nat
  | 0 => 0
  | d + 1 => S2 d + t2n d

theorem fa : ∀ d < 29, 1#32 <<< (t1s d % 32) = BitVec.ofNat 32 (t1n d) ∧ 1 ≤ t1n d ∧ t1n d ≤ 32 ∧
    t1b d + t1n d ≤ 256 ∧ t1s d < 256 ∧ t1b d < 256 := by decide +kernel

theorem fb : ∀ d < 18, 1#32 <<< (t2 d % 32) = BitVec.ofNat 32 (t2n d) ∧ 1 ≤ t2n d ∧ t2n d ≤ 128 ∧
    S2 d + t2n d ≤ 512 ∧ t2 d < 256 := by decide +kernel

theorem f0 : t1b 0 = 0 ∧ t1s 0 = 0 ∧ t2 0 = 0 ∧ S2 0 = 0 := by decide

/-- The image's three tables in the bytes `V`. -/
def Tb (V : Addr → Byte) : Prop :=
  (∀ i < 29, V (Addr.add 7235072#64 i) = BitVec.ofNat 8 (t1b i) ∧ V (Addr.add 7235008#64 i) = BitVec.ofNat 8 (t1s i))
    ∧ ∀ i < 18, V (Addr.add 7234816#64 i) = BitVec.ofNat 8 (t2 i)

/-! ## The invariant -/

/-- The bytes outside the two tables and the slot of the push as before. -/
def Out (sp : Addr) (V V' : Addr → Byte) : Prop :=
  ∀ a : Addr, ¬ (7985216 ≤ a.toNat ∧ a.toNat < 7985216 + 768) → ¬ (sp.toNat - 72 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
    V' a = V a

/-- The registers the first loops read: the image's tables, the table's end and start, and the shift's 1. -/
def AR (g : Gprs) : Prop :=
  g.r8 = 7235072#64 ∧ g.rdi = 7235008#64 ∧ g.r9 = 7985728#64 + 1#64 ∧ g.r10 = 7985728#64 ∧ g.r11.setWidth 32 = 1#32

/-- The registers the second loops read: the shift's 1, the table, the image's table. -/
def BR (g : Gprs) : Prop := g.r8.setWidth 32 = 1#32 ∧ g.rdi = 7985216#64 ∧ g.rsi = 7234816#64

/-- The registers a call keeps, but `rbx`, as at the entry, `rsp` 8 below. -/
def Cr (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 8 ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The bytes after the push. -/
abbrev V1 (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte := Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.rbx 8)

/-- The bytes: those after the push outside the tables, from the frame's `rsp` and the image's tables. -/
def Cv (sp : Addr) (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  g₀.rsp = sp - 64#64 ∧ Raf.Out 7985216 (7985216 + 768) (V1 g₀ V₀) V ∧ Tb V₀

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (sp : Addr) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 1888 ∧ n = 10000 ∧ g = g₀ ∧ V = V₀ ∧ g₀.rsp = sp - 64#64 ∧ Tb V₀) ∨
  (ℓ = 1936 ∧ ∃ d < 29, n = 4050 + 100 * (29 - d) ∧ g.rdx.toNat = d ∧ g.rax.toNat = t1b d ∧
    (g.rcx.setWidth 8).toNat = t1s d ∧ AR g ∧ Cr g₀ g ∧ Cv sp g₀ V₀ V) ∨
  (ℓ = 1968 ∧ ∃ d < 29, ∃ i < t1n d, n = 4005 + 100 * (29 - d) + (t1n d - i) ∧ g.rdx.toNat = d ∧
    g.rcx.toNat = 7985728 + t1b d + i ∧ g.rax.toNat = 7985728 + t1b d + t1n d ∧ AR g ∧ Cr g₀ g ∧ Cv sp g₀ V₀ V) ∨
  (ℓ = 1979 ∧ ∃ d < 29, n = 4002 + 100 * (29 - d) ∧ g.rdx.toNat = d ∧ AR g ∧ Cr g₀ g ∧ Cv sp g₀ V₀ V) ∨
  (ℓ = 2032 ∧ ∃ d < 18, n = 200 * (18 - d) + 150 ∧ g.rdx.toNat = d ∧ g.rax.toNat = S2 d ∧
    (g.rcx.setWidth 8).toNat = t2 d ∧ BR g ∧ Cr g₀ g ∧ Cv sp g₀ V₀ V) ∨
  (ℓ = 2048 ∧ ∃ d < 18, ∃ i < t2n d, n = 200 * (18 - d) + 10 + (t2n d - i) ∧ g.rdx.toNat = d ∧
    g.rax.toNat = S2 d + i ∧ g.rcx.toNat = S2 d + t2n d ∧ BR g ∧ Cr g₀ g ∧ Cv sp g₀ V₀ V) ∨
  (ℓ = 2062 ∧ ∃ d < 18, n = 200 * (18 - d) + 5 ∧ g.rdx.toNat = d ∧ g.rax.toNat = S2 (d + 1) ∧ BR g ∧ Cr g₀ g ∧
    Cv sp g₀ V₀ V)

theorem s72 {sp : Addr} (h : 72 ≤ sp.toNat) : (sp - 64#64 - 8).toNat = sp.toNat - 72 := by bv_omega

/-! ## The bytes -/

theorem slot {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat)
    (hV : Cv sp g₀ V₀ V) : (g₀.rsp - 8).toNat = sp.toNat - 72 := by
  rw [hV.1]; exact s72 (by omega)

/-- A byte below the tables and the slot, as at the entry. -/
theorem tbv {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} {a : Addr} (hS : 7991300 + 1024 ≤ sp.toNat)
    (hV : Cv sp g₀ V₀ V) (ha : a.toNat < 7985216) : V a = V₀ a := by
  have e := slot hS hV
  have := sp.isLt
  have hl := toBytesLE_length g₀.rbx 8
  exact (hV.2.1 a (by omega)).trans (Tun.Vst_out V₀ _ _ a (by rw [hl]; omega) (Or.inl (by omega)))

theorem tb1 {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat) (hV : Cv sp g₀ V₀ V)
    {d : Nat} (h : d < 29) :
    V (Addr.add 7235072#64 d) = BitVec.ofNat 8 (t1b d) ∧ V (Addr.add 7235008#64 d) = BitVec.ofNat 8 (t1s d) := by
  have e1 : (Addr.add 7235072#64 d).toNat = 7235072 + d := ta (by omega)
  have e2 : (Addr.add 7235008#64 d).toNat = 7235008 + d := ta (by omega)
  exact ⟨(tbv hS hV (by omega)).trans (hV.2.2.1 d h).1, (tbv hS hV (by omega)).trans (hV.2.2.1 d h).2⟩

theorem tb2 {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat) (hV : Cv sp g₀ V₀ V)
    {d : Nat} (h : d < 18) : V (Addr.add 7234816#64 d) = BitVec.ofNat 8 (t2 d) := by
  have e : (Addr.add 7234816#64 d).toNat = 7234816 + d := ta (by omega)
  exact (tbv hS hV (by omega)).trans (hV.2.2.2 d h)

/-- `pop rbx` reads what the push stored. -/
theorem pop {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat) (hV : Cv sp g₀ V₀ V) :
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8) 8)) = g₀.rbx := by
  have e := slot hS hV
  have := sp.isLt
  rw [Raf.Out.rd (x := g₀.rsp - 8) (n := 8) hV.2.1 (by omega) (Or.inr (by omega)),
    Tun.rd_Vst_self V₀ (g₀.rsp - 8) (toBytesLE g₀.rbx 8) (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- At the `ret`, the bytes outside the tables and the slot as at the entry. -/
theorem out_of {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat)
    (hV : Cv sp g₀ V₀ V) : Out sp V₀ V := fun a h1 h2 => by
  have e := slot hS hV
  have := sp.isLt
  have hl := toBytesLE_length g₀.rbx 8
  exact (hV.2.1 a h1).trans (Tun.Vst_out V₀ _ _ a (by rw [hl]; omega) (by rw [hl]; omega))

/-- A store of a byte inside the tables keeps `Cv`. -/
theorem cv_st {sp : Addr} {g₀ : Gprs} {V₀ V : Addr → Byte} {a : Addr} {bs : List Byte} (hV : Cv sp g₀ V₀ V)
    (hn : bs.length = 1) (h1 : 7985216 ≤ a.toNat) (h2 : a.toNat + 1 ≤ 7985216 + 768) : Cv sp g₀ V₀ (Vst V a bs) :=
  ⟨hV.1, out_at hV.2.1 hn h1 h2 (by omega), hV.2.2⟩

/-! ## The code from each cut point -/

/-- The entry: the push, the registers of the first loops, on to its head with `d = 0`. -/
theorem vc_1888 {sp : Addr} {g₀ : Gprs} {f : Rflags} {V₀ : Addr → Byte}
    (hstk : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8) i)) (hs : g₀.rsp = sp - 64#64) (hT : Tb V₀) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 10000, Inv sp g₀ V₀ j' n' g' f' V') → Q j' g' f' V') : W_1888 F Wl Q g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hs
  wpx [W_1888, o0]
  refine ⟨fun i hi => by rw [hs]; exact hstk i hi, fun _ _ _ => hQ _ _ _ _ ⟨_, by decide, Or.inr (Or.inl
    ⟨rfl, 0, by decide, rfl, xz rdx, (xz rax).trans f0.1.symm, (xz8 rcx).trans f0.2.1.symm,
      ⟨rfl, rfl, rfl, rfl, w1⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨hs, fun _ _ => rfl, hT⟩⟩)⟩⟩

/-- The head of the first loops: the run's length `2 ^ t1s d` (never 0), its end and start, on to the store. -/
theorem vc_1936 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat} (hd : d < 29)
    (hdx : g.rdx.toNat = d) (hax : g.rax.toNat = t1b d) (hcl : (g.rcx.setWidth 8).toNat = t1s d) (hA : AR g)
    (hC : Cr g₀ g) (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 4050 + 100 * (29 - d), Inv sp g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_1936 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, hdi, h9, h10, h11⟩ := hA
  dsimp only at hdx hax hcl h8 hdi h9 h10 h11
  obtain ⟨e, h1, h2, h3, -, -⟩ := fa d hd
  wpx [W_1936, W_1945, o1, o2]
  intro fl af
  rw [shl1 h11 hcl e]
  refine ⟨fun h => (nz h1 (by omega) h).elim, fun _ => hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inl
    ⟨rfl, d, hd, 0, by omega, rfl, hdx, (addB hax h10 (by omega)).trans (Nat.add_zero _).symm,
      endA hax h9 h1 (by omega) (by omega), ⟨h8, hdi, h9, h10, h11⟩, hC, hV⟩))⟩⟩

/-- The store of the first loops: the byte `d` at `rcx`, then on, or to the step after the run's last byte. -/
theorem vc_1968 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d i : Nat}
    (hw : ∀ i < 768, Foot Wl (Addr.add 7985216#64 i)) (hd : d < 29) (hi : i < t1n d) (hdx : g.rdx.toNat = d)
    (hcx : g.rcx.toNat = 7985728 + t1b d + i) (hax : g.rax.toNat = 7985728 + t1b d + t1n d) (hA : AR g)
    (hC : Cr g₀ g) (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 4005 + 100 * (29 - d) + (t1n d - i), Inv sp g₀ V₀ j' n' g' f' V') →
      Q j' g' f' V') :
    W_1968 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdx hcx hax
  obtain ⟨-, h1, h2, h3, -, -⟩ := fa d hd
  have hV' := cv_st (a := rcx) hV (toBytesLE_length (BitVec.setWidth 8 rbx) 1) (by omega) (by omega)
  wpx [W_1968, o3]
  refine ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun h => ?_⟩
  · have hne := inc64_ne hcx hax (by omega) h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, d, hd, i + 1, by omega, rfl, hdx,
      (inc64 hcx (by omega)).trans (by omega), hax, hA, hC, hV'⟩))⟩
  · exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, d, hd, rfl, hdx, hA, hC, hV'⟩)))⟩

/-- The step of the first loops: the next run's start and length from the image's tables, or after the last the
registers of the second loops. -/
theorem vc_1979 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat}
    (hS : 7991300 + 1024 ≤ sp.toNat) (hF1 : ∀ i < 29, Foot F.data (Addr.add 7235072#64 i))
    (hF2 : ∀ i < 29, Foot F.data (Addr.add 7235008#64 i)) (hd : d < 29) (hdx : g.rdx.toNat = d) (hA : AR g)
    (hC : Cr g₀ g) (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 4002 + 100 * (29 - d), Inv sp g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_1979 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, hdi, h9, h10, h11⟩ := hA
  dsimp only at hdx h8 hdi h9 h10 h11
  subst h8 hdi h9 h10
  wpx [W_1979, W_1989, W_2000, o4, o5, o6]
  refine ⟨fun h _ _ _ => ?_, fun h => ?_⟩
  · have e := eqk_t hdx (by omega) (by omega) h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, 0, by decide, rfl, xz _,
      (xz rax).trans f0.2.2.2.symm, (xz8 rcx).trans f0.2.2.1.symm, ⟨w1, rfl, rfl⟩, hC, hV⟩))))⟩
  · have e := eqk_f hdx (by omega) (by omega) h
    have hx := inc64 hdx (by omega)
    obtain ⟨-, -, -, -, h4, h5⟩ := fa (d + 1) (by omega)
    obtain ⟨v1, v2⟩ := tb1 hS hV (d := d + 1) (by omega)
    refine ⟨ft_bx hF1 (by omega) (by rw [hx]; omega), ft_bx hF2 (by omega) (by rw [hx]; omega),
      hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inl ⟨rfl, d + 1, by omega, rfl, hx, ldx hdx (by omega) v1 h5,
        ldx8 hdx (by omega) v2 h4, ⟨rfl, rfl, rfl, rfl, h11⟩, hC, hV⟩)⟩⟩

/-- The head of the second loops: the run's length `2 ^ t2 d` (never 0) and end, on to the store. -/
theorem vc_2032 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat} (hd : d < 18)
    (hdx : g.rdx.toNat = d) (hax : g.rax.toNat = S2 d) (hcl : (g.rcx.setWidth 8).toNat = t2 d) (hB : BR g)
    (hC : Cr g₀ g) (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 200 * (18 - d) + 150, Inv sp g₀ V₀ j' n' g' f' V') → Q j' g' f' V') :
    W_2032 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, hdi, hsi⟩ := hB
  dsimp only at hdx hax hcl h8 hdi hsi
  obtain ⟨e, h1, h2, h3, -⟩ := fb d hd
  wpx [W_2032, W_2046, o7, o8]
  intro fl af
  rw [shl1 h8 hcl e]
  refine ⟨fun h => (nz h1 (by omega) h).elim, fun _ => hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨rfl, d, hd, 0, by omega, rfl, hdx, hax.trans (Nat.add_zero _).symm,
      addw hax (by omega), ⟨h8, hdi, hsi⟩, hC, hV⟩)))))⟩⟩

/-- The store of the second loops: the byte `d` at `S2 d + i`, then on, or to the step after the run's last. -/
theorem vc_2048 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d i : Nat}
    (hw : ∀ i < 768, Foot Wl (Addr.add 7985216#64 i)) (hd : d < 18) (hi : i < t2n d) (hdx : g.rdx.toNat = d)
    (hax : g.rax.toNat = S2 d + i) (hcx : g.rcx.toNat = S2 d + t2n d) (hB : BR g) (hC : Cr g₀ g)
    (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 200 * (18 - d) + 10 + (t2n d - i), Inv sp g₀ V₀ j' n' g' f' V') →
      Q j' g' f' V') :
    W_2048 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, hdi, hsi⟩ := hB
  dsimp only at hdx hax hcx h8 hdi hsi
  subst hdi
  obtain ⟨-, h1, h2, h3, -⟩ := fb d hd
  have hz := zw hax (by omega)
  have eS : S2 (d + 1) = S2 d + t2n d := rfl
  have ea : (7985216#64 + BitVec.setWidth 64 (BitVec.setWidth 32 rax)).toNat = 7985216 + (S2 d + i) := by
    rw [toNat_bx (b := 7985216) (x := BitVec.setWidth 64 (BitVec.setWidth 32 rax)) (by omega), hz]
  have hV' := cv_st (a := 7985216#64 + BitVec.setWidth 64 (BitVec.setWidth 32 rax)) hV
    (toBytesLE_length (BitVec.setWidth 8 r9) 1) (by omega) (by omega)
  wpx [W_2048, o9]
  refine ⟨ft_bx hw (by omega) (by rw [hz]; omega), fun h => ?_, fun h => ?_⟩
  · have hne := inc32_ne hax hcx (by omega) (by omega) h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, d, hd, i + 1,
      by omega, rfl, hdx, (inc32w hax (by omega)).trans (by omega), hcx, ⟨h8, rfl, hsi⟩, hC, hV'⟩)))))⟩
  · have heq := inc32_eq hax hcx (by omega) (by omega) h
    exact hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, d, hd, rfl, hdx,
      (inc32w hax (by omega)).trans (by omega), ⟨h8, rfl, hsi⟩, hC, hV'⟩)))))⟩

/-- The step of the second loops: the next run's length from the image's table, or after the last the pop and the
`ret`. -/
theorem vc_2062 {sp : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} {d : Nat}
    (hS : 7991300 + 1024 ≤ sp.toNat) (hstk : ∀ i < 8, Foot F.data (Addr.add (sp - 64#64 - 8) i))
    (hF3 : ∀ i < 18, Foot F.data (Addr.add 7234816#64 i)) (hd : d < 18) (hdx : g.rdx.toNat = d)
    (hax : g.rax.toNat = S2 (d + 1)) (hB : BR g) (hC : Cr g₀ g) (hV : Cv sp g₀ V₀ V) (Q : Post)
    (hQ : ∀ j' g' f' V', (∃ n' < 200 * (18 - d) + 5, Inv sp g₀ V₀ j' n' g' f' V') → Q j' g' f' V')
    (hQr : ∀ g' f' V', Kp g₀ g' → Out sp V₀ V' → Q 2081 g' f' V') : W_2062 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h8, hdi, hsi⟩ := hB
  obtain ⟨hr, hbp, h12, h13, h14, h15⟩ := hC
  dsimp only at hdx hax h8 hdi hsi hr hbp h12 h13 h14 h15
  subst hsi hr
  wpx [W_2062, W_2072, W_2080, o10, o11, o12]
  refine ⟨fun h => ⟨fun i hi => by rw [hV.1]; exact hstk i hi, hQr _ _ _ ⟨BitVec.sub_add_cancel _ _, pop hS hV,
    hbp, h12, h13, h14, h15⟩ (out_of hS hV)⟩, fun h => ?_⟩
  have e := eqk_f hdx (by omega) (by omega) h
  have hx := inc64 hdx (by omega)
  obtain ⟨-, -, -, -, h4⟩ := fb (d + 1) (by omega)
  refine ⟨ft_bx hF3 (by omega) (by rw [hx]; omega), hQ _ _ _ _ ⟨_, by omega, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, d + 1, by omega, rfl, hx, hax, ldx8 hdx (by omega) (tb2 hS hV (d := d + 1) (by omega)) h4,
      ⟨h8, hdi, rfl⟩, ⟨rfl, hbp, h12, h13, h14, h15⟩, hV⟩))))⟩⟩

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the tables and the slot as at the entry. -/
theorem vc {sp : Addr} (hS : 7991300 + 1024 ≤ sp.toNat) (hw : ∀ i < 768, Foot Wl (Addr.add 7985216#64 i))
    (hstk : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8) i)) (hstkD : ∀ i < 8, Foot F.data (Addr.add (sp - 64#64 - 8) i))
    (hF1 : ∀ i < 29, Foot F.data (Addr.add 7235072#64 i)) (hF2 : ∀ i < 29, Foot F.data (Addr.add 7235008#64 i))
    (hF3 : ∀ i < 18, Foot F.data (Addr.add 7234816#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv sp g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv sp g₀ V₀ j' n' g' f' V') ∨ (j' = 2081 ∧ Kp g₀ g' ∧ Out sp V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl, hs, hT⟩ | ⟨rfl, d, hd, rfl, hdx, hax, hcl, hA, hC, hV⟩ |
    ⟨rfl, d, hd, i, hi, rfl, hdx, hcx, hax, hA, hC, hV⟩ | ⟨rfl, d, hd, rfl, hdx, hA, hC, hV⟩ |
    ⟨rfl, d, hd, rfl, hdx, hax, hcl, hB, hC, hV⟩ | ⟨rfl, d, hd, i, hi, rfl, hdx, hax, hcx, hB, hC, hV⟩ |
    ⟨rfl, d, hd, rfl, hdx, hax, hB, hC, hV⟩ <;> simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
  · exact vc_1888 hstk hs hT _ fun _ _ _ _ h => Or.inl h
  · exact vc_1936 hd hdx hax hcl hA hC hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_1968 hw hd hi hdx hcx hax hA hC hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_1979 hS hF1 hF2 hd hdx hA hC hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2032 hd hdx hax hcl hB hC hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2048 hw hd hi hdx hax hcx hB hC hV _ fun _ _ _ _ h => Or.inl h
  · exact vc_2062 hS hstkD hF3 hd hdx hax hB hC hV _ (fun _ _ _ _ h => Or.inl h)
      fun _ _ _ hK hO => Or.inr ⟨rfl, hK, hO⟩

/-! ## The constructor -/

/-- The tables. -/
def wr82 : List (Nat × Nat) := [(7985216, 7985984)]

/-- `Out` keeps the bytes outside `wr82` and the stack's window. -/
theorem out_wr {sp : Addr} {V V' : Addr → Byte} (hS : 7991300 + 1024 ≤ sp.toNat) (h : Out sp V V') :
    ∀ a : Addr, ¬ InR wr82 a.toNat → ¬ (sp.toNat - 1024 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) → V' a = V a :=
  fun a ha hk => h a (fun h' => ha (by simp only [wr82, InR, or_false]; omega)) (by omega)

/-- The image's tables in `W` when `W` holds the bytes of `V` below them. -/
theorem tbW {V W : Addr → Byte} (hT : Tb V) (h : ∀ a : Addr, a.toNat < 7235101 → W a = V a) : Tb W := by
  refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi => ?_⟩
  · have e : (Addr.add 7235072#64 i).toNat = 7235072 + i := ta (by omega)
    exact (h _ (by omega)).trans (hT.1 i hi).1
  · have e : (Addr.add 7235008#64 i).toNat = 7235008 + i := ta (by omega)
    exact (h _ (by omega)).trans (hT.1 i hi).2
  · have e : (Addr.add 7234816#64 i).toNat = 7234816 + i := ta (by omega)
    exact (h _ (by omega)).trans (hT.2 i hi)

/-- The `ret` at offset 2081 of `sti`. -/
def r2081 : List Byte := [0xc3]
theorem r2081_0 : ∀ feat, Dec feat r2081 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v2081 : r2081 <+: sti.drop 2081 := by decide +kernel
theorem tg82 : csuTg 82 = sti_at.add 1888 := by decide +kernel
theorem calls82 : calls 82 = [] := by decide +kernel
theorem wrT82 : ∀ x ∈ wr82, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- `csuTg 82` is a function as `Csu.csu_ok` asks, for an invariant whose bytes hold the image's tables and that goes
from `82` to `83` through `Out`. -/
theorem runs82 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hS : 7991300 + 1024 ≤ sp.toNat) (hw : ∀ i < 768, Foot Wl (Addr.add 7985216#64 i))
    (hstk : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8) i))
    (hF1 : ∀ i < 29, Foot F.data (Addr.add 7235072#64 i)) (hF2 : ∀ i < 29, Foot F.data (Addr.add 7235008#64 i))
    (hF3 : ∀ i < 18, Foot F.data (Addr.add 7234816#64 i)) (hT : ∀ V, J 82 V → Tb V)
    (hJ : ∀ V V', J 82 V → Out sp V V' → J 83 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 82 (csuTg 82) :=
  cfg_runsJ c hC hin tg82 (spAll prof) (Dec.shift (j := 2081) (k := 0) (r2081_0 _) v2081 (by decide))
    (lt_len (by decide)) (Out sp) (Inv sp)
    (fun _ _ _ hsp hJ0 => ⟨10000, Or.inl ⟨rfl, rfl, rfl, rfl, hsp, hT _ hJ0⟩⟩)
    (vc hS hw hstk (fun i hi => c.hws _ (hstk i hi)) hF1 hF2 hF3)
    (fun _ _ h a ha => h a (by omega) (by omega)) hJ

/-- `csuTg 82` for `Jg`, its spec `wrSpec wr82`: the image's tables from `V`, which no store before reaches. -/
theorem runs82_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hS : 7991300 + 1024 ≤ sp.toNat) (hw : ∀ i < 768, Foot Wl (Addr.add 7985216#64 i))
    (hstk : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8) i))
    (hF1 : ∀ i < 29, Foot F.data (Addr.add 7235072#64 i)) (hF2 : ∀ i < 29, Foot F.data (Addr.add 7235008#64 i))
    (hF3 : ∀ i < 18, Foot F.data (Addr.add 7234816#64 i)) (hTV : Tb V)
    (hspec : spec 82 = wrSpec wr82) (hD : ∀ k, (spec k).Dep) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hlo : ∀ k, ∀ x ∈ (spec k).wr, 7235101 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < 82 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr82, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 82 W → Out sp W W' → G 83 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 82 (csuTg 82) :=
  runs82 c hC hin hS hw hstk hF1 hF2 hF3
    (fun W hJ => tbW hTV fun a ha => hJ.1.2.1 a (by omega) (by unfold Pre; omega) (by omega)
      fun k _ _ => InR_ge (hlo k) ha)
    fun W W' hJ hO => jg_wrk (by decide) calls82 hS hspec hD wrT82 hB hXw (out_wr hS hO) (hG W W' · hO) hJ

end FV7z.C82
