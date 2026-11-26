import FV7z.Lpd.Cuts
import FV7z.Close.Holds
import FV7z.Tun.Inv
/-!
# `LzmaProps_Decode` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaProps_Decode (CLzmaProps *p, const Byte *data, unsigned size)` at `0x42bea0` in `7zzs`
(`C/LzmaDec.c`; `objdump -d`): with `size` ≤ 4, `SZ_ERROR_UNSUPPORTED` (4, the code at 96); else `dicSize` (the
4 bytes at `p + 4`) from `data[1..5)`, then with `data[0]` ≥ 225 again 4; else `lc`, `lp`, `pb` (the bytes at `p`,
`p + 2`, `p + 1`) and 0 (the `ret` at 86). Cut points: the entry and 96 (`mov eax, 4`); the `ret`s at 86 and 101.

- `props`: the memory after the four stores; `Res`: at the return, `rax` and the memory, 4 with nothing or
  `dicSize` stored, or 0 with all four stores. The values are not followed: the spec is the control flow and the
  stores (`data[0..5)` read, `p[0..3)` and `p[4..8)` written).
- `o2a`–`o2d`: the 16 effects from 36 to 86 in pieces of 4 (`pa`–`pd`), each with the registers it writes
  existential, so no `simp` sees more than four of them (one `simp` over a long stretch of register effects grows
  like a tree).
- `lpd_ok`: from the entry to the return address with `Res`, `rcx` and `rdx` some values.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lpd

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_86 : pret <+: lpd.drop 86 := by decide +kernel
theorem ret_86 (feat : Features) : Dec feat lpd 86 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 86) (k := 0) (pret_0 feat) w_86 (Nat.zero_le _)
theorem w_101 : pret <+: lpd.drop 101 := by decide +kernel
theorem ret_101 (feat : Features) : Dec feat lpd 101 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 101) (k := 0) (pret_0 feat) w_101 (Nat.zero_le _)

/-- The memory after the four stores: `dicSize`, `lc`, `pb`, `lp`. -/
abbrev props (V : Addr → Byte) (p : Addr) (w : BitVec 32) (b0 b2 b1 : BitVec 8) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (p + 4#64) (toBytesLE w 4)) p (toBytesLE b0 1)) (p + 2#64) (toBytesLE b2 1))
    (p + 1#64) (toBytesLE b1 1)

/-- At the return: 4 with the memory as it was or `dicSize` stored, or 0 with the four stores. -/
def Res (V₀ : Addr → Byte) (p : Addr) (V : Addr → Byte) (r : BitVec 64) : Prop :=
  (r = 4#64 ∧ (V = V₀ ∨ ∃ w : BitVec 32, V = Vst V₀ (p + 4#64) (toBytesLE w 4))) ∨
    (r = 0#64 ∧ ∃ (w : BitVec 32) (b0 b2 b1 : BitVec 8), V = props V₀ p w b0 b2 b1)

/-- The effects from 36 to 86 in four pieces. -/
def o2a : List Op :=
  [Op.zxr 1 2, Op.lea 32 0 none (some 1) 8 0, Op.sub 32 0 (.r 1), Op.lea 32 0 (some 1) (some 0) 8 0]
def o2b : List Op :=
  [Op.shr16 0 9, Op.lea 32 1 (some 0) (some 0) 8 0, Op.sub 32 2 (.r 1), Op.st 8 (some 7) none 1 0 2]
def o2c : List Op := [Op.sxb16 2 0, Op.imul3d 2 2 103, Op.shr16 2 9, Op.st 8 (some 7) none 1 2 2]
def o2d : List Op :=
  [Op.lea 32 2 (some 2) (some 2) 4 0, Op.sub 32 0 (.r 2), Op.st 8 (some 7) none 1 1 0, Op.xor 32 0 (.r 0)]
theorem o2_eq : o2 = o2a ++ (o2b ++ (o2c ++ o2d)) := rfl

/-- `rdi + 4`, `rdi + 2`, `rdi + 1` as numbers, `rdi` 8 bytes from the top. -/
theorem tn_add (p : Addr) (k : Nat) (hk : k < 8) (hp : p.toNat + 8 ≤ 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The return address after a store at `p + k` inside `p[0..8)`, `p[0..8)` apart from it. -/
theorem rdK (V : Addr → Byte) (a p x : Addr) (k : Nat) (bs : List Byte) (ha : a.toNat = p.toNat + k)
    (hk : k + bs.length ≤ 8) (hp : p.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (hs : p.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ p.toNat) :
    List.map (Vst V a bs) (byteAddrs x 8) = List.map V (byteAddrs x 8) :=
  Tun.rd_Vst V a bs x 8 (by omega) hx (by omega)

/-- `xor eax, eax` gives 0. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

theorem pa (g : Gprs) (f : Rflags) (V : Addr → Byte) :
    wp F Wl o2a (fun g' _ V' => ∃ a c, g' = { g with rax := a, rcx := c } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o2a, Op.zxr]
  repeat' (first | apply And.intro | intro _)
  all_goals first | exact ⟨_, _, rfl, rfl⟩ | exact ⟨_, _, rfl⟩

theorem pb (g : Gprs) (f : Rflags) (V : Addr → Byte) (fw : ∀ i < 1, Foot Wl (Addr.add g.rdi i)) :
    wp F Wl o2b (fun g' _ V' => ∃ (a c d : BitVec 64) (b : BitVec 8), g' = { g with rax := a, rcx := c, rdx := d } ∧
      V' = Vst V g.rdi (toBytesLE b 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [o2b, Op.shr16]
  repeat' (first | exact fw | apply And.intro | intro _)
  all_goals first | exact ⟨_, _, _, _, rfl, rfl⟩ | rfl

theorem pc (g : Gprs) (f : Rflags) (V : Addr → Byte) (fw : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 2#64) i)) :
    wp F Wl o2c (fun g' _ V' => ∃ (d : BitVec 64) (b : BitVec 8), g' = { g with rdx := d } ∧
      V' = Vst V (g.rdi + 2#64) (toBytesLE b 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [o2c, Op.shr16, Op.sxb16, Op.imul3d]
  repeat' (first | exact fw | apply And.intro | intro _)
  all_goals first | exact ⟨_, _, rfl, rfl⟩ | rfl

theorem pd (g : Gprs) (f : Rflags) (V : Addr → Byte) (fw : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 1#64) i)) :
    wp F Wl o2d (fun g' _ V' => ∃ (d : BitVec 64) (b : BitVec 8), g' = { g with rax := 0#64, rdx := d } ∧
      V' = Vst V (g.rdi + 1#64) (toBytesLE b 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [o2d, xz, BitVec.xor_self]
  repeat' (first | exact fw | apply And.intro | intro _)
  all_goals first | exact ⟨_, _, rfl, rfl⟩ | rfl

/-- From 36 to 86: the three byte stores and `eax` 0. -/
theorem vc_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw0 : ∀ i < 1, Foot Wl (Addr.add g.rdi i)) (fw2 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 2#64) i))
    (fw1 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 1#64) i))
    (h : ∀ (c d : BitVec 64) (b0 b2 b1 : BitVec 8) fl, Q 86 { g with rax := 0#64, rcx := c, rdx := d } fl
      (Vst (Vst (Vst V g.rdi (toBytesLE b0 1)) (g.rdi + 2#64) (toBytesLE b2 1)) (g.rdi + 1#64) (toBytesLE b1 1))) :
    W_36 F Wl Q g f V := by
  unfold W_36
  rw [o2_eq]
  refine wp_append _ _ (wp_mono o2a ?_ (pa g f V))
  rintro g₁ f₁ V₁ ⟨a, c, rfl, rfl⟩
  refine wp_append _ _ (wp_mono o2b ?_ (pb _ f₁ V fw0))
  rintro g₂ f₂ V₂ ⟨a₂, c₂, d₂, b0, rfl, rfl⟩
  refine wp_append _ _ (wp_mono o2c ?_ (pc _ f₂ _ fw2))
  rintro g₃ f₃ V₃ ⟨d₃, b2, rfl, rfl⟩
  refine wp_mono o2d ?_ (pd _ f₃ _ fw1)
  rintro g₄ f₄ V₄ ⟨d₄, b1, rfl, rfl⟩
  exact h c₂ d₄ b0 b2 b1 f₄

/-- What the run from the entry gives: at 96, `rax` and `rdx` some values and the memory as it was or `dicSize`
stored; at 86, `eax` 0 and the four stores. -/
def P0 (g₀ : Gprs) (V₀ : Addr → Byte) : Post := fun j g _ V =>
  (j = 96 ∧ ∃ a d, g = { g₀ with rax := a, rdx := d } ∧
      (V = V₀ ∨ ∃ w : BitVec 32, V = Vst V₀ (g₀.rdi + 4#64) (toBytesLE w 4))) ∨
    (j = 86 ∧ ∃ c d w b0 b2 b1, g = { g₀ with rax := 0#64, rcx := c, rdx := d } ∧ V = props V₀ g₀.rdi w b0 b2 b1)

/-- From the entry: the two exits to 96 and the stretch to 86. -/
set_option maxHeartbeats 1000000 in
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fr1 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 1#64) i)) (fr0 : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (fw4 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 4#64) i)) (fw0 : ∀ i < 1, Foot Wl (Addr.add g.rdi i))
    (fw2 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 2#64) i)) (fw1 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 1#64) i)) :
    W_0 F Wl (P0 g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fr1 fr0 fw4 fw0 fw2 fw1 ⊢
  wpx [W_0, W_9, o0, o1, Op.ldzx]
  repeat' (first | exact fr1 | exact fr0 | exact fw4 | apply And.intro | intro _)
  all_goals first
    | exact Or.inl ⟨rfl, _, _, rfl, Or.inl (by with_reducible rfl)⟩
    | exact Or.inl ⟨rfl, _, _, rfl, Or.inr ⟨_, by with_reducible rfl⟩⟩
    | exact vc_36 fw0 fw2 fw1 fun c d b0 b2 b1 _ => Or.inr ⟨rfl, c, d, _, b0, b2, b1, rfl, rfl⟩

/-- `mov eax, 4`. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 101 { g with rax := 4#64 } fl V) :
    W_96 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_96, o3, show BitVec.setWidth 64 4#32 = 4#64 from by decide]
  first | exact h _ | exact fun _ => h _ | exact fun _ _ => h _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `LzmaProps_Decode (p, data, size)` from its entry: the run reaches the return address with `Res` of the memory
and `rax`, `rcx` and `rdx` some values, the return address popped. -/
theorem lpd_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lpd_at lpd) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lpd_at)
    (fr1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 1#64) i))
    (fr0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 4#64) i)) (fw0 : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw2 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (fw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 1#64) i))
    (hpw : X.cpu.gpr.rdi.toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsep : X.cpu.gpr.rdi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ Z t' (V' : Addr → Byte) (r c d : BitVec 64), Res V X.cpu.gpr.rdi V' r → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := r, rcx := c, rdx := d, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e4 := tn_add X.cpu.gpr.rdi 4 (by decide) hpw
  have e2 := tn_add X.cpu.gpr.rdi 2 (by decide) hpw
  have e1 := tn_add X.cpu.gpr.rdi 1 (by decide) hpw
  have r4 : ∀ (V₀ : Addr → Byte) (w : BitVec 32), List.map (Vst V₀ (X.cpu.gpr.rdi + 4#64) (toBytesLE w 4))
      (byteAddrs X.cpu.gpr.rsp 8) = List.map V₀ (byteAddrs X.cpu.gpr.rsp 8) := fun V₀ w =>
    rdK V₀ _ _ _ 4 _ e4 (by rw [toBytesLE_length] <;> decide) hpw hsp hsep
  refine (c_0 prof).run c hin (P0 X.cpu.gpr V) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 fr1 fr0 fw4 fw0 fw2 fw1) ?_
  rintro j' g fl V₁ (⟨rfl, a, d, rfl, hV₁⟩ | ⟨rfl, c', d, w, b0, b2, b1, rfl, rfl⟩) Y t₁ hKY hAY hrY hgY -
  · refine (c_96 prof).run c hin (fun j' g' _ V' => j' = 101 ∧ g' = { Y.cpu.gpr with rax := 4#64 } ∧ V' = V₁)
      hKY hAY hrY (vc_96 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hgY] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_101 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · rw [hspZ]
      rcases hV₁ with rfl | ⟨w, rfl⟩
      · exact hra
      · rw [r4]; exact hra
    · rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      exact k Z' t₃ V₂ 4#64 X.cpu.gpr.rcx d (Or.inl ⟨rfl, hV₁⟩) hKZ' hAZ' hrZ' (by rw [hgZ', hgZ, hgY] <;> rfl)
  · have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_86 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · rw [hspY, props, rdK _ _ _ _ 1 _ e1 (by rw [toBytesLE_length] <;> decide) hpw hsp hsep,
        rdK _ _ _ _ 2 _ e2 (by rw [toBytesLE_length] <;> decide) hpw hsp hsep,
        rdK _ _ _ _ 0 _ rfl (by rw [toBytesLE_length] <;> decide) hpw hsp hsep, r4]
      exact hra
    · rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      exact k Z' t₃ _ 0#64 c' d (Or.inr ⟨rfl, w, b0, b2, b1, rfl⟩) hKZ' hAZ' hrZ' (by rw [hgZ', hgY] <;> rfl)

end FV7z.Lpd
