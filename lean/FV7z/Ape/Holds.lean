import FV7z.Ape.Cuts
import FV7z.Agr.Code
import FV7z.Agr.Blocks
import FV7z.Acp.Loop
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.Fr24
import FV7z.Tun.Inv
/-!
# `AString::operator+= (const AString &)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::operator+= (const AString &s)` at `0x44c920` in `7zzs` (`CPP/Common/MyString.cpp`), `this` =
`rdi`, `s` = `rsi`: `push r12; mov r12, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, [rsi + 8]`; at 20 the `call`
of `Grow (s._len)` (`Agr.agr_at`); at 25 `mov r8, [rbx]; mov esi, [r12 + 8]; xor edx, edx; add rsi, [r12]` (`r8` =
`s._chars`, `rsi` = `_chars + _len`); the copy loop at 48 (`movzx ecx, byte [r8 + rdx]; mov [rsi + rdx], cl;
add rdx, 1; test cl, cl; jne 48`, as in `AString::operator= (const AString &)`, `FV7z/Aas/Loop.lean`); at 64
`mov eax, [rbx + 8]`; at 67 `add dword [r12 + 8], eax` (`Seg.s_add_mr32`: `_len += s._len`); at 72 `add rsp, 8;
mov rax, r12; pop rbx; pop r12`; the `ret` (82).

Design as `FV7z/Upe/Holds.lean` (`UString::operator+=`, the same frame) with the copy proved here in place of the
`call` of `wmemcpy`: `Grow` is a hypothesis (`k1`), a continuation at its entry given the run from its return with
its own post `P1`; of the bytes `W` it leaves the caller gives the copy's facts (`hcp`, `Cpy`: the `n` bytes of
`s._chars` not 0 and a 0 after them, the `n + 1` bytes at `_chars + _len` writable and apart from them and from the
frame). The bytes copied are `Acp.Cp`, as in `AString (const AString &)`.

- `V0`, `gE`: the bytes and the registers at the `call`; `src`, `dst`: where the copy reads and writes; `g48`: the
  registers at the loop; `V3`: the bytes after the `add`; `Cpy`: the copy's facts.
- `vc_0`, `vc_25`, `vc_48n`, `vc_48z`, `vc_72`: the verification conditions of the pieces; `loop`: the copy by
  induction.
- `ape_ok`: from the entry to the return address with `rax` = `this`, `rbx`, `r12`, `rsp` restored, the bytes `V3`
  of the copy's.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24 FV7z.Mys
namespace FV7z.Ape

/-- The `call` to `AString::Grow`. -/
def pcg : List Byte := [0xe8, 0xa7, 0xf7, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709549479] 5) := by dec_rfl
theorem wg_20 : pcg <+: ape.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat ape 20 (FV7z.mk .call 64 [.rel 18446744073709549479] 5) :=
  Dec.shift (j := 20) (k := 0) (pcg_0 feat) wg_20 (Nat.zero_le _)
theorem tgt_20 : ape_at.add (20 + 5) + BitVec.ofNat 64 18446744073709549479 = Agr.agr_at.add 0 := by decide

/-- `add dword [r12 + 8], eax`. -/
def pad : List Byte := [0x41, 0x01, 0x44, 0x24, 0x08]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 0] 5) := by dec_rfl
theorem wa_67 : pad <+: ape.drop 67 := by decide +kernel
theorem add_67 (feat : Features) : Dec feat ape 67 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 0] 5) :=
  Dec.shift (j := 67) (k := 0) (pad_0 feat) wa_67 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_82 : pret <+: ape.drop 82 := by decide +kernel
theorem ret_82 (feat : Features) : Dec feat ape 82 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 82) (k := 0) (pret_0 feat) w_82 (Nat.zero_le _)

/-- The bytes after `push r12; push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call`: `r12` = `this`, `rbx` = `s`, `esi` = `s._len` (read from `V0`), `rsp` 24 down. -/
abbrev gE (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8#64
    rsi := BitVec.setWidth 64 rdd(V0 V g, g.rsi + 8#64)
    r12 := g.rdi }

/-- `s._chars` of the string at `q` in the bytes `W`: where the copy reads. -/
abbrev src (W : Addr → Byte) (q : Addr) : Addr := rdq(W, q)

/-- `_chars + _len` of the string at `p` in the bytes `W`: where the copy writes. -/
abbrev dst (W : Addr → Byte) (p : Addr) : Addr := BitVec.setWidth 64 rdd(W, p + 8#64) + rdq(W, p)

/-- The registers at the loop: `r8` = `s._chars`, `rsi` = `_chars + _len`, `rdx` = 0. -/
abbrev g48 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rdx := 0#64
    rsi := dst V g.r12
    r8 := src V g.rbx }

/-- The bytes after `_len += s._len` (`this` = `p`, `s` = `q`). -/
abbrev V3 (W : Addr → Byte) (p q : Addr) : Addr → Byte :=
  Vst W (p + 8#64) (toBytesLE (rdd(W, p + 8#64) + rdd(W, q + 8#64)) 4)

/-- The copy's facts of the bytes `W` that `Grow` leaves (`this` = `p`, `s` = `q`, `S` the entry's `rsp`): the `n`
bytes of `s._chars` not 0, a 0 after them, all readable; the `n + 1` bytes at `_chars + _len` writable, apart from
them, from the saved `rbx` and `r12` and from the return address. -/
structure Cpy (F : Footprint) (Wl : List Rgn) (W : Addr → Byte) (p q S : Addr) (n : Nat) : Prop where
  nz : ∀ i < n, W (Addr.add (src W q) i) ≠ 0
  z : W (Addr.add (src W q) n) = 0
  rd : ∀ i, i ≤ n → Foot F.data (Addr.add (src W q) i)
  wr : ∀ i, i ≤ n → Foot Wl (Addr.add (dst W p) i)
  sep : ∀ i, i ≤ n → ∀ j, j ≤ n → Addr.add (src W q) i ≠ Addr.add (dst W p) j
  f16 : ∀ b < 8, ∀ i < n + 1, Addr.add (S - 16) b ≠ Addr.add (dst W p) i
  f8 : ∀ b < 8, ∀ i < n + 1, Addr.add (S - 8) b ≠ Addr.add (dst W p) i
  f0 : ∀ b < 8, ∀ i < n + 1, Addr.add S b ≠ Addr.add (dst W p) i

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, [rsi + 8]`, to the `call` at 20. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h : ∀ fl, Q 20 (gE g V) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gE, V0] at hs1 hs2 fn h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov r8, [rbx]; mov esi, [r12 + 8]; xor edx, edx; add rsi, [r12]`, to the loop at 48. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (f2 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ fl, Q 48 (g48 g V) fl V) : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g48, dst, src] at f1 f2 f3 h ⊢
  wpx [W_25, o1, xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at a byte not 0: the byte stored, `rdx` one on, back to 48. -/
theorem vc_48n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.r8 + g.rdx) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.r8 + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rsi + g.rdx) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 48 ∧ g'.rdx = g.rdx + 1#64 ∧ g'.r8 = g.r8 ∧ g'.rsi = g.rsi ∧ Kp g g' ∧
      V' = Vst V (g.rsi + g.rdx) [V (g.r8 + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_48, W_64, o2, o3, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at the 0: the 0 stored, then `mov eax, [rbx + 8]` (`s._len`, after the store), to the `add` at
67. -/
theorem vc_48z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.r8 + g.rdx) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.r8 + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rsi + g.rdx) i))
    (hq : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 67 ∧ Kp g g' ∧ g'.rax = BitVec.setWidth 64 rdd(V', g.rbx + 8#64) ∧
      V' = Vst V (g.rsi + g.rdx) [V (g.r8 + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw hq ⊢
  wpx [W_48, W_64, o2, o3, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `add rsp, 8; mov rax, r12; pop rbx; pop r12`, to the `ret` at 82. -/
theorem vc_72 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 82
      { g with
        rax := g.r12
        rbx := rdq(V, g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_72 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_72, o4]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}

/-- The copy loop from 48 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`, `r8` = `p`), the first `j`
stored at `d` (`rsi`): on to the `add` at 67 with all `n + 1` stored, `eax` = `s._len` read after them (`rbx` = `s`)
and the registers a call keeps as at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ape_at ape) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j)
    (hq : ∀ i < 4, Foot F.data (Addr.add (g₀.rbx + 8#64) i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Acp.Cp W p d (n + 1)) →
      Z.cpu.rip = ape_at.add 67 → Kp g₀ Z.cpu.gpr →
      Z.cpu.gpr.rax = BitVec.setWidth 64 rdd(Acp.Cp W p d (n + 1), g₀.rbx + 8#64) →
      GoG prof L o gev gP gE' Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Acp.Cp W p d j) →
      X.cpu.rip = ape_at.add 48 → X.cpu.gpr.rdx = BitVec.ofNat 64 j → X.cpu.gpr.r8 = p → X.cpu.gpr.rsi = d →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE' X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hr8 hsi hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.r8 + X.cpu.gpr.rdx = p.add j := by rw [hr8, hdx]; rfl
    have ed : X.cpu.gpr.rsi + X.cpu.gpr.rdx = d.add j := by rw [hsi, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.r8 + X.cpu.gpr.rdx) == 0) = true := by
      rw [es, hb]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.r8 + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    have hq' : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rbx + 8#64) i) := by rw [hkp.2.1]; exact hq
    refine (c_48 prof).run c hin _ hK hA hrip (vc_48z hz' hf1 hw1 hq') ?_
    rintro j' g fl V₁ ⟨rfl, hkp', hax', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) ?_
    rw [hgY, hax', hkp.2.1] <;> rfl
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hr8 hsi hkp
    have es : X.cpu.gpr.r8 + X.cpu.gpr.rdx = p.add j := by rw [hr8, hdx]; rfl
    have ed : X.cpu.gpr.rsi + X.cpu.gpr.rdx = d.add j := by rw [hsi, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.r8 + X.cpu.gpr.rdx) == 0) = false := by
      rw [es, hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.r8 + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_48 prof).run c hin _ hK hA hrip (vc_48n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hr8', hsi', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ ?_ ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    · rw [hgY, hdx', hdx]
      exact (BitVec.ofNat_add j 1).symm
    · rw [hgY, hr8', hr8]
    · rw [hgY, hsi', hsi]

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::operator+= (s)` (`this` = `rdi`, `s` = `rsi`) from its entry, `r12` and `rbx` saved at `rsp - 8` and
`rsp - 16`: at `Grow`'s entry with the registers `gE`, the return address `ape_at + 25` at `rsp - 32` (`k1`); from its
return (the bytes `W`, the post `P1`, the copy's facts `Cpy` by `hcp`), the copy of `s._chars` through its 0 to
`_chars + _len` (`Acp.Cp`), `_len += s._len` (`V3`), and the return address with `rax` = `this`, `rbx`, `r12`, `rsp`
restored and `rbp`, `r13`–`r15` as `Grow` left them (`kr`). -/
theorem ape_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ape_at ape)
    (hinG : CodeIn L Agr.agr_at Agr.agr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ape_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ape_at.add 25) 8)) →
      Y.cpu.rip = Agr.agr_at → Y.cpu.gpr = (gE X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (W : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
        Z.cpu.rip = ape_at.add 25 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.r12 = X.cpu.gpr.rdi → rdq(W, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z W →
        GoG prof L o gev gP gE' Z t'') →
      GoG prof L o gev gP gE' Y t')
    (hcp : ∀ (Z : State) (W : Addr → Byte), P1 Z W →
      ∃ n, Cpy F Wl W X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rsp n)
    (kr : ∀ (Z : State) (W : Addr → Byte) (n : Nat) (Z' : State) (t' : Nat), P1 Z W →
      Cpy F Wl W X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rsp n → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rax = X.cpu.gpr.rdi → Z'.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z'.cpu.gpr.r12 = X.cpu.gpr.r12 → Z'.cpu.gpr.rbp = Z.cpu.gpr.rbp →
      Z'.cpu.gpr.r13 = Z.cpu.gpr.r13 → Z'.cpu.gpr.r14 = Z.cpu.gpr.r14 → Z'.cpu.gpr.r15 = Z.cpu.gpr.r15 →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have fl8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i) := fun i hi => c.hws _ (fw i hi)
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := pt8 _ hp
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := pt16 _ hp
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the frame's bytes as they were after the `add` to `_len`
  have m3 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (V3 W X.cpu.gpr.rdi X.cpu.gpr.rsi) = (byteAddrs x 8).map W := fun W x hx h =>
    Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, t8]; omega) hx (by rw [toBytesLE_length, t8]; omega)
  have hrip' : X.cpu.rip = ape_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the prologue, to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gE X.cpu.gpr V ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) fn fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, pe32]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_20 _) hinG (tgt := 0) (Agr.lt_len (by decide))
    tgt_20 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gE X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
  refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `Grow`, at 25: to the loop
  intro Z W t'' hKZ hAZ hrZ hzs hzb hz12 hb hr12 hr' hP1
  obtain ⟨n, cp⟩ := hcp Z W hP1
  refine (c_25 prof).run c hin (fun j' g' _ V'' => j' = 48 ∧ g' = g48 Z.cpu.gpr W ∧ V'' = W) hKZ hAZ hrZ
    (vc_25 (by rw [hzb]; exact fb) (by rw [hz12]; exact fl8) (by rw [hz12]; exact fc) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hU8 : U.cpu.gpr.r8 = src W X.cpu.gpr.rsi := by
    rw [hgU]
    show rdq(W, Z.cpu.gpr.rbx) = _
    rw [hzb]
  have hUsi : U.cpu.gpr.rsi = dst W X.cpu.gpr.rdi := by
    rw [hgU]
    show dst W Z.cpu.gpr.r12 = _
    rw [hz12]
  have hUdx : U.cpu.gpr.rdx = BitVec.ofNat 64 0 := by rw [hgU] <;> rfl
  have hUb : U.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hgU]; exact hzb
  have hUs : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
  have hU12 : U.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgU]; exact hz12
  have hUk : U.cpu.gpr.rbp = Z.cpu.gpr.rbp ∧ U.cpu.gpr.r13 = Z.cpu.gpr.r13 ∧ U.cpu.gpr.r14 = Z.cpu.gpr.r14 ∧
      U.cpu.gpr.r15 = Z.cpu.gpr.r15 := by
    rw [hgU]
    exact ⟨rfl, rfl, rfl, rfl⟩
  -- the copy, to the `add` at 67
  refine loop c hin (W := W) (p := src W X.cpu.gpr.rsi) (d := dst W X.cpu.gpr.rdi) (n := n) (g₀ := U.cpu.gpr)
    cp.nz cp.z cp.rd cp.wr cp.sep (by rw [hUb]; exact fn) ?_ n 0 (by omega) U t₃ hKU hAU hrU hUdx hU8 hUsi
    (Kp.refl _)
  intro Z₃ t₄ hK₃ hA₃ hr₃ hkp3 hz3a
  obtain ⟨k3s, k3b, k3p, k312, k313, k314, k315⟩ := hkp3
  have e12 : eaD Z₃ 12 8 = X.cpu.gpr.rdi + 8#64 := by
    show Z₃.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 8 = _
    rw [show Z₃.cpu.gpr.get (regOf 12) = Z₃.cpu.gpr.r12 from rfl, k312, hU12]
  have erv : rv Z₃ 32 0 =
      rdd(Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1), X.cpu.gpr.rsi + 8#64) := by
    show BitVec.setWidth 32 (Z₃.cpu.gpr.get (regOf 0)) = _
    rw [show Z₃.cpu.gpr.get (regOf 0) = Z₃.cpu.gpr.rax from rfl, hz3a, hUb]
    exact sw_64_32 _
  refine c.s_add_mr32 hK₃ hA₃ hin (lt_len (by decide)) hr₃ (add_67 _) (by rw [e12]; exact fw) ?_
  rw [e12, erv]
  rintro Y₆ t₇ hK₆ hA₆ ⟨hr₆, hg₆⟩
  replace hA₆ : Agree F Y₆.proc.mm.mem
      (V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi) := hA₆
  have hY6s : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₆, k3s, hUs]
  have hY6r : Y₆.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hg₆, k312, hU12]
  have hb2' : rdq(V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi,
      X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [m3 _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact (congrArg (ofBytesLE 64) (Acp.rd_far W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) cp.f16)).trans hb
  have h12b' : rdq(V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi,
      X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
    rw [m3 _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact (congrArg (ofBytesLE 64) (Acp.rd_far W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) cp.f8)).trans hr12
  have hr2' : rdq(V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi,
      X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m3 _ X.cpu.gpr.rsp hp8 (by omega)]
    exact (congrArg (ofBytesLE 64) (Acp.rd_far W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) cp.f0)).trans hr'
  -- the epilogue at 72, then the `ret` at 82
  refine (c_72 prof).run c hin (fun j' g' _ V'' => j' = 82 ∧
      g' = { Y₆.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp
        r12 := X.cpu.gpr.r12 } ∧
      V'' = V3 (Acp.Cp W (src W X.cpu.gpr.rsi) (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi X.cpu.gpr.rsi)
    hK₆ hA₆ hr₆
    (vc_72 (by rw [hY6s, peA']; exact h16) (by rw [hY6s, peA', peB]; exact h8)
      fun _ => ⟨rfl, by rw [hY6s, hY6r, peA', peB, peC, hb2', h12b'], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₈ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₄
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_82 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hr2') ?_
  rintro Z' t₉ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  have hY6k : Y₆.cpu.gpr.rbp = Z.cpu.gpr.rbp ∧ Y₆.cpu.gpr.r13 = Z.cpu.gpr.r13 ∧
      Y₆.cpu.gpr.r14 = Z.cpu.gpr.r14 ∧ Y₆.cpu.gpr.r15 = Z.cpu.gpr.r15 := by
    rw [hg₆, k3p, k313, k314, k315]
    exact hUk
  refine kr Z W n Z' t₉ hP1 cp hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hgZ', hgU₂] <;> rfl
  · rw [hgZ', hgU₂] <;> rfl
  · rw [hgZ', hsU₂] <;> rfl
  · rw [hgZ', hgU₂] <;> rfl
  · rw [hgZ', hgU₂]
    exact hY6k.1
  · rw [hgZ', hgU₂]
    exact hY6k.2.1
  · rw [hgZ', hgU₂]
    exact hY6k.2.2.1
  · rw [hgZ', hgU₂]
    exact hY6k.2.2.2

end FV7z.Ape
