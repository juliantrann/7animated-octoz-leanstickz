import FV7z.Hsh.Cuts
import FV7z.Lemmas.LeafRet
import Std.Tactic.BVDecide
/-!
# `__hash_string`: the hash of a string (PLAN.md §M, M1)

glibc 2.31's `__hash_string (str)` at `0x6222e0` in `7zzs` (`intl/hash-string.c`; `objdump -d`): the ELF-style hash
of the bytes up to the NUL (`hval = (hval << 4) + c`, the top nibble of the low 32 bits folded back in), in `rax`.
The code reads the first byte (0: `xor eax, eax; ret` at 88), the second (0: `ret` at 80, the first byte the hash),
then loops from 40 (the step) to 72 (the next byte) and back, to the `ret` at 79.

- `rb`, `zx`: a byte as the code loads it, and zero-extended into a register (`movzx r32, byte`).
- `stepR h d`: one step of the code on the hash `h` and the byte `d` in `rdx`; `hashN V a n`: the hash of the `n`
  bytes at `a` (`stepR 0 (zx b) = zx b`: the first byte is its own hash, `step0`).
- `vc_*`: the pieces from the cut points; `loop`: from 40 to 79 by induction on the bytes left;
  `hsh_ok`: from the entry to the return address, `rax` the hash, `rcx`, `rdx`, `rsi` some values.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hsh

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_79 : pret <+: hsh.drop 79 := by decide +kernel
theorem w_80 : pret <+: hsh.drop 80 := by decide +kernel
theorem w_90 : pret <+: hsh.drop 90 := by decide +kernel
theorem ret_79 (feat : Features) : Dec feat hsh 79 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 79) (k := 0) (pret_0 feat) w_79 (Nat.zero_le _)
theorem ret_80 (feat : Features) : Dec feat hsh 80 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 80) (k := 0) (pret_0 feat) w_80 (Nat.zero_le _)
theorem ret_90 (feat : Features) : Dec feat hsh 90 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 90) (k := 0) (pret_0 feat) w_90 (Nat.zero_le _)

/-- The byte at `a`, as the code loads it. -/
abbrev rb (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs a 1).map V)
/-- A byte in a register by `movzx r32, byte`: to 32 bits, the upper half cleared. -/
abbrev zx (b : BitVec 8) : BitVec 64 := (b.setWidth 32).setWidth 64
/-- `shl rax, 4; add rax, rdx`. -/
abbrev hx (h d : BitVec 64) : BitVec 64 := h <<< 4 + d
/-- `mov rdx, rax; and edx, 0xf0000000`. -/
abbrev hg (h d : BitVec 64) : BitVec 32 := BitVec.setWidth 32 (hx h d) &&& 4026531840#32
/-- One step: with the top nibble (of the low 32 bits) set, `and rax, ~0xf0000000; shr rdx, 24; xor rax, rdx`. -/
def stepR (h d : BitVec 64) : BitVec 64 :=
  if (hg h d == 0#32) = true then hx h d
  else (hx h d &&& 18446744069683019775#64) ^^^ ((hg h d).setWidth 64 >>> 24)
/-- The hash of the `n` bytes at `a`. -/
def hashN (V : Addr → Byte) (a : Addr) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => stepR (hashN V a n) (zx (rb V (a + BitVec.ofNat 64 n)))

/-- The first byte is its own hash (the top nibble is clear). -/
theorem step0 : ∀ b : BitVec 8, stepR 0 (zx b) = zx b := by
  first
  | decide +kernel
  | (intro b; simp only [stepR, hg, hx, zx]; bv_decide)

/-- The hash of one byte. -/
theorem hash1 (V : Addr → Byte) (a : Addr) : hashN V a 1 = zx (rb V a) := by
  show stepR 0 (zx (rb V (a + BitVec.ofNat 64 0))) = _
  rw [step0, BitVec.add_zero]

theorem sw8 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow] at this ⊢
  omega

theorem adv (a : Addr) (k : Nat) : a + BitVec.ofNat 64 k + 1#64 = a + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem a0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem ft1 {F : Footprint} {x : Addr} (h : Foot F.data x) : ∀ j < 1, Foot F.data (Addr.add x j) := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [addr_add_zero]
  exact h

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry, the first byte 0: to 88, `eax` 0, then the `ret` (90). -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ j < 1, Foot F.data (Addr.add g.rdi j))
    (h0 : rb V g.rdi = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 90 ∧ g' = { g with rax := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fa h0 ⊢
  have hz : (ofBytesLE 8 ((byteAddrs rdi 1).map V) == 0) = true := by rw [h0]; rfl
  wpx [W_0, W_11, W_33, W_88, o0, o1, o2, o6, sw8, BitVec.and_self, hz, BitVec.xor_self, BitVec.reduceSetWidth,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)

/-- From the entry, the first byte not 0, the second 0: to the `ret` at 80, the first byte in `rax`. -/
theorem vc_0a {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ j < 1, Foot F.data (Addr.add g.rdi j))
    (fb : ∀ j < 1, Foot F.data (Addr.add (g.rdi + 1#64) j)) (h0 : rb V g.rdi ≠ 0) (h1 : rb V (g.rdi + 1#64) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 80 ∧
      g' = { g with
        rax := zx (rb V g.rdi), rdx := zx (rb V (g.rdi + 1#64)), rcx := g.rdi + 1#64,
        rsi := 18446744069683019775#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fa fb h0 h1 ⊢
  have hz0 : (ofBytesLE 8 ((byteAddrs rdi 1).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  have hz1 : (ofBytesLE 8 ((byteAddrs (rdi + 1#64) 1).map V) == 0) = true := by rw [h1]; rfl
  wpx [W_0, W_11, W_33, W_88, o0, o1, o2, o6, sw8, BitVec.and_self, hz0, hz1, BitVec.xor_self,
    BitVec.reduceSetWidth, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true,
    Bool.not_false]
  all_goals repeat' (first | exact fa | exact fb | exact rfl | exact trivial | apply And.intro | intro _)

/-- From the entry, the first two bytes not 0: to the loop (40). -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ j < 1, Foot F.data (Addr.add g.rdi j))
    (fb : ∀ j < 1, Foot F.data (Addr.add (g.rdi + 1#64) j)) (h0 : rb V g.rdi ≠ 0) (h1 : rb V (g.rdi + 1#64) ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧
      g' = { g with
        rax := zx (rb V g.rdi), rdx := zx (rb V (g.rdi + 1#64)), rcx := g.rdi + 1#64,
        rsi := 18446744069683019775#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fa fb h0 h1 ⊢
  have hz0 : (ofBytesLE 8 ((byteAddrs rdi 1).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  have hz1 : (ofBytesLE 8 ((byteAddrs (rdi + 1#64) 1).map V) == 0) = false := beq_eq_false_iff_ne.2 h1
  wpx [W_0, W_11, W_33, W_88, o0, o1, o2, o6, sw8, BitVec.and_self, hz0, hz1, BitVec.xor_self,
    BitVec.reduceSetWidth, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true,
    Bool.not_false]
  all_goals repeat' (first | exact fa | exact fb | exact rfl | exact trivial | apply And.intro | intro _)

/-- The step, from 40 to 72: `rax` the next hash, `rcx` one on, `rdx` some value. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hm : g.rsi = 18446744069683019775#64) :
    W_40 F Wl (fun j' g' _ V' => j' = 72 ∧
      (∃ d, g' = { g with rax := stepR g.rax g.rdx, rcx := g.rcx + 1#64, rdx := d }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  subst hm
  by_cases hz : (hg rax rdx == 0#32) = true
  · have e : stepR rax rdx = hx rax rdx := if_pos hz
    rw [e]
    dsimp only [hg, hx] at hz
    wpx [W_40, W_62, o3, o4, Op.shl64, Op.shr64, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies,
      implies_true, Bool.not_true, Bool.not_false]
    all_goals repeat' (first | exact ⟨_, rfl⟩ | exact rfl | exact trivial | apply And.intro | intro _)
    all_goals first | exact ⟨_, rfl⟩ | (exfalso; simp_all)
  · have e : stepR rax rdx = (hx rax rdx &&& 18446744069683019775#64) ^^^ ((hg rax rdx).setWidth 64 >>> 24) :=
      if_neg hz
    rw [e]
    have hz' : (hg rax rdx == 0#32) = false := by simpa using hz
    dsimp only [hg, hx] at hz' ⊢
    wpx [W_40, W_62, o3, o4, Op.shl64, Op.shr64, hz', Bool.true_eq_false, Bool.false_eq_true, false_implies,
      implies_true, Bool.not_true, Bool.not_false]
    all_goals repeat' (first | exact ⟨_, rfl⟩ | exact rfl | exact trivial | apply And.intro | intro _)
    all_goals first | exact ⟨_, rfl⟩ | (exfalso; simp_all)

/-- The next byte, from 72: not 0, back to 40. -/
theorem vc_72c {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ j < 1, Foot F.data (Addr.add g.rcx j))
    (h : rb V g.rcx ≠ 0) :
    W_72 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = { g with rdx := zx (rb V g.rcx) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fa h ⊢
  have hz : (ofBytesLE 8 ((byteAddrs rcx 1).map V) == 0) = false := beq_eq_false_iff_ne.2 h
  wpx [W_72, o5, sw8, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)

/-- The next byte, from 72: 0, to the `ret` (79). -/
theorem vc_72e {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ j < 1, Foot F.data (Addr.add g.rcx j))
    (h : rb V g.rcx = 0) :
    W_72 F Wl (fun j' g' _ V' => j' = 79 ∧ g' = { g with rdx := zx (rb V g.rcx) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fa h ⊢
  have hz : (ofBytesLE 8 ((byteAddrs rcx 1).map V) == 0) = true := by rw [h]; rfl
  wpx [W_72, o5, sw8, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)

/-! ## The loop and the function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The registers at 40 after `kk` bytes, at 79 after all `n`. -/
abbrev Gk (g₀ : Gprs) (V : Addr → Byte) (a : Addr) (kk : Nat) : Gprs :=
  { g₀ with
    rax := hashN V a kk, rcx := a + BitVec.ofNat 64 kk, rdx := zx (rb V (a + BitVec.ofNat 64 kk)),
    rsi := 18446744069683019775#64 }

/-- From 40 with `kk` bytes hashed and `m + 1` left (the `kk`-th not 0): to 79 with the `n` bytes hashed. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hsh_at hsh) {V : Addr → Byte} {a : Addr} {n : Nat}
    {g₀ : Gprs} (fa : ∀ i < n + 1, Foot F.data (a + BitVec.ofNat 64 i))
    (hnz : ∀ i < n, rb V (a + BitVec.ofNat 64 i) ≠ 0) (hz : rb V (a + BitVec.ofNat 64 n) = 0)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = hsh_at.add 79 →
      Z.cpu.gpr = Gk g₀ V a n → GoG prof L o gev gP gE Z t') :
    ∀ (m kk : Nat), kk + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = hsh_at.add 40 → X.cpu.gpr = Gk g₀ V a kk → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro kk hkk X t hK hA hrip hX
    have hn : kk + 1 = n := by omega
    refine (c_40 prof).run c hin _ hK hA hrip (vc_40 (by rw [hX]; try rfl)) ?_
    rintro j' g fl V' ⟨rfl, ⟨d, hg⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    have e : Y.cpu.gpr.rcx = a + BitVec.ofNat 64 (kk + 1) := by
      rw [hgY, hg, hX]
      exact adv a kk
    refine (c_72 prof).run c hin _ hKY hAY hrY
      (vc_72e (by rw [e]; exact ft1 (fa _ (by omega))) (by rw [e, hn]; exact hz)) ?_
    rintro j' g₂ fl V₂ ⟨rfl, hg₂, hV₂⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V₂
    refine k Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hg₂, e, hgY, hg, hX, ← hn]
    dsimp only [Gk]
    rfl
  | succ m ih =>
    intro kk hkk X t hK hA hrip hX
    refine (c_40 prof).run c hin _ hK hA hrip (vc_40 (by rw [hX]; try rfl)) ?_
    rintro j' g fl V' ⟨rfl, ⟨d, hg⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    have e : Y.cpu.gpr.rcx = a + BitVec.ofNat 64 (kk + 1) := by
      rw [hgY, hg, hX]
      exact adv a kk
    refine (c_72 prof).run c hin _ hKY hAY hrY
      (vc_72c (by rw [e]; exact ft1 (fa _ (by omega))) (by rw [e]; exact hnz _ (by omega))) ?_
    rintro j' g₂ fl V₂ ⟨rfl, hg₂, hV₂⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V₂
    refine ih (kk + 1) (by omega) Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hg₂, e, hgY, hg, hX]
    dsimp only [Gk]
    rfl

/-- The `ret`s: from `Y` at a `ret` with the registers `G` (`rsp` as at the entry) to the return address. -/
theorem ret_k (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hsh_at hsh) {V : Addr → Byte} {X : State} {j : Nat}
    (hj : j < 91) (hd : Dec prof.feat hsh j (FV7z.mk .ret 64 [] 1)) {Y : State} {t' : Nat} (hKY : KeptW Wl s₀ Y)
    (hAY : Agree F Y.proc.mm.mem V) (hrY : Y.cpu.rip = hsh_at.add j) {G : Gprs} (hgY : Y.cpu.gpr = G)
    (hsp : G.rsp = X.cpu.gpr.rsp) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = G.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t' := by
  refine c.s_ret hKY hAY hin (lt_len hj) hrY hd (fun i hi => by rw [hgY, hsp]; exact hl i hi) hin₂ h₂
    (by rw [hgY, hsp]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY, hsp])

/-- `__hash_string (str)` from its entry, the `n` bytes at `str` not 0 and the next 0: at the return address, the
return address popped, `rax` the hash of the `n` bytes, `rcx`, `rdx`, `rsi` some values, the rest and the memory
kept. -/
theorem hsh_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hsh_at hsh) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = hsh_at) {n : Nat}
    (fa : ∀ i < n + 1, Foot F.data (X.cpu.gpr.rdi + BitVec.ofNat 64 i))
    (hnz : ∀ i < n, rb V (X.cpu.gpr.rdi + BitVec.ofNat 64 i) ≠ 0) (hz : rb V (X.cpu.gpr.rdi + BitVec.ofNat 64 n) = 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ cx dx si, Z.cpu.gpr = Gprs.set { X.cpu.gpr with
        rax := hashN V X.cpu.gpr.rdi n, rcx := cx, rdx := dx, rsi := si } 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have f0 : ∀ j < 1, Foot F.data (Addr.add X.cpu.gpr.rdi j) := ft1 (by rw [← a0 X.cpu.gpr.rdi]; exact fa 0 (by omega))
  have hrip' : X.cpu.rip = hsh_at.add 0 := by rw [addr_add_zero]; exact hrip
  rcases n with _ | _ | n
  · -- the empty string
    have h0 : rb V X.cpu.gpr.rdi = 0 := by rw [← a0 X.cpu.gpr.rdi]; exact hz
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0e f0 h0) ?_
    rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    exact ret_k c hin (by decide) (ret_90 _) hKY hAY hrY (hgY.trans hg) rfl hl hin₂ h₂ hra
      fun Z t₂ hKZ hAZ hrZ hgZ => k Z t₂ hKZ hAZ hrZ ⟨_, _, _, hgZ⟩
  · -- one byte
    have h0 : rb V X.cpu.gpr.rdi ≠ 0 := by rw [← a0 X.cpu.gpr.rdi]; exact hnz 0 (by omega)
    have f1 : ∀ j < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 1#64) j) := ft1 (fa 1 (by omega))
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0a f0 f1 h0 hz) ?_
    rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine ret_k c hin (by decide) (ret_80 _) hKY hAY hrY (hgY.trans hg) rfl hl hin₂ h₂ hra
      fun Z t₂ hKZ hAZ hrZ hgZ => k Z t₂ hKZ hAZ hrZ ⟨X.cpu.gpr.rdi + 1#64, zx (rb V (X.cpu.gpr.rdi + 1#64)),
        18446744069683019775#64, ?_⟩
    rw [hgZ, hash1]
  · -- two bytes or more: the loop
    have h0 : rb V X.cpu.gpr.rdi ≠ 0 := by rw [← a0 X.cpu.gpr.rdi]; exact hnz 0 (by omega)
    have h1 : rb V (X.cpu.gpr.rdi + 1#64) ≠ 0 := hnz 1 (by omega)
    have f1 : ∀ j < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 1#64) j) := ft1 (fa 1 (by omega))
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0b f0 f1 h0 h1) ?_
    rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine loop c hin fa hnz hz (g₀ := X.cpu.gpr) ?_ n 1 (by omega) Y t₁ hKY hAY hrY ?_
    · intro Z t₂ hKZ hAZ hrZ hgZ
      exact ret_k c hin (by decide) (ret_79 _) hKZ hAZ hrZ hgZ rfl hl hin₂ h₂ hra
        fun Z' t₃ hKZ' hAZ' hrZ' hgZ' => k Z' t₃ hKZ' hAZ' hrZ' ⟨_, _, _, hgZ'⟩
    · rw [hgY, hg]
      dsimp only [Gk]
      rw [hash1]

end FV7z.Hsh
