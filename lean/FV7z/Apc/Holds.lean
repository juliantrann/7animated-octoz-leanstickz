import FV7z.Apc.Cuts
import FV7z.Agr.Code
import FV7z.Agr.Blocks
import FV7z.Acp.Loop
import FV7z.Acc.Loop
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.Fr24
import FV7z.Tun.Inv
/-!
# `AString::operator+= (const char *)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::operator+= (const char *s)` at `0x44c890` in `7zzs` (`CPP/Common/MyString.cpp`), `this` =
`rdi`, `s` = `rsi`: `push r12; mov r12, rdi; push rbp; mov rbp, rsi; push rbx; xor ebx, ebx; cmp byte [rsi], 0;
je 37`; the length loop at 24 (`lea edx, [rbx + 1]; cmp byte [rbp + rdx], 0; mov rbx, rdx; jne 24`, as in
`AString::operator= (const char *)`, `FV7z/Aac/Loop.lean`); at 37 `mov esi, ebx; mov rdi, r12` and the `call` of
`Grow (len)` at 42 (`Agr.agr_at`); at 47 `mov esi, [r12 + 8]; xor edx, edx; add rsi, [r12]` (`rsi` = `_chars + _len`);
the copy loop at 64 (`movzx ecx, byte [rbp + rdx]; mov [rsi + rdx], cl; add rdx, 1; test cl, cl; jne 64`); at 80
`add dword [r12 + 8], ebx` (`Seg.s_add_mr32`: `_len += len`); at 85 `mov rax, r12; pop rbx; pop rbp; pop r12`; the
`ret` (92).

Design as `FV7z/Ape/Holds.lean` (`AString::operator+= (const AString &)`), with the length computed here: the `n`
bytes of `s` not 0 and a 0 after them are hypotheses on the bytes after the pushes (`sn`, `sz`); `Grow` is a
hypothesis (`k1`), a continuation at its entry given the run from its return with its own post `P1`; of the bytes `W`
it leaves the caller gives the copy's facts for the same `n` (`hcp`, `Cpy`). The bytes copied are `Acp.Cp`.

- `V0`, `gS`: the bytes and the registers after the pushes; `nb`: `ebx + 1`, zero-extended; `Ks`: the registers the
  length loop keeps; `dst`: where the copy writes; `g64`: the registers at the copy loop; `V3`: the bytes after the
  `add`; `Cpy`: the copy's facts.
- `vc_0z`, `vc_0n`, `vc_24n`, `vc_24z`, `vc_37`, `vc_47`, `vc_64n`, `vc_64z`, `vc_85`: the verification conditions of
  the pieces; `slen`, `loop`: the two loops by induction.
- `apc_ok`: from the entry to the return address with `rax` = `this`, `rbx`, `rbp`, `r12`, `rsp` restored, the bytes
  `V3` of the copy's.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24 FV7z.Mys
namespace FV7z.Apc

/-- The `call` to `AString::Grow`. -/
def pcg : List Byte := [0xe8, 0x21, 0xf8, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709549601] 5) := by dec_rfl
theorem wg_42 : pcg <+: apc.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat apc 42 (FV7z.mk .call 64 [.rel 18446744073709549601] 5) :=
  Dec.shift (j := 42) (k := 0) (pcg_0 feat) wg_42 (Nat.zero_le _)
theorem tgt_42 : apc_at.add (42 + 5) + BitVec.ofNat 64 18446744073709549601 = Agr.agr_at.add 0 := by decide

/-- `add dword [r12 + 8], ebx`. -/
def pad : List Byte := [0x41, 0x01, 0x5c, 0x24, 0x08]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 3] 5) := by dec_rfl
theorem wa_80 : pad <+: apc.drop 80 := by decide +kernel
theorem add_80 (feat : Features) : Dec feat apc 80 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 3] 5) :=
  Dec.shift (j := 80) (k := 0) (pad_0 feat) wa_80 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_92 : pret <+: apc.drop 92 := by decide +kernel
theorem ret_92 (feat : Features) : Dec feat apc 92 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 92) (k := 0) (pret_0 feat) w_92 (Nat.zero_le _)

theorem fa24 (s : BitVec 64) : s - 8 - 8 - 8 = s - 24 := by bv_omega
theorem fa32 (s : BitVec 64) : s - 24 - 8 = s - 32 := by bv_omega
theorem fa16 (s : BitVec 64) : s - 24 + 8 = s - 16 := by bv_omega
theorem ft24 (s : BitVec 64) (h : 32 ≤ s.toNat) : (s - 24).toNat = s.toNat - 24 := by bv_omega

/-- `mov esi, ebx` at a length below `2 ^ 32`. -/
theorem zx_ofNat (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `ebx` of `rbx` = `n`. -/
theorem sw32 (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The bytes after `push r12; push rbp; push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers after the pushes and `xor ebx, ebx`: `r12` = `this`, `rbp` = `s`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with r12 := g.rdi, rbp := g.rsi, rbx := 0#64, rsp := g.rsp - 8 - 8 - 8 }

/-- `lea edx, [rbx + 1]`. -/
abbrev nb (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rbx + 1#64))

/-- The registers the length loop keeps. -/
def Ks (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- `_chars + _len` of the string at `p` in the bytes `W`: where the copy writes. -/
abbrev dst (W : Addr → Byte) (p : Addr) : Addr := BitVec.setWidth 64 rdd(W, p + 8#64) + rdq(W, p)

/-- The registers at the copy loop: `rsi` = `_chars + _len`, `rdx` = 0. -/
abbrev g64 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rdx := 0#64
    rsi := dst V g.r12 }

/-- The bytes after `_len += n` (`this` = `p`). -/
abbrev V3 (W : Addr → Byte) (p : Addr) (n : Nat) : Addr → Byte :=
  Vst W (p + 8#64) (toBytesLE (rdd(W, p + 8#64) + BitVec.ofNat 32 n) 4)

/-- The copy's facts of the bytes `W` that `Grow` leaves (`this` = `p`, `s` = `q`, `S` the entry's `rsp`): the `n`
bytes of `s` not 0, a 0 after them, all readable; the `n + 1` bytes at `_chars + _len` writable, apart from them, from
the saved `rbx`, `rbp`, `r12` and from the return address. -/
structure Cpy (F : Footprint) (Wl : List Rgn) (W : Addr → Byte) (p q S : Addr) (n : Nat) : Prop where
  nz : ∀ i < n, W (Addr.add q i) ≠ 0
  z : W (Addr.add q n) = 0
  rd : ∀ i, i ≤ n → Foot F.data (Addr.add q i)
  wr : ∀ i, i ≤ n → Foot Wl (Addr.add (dst W p) i)
  sep : ∀ i, i ≤ n → ∀ j, j ≤ n → Addr.add q i ≠ Addr.add (dst W p) j
  f24 : ∀ b < 8, ∀ i < n + 1, Addr.add (S - 24) b ≠ Addr.add (dst W p) i
  f16 : ∀ b < 8, ∀ i < n + 1, Addr.add (S - 16) b ≠ Addr.add (dst W p) i
  f8 : ∀ b < 8, ∀ i < n + 1, Addr.add (S - 8) b ≠ Addr.add (dst W p) i
  f0 : ∀ b < 8, ∀ i < n + 1, Addr.add S b ≠ Addr.add (dst W p) i

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry at an empty string: to 37. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
      (toBytesLE g.rbx 8) g.rsi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 37 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hf hz ⊢
  wpx [W_0, W_21, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, BitVec.xor_self, BitVec.setWidth_zero, hz, gS, V0,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the entry at a string not empty: to 24. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
      (toBytesLE g.rbx 8) g.rsi ≠ 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hf hz ⊢
  wpx [W_0, W_21, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, BitVec.xor_self, BitVec.setWidth_zero, hz, gS, V0,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at a byte not 0: back to 24, `rbx` = `rdx` = `nb`. -/
theorem vc_24n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nb g) i)) (hz : V (g.rbp + nb g) ≠ 0#8) :
    W_24 F Wl (fun j' g' _ V' => j' = 24 ∧ g' = { g with rdx := nb g, rbx := nb g } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_24, o2, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at the 0: to 37, `rbx` = `rdx` = `nb`. -/
theorem vc_24z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nb g) i)) (hz : V (g.rbp + nb g) = 0#8) :
    W_24 F Wl (fun j' g' _ V' => j' = 37 ∧ g' = { g with rdx := nb g, rbx := nb g } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_24, o2, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `mov esi, ebx; mov rdi, r12`, to the `call` at 42. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 42 { g with rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx), rdi := g.r12 } fl V) :
    W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_37, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov esi, [r12 + 8]; xor edx, edx; add rsi, [r12]`, to the loop at 64. -/
theorem vc_47 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i)) (f3 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ fl, Q 64 (g64 g V) fl V) : W_47 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g64, dst] at f2 f3 h ⊢
  wpx [W_47, o4, xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at a byte not 0: the byte stored, `rdx` one on, back to 64. -/
theorem vc_64n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbp + g.rdx) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rsi + g.rdx) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 64 ∧ g'.rdx = g.rdx + 1#64 ∧ g'.rsi = g.rsi ∧ Kp g g' ∧
      V' = Vst V (g.rsi + g.rdx) [V (g.rbp + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_64, o5, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at the 0: the 0 stored, to the `add` at 80. -/
theorem vc_64z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbp + g.rdx) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rsi + g.rdx) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 80 ∧ Kp g g' ∧ V' = Vst V (g.rsi + g.rdx) [V (g.rbp + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_64, o5, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `mov rax, r12; pop rbx; pop rbp; pop r12`, to the `ret` at 92. -/
theorem vc_85 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 92
      { g with
        rax := g.r12
        rbx := rdq(V, g.rsp)
        rbp := rdq(V, g.rsp + 8)
        rsp := g.rsp + 8 + 8 + 8
        r12 := rdq(V, g.rsp + 8 + 8) } fl V) :
    W_85 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 hl3 h ⊢
  wpx [W_85, o6]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The length loop from 24 at the length `j` so far (`j + 1 ≤ n`) of the `n` bytes not 0 and a 0 at `p` (in `W`,
`rbp` = `p`): on to 37 with `rbx` = `n`, the registers `Ks` keeps as at `g₀`. By induction on `n - j - 1`. -/
theorem slen (c : Seg prof F Wl L s₀ o) (hin : CodeIn L apc_at apc) {W : Addr → Byte} {p : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hnz : ∀ i < n, W (p.add i) ≠ 0#8) (hz : W (p.add n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hp : g₀.rbp = p)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = apc_at.add 37 →
      Z.cpu.gpr.rbx = BitVec.ofNat 64 n → Ks g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = apc_at.add 24 → X.cpu.gpr.rbx = BitVec.ofNat 64 j → Ks g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hbx hks
    obtain rfl : n = j + 1 := by omega
    have enx : nb X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Acc.nx_ofNat j hn]
    have ea : X.cpu.gpr.rbp + nb X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nb X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (Nat.le_refl _)
    have hz1 : W (X.cpu.gpr.rbp + nb X.cpu.gpr) = 0#8 := by rw [ea]; exact hz
    refine (c_24 prof).run c hin _ hK hA hrip (vc_24z hf1 hz1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k Y t₁ hKY hAY hrY ?_ (by rw [hgY]; exact hks)
    rw [hgY]; exact enx
  | succ m ih =>
    intro j hj X t hK hA hrip hbx hks
    have enx : nb X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Acc.nx_ofNat j (by omega)]
    have ea : X.cpu.gpr.rbp + nb X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nb X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    refine (c_24 prof).run c hin _ hK hA hrip (vc_24n hf1 (by rw [ea]; exact hnz (j + 1) (by omega))) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY]; exact hks)
    rw [hgY]; exact enx

/-- The copy loop from 64 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`, `rbp` = `p`), the first `j`
stored at `d` (`rsi`): on to the `add` at 80 with all `n + 1` stored and the registers a call keeps as at `g₀`. By
induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L apc_at apc) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j) (hp : g₀.rbp = p)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Acp.Cp W p d (n + 1)) →
      Z.cpu.rip = apc_at.add 80 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Acp.Cp W p d j) →
      X.cpu.rip = apc_at.add 64 → X.cpu.gpr.rdx = BitVec.ofNat 64 j → X.cpu.gpr.rsi = d →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hsi hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = p.add j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.rsi + X.cpu.gpr.rdx = d.add j := by rw [hsi, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbp + X.cpu.gpr.rdx) == 0) = true := by
      rw [es, hb]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    refine (c_64 prof).run c hin _ hK hA hrip (vc_64z hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hsi hkp
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = p.add j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.rsi + X.cpu.gpr.rdx = d.add j := by rw [hsi, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbp + X.cpu.gpr.rdx) == 0) = false := by
      rw [es, hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_64 prof).run c hin _ hK hA hrip (vc_64n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hsi', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    · rw [hgY, hdx', hdx]
      exact (BitVec.ofNat_add j 1).symm
    · rw [hgY, hsi', hsi]

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::operator+= (s)` (`this` = `rdi`, `s` = `rsi`, its `n` bytes not 0 and a 0 after them in the bytes after
the pushes) from its entry, `r12`, `rbp`, `rbx` saved at `rsp - 8`, `rsp - 16`, `rsp - 24`: at `Grow`'s entry with
`rdi` = `this`, `esi` = `n`, the return address `apc_at + 47` at `rsp - 32` (`k1`); from its return (the bytes `W`,
the post `P1`, the copy's facts `Cpy` by `hcp`), the copy of `s` through its 0 to `_chars + _len` (`Acp.Cp`),
`_len += n` (`V3`), and the return address with `rax` = `this`, `rbx`, `rbp`, `r12`, `rsp` restored and `r13`–`r15`
as `Grow` left them (`kr`). -/
theorem apc_ok {P1 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L apc_at apc)
    (hinG : CodeIn L Agr.agr_at Agr.agr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = apc_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {n : Nat} (hn : n < 2 ^ 32)
    (sn : ∀ i < n, V0 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi i) ≠ 0#8)
    (sz : V0 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi n) = 0#8)
    (sf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (apc_at.add 47) 8)) →
      Y.cpu.rip = Agr.agr_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = BitVec.ofNat 64 n → Y.cpu.gpr.rbx = BitVec.ofNat 64 n → Y.cpu.gpr.rbp = X.cpu.gpr.rsi →
      Y.cpu.gpr.r12 = X.cpu.gpr.rdi → Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 →
      Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ (Z : State) (W : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
        Z.cpu.rip = apc_at.add 47 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = BitVec.ofNat 64 n →
        Z.cpu.gpr.rbp = X.cpu.gpr.rsi → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(W, X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx → rdq(W, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z W →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (hcp : ∀ (Z : State) (W : Addr → Byte), P1 Z W → Cpy F Wl W X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rsp n)
    (kr : ∀ (Z : State) (W : Addr → Byte) (Z' : State) (t' : Nat), P1 Z W → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rax = X.cpu.gpr.rdi → Z'.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z'.cpu.gpr.rbp = X.cpu.gpr.rbp → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z'.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z'.cpu.gpr.r13 = Z.cpu.gpr.r13 → Z'.cpu.gpr.r14 = Z.cpu.gpr.r14 → Z'.cpu.gpr.r15 = Z.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have fl8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i) := fun i hi => c.hws _ (fw i hi)
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := pt8 _ hp
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := pt16 _ hp
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := ft24 _ hp
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the frame's bytes as they were after the `add` to `_len`
  have m3 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (V3 W X.cpu.gpr.rdi n) = (byteAddrs x 8).map W := fun W x hx h =>
    Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, t8]; omega) hx (by rw [toBytesLE_length, t8]; omega)
  have hrip' : X.cpu.rip = apc_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    exact sf 0 (Nat.zero_le _)
  -- from 37, the length `n` in `ebx`: the `call` of `Grow`, the copy, the `add`, the epilogue
  have k37 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (V0 V X.cpu.gpr) →
      Z.cpu.rip = apc_at.add 37 → Z.cpu.gpr.rbx = BitVec.ofNat 64 n → Ks (gS X.cpu.gpr) Z.cpu.gpr →
      GoG prof L o gev gP gE Z t' := by
    intro Z t₁ hKZ hAZ hrZ hbZ hks
    obtain ⟨ks_s, ks_p, ks_12, ks_13, ks_14, ks_15⟩ := hks
    have hs37 : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := ks_s.trans (fa24 _)
    refine (c_37 prof).run c hin (fun j' g' _ V' => j' = 42 ∧
        g' = { Z.cpu.gpr with rsi := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx), rdi := Z.cpu.gpr.r12 } ∧
        V' = V0 V X.cpu.gpr) hKZ hAZ hrZ (vc_37 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₂ hKY hAY hrY hgY -
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by
      rw [hgY]
      show Z.cpu.gpr.rsp - 8 = _
      rw [hs37]
      exact fa32 _
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_42 _) hinG (tgt := 0) (Agr.lt_len (by decide))
      tgt_42 (by rw [hY32]; exact hs4) ?_
    rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    refine k1 Y₂ t₃ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY32) (by rw [hg₂, hgY]; exact ks_12)
      ?_ (by rw [hg₂, hgY]; exact hbZ) (by rw [hg₂, hgY]; exact ks_p) (by rw [hg₂, hgY]; exact ks_12)
      (by rw [hg₂, hgY]; exact ks_13) (by rw [hg₂, hgY]; exact ks_14) (by rw [hg₂, hgY]; exact ks_15) ?_
    · rw [hg₂, hgY]
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx) = _
      rw [hbZ]
      exact zx_ofNat n hn
    -- back from `Grow`, at 47: to the copy loop
    intro Z₁ W t'' hKZ₁ hAZ₁ hrZ₁ hzs hzb hzp hz12 hb hbp hr12 hr' hP1
    have cp := hcp Z₁ W hP1
    refine (c_47 prof).run c hin (fun j' g' _ V'' => j' = 64 ∧ g' = g64 Z₁.cpu.gpr W ∧ V'' = W) hKZ₁ hAZ₁ hrZ₁
      (vc_47 (by rw [hz12]; exact fl8) (by rw [hz12]; exact fc) fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
    subst V₂
    have hUsi : U.cpu.gpr.rsi = dst W X.cpu.gpr.rdi := by
      rw [hgU]
      show dst W Z₁.cpu.gpr.r12 = _
      rw [hz12]
    have hUdx : U.cpu.gpr.rdx = BitVec.ofNat 64 0 := by rw [hgU] <;> rfl
    have hUb : U.cpu.gpr.rbx = BitVec.ofNat 64 n := by rw [hgU]; exact hzb
    have hUp : U.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hgU]; exact hzp
    have hUs : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
    have hU12 : U.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgU]; exact hz12
    have hUk : U.cpu.gpr.r13 = Z₁.cpu.gpr.r13 ∧ U.cpu.gpr.r14 = Z₁.cpu.gpr.r14 ∧
        U.cpu.gpr.r15 = Z₁.cpu.gpr.r15 := by
      rw [hgU]
      exact ⟨rfl, rfl, rfl⟩
    -- the copy, to the `add` at 80
    refine loop c hin (W := W) (p := X.cpu.gpr.rsi) (d := dst W X.cpu.gpr.rdi) (n := n) (g₀ := U.cpu.gpr)
      cp.nz cp.z cp.rd cp.wr cp.sep hUp ?_ n 0 (by omega) U t₄ hKU hAU hrU hUdx hUsi (Kp.refl _)
    intro Z₃ t₅ hK₃ hA₃ hr₃ hkp3
    obtain ⟨k3s, k3b, k3p, k312, k313, k314, k315⟩ := hkp3
    have e12 : eaD Z₃ 12 8 = X.cpu.gpr.rdi + 8#64 := by
      show Z₃.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 8 = _
      rw [show Z₃.cpu.gpr.get (regOf 12) = Z₃.cpu.gpr.r12 from rfl, k312, hU12]
    have erv : rv Z₃ 32 3 = BitVec.ofNat 32 n := by
      show BitVec.setWidth 32 (Z₃.cpu.gpr.get (regOf 3)) = _
      rw [show Z₃.cpu.gpr.get (regOf 3) = Z₃.cpu.gpr.rbx from rfl, k3b, hUb]
      exact sw32 n
    refine c.s_add_mr32 hK₃ hA₃ hin (lt_len (by decide)) hr₃ (add_80 _) (by rw [e12]; exact fw) ?_
    rw [e12, erv]
    rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
    replace hA₆ : Agree F Y₆.proc.mm.mem
        (V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n) := hA₆
    have hY6s : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₆, k3s, hUs]
    have hY6r : Y₆.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hg₆, k312, hU12]
    have hb3 : rdq(V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n,
        X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx := by
      rw [m3 _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]
      exact (congrArg (ofBytesLE 64) (Acp.rd_far W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) cp.f24)).trans hb
    have hb2 : rdq(V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n,
        X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp := by
      rw [m3 _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
      exact (congrArg (ofBytesLE 64) (Acp.rd_far W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) cp.f16)).trans hbp
    have hb1 : rdq(V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n,
        X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
      rw [m3 _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
      exact (congrArg (ofBytesLE 64) (Acp.rd_far W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) cp.f8)).trans hr12
    have hb0 : rdq(V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n,
        X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [m3 _ X.cpu.gpr.rsp hp8 (by omega)]
      exact (congrArg (ofBytesLE 64) (Acp.rd_far W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) cp.f0)).trans hr'
    -- the epilogue at 85, then the `ret` at 92
    refine (c_85 prof).run c hin (fun j' g' _ V'' => j' = 92 ∧
        g' = { Y₆.cpu.gpr with
          rax := X.cpu.gpr.rdi
          rbx := X.cpu.gpr.rbx
          rbp := X.cpu.gpr.rbp
          rsp := X.cpu.gpr.rsp
          r12 := X.cpu.gpr.r12 } ∧
        V'' = V3 (Acp.Cp W X.cpu.gpr.rsi (dst W X.cpu.gpr.rdi) (n + 1)) X.cpu.gpr.rdi n)
      hK₆ hA₆ hr₆
      (vc_85 (by rw [hY6s]; exact h24) (by rw [hY6s, fa16]; exact h16) (by rw [hY6s, fa16, peB]; exact h8)
        fun _ => ⟨rfl, by rw [hY6s, hY6r, fa16, peB, peC, hb3, hb2, hb1], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₇ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₄
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_92 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hb0) ?_
    rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    have hY6k : Y₆.cpu.gpr.r13 = Z₁.cpu.gpr.r13 ∧ Y₆.cpu.gpr.r14 = Z₁.cpu.gpr.r14 ∧
        Y₆.cpu.gpr.r15 = Z₁.cpu.gpr.r15 := by
      rw [hg₆, k313, k314, k315]
      exact hUk
    refine kr Z₁ W Z' t₈ hP1 hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hgZ', hgU₂] <;> rfl
    · rw [hgZ', hgU₂] <;> rfl
    · rw [hgZ', hgU₂] <;> rfl
    · rw [hgZ', hsU₂] <;> rfl
    · rw [hgZ', hgU₂] <;> rfl
    · rw [hgZ', hgU₂]
      exact hY6k.1
    · rw [hgZ', hgU₂]
      exact hY6k.2.1
    · rw [hgZ', hgU₂]
      exact hY6k.2.2
  -- the length loop, to 37
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hz0 := sz
    rw [addr_add_zero] at hz0
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧ g' = gS X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_0z hs1 (by rw [pe16]; exact hs2) (by rw [fa24]; exact hs3) hf0 hz0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact k37 Y t₁ hKY hAY hrY (by rw [hgY] <;> rfl) (by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  · have hnz0 := sn 0 hn0
    rw [addr_add_zero] at hnz0
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 24 ∧ g' = gS X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_0n hs1 (by rw [pe16]; exact hs2) (by rw [fa24]; exact hs3) hf0 hnz0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact slen c hin (W := V0 V X.cpu.gpr) (p := X.cpu.gpr.rsi) (n := n) (g₀ := gS X.cpu.gpr) hn sn sz sf rfl k37
      (n - 1) 0 (by omega) Y t₁ hKY hAY hrY (by rw [hgY] <;> rfl) (by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end FV7z.Apc
