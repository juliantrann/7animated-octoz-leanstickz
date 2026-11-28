import FV7z.Aba.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr24
import FV7z.Mys.Lem
import FV7z.Uca.Holds
/-!
# `NCOM::AllocBstrFromAscii` (PLAN.md §M, M1)

7-Zip 26.06's `BSTR AllocBstrFromAscii (const char *s)` at `0x456e50` in `7zzs` (`CPP/Windows/PropVariant.cpp`;
`objdump -d`), `s` = `rdi`: `endbr64; test rdi, rdi; je 96` (96: `xor eax, eax`, the `ret` at 98); at 9
`push rbp; push rbx; mov rbx, rdi; sub rsp, 8`; at 18 the `call` of `strlen` (its PLT entry `0x401108`); at 23
`xor edi, edi; mov rsi, rax; mov ebp, eax` (`len` = `ebp`); at 30 the `call` of `SysAllocStringLen (NULL, len)`
(`0x5a0010`); at 35 `test rax, rax; je 80` (80: `add rsp, 8; xor eax, eax; pop rbx; pop rbp`, the `ret` at 88); at 40
`xor edx, edx`; the copy loop at 48 (`mov ecx, edx; add edx, 1; movzx esi, byte [rbx + rcx]; mov [rax + rcx * 4], esi;
cmp ebp, edx; jae 48`: `p[i] = s[i]` for `i <= len`); at 64 `add rsp, 8; pop rbx; pop rbp`, the `ret` at 70.

Design as `FV7z/Gcf/Holds.lean` (the 24-byte frame of `FV7z/Lemmas/Fr24.lean`, `rbp` at `s - 8`, `rbx` at `s - 16`)
with the copy loop of `FV7z/Ape/Holds.lean`: the two callees are hypotheses, each a continuation at its entry given
the run from its return (`rsp` 24 below the entry's, `rbx` = `s`, the saved `rbp`, `rbx` and the return address left
as they were, the callee's own post `P1`, `P2`): `k1` at `strlen` (for `s` not NULL), `k2` at `SysAllocStringLen`
(`rbp` = `len` zero-extended). Of the bytes `W₂` that `SysAllocStringLen` leaves and its result `d` not NULL, the
caller gives the copy's facts (`hcp`, `Cpy`). The bytes copied, each widened to 4, are `Uca.Cw`, as in
`UString (const char *)`. `kz`, `kn`, `kr`: the return address for `s` NULL, for `d` NULL, and after the copy.

- `V0`, `gE`, `g30`: the bytes and the registers at the `call`s; `K4`: `r12`–`r15` kept; `Cpy`: the copy's facts.
- `vc_0`, `vc_23`, `vc_35`, `vc_48n`, `vc_48z`: the verification conditions of the pieces; `rdCw`: 8 bytes apart from
  the copy; `loop`: the copy by induction.
- `aba_ok`: from the entry to the return address with `rax` = 0 or `d`, `rbx`, `rbp`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24 FV7z.Mys
namespace FV7z.Aba
open FV7z.Uca (Cw Cw_out)

/-- The `call` to `strlen` (its PLT entry). -/
def pc1 : List Byte := [0xe8, 0xa1, 0xa2, 0xfa, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709200033] 5) := by dec_rfl
theorem wc_18 : pc1 <+: aba.drop 18 := by decide +kernel
theorem call_18 (feat : Features) : Dec feat aba 18 (FV7z.mk .call 64 [.rel 18446744073709200033] 5) :=
  Dec.shift (j := 18) (k := 0) (pc1_0 feat) wc_18 (Nat.zero_le _)

/-- The `call` to `SysAllocStringLen`. -/
def pc2 : List Byte := [0xe8, 0x9d, 0x91, 0x14, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 1347997] 5) := by dec_rfl
theorem wc_30 : pc2 <+: aba.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat aba 30 (FV7z.mk .call 64 [.rel 1347997] 5) :=
  Dec.shift (j := 30) (k := 0) (pc2_0 feat) wc_30 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_70 : pret <+: aba.drop 70 := by decide +kernel
theorem ret_70 (feat : Features) : Dec feat aba 70 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 70) (k := 0) (pret_0 feat) w_70 (Nat.zero_le _)
theorem w_88 : pret <+: aba.drop 88 := by decide +kernel
theorem ret_88 (feat : Features) : Dec feat aba 88 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 88) (k := 0) (pret_0 feat) w_88 (Nat.zero_le _)
theorem w_98 : pret <+: aba.drop 98 := by decide +kernel
theorem ret_98 (feat : Features) : Dec feat aba 98 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 98) (k := 0) (pret_0 feat) w_98 (Nat.zero_le _)

/-- The bytes after `push rbp; push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `rbx` = `s`, `rsp` 24 down (`rdi` = `s` as at the entry). -/
abbrev gE (g : Gprs) : Gprs := { g with rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8#64 }

/-- The registers at the second `call`: `rdi` = 0, `rsi` = `strlen (s)`, `ebp` = its low 32 bits. -/
abbrev g30 (g : Gprs) : Gprs :=
  { g with rsi := g.rax, rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax), rdi := 0#64 }

/-- `r12`–`r15` as in `g`. -/
def K4 (g g' : Gprs) : Prop := g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The copy's facts (`s` the string, `d` the result of `SysAllocStringLen`, `S` the entry's `rsp`, `n` = `len`):
`n + 1` short of `2 ^ 32` (the loop's index in 32 bits), the `n + 1` bytes at `s` readable, the `4 (n + 1)` at `d`
writable and apart from the saved `rbx`, `rbp` and the return address. -/
structure Cpy (F : Footprint) (Wl : List Rgn) (s d S : Addr) (n : Nat) : Prop where
  lt : n + 1 < 2 ^ 32
  rd : ∀ i ≤ n, Foot F.data (Addr.add s i)
  wr : ∀ i < 4 * (n + 1), Foot Wl (Addr.add d i)
  f16 : ∀ b < 8, ∀ i < 4 * (n + 1), Addr.add (S - 16) b ≠ Addr.add d i
  f8 : ∀ b < 8, ∀ i < 4 * (n + 1), Addr.add (S - 8) b ≠ Addr.add d i
  f0 : ∀ b < 8, ∀ i < 4 * (n + 1), Addr.add S b ≠ Addr.add d i

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

/-- 8 bytes apart from the first `4 k` at `d`: as before the copy. -/
theorem rdCw (W : Addr → Byte) (s d : Addr) {k : Nat} {a : Addr}
    (h : ∀ b < 8, ∀ i < 4 * k, Addr.add a b ≠ Addr.add d i) : rdq(Cw W s d k, a) = rdq(W, a) := by
  congr 1
  refine List.map_congr_left fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := mem_byteAddrs.1 hy
  exact Cw_out W s d k _ fun i hi => h b hb i hi

variable {F : Footprint} {Wl : List Rgn}

/-- `test rdi, rdi; je 96`: for `s` NULL `xor eax, eax` to the `ret` at 98; else `push rbp; push rbx; mov rbx, rdi;
sub rsp, 8` to the `call` at 18. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h98 : g.rdi = 0 → ∀ fl, Q 98 { g with rax := 0#64 } fl V)
    (h18 : g.rdi ≠ 0 → ∀ fl, Q 18 (gE g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gE, V0] at hs1 hs2 h98 h18 ⊢
  by_cases h0 : rdi = 0
  · have hz : (rdi == 0) = true := beq_iff_eq.2 h0
    wpx [W_0, W_96, W_9, o0, o1, o8, hz, xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h98 h0 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hz : (rdi == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_0, W_96, W_9, o0, o1, o8, hz, xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h18 h0 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor edi, edi; mov rsi, rax; mov ebp, eax`, to the `call` at 30. -/
theorem vc_23 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 30 (g30 g) fl V) :
    W_23 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g30] at h ⊢
  wpx [W_23, o2, xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `test rax, rax; je 80`: for NULL `add rsp, 8; xor eax, eax; pop rbx; pop rbp` to the `ret` at 88; else
`xor edx, edx` to the loop at 48. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h88 : g.rax = 0 → ∀ fl, Q 88
      { g with
        rax := 0#64
        rbx := rdq(V, g.rsp + 8#64)
        rbp := rdq(V, g.rsp + 8#64 + 8)
        rsp := g.rsp + 8#64 + 8 + 8 } fl V)
    (h48 : g.rax ≠ 0 → ∀ fl, Q 48 { g with rdx := 0#64 } fl V) :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h88 h48 ⊢
  by_cases h0 : rax = 0
  · have hz : (rax == 0) = true := beq_iff_eq.2 h0
    wpx [W_35, W_80, W_40, o3, o7, o4, hz, xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h88 h0 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hz : (rax == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_35, W_80, W_40, o3, o7, o4, hz, xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h48 h0 _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- The copy loop at an index `i = edx` short of `len = ebp`: `s[i]` stored as 4 bytes at `d + 4 i`, `edx` one on,
back to 48. -/
theorem vc_48n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : ¬ (BitVec.setWidth 32 g.rbp).toNat < (BitVec.setWidth 32 g.rdx + 1#32).toNat)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rax + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) * 4#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 48 ∧ g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx + 1#32) ∧
      g'.rax = g.rax ∧ Kp g g' ∧
      V' = Vst V (g.rax + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) * 4#64)
        (toBytesLE (BitVec.setWidth 32 (V (g.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)))) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hf hw ⊢
  have hd := decide_eq_false hc
  wpx [W_48, W_64, o5, o6, Tun.rd1, hd, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

set_option maxHeartbeats 1000000 in
/-- The copy loop at the index `len`: `s[len]` stored, then `add rsp, 8; pop rbx; pop rbp` to the `ret` at 70. -/
theorem vc_48z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : (BitVec.setWidth 32 g.rbp).toNat < (BitVec.setWidth 32 g.rdx + 1#32).toNat)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rax + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) * 4#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 70 ∧
      V' = Vst V (g.rax + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) * 4#64)
        (toBytesLE (BitVec.setWidth 32 (V (g.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)))) 4) ∧
      g'.rax = g.rax ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 ∧ g'.rbx = rdq(V', g.rsp + 8#64) ∧
      g'.rbp = rdq(V', g.rsp + 8#64 + 8) ∧ K4 g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hf hw hl1 hl2 ⊢
  have hd := decide_eq_true hc
  wpx [W_48, W_64, o5, o6, Tun.rd1, hd, K4, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}

/-- The copy loop from 48 at the index `j` (`j ≤ n`, `edx` = `j`) of the `n + 1` bytes at `s` (`rbx`) to `d` (`rax`),
`ebp` = `n`: on to the `ret` at 70 with all `n + 1` stored (`Cw`), `rbx`, `rbp` popped and `rsp`, `r12`–`r15` as
at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aba_at aba) {W : Addr → Byte} {s d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n + 1 < 2 ^ 32) (hf : ∀ i ≤ n, Foot F.data (Addr.add s i))
    (hw : ∀ i < 4 * (n + 1), Foot Wl (Addr.add d i)) (hb : g₀.rbx = s)
    (hp : (BitVec.setWidth 32 g₀.rbp).toNat = n)
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8) i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cw W s d (n + 1)) →
      Z.cpu.rip = aba_at.add 70 → Z.cpu.gpr.rax = d → Z.cpu.gpr.rsp = g₀.rsp + 8#64 + 8 + 8 →
      Z.cpu.gpr.rbx = rdq(Cw W s d (n + 1), g₀.rsp + 8#64) →
      Z.cpu.gpr.rbp = rdq(Cw W s d (n + 1), g₀.rsp + 8#64 + 8) → K4 g₀ Z.cpu.gpr →
      GoG prof L o gev gP gE' Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Cw W s d j) → X.cpu.rip = aba_at.add 48 → X.cpu.gpr.rdx = BitVec.ofNat 64 j →
      X.cpu.gpr.rax = d → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE' X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hax hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) = Addr.add s j := by
      rw [hkp.2.1, hb, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have ed : X.cpu.gpr.rax + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) * 4#64 = Addr.add d (4 * j) := by
      rw [hax, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have hc : (BitVec.setWidth 32 X.cpu.gpr.rbp).toNat < (BitVec.setWidth 32 X.cpu.gpr.rdx + 1#32).toNat := by
      rw [hkp.2.2.1, hp, hdx]
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx))
        i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rax + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) *
        4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_48 prof).run c hin _ hK hA hrip
      (vc_48z hc hf1 hw4 (by rw [hkp.1]; exact hl1) (by rw [hkp.1]; exact hl2)) ?_
    rintro j' g fl V₁ ⟨rfl, hV, hax', hsp', hbx', hbp', hk4⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    refine k Y t₁ hKY hAY hrY (by rw [hgY, hax', hax]) (by rw [hgY, hsp', hkp.1]) (by rw [hgY, hbx', hkp.1] <;> rfl)
      (by rw [hgY, hbp', hkp.1] <;> rfl) ⟨?_, ?_, ?_, ?_⟩
    · rw [hgY, hk4.1, hkp.2.2.2.1]
    · rw [hgY, hk4.2.1, hkp.2.2.2.2.1]
    · rw [hgY, hk4.2.2.1, hkp.2.2.2.2.2.1]
    · rw [hgY, hk4.2.2.2, hkp.2.2.2.2.2.2]
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hax hkp
    have es : X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) = Addr.add s j := by
      rw [hkp.2.1, hb, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have ed : X.cpu.gpr.rax + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) * 4#64 = Addr.add d (4 * j) := by
      rw [hax, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have hc : ¬ (BitVec.setWidth 32 X.cpu.gpr.rbp).toNat < (BitVec.setWidth 32 X.cpu.gpr.rdx + 1#32).toNat := by
      rw [hkp.2.2.1, hp, hdx]
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      omega
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx))
        i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rax + BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) *
        4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_48 prof).run c hin _ hK hA hrip (vc_48n hc hf1 hw4) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hax', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hax', hax]) (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hdx', hdx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
    omega

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- `AllocBstrFromAscii (s)` (`s` = `rdi`) from its entry: for `s` NULL at the return address with `rax` = 0 (`kz`);
else, `rbp` and `rbx` saved at `rsp - 8` and `rsp - 16`, at `strlen` (`0x401108`) with the registers `gE`, the return
address `aba_at + 23` at `rsp - 32` (`k1`); from its return (`rax` = `len`, the post `P1`), at `SysAllocStringLen`
(`0x5a0010`) with `g30` (`k2`); from its return (the bytes `W₂`, `rax` = `d`, the post `P2`), for `d` NULL at the
return address with `rax` = 0 (`kn`); else, with the copy's facts (`hcp`), the `len + 1` bytes at `s` widened to 4
each at `d` (`Cw`) and the return address with `rax` = `d` (`kr`); `rbx`, `rbp`, `rsp` restored. -/
theorem aba_ok {P1 : State → (Addr → Byte) → Prop} {P2 : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aba_at aba)
    {code1 : List Byte} (hin1 : CodeIn L 0x401108#64 code1) (hc1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L 0x5a0010#64 code2) (hc2 : 0 < code2.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aba_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : X.cpu.gpr.rdi = 0 → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE' Z' t')
    (k1 : X.cpu.gpr.rdi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (aba_at.add 23) 8)) →
      Y.cpu.rip = 0x401108#64 → Y.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (W : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
        Z.cpu.rip = aba_at.add 23 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(W, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z W →
        GoG prof L o gev gP gE' Z t'') →
      GoG prof L o gev gP gE' Y t')
    (k2 : ∀ (Z : State) (W : Addr → Byte), P1 Z W →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W (X.cpu.gpr.rsp - 32) (toBytesLE (aba_at.add 35) 8)) →
      Y.cpu.rip = 0x5a0010#64 → Y.cpu.gpr = (g30 Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (W₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem W₂ →
        Z₂.cpu.rip = aba_at.add 35 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) →
        rdq(W₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(W₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(W₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z Z₂ W₂ →
        GoG prof L o gev gP gE' Z₂ t'') →
      GoG prof L o gev gP gE' Y t')
    (kn : ∀ (Z Z₂ : State) (W₂ : Addr → Byte), P2 Z Z₂ W₂ → Z₂.cpu.gpr.rax = 0 →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W₂ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := 0#64
        rbx := X.cpu.gpr.rbx
        rbp := X.cpu.gpr.rbp
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE' Z' t')
    (hcp : ∀ (Z Z₂ : State) (W₂ : Addr → Byte), P2 Z Z₂ W₂ → Z₂.cpu.gpr.rax ≠ 0 →
      Cpy F Wl X.cpu.gpr.rdi Z₂.cpu.gpr.rax X.cpu.gpr.rsp (BitVec.setWidth 32 Z.cpu.gpr.rax).toNat)
    (kr : ∀ (Z Z₂ : State) (W₂ : Addr → Byte), P2 Z Z₂ W₂ → Z₂.cpu.gpr.rax ≠ 0 →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Cw W₂ X.cpu.gpr.rdi Z₂.cpu.gpr.rax ((BitVec.setWidth 32 Z.cpu.gpr.rax).toNat + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rax = Z₂.cpu.gpr.rax → Z'.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z'.cpu.gpr.rbp = X.cpu.gpr.rbp → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → K4 Z₂.cpu.gpr Z'.cpu.gpr →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have hrip' : X.cpu.rip = aba_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the test of `s`: the `ret` at 98, or the prologue to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (X.cpu.gpr.rdi = 0 ∧ j' = 98 ∧ g' = { X.cpu.gpr with rax := 0#64 } ∧ V' = V) ∨
      (X.cpu.gpr.rdi ≠ 0 ∧ j' = 18 ∧ g' = gE X.cpu.gpr ∧ V' = V0 V X.cpu.gpr)) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) (fun h0 _ => Or.inl ⟨h0, rfl, rfl, rfl⟩)
      (fun h0 _ => Or.inr ⟨h0, rfl, rfl, rfl⟩)) ?_
  rintro j' g fl V₁ hpost Y t₁ hKY hAY hrY hgY -
  rcases hpost with ⟨h0, rfl, hg, hV₁⟩ | ⟨h0, rfl, hg, hV₁⟩
  · -- `s` NULL: the `ret` at 98
    subst hg
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_98 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kz h0 Z' t₂ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgY]
    try rfl
  -- the `call` of `strlen`
  subst hg
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, pe32]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_18 _) hin1 hc1 (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
  refine k1 h0 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `strlen`, at 23: to the `call` of `SysAllocStringLen`
  intro Z W t₃ hKZ hAZ hrZ hzs hzb hb hp hr' hP1
  refine (c_23 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = g30 Z.cpu.gpr ∧ V' = W) hKZ hAZ hrZ
    (vc_23 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hg, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst hg
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
  have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsU, peD]
  have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hU32]; exact hs4
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_30 _) hin2 hc2 (by decide) hst2 ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hU32] at hA₃
  have hg₃' : Y₃.cpu.gpr = (g30 Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₃, hU32, hgU]
  refine k2 Z W hP1 Y₃ t₅ hK₃ hA₃ hr₃ hg₃' ?_
  -- back from `SysAllocStringLen`, at 35: NULL to the `ret` at 88, else to the loop
  intro Z₂ W₂ t₆ hKZ₂ hAZ₂ hrZ₂ hz2s hz2b hz2p hb2 hp2 hr2 hP2
  refine (c_35 prof).run c hin (fun j' g' _ V' => V' = W₂ ∧
      ((Z₂.cpu.gpr.rax = 0 ∧ j' = 88 ∧
        g' = { Z₂.cpu.gpr with
          rax := 0#64
          rbx := X.cpu.gpr.rbx
          rbp := X.cpu.gpr.rbp
          rsp := X.cpu.gpr.rsp }) ∨
        (Z₂.cpu.gpr.rax ≠ 0 ∧ j' = 48 ∧ g' = { Z₂.cpu.gpr with rdx := 0#64 }))) hKZ₂ hAZ₂ hrZ₂
    (vc_35 (by rw [hz2s, peA']; exact h16) (by rw [hz2s, peA', peB]; exact h8)
      (fun h0 _ => ⟨rfl, Or.inl ⟨h0, rfl, by rw [hz2s, peA', peB, peC, hb2, hp2]⟩⟩)
      (fun h0 _ => ⟨rfl, Or.inr ⟨h0, rfl, rfl⟩⟩)) ?_
  rintro j' g fl V₃ ⟨hV₃, hpost⟩ U₁ t₇ hKU₁ hAU₁ hrU₁ hgU₁ -
  subst V₃
  rcases hpost with ⟨h0', rfl, hg⟩ | ⟨h0', rfl, hg⟩
  · -- `d` NULL: the `ret` at 88
    subst hg
    have hsU₁ : U₁.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₁]
    refine c.s_ret hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (ret_88 _) (by rw [hsU₁]; exact hl) hin₂ h₂
      (by rw [hsU₁]; exact hr2) ?_
    rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kn Z Z₂ W₂ hP2 h0' Z' t₈ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₁]
    try rfl
  -- the copy, to the `ret` at 70
  subst hg
  obtain ⟨hn, hrd, hwr, f16, f8, f0⟩ := hcp Z Z₂ W₂ hP2 h0'
  have hUs : U₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU₁]; exact hz2s
  have hUp : (BitVec.setWidth 32 U₁.cpu.gpr.rbp).toNat = (BitVec.setWidth 32 Z.cpu.gpr.rax).toNat := by
    rw [hgU₁]
    show (BitVec.setWidth 32 Z₂.cpu.gpr.rbp).toNat = _
    rw [hz2p, sw_64_32]
  refine loop c hin (W := W₂) (s := X.cpu.gpr.rdi) (d := Z₂.cpu.gpr.rax)
    (n := (BitVec.setWidth 32 Z.cpu.gpr.rax).toNat) (g₀ := U₁.cpu.gpr) hn hrd hwr (by rw [hgU₁]; exact hz2b) hUp
    (by rw [hUs, peA']; exact h16) (by rw [hUs, peA', peB]; exact h8) ?_ (BitVec.setWidth 32 Z.cpu.gpr.rax).toNat 0
    (by omega) U₁ t₇ hKU₁ hAU₁ hrU₁ (by rw [hgU₁] <;> rfl) (by rw [hgU₁] <;> rfl) (Kp.refl _)
  intro Z₃ t₈ hK₃ hA₃ hr₃ hax3 hsp3 hbx3 hbp3 hk43
  have hsp3' : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hsp3, hUs, peA', peB, peC]
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_70 _) (by rw [hsp3']; exact hl) hin₂ h₂
    (by rw [hsp3']; exact (rdCw _ _ _ f0).trans hr2) ?_
  rintro Z' t₉ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  rw [hgU₁] at hk43
  refine kr Z Z₂ W₂ hP2 h0' Z' t₉ hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩
  · rw [hgZ']; exact hax3
  · rw [hgZ']
    exact hbx3.trans (by rw [hUs, peA']; exact (rdCw _ _ _ f16).trans hb2)
  · rw [hgZ']
    exact hbp3.trans (by rw [hUs, peA', peB]; exact (rdCw _ _ _ f8).trans hp2)
  · rw [hgZ']
    show Z₃.cpu.gpr.rsp + 8 = _
    rw [hsp3']
  · rw [hgZ']; exact hk43.1
  · rw [hgZ']; exact hk43.2.1
  · rw [hgZ']; exact hk43.2.2.1
  · rw [hgZ']; exact hk43.2.2.2

end FV7z.Aba
