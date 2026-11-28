import FV7z.Sns.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Tcg.Ok
/-!
# `CDirPathSortPair::SetNumSlashes (s)` (PLAN.md §M, M1)

7-Zip 26.06's `CDirPathSortPair::SetNumSlashes (const FChar *s)` at `0x5ad550` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`): `Len` (the `unsigned` at `this`) set to the number of `/` among
the bytes of `s` before its 0 (`for (unsigned numSlashes = 0;;) { FChar c = *s++; if (c == 0) { Len = numSlashes;
return; } if (IS_PATH_SEPAR (c)) numSlashes++; }`).

The loop's head is the cut point 24 (`cmp al, 0x2f`). Its invariant, for `s` (`rsi` at the entry) `n` bytes not 0 and
a 0, at the index `j < n`: `al = s[j]`, `rdx = s + j + 1`, `ecx = cnt V s j` (the `/` among `s[0..j)`), `rdi` the
entry's, the registers a call keeps as at the entry. Each turn adds `s[j] = '/'` to `ecx` (`sete al; movzx eax, al;
add ecx, eax`), loads `s[j + 1]` and goes back to 24 if it is not 0, else to 46 (`mov [rdi], ecx`) with
`ecx = cnt V s n`.

- `cnt`: the `/` among the first `k` bytes.
- `vc_0z`, `vc_0n`: from the entry, `s[0] = 0` (to 46) or not (to 24); `vc_24sz`, `vc_24sn`, `vc_24pz`, `vc_24pn`:
  the loop's turn, `s[j]` a `/` or not, `s[j + 1]` 0 (to 46) or not (back to 24); `vc_46`: the store.
- `loop`: from 24, by induction on the bytes left; `sns_ok`: from the entry to the return address, `Len` stored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Sns

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: sns.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat sns 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)

/-- The `/` among the first `k` bytes at `s`. -/
def cnt (V : Addr → Byte) (s : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt V s k + if V (s.add k) = 47#8 then 1 else 0

theorem cnt_s {V : Addr → Byte} {s : Addr} {j : Nat} (h : V (s.add j) = 47#8) : cnt V s (j + 1) = cnt V s j + 1 := by
  simp [cnt, h]

theorem cnt_n {V : Addr → Byte} {s : Addr} {j : Nat} (h : ¬ V (s.add j) = 47#8) : cnt V s (j + 1) = cnt V s j := by
  simp [cnt, h]

/-- `movzx eax, byte [rdx - 1]` after `add rdx, 1`. -/
theorem a1 (x : BitVec 64) : x + 1#64 + 18446744073709551615#64 = x := by bv_omega

/-- A low byte made of a `wrLo` (`setcc`), bit by bit: equal to a literal (as in `FV7z/Dde/Holds.lean`). -/
local macro "lob" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

/-- `sete al` then `movzx eax, al`: the low byte. -/
theorem lo1 (x : BitVec 64) : BitVec.setWidth 8 (x &&& 18446744073709551360#64 ||| 1#64) = 1#8 := by
  first | simp | lob
theorem lo0 (x : BitVec 64) : BitVec.setWidth 8 (x &&& 18446744073709551360#64) = 0#8 := by
  first | simp | lob

/-- The registers after a turn of the loop from `g`: `al` the next byte, `ecx` = `e`, `rdx` one on. -/
abbrev Nx (V : Addr → Byte) (g g' : Gprs) (e : BitVec 32) : Prop :=
  ∃ a c, g' = { g with rax := a, rcx := c, rdx := g.rdx + 1#64 } ∧ a.setWidth 8 = V g.rdx ∧ c.setWidth 32 = e

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a turn's condition. -/
local macro "fin24" : tactic => `(tactic| repeat' (first
  | assumption
  | exact ⟨_, _, rfl, sw8b _, sw32 _⟩
  | exact ⟨_, _, rfl, sw8b _, rfl⟩
  | exact ⟨_, _, rfl, by simp [sw8b, sw8a], by simp [sw32, lo1, lo0]⟩
  | rfl
  | (intro h; exact absurd h (by decide))
  | apply And.intro
  | intro _))

/-- From the entry, `s[0] = 0`: to 46 with `ecx` 0. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V g.rsi == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 46 ∧
      (∃ a c, g' = { g with rax := a, rcx := c, rdx := g.rsi + 1#64 } ∧ c.setWidth 32 = 0#32) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf ⊢
  wpx [W_0, W_17, o0, o1, Tun.rd1, hz, sw8a, sw8b, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | assumption
    | exact ⟨_, _, rfl, by first | rfl | decide | simp⟩
    | rfl
    | apply And.intro
    | intro _)

/-- From the entry, `s[0] ≠ 0`: to 24 with `al = s[0]`, `rdx = s + 1`, `ecx` 0. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V g.rsi == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧
      (∃ a c, g' = { g with rax := a, rcx := c, rdx := g.rsi + 1#64 } ∧ a.setWidth 8 = V g.rsi ∧
        c.setWidth 32 = 0#32) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf ⊢
  wpx [W_0, W_17, o0, o1, Tun.rd1, hz, sw8a, sw8b, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | assumption
    | exact ⟨_, _, rfl, sw8b _, by first | rfl | decide | simp⟩
    | exact ⟨_, _, rfl, by simp [sw8b, sw8a], by first | rfl | decide | simp⟩
    | rfl
    | apply And.intro
    | intro _)

/-- A turn, `s[j]` a `/`, `s[j + 1]` 0: to 46 with `ecx` one more. -/
theorem vc_24sz {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : BitVec.setWidth 8 g.rax = 47#8)
    (hz : (V g.rdx == 0) = true) (hf : ∀ i < 1, Foot F.data (Addr.add g.rdx i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 46 ∧ Nx V g g' (BitVec.setWidth 32 g.rcx + 1#32) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hz hf ⊢
  have d := decide_eq_true hs
  wpx [W_24, o2, Op.setcc, Op.zxr, Tun.rd1, a1, lo1, lo0, d, hz, sw8a, sw8b, BitVec.and_self, Nat.reduceSub,
    BitVec.reduceNot, BitVec.reduceSetWidth, BitVec.shiftLeft_zero, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.or_zero, BitVec.setWidth_or, BitVec.setWidth_and, BitVec.and_zero, BitVec.zero_or, decide_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals fin24

/-- A turn, `s[j]` a `/`, `s[j + 1]` not 0: back to 24 with `ecx` one more. -/
theorem vc_24sn {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : BitVec.setWidth 8 g.rax = 47#8)
    (hz : (V g.rdx == 0) = false) (hf : ∀ i < 1, Foot F.data (Addr.add g.rdx i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 24 ∧ Nx V g g' (BitVec.setWidth 32 g.rcx + 1#32) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hz hf ⊢
  have d := decide_eq_true hs
  wpx [W_24, o2, Op.setcc, Op.zxr, Tun.rd1, a1, lo1, lo0, d, hz, sw8a, sw8b, BitVec.and_self, Nat.reduceSub,
    BitVec.reduceNot, BitVec.reduceSetWidth, BitVec.shiftLeft_zero, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.or_zero, BitVec.setWidth_or, BitVec.setWidth_and, BitVec.and_zero, BitVec.zero_or, decide_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals fin24

/-- A turn, `s[j]` not a `/`, `s[j + 1]` 0: to 46 with `ecx` as it was. -/
theorem vc_24pz {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : ¬ BitVec.setWidth 8 g.rax = 47#8)
    (hz : (V g.rdx == 0) = true) (hf : ∀ i < 1, Foot F.data (Addr.add g.rdx i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 46 ∧ Nx V g g' (BitVec.setWidth 32 g.rcx) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hz hf ⊢
  have d := decide_eq_false hs
  wpx [W_24, o2, Op.setcc, Op.zxr, Tun.rd1, a1, lo1, lo0, d, hz, sw8a, sw8b, BitVec.and_self, Nat.reduceSub,
    BitVec.reduceNot, BitVec.reduceSetWidth, BitVec.shiftLeft_zero, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.or_zero, BitVec.setWidth_or, BitVec.setWidth_and, BitVec.and_zero, BitVec.zero_or, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals fin24

/-- A turn, `s[j]` not a `/`, `s[j + 1]` not 0: back to 24 with `ecx` as it was. -/
theorem vc_24pn {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : ¬ BitVec.setWidth 8 g.rax = 47#8)
    (hz : (V g.rdx == 0) = false) (hf : ∀ i < 1, Foot F.data (Addr.add g.rdx i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 24 ∧ Nx V g g' (BitVec.setWidth 32 g.rcx) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hz hf ⊢
  have d := decide_eq_false hs
  wpx [W_24, o2, Op.setcc, Op.zxr, Tun.rd1, a1, lo1, lo0, d, hz, sw8a, sw8b, BitVec.and_self, Nat.reduceSub,
    BitVec.reduceNot, BitVec.reduceSetWidth, BitVec.shiftLeft_zero, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.or_zero, BitVec.setWidth_or, BitVec.setWidth_and, BitVec.and_zero, BitVec.zero_or, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals fin24

/-- `mov [rdi], ecx`: to the `ret` at 48. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 4, Foot Wl (Addr.add g.rdi i)) :
    W_46 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = g ∧ V' = Vst V g.rdi (toBytesLE (BitVec.setWidth 32 g.rcx) 4))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw ⊢
  wpx [W_46, o3]
  all_goals repeat' (first | assumption | rfl | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 24 at the index `j < n` of the `n` bytes not 0 and a 0 at `s`: `al = s[j]`, `rdx = s + j + 1`,
`ecx` the `/` before `j`, `rdi` and the registers a call keeps as at `g₀`: on to 46 with `ecx` the `/` among the `n`
bytes. By induction on `n - j - 1`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sns_at sns) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hnz : ∀ i < n, V (s.add i) ≠ 0) (hz : V (s.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (s.add i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = sns_at.add 46 →
      Kp g₀ Z.cpu.gpr → Z.cpu.gpr.rdi = g₀.rdi →
      BitVec.setWidth 32 Z.cpu.gpr.rcx = BitVec.ofNat 32 (cnt V s n) →
      GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = sns_at.add 24 → BitVec.setWidth 8 X.cpu.gpr.rax = V (s.add j) → X.cpu.gpr.rdx = s.add (j + 1) →
      BitVec.setWidth 32 X.cpu.gpr.rcx = BitVec.ofNat 32 (cnt V s j) → X.cpu.gpr.rdi = g₀.rdi →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hdx hcx hdi hkp
    have hn : j + 1 = n := by omega
    have hz' : (V X.cpu.gpr.rdx == 0) = true := by rw [hdx, hn]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdx i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hdx]
      exact hf (j + 1) (by omega)
    by_cases he : V (s.add j) = 47#8
    · refine (c_24 prof).run c hin _ hK hA hrip (vc_24sz (by rw [hax]; exact he) hz' hf1) ?_
      rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, ha, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine k Y t₁ hKY hAY hrY (hkp.trans (kp_w hgY)) (by rw [hgY]; exact hdi) ?_
      rw [hgY]
      show BitVec.setWidth 32 cx = _
      rw [hc, hcx, ← hn, cnt_s he, BitVec.ofNat_add]
    · refine (c_24 prof).run c hin _ hK hA hrip (vc_24pz (by rw [hax]; exact he) hz' hf1) ?_
      rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, ha, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine k Y t₁ hKY hAY hrY (hkp.trans (kp_w hgY)) (by rw [hgY]; exact hdi) ?_
      rw [hgY]
      show BitVec.setWidth 32 cx = _
      rw [hc, hcx, ← hn, cnt_n he]
  | succ m ih =>
    intro j hj X t hK hA hrip hax hdx hcx hdi hkp
    have hz' : (V X.cpu.gpr.rdx == 0) = false := by
      rw [hdx]
      exact beq_eq_false_iff_ne.2 (hnz (j + 1) (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdx i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hdx]
      exact hf (j + 1) (by omega)
    have ea : X.cpu.gpr.rdx + 1#64 = s.add (j + 1 + 1) := by rw [hdx]; exact ptr_step s (j + 1) 1
    by_cases he : V (s.add j) = 47#8
    · refine (c_24 prof).run c hin _ hK hA hrip (vc_24sn (by rw [hax]; exact he) hz' hf1) ?_
      rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, ha, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ ?_ ?_ (by rw [hgY]; exact hdi) (hkp.trans (kp_w hgY))
      · rw [hgY]
        show BitVec.setWidth 8 a = _
        rw [ha, hdx]
      · rw [hgY]
        exact ea
      · rw [hgY]
        show BitVec.setWidth 32 cx = _
        rw [hc, hcx, cnt_s he, BitVec.ofNat_add]
    · refine (c_24 prof).run c hin _ hK hA hrip (vc_24pn (by rw [hax]; exact he) hz' hf1) ?_
      rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, ha, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ ?_ ?_ (by rw [hgY]; exact hdi) (hkp.trans (kp_w hgY))
      · rw [hgY]
        show BitVec.setWidth 8 a = _
        rw [ha, hdx]
      · rw [hgY]
        exact ea
      · rw [hgY]
        show BitVec.setWidth 32 cx = _
        rw [hc, hcx, cnt_n he]

/-- `CDirPathSortPair::SetNumSlashes (s)` from its entry, `this` in `rdi` (its 4 bytes in what the run may store
into, apart from the return address), `s` (`rsi`) `n` bytes not 0 and a 0, those bytes data of the footprint: at the
return address with `Len` (the 4 bytes at `this`) the number of `/` among the `n` bytes (`cnt`), the registers a
call keeps (`Str.Back`), the other bytes as they were. -/
theorem sns_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sns_at sns) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sns_at) {n : Nat}
    (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rsi i) ≠ 0) (hz : V (Addr.add X.cpu.gpr.rsi n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hdb : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64) (hsb : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hds : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rdi (toBytesLE (BitVec.ofNat 32 (cnt V X.cpu.gpr.rsi n)) 4)) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kfin : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = sns_at.add 46 →
      Kp X.cpu.gpr Z.cpu.gpr → Z.cpu.gpr.rdi = X.cpu.gpr.rdi →
      BitVec.setWidth 32 Z.cpu.gpr.rcx = BitVec.ofNat 32 (cnt V X.cpu.gpr.rsi n) → GoG prof L o gev gP gE Z t' := by
    intro Z t' hKZ hAZ hrZ hkp hdi hcx
    refine (c_46 prof).run c hin _ hKZ hAZ hrZ (vc_46 (g := Z.cpu.gpr) (by rw [hdi]; exact hw)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    rw [hdi, hcx] at hAY
    have hra' : rdq(Vst V X.cpu.gpr.rdi (toBytesLE (BitVec.ofNat 32 (cnt V X.cpu.gpr.rsi n)) 4), X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [Tcg.t_rdq_vst (by rw [toBytesLE_length]; exact hdb) hsb (by rw [toBytesLE_length]; exact hds)]
      exact hra
    exact ret_back c hin (lt_len (by decide)) (ret_48 _) hKY hAY hrY (hkp.trans (Kp.of_eq hgY (Kp.refl _))) hl hin₂
      h₂ hra' fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => hf i (by omega)
  have hr0 : X.cpu.rip = sns_at.add 0 := by rw [addr_add_zero]; exact hrip
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have hz' : (V X.cpu.gpr.rsi == 0) = true := by
      rw [addr_add_zero] at hz
      exact beq_iff_eq.2 hz
    refine (c_0 prof).run c hin _ hK hA hr0 (vc_0z hz' hf0) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine kfin Y t₁ hKY hAY hrY (kp_w hgY) (by rw [hgY]; try rfl) ?_
    rw [hgY]
    exact hc
  · have hz' : (V X.cpu.gpr.rsi == 0) = false := by
      have h := hnz 0 h0
      rw [addr_add_zero] at h
      exact beq_eq_false_iff_ne.2 h
    refine (c_0 prof).run c hin _ hK hA hr0 (vc_0n hz' hf0) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, cx, rfl, ha, hc⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine loop c hin hnz hz hf kfin (n - 1) 0 (by omega) Y t₁ hKY hAY hrY ?_ ?_ ?_ (by rw [hgY]; try rfl) (kp_w hgY)
    · rw [hgY, addr_add_zero]
      exact ha
    · rw [hgY]
      rfl
    · rw [hgY]
      exact hc

end FV7z.Sns
