import FV7z.Aac.Loop
import FV7z.Acp.Holds
/-!
# `AString::operator= (const char *)` (PLAN.md §M, M1)

7-Zip's `AString::operator= (const char *s)` at `0x44c4c0` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi`
and `s` in `rsi`, `push r13; mov r13, rdi; push r12; push rbp; mov rbp, rsi; push rbx; xor ebx, ebx; sub rsp, 8`, the
length loop (`FV7z/Aac/Loop.lean`); at a length above `_limit` (the 4 bytes at `this + 12`) `operator new [] (len +
1)` (`call` at 100 to `0x6029b0`), `delete [] _chars` (`call` at 117 to `0x6014f0`) unless null, `_chars` = the new
buffer and `_limit` = `len` (122); else (51) `r12` = `_chars`; then (55) `_len` = `len` (at `this + 8`), the copy loop
at 64 through the 0, `rax` = `this`, the `pop`s and the `ret` at 94.

The callees are hypotheses (`kn`, `kd`), as in `FV7z/Arb/Holds.lean`: their posts give the frame, the string as it
was and the buffer writable and apart (`Pn`), and `P1`, `P2`.

- `Sv`: the saved `r13`, `r12`, `rbp`, `rbx` and the return address; `Bf`: the buffer of `n + 1` bytes writable and
  apart from the string and from the frame; `Pn`: the post of a callee; `W2`: the bytes after `_chars` = `p`,
  `_limit` = `v`.
- `vc_51`, `vc_55`, `vc_105`, `vc_122`: the verification conditions of the pieces between the loops and the calls.
- `aac_ok`: from the entry, through the length loop, in place (`ki`) or through `operator new []` and `operator
  delete []` (`kz`, `kr`), the copy loop, to the return with `rax` = `this`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Aac

/-- The `call`s to `operator new []` and `operator delete []`. -/
def pcn : List Byte := [0xe8, 0x87, 0x64, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1795207] 5) := by dec_rfl
theorem wc_100 : pcn <+: aac.drop 100 := by decide +kernel
theorem call_100 (feat : Features) : Dec feat aac 100 (FV7z.mk .call 64 [.rel 1795207] 5) :=
  Dec.shift (j := 100) (k := 0) (pcn_0 feat) wc_100 (Nat.zero_le _)
def pcd : List Byte := [0xe8, 0xb6, 0x4f, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1789878] 5) := by dec_rfl
theorem wc_117 : pcd <+: aac.drop 117 := by decide +kernel
theorem call_117 (feat : Features) : Dec feat aac 117 (FV7z.mk .call 64 [.rel 1789878] 5) :=
  Dec.shift (j := 117) (k := 0) (pcd_0 feat) wc_117 (Nat.zero_le _)

/-- The `ret`. -/
theorem w_94 : Asl.pret <+: aac.drop 94 := by decide +kernel
theorem ret_94 (feat : Features) : Dec feat aac 94 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 94) (k := 0) (Asl.pret_0 feat) w_94 (Nat.zero_le _)

/-- The saved `r13`, `r12`, `rbp`, `rbx` and the return address, for the registers `g` at the entry. -/
def Sv (V : Addr → Byte) (g : Gprs) (ra : Addr) : Prop :=
  rdq(V, g.rsp - 8) = g.r13 ∧ rdq(V, g.rsp - 16) = g.r12 ∧ rdq(V, g.rsp - 24) = g.rbp ∧ rdq(V, g.rsp - 32) = g.rbx ∧
    rdq(V, g.rsp) = ra

/-- The bytes after `_chars` = `p` and `_limit` = `v` for the object at `b`. -/
abbrev W2 (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)

variable {F : Footprint} {Wl : List Rgn}

/-- The buffer `d` of `n + 1` bytes: writable, apart from the string (`rsi`) and from the frame. -/
def Bf (g : Gprs) (n : Nat) (d : Addr) : Prop :=
  (∀ i, i ≤ n → Foot Wl (Addr.add d i)) ∧ d.toNat + n + 1 ≤ 2 ^ 64 ∧
    (d.toNat + n + 1 ≤ g.rsi.toNat ∨ g.rsi.toNat + n + 1 ≤ d.toNat) ∧
    (d.toNat + n + 1 ≤ g.rsp.toNat - 40 ∨ g.rsp.toNat + 8 ≤ d.toNat)

/-- The post of a callee, for the registers `g` and the bytes `V` at the entry: the frame, the string of `n` bytes
and a 0 as it was, the buffer `d` as `Bf`. -/
def Pn (g : Gprs) (V : Addr → Byte) (n : Nat) (ra d : Addr) (V' : Addr → Byte) : Prop :=
  Sv V' g ra ∧ (∀ i, i ≤ n → V' (Addr.add g.rsi i) = V (Addr.add g.rsi i)) ∧ Bf (Wl := Wl) g n d

/-- `mov r12, [r13]`, to 55. -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f0 : ∀ i < 8, Foot F.data (Addr.add g.r13 i)) :
    W_51 F Wl (fun j' g' _ V' => j' = 55 ∧ g' = { g with r12 := rdq(V, g.r13) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 ⊢
  wpx [W_51, o4]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r13 + 8], ebx; xor edx, edx`, to the copy loop at 64. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 4, Foot Wl (Addr.add (g.r13 + 8#64) i)) :
    W_55 F Wl (fun j' g' _ V' => j' = 64 ∧ g' = { g with rdx := 0#64 } ∧
      V' = Vst V (g.r13 + 8#64) (toBytesLE (BitVec.setWidth 32 g.rbx) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw ⊢
  wpx [W_55, o5, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new []`: `mov rdi, [r13]; mov r12, rax; test rdi, rdi; je 122`, else to the `call` at 117. -/
theorem vc_105 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r13 i))
    (h122 : rdq(V, g.r13) = 0 → ∀ fl, Q 122 { g with rdi := rdq(V, g.r13), r12 := g.rax } fl V)
    (h117 : rdq(V, g.r13) ≠ 0 → ∀ fl, Q 117 { g with rdi := rdq(V, g.r13), r12 := g.rax } fl V) :
    W_105 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h122 h117 ⊢
  by_cases h0 : rdq(V, r13) = 0
  · have hb : (rdq(V, r13) == 0) = true := beq_iff_eq.2 h0
    wpx [W_105, o9, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h122 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rdq(V, r13) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_105, o9, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h117 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `mov [r13], r12; mov [r13 + 12], ebx; jmp 55`. -/
theorem vc_122 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.r13 i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.r13 + 12#64) i)) :
    W_122 F Wl (fun j' g' _ V' => j' = 55 ∧ g' = g ∧ V' = W2 V g.r13 g.r12 (BitVec.setWidth 32 g.rbx)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw12 ⊢
  wpx [W_122, o10]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::operator= (const char *s)` (`this` = `rdi`, `s` = `rsi`) from its entry, for `s` with `n` bytes not 0
and a 0, apart from the object and the frame. With `n` = 0 or `_limit` not below `n` the bytes go in place into
`_chars` (`Bf` by `hbi`), and the run returns (`ki`). Else at `operator new []`'s entry (`kn`, for any registers with
`rsp`, `rdi` = `n + 1`, `rbx` = `n`, `rbp` = `s`, `r12` … `r15` as the code has them), back at 105 with the buffer
`rax` (`Pn`, `P1`); with `_chars` null the run returns (`kz`); else at `operator delete []`'s entry (`kd`) and back at
122 (`Pn`, `P2`), then the run returns (`kr`). At the return the registers a call keeps are as at the entry, `rax` =
`this`, and the bytes are `_chars`, `_limit` as stored (`W2`), `_len` = `n` and the string copied (`Acp.Cp`). -/
theorem aac_ok {P1 P2 : State → (Addr → Byte) → Prop} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L aac_at aac) {codeN codeD : List Byte}
    (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aac_at)
    (hp : 64 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hn : n < 2 ^ 32) (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rsi i) ≠ 0#8)
    (hz : V (Addr.add X.cpu.gpr.rsi n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hpw : X.cpu.gpr.rsi.toNat + n + 1 ≤ 2 ^ 64)
    (hpf : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    (hpt : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hbi : (n = 0 ∨ ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n) →
      Bf (Wl := Wl) X.cpu.gpr n rdq(V, X.cpu.gpr.rdi))
    (ki : (n = 0 ∨ ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n) → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi rdq(V, X.cpu.gpr.rdi) (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kn : 0 < n → rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (G : Gprs), G.rsp = X.cpu.gpr.rsp - 40 →
      G.rdi = BitVec.ofNat 64 (n + 1) → G.rbx = BitVec.ofNat 64 n → G.rbp = X.cpu.gpr.rsi →
      G.r12 = X.cpu.gpr.r12 → G.r13 = X.cpu.gpr.rdi → G.r14 = X.cpu.gpr.r14 → G.r15 = X.cpu.gpr.r15 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (aac_at.add 105) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = aac_at.add 105 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = BitVec.ofNat 64 n →
        Z.cpu.gpr.rbp = X.cpu.gpr.rsi → Z.cpu.gpr.r13 = X.cpu.gpr.rdi → Z.cpu.gpr.r14 = X.cpu.gpr.r14 →
        Z.cpu.gpr.r15 = X.cpu.gpr.r15 → Pn (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) Z.cpu.gpr.rax V' → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) = 0 → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 V' X.cpu.gpr.rdi Z.cpu.gpr.rax (BitVec.ofNat 32 n))
        (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi Z.cpu.gpr.rax (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kd : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) ≠ 0 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48) (toBytesLE (aac_at.add 122) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r12 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = aac_at.add 122 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = BitVec.ofNat 64 n →
        Z₂.cpu.gpr.rbp = X.cpu.gpr.rsi → Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax → Z₂.cpu.gpr.r13 = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.r14 = X.cpu.gpr.r14 → Z₂.cpu.gpr.r15 = X.cpu.gpr.r15 →
        Pn (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) Z.cpu.gpr.rax V'' → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 V'' X.cpu.gpr.rdi Z₂.cpu.gpr.r12 (BitVec.ofNat 32 n))
        (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi Z₂.cpu.gpr.r12 (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have e48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have q32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have q24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have q16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have q8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have q0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have hrip' : X.cpu.rip = aac_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hpw' : X.cpu.gpr.rsi.toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have tp : ∀ i, i ≤ n → (Addr.add X.cpu.gpr.rsi i).toNat = X.cpu.gpr.rsi.toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hpw'
  have hl32 : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp <;> omega
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40 - 8) i) := by rw [e48]; exact hs6
  -- a quad word read through a store apart from it, and read back from its own store
  have pk : ∀ (W : Addr → Byte) (a x : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 → x.toNat + 8 ≤ 2 ^ 64 →
      (a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) → rdq(Vst W a (toBytesLE v 8), x) = rdq(W, x) :=
    fun W a x v ha hx h => congrArg (ofBytesLE 64)
      (Tun.rd_Vst W a (toBytesLE v 8) x 8 (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))
  have rq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 →
      rdq(Vst W a (toBytesLE v 8), a) = v := fun W a v ha => by
    rw [Tun.rd_Vst_self (n := 8) _ a _ (toBytesLE_length _ _) ha]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have mq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr) (m : Nat), a.toNat + 8 ≤ 2 ^ 64 →
      x.toNat + m ≤ 2 ^ 64 → (a.toNat + 8 ≤ x.toNat ∨ x.toNat + m ≤ a.toNat) →
      List.map (Vst W a (toBytesLE v 8)) (byteAddrs x m) = List.map W (byteAddrs x m) :=
    fun W a v x m ha hx h =>
      Tun.rd_Vst W a (toBytesLE v 8) x m (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h)
  have vq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr), a.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat < a.toNat ∨ a.toNat + 8 ≤ x.toNat) → Vst W a (toBytesLE v 8) x = W x :=
    fun W a v x ha h =>
      Tun.Vst_out W a (toBytesLE v 8) x (by rw [toBytesLE_length]; exact ha) (by rw [toBytesLE_length]; exact h)
  -- the bytes after the four pushes, apart from them
  have m0 : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ 2 ^ 64 →
      (x.toNat + m ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x m).map (V0 V X.cpu.gpr) = (byteAddrs x m).map V := by
    intro x m hx h
    show List.map (Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8)) (byteAddrs x m) = _
    rw [e32, e24, e16,
      mq _ (X.cpu.gpr.rsp - 32) _ x m (by rw [tn32]; omega) hx (by rw [tn32]; omega),
      mq _ (X.cpu.gpr.rsp - 24) _ x m (by rw [tn24]; omega) hx (by rw [tn24]; omega),
      mq _ (X.cpu.gpr.rsp - 16) _ x m (by rw [tn16]; omega) hx (by rw [tn16]; omega),
      mq _ (X.cpu.gpr.rsp - 8) _ x m (by rw [tn8]; omega) hx (by rw [tn8]; omega)]
  have hV0 : ∀ i, i ≤ n → V0 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) :=
      fun i hi => by
    show Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (Addr.add X.cpu.gpr.rsi i) = _
    rw [e32, e24, e16,
      vq _ (X.cpu.gpr.rsp - 32) _ (Addr.add X.cpu.gpr.rsi i) (by rw [tn32]; omega) (by rw [tn32, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 24) _ (Addr.add X.cpu.gpr.rsi i) (by rw [tn24]; omega) (by rw [tn24, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 16) _ (Addr.add X.cpu.gpr.rsi i) (by rw [tn16]; omega) (by rw [tn16, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 8) _ (Addr.add X.cpu.gpr.rsi i) (by rw [tn8]; omega) (by rw [tn8, tp i hi]; omega)]
  have hT0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by
    rw [m0 X.cpu.gpr.rdi 8 (by omega) (by omega)]
  have hT12 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = rdd(V, X.cpu.gpr.rdi + 12#64) := by
    rw [m0 (X.cpu.gpr.rdi + 12#64) 4 (by rw [t12]; omega) (by rw [t12]; omega)]
  -- the frame after the four pushes
  have sv0 : Sv (V0 V X.cpu.gpr) X.cpu.gpr (e₂.add j₂) := by
    refine ⟨?_, ?_, ?_, ?_, by rw [m0 X.cpu.gpr.rsp 8 hp8 (by omega)]; exact hra⟩
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 8) = _
      rw [e32, e24, e16, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 8) _ (by rw [tn32]; omega) (by rw [tn8]; omega)
          (by rw [tn32, tn8]; omega),
        pk _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 8) _ (by rw [tn24]; omega) (by rw [tn8]; omega)
          (by rw [tn24, tn8]; omega),
        pk _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rsp - 8) _ (by rw [tn16]; omega) (by rw [tn8]; omega)
          (by rw [tn16, tn8]; omega),
        rq _ (X.cpu.gpr.rsp - 8) _ (by rw [tn8]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 16) = _
      rw [e32, e24, e16, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 16) _ (by rw [tn32]; omega) (by rw [tn16]; omega)
          (by rw [tn32, tn16]; omega),
        pk _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 16) _ (by rw [tn24]; omega) (by rw [tn16]; omega)
          (by rw [tn24, tn16]; omega),
        rq _ (X.cpu.gpr.rsp - 16) _ (by rw [tn16]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 24) = _
      rw [e32, e24, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 24) _ (by rw [tn32]; omega) (by rw [tn24]; omega)
          (by rw [tn32, tn24]; omega),
        rq _ (X.cpu.gpr.rsp - 24) _ (by rw [tn24]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 32) = _
      rw [e32, rq _ (X.cpu.gpr.rsp - 32) _ (by rw [tn32]; omega)]
  -- the bytes after `_chars` and `_limit`, apart from the object
  have m2 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (W2 W X.cpu.gpr.rdi p v) = (byteAddrs x 8).map W := by
    intro W p v x hx h
    have a1 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) x 8
      (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega)
    have a2 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    exact a1.trans a2
  have b2 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (i : Nat), i ≤ n →
      W2 W X.cpu.gpr.rdi p v (Addr.add X.cpu.gpr.rsi i) = W (Addr.add X.cpu.gpr.rsi i) := fun W p v i hi => by
    show Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4)
      (Addr.add X.cpu.gpr.rsi i) = _
    rw [Tun.Vst_out _ (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) (Addr.add X.cpu.gpr.rsi i)
        (by rw [toBytesLE_length, t12]; omega)
        (by rw [toBytesLE_length, t12, tp i hi]; omega),
      vq _ X.cpu.gpr.rdi _ (Addr.add X.cpu.gpr.rsi i) (by omega)
        (by rw [toBytesLE_length, tp i hi]; omega)]
  -- from 55: `_len` = `n`, the copy loop, the `pop`s and the `ret`
  have fin : ∀ (U : State) (M : Addr → Byte) (d : Addr) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
      U.cpu.rip = aac_at.add 55 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.rbx = BitVec.ofNat 64 n →
      U.cpu.gpr.rbp = X.cpu.gpr.rsi → U.cpu.gpr.r12 = d → U.cpu.gpr.r13 = X.cpu.gpr.rdi →
      U.cpu.gpr.r14 = X.cpu.gpr.r14 → U.cpu.gpr.r15 = X.cpu.gpr.r15 → Sv M X.cpu.gpr (e₂.add j₂) →
      (∀ i, i ≤ n → M (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i)) → Bf (Wl := Wl) X.cpu.gpr n d →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Acp.Cp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4))
          X.cpu.gpr.rsi d (n + 1)) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U M d t' hKU hAU hrU hus hubx hubp hu12 hu13 hu14 hu15 hSv hstr hbf k
    obtain ⟨f13, f12, fbp, fbx, fra⟩ := hSv
    obtain ⟨hwd, hdw, hdp, hdf⟩ := hbf
    refine (c_55 prof).run c hin _ hKU hAU hrU (vc_55 (by rw [hu13]; exact fw8)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    rw [hu13, hubx, hl32] at hAY
    have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact hus
    have hYbp : Y.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hgY]; exact hubp
    have hY12 : Y.cpu.gpr.r12 = d := by rw [hgY]; exact hu12
    have hY13 : Y.cpu.gpr.r13 = X.cpu.gpr.rdi := by rw [hgY]; exact hu13
    have hY14 : Y.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hgY]; exact hu14
    have hY15 : Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgY]; exact hu15
    have hYdx : Y.cpu.gpr.rdx = BitVec.ofNat 64 0 := by rw [hgY] <;> rfl
    have hdw' : d.toNat + (n + 1) ≤ 2 ^ 64 := by omega
    have td : ∀ i, i ≤ n → (Addr.add d i).toNat = d.toNat + i := fun i hi => toNat_add_of_fits (by omega) hdw'
    have hW8 : ∀ i, i ≤ n → Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)
        (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
      rw [Tun.Vst_out M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4) (Addr.add X.cpu.gpr.rsi i)
        (by rw [toBytesLE_length, t8]; omega)
        (by rw [toBytesLE_length, t8, tp i hi]; omega), hstr i hi]
    have fr : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat →
        a.toNat ≤ X.cpu.gpr.rsp.toNat →
        rdq(Acp.Cp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi d (n + 1), a) =
          rdq(M, a) := fun a ha h1 h2 => by
      rw [Acp.rdCp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi d (n + 1) a ha
        hdw' (by omega)]
      exact congrArg (ofBytesLE 64) (Tun.rd_Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4) a 8
        (by rw [toBytesLE_length, t8]; omega) ha
        (by rw [toBytesLE_length, t8]; omega))
    refine loop c hin (W := Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4))
      (p := X.cpu.gpr.rsi) (d := d) (n := n) (g₀ := Y.cpu.gpr) (by omega)
      (fun i hi => by rw [hW8 i (by omega)]; exact hnz i hi) (by rw [hW8 n (Nat.le_refl _)]; exact hz) hf hwd
      (fun i hi j hj e => by
        have := congrArg BitVec.toNat e
        rw [tp i hi, td j hj] at this
        omega) hYbp hY12
      (by rw [hYs, q32]; exact fun i hi => c.hws _ (hs4 i hi))
      (by rw [hYs, q32, q24]; exact fun i hi => c.hws _ (hs3 i hi))
      (by rw [hYs, q32, q24, q16]; exact fun i hi => c.hws _ (hs2 i hi))
      (by rw [hYs, q32, q24, q16, q8]; exact fun i hi => c.hws _ (hs1 i hi)) ?_ n 0 (by omega) Y t₁ hKY hAY hrY
      hYdx (Kp.refl _)
    intro Z₄ t₂ hK₄ hA₄ hr₄ hbx hbp h12 h13 hsp4 hax h14 h15
    rw [hYs, q32] at hbx hbp h12 h13 hsp4
    rw [q24] at hbp h12 h13 hsp4
    rw [q16] at h12 h13 hsp4
    rw [q8] at h13 hsp4
    rw [q0] at hsp4
    have hkp : Kp X.cpu.gpr Z₄.cpu.gpr := by
      refine ⟨hsp4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbx, fr (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega)
          (by rw [tn32]; omega)]; exact fbx
      · rw [hbp, fr (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)
          (by rw [tn24]; omega)]; exact fbp
      · rw [h12, fr (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)
          (by rw [tn16]; omega)]; exact f12
      · rw [h13, fr (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)
          (by rw [tn8]; omega)]; exact f13
      · rw [h14, hY14]
      · rw [h15, hY15]
    have hra' : rdq(Acp.Cp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi d
        (n + 1), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [fr X.cpu.gpr.rsp hp8 (by omega) (by omega)]; exact fra
    exact ret_back c hin (lt_len (by decide)) (ret_94 _) hK₄ hA₄ hr₄ hkp hl hin₂ h₂ hra'
      fun Z'' t'' hK'' hA'' hr'' hB hax'' => k Z'' t'' hK'' hA'' hr'' hB (by rw [hax'', hax, hY13])
  -- from 51 (in place): `mov r12, [r13]`, then on from 55
  have h51 : (n = 0 ∨ ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n) → ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (V0 V X.cpu.gpr) → Y.cpu.rip = aac_at.add 51 → Ks (gS X.cpu.gpr) Y.cpu.gpr →
      Y.cpu.gpr.rbx = BitVec.ofNat 64 n → GoG prof L o gev gP gE Y t₁ := by
    intro hc Y t₁ hKY hAY hrY hks hbx
    obtain ⟨ksp, kbp, k12, k13, k14, k15⟩ := hks
    refine (c_51 prof).run c hin _ hKY hAY hrY (vc_51 (by rw [k13]; exact fun i hi => c.hws _ (fw0 i hi))) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₂ hKU hAU hrU hgU -
    refine fin U (V0 V X.cpu.gpr) rdq(V, X.cpu.gpr.rdi) t₂ hKU hAU hrU ?_ ?_ ?_ ?_ ?_ ?_ ?_ sv0 hV0 (hbi hc) (ki hc)
    · rw [hgU]; show Y.cpu.gpr.rsp = _; rw [ksp]; exact e40
    · rw [hgU]; exact hbx
    · rw [hgU]; show Y.cpu.gpr.rbp = _; rw [kbp] <;> rfl
    · rw [hgU]; show rdq(V0 V X.cpu.gpr, Y.cpu.gpr.r13) = _; rw [k13]; exact hT0
    · rw [hgU]; show Y.cpu.gpr.r13 = _; rw [k13] <;> rfl
    · rw [hgU]; show Y.cpu.gpr.r14 = _; rw [k14] <;> rfl
    · rw [hgU]; show Y.cpu.gpr.r15 = _; rw [k15] <;> rfl
  -- from 100: `operator new []`, then `delete [] _chars` unless null, the stores at 122, on from 55
  have h100 : 0 < n → rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (Y₂ : State) (t₃ : Nat), KeptW Wl s₀ Y₂ →
      Agree F Y₂.proc.mm.mem (V0 V X.cpu.gpr) → Y₂.cpu.rip = aac_at.add 100 →
      Y₂.cpu.gpr.rbx = BitVec.ofNat 64 n → Y₂.cpu.gpr.rdi = BitVec.ofNat 64 (n + 1) →
      Ks (gS X.cpu.gpr) Y₂.cpu.gpr → GoG prof L o gev gP gE Y₂ t₃ := by
    intro hn0 hc Y₂ t₃ hK₂ hA₂ hr₂ hbx hdi hks
    obtain ⟨ksp, kbp, k12, k13, k14, k15⟩ := hks
    have hs2' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [ksp]; exact e40
    refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_100 _) hinN hN (by decide) (by rw [hs2']; exact hst) ?_
    rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [hs2', e48] at hA₃
    have hg₃' : Y₃.cpu.gpr = Y₂.cpu.gpr.set 4 (X.cpu.gpr.rsp - 48) := by rw [hg₃, hs2', e48]
    refine kn hn0 hc Y₂.cpu.gpr hs2' hdi hbx (by rw [kbp] <;> rfl) (by rw [k12] <;> rfl) (by rw [k13] <;> rfl)
      (by rw [k14] <;> rfl) (by rw [k15] <;> rfl) Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
    -- back from `operator new []`
    intro Z V' t₅ hKZ hAZ hrZ hzs hzb hzp hz13 hz14 hz15 hPn hP1
    -- at 122 with the bytes `M`: the stores of `_chars` and `_limit`, then on from 55
    have h122 : ∀ (U : State) (M : Addr → Byte) (t₇ : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
        U.cpu.rip = aac_at.add 122 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.rbx = BitVec.ofNat 64 n →
        U.cpu.gpr.rbp = X.cpu.gpr.rsi → U.cpu.gpr.r12 = Z.cpu.gpr.rax → U.cpu.gpr.r13 = X.cpu.gpr.rdi →
        U.cpu.gpr.r14 = X.cpu.gpr.r14 → U.cpu.gpr.r15 = X.cpu.gpr.r15 →
        Pn (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) Z.cpu.gpr.rax M →
        (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
          Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 M X.cpu.gpr.rdi Z.cpu.gpr.rax (BitVec.ofNat 32 n))
            (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) X.cpu.gpr.rsi Z.cpu.gpr.rax (n + 1)) →
          Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
          GoG prof L o gev gP gE Z' t'') →
        GoG prof L o gev gP gE U t₇ := by
      intro U M t₇ hKU hAU hrU hus hubx hubp hu12 hu13 hu14 hu15 hPnU kU
      obtain ⟨⟨f13, f12, fbp, fbx, fra⟩, hstrU, hbfU⟩ := hPnU
      refine (c_122 prof).run c hin _ hKU hAU hrU (vc_122 (by rw [hu13]; exact fw0) (by rw [hu13]; exact fw12)) ?_
      rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ U' t₈ hKU' hAU' hrU' hgU' -
      rw [hu13, hu12, hubx, hl32] at hAU'
      refine fin U' _ Z.cpu.gpr.rax t₈ hKU' hAU' hrU' (by rw [hgU']; exact hus) (by rw [hgU']; exact hubx)
        (by rw [hgU']; exact hubp) (by rw [hgU']; exact hu12) (by rw [hgU']; exact hu13) (by rw [hgU']; exact hu14)
        (by rw [hgU']; exact hu15) ⟨?_, ?_, ?_, ?_, ?_⟩ (fun i hi => by rw [b2 M _ _ i hi]; exact hstrU i hi) hbfU kU
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact f13
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact f12
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact fbp
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega)]; exact fbx
      · rw [m2 _ _ _ X.cpu.gpr.rsp hp8 (by omega)]; exact fra
    refine (c_105 prof).run c hin (fun j' g' _ V'' =>
        g' = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r12 := Z.cpu.gpr.rax } ∧ V'' = V' ∧
        ((j' = 122 ∧ rdq(V', X.cpu.gpr.rdi) = 0) ∨ (j' = 117 ∧ rdq(V', X.cpu.gpr.rdi) ≠ 0))) hKZ hAZ hrZ
      (vc_105 (by rw [hz13]; exact fun i hi => c.hws _ (fw0 i hi))
        (fun h0 _ => ⟨by rw [hz13], rfl, .inl ⟨rfl, by rw [← hz13]; exact h0⟩⟩)
        (fun h0 _ => ⟨by rw [hz13], rfl, .inr ⟨rfl, by rw [← hz13]; exact h0⟩⟩)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, h⟩ Y₄ t₆ hK₄ hA₄ hr₄ hg₄ -
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- `_chars` null
      exact h122 Y₄ V' t₆ hK₄ hA₄ hr₄ (by rw [hg₄]; exact hzs) (by rw [hg₄]; exact hzb) (by rw [hg₄]; exact hzp)
        (by rw [hg₄] <;> rfl) (by rw [hg₄]; exact hz13) (by rw [hg₄]; exact hz14) (by rw [hg₄]; exact hz15) hPn
        (kz Z V' hP1 h0)
    · -- `operator delete [] (_chars)`
      have hs4' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₄]; exact hzs
      refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_117 _) hinD hD (by decide)
        (by rw [hs4']; exact hst) ?_
      rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hs4', e48] at hA₅
      have hg₅' : Y₅.cpu.gpr =
          { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r12 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 48) := by
        rw [hg₅, hs4', e48, hg₄]
      refine kd Z V' hP1 h0 Y₅ t₇ hK₅ hA₅ hr₅ hg₅' ?_
      intro Z₂ V'' t₈ hK₆ hA₆ hr₆ h2s h2b h2p h212 h213 h214 h215 hPn₂ hP2
      exact h122 Z₂ V'' t₈ hK₆ hA₆ hr₆ h2s h2b h2p h212 h213 h214 h215 hPn₂
        fun Z' t'' hK' hA' hr' hB hax => kr Z₂ V'' hP2 Z' t'' hK' (by rw [h212]; exact hA') hr' hB hax
  -- the entry and the length loop
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => hf i (by omega)
  have hb0 : Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsi = V (Addr.add X.cpu.gpr.rsi 0) := by
    have := hV0 0 (Nat.zero_le _)
    rw [addr_add_zero] at this ⊢
    exact this
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0z hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) hf0
        (by rw [hb0]; exact hz)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact h51 (.inl rfl) Y t₁ hKY hAY hrY (by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hgY] <;> rfl)
  · refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0n hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) hf0
        (by rw [hb0]; exact hnz 0 h0)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine slen c hin (W := V0 V X.cpu.gpr) (p := X.cpu.gpr.rsi) (n := n) (g₀ := gS X.cpu.gpr) hn
      (fun i hi => by rw [hV0 i (by omega)]; exact hnz i hi) (by rw [hV0 n (Nat.le_refl _)]; exact hz) hf rfl
      (fun i hi => c.hws _ (fw12 i hi)) ?_ ?_ (n - 1) 0 (by omega) Y t₁ hKY hAY hrY (by rw [hgY] <;> rfl)
      (by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    · intro hc Z t' hKZ hAZ hrZ hbx hdi hks
      exact h100 h0 (by rw [← hT12]; exact hc) Z t' hKZ hAZ hrZ hbx hdi hks
    · intro hc Z t' hKZ hAZ hrZ hbx hks
      exact h51 (.inr (by rw [← hT12]; exact hc)) Z t' hKZ hAZ hrZ hks hbx

end FV7z.Aac
