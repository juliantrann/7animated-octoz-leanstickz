import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# Contracts of `strlen`, `strncmp` and `strrchr` (PLAN.md G3, startup)

glibc's startup calls `strlen`, `strncmp`, `strrchr` through the PLT (`0x401108`, `0x401048`, `0x401050`: IFUNCs,
the implementation chosen by the processor's features). What a call does is a hypothesis here, as `Tls.CpyAt` is of
`memcpy`; `Pm` is what the contract asks of the bytes at the call (the GOT entry the PLT jumps through, say). The
implementations read whole vectors, never across the end of a page a byte of the string is not in: the contracts ask
the pages of the strings' bytes to be read, not only the bytes.

- `LenAt`: `strlen (s)`, the string of `n` bytes and its 0: `rax` is `n`.
- `RchrAt`: `strrchr (s, c)`, `c` not 0: `rax` is null or the address of the last `c`. `last_with`: of `n`
  indices, none has a property or there is a last one with it.
- `NcmpAt`: `strncmp (a, b, n)`, the first `m ≤ n` bytes of both equal and not 0: `eax` is 0 if `m = n` or both have
  a 0 next, not 0 if the next bytes differ.

Both keep the bytes and the registers a call keeps. `Back`: the registers a function keeps, after its `ret`;
`first_not`: of `n` indices, all have a property or there is a first one without.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Str

/-- What a call of `strlen` at `e` does, the bytes at the call with `Pm`: called with a return address in code of the
list and `rdi` a string of `n` bytes that are not 0 and a 0, the pages of these to read, the run reaches the return
address with `rax` `n`, the registers a call keeps kept, and the bytes as they were. -/
def LenAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat} (n : Nat), Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    X.cpu.gpr.rdi.toNat + n < 2 ^ 64 →
    (∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ 0) → V (Addr.add X.cpu.gpr.rdi n) = 0 →
    (∀ x : Addr, X.cpu.gpr.rdi.toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ (X.cpu.gpr.rdi.toNat + n) / 4096 → Foot F.data x) →
    (∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = BitVec.ofNat 64 n → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- What a call of `strncmp` at `e` does, the bytes at the call with `Pm`: called with a return address in code of
the list, the first `m ≤ rdx` bytes at `rdi` and at `rsi` equal and not 0, the pages of these and of the next byte
(if `m < rdx`) to read, the run reaches the return address with `eax` 0 if `m = rdx` or the next bytes are both 0,
not 0 if the next bytes differ, the registers a call keeps kept, and the bytes as they were. -/
def NcmpAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat} (m : Nat), Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    m ≤ X.cpu.gpr.rdx.toNat → X.cpu.gpr.rdi.toNat + m < 2 ^ 64 → X.cpu.gpr.rsi.toNat + m < 2 ^ 64 →
    (∀ k < m, V (Addr.add X.cpu.gpr.rdi k) = V (Addr.add X.cpu.gpr.rsi k) ∧ V (Addr.add X.cpu.gpr.rdi k) ≠ 0) →
    (∀ x : Addr, ∀ k ≤ m, k < X.cpu.gpr.rdx.toNat →
      x.toNat / 4096 = (X.cpu.gpr.rdi.toNat + k) / 4096 ∨ x.toNat / 4096 = (X.cpu.gpr.rsi.toNat + k) / 4096 →
      Foot F.data x) →
    (∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      (m = X.cpu.gpr.rdx.toNat → Z.cpu.gpr.rax.setWidth 32 = 0#32) →
      (m < X.cpu.gpr.rdx.toNat → V (Addr.add X.cpu.gpr.rdi m) = V (Addr.add X.cpu.gpr.rsi m) →
        V (Addr.add X.cpu.gpr.rdi m) = 0 → Z.cpu.gpr.rax.setWidth 32 = 0#32) →
      (m < X.cpu.gpr.rdx.toNat → V (Addr.add X.cpu.gpr.rdi m) ≠ V (Addr.add X.cpu.gpr.rsi m) →
        Z.cpu.gpr.rax.setWidth 32 ≠ 0#32) →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- What a call of `strrchr` at `e` does, the bytes at the call with `Pm`: called with a return address in code of
the list, `rdi` a string of `n` bytes that are not 0 and a 0, the pages of these to read, and `sil` a character `c`
not 0, the run reaches the return address with `rax` null if the string has no `c`, the address of its last `c`
otherwise, the registers a call keeps kept, and the bytes as they were. -/
def RchrAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat} (n : Nat), Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) → X.cpu.gpr.rdi.toNat + n < 2 ^ 64 →
    (∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ 0) → V (Addr.add X.cpu.gpr.rdi n) = 0 →
    X.cpu.gpr.rsi.setWidth 8 ≠ 0#8 →
    (∀ x : Addr, X.cpu.gpr.rdi.toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ (X.cpu.gpr.rdi.toNat + n) / 4096 → Foot F.data x) →
    (∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      ((∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ X.cpu.gpr.rsi.setWidth 8) → Z.cpu.gpr.rax = 0) →
      (∀ m < n, V (Addr.add X.cpu.gpr.rdi m) = X.cpu.gpr.rsi.setWidth 8 →
        (∀ k, m < k → k < n → V (Addr.add X.cpu.gpr.rdi k) ≠ X.cpu.gpr.rsi.setWidth 8) →
        Z.cpu.gpr.rax = Addr.add X.cpu.gpr.rdi m) →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- Of `n` indices, none has a property or there is a last one with it. -/
theorem last_with (P : Nat → Prop) : ∀ n : Nat, (∀ k < n, ¬ P k) ∨ ∃ m < n, P m ∧ ∀ k, m < k → k < n → ¬ P k
  | 0 => .inl fun _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    rcases Classical.em (P n) with h | h
    · exact .inr ⟨n, Nat.lt_succ_self n, h, fun k h1 h2 => by omega⟩
    · rcases last_with P n with h' | ⟨m, hm, hp, hl⟩
      · refine .inl fun k hk => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h1 | rfl
        · exact h' k h1
        · exact h
      · refine .inr ⟨m, by omega, hp, fun k h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
        · exact hl k h1 h3
        · exact h

/-- The registers a function keeps, after its `ret`. -/
def Back (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp + 8#64 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- Of `n` indices, either all have `P` or there is a first one without. -/
theorem first_not (P : Nat → Prop) : ∀ n : Nat, (∀ k < n, P k) ∨ ∃ m < n, (∀ k < m, P k) ∧ ¬ P m
  | 0 => .inl fun _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    rcases first_not P n with h | ⟨m, hm, h1, h2⟩
    · by_cases hn : P n
      · refine .inl fun k hk => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | rfl
        · exact h k h'
        · exact hn
      · exact .inr ⟨n, Nat.lt_succ_self n, h, hn⟩
    · exact .inr ⟨m, Nat.lt_succ_of_lt hm, h1, h2⟩

end FV7z.Str
