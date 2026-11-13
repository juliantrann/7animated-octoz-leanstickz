import FV7z.Gor.Cuts
import FV7z.Lemmas.Rmw4
import FV7z.Lemmas.SysLink
import FV7z.Memcmp.Words
import FV7z.Tun.Inv
/-!
# `_dl_get_origin`: the bytes, the path asked for, `mempcpy` (PLAN.md G3, startup)

glibc 2.31's `_dl_get_origin` (`sysdeps/unix/sysv/linux/dl-origin.c`) at `0x6aefa0` in `7zzs`.

- `Vst_map_self`, `probe_same`: the stack probe `or qword [rsp], 0` stores the bytes that are there.
- `frV`: the bytes after the four `push`es.
- `pse`: the path `/proc/self/exe` (14 bytes at `0x706823`, then a NUL), as `ProcSelfExe` names it.
- `PcpyAt`: the contract of `mempcpy` (`0x4010c0`, through the PLT: an IFUNC), a hypothesis, as `Tls.CpyAt` is of
  `memcpy`: the same, `rax` the end of the bytes stored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gor

/-- Storing at `a` the `n` bytes that are there. -/
theorem Vst_map_self (n : Nat) : ∀ (V : Addr → Byte) (a : Addr), Vst V a ((byteAddrs a n).map V) = V := by
  induction n with
  | zero =>
    intro V a
    simp [byteAddrs, Vst]
  | succ n ih =>
    intro V a
    have e : upd1 V a (V a) = V := funext fun x => by
      unfold upd1
      split <;> simp_all
    rw [byteAddrs_succ, List.map_cons, Vst, e, ih]

/-- The stack probe `or qword [rsp], 0`: the bytes are as they were. -/
theorem probe_same (V : Addr → Byte) (a : Addr) :
    Vst V a (toBytesLE (ofBytesLE 64 ((byteAddrs a 8).map V) ||| BitVec.ofNat 64 0) 8) = V := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_zero,
    Order.toBytesLE_ofBytesLE (by simp [byteAddrs]) (by decide), Vst_map_self]

/-- The bytes after the four `push`es of the entry (`r13`, `r12`, `rbp`, `rbx`). -/
def frV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The path `/proc/self/exe`. -/
def pse : List Byte := "/proc/self/exe".toUTF8.toList.map UInt8.toBitVec

theorem pse_eq : pse = [0x2f, 0x70, 0x72, 0x6f, 0x63, 0x2f, 0x73, 0x65, 0x6c, 0x66, 0x2f, 0x65, 0x78, 0x65] := by
  first | decide +kernel | decide | rfl

theorem pse_length : pse.length = 14 := by rw [pse_eq]; rfl

/-- Where the loop of `_dl_get_origin` stops in the `c` bytes at `B`: the last `/` at an index from 1 to `c - 1`,
or 0 if there is none (the directory is `/`). -/
def sl (V : Addr → Byte) (B : Addr) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | c + 2 => if V (B.add (c + 1)) = 0x2f then c + 1 else sl V B (c + 1)

theorem sl_lt (V : Addr → Byte) (B : Addr) : ∀ c, sl V B c < c ∨ c = 0
  | 0 => .inr rfl
  | 1 => .inl (by simp [sl])
  | c + 2 => by
    unfold sl
    split
    · exact .inl (by omega)
    · rcases sl_lt V B (c + 1) with h | h
      · exact .inl (by omega)
      · omega

/-- The last `/` is a `/`. -/
theorem sl_slash (V : Addr → Byte) (B : Addr) : ∀ c, sl V B c ≠ 0 → V (B.add (sl V B c)) = 0x2f
  | 0 => fun h => absurd rfl h
  | 1 => fun h => absurd rfl h
  | c + 2 => by
    unfold sl
    split
    · intro _; assumption
    · exact sl_slash V B (c + 1)

/-- After the last `/`, none. -/
theorem sl_after (V : Addr → Byte) (B : Addr) : ∀ c i, sl V B c < i → i < c → V (B.add i) ≠ 0x2f
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | 1 => fun i h1 h2 => by simp [sl] at h1; omega
  | c + 2 => fun i h1 h2 => by
    unfold sl at h1
    split at h1
    · omega
    · rcases Nat.lt_or_ge i (c + 1) with h | h
      · exact sl_after V B (c + 1) i h1 h
      · obtain rfl : i = c + 1 := by omega
        assumption

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}

/-- What a call of `mempcpy` at `e` does, the bytes at the call with `Pm`: called with a return address in code of
the list, the `rdx` bytes at `rsi` to read, those at `rdi` to store to, the two apart and those at `rdi` apart from
the return address, the run reaches the return address with `rax` the end `rdi + rdx` of the bytes stored, the
registers a call keeps kept, the bytes at `rdi` those at `rsi`, and the other bytes as they were. -/
def PcpyAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot F.data (Addr.add X.cpu.gpr.rsi i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
    X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 → X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 →
    (X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsi.toNat) →
    (X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
    (∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi + X.cpu.gpr.rdx →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < X.cpu.gpr.rdx.toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = V (Addr.add X.cpu.gpr.rsi i)) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat) →
        V₂ a = V a) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

end FV7z.Gor
