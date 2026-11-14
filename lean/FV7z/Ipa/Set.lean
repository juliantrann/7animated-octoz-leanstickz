import FV7z.Gor.Mem
/-!
# `memset` through the PLT (`0x401080`), a contract **assumed** (PLAN.md G3, startup)

`_dl_init_paths` clears the status array of each of the 4 system directories with `memset (p, 0, 4 * ncapstr)`.
`memset` is an IFUNC (glibc 2.31 picks `__memset_avx2_unaligned_erms` or another by the CPU's features), reached
through the PLT slot `0x401080`: like `mempcpy` (`Gor.PcpyAt`) and the string functions (`Str.LenAt`), what a call
does is a hypothesis here, `Pm` the state of its GOT slot; to be discharged with the IFUNC bodies (PLAN.md, item
«contract cho các hàm chuỗi IFUNC»).

- `SetAt`: called with a return address in code, the `rdx` bytes at `rdi` to store to, apart from the return
  address: the run reaches the return address with `rax = rdi`, the registers a call keeps kept, the bytes at `rdi`
  the low byte of `rsi`, the other bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Ipa

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}

/-- What a call of `memset` at `e` does (assumed; see the module doc). -/
def SetAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
    X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 →
    (X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
    (∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < X.cpu.gpr.rdx.toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = X.cpu.gpr.rsi.setWidth 8) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat) →
        V₂ a = V a) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

end FV7z.Ipa
