import FV7z.Gpm.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CArcCommand::GetPathMode` (PLAN.md §M, M1)

7-Zip 26.06's `CArcCommand::GetPathMode` at `0x5a70e0` in `7zzs` (`CPP/7zip/UI/Common/ArchiveCommandLine.h`;
`objdump -d`): `(CommandType - 3) & ~2`, or 2 where that is not 0 (`cmovne`); `edx` 2.

- `pmV`: the value returned; `vc_0`: the stretch to the `ret` (20); `gpm_ok`: from the entry to the return address
  (`Fn.leaf_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gpm

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_20 : pret <+: gpm.drop 20 := by decide +kernel
theorem ret_20 (feat : Features) : Dec feat gpm 20 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 20) (k := 0) (pret_0 feat) w_20 (Nat.zero_le _)

/-- `(CommandType - 3) & ~2`, `CommandType` the 4 bytes at `this`. -/
abbrev pmR (V : Addr → Byte) (p : Addr) : BitVec 32 := (ofBytesLE 32 ((byteAddrs p 4).map V) - 3#32) &&& 4294967293#32

/-- The value returned: `pmR`, or 2 where `pmR` is not 0. -/
abbrev pmV (V : Addr → Byte) (p : Addr) : BitVec 32 := if (!(pmR V p == 0)) = true then 2#32 else pmR V p

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov eax, [rdi]; mov edx, 2; sub eax, 3; and eax, -3; cmovne eax, edx`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' =>
      g' = (g.set 2 ((2#32).setWidth 64)).set 0 ((pmV V g.rdi).setWidth 64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa ⊢
  wpx [o0, pmV, pmR]
  first
  | rfl
  | exact fa
  | exact ⟨fa, rfl⟩
  | exact ⟨fa, rfl, rfl⟩
  | exact ⟨fa, fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => rfl⟩
  | repeat' (first | exact fa | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `CArcCommand::GetPathMode` from its entry to the return address: `eax` = `pmV`, `edx` 2. -/
theorem gpm_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gpm_at gpm) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gpm_at)
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = ((X.cpu.gpr.set 2 ((2#32).setWidth 64)).set 0 ((pmV V X.cpu.gpr.rdi).setWidth 64)).set 4
        (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  leaf_ok (c_0 prof) (ret_20 _) (lt_len (by decide)) c hin hK hA hrip (vc_0 fa) rfl hl hin₂ h₂ hra k

end FV7z.Gpm
