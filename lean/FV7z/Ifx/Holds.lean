import FV7z.Ifx.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CArcCommand::IsFromExtractGroup` (PLAN.md §M, M1)

7-Zip 26.06's `CArcCommand::IsFromExtractGroup` at `0x5a70d0` in `7zzs` (`CPP/7zip/UI/Common/ArchiveCommandLine.h`;
`objdump -d`): `CommandType - 3 <= 2` (unsigned: `kTest`, `kExtract`, `kExtractFull`) in `al`.

- `cmdT`: `CommandType`, the 4 bytes at `this`; `vc_0`: the stretch to the `ret` (15); `ifx_ok`: from the entry to
  the return address (`Fn.leaf_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ifx

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_15 : pret <+: ifx.drop 15 := by decide +kernel
theorem ret_15 (feat : Features) : Dec feat ifx 15 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 15) (k := 0) (pret_0 feat) w_15 (Nat.zero_le _)

/-- `CommandType`, at `this`. -/
abbrev cmdT (V : Addr → Byte) (p : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs p 4).map V)

/-- The registers after: `eax` = `CommandType - 3`, its low byte the test (`setbe`). -/
abbrev ifxG (g : Gprs) (V : Addr → Byte) (f : Rflags) : Gprs :=
  wrLo (g.set 0 ((cmdT V g.rdi - 3#32).setWidth 64)) 0
    ((BitVec.ofBool ((subF f (cmdT V g.rdi - 3#32) 2#32).cond 6)).setWidth 8)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov eax, [rdi]; sub eax, 3; cmp eax, 2; setbe al`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' => g' = ifxG g V f ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa ⊢
  wpx [o0, Op.setcc, ifxG, cmdT]
  first
  | rfl
  | exact fa
  | exact ⟨fa, rfl⟩
  | exact ⟨fa, rfl, rfl⟩
  | exact ⟨fa, fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => rfl⟩
  | repeat' (first | exact fa | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `CArcCommand::IsFromExtractGroup` from its entry to the return address: the registers `ifxG`. -/
theorem ifx_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ifx_at ifx) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifx_at)
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (ifxG X.cpu.gpr V X.cpu.rflags).set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  leaf_ok (c_0 prof) (ret_15 _) (lt_len (by decide)) c hin hK hA hrip (vc_0 fa) rfl hl hin₂ h₂ hra k

end FV7z.Ifx
