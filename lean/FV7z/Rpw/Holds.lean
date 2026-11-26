import FV7z.Rpw.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `NWindows::NFile::NName::GetRootPrefixSize(const wchar_t *)` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NName::GetRootPrefixSize(const wchar_t *)` at `0x456a70` in `7zzs`
(`CPP/Windows/FileName.cpp`; `objdump -d`): 1 if the path's first `wchar_t` is `/`, else 0.

- `vc_0`: the stretch to the `ret` (12); `rpw_ok`: from the entry to the return address (`Fn.leaf_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rpw

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_12 : pret <+: rpw.drop 12 := by decide +kernel
theorem ret_12 (feat : Features) : Dec feat rpw 12 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 12) (k := 0) (pret_0 feat) w_12 (Nat.zero_le _)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The path's first `wchar_t` is `/`. -/
abbrev isSl (V : Addr → Byte) (p : Addr) : Bool := decide (ofBytesLE 32 ((byteAddrs p 4).map V) = 47#32)

/-- `xor eax, eax; cmp dword [rdi], '/'; sete al`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' =>
      g' = wrLo (g.set 0 0) 0 ((BitVec.ofBool (isSl V g.rdi)).setWidth 8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa ⊢
  wpx [o0, lf_xz, Op.cmpmi, Op.setcc, isSl]
  first
  | rfl
  | exact fa
  | exact ⟨fa, rfl⟩
  | exact ⟨fa, rfl, rfl⟩
  | exact ⟨fa, fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => rfl⟩
  | repeat' (first | exact fa | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `NWindows::NFile::NName::GetRootPrefixSize(const wchar_t *)` from its entry to the return address:
`rax` 1 if the path's first `wchar_t` is `/`, else 0. -/
theorem rpw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rpw_at rpw) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rpw_at) (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (X.cpu.gpr.set 0 ((BitVec.ofBool (isSl V X.cpu.gpr.rdi)).setWidth 64)).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  leaf_ok (G := X.cpu.gpr.set 0 ((BitVec.ofBool (isSl V X.cpu.gpr.rdi)).setWidth 64)) (c_0 prof) (ret_12 _)
    (lt_len (by decide)) c hin hK hA hrip (by rw [← lf_setb]; exact vc_0 fa) rfl hl hin₂ h₂ hra k

end FV7z.Rpw
