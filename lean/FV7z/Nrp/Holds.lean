import FV7z.Nrp.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `NHash::CHandler::GetNumRawProps` (PLAN.md §M, M1)

7-Zip 26.06's `NHash::CHandler::GetNumRawProps` at `0x49e940` in `7zzs`
(`objdump -d`): `*numProps = 1`, 0 (`S_OK`)
returned.

- `vc_0`: the stretch to the `ret` (12); `nrp_ok`: from the entry to the return address (`Fn.leaf_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Nrp

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_12 : pret <+: nrp.drop 12 := by decide +kernel
theorem ret_12 (feat : Features) : Dec feat nrp 12 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 12) (k := 0) (pret_0 feat) w_12 (Nat.zero_le _)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov dword [rsi], 1; xor eax, eax`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fw : ∀ i < 4, Foot Wl (Addr.add g.rsi i)) :
    wp F Wl o0 (fun g' _ V' => g' = g.set 0 0 ∧ V' = Vst V g.rsi (toBytesLE 1#32 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [o0, lf_xz]
  first
  | rfl
  | exact fw
  | exact ⟨fw, rfl⟩
  | exact ⟨fw, rfl, rfl⟩
  | exact ⟨fw, fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fw, fun _ => rfl⟩
  | repeat' (first | exact fw | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `NHash::CHandler::GetNumRawProps` from its entry to the return address:
`1` stored at `rsi`, `rax` 0. -/
theorem nrp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nrp_at nrp) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nrp_at) (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (hfa : X.cpu.gpr.rsi.toNat + 4 ≤ 2 ^ 64) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : X.cpu.gpr.rsi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → 
      Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rsi (toBytesLE 1#32 4)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (X.cpu.gpr.set 0 0).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hb : (toBytesLE (1#32 : BitVec 32) 4).length = 4 := toBytesLE_length _ _
  have h1 : X.cpu.gpr.rsi.toNat + (toBytesLE (1#32 : BitVec 32) 4).length ≤ 2 ^ 64 := by rw [hb]; exact hfa
  have h2 : X.cpu.gpr.rsi.toNat + (toBytesLE (1#32 : BitVec 32) 4).length ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat := by rw [hb]; exact hsa
  exact leaf_ok (c_0 prof) (ret_12 _) (lt_len (by decide)) c hin hK hA hrip (vc_0 fw) rfl hl hin₂ h₂
    (by rw [Tun.rd_Vst V _ _ X.cpu.gpr.rsp 8 h1 hsp h2]; exact hra) k

end FV7z.Nrp
