import FV7z.Ar3.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CInFileStream::AddRef` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::AddRef` at `0x5a48a0` in `7zzs`
(`Z7_COM_ADDREF_RELEASE`, `CPP/Common/MyCom.h`): the reference count at `this + 40` one more,
and returned (`Fn.addref_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ar3

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_13 : pret <+: ar3.drop 13 := by decide +kernel
theorem ret_13 (feat : Features) : Dec feat ar3 13 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 13) (k := 0) (pret_0 feat) w_13 (Nat.zero_le _)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFileStream::AddRef` from its entry to the return address: `Fn.addref_ok` with the
count at `this + 40`. -/
theorem ar3_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ar3_at ar3) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ar3_at)
    (fa : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 40) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 40) i))
    (hfa : (X.cpu.gpr.rdi + BitVec.ofNat 64 40).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (X.cpu.gpr.rdi + BitVec.ofNat 64 40).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + BitVec.ofNat 64 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rdi + BitVec.ofNat 64 40)
        (toBytesLE (arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 40) + 1#32) 4)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (X.cpu.gpr.set 0 ((arCnt V (X.cpu.gpr.rdi + BitVec.ofNat 64 40) + 1#32).setWidth 64)).set 4
        (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  addref_ok (d := 40) (c_0 prof) (ret_13 _) (lt_len (by decide)) c hin hK hA hrip fa fw hfa hl hsp hsa
    hin₂ h₂ hra k

end FV7z.Ar3
