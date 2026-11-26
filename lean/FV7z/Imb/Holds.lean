import FV7z.Imb.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `_IO_default_imbue` (PLAN.md §M, M1)

glibc 2.31's `_IO_default_imbue` at `0x5ab370` in `7zzs` (`libio/genops.c`; `objdump -d`): `endbr64; ret`, nothing
done.

- `imb_ok`: from the entry to the return address, the registers but `rsp` and the memory kept (`Fn.leaf_ok`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Imb

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_4 : pret <+: imb.drop 4 := by decide +kernel
theorem ret_4 (feat : Features) : Dec feat imb 4 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 4) (k := 0) (pret_0 feat) w_4 (Nat.zero_le _)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `endbr64`. -/
theorem vc_0 {g : Gprs} {f : Rflags} : wp F Wl o0 (fun g' _ V' => g' = g ∧ V' = V) g f V := by
  wpx [o0]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- `_IO_default_imbue (fp, locale)` from its entry: at the return address, the return address popped, nothing
else changed. -/
theorem imb_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L imb_at imb) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imb_at) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  leaf_ok (G := X.cpu.gpr) (c_0 prof) (ret_4 _) (lt_len (by decide)) c hin hK hA hrip vc_0 rfl hl hin₂ h₂ hra k

end FV7z.Imb
