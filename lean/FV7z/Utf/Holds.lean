import FV7z.Utf.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps4
/-!
# `NWindows::NTime::UnixTime64_To_FileTime64` (PLAN.md §M, M1)

7-Zip 26.06's `UnixTime64_To_FileTime64` at `0x458880` in `7zzs` (`CPP/Windows/TimeUtils.cpp`): the Unix time in
`rdi` plus the seconds from 1601 to 1970 (11644473600), times 10⁷ (100 ns steps), modulo 2⁶⁴, in `rax`.

- `ftV`: that value; `utf_ok`: from the entry to the return address with `rax` = `ftV rdi`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Utf

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_24 : pret <+: utf.drop 24 := by decide +kernel
theorem ret_24 (feat : Features) : Dec feat utf 24 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 24) (k := 0) (pret_0 feat) w_24 (Nat.zero_le _)

/-- The file time of the Unix time `r`: `(r + 11644473600) · 10⁷` at 64 bits. -/
def ftV (r : BitVec 64) : BitVec 64 := (11644473600#64 + r) * 10000000#64

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov rax, 11644473600; add rax, rdi; imul rax, rax, 10000000`. -/
theorem vc_0 {g : Gprs} {f : Rflags} :
    wp F Wl o0 (fun g' _ V' => g' = g.set 0 (ftV g.rdi) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o0, Op.imul3, imul64_eq]
  first
  | rfl
  | exact fun _ => rfl
  | (intro _; unfold ftV; rw [← imul64_eq]; rfl)
  | (intro _; unfold ftV; rw [← imul64_eq]; exact rfl)
  | (intro _; rw [show ftV rdi = BitVec.setWidth 64 (BitVec.signExtend 128 (11644473600#64 + rdi) *
      BitVec.signExtend 128 10000000#64) from (imul64_eq _ _).symm]; rfl)
  | (trace_state; done)

/-- `rsp` after `rax` is written (by the structure, not by the value: the kernel would evaluate it). -/
theorem set0_rsp (g : Gprs) (v : BitVec 64) : (g.set 0 v).rsp = g.rsp := rfl

/-- `UnixTime64_To_FileTime64` from its entry to the return address: `rax` = `ftV rdi`. -/
theorem utf_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L utf_at utf) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = utf_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (X.cpu.gpr.set 0 (ftV X.cpu.gpr.rdi)).set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  leaf_ok (c_0 prof) (ret_24 _) (lt_len (by decide)) c hin hK hA hrip vc_0 (set0_rsp _ _) hl hin₂ h₂ hra k

end FV7z.Utf
