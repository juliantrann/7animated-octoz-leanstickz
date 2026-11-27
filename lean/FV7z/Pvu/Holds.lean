import FV7z.Pvu.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr24
/-!
# `CPropVariant::operator=(UInt32)` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NCOM::CPropVariant::operator=(UInt32)` at `0x457430` in `7zzs`
(`CPP/Windows/PropVariant.cpp`), `p` = `rdi` (`this`), `u` = `esi`:
`push r12; mov r12, rdi; push rbx; mov ebx, esi; sub rsp, 8; cmp word [rdi], 19; je 37`; at 22 `call 0x457130`
(`InternalClear`, `FV7z/Pic`); at 27 `mov edx, 19; mov [r12], dx`; at 37 `xor eax, eax; mov [r12 + 8], ebx;
mov [r12 + 2], ax; add rsp, 8; mov rax, r12; pop rbx; pop r12; ret` (60). Cuts 0, 27, 37 (kt632).

The wpx goals (kt632 probe):
- `W_0`: `Foot Wl` of `rsp - 8` and `rsp - 8 - 8` (8 bytes), `Foot F.data` of `rdi` (2 bytes); then
  `decide (rdw(Vp, rdi) = 19#16) = true → Q 37 …` and `= false → Q 22 …`, both with
  `{ g with rbx := sw64 (sw32 rsi), rsp := rsp - 8 - 8 - 8#64, r12 := rdi }` and
  `Vp = Vst (Vst V (rsp - 8) (toBytesLE r12 8)) (rsp - 8 - 8) (toBytesLE rbx 8)`.
- `W_27`: `Foot Wl` of `r12` (2 bytes) ∧ `Q 37 { g with rdx := sw64 19#32 } …
  (Vst V r12 (toBytesLE (sw16 19#32) 2))`.
- `W_37`: `∀ af,` `Foot Wl` of `r12 + 8#64` (4) and `r12 + 2#64` (2), `Foot F.data` of `rsp + 8#64` and
  `rsp + 8#64 + 8` (8) ∧ `Q 60` with `rax := r12`, `rbx`/`r12` the loads at `rsp + 8#64` and `rsp + 8#64 + 8` of
  `Vs = Vst (Vst V (r12 + 8#64) (toBytesLE (sw32 rbx) 4)) (r12 + 2#64) (toBytesLE (sw16 (sw32 rax ^^^ sw32 rax)) 2)`,
  `rsp := rsp + 8#64 + 8 + 8`.

Design (as `FV7z/Pic/Holds.lean`): the callee is a hypothesis (`kf`), a continuation at its entry, given the run
from its return (`pvu_at + 27`, `rsp` 24 below the entry's, `rbx` = `u`, `r12` = `p`, the saved `rbx`, `r12` and the
return address left as they were, and the callee's own post `Pc`) to the return address (`kr`). The pieces' VCs take
an opaque `Q` and the post as a hypothesis (`h37`/`h22` for the branch, as `Caa.vc_0`); the run posts are closed
with `⟨rfl, …⟩` and `show`-free `rw` on the named register equations. Address facts are the standalone `bv_omega`
lemmas of `FV7z/Lemmas/Fr24.lean` (`pe16` …), rewritten before `omega`.
- `vtw V a`: the 2 bytes at `a` (the type tag `vt` at `p`); `gN g`: the registers after the prologue.
- `pvu_ok`: from the entry to the return address, directly when `vt` is already `VT_UI4` (19, `kz`), else through
  the callee (`kf`, `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Pvu

theorem pvu_22 : ∀ feat, Dec feat pvu 22 (FV7z.mk .call 64 [.rel 18446744073709550821] 5) := by intro feat f; rfl
theorem pvu_60 : ∀ feat, Dec feat pvu 60 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The 2 bytes at `a`. -/
abbrev vtw (V : Addr → Byte) (a : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs a 2).map V)

/-- The registers after the prologue: `r12` = `p`, `rbx` = `u`, `rsp` 24 down. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with
    rbx := (g.rsi.setWidth 32).setWidth 64
    rsp := g.rsp - 8 - 8 - 8#64
    r12 := g.rdi }

theorem sw19 : (19#32).setWidth 64 = 19#64 := by decide
theorem sw19a : (19#32).setWidth 16 = 19#16 := by decide
theorem sw19b : (19#64).setWidth 16 = 19#16 := by decide

/-! ## Address arithmetic, one small fact each -/

theorem pd2 (p : BitVec 64) (h : p.toNat + 12 ≤ 2 ^ 64) : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
theorem pd8 (p : BitVec 64) (h : p.toNat + 12 ≤ 2 ^ 64) : (p + 8#64).toNat = p.toNat + 8 := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; push rbx; mov ebx, esi; sub rsp, 8; cmp word [rdi], 19; je`: to 37 if `vt` (after the
pushes) is 19, else to the `call` at 22. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h37 : vtw (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) g.rdi = 19#16 →
      ∀ fl, Q 37 (gN g) fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)))
    (h22 : ¬ vtw (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) g.rdi = 19#16 →
      ∀ fl, Q 22 (gN g) fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw, gN] at hs1 hs2 ft h37 h22 ⊢
  wpx [W_0, o0, Op.cmpmi, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact h37 h _)
    | (intro h; exact h22 h _)
    | apply And.intro
    | intro _

/-- `mov edx, 19; mov [r12], dx`, to 37. -/
theorem vc_27 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fw : ∀ i < 2, Foot Wl (Addr.add g.r12 i))
    (h : ∀ fl, Q 37 { g with rdx := 19#64 } fl (Vst V g.r12 (toBytesLE 19#16 2))) : W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_27, o1, sw19, sw19a, sw19b]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax; mov [r12 + 8], ebx; mov [r12 + 2], ax; add rsp, 8; mov rax, r12; pop rbx; pop r12`, to the `ret`
at 60. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 8#64) i)) (fw2 : ∀ i < 2, Foot Wl (Addr.add (g.r12 + 2#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 60
      { g with
        rax := g.r12
        rbx := rdq(Vst (Vst V (g.r12 + 8#64) (toBytesLE (g.rbx.setWidth 32) 4)) (g.r12 + 2#64) (toBytesLE 0#16 2),
          g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(Vst (Vst V (g.r12 + 8#64) (toBytesLE (g.rbx.setWidth 32) 4)) (g.r12 + 2#64) (toBytesLE 0#16 2),
          g.rsp + 8#64 + 8) } fl
      (Vst (Vst V (g.r12 + 8#64) (toBytesLE (g.rbx.setWidth 32) 4)) (g.r12 + 2#64) (toBytesLE 0#16 2))) :
    W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw8 fw2 hl1 hl2 h ⊢
  wpx [W_37, o2, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::operator=(UInt32)` (`p` = `rdi`, `u` = `esi`) from its entry, `r12` and `rbx` saved at `rsp - 8`
and `rsp - 16`. `vt` already 19 (`VT_UI4`): at the return address with `ulVal` (the 4 bytes at `p + 8`) = `u`,
`wReserved1` (the 2 bytes at `p + 2`) = 0, `rax` = `p`, the other registers as at the entry (`kz`). Else at the
callee's entry (`0x457130`) with the registers `gN` and the return address `pvu_at + 27` at `rsp - 32` (`kf`); if the
callee returns there with `rsp`, `rbx`, `r12` as it found them and the saved registers and the return address left
as they were, the run reaches the return address with also `vt` = 19 and `rdx` = 19 (`kr`). -/
theorem pvu_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pvu_at pvu)
    {codeC : List Byte} (hinC : CodeIn L 0x457130#64 codeC) (hC0 : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pvu_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw : ∀ i < 2, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw2 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : vtw V X.cpu.gpr.rdi = 19#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem
        (Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
          (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4))
          (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : vtw V X.cpu.gpr.rdi ≠ 19#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 32) (toBytesLE (pvu_at.add 27) 8)) →
      Y.cpu.rip = 0x457130#64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pvu_at.add 27 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 →
        Z.cpu.gpr.rbx = (X.cpu.gpr.rsi.setWidth 32).setWidth 64 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rdx := 19#64
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have t8 := pt8 _ hp
  have t16 := pt16 _ hp
  have d2 := pd2 _ hq
  have d8 := pd8 _ hq
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  -- reads of 8 bytes past the stores
  have mS1 : ∀ (W : Addr → Byte) (v : BitVec 64) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rsp - 8) (toBytesLE v 8)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)
  have mS2 : ∀ (W : Addr → Byte) (v : BitVec 64) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ x.toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rsp - 16) (toBytesLE v 8)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, t16]; omega) hx
      (by rw [toBytesLE_length, t16]; omega)
  have m0 : ∀ (W : Addr → Byte) (v : BitVec 16) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 2 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (Vst W X.cpu.gpr.rdi (toBytesLE v 2)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)
  have m2 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 4 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 2) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, d2]; omega) hx
      (by rw [toBytesLE_length, d2]; omega)
  have m8 : ∀ (W : Addr → Byte) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 4)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, d8]; omega) hx
      (by rw [toBytesLE_length, d8]; omega)
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [t8]; omega
  have hq16 : (X.cpu.gpr.rsp - 16).toNat + 8 ≤ 2 ^ 64 := by rw [t16]; omega
  -- `vt` after the pushes is `vt` at the entry
  have hx2 : X.cpu.gpr.rdi.toNat + 2 ≤ 2 ^ 64 := by omega
  have ha8 : (X.cpu.gpr.rsp - 8).toNat + (toBytesLE X.cpu.gpr.r12 8).length ≤ 2 ^ 64 := by
    rw [toBytesLE_length, t8]; omega
  have ha16 : (X.cpu.gpr.rsp - 16).toNat + (toBytesLE X.cpu.gpr.rbx 8).length ≤ 2 ^ 64 := by
    rw [toBytesLE_length, t16]; omega
  have hd8 : (X.cpu.gpr.rsp - 8).toNat + (toBytesLE X.cpu.gpr.r12 8).length ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + 2 ≤ (X.cpu.gpr.rsp - 8).toNat := by
    rw [toBytesLE_length, t8]; omega
  have hd16 : (X.cpu.gpr.rsp - 16).toNat + (toBytesLE X.cpu.gpr.rbx 8).length ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + 2 ≤ (X.cpu.gpr.rsp - 16).toNat := by
    rw [toBytesLE_length, t16]; omega
  have hvt : vtw (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi = vtw V X.cpu.gpr.rdi := by
    dsimp only [vtw]
    rw [pe16, Tun.rd_Vst _ _ _ _ 2 ha16 hx2 hd16, Tun.rd_Vst _ _ _ _ 2 ha8 hx2 hd8]
  have hrip' : X.cpu.rip = pvu_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases ht : vtw V X.cpu.gpr.rdi = 19#16
  · -- `vt` 19: to 37, then the `ret` at 60
    have hrb : rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4))
        (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
      rw [m2 _ _ hq16 (by rw [t16]; omega), m8 _ _ _ hq16 (by rw [t16]; omega),
        Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq16, ofBytesLE_toBytesLE (n := 8) rfl]
    have hr12 : rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4))
        (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
      rw [m2 _ _ hq8 (by rw [t8]; omega), m8 _ _ _ hq8 (by rw [t8]; omega), mS2 _ _ _ hq8 (by rw [t8]; omega),
        Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8, ofBytesLE_toBytesLE (n := 8) rfl]
    have hrz : rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4))
        (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [m2 _ _ hp8 (by omega), m8 _ _ _ hp8 (by omega), mS2 _ _ _ hp8 (by omega), mS1 _ _ _ hp8 (by omega)]
      exact hra
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧ g' = gN X.cpu.gpr ∧
        V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
          (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip'
      (vc_0 hs1 (by rw [pe16]; exact hs2) ft (fun _ _ => ⟨rfl, rfl, by rw [pe16]⟩)
        (fun hn => absurd (hvt.trans ht) hn)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgU]
    have h12U : U.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgU]
    refine (c_37 prof).run c hin (fun j' g' _ V' => j' = 60 ∧
        g' = { X.cpu.gpr with
          rax := X.cpu.gpr.rdi
          rsp := X.cpu.gpr.rsp } ∧
        V' = Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
          (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4))
          (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) hKU hAU hrU
      (vc_37 (by rw [h12U]; exact fw8) (by rw [h12U]; exact fw2) (by rw [hsU, peA]; exact h16)
        (by rw [hsU, peA, peB]; exact h8)
        fun _ => ⟨rfl, by rw [hgU]; dsimp only; rw [sw_64_32, peA, peB, peC, hrb, hr12],
          by rw [hgU]; dsimp only; rw [sw_64_32]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₂
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (pvu_60 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hrz) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kz ht Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU₂]
    try rfl
  · -- `vt` not 19: to the `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ g' = gN X.cpu.gpr ∧
        V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
          (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip'
      (vc_0 hs1 (by rw [pe16]; exact hs2) ft (fun h => absurd (hvt.symm.trans h) ht)
        (fun _ _ => ⟨rfl, rfl, by rw [pe16]⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, pe32]; exact hs4
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (pvu_22 _) hinC hC0 (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, pe32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gN X.cpu.gpr).set 4 v) (pe32 X.cpu.gpr.rsp)
    refine kf ht Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee, at 27
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hz12 hb hr12 hr' hPc
    refine (c_27 prof).run c hin (fun j' g' _ V'' => j' = 37 ∧ g' = { Z.cpu.gpr with rdx := 19#64 } ∧
        V'' = Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) hKZ hAZ hrZ
      (vc_27 (by rw [hz12]; exact fw) fun _ => ⟨rfl, rfl, by rw [hz12]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hbK : rdq(Vst (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp - 16) =
        X.cpu.gpr.rbx := by
      rw [m2 _ _ hq16 (by rw [t16]; omega), m8 _ _ _ hq16 (by rw [t16]; omega), m0 _ _ _ hq16 (by rw [t16]; omega)]
      exact hb
    have h12K : rdq(Vst (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp - 8) =
        X.cpu.gpr.r12 := by
      rw [m2 _ _ hq8 (by rw [t8]; omega), m8 _ _ _ hq8 (by rw [t8]; omega), m0 _ _ _ hq8 (by rw [t8]; omega)]
      exact hr12
    have hrK : rdq(Vst (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2), X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [m2 _ _ hp8 (by omega), m8 _ _ _ hp8 (by omega), m0 _ _ _ hp8 (by omega)]
      exact hr'
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
    have h12U : U.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgU]; exact hz12
    refine (c_37 prof).run c hin (fun j' g' _ V'' => j' = 60 ∧
        g' = { Z.cpu.gpr with
          rax := X.cpu.gpr.rdi
          rdx := 19#64
          rbx := X.cpu.gpr.rbx
          rsp := X.cpu.gpr.rsp
          r12 := X.cpu.gpr.r12 } ∧
        V'' = Vst (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 19#16 2)) (X.cpu.gpr.rdi + 8#64)
          (toBytesLE (X.cpu.gpr.rsi.setWidth 32) 4)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) hKU hAU hrU
      (vc_37 (by rw [h12U]; exact fw8) (by rw [h12U]; exact fw2) (by rw [hsU, peA']; exact h16)
        (by rw [hsU, peA', peB]; exact h8)
        fun _ => ⟨rfl, by rw [hgU]; dsimp only; rw [hzs, hz12, hzb, sw_64_32, peA', peB, peC, hbK, h12K],
          by rw [hgU]; dsimp only; rw [hz12, hzb, sw_64_32]⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₃
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (pvu_60 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hrK) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₂]
    try rfl

end FV7z.Pvu
