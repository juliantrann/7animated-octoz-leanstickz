import FV7z.Iag.Cuts
import FV7z.Isb.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `InStream_AtBegin_GetSize` (PLAN.md §M, M1)

7-Zip 26.06's `InStream_AtBegin_GetSize (stream, size)` at `0x463200` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`):
`push r12; push rbp; sub rsp, 8`, `res = stream->Seek (0, STREAM_SEEK_END, &size)` (`call qword [rax + 0x20]` at 27
through the vtable, `rcx` = `size`, `edx` = 2, `esi` = 0, `rbp` = `stream`), then `res2 = InStream_SeekToBegin (stream)`
(`call` at 36 to `Isb.isb_at`), `return res ? res : res2` (`test r12d, r12d; cmove r12d, eax`), `pop rbp; pop r12; ret`
(58).

Both callees are hypotheses, as in `FV7z/Lfp/Holds.lean` and `FV7z/Vcl/Holds.lean`: continuations at their entries
(`kf1`, `kf2`), each given the run from its return to the next piece. `Pc`, `Pc2` are what the callees leave.

- `gC`, `V0`: the registers and the bytes at the first `call`; `zl`: `res` in `r12` across the second.
- `res`: the answer, `res ? res : res2`.
- `vc_0`, `vc_30`, `vc_41`: the verification conditions of the three pieces.
- `iag_ok`: from the entry, through both callees, to the return address with `eax` = `res` and `rbp`, `r12`, `rsp`
  restored (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Iag

/-- The `call qword [rax + 0x20]` (`IInStream::Seek`). -/
def pcm : List Byte := [0xff, 0x50, 0x20]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 32 64)] 3) := by dec_rfl
theorem wm_27 : pcm <+: iag.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat iag 27 (FV7z.mk .call 64 [.mem (mbd 0 32 64)] 3) :=
  Dec.shift (j := 27) (k := 0) (pcm_0 feat) wm_27 (Nat.zero_le _)

/-- The `call` to `InStream_SeekToBegin`. -/
def pcall : List Byte := [0xe8, 0xb7, 0xff, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709551543] 5) := by dec_rfl
theorem wc_36 : pcall <+: iag.drop 36 := by decide +kernel
theorem call_36 (feat : Features) : Dec feat iag 36 (FV7z.mk .call 64 [.rel 18446744073709551543] 5) :=
  Dec.shift (j := 36) (k := 0) (pcall_0 feat) wc_36 (Nat.zero_le _)
theorem tgt_36 : iag_at.add (36 + 5) + BitVec.ofNat 64 18446744073709551543 = Isb.isb_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_58 : pret <+: iag.drop 58 := by decide +kernel
theorem ret_58 (feat : Features) : Dec feat iag 58 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)

/-- The low 32 bits, zero-extended. -/
abbrev zl (a : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 a)

/-- `res ? res : res2` of 32 bits. -/
abbrev res (a b : BitVec 64) : BitVec 32 :=
  if (BitVec.setWidth 32 a == 0) = true then BitVec.setWidth 32 b else BitVec.setWidth 32 a

/-- The registers at the first `call`: `rax` the vtable, `rcx` = `size`, `rdx` = 2, `rsi` = 0, `rbp` = `stream`,
`r12` and `rbp` pushed and 8 bytes more. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rax := rdq(V, g.rdi),
      rcx := g.rsi,
      rdx := 2#64,
      rbp := g.rdi,
      rsp := g.rsp - 8 - 8 - 8,
      rsi := 0#64 }

/-- The bytes at the first `call`: `r12` and `rbp` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov rcx, rsi; mov edx, 2; xor esi, esi; push rbp; mov rbp, rdi; sub rsp, 8; mov rax, [rdi]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hx : rdq(Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8), g.rdi) =
      rdq(V, g.rdi)) :
    W_0 F Wl (fun j' g' _ V' => j' = 27 ∧ g' = gC V g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 fa hx ⊢
  wpx [W_0, o0, gC, V0, hx, BitVec.xor_self, BitVec.reduceSetWidth]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `Seek`: `mov rdi, rbp; mov r12d, eax` to the second `call`. -/
theorem vc_30 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_30 F Wl (fun j' g' _ V' => j' = 36 ∧ g' = { g with rdi := g.rbp, r12 := zl g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_30, o1]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `InStream_SeekToBegin`: `test r12d, r12d; cmove r12d, eax; add rsp, 8; pop rbp; mov eax, r12d;
pop r12` to the `ret` at 58. -/
theorem vc_41 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 58
      { g with
          rax := BitVec.setWidth 64 (res g.r12 g.rax),
          rbp := rdq(V, g.rsp + 8#64),
          rsp := g.rsp + 8#64 + 8 + 8,
          r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_41 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_41, o2, BitVec.and_self]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `InStream_AtBegin_GetSize (stream, size)` (`rdi`, `rsi`) from its entry. At `Seek`'s entry `eF` (the 8 bytes at
the vtable + 0x20) the registers are `gC` with `rsp` 32 below the entry's and the bytes `V0` with the return address
pushed (`kf1`); if `Seek` returns to `iag_at + 30` with `rsp`, `rbp` as at its entry and the saved registers and the
return address as they were, the run reaches `InStream_SeekToBegin`'s entry with `rdi` = `stream`, `r12` = `res` and
the return address `iag_at + 41` pushed (`kf2`); if that returns with `rsp`, `r12` as at its entry and the saved
registers and the return address as they were, the run reaches the return address with `eax` = `res ? res : res2`
and `rbp`, `r12`, `rsp` restored (`kr`). No bytes but the frame's are stored. -/
theorem iag_ok {Pc : State → (Addr → Byte) → Prop} {Pc2 : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L iag_at iag) (hinI : CodeIn L Isb.isb_at Isb.isb)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = iag_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hqa : X.cpu.gpr.rdi.toNat + 8 ≤ 2 ^ 64)
    (hda : X.cpu.gpr.rdi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (fb : ∀ i < 8, Foot F.data (Addr.add (rdq(V, X.cpu.gpr.rdi) + 32#64) i))
    (hqb : (rdq(V, X.cpu.gpr.rdi) + 32#64).toNat + 8 ≤ 2 ^ 64)
    (hdb : (rdq(V, X.cpu.gpr.rdi) + 32#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨
      X.cpu.gpr.rsp.toNat ≤ (rdq(V, X.cpu.gpr.rdi) + 32#64).toNat)
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(V, rdq(V, X.cpu.gpr.rdi) + 32#64) = eF)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (iag_at.add 30) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = iag_at.add 30 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), Pc Z V' →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
      rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (iag_at.add 41) 8)) →
      Y.cpu.rip = Isb.isb_at →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := X.cpu.gpr.rdi, r12 := zl Z.cpu.gpr.rax }).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = iag_at.add 41 → W.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → W.cpu.gpr.r12 = zl Z.cpu.gpr.rax →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V'', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (W : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat),
      Pc Z V' → Pc2 Z W V'' → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (res Z.cpu.gpr.rax W.cpu.gpr.rax),
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8,
          r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32b : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by rw [e24, e32b]
  have r16 : X.cpu.gpr.rsp - 24 + 8#64 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have r8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  -- the bytes outside the pushed `r12` and `rbp`
  have m8 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x 8).map (V0 V X.cpu.gpr) = (byteAddrs x 8).map V := by
    intro x hx h
    have a1 := Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8) x 8 (by rw [toBytesLE_length, e16, tn16]; omega) hx
      (by rw [toBytesLE_length, e16, tn16]; omega)
    have a2 := Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) x 8 (by rw [toBytesLE_length, tn8]; omega)
      hx (by rw [toBytesLE_length, tn8]; omega)
    exact a1.trans a2
  have hx : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by rw [m8 X.cpu.gpr.rdi hqa hda]
  have hrip' : X.cpu.rip = iag_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 27 ∧ g' = gC V X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) fa hx) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
  have he : eaD Y 0 32 = rdq(V, X.cpu.gpr.rdi) + 32#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 32 = _
    rw [hgY]
    rfl
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_27 _) (by rw [he]; exact fb) hinF hF0
    (by rw [he, m8 _ hqb hdb]; exact htgt) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e32
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `Seek`
  intro Z V' t'' hKZ hAZ hrZ hzs hzp hb1 hb2 hr' hPc
  refine (c_30 prof).run c hin (fun j' g' _ V'' => j' = 36 ∧
      g' = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbp, r12 := zl Z.cpu.gpr.rax } ∧ V'' = V') hKZ hAZ hrZ vc_30 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hgU' : U.cpu.gpr = { Z.cpu.gpr with rdi := X.cpu.gpr.rdi, r12 := zl Z.cpu.gpr.rax } := by
    rw [hgU, hzp]
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU']; exact hzs
  have hst' : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, e32b]; exact hs4
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_36 _) hinI (Isb.lt_len (by decide)) tgt_36 hst' ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU, e32b] at hA₃
  have h32 : Z.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hzs, e32b]
  have hg₃' : Y₃.cpu.gpr =
      ({ Z.cpu.gpr with rdi := X.cpu.gpr.rdi, r12 := zl Z.cpu.gpr.rax }).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₃, hgU']
    exact congrArg (fun v => ({ Z.cpu.gpr with rdi := X.cpu.gpr.rdi, r12 := zl Z.cpu.gpr.rax }).set 4 v) h32
  refine kf2 Z V' Y₃ t₄ hPc hzs hb1 hb2 hr' hK₃ hA₃ hr₃ hg₃' ?_
  -- back from `InStream_SeekToBegin`
  intro W V'' t₅ hKW hAW hrW hws hw12 hc1 hc2 hcr hPc2
  have hres : res (zl Z.cpu.gpr.rax) W.cpu.gpr.rax = res Z.cpu.gpr.rax W.cpu.gpr.rax := by
    simp only [res, zl, sw_64_32]
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_41 prof).run c hin (fun j' g' _ V₃ => j' = 58 ∧
      g' = { W.cpu.gpr with
          rax := BitVec.setWidth 64 (res Z.cpu.gpr.rax W.cpu.gpr.rax),
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp,
          r12 := X.cpu.gpr.r12 } ∧ V₃ = V'') hKW hAW hrW
    (vc_41 (by rw [hws, r16]; exact h16) (by rw [hws, r16, r8]; exact h8)
      fun _ => ⟨rfl, by rw [hw12, hres, hws, r16, r8, e8, hc2, hc1], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₄
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_58 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hcr) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' W V'' Z' t₇ hPc hPc2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Iag
