import FV7z.Ucc.Cuts
import FV7z.Usl.Code
import FV7z.Usl.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::UString (const UString &)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::UString (const UString &s)` at `0x44d5d0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in
`rdi`, `&s` in `rsi`: `SetStartLen (s._len)` (`call` at 19 to `UString::SetStartLen`, `Usl.usl_at`; `_len` is the 4
bytes at `&s + 8`), then a tail jump (43) to `wmemcpy (_chars, s._chars, s._len + 1)` (`Wmc.wmc_at`). `push rbp;
push rbx; sub rsp, 8`, `rbp` = `this` and `rbx` = `&s` across the call, `add rsp, 8; pop rbx; pop rbp` before the jump.

The callees are hypotheses (`kf`, `kr`), as in `FV7z/Usl/Holds.lean` and `FV7z/Sos/Holds.lean`; `Usl.usl_ok` and
`Wmc.wmc_ok` are their contracts.

- `V0`, `gC`: the bytes and the registers at the `call`.
- `gJ`: the registers at the jump.
- `vc_0`, `vc_24`: the verification conditions of the two pieces.
- `ucc_ok`: from the entry, through `SetStartLen`, to `wmemcpy`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ucc

/-- The `call` to `UString::SetStartLen`. -/
def pcall : List Byte := [0xe8, 0x78, 0xfa, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709550200] 5) := by dec_rfl
theorem wc_19 : pcall <+: ucc.drop 19 := by decide +kernel
theorem call_19 (feat : Features) : Dec feat ucc 19 (FV7z.mk .call 64 [.rel 18446744073709550200] 5) :=
  Dec.shift (j := 19) (k := 0) (pcall_0 feat) wc_19 (Nat.zero_le _)
theorem tgt_19 : ucc_at.add (19 + 5) + BitVec.ofNat 64 18446744073709550200 = Usl.usl_at.add 0 := by decide

/-- The jump to `wmemcpy`. -/
def pjm : List Byte := [0xe9, 0x00, 0xfd, 0x20, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2161920] 5) := by dec_rfl
theorem wj_43 : pjm <+: ucc.drop 43 := by decide +kernel
theorem jmp_43 (feat : Features) : Dec feat ucc 43 (FV7z.mk .jmp 64 [.rel 2161920] 5) :=
  Dec.shift (j := 43) (k := 0) (pjm_0 feat) wj_43 (Nat.zero_le _)
theorem tgt_43 : ucc_at.add (43 + 5) + BitVec.ofNat 64 2161920 = Wmc.wmc_at.add 0 := by decide

/-- The bytes at the `call`: `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call`: `rbp` = `this`, `rbx` = `&s`, `esi` = `n` (`s._len`), 24 below the entry. -/
abbrev gC (g : Gprs) (n : BitVec 32) : Gprs :=
  { g with rbp := g.rdi, rbx := g.rsi, rsp := g.rsp - 8 - 8 - 8, rsi := n.setWidth 64 }

/-- The registers at the jump for the bytes `V` after the call (`z` its registers, `x` the entry's): `rdi` =
`_chars`, `rsi` = `s._chars`, `edx` = `s._len + 1`, `rax` = `s._len`, and `rbx`, `rbp`, `rsp` the entry's. -/
abbrev gJ (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with
      rax := (rdd(V, x.rsi + 8#64)).setWidth 64,
      rsi := rdq(V, x.rsi),
      rdi := rdq(V, x.rdi),
      rbx := x.rbx,
      rsp := x.rsp,
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 ((rdd(V, x.rsi + 8#64)).setWidth 64 + 1#64)),
      rbp := x.rbp }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, [rsi + 8]` to the `call` at 19. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fr : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 19 ∧ g' = gC g (rdd(V0 V g, g.rsi + 8#64)) ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 fr ⊢
  wpx [W_0, o0, gC, V0]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov eax, [rbx + 8]; mov rsi, [rbx]; mov rdi, [rbp]; add rsp, 8; pop rbx;
lea edx, [rax + 1]; pop rbp` to the jump at 43. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 43
      { g with
          rax := (rdd(V, g.rbx + 8#64)).setWidth 64,
          rsi := rdq(V, g.rbx),
          rdi := rdq(V, g.rbp),
          rbx := rdq(V, g.rsp + 8#64),
          rsp := g.rsp + 8#64 + 8 + 8,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 ((rdd(V, g.rbx + 8#64)).setWidth 64 + 1#64)),
          rbp := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 fp hl1 hl2 h ⊢
  wpx [W_24, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::UString (const UString &s)` (`this` = `rdi`, `&s` = `rsi`) from its entry. At `SetStartLen`'s entry the
registers are `gC` with `esi` = `s._len`, `rsp` 32 below the entry's, and the bytes `V0` with the return address into
the constructor pushed (`kf`); if the callee returns to `ucc_at + 24` with `rsp`, `rbx`, `rbp` as at its entry and the
saved `rbx`, `rbp` as they were, the run reaches `wmemcpy`'s entry with the registers `gJ` of the bytes then (`kr`). -/
theorem ucc_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ucc_at ucc)
    (hinU : CodeIn L Usl.usl_at Usl.usl) (hinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucc_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (fr8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rsi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat + 8)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucc_at.add 24) 8)) →
      Y.cpu.rip = Usl.usl_at →
      Y.cpu.gpr = (gC X.cpu.gpr (rdd(V, X.cpu.gpr.rsi + 8#64))).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ucc_at.add 24 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V' → Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = gJ V' Z.cpu.gpr X.cpu.gpr →
      GoG prof L o gev gP gE Y t') :
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
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have r16 : X.cpu.gpr.rsp - 24 + 8#64 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have r8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- `s._len` as it was before the pushes
  have x8 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) = rdd(V, X.cpu.gpr.rsi + 8#64) := by
    have a1 := Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsi + 8#64) 4 (by rw [toBytesLE_length, e16, tn16]; omega)
      (by rw [t8]; omega) (by rw [toBytesLE_length, e16, tn16, t8]; omega)
    have a2 := Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rsi + 8#64) 4
      (by rw [toBytesLE_length, tn8]; omega) (by rw [t8]; omega) (by rw [toBytesLE_length, tn8, t8]; omega)
    exact congrArg (ofBytesLE 32) (a1.trans a2)
  have hrip' : X.cpu.rip = ucc_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 19 ∧
      g' = gC X.cpu.gpr (rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64)) ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) fr8) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rw [x8] at hgY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_19 _) hinU (tgt := 0) (Usl.lt_len (by decide))
    tgt_19 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr (rdd(V, X.cpu.gpr.rsi + 8#64))).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC X.cpu.gpr (rdd(V, X.cpu.gpr.rsi + 8#64))).set 4 v) e32
  refine kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hb hp' hPc
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_24 prof).run c hin (fun j' g' _ V'' => j' = 43 ∧ g' = gJ V' Z.cpu.gpr X.cpu.gpr ∧ V'' = V') hKZ hAZ
    hrZ
    (vc_24 (by rw [hzb]; exact fr8) (by rw [hzb]; exact fr0) (by rw [hzp]; exact fd0)
      (by rw [hzs, r16]; exact h16) (by rw [hzs, r16, r8]; exact h8)
      fun _ => ⟨rfl, by rw [hzb, hzp, hzs, r16, r8, e8, hb, hp'], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_43 _) hinW (Wmc.lt_len (j := 0) (by decide))
    tgt_43 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact kr Z V' Y₃ t₄ hPc hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (by rw [hg₃, hgU])

end FV7z.Ucc
