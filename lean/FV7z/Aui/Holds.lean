import FV7z.Aui.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `AString::Add_UInt32 (v)` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Add_UInt32 (UInt32 v)` at `0x44c980` in `7zzs` (`CPP/Common/MyString.cpp`), `this` = `rdi`,
`v` = `esi`, `S` the entry's `rsp`: `push rbp; mov ebp, esi; mov esi, 10; push rbx; mov rbx, rdi; sub rsp, 8`
(`aR S`, `V1`, `gC`), `Grow (10)` (`call` at 20 to `0x44c0e0`); back at 25 `esi` = `_len`, `edi` = `v`,
`rsi += _chars` (`g25`), `ConvertUInt32ToString (v, _chars + _len)` (`call` at 33 to `0x44ab70`); back at 38
`rax -= _chars`, `_len` = `eax` (the store at `rbx + 8`), `add rsp, 8; pop rbx; pop rbp`; the `ret` (50).

The callees are hypotheses, as in `FV7z/Ain/Holds.lean`: each a continuation at its entry (`kf1`, `kf2`), given the
run from its return; `Pc1`, `Pc2` are what they leave. The second's return gives the saved registers and the return
address in the bytes it leaves.

- `aR`, `V1`, `gC`, `g25`, `Wst`: the frame's `rsp`; the bytes with the two pushes; the registers at the two
  `call`s; the bytes with `_len` stored.
- `vc_0`, `vc_25`, `vc_38`: the pieces from the entry, from 25 and from 38.
- `aui_ok`: through both callees and the store to the return address with `rbx`, `rbp`, `rsp` restored (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aui

/-- `AString::Grow`. -/
abbrev grow_at : Addr := 0x44c0e0

/-- `ConvertUInt32ToString`. -/
abbrev cvt_at : Addr := 0x44ab70

/-- The `call` to `Grow`. -/
def pcg : List Byte := [0xe8, 0x47, 0xf7, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709549383] 5) := by dec_rfl
theorem wc_20 : pcg <+: aui.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat aui 20 (FV7z.mk .call 64 [.rel 18446744073709549383] 5) :=
  Dec.shift (j := 20) (k := 0) (pcg_0 feat) wc_20 (Nat.zero_le _)
theorem tgt_20 : aui_at.add (20 + 5) + BitVec.ofNat 64 18446744073709549383 = grow_at := by decide

/-- The `call` to `ConvertUInt32ToString`. -/
def pcc : List Byte := [0xe8, 0xca, 0xe1, 0xff, 0xff]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 18446744073709543882] 5) := by dec_rfl
theorem wc_33 : pcc <+: aui.drop 33 := by decide +kernel
theorem call_33 (feat : Features) : Dec feat aui 33 (FV7z.mk .call 64 [.rel 18446744073709543882] 5) :=
  Dec.shift (j := 33) (k := 0) (pcc_0 feat) wc_33 (Nat.zero_le _)
theorem tgt_33 : aui_at.add (33 + 5) + BitVec.ofNat 64 18446744073709543882 = cvt_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_50 : pret <+: aui.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat aui 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `push rbp; push rbx; sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8#64

/-- The bytes with `rbp`, `rbx` pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call` of `Grow`: `rbx` = `this`, `ebp` = `v`, `esi` = 10. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rsp := aR g.rsp,
      rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
      rsi := BitVec.setWidth 64 (BitVec.ofNat 32 10) }

/-- The registers at the `call` of `ConvertUInt32ToString`: `rsi` = `_chars + _len`, `edi` = `v` (`ebp`). -/
abbrev g25 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
      rsi := BitVec.setWidth 64 rdd(V, g.rbx + 8#64) + rdq(V, g.rbx),
      rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp) }

/-- The bytes with `_len` (at `rbx + 8`) stored: the low half of `rax - _chars`. -/
abbrev Wst (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V (g.rbx + 8#64) (toBytesLE (BitVec.setWidth 32 (g.rax - rdq(V, g.rbx))) 4)

theorem aE1 (s : Addr) : aR s + 8#64 = s - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE3 (s : Addr) : s - 8 - 8 + 8 = s - 8 := BitVec.sub_add_cancel _ _
theorem aE4 (s : Addr) : s - 8 + 8 = s := BitVec.sub_add_cancel _ _

theorem aT8 (s : BitVec 64) (h : 24 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem aT16 (s : BitVec 64) (h : 24 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem aTr8 (x : BitVec 64) (h : x.toNat + 12 ≤ 2 ^ 64) : (x + 8#64).toNat = x.toNat + 8 := by bv_omega

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry's code: the two pushes, the moves and `sub rsp, 8`, up to the `call` at 20. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ fl, Q 20 (gC g) fl (V1 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, aR, V1] at hs1 hs2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `Grow`, at 25: `mov esi, [rbx + 8]; mov edi, ebp; add rsi, [rbx]` to the `call` at 33. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (fc : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ fl, Q 33 (g25 g V) fl V) : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g25] at fl fc h ⊢
  wpx [W_25, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `ConvertUInt32ToString`, at 38: `sub rax, [rbx]; mov [rbx + 8], eax; add rsp, 8; pop rbx; pop rbp`
to the `ret` at 50. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fc : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (fw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 50
      { g with
          rax := g.rax - rdq(V, g.rbx),
          rbx := rdq(Wst V g, g.rsp + 8#64),
          rsp := g.rsp + 8#64 + 8 + 8,
          rbp := rdq(Wst V g, g.rsp + 8#64 + 8) } fl (Wst V g)) :
    W_38 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Wst] at fc fw l1 l2 h ⊢
  wpx [W_38, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Add_UInt32 (v)` (`this` = `rdi`, `v` = `esi`) from its entry, `S` = `rsp`: at `Grow`'s entry with the
registers `gC`, the bytes `V1` and the return address `aui_at + 25` at `aR S - 8` (`kf1`); from its return (`rsp` =
`aR S`, `rbx` = `this`, `ebp` = `v`, the post `Pc1`) at `ConvertUInt32ToString`'s entry with the registers `g25` and
the return address `aui_at + 38` (`kf2`); from its return (`rsp` = `aR S`, `rbx` = `this`, the saved registers and
the return address in its bytes, the post `Pc2`) through `_len` = `rax - _chars` to the return address with `rbx`,
`rbp`, `rsp` restored (`kr`). -/
theorem aui_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aui_at aui)
    {codeG : List Byte} (hinG : CodeIn L grow_at codeG) (hG : 0 < codeG.length)
    {codeC : List Byte} (hinC : CodeIn L cvt_at codeC) (hC : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aui_at)
    (hp : 24 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (aR X.cpu.gpr.rsp - 8) (toBytesLE (aui_at.add 25) 8)) →
      Y.cpu.rip = grow_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = aui_at.add 25 → Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi) → Pc1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      Z.cpu.gpr.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi) → Pc1 Z V' →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (aR X.cpu.gpr.rsp - 8) (toBytesLE (aui_at.add 38) 8)) →
      Y.cpu.rip = cvt_at → Y.cpu.gpr = (g25 Z.cpu.gpr V').set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = aui_at.add 38 → Z₂.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V₂, X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbx → rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (BitVec.setWidth 32 (Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi))) 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi),
        rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = aui_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the entry's code, to the `call` of `Grow`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gC X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 hs2 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_20 _) hinG hG tgt_20 (by rw [hsY]; exact hs3) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₂, hsY, hgY]
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `Grow`, at 25: to the `call` of `ConvertUInt32ToString`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hP1
  refine (c_25 prof).run c hin (fun j' g' _ V'' => j' = 33 ∧ g' = g25 Z.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
    (vc_25 (by rw [hzb]; exact fl) (by rw [hzb]; exact fc) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgU]; exact hzs
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_33 _) hinC hC tgt_33 (by rw [hsU]; exact hs3) ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsU] at hA₄
  have hg₄' : U₂.cpu.gpr = (g25 Z.cpu.gpr V').set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₄, hsU, hgU]
  refine kf2 Z V' hzs hzb hzp hP1 U₂ t₄ hK₄ hA₄ hr₄ hg₄' ?_
  -- back from `ConvertUInt32ToString`, at 38: the store, the epilogue, the `ret` at 50
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2b q1 q2 qr hP2
  have t8 := aT8 X.cpu.gpr.rsp hp
  have t16 := aT16 X.cpu.gpr.rsp hp
  have tr := aTr8 X.cpu.gpr.rdi hq
  have m2 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8 ∨ X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat) →
      (byteAddrs x 8).map
        (Vst V₂ (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 (Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi))) 4)) =
      (byteAddrs x 8).map V₂ := by
    intro x hx h
    exact Tun.rd_Vst V₂ (X.cpu.gpr.rdi + 8#64)
      (toBytesLE (BitVec.setWidth 32 (Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi))) 4) x 8
      (by rw [toBytesLE_length, tr]; omega) hx (by rw [toBytesLE_length, tr]; omega)
  have hc1' := m2 (X.cpu.gpr.rsp - 8 - 8) (by rw [t16]; omega) (by rw [t16]; omega)
  have hc2' := m2 (X.cpu.gpr.rsp - 8) (by rw [t8]; omega) (by rw [t8]; omega)
  have hcr' := m2 X.cpu.gpr.rsp hp8 (by omega)
  refine (c_38 prof).run c hin (fun j' g' _ V₃ => j' = 50 ∧
      g' = { Z₂.cpu.gpr with
        rax := Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi),
        rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp } ∧
      V₃ = Vst V₂ (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (BitVec.setWidth 32 (Z₂.cpu.gpr.rax - rdq(V₂, X.cpu.gpr.rdi))) 4))
    hKZ₂ hAZ₂ hrZ₂
    (vc_38 (by rw [hz2b]; exact fc) (by rw [hz2b]; exact fw) (by rw [hz2s, aE1]; exact h16)
      (by rw [hz2s, aE1, aE3]; exact h8)
      fun _ => ⟨rfl, by dsimp only [Wst]; rw [hz2s, hz2b, aE1, aE3, aE4, hc1', hc2', q1, q2],
        by dsimp only [Wst]; rw [hz2b]⟩) ?_
  rintro j' g fl₃ V₄ ⟨rfl, rfl, hV₄⟩ U₄ t₇ hKU₄ hAU₄ hrU₄ hgU₄ -
  subst V₄
  have hsU₄ : U₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₄]
  refine c.s_ret hKU₄ hAU₄ hin (lt_len (by decide)) hrU₄ (ret_50 _) (by rw [hsU₄]; exact hl) hin₂ h₂
    (by rw [hsU₄, hcr']; exact qr) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V₂ Z' t₈ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₄]
  try rfl

end FV7z.Aui
