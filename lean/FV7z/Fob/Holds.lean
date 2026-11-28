import FV7z.Fob.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `CFileBase::OpenBinary (name, flags, mode)` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NIO::CFileBase::OpenBinary (const char *name, int flags, mode_t mode)` at `0x456060`
in `7zzs` (`CPP/Windows/FileIO.cpp`), `this` = `rdi`, `name` = `rsi`, `flags` = `edx`, `mode` = `ecx`, `S` the entry's
`rsp`: `push r13; push r12; push rbp; push rbx; sub rsp, 8` (`aR S`, `V1`), `r13d` = `mode`, `r12d` = `flags`, `rbp` =
`name`, `rbx` = `this` (`gC`), `Close ()` (`call` at 26 to `0x456030`); back at 31 `edx` = `mode`, `esi` = `flags`,
`rdi` = `name`, `eax` = 0 (`g31`), `open64` (`call` at 42 to `0x5ff470`); back at 47 `cmp eax, -1`, `_handle` = `eax`
(the store at `rbx`), `setne al`, `add rsp, 8` and the four pops; the `ret` (65).

The callees are hypotheses, as in `FV7z/Ain/Holds.lean`: each a continuation at its entry (`kf1`, `kf2`), given the
run from its return; `Pc1`, `Pc2` are what they leave. The second's return gives the saved registers and the return
address in the bytes it leaves. `al` (`setne`) is left unnamed here: `rax` is some value.

- `aR`, `V1`, `gC`, `g31`, `Wst`: the frame's `rsp`; the bytes with the four pushes; the registers at the two
  `call`s; the bytes with `_handle` stored.
- `vc_0`, `vc_31`, `vc_47`: the pieces from the entry, from 31 and from 47.
- `fob_ok`: through both callees and the store to the return address with `rbx`, `rbp`, `r12`, `r13`, `rsp`
  restored (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fob

/-- `CFileBase::Close`. -/
abbrev close_at : Addr := 0x456030

/-- `open64`. -/
abbrev open_at : Addr := 0x5ff470

/-- The `call` to `Close`. -/
def pcc : List Byte := [0xe8, 0xb1, 0xff, 0xff, 0xff]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 18446744073709551537] 5) := by dec_rfl
theorem wc_26 : pcc <+: fob.drop 26 := by decide +kernel
theorem call_26 (feat : Features) : Dec feat fob 26 (FV7z.mk .call 64 [.rel 18446744073709551537] 5) :=
  Dec.shift (j := 26) (k := 0) (pcc_0 feat) wc_26 (Nat.zero_le _)
theorem tgt_26 : fob_at.add (26 + 5) + BitVec.ofNat 64 18446744073709551537 = close_at := by decide

/-- The `call` to `open64`. -/
def pco : List Byte := [0xe8, 0xe1, 0x93, 0x1a, 0x00]
theorem pco_0 : ∀ feat, Dec feat pco 0 (FV7z.mk .call 64 [.rel 1741793] 5) := by dec_rfl
theorem wc_42 : pco <+: fob.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat fob 42 (FV7z.mk .call 64 [.rel 1741793] 5) :=
  Dec.shift (j := 42) (k := 0) (pco_0 feat) wc_42 (Nat.zero_le _)
theorem tgt_42 : fob_at.add (42 + 5) + BitVec.ofNat 64 1741793 = open_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_65 : pret <+: fob.drop 65 := by decide +kernel
theorem ret_65 (feat : Features) : Dec feat fob 65 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 65) (k := 0) (pret_0 feat) w_65 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8#64

/-- The bytes with `r13`, `r12`, `rbp`, `rbx` pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call` of `Close`: `rbx` = `this`, `rbp` = `name`, `r12d` = `flags`, `r13d` = `mode`. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rsp := aR g.rsp,
      rbp := g.rsi,
      r12 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx),
      r13 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx) }

/-- The registers at the `call` of `open64`: `edx` = `r13d`, `esi` = `r12d`, `rdi` = `rbp`, `eax` = 0. -/
abbrev g31 (g : Gprs) : Gprs :=
  { g with
      rax := 0#64,
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.r13),
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12),
      rdi := g.rbp }

/-- The bytes with `_handle` (at `rbx`) stored: `eax`. -/
abbrev Wst (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V g.rbx (toBytesLE (BitVec.setWidth 32 g.rax) 4)

theorem aE1 (s : Addr) : aR s + 8#64 = s - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE5 (s : Addr) : s - 8 - 8 - 8 - 8 + 8 = s - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE2 (s : Addr) : s - 8 - 8 - 8 + 8 = s - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE3 (s : Addr) : s - 8 - 8 + 8 = s - 8 := BitVec.sub_add_cancel _ _
theorem aE4 (s : Addr) : s - 8 + 8 = s := BitVec.sub_add_cancel _ _

theorem aT8 (s : BitVec 64) (h : 40 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem aT16 (s : BitVec 64) (h : 40 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem aT24 (s : BitVec 64) (h : 40 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem aT32 (s : BitVec 64) (h : 40 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry's code: the four pushes, the moves and `sub rsp, 8`, up to the `call` at 26. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h : ∀ fl, Q 26 (gC g) fl (V1 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, aR, V1] at hs1 hs2 hs3 hs4 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `Close`, at 31: `mov edx, r13d; mov esi, r12d; mov rdi, rbp; xor eax, eax` to the `call` at 42. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 42 (g31 g) fl V) : W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g31] at h ⊢
  wpx [W_31, o1, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `open64`, at 47: `cmp eax, -1; mov [rbx], eax; setne al; add rsp, 8; pop rbx; pop rbp; pop r12;
pop r13` to the `ret` at 65. -/
theorem vc_47 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 4, Foot Wl (Addr.add g.rbx i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ (a : BitVec 64) fl, Q 65
      { g with
          rax := a,
          rbx := rdq(Wst V g, g.rsp + 8#64),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8,
          rbp := rdq(Wst V g, g.rsp + 8#64 + 8),
          r12 := rdq(Wst V g, g.rsp + 8#64 + 8 + 8),
          r13 := rdq(Wst V g, g.rsp + 8#64 + 8 + 8 + 8) } fl (Wst V g)) :
    W_47 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Wst] at fw l1 l2 l3 l4 h ⊢
  wpx [W_47, o2, Op.setcc]
  all_goals repeat' (first | exact h _ _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CFileBase::OpenBinary (name, flags, mode)` (`this` = `rdi`, `name` = `rsi`, `flags` = `edx`, `mode` = `ecx`)
from its entry, `S` = `rsp`: at `Close`'s entry with the registers `gC`, the bytes `V1` and the return address
`fob_at + 31` at `aR S - 8` (`kf1`); from its return (`rsp` = `aR S`, `rbx` = `this`, `rbp` = `name`, `r12d` =
`flags`, `r13d` = `mode`, the post `Pc1`) at `open64`'s entry with the registers `g31` and the return address
`fob_at + 47` (`kf2`); from its return (`rsp` = `aR S`, `rbx` = `this`, the saved registers and the return address in
its bytes, the post `Pc2`) through `_handle` = `eax` to the return address with `rbx`, `rbp`, `r12`, `r13`, `rsp`
restored (`kr`). -/
theorem fob_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fob_at fob)
    {codeC : List Byte} (hinC : CodeIn L close_at codeC) (hC : 0 < codeC.length)
    {codeO : List Byte} (hinO : CodeIn L open_at codeO) (hO : 0 < codeO.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fob_at)
    (hp : 40 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (aR X.cpu.gpr.rsp - 8) (toBytesLE (fob_at.add 31) 8)) →
      Y.cpu.rip = close_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = fob_at.add 31 → Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdi → Pc1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      Pc1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (aR X.cpu.gpr.rsp - 8) (toBytesLE (fob_at.add 47) 8)) →
      Y.cpu.rip = open_at → Y.cpu.gpr = (g31 Z.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = fob_at.add 47 → Z₂.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V₂, X.cpu.gpr.rsp - 8 - 8 - 8 - 8) = X.cpu.gpr.rbx →
        rdq(V₂, X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V₂, X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.r12 → rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r13 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat) (a : BitVec 64), Pc2 Z₂ V₂ →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vst V₂ X.cpu.gpr.rdi (toBytesLE (BitVec.setWidth 32 Z₂.cpu.gpr.rax) 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := a, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = fob_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the entry's code, to the `call` of `Close`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 26 ∧ g' = gC X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 hs2 hs3 hs4 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_26 _) hinC hC tgt_26 (by rw [hsY]; exact hs5) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₂, hsY, hgY]
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `Close`, at 31: to the `call` of `open64`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hP1
  refine (c_31 prof).run c hin (fun j' g' _ V'' => j' = 42 ∧ g' = g31 Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
    (vc_31 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgU]; exact hzs
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_42 _) hinO hO tgt_42 (by rw [hsU]; exact hs5) ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsU] at hA₄
  have hg₄' : U₂.cpu.gpr = (g31 Z.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₄, hsU, hgU]
  refine kf2 Z V' hzs hzb hP1 U₂ t₄ hK₄ hA₄ hr₄ hg₄' ?_
  -- back from `open64`, at 47: the store, the epilogue, the `ret` at 65
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2b q1 q2 q3 q4 qr hP2
  have t8 := aT8 X.cpu.gpr.rsp hp
  have t16 := aT16 X.cpu.gpr.rsp hp
  have t24 := aT24 X.cpu.gpr.rsp hp
  have t32 := aT32 X.cpu.gpr.rsp hp
  have m2 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 4 ≤ x.toNat) →
      (byteAddrs x 8).map (Vst V₂ X.cpu.gpr.rdi (toBytesLE (BitVec.setWidth 32 Z₂.cpu.gpr.rax) 4)) =
      (byteAddrs x 8).map V₂ := by
    intro x hx h
    exact Tun.rd_Vst V₂ X.cpu.gpr.rdi (toBytesLE (BitVec.setWidth 32 Z₂.cpu.gpr.rax) 4) x 8
      (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)
  have hc1' := m2 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (by rw [t32]; omega) (by rw [t32]; omega)
  have hc2' := m2 (X.cpu.gpr.rsp - 8 - 8 - 8) (by rw [t24]; omega) (by rw [t24]; omega)
  have hc3' := m2 (X.cpu.gpr.rsp - 8 - 8) (by rw [t16]; omega) (by rw [t16]; omega)
  have hc4' := m2 (X.cpu.gpr.rsp - 8) (by rw [t8]; omega) (by rw [t8]; omega)
  have hcr' := m2 X.cpu.gpr.rsp hp8 (by omega)
  refine (c_47 prof).run c hin (fun j' g' _ V₃ => j' = 65 ∧
      (∃ a : BitVec 64, g' = { Z₂.cpu.gpr with
        rax := a, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
        rsp := X.cpu.gpr.rsp }) ∧
      V₃ = Vst V₂ X.cpu.gpr.rdi (toBytesLE (BitVec.setWidth 32 Z₂.cpu.gpr.rax) 4))
    hKZ₂ hAZ₂ hrZ₂
    (vc_47 (by rw [hz2b]; exact fw) (by rw [hz2s, aE1]; exact h32) (by rw [hz2s, aE1, aE5]; exact h24)
      (by rw [hz2s, aE1, aE5, aE2]; exact h16) (by rw [hz2s, aE1, aE5, aE2, aE3]; exact h8)
      fun a _ => ⟨rfl, ⟨a, by
        dsimp only [Wst]
        rw [hz2s, hz2b, aE1, aE5, aE2, aE3, aE4, hc1', hc2', hc3', hc4', q1, q2, q3, q4]⟩,
        by dsimp only [Wst]; rw [hz2b]⟩) ?_
  rintro j' g fl₃ V₄ ⟨rfl, ⟨a, rfl⟩, hV₄⟩ U₄ t₇ hKU₄ hAU₄ hrU₄ hgU₄ -
  subst V₄
  have hsU₄ : U₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₄]
  refine c.s_ret hKU₄ hAU₄ hin (lt_len (by decide)) hrU₄ (ret_65 _) (by rw [hsU₄]; exact hl) hin₂ h₂
    (by rw [hsU₄, hcr']; exact qr) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V₂ Z' t₈ a hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₄]
  try rfl

end FV7z.Fob
