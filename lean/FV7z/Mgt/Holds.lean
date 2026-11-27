import FV7z.Mgt.Cuts
import FV7z.Aac.Blocks
import FV7z.Dde.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.Fr24
import FV7z.Tun.Inv
/-!
# `MyGetTempPath` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NDir::MyGetTempPath (AString &path)` at `0x454b40` in `7zzs`
(`CPP/Windows/FileDir.cpp`), `path` in `rdi`: `push rbp; lea rsi, [rip + …]` (the string "/tmp" at `0x6d944d`),
`mov rbp, rdi`, the `call` (15) of `AString::operator= (const char *)` (`Aac.aac_at`); `mov rdi, [rbp]; mov esi, 1`,
the `call` (29) of `NFind::DoesDirExist (path._chars, true)` (`Dde.dde_at`); `lea rsi, [rip + …]` ("/tmp/" at
`0x6d9447`), `mov rdi, rbp; test al, al; lea rax, [rip + …]` ("./" at `0x6ee956`), `cmove rsi, rax`, the `call` (57)
of `AString::operator=` again; `mov eax, 1; pop rbp; ret` (68).

The three callees are hypotheses (`k1`, `k2`, `k3`), as in `FV7z/Upe/Holds.lean`: each a continuation at its entry,
given the run from its return (`rsp` 8 below the entry's, `rbp` = `path` as the ABI keeps it, the saved `rbp` and the
return address as they were, and the callee's own post `P1`, `P2`, `P3`); the last post to the return address (`kr`).

- `g15`, `V0`: the registers and the bytes at the first `call`.
- `g29`: the registers at the second `call`, from those at the return of the first.
- `gA`, `gB`: the registers at the third `call` when `DoesDirExist` answered false ("./"), true ("/tmp/").
- `vc_0`, `vc_20`, `vc_34`, `vc_62`: the verification conditions of the four pieces.
- `mgt_ok`: from the entry, through the three callees, to the return address with `eax` = 1 and `rbp`, `rsp`
  restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Mgt

/-- The first `call` of `AString::operator= (const char *)`. -/
def pc1 : List Byte := [0xe8, 0x6c, 0x79, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709517164] 5) := by dec_rfl
theorem wc_15 : pc1 <+: mgt.drop 15 := by decide +kernel
theorem call_15 (feat : Features) : Dec feat mgt 15 (FV7z.mk .call 64 [.rel 18446744073709517164] 5) :=
  Dec.shift (j := 15) (k := 0) (pc1_0 feat) wc_15 (Nat.zero_le _)
theorem tgt_15 : mgt_at.add (15 + 5) + BitVec.ofNat 64 18446744073709517164 = Aac.aac_at.add 0 := by decide

/-- The `call` of `NFind::DoesDirExist`. -/
def pc2 : List Byte := [0xe8, 0x8e, 0x11, 0x00, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 4494] 5) := by dec_rfl
theorem wc_29 : pc2 <+: mgt.drop 29 := by decide +kernel
theorem call_29 (feat : Features) : Dec feat mgt 29 (FV7z.mk .call 64 [.rel 4494] 5) :=
  Dec.shift (j := 29) (k := 0) (pc2_0 feat) wc_29 (Nat.zero_le _)
theorem tgt_29 : mgt_at.add (29 + 5) + BitVec.ofNat 64 4494 = Dde.dde_at.add 0 := by decide

/-- The second `call` of `AString::operator= (const char *)`. -/
def pc3 : List Byte := [0xe8, 0x42, 0x79, 0xff, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073709517122] 5) := by dec_rfl
theorem wc_57 : pc3 <+: mgt.drop 57 := by decide +kernel
theorem call_57 (feat : Features) : Dec feat mgt 57 (FV7z.mk .call 64 [.rel 18446744073709517122] 5) :=
  Dec.shift (j := 57) (k := 0) (pc3_0 feat) wc_57 (Nat.zero_le _)
theorem tgt_57 : mgt_at.add (57 + 5) + BitVec.ofNat 64 18446744073709517122 = Aac.aac_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_68 : pret <+: mgt.drop 68 := by decide +kernel
theorem ret_68 (feat : Features) : Dec feat mgt 68 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 68) (k := 0) (pret_0 feat) w_68 (Nat.zero_le _)

/-- The bytes at the first `call`: `rbp` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbp 8)

/-- The registers at the first `call`: `rbp` pushed, `rbp` = `path`, `rsi` = "/tmp". -/
abbrev g15 (g : Gprs) : Gprs := { g with rsp := g.rsp - 8, rbp := g.rdi, rsi := 7181389#64 }

/-- The registers at the second `call`: `rdi` = `path._chars`, `esi` = 1. -/
abbrev g29 (g : Gprs) (V : Addr → Byte) : Gprs := { g with rsi := 1#64, rdi := rdq(V, g.rbp) }

/-- The registers at the third `call` with "./" (`DoesDirExist` answered false). -/
abbrev gA (g : Gprs) : Gprs := { g with rax := 7268694#64, rsi := 7268694#64, rdi := g.rbp }

/-- The registers at the third `call` with "/tmp/" (`DoesDirExist` answered true). -/
abbrev gB (g : Gprs) : Gprs := { g with rax := 7268694#64, rsi := 7181383#64, rdi := g.rbp }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; lea rsi, [rip + …]; mov rbp, rdi` to the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h : ∀ fl, Q 15 (g15 g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | exact hs1 | apply And.intro | intro _)

/-- `mov rdi, [rbp]; mov esi, 1` to the second `call`. -/
theorem vc_20 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (h : ∀ fl, Q 29 (g29 g V) fl V) : W_20 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 h ⊢
  wpx [W_20, o1]
  all_goals repeat' (first | exact h _ | exact f1 | apply And.intro | intro _)

/-- `lea rsi, [rip + …]; mov rdi, rbp; test al, al; lea rax, [rip + …]; cmove rsi, rax` to the third `call`. -/
theorem vc_34 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', (g' = gA g ∨ g' = gB g) → ∀ fl, Q 57 g' fl V) : W_34 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at h ⊢
  wpx [W_34, o2, Op.cmov64]
  all_goals repeat'
    first
    | exact h _ (Or.inl rfl) _
    | exact h _ (Or.inr rfl) _
    | apply And.intro
    | intro _
    | split

/-- `mov eax, 1; pop rbp` to the `ret` at 68. -/
theorem vc_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 68 { g with rax := 1#64, rbp := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) : W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_62, o3]
  all_goals repeat' (first | exact h _ | exact hl | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `MyGetTempPath (path)` (`path` = `rdi`) from its entry. The first `AString::operator=` at its entry with the
registers `g15` (`rsp` 16 below the entry's) and the bytes `V0` with the return address pushed (`k1`); from its return
(`rsp` 8 below the entry's, `rbp` = `path`, the saved `rbp` and the return address as they were, `P1`) the call of
`DoesDirExist` with `g29` (`k2`); from its return (likewise, `P2`) the second `AString::operator=` with `gA` or `gB`
(`k3`); from its return (`P3`) the run reaches the return address with `eax` = 1, `rbp` and `rsp` restored (`kr`). -/
theorem mgt_ok {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L mgt_at mgt)
    (hinA : CodeIn L Aac.aac_at Aac.aac) (hinD : CodeIn L Dde.dde_at Dde.dde)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mgt_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (mgt_at.add 20) 8)) →
      Y.cpu.rip = Aac.aac_at → Y.cpu.gpr = (g15 X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = mgt_at.add 20 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 16) (toBytesLE (mgt_at.add 34) 8)) →
      Y.cpu.rip = Dde.dde_at → Y.cpu.gpr = (g29 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = mgt_at.add 34 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z₂.cpu.gpr.rbp = X.cpu.gpr.rdi →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V₂ →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (k3 : ∀ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ → ∀ g' : Gprs, (g' = gA Z₂.cpu.gpr ∨ g' = gB Z₂.cpu.gpr) →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₂ (X.cpu.gpr.rsp - 16) (toBytesLE (mgt_at.add 62) 8)) →
      Y.cpu.rip = Aac.aac_at → Y.cpu.gpr = g'.set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = mgt_at.add 62 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 →
        rdq(V₃, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V₃, X.cpu.gpr.rsp) = e₂.add j₂ → P3 Z₃ V₃ →
        GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), P3 Z₃ V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₃ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₃.cpu.gpr with rax := 1#64, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = mgt_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 15 ∧ g' = g15 X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hY16 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hgY]; exact pe16 _
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_15 _) hinA (tgt := 0) (Aac.lt_len (by decide))
    tgt_15 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (g15 X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by rw [hg₂, hY16, hgY]
  refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from the first `operator=`, at 20: to the `call` of `DoesDirExist`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hP1
  refine (c_20 prof).run c hin (fun j' g' _ V'' => j' = 29 ∧ g' = g29 Z.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
    (vc_20 (by rw [hzb]; exact fp) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hU16 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hgU]; show Z.cpu.gpr.rsp - 8 = _; rw [hzs]; exact pe16 _
  have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hU16]; exact hs2
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_29 _) hinD (tgt := 0) (Dde.lt_len (by decide))
    tgt_29 hst2 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hU16] at hA₃
  have hg₃' : Y₃.cpu.gpr = (g29 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 16) := by rw [hg₃, hU16, hgU]
  refine k2 Z V' hP1 Y₃ t₄ hK₃ hA₃ (by rw [hr₃, addr_add_zero]) hg₃' ?_
  -- back from `DoesDirExist`, at 34: to the second `call` of `operator=`
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2b hb2 hr2 hP2
  refine (c_34 prof).run c hin (fun j' g' _ V'' => j' = 57 ∧ (g' = gA Z₂.cpu.gpr ∨ g' = gB Z₂.cpu.gpr) ∧ V'' = V₂)
    hKZ₂ hAZ₂ hrZ₂ (vc_34 fun _ hg _ => ⟨rfl, hg, rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, hgAB, hV₃⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₃
  have hsg : g.rsp = Z₂.cpu.gpr.rsp := by rcases hgAB with rfl | rfl <;> rfl
  have hU216 : U₂.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hgU₂, hsg, hz2s]; exact pe16 _
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (U₂.cpu.gpr.rsp - 8) i) := by rw [hU216]; exact hs2
  refine c.s_call_x hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (call_57 _) hinA (tgt := 0) (Aac.lt_len (by decide))
    tgt_57 hst3 ?_
  rintro Y₄ t₇ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hU216] at hA₄
  have hg₄' : Y₄.cpu.gpr = g.set 4 (X.cpu.gpr.rsp - 16) := by rw [hg₄, hU216, hgU₂]
  refine k3 Z₂ V₂ hP2 g hgAB Y₄ t₇ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from the second `operator=`, at 62: the epilogue, then the `ret` at 68
  intro Z₃ V₃ t₈ hKZ₃ hAZ₃ hrZ₃ hz3s hb3 hr3 hP3
  refine (c_62 prof).run c hin (fun j' g' _ V'' => j' = 68 ∧
      g' = { Z₃.cpu.gpr with rax := 1#64, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp } ∧ V'' = V₃)
    hKZ₃ hAZ₃ hrZ₃ (vc_62 (by rw [hz3s]; exact h8) fun _ => ⟨rfl, by rw [hz3s, peC, hb3], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₃ t₉ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst V₄
  have hsU₃ : U₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₃]
  refine c.s_ret hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (ret_68 _) (by rw [hsU₃]; exact hl) hin₂ h₂
    (by rw [hsU₃]; exact hr3) ?_
  rintro Z' t₁₀ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₃ V₃ Z' t₁₀ hP3 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₃]
  try rfl

end FV7z.Mgt
