import FV7z.Amp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `Add_Messsage_Pre_ArcType (s, pre, arcType)` (PLAN.md §M, M1)

7-Zip 26.06's `Add_Messsage_Pre_ArcType (UString &s, const char *pre, const wchar_t *arcType)` at `0x5e7a50` in
`7zzs` (`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`; `objdump -d`): `push r13; push r12; push rbp` (`r13` =
`pre`, `r12` = `arcType`, `rbp` = `s`), then `s.Add_LF ()` (the `call` at 14 to `0x44dab0`), `s += pre` (25,
`0x44dbe0`), `s += " "` (40, `0x44dbe0`, the string at `0x6ea344`), `s += arcType` (51, `0x44db10`), and with the
three registers popped the tail `jmp` (71) to `s += "]"` (`0x44dbe0`, the string at `0x6e9ae6`).

As in `FV7z/Lif/Holds.lean`, one theorem per piece, each from a cut point to the first instruction of the next
callee, with its registers and bytes (the return address pushed below the three saved registers):

- `AmpStk`, `ampG`: the bytes after the pushes and the registers at the first `call`; `ampB`, `ampC`, `ampD`: the
  registers at the other `call`s; `ampE`: at the tail `jmp`, the three registers popped.
- `vc_0`, `vc_19`, `vc_30`, `vc_45`, `vc_56`: the pieces' verification conditions.
- `amp_a` (entry to `Add_LF`), `amp_b` (19 to `+= pre`), `amp_c` (30 to `+= " "`), `amp_d` (45 to `+= arcType`),
  `amp_e` (56 to `+= "]"` by the tail `jmp`, `rsp` back at the entry's).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Amp

/-- `UString::Add_LF ()`. -/
abbrev alf_at : Addr := 0x44dab0

/-- `UString::operator+= (const char *)`. -/
abbrev pca_at : Addr := 0x44dbe0

/-- `UString::operator+= (const wchar_t *)`. -/
abbrev pcw_at : Addr := 0x44db10

def pc14 : List Byte := [0xe8, 0x4d, 0x60, 0xe6, 0xff]
theorem pc14_0 : ∀ feat, Dec feat pc14 0 (FV7z.mk .call 64 [.rel 18446744073707872333] 5) := by dec_rfl
theorem wc_14 : pc14 <+: amp.drop 14 := by decide +kernel
theorem call_14 (feat : Features) : Dec feat amp 14 (FV7z.mk .call 64 [.rel 18446744073707872333] 5) :=
  Dec.shift (j := 14) (k := 0) (pc14_0 feat) wc_14 (Nat.zero_le _)
theorem tgt_14 : amp_at.add (14 + 5) + BitVec.ofNat 64 18446744073707872333 = alf_at := by decide

def pc25 : List Byte := [0xe8, 0x72, 0x61, 0xe6, 0xff]
theorem pc25_0 : ∀ feat, Dec feat pc25 0 (FV7z.mk .call 64 [.rel 18446744073707872626] 5) := by dec_rfl
theorem wc_25 : pc25 <+: amp.drop 25 := by decide +kernel
theorem call_25 (feat : Features) : Dec feat amp 25 (FV7z.mk .call 64 [.rel 18446744073707872626] 5) :=
  Dec.shift (j := 25) (k := 0) (pc25_0 feat) wc_25 (Nat.zero_le _)
theorem tgt_25 : amp_at.add (25 + 5) + BitVec.ofNat 64 18446744073707872626 = pca_at := by decide

def pc40 : List Byte := [0xe8, 0x63, 0x61, 0xe6, 0xff]
theorem pc40_0 : ∀ feat, Dec feat pc40 0 (FV7z.mk .call 64 [.rel 18446744073707872611] 5) := by dec_rfl
theorem wc_40 : pc40 <+: amp.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat amp 40 (FV7z.mk .call 64 [.rel 18446744073707872611] 5) :=
  Dec.shift (j := 40) (k := 0) (pc40_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : amp_at.add (40 + 5) + BitVec.ofNat 64 18446744073707872611 = pca_at := by decide

def pc51 : List Byte := [0xe8, 0x88, 0x60, 0xe6, 0xff]
theorem pc51_0 : ∀ feat, Dec feat pc51 0 (FV7z.mk .call 64 [.rel 18446744073707872392] 5) := by dec_rfl
theorem wc_51 : pc51 <+: amp.drop 51 := by decide +kernel
theorem call_51 (feat : Features) : Dec feat amp 51 (FV7z.mk .call 64 [.rel 18446744073707872392] 5) :=
  Dec.shift (j := 51) (k := 0) (pc51_0 feat) wc_51 (Nat.zero_le _)
theorem tgt_51 : amp_at.add (51 + 5) + BitVec.ofNat 64 18446744073707872392 = pcw_at := by decide

def pj71 : List Byte := [0xe9, 0x44, 0x61, 0xe6, 0xff]
theorem pj71_0 : ∀ feat, Dec feat pj71 0 (FV7z.mk .jmp 64 [.rel 18446744073707872580] 5) := by dec_rfl
theorem wj_71 : pj71 <+: amp.drop 71 := by decide +kernel
theorem jmp_71 (feat : Features) : Dec feat amp 71 (FV7z.mk .jmp 64 [.rel 18446744073707872580] 5) :=
  Dec.shift (j := 71) (k := 0) (pj71_0 feat) wj_71 (Nat.zero_le _)
theorem tgt_71 : amp_at.add (71 + 5) + BitVec.ofNat 64 18446744073707872580 = pca_at.add 0 := by decide

/-! ## The frame -/

/-- The bytes after the three `push`es: `r13`, `r12`, `rbp` below the stack pointer. -/
def AmpStk (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8#64) (toBytesLE g.r13 8)) (g.rsp - 16#64) (toBytesLE g.r12 8)) (g.rsp - 24#64)
    (toBytesLE g.rbp 8)

/-- The registers at the `call` of `Add_LF`: `rsp` 24 lower, `r13` = `pre`, `r12` = `arcType`, `rbp` = `s`. -/
def ampG (g : Gprs) : Gprs := { g with rsp := g.rsp - 24#64, r13 := g.rsi, r12 := g.rdx, rbp := g.rdi }

/-- The registers at the `call` of `s += pre`. -/
def ampB (g : Gprs) : Gprs := { g with rsi := g.r13, rdi := g.rbp }

/-- The registers at the `call` of `s += " "`. -/
def ampC (g : Gprs) : Gprs := { g with rdi := g.rbp, rsi := 7250756#64 }

/-- The registers at the `call` of `s += arcType`. -/
def ampD (g : Gprs) : Gprs := { g with rsi := g.r12, rdi := g.rbp }

/-- The registers at the tail `jmp` to `s += "]"`: the three saved ones popped. -/
def ampE (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rdi := g.rbp, rsi := 7248614#64, rsp := g.rsp + 24#64, rbp := rdq(V, g.rsp),
           r12 := rdq(V, g.rsp + 8#64), r13 := rdq(V, g.rsp + 16#64) }

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24#64) i)) (h : ∀ fl, Q 14 (ampG g) fl (AmpStk V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ampG, AmpStk] at hst h
  have w1 : ∀ i < 8, Foot Wl (Addr.add (rsp - 8) i) := fun i hi => by
    have := hst (16 + i) (by omega)
    rwa [show Addr.add (rsp - 24#64) (16 + i) = Addr.add (rsp - 8) i by simp only [Addr.add]; bv_omega] at this
  have w2 : ∀ i < 8, Foot Wl (Addr.add (rsp - 16#64) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (rsp - 24#64) (8 + i) = Addr.add (rsp - 16#64) i by simp only [Addr.add]; bv_omega] at this
  have w3 : ∀ i < 8, Foot Wl (Addr.add (rsp - 24#64) i) := fun i hi => hst i (by omega)
  have e2 : rsp - 8 - 8 = rsp - 16#64 := by bv_omega
  have e3 : rsp - 8 - 8 - 8 = rsp - 24#64 := by
    clear e2
    bv_omega
  wpx [W_0, o0, Op.push]
  rw [e3, e2]
  all_goals repeat' (first | exact h _ | exact w1 | exact w2 | exact w3 | apply And.intro | intro _)

theorem vc_19 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 25 (ampB g) fl V) :
    W_19 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ampB] at h
  wpx [W_19, o1]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

theorem vc_30 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 40 (ampC g) fl V) :
    W_30 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ampC] at h
  wpx [W_30, o2]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 51 (ampD g) fl V) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ampD] at h
  wpx [W_45, o3]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hl : ∀ i < 24, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 71 (ampE g V) fl V) : W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ampE] at hl h
  have l1 : ∀ i < 8, Foot F.data (Addr.add rsp i) := fun i hi => hl i (by omega)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (rsp + 8#64) i) := fun i hi => by
    have := hl (8 + i) (by omega)
    rwa [show Addr.add rsp (8 + i) = Addr.add (rsp + 8#64) i by simp only [Addr.add]; bv_omega] at this
  have l3 : ∀ i < 8, Foot F.data (Addr.add (rsp + 16#64) i) := fun i hi => by
    have := hl (16 + i) (by omega)
    rwa [show Addr.add rsp (16 + i) = Addr.add (rsp + 16#64) i by simp only [Addr.add]; bv_omega] at this
  have e3 : rsp + 8 + 8 + 8 = rsp + 24#64 := by bv_omega
  have e2 : rsp + 8 + 8 = rsp + 16#64 := by
    clear e3
    bv_omega
  wpx [W_56, o4, Op.pop]
  rw [e3, e2]
  all_goals repeat' (first | exact h _ | exact l1 | exact l2 | exact l3 | apply And.intro | intro _)

/-! ## The function, piece by piece -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From the entry to the first instruction of `UString::Add_LF` (`s` in `rdi`): the three saved registers and
the return address (19) below the entry's `rsp`. -/
theorem amp_a {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amp_at amp)
    (hin₂ : CodeIn L alf_at code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amp_at)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i))
    (k : ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (AmpStk V X.cpu.gpr) (X.cpu.gpr.rsp - 32#64) (toBytesLE (amp_at.add 19) 8)) →
      Y.cpu.rip = alf_at → Y.cpu.gpr = (ampG X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32#64) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have s24 : ∀ i < 24, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24#64) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 32#64) (8 + i) = Addr.add (X.cpu.gpr.rsp - 24#64) i by
      simp only [Addr.add]; bv_omega] at this
  have e1 : (ampG X.cpu.gpr).rsp - 8 = X.cpu.gpr.rsp - 32#64 := by
    show X.cpu.gpr.rsp - 24#64 - 8 = _
    bv_omega
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 14 ∧ g' = ampG X.cpu.gpr ∧ V' = AmpStk V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 s24 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_14 _) hin₂ h₂ tgt_14 (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ hg₂

/-- From the return of `Add_LF` (19) to the first instruction of `s += pre` (`rdi` = `rbp`, `rsi` = `r13`). -/
theorem amp_b {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amp_at amp)
    (hin₂ : CodeIn L pca_at code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amp_at.add 19)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (amp_at.add 30) 8)) →
      Y.cpu.rip = pca_at → Y.cpu.gpr = (ampB X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_19 prof).run c hin (fun j' g' _ V' => j' = 25 ∧ g' = ampB X.cpu.gpr ∧ V' = V) hK hA hrip
    (vc_19 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e1 : (ampB X.cpu.gpr).rsp = X.cpu.gpr.rsp := rfl
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_25 _) hin₂ h₂ tgt_25 (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ hg₂

/-- From the return of `s += pre` (30) to the first instruction of `s += " "` (`rdi` = `rbp`). -/
theorem amp_c {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amp_at amp)
    (hin₂ : CodeIn L pca_at code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amp_at.add 30)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (amp_at.add 45) 8)) →
      Y.cpu.rip = pca_at → Y.cpu.gpr = (ampC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_30 prof).run c hin (fun j' g' _ V' => j' = 40 ∧ g' = ampC X.cpu.gpr ∧ V' = V) hK hA hrip
    (vc_30 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e1 : (ampC X.cpu.gpr).rsp = X.cpu.gpr.rsp := rfl
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_40 _) hin₂ h₂ tgt_40 (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ hg₂

/-- From the return of `s += " "` (45) to the first instruction of `s += arcType` (`rdi` = `rbp`, `rsi` = `r12`). -/
theorem amp_d {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amp_at amp)
    (hin₂ : CodeIn L pcw_at code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amp_at.add 45)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (amp_at.add 56) 8)) →
      Y.cpu.rip = pcw_at → Y.cpu.gpr = (ampD X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_45 prof).run c hin (fun j' g' _ V' => j' = 51 ∧ g' = ampD X.cpu.gpr ∧ V' = V) hK hA hrip
    (vc_45 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e1 : (ampD X.cpu.gpr).rsp = X.cpu.gpr.rsp := rfl
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_51 _) hin₂ h₂ tgt_51 (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ hg₂

/-- From the return of `s += arcType` (56), the three saved registers popped, by the tail `jmp` to the first
instruction of `s += "]"` (`rdi` = the old `rbp`), the bytes as they were. -/
theorem amp_e {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L amp_at amp)
    (hin₂ : CodeIn L pca_at code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = amp_at.add 56)
    (hl : ∀ i < 24, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = pca_at →
      Y.cpu.gpr = ampE X.cpu.gpr V → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_56 prof).run c hin (fun j' g' _ V' => j' = 71 ∧ g' = ampE X.cpu.gpr V ∧ V' = V) hK hA hrip
    (vc_56 hl fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_jmp_x hK₁ hA₁ hin (lt_len (by decide)) hr₁ (jmp_71 _) hin₂ (tgt := 0) h₂ tgt_71 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hg₁])

end FV7z.Amp
