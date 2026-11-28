import FV7z.Ifd.Cuts
import FV7z.Fcl.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
/-!
# `CInFileStream::~CInFileStream ()` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::~CInFileStream ()` at `0x5a4040` in `7zzs` (`CPP/7zip/Common/FileStreams.cpp`;
`objdump -d`): `rbx` saved, `rbx` = `this`, the five vtable pointers (`0x78e748` + 16, + 112, + 160, + 208, + 256 at
`this`, `this + 8`, `this + 16`, `this + 24`, `this + 32`) stored; `if (Callback) Callback->InFileStream_On_Destroy
(this, CallbackRef)`: `rdi` = `Callback` (the 8 bytes at `this + 248`, `cb`); if it is set, `rax` = its vtable, `rdx`
= `CallbackRef` (the 8 bytes at `this + 256`), `rsi` = `this`, `call qword [rax + 8]` (87, `Seg.s_callM`). Then the
two `UString`s' buffers: the 8 bytes at `this + 224`, unless 0, to `operator delete []` (`call` at 102 to
`0x6014f0`), the 8 bytes at `this + 208` likewise (119); then `File.Close ()` (`rdi` = `this + 44`, `call` at 128 to
`CFileBase::Close`, `Fcl.fcl_at`), `pop rbx` (133) and `ret` (134).

The callees are hypotheses, as in `FV7z.Ris` and `FV7z.Aac`: each a continuation at its entry, given the run from its
return (`rsp` 8 below the entry's, `rbx` = `this`) on (`kcb`, `kd1`, `kd2`). `File.Close ()`'s run (`kc`) also gives
the saved `rbx` and the return address back as they were, and its own post `Pc`; `kr` takes the run on from the
return address.

- `V1`: the bytes after `push rbx` and the five stores; `cb`, `vt`: `Callback` and its vtable, read from them; `gC`:
  the registers at the `call` through the vtable.
- `vc_0z`, `vc_0n`, `vc_90z`, `vc_90n`, `vc_107z`, `vc_107n`, `vc_124`, `vc_133`: the verification conditions of the
  pieces.
- `ifd_ok`: from the entry, through the callees, to the return address with `rbx` restored and `rsp` 8 up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ifd

/-- The `call` through the vtable. -/
def pcall : List Byte := [0xff, 0x50, 0x08]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) := by dec_rfl
theorem wc_87 : pcall <+: ifd.drop 87 := by decide +kernel
theorem call_87 (feat : Features) : Dec feat ifd 87 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) :=
  Dec.shift (j := 87) (k := 0) (pcall_0 feat) wc_87 (Nat.zero_le _)

/-- The `call`s to `operator delete []`. -/
def pcd1 : List Byte := [0xe8, 0x45, 0xd4, 0x05, 0x00]
theorem pcd1_0 : ∀ feat, Dec feat pcd1 0 (FV7z.mk .call 64 [.rel 382021] 5) := by dec_rfl
theorem wc_102 : pcd1 <+: ifd.drop 102 := by decide +kernel
theorem call_102 (feat : Features) : Dec feat ifd 102 (FV7z.mk .call 64 [.rel 382021] 5) :=
  Dec.shift (j := 102) (k := 0) (pcd1_0 feat) wc_102 (Nat.zero_le _)
def pcd2 : List Byte := [0xe8, 0x34, 0xd4, 0x05, 0x00]
theorem pcd2_0 : ∀ feat, Dec feat pcd2 0 (FV7z.mk .call 64 [.rel 382004] 5) := by dec_rfl
theorem wc_119 : pcd2 <+: ifd.drop 119 := by decide +kernel
theorem call_119 (feat : Features) : Dec feat ifd 119 (FV7z.mk .call 64 [.rel 382004] 5) :=
  Dec.shift (j := 119) (k := 0) (pcd2_0 feat) wc_119 (Nat.zero_le _)

/-- The `call` to `CFileBase::Close ()`. -/
def pcc : List Byte := [0xe8, 0x6b, 0x1f, 0xeb, 0xff]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 18446744073708183403] 5) := by dec_rfl
theorem wc_128 : pcc <+: ifd.drop 128 := by decide +kernel
theorem call_128 (feat : Features) : Dec feat ifd 128 (FV7z.mk .call 64 [.rel 18446744073708183403] 5) :=
  Dec.shift (j := 128) (k := 0) (pcc_0 feat) wc_128 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_134 : pret <+: ifd.drop 134 := by decide +kernel
theorem ret_134 (feat : Features) : Dec feat ifd 134 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 134) (k := 0) (pret_0 feat) w_134 (Nat.zero_le _)

/-- The bytes after `push rbx` and the five vtable pointers. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE (7923528#64 + 16#64) 8))
    (g.rdi + 8#64) (toBytesLE (7923528#64 + 112#64) 8)) (g.rdi + 16#64) (toBytesLE (7923528#64 + 160#64) 8))
    (g.rdi + 24#64) (toBytesLE (7923528#64 + 208#64) 8)) (g.rdi + 32#64) (toBytesLE (7923528#64 + 256#64) 8)
/-- `Callback`, read after the stores. -/
abbrev cb (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, g.rdi + 248#64)
/-- Its vtable. -/
abbrev vt (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, cb V g)
/-- The registers at the `call` through the vtable. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rax := vt V g,
      rdx := rdq(V1 V g, g.rdi + 256#64),
      rbx := g.rdi,
      rsp := g.rsp - 8,
      rsi := g.rdi,
      rdi := cb V g }

variable {F : Footprint} {Wl : List Rgn}

/-- `Callback` not set: `push rbx`, the stores, `mov rdi, [rdi + 248]; test rdi, rdi; je` taken, to 90. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : cb V g = 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 24#64) i))
    (fw32 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 32#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 248#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 90 ∧ g'.rsp = g.rsp - 8 ∧ g'.rbx = g.rdi ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cb, V1] at h hst fw0 fw8 fw16 fw24 fw32 fa ⊢
  wpx [W_0, o0, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | exact rfl
    | apply And.intro
    | intro _

/-- `Callback` set: `je` not taken, `mov rax, [rdi]; mov rdx, [rbx + 256]; mov rsi, rbx`, up to the `call`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : cb V g ≠ 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 24#64) i))
    (fw32 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 32#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 248#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (cb V g) i))
    (fr : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 256#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 87 ∧ g' = gC V g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, vt, cb, V1] at h hst fw0 fw8 fw16 fw24 fw32 fa fs fr ⊢
  wpx [W_0, W_74, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | exact fs
    | exact rfl
    | apply And.intro
    | intro _

/-- The first buffer 0: `mov rdi, [rbx + 224]; test rdi, rdi; je` taken, to 107. -/
theorem vc_90z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdq(V, g.rbx + 224#64) = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 224#64) i)) :
    W_90 F Wl (fun j' g' _ V' => j' = 107 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_90, o2, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | exact rfl
    | apply And.intro
    | intro _

/-- The first buffer set: `je` not taken, to the `call` at 102. -/
theorem vc_90n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdq(V, g.rbx + 224#64) ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 224#64) i)) :
    W_90 F Wl (fun j' g' _ V' => j' = 102 ∧ g' = { g with rdi := rdq(V, g.rbx + 224#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_90, o2, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | exact rfl
    | apply And.intro
    | intro _

/-- The second buffer 0: `mov rdi, [rbx + 208]; test rdi, rdi; je` taken, to 124. -/
theorem vc_107z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdq(V, g.rbx + 208#64) = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 208#64) i)) :
    W_107 F Wl (fun j' g' _ V' => j' = 124 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_107, o3, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | exact rfl
    | apply And.intro
    | intro _

/-- The second buffer set: `je` not taken, to the `call` at 119. -/
theorem vc_107n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdq(V, g.rbx + 208#64) ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 208#64) i)) :
    W_107 F Wl (fun j' g' _ V' => j' = 119 ∧ g' = { g with rdi := rdq(V, g.rbx + 208#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_107, o3, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | exact rfl
    | apply And.intro
    | intro _

/-- `lea rdi, [rbx + 44]`, to the `call` at 128. -/
theorem vc_124 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_124 F Wl (fun j' g' _ V' => j' = 128 ∧ g' = { g with rdi := g.rbx + 44#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only
  wpx [W_124, o4]
  all_goals repeat'
    first
    | with_reducible rfl
    | exact trivial
    | exact rfl
    | apply And.intro
    | intro _

/-- `pop rbx`, to the `ret` at 134. -/
theorem vc_133 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 134 { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) :
    W_133 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_133, o5]
  all_goals repeat'
    first
    | exact h _
    | with_reducible assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFileStream::~CInFileStream ()` (`this` = `rdi`) from its entry. With `Callback` (`cb`) set the run is at its
vtable's entry at 8 with the registers `gC` and the return address `ifd_at + 90` pushed (`kcb`); with a buffer set
at `operator delete []`'s entry with `rdi` = it (`kd1`, `kd2`; for any registers at 90 or 107 with `rsp` 8 below the
entry's and `rbx` = `this`); then at `CFileBase::Close ()`'s entry with `rdi` = `this + 44` (`kc`); back from it at
133 with the saved `rbx`, the return address and `Pc`, the run reaches the return address with `rbx` restored and
`rsp` 8 up (`kr`). -/
theorem ifd_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ifd_at ifd)
    {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hinC : CodeIn L Fcl.fcl_at Fcl.fcl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (fw32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 248#64) i))
    (f224 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 224#64) i))
    (f208 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 208#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (fs : cb V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (cb V X.cpu.gpr) i))
    (fr : cb V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 256#64) i))
    (fb : cb V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt V X.cpu.gpr + 8#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : cb V X.cpu.gpr ≠ 0 → rdq(V1 V X.cpu.gpr, vt V X.cpu.gpr + 8#64) = eF)
    (kcb : cb V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (ifd_at.add 90) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ifd_at.add 90 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kd1 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      rdq(V', Z.cpu.gpr.rbx + 224#64) ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (ifd_at.add 107) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.rbx + 224#64) }).set 4 (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = ifd_at.add 107 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kd2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      rdq(V', Z.cpu.gpr.rbx + 208#64) ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (ifd_at.add 124) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.rbx + 208#64) }).set 4 (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = ifd_at.add 124 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kc : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (ifd_at.add 133) 8)) →
      Y.cpu.rip = Fcl.fcl_at →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 44#64 }).set 4 (X.cpu.gpr.rsp - 8 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = ifd_at.add 133 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z₂ V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 124: `File.Close ()`, `pop rbx`, `ret`
  have k124 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ifd_at.add 124 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb
    refine (c_124 prof).run c hin (fun j' g' _ V'' => j' = 128 ∧ g' = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 44#64 } ∧
      V'' = V') hKZ hAZ hrZ vc_124 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgU]; exact hzs
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_128 _) hinC (Fcl.lt_len (by decide)) (by decide)
      (by rw [hsU]; exact hs2) ?_
    rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
    rw [hsU] at hAY
    refine kc Z V' hzs hzb Y t₂ hKY hAY hrY (by rw [hgY, hsU, hgU]) ?_
    intro Z₂ V'' t₃ hKZ₂ hAZ₂ hrZ₂ hzs₂ hb hra hPc
    refine (c_133 prof).run c hin (fun j' g' _ V₃ => j' = 134 ∧
        g' = { Z₂.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧ V₃ = V'') hKZ₂ hAZ₂ hrZ₂
      (vc_133 (by rw [hzs₂]; exact h8) fun _ => ⟨rfl, by rw [hzs₂, hb, e8], rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₃
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_134 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hra) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z₂ V'' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₂]
    try rfl
  -- from 107: the second buffer
  have k107 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ifd_at.add 107 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb
    have fa' : ∀ i < 8, Foot F.data (Addr.add (Z.cpu.gpr.rbx + 208#64) i) := by rw [hzb]; exact f208
    by_cases hp : rdq(V', Z.cpu.gpr.rbx + 208#64) = 0
    · refine (c_107 prof).run c hin (fun j' g' _ V'' => j' = 124 ∧ g'.rsp = Z.cpu.gpr.rsp ∧
          g'.rbx = Z.cpu.gpr.rbx ∧ V'' = V') hKZ hAZ hrZ (vc_107z hp fa') ?_
      rintro j' g fl V₁ ⟨rfl, hg1, hg2, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact k124 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzb])
    · refine (c_107 prof).run c hin (fun j' g' _ V'' => j' = 119 ∧
          g' = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.rbx + 208#64) } ∧ V'' = V') hKZ hAZ hrZ (vc_107n hp fa') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgU]; exact hzs
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_119 _) hinD hD (by decide)
        (by rw [hsU]; exact hs2) ?_
      rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
      rw [hsU] at hAY
      exact kd2 Z V' hzs hzb hp Y t₂ hKY hAY hrY (by rw [hgY, hsU, hgU]) k124
  -- from 90: the first buffer
  have k90 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ifd_at.add 90 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb
    have fa' : ∀ i < 8, Foot F.data (Addr.add (Z.cpu.gpr.rbx + 224#64) i) := by rw [hzb]; exact f224
    by_cases hp : rdq(V', Z.cpu.gpr.rbx + 224#64) = 0
    · refine (c_90 prof).run c hin (fun j' g' _ V'' => j' = 107 ∧ g'.rsp = Z.cpu.gpr.rsp ∧
          g'.rbx = Z.cpu.gpr.rbx ∧ V'' = V') hKZ hAZ hrZ (vc_90z hp fa') ?_
      rintro j' g fl V₁ ⟨rfl, hg1, hg2, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact k107 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzb])
    · refine (c_90 prof).run c hin (fun j' g' _ V'' => j' = 102 ∧
          g' = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.rbx + 224#64) } ∧ V'' = V') hKZ hAZ hrZ (vc_90n hp fa') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgU]; exact hzs
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_102 _) hinD hD (by decide)
        (by rw [hsU]; exact hs2) ?_
      rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
      rw [hsU] at hAY
      exact kd1 Z V' hzs hzb hp Y t₂ hKY hAY hrY (by rw [hgY, hsU, hgU]) k107
  -- from the entry
  have hrip' : X.cpu.rip = ifd_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hs : cb V X.cpu.gpr = 0
  · -- `Callback` not set
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 90 ∧ g'.rsp = X.cpu.gpr.rsp - 8 ∧
        g'.rbx = X.cpu.gpr.rdi ∧ V' = V1 V X.cpu.gpr) hK hA hrip' (vc_0z hs hs1 fw0 fw8 fw16 fw24 fw32 fa) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k90 Y _ t₁ hKY hAY hrY (by rw [hgY, hg1]) (by rw [hgY, hg2])
  · -- `Callback` set: to the `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 87 ∧ g' = gC V X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA hrip'
      (vc_0n hs hs1 fw0 fw8 fw16 fw24 fw32 fa (fs hs) (fr hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have he : eaD Y 0 8 = vt V X.cpu.gpr + 8#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
      rw [hgY]
      rfl
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_87 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) (by rw [hsY]; exact hs2) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    exact kcb hs Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) k90

end FV7z.Ifd
