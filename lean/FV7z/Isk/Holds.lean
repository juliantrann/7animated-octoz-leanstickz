import FV7z.Isk.Cuts
import FV7z.Fsk.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CInFileStream::Seek (Int64 offset, UInt32 seekOrigin, UInt64 *newPosition)` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::Seek` at `0x5a3770` in `7zzs` (`CPP/7zip/Common/FileStreams.cpp`; `objdump -d`):
`r12`, `rbp`, `rbx` saved; `seekOrigin` (`edx`) above 2: `r12d` = `STG_E_INVALIDFUNCTION`, to the epilogue (45).
Else `rbp` = `rdi` = `this + 44` (`File`), `rbx` = `newPosition`, `call` at 23 to `File.seek` (`Fsk.fsk_at`); back
at 28, `rax` = -1: `call` at 56 to `0x5a0200` (the error as an `HRESULT`), back at 61 `r12d` the `HRESULT` (or
`E_FAIL` for 0); `newPosition` set: `call` at 90 to `0x4560f0` (`File.GetPosition`), back at 95 its `rax` stored to
`*newPosition`; to the epilogue. Else (28) `r12d` = 0 and, `newPosition` set, `rax` stored to it. The epilogue (45):
`eax` = `r12d`, the three pops, `ret` (52).

The callees are hypotheses, as in `FV7z.Ifd`: each a continuation at its entry, given the run from its return
(`rsp` 24 below the entry's, `rbx` = `newPosition`, `rbp` = `this + 44`) on, with the saved registers and the return
address as they were (`Frm`) (`kS`, `kE`, `kP`); `kr` takes the run on from the return address. The stores to
`*newPosition` lie apart from the saved registers and the return address (`hap`), so the pops read them back
(`fr_st`).

- `V3`: the bytes after the pushes; `gS`: the registers at the `call` to `File.seek`; `Frm`: the saved registers
  and the return address in the frame.
- `vc_0`, `vc_28z`, `vc_28n`, `vc_45`, `vc_61`, `vc_82z`, `vc_82n`, `vc_95`: the verification conditions of the
  pieces (where a `cmp` picks the exit, the post is the two exits' disjunction).
- `isk_ok`: from the entry, through the callees, to the return address with `rbx`, `rbp`, `r12` restored and `rsp`
  8 up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Isk

/-- The `call` to `File.seek`. -/
def pc23 : List Byte := [0xe8, 0x24, 0x29, 0xeb, 0xff]
theorem pc23_0 : ∀ feat, Dec feat pc23 0 (FV7z.mk .call 64 [.rel 18446744073708185892] 5) := by dec_rfl
theorem wc_23 : pc23 <+: isk.drop 23 := by decide +kernel
theorem call_23 (feat : Features) : Dec feat isk 23 (FV7z.mk .call 64 [.rel 18446744073708185892] 5) :=
  Dec.shift (j := 23) (k := 0) (pc23_0 feat) wc_23 (Nat.zero_le _)

/-- The `call` to `0x5a0200` (the error as an `HRESULT`). -/
def pc56 : List Byte := [0xe8, 0x53, 0xca, 0xff, 0xff]
theorem pc56_0 : ∀ feat, Dec feat pc56 0 (FV7z.mk .call 64 [.rel 18446744073709537875] 5) := by dec_rfl
theorem wc_56 : pc56 <+: isk.drop 56 := by decide +kernel
theorem call_56 (feat : Features) : Dec feat isk 56 (FV7z.mk .call 64 [.rel 18446744073709537875] 5) :=
  Dec.shift (j := 56) (k := 0) (pc56_0 feat) wc_56 (Nat.zero_le _)

/-- The `call` to `0x4560f0` (`File.GetPosition`). -/
def pc90 : List Byte := [0xe8, 0x21, 0x29, 0xeb, 0xff]
theorem pc90_0 : ∀ feat, Dec feat pc90 0 (FV7z.mk .call 64 [.rel 18446744073708185889] 5) := by dec_rfl
theorem wc_90 : pc90 <+: isk.drop 90 := by decide +kernel
theorem call_90 (feat : Features) : Dec feat isk 90 (FV7z.mk .call 64 [.rel 18446744073708185889] 5) :=
  Dec.shift (j := 90) (k := 0) (pc90_0 feat) wc_90 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_52 : pret <+: isk.drop 52 := by decide +kernel
theorem ret_52 (feat : Features) : Dec feat isk 52 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 52) (k := 0) (pret_0 feat) w_52 (Nat.zero_le _)

theorem b3s (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem b2s (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem b1s (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The stack's addresses as numbers. -/
theorem sp_t (S : Addr) (h : 24 ≤ S.toNat) :
    (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧ (S - 8 - 8 - 8).toNat = S.toNat - 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

/-- The bytes after the three pushes. -/
abbrev V3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)
/-- The registers at the `call` to `File.seek`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with rbx := g.rcx, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi + 44#64, rdi := g.rdi + 44#64 }
/-- The frame under the entry's `S`: the saved `rbx`, `rbp`, `r12` of `g` and the return address `ra`. -/
abbrev Frm (S : Addr) (g : Gprs) (ra : Addr) (W : Addr → Byte) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g.rbx ∧ rdq(W, S - 8 - 8) = g.rbp ∧ rdq(W, S - 8) = g.r12 ∧ rdq(W, S) = ra

/-- The pushes give the frame. -/
theorem fr_push (V : Addr → Byte) (g : Gprs) (hS : 24 ≤ g.rsp.toNat) (hS8 : g.rsp.toNat + 8 ≤ 2 ^ 64) {ra : Addr}
    (hra : rdq(V, g.rsp) = ra) : Frm g.rsp g ra (V3 V g) := by
  obtain ⟨s8, s16, s24⟩ := sp_t g.rsp hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [V3]
    rw [Tun.rd_Vst_self _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · dsimp only [V3]
    rw [Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (g.rsp - 8 - 8) 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · dsimp only [V3]
    rw [Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (g.rsp - 8) 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) (g.rsp - 8) 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ (g.rsp - 8) (toBytesLE g.r12 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · dsimp only [V3]
    rw [Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) g.rsp 8 (by rw [toBytesLE_length]; omega)
        hS8 (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) g.rsp 8 (by rw [toBytesLE_length]; omega)
        hS8 (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.r12 8) g.rsp 8 (by rw [toBytesLE_length]; omega)
        hS8 (by rw [toBytesLE_length]; omega)]
    exact hra

/-- A store of 8 bytes at `x`, apart from the frame, keeps it. -/
theorem fr_st {S x ra : Addr} {g : Gprs} {W : Addr → Byte} (v : BitVec 64) (hS : 24 ≤ S.toNat)
    (hS8 : S.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (hap : x.toNat + 8 ≤ S.toNat - 24 ∨ S.toNat + 8 ≤ x.toNat) (h : Frm S g ra W) :
    Frm S g ra (Vst W x (toBytesLE v 8)) := by
  obtain ⟨s8, s16, s24⟩ := sp_t S hS
  obtain ⟨f1, f2, f3, f4⟩ := h
  have rd : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 → (x.toNat + 8 ≤ y.toNat ∨ y.toNat + 8 ≤ x.toNat) →
      rdq(Vst W x (toBytesLE v 8), y) = rdq(W, y) := fun y hy hxy =>
    congrArg (ofBytesLE 64) (Tun.rd_Vst W x (toBytesLE v 8) y 8 (by rw [toBytesLE_length]; exact hx) hy
      (by rw [toBytesLE_length]; exact hxy))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rd (S - 8 - 8 - 8) (by omega) (by omega)]; exact f1
  · rw [rd (S - 8 - 8) (by omega) (by omega)]; exact f2
  · rw [rd (S - 8) (by omega) (by omega)]; exact f3
  · rw [rd S hS8 (by omega)]; exact f4

/-- The closers of the verification conditions; a disjunction of two exits' posts by either side. -/
local macro "iskc" : tactic => `(tactic| all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; contradiction)
    | exact rfl
    | (apply Or.inl; repeat' (first | exact trivial | exact rfl | apply And.intro); done)
    | (apply Or.inr; repeat' (first | exact trivial | exact rfl | apply And.intro); done)
    | apply And.intro
    | intro _)

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `cmp edx, 2; ja`: taken, `r12d` = `STG_E_INVALIDFUNCTION`, to 45; else `lea rbp, [rdi + 44];
mov rbx, rcx; mov rdi, rbp`, to the `call` at 23. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => (j' = 45 ∧ g'.rsp = g.rsp - 8 - 8 - 8 ∧ V' = V3 V g) ∨
      (j' = 23 ∧ g' = gS g ∧ V' = V3 V g)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V3, gS] at h1 h2 h3 ⊢
  wpx [W_0, W_104, W_13, o0, o1, o10]
  iskc

/-- Back from `File.seek`, `newPosition` 0: `cmp rax, -1; je` taken, to the `call` at 56; else `xor r12d, r12d;
test rbx, rbx; je` taken, to 45. -/
theorem vc_28z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rbx = 0) :
    W_28 F Wl (fun j' g' _ V' => (j' = 56 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ V' = V) ∨
      (j' = 45 ∧ g'.rsp = g.rsp ∧ V' = V)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_28, W_34, W_42, o2, o3, o4, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  iskc

/-- Back from `File.seek`, `newPosition` set: to the `call` at 56, or `rax` stored to `*newPosition`, to 45. -/
theorem vc_28n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬g.rbx = 0)
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_28 F Wl (fun j' g' _ V' => (j' = 56 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ V' = V) ∨
      (j' = 45 ∧ g'.rsp = g.rsp ∧ V' = Vst V g.rbx (toBytesLE g.rax 8))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fw ⊢
  wpx [W_28, W_34, W_42, o2, o3, o4, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  iskc

/-- The epilogue: `mov eax, r12d` and the three pops, to the `ret` at 52. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_45 F Wl (fun j' g' _ V' => j' = 52 ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧ g'.rbx = rdq(V, g.rsp) ∧
      g'.rbp = rdq(V, g.rsp + 8) ∧ g'.r12 = rdq(V, g.rsp + 8 + 8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 ⊢
  wpx [W_45, o5]
  iskc

/-- Back from `0x5a0200`: `test eax, eax`, `r12d` = `E_FAIL` or the `HRESULT`, to 82. -/
theorem vc_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_61 F Wl (fun j' g' _ V' => j' = 82 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only
  wpx [W_61, W_112, W_65, o6, o7, o11, Op.zxr16]
  iskc

/-- `newPosition` 0: `test rbx, rbx; je` taken, to 45. -/
theorem vc_82z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rbx = 0) :
    W_82 F Wl (fun j' g' _ V' => j' = 45 ∧ g'.rsp = g.rsp ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_82, W_87, o8, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  iskc

/-- `newPosition` set: `mov rdi, rbp`, to the `call` at 90. -/
theorem vc_82n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬g.rbx = 0) :
    W_82 F Wl (fun j' g' _ V' => j' = 90 ∧ g' = { g with rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_82, W_87, o8, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  iskc

/-- Back from `File.GetPosition`: `rax` stored to `*newPosition`, to 45. -/
theorem vc_95 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fw : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_95 F Wl (fun j' g' _ V' => j' = 45 ∧ g'.rsp = g.rsp ∧ V' = Vst V g.rbx (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [W_95, o4]
  iskc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFileStream::Seek` (`this` = `rdi`, `seekOrigin` = `edx`, `newPosition` = `rcx`) from its entry. For
`seekOrigin` at most 2 the run is at `File.seek`'s entry with the registers `gS` and the return address
`isk_at + 28` pushed (`kS`); back at 28 (`rsp` 24 below the entry's, `rbx` = `newPosition`, `rbp` = `this + 44`,
the frame `Frm` kept), on -1 at `0x5a0200`'s entry (`kE`), back at 61 likewise; with `newPosition` set at
`0x4560f0`'s entry with `rdi` = `this + 44` (`kP`), back at 95 likewise. The run reaches the return address with
`rbx`, `rbp`, `r12` restored and `rsp` 8 up (`kr`). -/
theorem isk_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L isk_at isk) (hinS : CodeIn L Fsk.fsk_at Fsk.fsk)
    {codeE : List Byte} (hinE : CodeIn L 0x5a0200#64 codeE) (hE : 0 < codeE.length)
    {codeP : List Byte} (hinP : CodeIn L 0x4560f0#64 codeP) (hP : 0 < codeP.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isk_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hS : 24 ≤ X.cpu.gpr.rsp.toNat) (hS8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (fw : ¬X.cpu.gpr.rcx = 0 → ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (hc : ¬X.cpu.gpr.rcx = 0 → X.cpu.gpr.rcx.toNat + 8 ≤ 2 ^ 64)
    (hap : ¬X.cpu.gpr.rcx = 0 →
      X.cpu.gpr.rcx.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rcx.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kS : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V3 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (isk_at.add 28) 8)) →
      Y.cpu.rip = Fsk.fsk_at → Y.cpu.gpr = (gS X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = isk_at.add 28 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kE : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rcx → Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 →
      Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (isk_at.add 61) 8)) →
      Y.cpu.rip = 0x5a0200#64 → Y.cpu.gpr = Z.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = isk_at.add 61 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
        Z₂.cpu.gpr.rbx = X.cpu.gpr.rcx → Z₂.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 →
        Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kP : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rcx → Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 →
      Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (isk_at.add 95) 8)) →
      Y.cpu.rip = 0x4560f0#64 →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := Z.cpu.gpr.rbp }).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = isk_at.add 95 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
        Z₂.cpu.gpr.rbx = X.cpu.gpr.rcx → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z' : State) (V'' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z'.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z'.cpu.gpr.rbp = X.cpu.gpr.rbp → Z'.cpu.gpr.r12 = X.cpu.gpr.r12 → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  -- from 45: the epilogue and the `ret`
  have k45 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = isk_at.add 45 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
      Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    rintro Z V' t' hKZ hAZ hrZ hzs ⟨f1, f2, f3, f4⟩
    refine (c_45 prof).run c hin (fun j' g' _ V'' => j' = 52 ∧ g'.rsp = Z.cpu.gpr.rsp + 8 + 8 + 8 ∧
        g'.rbx = rdq(V', Z.cpu.gpr.rsp) ∧ g'.rbp = rdq(V', Z.cpu.gpr.rsp + 8) ∧
        g'.r12 = rdq(V', Z.cpu.gpr.rsp + 8 + 8) ∧ V'' = V') hKZ hAZ hrZ
      (vc_45 (by rw [hzs]; exact h24) (by rw [hzs, b3s]; exact h16) (by rw [hzs, b3s, b2s]; exact h8)) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hg4, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU, hg1, hzs, b3s, b2s, b1s]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_52 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact f4) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z' V' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ ?_
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ']
      show U.cpu.gpr.rbx = _
      rw [hgU, hg2, hzs]
      exact f1
    · rw [hgZ']
      show U.cpu.gpr.rbp = _
      rw [hgU, hg3, hzs, b3s]
      exact f2
    · rw [hgZ']
      show U.cpu.gpr.r12 = _
      rw [hgU, hg4, hzs, b3s, b2s]
      exact f3
  -- from 95: `rax` stored to `*newPosition`
  have k95 : ¬X.cpu.gpr.rcx = 0 → ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = isk_at.add 95 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rcx → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
      GoG prof L o gev gP gE Z t' := by
    intro hb Z V' t' hKZ hAZ hrZ hzs hzb hF
    refine (c_95 prof).run c hin (fun j' g' _ V'' => j' = 45 ∧ g'.rsp = Z.cpu.gpr.rsp ∧
        V'' = Vst V' Z.cpu.gpr.rbx (toBytesLE Z.cpu.gpr.rax 8)) hKZ hAZ hrZ (vc_95 (by rw [hzb]; exact fw hb)) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact k45 U _ t₁ hKU hAU hrU (by rw [hgU, hg1, hzs])
      (by rw [hzb]; exact fr_st _ hS hS8 (hc hb) (hap hb) hF)
  -- from 82: `newPosition` set, `File.GetPosition`
  have k82 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = isk_at.add 82 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb hzp hF
    by_cases hb : X.cpu.gpr.rcx = 0
    · refine (c_82 prof).run c hin (fun j' g' _ V'' => j' = 45 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ V'' = V') hKZ hAZ hrZ
        (vc_82z (by rw [hzb]; exact hb)) ?_
      rintro j' g fl V₁ ⟨rfl, hg1, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact k45 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) hF
    · refine (c_82 prof).run c hin (fun j' g' _ V'' => j' = 90 ∧ g' = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbp } ∧
          V'' = V') hKZ hAZ hrZ (vc_82n (by rw [hzb]; exact hb)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgU]; exact hzs
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_90 _) hinP hP (by decide)
        (by rw [hsU]; exact hs4) ?_
      rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
      rw [hsU] at hAY
      exact kP Z V' hzs hzb hzp hF Y t₂ hKY hAY hrY (by rw [hgY, hsU, hgU]) (k95 hb)
  -- from 61: the `HRESULT` in `r12d`
  have k61 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = isk_at.add 61 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb hzp hF
    refine (c_61 prof).run c hin (fun j' g' _ V'' => j' = 82 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ g'.rbx = Z.cpu.gpr.rbx ∧
        g'.rbp = Z.cpu.gpr.rbp ∧ V'' = V') hKZ hAZ hrZ vc_61 ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact k82 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzb]) (by rw [hgU, hg3, hzp]) hF
  -- at 56: the `call` to `0x5a0200`
  have k56 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = isk_at.add 56 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb hzp hF
    refine c.s_call hKZ hAZ hin (lt_len (by decide)) hrZ (call_56 _) hinE hE (by decide)
      (by rw [hzs]; exact hs4) ?_
    rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
    rw [hzs] at hAY
    exact kE Z V' hzs hzb hzp hF Y t₂ hKY hAY hrY (by rw [hgY, hzs]) k61
  -- from 28: back from `File.seek`
  have k28 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = isk_at.add 28 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi + 44#64 → Frm X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
      GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzb hzp hF
    by_cases hb : X.cpu.gpr.rcx = 0
    · refine (c_28 prof).run c hin (fun j' g' _ V'' => (j' = 56 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ g'.rbx = Z.cpu.gpr.rbx ∧
          g'.rbp = Z.cpu.gpr.rbp ∧ V'' = V') ∨ (j' = 45 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ V'' = V')) hKZ hAZ hrZ
        (vc_28z (by rw [hzb]; exact hb)) ?_
      rintro j' g fl V₁ (⟨rfl, hg1, hg2, hg3, hV₁⟩ | ⟨rfl, hg1, hV₁⟩) U t₁ hKU hAU hrU hgU - <;> subst V₁
      · exact k56 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzb]) (by rw [hgU, hg3, hzp]) hF
      · exact k45 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) hF
    · refine (c_28 prof).run c hin (fun j' g' _ V'' => (j' = 56 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ g'.rbx = Z.cpu.gpr.rbx ∧
          g'.rbp = Z.cpu.gpr.rbp ∧ V'' = V') ∨
          (j' = 45 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ V'' = Vst V' Z.cpu.gpr.rbx (toBytesLE Z.cpu.gpr.rax 8))) hKZ hAZ hrZ
        (vc_28n (by rw [hzb]; exact hb) (by rw [hzb]; exact fw hb)) ?_
      rintro j' g fl V₁ (⟨rfl, hg1, hg2, hg3, hV₁⟩ | ⟨rfl, hg1, hV₁⟩) U t₁ hKU hAU hrU hgU - <;> subst V₁
      · exact k56 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzb]) (by rw [hgU, hg3, hzp]) hF
      · exact k45 U _ t₁ hKU hAU hrU (by rw [hgU, hg1, hzs])
          (by rw [hzb]; exact fr_st _ hS hS8 (hc hb) (hap hb) hF)
  -- from the entry
  have hrip' : X.cpu.rip = isk_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hF0 := fr_push V X.cpu.gpr hS hS8 hra
  refine (c_0 prof).run c hin (fun j' g' _ V' => (j' = 45 ∧ g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 ∧
      V' = V3 V X.cpu.gpr) ∨ (j' = 23 ∧ g' = gS X.cpu.gpr ∧ V' = V3 V X.cpu.gpr)) hK hA hrip'
    (vc_0 hs1 hs2 hs3) ?_
  rintro j' g fl V₁ (⟨rfl, hg1, hV₁⟩ | ⟨rfl, rfl, hV₁⟩) Y t₁ hKY hAY hrY hgY - <;> subst V₁
  · exact k45 Y _ t₁ hKY hAY hrY (by rw [hgY, hg1]) hF0
  · have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_23 _) hinS (Fsk.lt_len (by decide)) (by decide)
      (by rw [hsY]; exact hs4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    exact kS Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) k28

end FV7z.Isk
