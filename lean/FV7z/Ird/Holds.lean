import FV7z.Ird.Cuts
import FV7z.Irp.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `CInFileStream::Read (void *data, UInt32 size, UInt32 *processedSize)` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::Read` at `0x5a35a0` in `7zzs` (`CPP/7zip/Common/FileStreams.cpp`; `objdump -d`):
`rbp`, `rbx` saved, `rbp` = `this`, `rdi` = `this + 44` (`File`), `edx` = `size`, `rsp` 8 lower. With
`processedSize` set: the 4 bytes at it 0, `rbx` = it, `call` at 33 to `File.read_part` (`Irp.irp_at`); back at 38,
unless `rax` = -1, `eax` stored to `*processedSize`, `eax` = 0, to the epilogue (48). Without: `call` at 64 to the
same callee; back at 69, unless `rax` = -1, `eax` = 0, to 48. On -1: `call` at 80 to `0x5a0200` (the error as an
`HRESULT`); back at 85, `Callback` (the 8 bytes at `this + 248`, `cb`) 0: `eax` the `HRESULT` (or `E_FAIL`), to 48;
set: `rax` = its vtable, `rsi` = `CallbackRef` (the 8 bytes at `this + 256`), `edx` = the error, `call qword [rax]`
(113, `Seg.s_callM`); back at 115 the epilogue again. The epilogue: `add rsp, 8`, the two pops, `ret` (54, 121).

The callees are hypotheses, as in `FV7z.Isk`: each a continuation at its entry, given the run from its return (`rsp`
24 below the entry's, `rbp` = `this`, `rbx` = `processedSize` after the first `call`) on, with the saved registers
and the return address as they were (`Fr2`) (`kR1`, `kR2`, `kE`, `kcb`); `kr` takes the run on from the return
address. The store of `eax` to `*processedSize` lies apart from the saved registers and the return address
(`hap`), so the pops read them back (`fr2_st`). `CbOk`: what the `call` through `Callback`'s vtable needs of the
bytes at 85, for any bytes there (the callees before may have stored).

- `V2`: the bytes after the pushes; `Fr2`: the saved registers and the return address in the frame; `cb`, `vt`,
  `tg`: `Callback`, its vtable and the vtable's first entry.
- `vc_0z`, `vc_0n`, `vc_38`, `vc_48`, `vc_69`, `vc_85z`, `vc_85n`, `vc_115`: the verification conditions of the
  pieces (where a `cmp` picks the exit, the post is the two exits' disjunction).
- `ird_ok`: from the entry, through the callees, to the return address with `rbx`, `rbp` restored and `rsp` 8 up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ird

/-- The `call`s to `File.read_part`. -/
def pc33 : List Byte := [0xe8, 0xda, 0x2b, 0xeb, 0xff]
theorem pc33_0 : ∀ feat, Dec feat pc33 0 (FV7z.mk .call 64 [.rel 18446744073708186586] 5) := by dec_rfl
theorem wc_33 : pc33 <+: ird.drop 33 := by decide +kernel
theorem call_33 (feat : Features) : Dec feat ird 33 (FV7z.mk .call 64 [.rel 18446744073708186586] 5) :=
  Dec.shift (j := 33) (k := 0) (pc33_0 feat) wc_33 (Nat.zero_le _)
def pc64 : List Byte := [0xe8, 0xbb, 0x2b, 0xeb, 0xff]
theorem pc64_0 : ∀ feat, Dec feat pc64 0 (FV7z.mk .call 64 [.rel 18446744073708186555] 5) := by dec_rfl
theorem wc_64 : pc64 <+: ird.drop 64 := by decide +kernel
theorem call_64 (feat : Features) : Dec feat ird 64 (FV7z.mk .call 64 [.rel 18446744073708186555] 5) :=
  Dec.shift (j := 64) (k := 0) (pc64_0 feat) wc_64 (Nat.zero_le _)

/-- The `call` to `0x5a0200` (the error as an `HRESULT`). -/
def pc80 : List Byte := [0xe8, 0x0b, 0xcc, 0xff, 0xff]
theorem pc80_0 : ∀ feat, Dec feat pc80 0 (FV7z.mk .call 64 [.rel 18446744073709538315] 5) := by dec_rfl
theorem wc_80 : pc80 <+: ird.drop 80 := by decide +kernel
theorem call_80 (feat : Features) : Dec feat ird 80 (FV7z.mk .call 64 [.rel 18446744073709538315] 5) :=
  Dec.shift (j := 80) (k := 0) (pc80_0 feat) wc_80 (Nat.zero_le _)

/-- The `call` through `Callback`'s vtable. -/
def pcm : List Byte := [0xff, 0x10]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 0 64)] 2) := by dec_rfl
theorem wc_113 : pcm <+: ird.drop 113 := by decide +kernel
theorem call_113 (feat : Features) : Dec feat ird 113 (FV7z.mk .call 64 [.mem (mbd 0 0 64)] 2) :=
  Dec.shift (j := 113) (k := 0) (pcm_0 feat) wc_113 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_54 : pret <+: ird.drop 54 := by decide +kernel
theorem ret_54 (feat : Features) : Dec feat ird 54 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 54) (k := 0) (pret_0 feat) w_54 (Nat.zero_le _)
theorem w_121 : pret <+: ird.drop 121 := by decide +kernel
theorem ret_121 (feat : Features) : Dec feat ird 121 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 121) (k := 0) (pret_0 feat) w_121 (Nat.zero_le _)

theorem b3s (S : Addr) : S - 8 - 8 - 8#64 + 8#64 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem b2s (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem b1s (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The stack's addresses as numbers. -/
theorem sp_t (S : Addr) (h : 16 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 := by
  refine ⟨?_, ?_⟩ <;> bv_omega

/-- The bytes after the two pushes. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)
/-- The frame under the entry's `S`: the saved `rbx`, `rbp` of `g` and the return address `ra`. -/
abbrev Fr2 (S : Addr) (g : Gprs) (ra : Addr) (W : Addr → Byte) : Prop :=
  rdq(W, S - 8 - 8) = g.rbx ∧ rdq(W, S - 8) = g.rbp ∧ rdq(W, S) = ra
/-- `Callback` (`r` = `this`). -/
abbrev cb (W : Addr → Byte) (r : Addr) : Addr := rdq(W, r + 248#64)
/-- Its vtable. -/
abbrev vt (W : Addr → Byte) (r : Addr) : Addr := rdq(W, cb W r)
/-- The vtable's first entry. -/
abbrev tg (W : Addr → Byte) (r : Addr) : Addr := rdq(W, vt W r)
/-- What the `call` through `Callback`'s vtable needs of the bytes `W`: `Callback`, `CallbackRef` and the vtable's
first entry readable, and code at that entry. -/
abbrev CbOk (F : Footprint) (L : List (Addr × List Byte)) (W : Addr → Byte) (r : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add (cb W r) i)) ∧ (∀ i < 8, Foot F.data (Addr.add (r + 256#64) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (vt W r) i)) ∧ ∃ code : List Byte, CodeIn L (tg W r) code ∧ 0 < code.length

/-- A store at `x` apart from the frame keeps it. -/
theorem fr2_st {S x ra : Addr} {g : Gprs} {W : Addr → Byte} (bs : List Byte) (hS : 16 ≤ S.toNat)
    (hS8 : S.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + bs.length ≤ 2 ^ 64)
    (hap : x.toNat + bs.length ≤ S.toNat - 16 ∨ S.toNat + 8 ≤ x.toNat) (h : Fr2 S g ra W) :
    Fr2 S g ra (Vst W x bs) := by
  obtain ⟨s8, s16⟩ := sp_t S hS
  obtain ⟨f1, f2, f3⟩ := h
  have rd : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 → (x.toNat + bs.length ≤ y.toNat ∨ y.toNat + 8 ≤ x.toNat) →
      rdq(Vst W x bs, y) = rdq(W, y) := fun y hy hxy =>
    congrArg (ofBytesLE 64) (Tun.rd_Vst W x bs y 8 hx hy hxy)
  refine ⟨?_, ?_, ?_⟩
  · rw [rd (S - 8 - 8) (by omega) (by omega)]; exact f1
  · rw [rd (S - 8) (by omega) (by omega)]; exact f2
  · rw [rd S hS8 (by omega)]; exact f3

/-- The closers of the verification conditions; a disjunction of two exits' posts by either side. -/
local macro "irdc" : tactic => `(tactic| all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | (intro hh; contradiction)
    | exact rfl
    | (apply Or.inl; (repeat' (first | exact trivial | exact rfl | apply And.intro)); done)
    | (apply Or.inr; (repeat' (first | exact trivial | exact rfl | apply And.intro)); done)
    | apply And.intro
    | intro _)

variable {F : Footprint} {Wl : List Rgn}

/-- No `processedSize`: the pushes, `mov edx, edx; mov rbp, rdi; add rdi, 44; sub rsp, 8; test rcx, rcx; je`
taken, to the `call` at 64. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rcx = 0)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 64 ∧ g'.rsp = g.rsp - 8 - 8 - 8#64 ∧ g'.rbp = g.rdi ∧
      g'.rdi = g.rdi + 44#64 ∧ g'.rsi = g.rsi ∧ V' = V2 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V2] at h h1 h2 ⊢
  wpx [W_0, W_24, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  irdc

/-- `processedSize` set: `je` not taken, the 4 bytes at it 0, `mov rbx, rcx`, to the `call` at 33. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬g.rcx = 0)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add g.rcx i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 33 ∧ g'.rsp = g.rsp - 8 - 8 - 8#64 ∧ g'.rbp = g.rdi ∧
      g'.rdi = g.rdi + 44#64 ∧ g'.rsi = g.rsi ∧ g'.rbx = g.rcx ∧ V' = Vst (V2 V g) g.rcx (toBytesLE 0#32 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V2] at h h1 h2 fw ⊢
  wpx [W_0, W_24, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  irdc

/-- Back from `File.read_part` with `processedSize`: `cmp rax, -1; je` taken, to the `call` at 80; else `eax`
stored to `*processedSize`, `xor eax, eax`, to 48. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fw : ∀ i < 4, Foot Wl (Addr.add g.rbx i)) :
    W_38 F Wl (fun j' g' _ V' => (j' = 80 ∧ g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ V' = V) ∨
      (j' = 48 ∧ g'.rsp = g.rsp ∧ V' = Vst V g.rbx (toBytesLE (BitVec.setWidth 32 g.rax) 4))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw ⊢
  wpx [W_38, W_44, o2, o3]
  irdc

/-- Back from `File.read_part` without `processedSize`: `mov r8, rax; xor eax, eax; cmp r8, -1; jne` taken, to
48; else to the `call` at 80. -/
theorem vc_69 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_69 F Wl (fun j' g' _ V' => (j' = 48 ∧ g'.rsp = g.rsp ∧ V' = V) ∨
      (j' = 80 ∧ g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ V' = V)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only
  wpx [W_69, o5]
  irdc

/-- The epilogue: `add rsp, 8` and the two pops, to the `ret` at 54. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 54 ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 ∧ g'.rbx = rdq(V, g.rsp + 8#64) ∧
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 ⊢
  wpx [W_48, o4]
  irdc

/-- The same epilogue after `Callback`, to the `ret` at 121. -/
theorem vc_115 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_115 F Wl (fun j' g' _ V' => j' = 121 ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 ∧ g'.rbx = rdq(V, g.rsp + 8#64) ∧
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 ⊢
  wpx [W_115, o4]
  irdc

/-- Back from `0x5a0200`, `Callback` 0: `mov rdi, [rbp + 248]; mov r8d, eax; test rdi, rdi; je` taken, `eax` the
`HRESULT` (or `E_FAIL`), to 48. -/
theorem vc_85z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdq(V, g.rbp + 248#64) = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 248#64) i)) :
    W_85 F Wl (fun j' g' _ V' => j' = 48 ∧ g'.rsp = g.rsp ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_85, W_128, W_153, W_132, W_100, o6, o7, o8, o9, o10, Op.zxr16, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq]
  irdc

/-- `Callback` set: `je` not taken, `mov rax, [rdi]; mov rsi, [rbp + 256]; mov edx, r8d`, to the `call` at 113. -/
theorem vc_85n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬rdq(V, g.rbp + 248#64) = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 248#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbp + 248#64)) i))
    (fr : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 256#64) i)) :
    W_85 F Wl (fun j' g' _ V' => j' = 113 ∧ g'.rsp = g.rsp ∧ g'.rax = rdq(V, rdq(V, g.rbp + 248#64)) ∧
      g'.rdi = rdq(V, g.rbp + 248#64) ∧ g'.rsi = rdq(V, g.rbp + 256#64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa fs fr ⊢
  wpx [W_85, W_128, W_153, W_132, W_100, o6, o7, o8, o9, o10, Op.zxr16, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq]
  irdc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFileStream::Read` (`this` = `rdi`, `data` = `rsi`, `size` = `edx`, `processedSize` = `rcx`) from its entry.
With `processedSize` set the run is at `File.read_part`'s entry with the return address `ird_at + 38` pushed, `rbx`
= it and the 4 bytes at it 0 (`kR1`); without, with `ird_at + 69` pushed (`kR2`); each with `rsp` 24 below the
entry's, `rbp` = `this`, `rdi` = `this + 44`, `rsi` = `data`. Back with the frame `Fr2` kept, on -1 at `0x5a0200`'s
entry (`kE`), back at 85 likewise; with `Callback` set (`CbOk` of the bytes then, `hcb`) at its vtable's first entry
with `rdi` = `Callback`, `rsi` = `CallbackRef` (`kcb`), back at 115 likewise. The run reaches the return address with
`rbx`, `rbp` restored and `rsp` 8 up (`kr`). -/
theorem ird_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ird_at ird) (hinR : CodeIn L Irp.irp_at Irp.irp)
    {codeE : List Byte} (hinE : CodeIn L 0x5a0200#64 codeE) (hE : 0 < codeE.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ird_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hS : 16 ≤ X.cpu.gpr.rsp.toNat) (hS8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (fw : ¬X.cpu.gpr.rcx = 0 → ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (hc : ¬X.cpu.gpr.rcx = 0 → X.cpu.gpr.rcx.toNat + 4 ≤ 2 ^ 64)
    (hap : ¬X.cpu.gpr.rcx = 0 →
      X.cpu.gpr.rcx.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rcx.toNat)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 248#64) i))
    (hcb : ∀ W : Addr → Byte, ¬cb W X.cpu.gpr.rdi = 0 → CbOk F L W X.cpu.gpr.rdi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kR1 : ¬X.cpu.gpr.rcx = 0 → ∀ (G : Gprs) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst (V2 V X.cpu.gpr) X.cpu.gpr.rcx (toBytesLE 0#32 4))
        (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) (toBytesLE (ird_at.add 38) 8)) →
      Y.cpu.rip = Irp.irp_at → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      G.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → G.rbp = X.cpu.gpr.rdi → G.rdi = X.cpu.gpr.rdi + 44#64 →
      G.rsi = X.cpu.gpr.rsi → G.rbx = X.cpu.gpr.rcx →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ird_at.add 38 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbx = X.cpu.gpr.rcx → Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kR2 : X.cpu.gpr.rcx = 0 → ∀ (G : Gprs) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V2 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) (toBytesLE (ird_at.add 69) 8)) →
      Y.cpu.rip = Irp.irp_at → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      G.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → G.rbp = X.cpu.gpr.rdi → G.rdi = X.cpu.gpr.rdi + 44#64 →
      G.rsi = X.cpu.gpr.rsi →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ird_at.add 69 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kE : ∀ (G : Gprs) (V' : Addr → Byte), G.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → G.rbp = X.cpu.gpr.rdi →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) (toBytesLE (ird_at.add 85) 8)) →
      Y.cpu.rip = 0x5a0200#64 → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      (∀ (Z : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V'' →
        Z.cpu.rip = ird_at.add 85 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V'' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kcb : ∀ (G : Gprs) (V' : Addr → Byte), ¬cb V' X.cpu.gpr.rdi = 0 → G.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
      G.rdi = cb V' X.cpu.gpr.rdi → G.rsi = rdq(V', X.cpu.gpr.rdi + 256#64) →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) (toBytesLE (ird_at.add 115) 8)) →
      Y.cpu.rip = tg V' X.cpu.gpr.rdi → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      (∀ (Z : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V'' →
        Z.cpu.rip = ird_at.add 115 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
        Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V'' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z' : State) (V'' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z'.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z'.cpu.gpr.rbp = X.cpu.gpr.rbp → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  -- from 48: the epilogue and the `ret` at 54
  have k48 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ird_at.add 48 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    rintro Z V' t' hKZ hAZ hrZ hzs ⟨f1, f2, f3⟩
    refine (c_48 prof).run c hin (fun j' g' _ V'' => j' = 54 ∧ g'.rsp = Z.cpu.gpr.rsp + 8#64 + 8 + 8 ∧
        g'.rbx = rdq(V', Z.cpu.gpr.rsp + 8#64) ∧ g'.rbp = rdq(V', Z.cpu.gpr.rsp + 8#64 + 8) ∧ V'' = V') hKZ hAZ hrZ
      (vc_48 (by rw [hzs, b3s]; exact h16) (by rw [hzs, b3s, b2s]; exact h8)) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU, hg1, hzs, b3s, b2s, b1s]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_54 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact f3) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z' V' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ']
      show U.cpu.gpr.rbx = _
      rw [hgU, hg2, hzs, b3s]
      exact f1
    · rw [hgZ']
      show U.cpu.gpr.rbp = _
      rw [hgU, hg3, hzs, b3s, b2s]
      exact f2
  -- from 115: the epilogue and the `ret` at 121
  have k115 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ird_at.add 115 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    rintro Z V' t' hKZ hAZ hrZ hzs ⟨f1, f2, f3⟩
    refine (c_115 prof).run c hin (fun j' g' _ V'' => j' = 121 ∧ g'.rsp = Z.cpu.gpr.rsp + 8#64 + 8 + 8 ∧
        g'.rbx = rdq(V', Z.cpu.gpr.rsp + 8#64) ∧ g'.rbp = rdq(V', Z.cpu.gpr.rsp + 8#64 + 8) ∧ V'' = V') hKZ hAZ hrZ
      (vc_115 (by rw [hzs, b3s]; exact h16) (by rw [hzs, b3s, b2s]; exact h8)) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU, hg1, hzs, b3s, b2s, b1s]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_121 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact f3) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z' V' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ']
      show U.cpu.gpr.rbx = _
      rw [hgU, hg2, hzs, b3s]
      exact f1
    · rw [hgZ']
      show U.cpu.gpr.rbp = _
      rw [hgU, hg3, hzs, b3s, b2s]
      exact f2
  -- from 85: `Callback`
  have k85 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ird_at.add 85 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzp hF
    have fa' : ∀ i < 8, Foot F.data (Addr.add (Z.cpu.gpr.rbp + 248#64) i) := by rw [hzp]; exact fa
    by_cases hp : cb V' X.cpu.gpr.rdi = 0
    · refine (c_85 prof).run c hin (fun j' g' _ V'' => j' = 48 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ V'' = V') hKZ hAZ hrZ
        (vc_85z (by rw [hzp]; exact hp) fa') ?_
      rintro j' g fl V₁ ⟨rfl, hg1, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact k48 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) hF
    · obtain ⟨fs, fr, fb, codeF, hinF, hF0⟩ := hcb V' hp
      refine (c_85 prof).run c hin (fun j' g' _ V'' => j' = 113 ∧ g'.rsp = Z.cpu.gpr.rsp ∧
          g'.rax = rdq(V', rdq(V', Z.cpu.gpr.rbp + 248#64)) ∧ g'.rdi = rdq(V', Z.cpu.gpr.rbp + 248#64) ∧
          g'.rsi = rdq(V', Z.cpu.gpr.rbp + 256#64) ∧ V'' = V') hKZ hAZ hrZ
        (vc_85n (by rw [hzp]; exact hp) fa' (by rw [hzp]; exact fs) (by rw [hzp]; exact fr)) ?_
      rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hg4, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgU, hg1, hzs]
      have he : eaD U 0 0 = vt V' X.cpu.gpr.rdi := by
        show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 0 = _
        rw [hgU]
        show g.rax + BitVec.ofNat 64 0 = _
        rw [hg2, hzp]
        exact BitVec.add_zero _
      refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_113 _) (by rw [he]; exact fb) hinF hF0
        (by rw [he]; rfl) (by rw [hsU]; exact hs3) ?_
      rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
      rw [hsU] at hAY
      exact kcb U.cpu.gpr V' hp hsU (by rw [hgU, hg3, hzp]) (by rw [hgU, hg4, hzp]) hF Y t₂ hKY hAY hrY
        (by rw [hgY, hsU]) k115
  -- at 80: the `call` to `0x5a0200`
  have k80 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ird_at.add 80 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzp hF
    refine c.s_call hKZ hAZ hin (lt_len (by decide)) hrZ (call_80 _) hinE hE (by decide)
      (by rw [hzs]; exact hs3) ?_
    rintro Y t₂ hKY hAY ⟨hrY, hgY⟩
    rw [hzs] at hAY
    exact kE Z.cpu.gpr V' hzs hzp hF Y t₂ hKY hAY hrY (by rw [hgY, hzs]) k85
  -- from 69: back from `File.read_part` without `processedSize`
  have k69 : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = ird_at.add 69 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    intro Z V' t' hKZ hAZ hrZ hzs hzp hF
    refine (c_69 prof).run c hin (fun j' g' _ V'' => (j' = 48 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ V'' = V') ∨
        (j' = 80 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ g'.rbp = Z.cpu.gpr.rbp ∧ V'' = V')) hKZ hAZ hrZ vc_69 ?_
    rintro j' g fl V₁ (⟨rfl, hg1, hV₁⟩ | ⟨rfl, hg1, hg2, hV₁⟩) U t₁ hKU hAU hrU hgU - <;> subst V₁
    · exact k48 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) hF
    · exact k80 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzp]) hF
  -- from 38: back from `File.read_part` with `processedSize`
  have k38 : ¬X.cpu.gpr.rcx = 0 → ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = ird_at.add 38 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.rbx = X.cpu.gpr.rcx →
      Fr2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' → GoG prof L o gev gP gE Z t' := by
    intro hb Z V' t' hKZ hAZ hrZ hzs hzp hzb hF
    refine (c_38 prof).run c hin (fun j' g' _ V'' => (j' = 80 ∧ g'.rsp = Z.cpu.gpr.rsp ∧ g'.rbp = Z.cpu.gpr.rbp ∧
        V'' = V') ∨ (j' = 48 ∧ g'.rsp = Z.cpu.gpr.rsp ∧
        V'' = Vst V' Z.cpu.gpr.rbx (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4))) hKZ hAZ hrZ
      (vc_38 (by rw [hzb]; exact fw hb)) ?_
    rintro j' g fl V₁ (⟨rfl, hg1, hg2, hV₁⟩ | ⟨rfl, hg1, hV₁⟩) U t₁ hKU hAU hrU hgU - <;> subst V₁
    · exact k80 U V' t₁ hKU hAU hrU (by rw [hgU, hg1, hzs]) (by rw [hgU, hg2, hzp]) hF
    · exact k48 U _ t₁ hKU hAU hrU (by rw [hgU, hg1, hzs])
        (by
          rw [hzb]
          exact fr2_st _ hS hS8 (by rw [toBytesLE_length]; exact hc hb) (by rw [toBytesLE_length]; exact hap hb) hF)
  -- from the entry
  have hrip' : X.cpu.rip = ird_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hb : X.cpu.gpr.rcx = 0
  · -- no `processedSize`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 64 ∧ g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 ∧
        g'.rbp = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi + 44#64 ∧ g'.rsi = X.cpu.gpr.rsi ∧ V' = V2 V X.cpu.gpr)
      hK hA hrip' (vc_0z hb hs1 hs2) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hg4, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY, hg1]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_64 _) hinR (Irp.lt_len (by decide)) (by decide)
      (by rw [hsY]; exact hs3) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    exact kR2 hb Y.cpu.gpr Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY]) hsY (by rw [hgY, hg2]) (by rw [hgY, hg3])
      (by rw [hgY, hg4]) k69
  · -- `processedSize` set
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 33 ∧ g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 ∧
        g'.rbp = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi + 44#64 ∧ g'.rsi = X.cpu.gpr.rsi ∧
        g'.rbx = X.cpu.gpr.rcx ∧ V' = Vst (V2 V X.cpu.gpr) X.cpu.gpr.rcx (toBytesLE 0#32 4))
      hK hA hrip' (vc_0n hb hs1 hs2 (fw hb)) ?_
    rintro j' g fl V₁ ⟨rfl, hg1, hg2, hg3, hg4, hg5, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY, hg1]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_33 _) hinR (Irp.lt_len (by decide)) (by decide)
      (by rw [hsY]; exact hs3) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    exact kR1 hb Y.cpu.gpr Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY]) hsY (by rw [hgY, hg2]) (by rw [hgY, hg3])
      (by rw [hgY, hg4]) (by rw [hgY, hg5]) (k38 hb)

end FV7z.Ird
