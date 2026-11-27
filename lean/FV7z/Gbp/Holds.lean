import FV7z.Gbp.Cuts
import FV7z.Pvd.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.SetccM
import FV7z.Tun.Inv
/-!
# `Archive_GetItemBoolProp` (PLAN.md §M, M1)

7-Zip 26.06's `Archive_GetItemBoolProp (arc, index, propID, result)` at `0x5d15e0` in `7zzs`
(`CPP/7zip/UI/Common/OpenArchive.cpp`), `S` the stack pointer at the entry: `r12`, `rbp`, `rbx` pushed, `rbx` =
`result` (`rcx`), a frame of 32 bytes (`gq S`) with the stack guard (`fs:0x28`) at `gq S + 24`, `*result` = 0, the
`PROPVARIANT prop` at `gq S` cleared (`vt`, the 4 bytes at `gq S`, and the 8 bytes at `gq S + 8`), then
`arc->GetProperty (index, propID, &prop)` (`call qword [rax + 0x30]` at 59 through the vtable, `rcx` = `rbp` =
`&prop`). Back at 62: `res` (`eax`) into `r12d`; when it is 0 and `prop.vt` (the 2 bytes at `rsp`) is `VT_BOOL`
(11), `*result` = `prop.boolVal != 0` (the 2 bytes at `rsp + 8`; `setne byte [rbx]` at 134, a step of its own);
when it is 0 and `prop.vt` is neither `VT_BOOL` nor `VT_EMPTY`, `r12d` = `E_INVALIDARG` (`0x80004005`, `cmovne`).
Then `prop.~CPropVariant ()` (`call` at 94 to `Pvd.pvd_at`, `rdi` = `&prop`), the stack guard checked (99), the
frame dropped, `eax` = `r12d`, the registers popped and `ret` (126).

Both callees are hypotheses, as in `FV7z/Iag/Holds.lean`: continuations at their entries (`kf1`, `kf2`), each given
the run from its return to the next piece. `P1`, `P2` are what the callees leave.

- `gq`: the frame; `Vp`, `Vg`, `VC`: the bytes after the pushes, after the stack guard's store, at the first `call`;
  `gC`: the registers at the first `call`.
- `vtw V a`: the 2 bytes at `a`; `gres`: `r12` at 91; `bres`: the byte stored at `result`; `gV`: the bytes at 91.
- `vc_*`: the verification conditions of the pieces; `gbp_mid`: from 62 to 91, the four ways.
- `gbp_ok`: from the entry, through both callees, to the return address with `eax` = `gres` and `rbx`, `rbp`,
  `r12`, `rsp` restored (`kr`).

The reads at the entry (the stack guard, the vtable pointer, the vtable's entry) are stated on the bytes as they are
at the reads (`hcn`, `hvt`, `htgt`). Not covered: the stack guard failing (`__stack_chk_fail`, 139).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gbp

/-- The `call qword [rax + 0x30]` (`IInArchive::GetProperty`). -/
def pcm : List Byte := [0xff, 0x50, 0x30]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) := by dec_rfl
theorem wm_59 : pcm <+: gbp.drop 59 := by decide +kernel
theorem call_59 (feat : Features) : Dec feat gbp 59 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) :=
  Dec.shift (j := 59) (k := 0) (pcm_0 feat) wm_59 (Nat.zero_le _)

/-- The `call` to `CPropVariant::~CPropVariant`. -/
def pcall : List Byte := [0xe8, 0x1d, 0x59, 0xe8, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073708001565] 5) := by dec_rfl
theorem wc_94 : pcall <+: gbp.drop 94 := by decide +kernel
theorem call_94 (feat : Features) : Dec feat gbp 94 (FV7z.mk .call 64 [.rel 18446744073708001565] 5) :=
  Dec.shift (j := 94) (k := 0) (pcall_0 feat) wc_94 (Nat.zero_le _)
theorem tgt_94 : gbp_at.add (94 + 5) + BitVec.ofNat 64 18446744073708001565 = Pvd.pvd_at := by decide

/-- The `setne byte [rbx]`. -/
def pset : List Byte := [0x0f, 0x95, 0x03]
theorem pset_0 : ∀ feat, Dec feat pset 0 (FV7z.mk (.setcc 5) 8 [.mem (mbd 3 0 8)] 3) := by dec_rfl
theorem ws_134 : pset <+: gbp.drop 134 := by decide +kernel
theorem set_134 (feat : Features) : Dec feat gbp 134 (FV7z.mk (.setcc 5) 8 [.mem (mbd 3 0 8)] 3) :=
  Dec.shift (j := 134) (k := 0) (pset_0 feat) ws_134 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_126 : pret <+: gbp.drop 126 := by decide +kernel
theorem ret_126 (feat : Features) : Dec feat gbp 126 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 126) (k := 0) (pret_0 feat) w_126 (Nat.zero_le _)

/-- The frame: `rsp` after the three pushes and `sub rsp, 0x20`. -/
abbrev gq (S : Addr) : Addr := S - 8 - 8 - 8 - 32#64

/-- The bytes after the pushes of `r12`, `rbp`, `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The bytes after the stack guard `cn` is stored at `gq S + 24`. -/
abbrev Vg (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vp V g) (gq g.rsp + 24#64) (toBytesLE cn 8)

/-- The bytes at the first `call`: `*result` = 0, `prop` cleared. -/
abbrev VC (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vg V g cn) g.rcx (toBytesLE 0#8 1)) (gq g.rsp) (toBytesLE 0#32 4)) (gq g.rsp + 8#64)
    (toBytesLE 0#64 8)

/-- The registers at the first `call`: `rax` the vtable `vt`, `rcx` = `rbp` = `rsp` = `&prop`, `rbx` = `result`. -/
abbrev gC (g : Gprs) (vt : BitVec 64) : Gprs :=
  { g with
      rax := vt,
      rcx := gq g.rsp,
      rbx := g.rcx,
      rbp := gq g.rsp,
      rsp := gq g.rsp }

/-- The low 32 bits, zero-extended. -/
abbrev zl (a : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 a)

/-- The 2 bytes at `a`. -/
abbrev vtw (V : Addr → Byte) (a : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs a 2).map V)

/-- `r12` at 91: `E_INVALIDARG` when `GetProperty` answered 0 and `prop.vt` is neither `VT_BOOL` nor `VT_EMPTY`,
else the answer's low 32 bits. -/
def gres (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  if g.rax.setWidth 32 = 0#32 ∧ vtw V g.rsp ≠ 11#16 ∧ vtw V g.rsp ≠ 0#16 then 2147500037#64 else zl g.rax

/-- The byte stored at `result`: `prop.boolVal != 0`. -/
abbrev bres (V : Addr → Byte) (S : Addr) : BitVec 8 :=
  (BitVec.ofBool (!decide (vtw V (S + 8#64) = 0#16))).setWidth 8

/-- The bytes at 91: `*result` = `bres` when `GetProperty` answered 0 and `prop.vt` is `VT_BOOL`. -/
def gV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if g.rax.setWidth 32 = 0#32 ∧ vtw V g.rsp = 11#16 then Vst V g.rbx (toBytesLE (bres V g.rsp) 1) else V

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

theorem sw3' (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem g32 (x : Addr) : gq x + 32#64 = x - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- The closer of the pieces' conditions. -/
local macro "gcl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- From the entry to the first `call`: the pushes, the stack guard stored, `*result` = 0, `prop` cleared,
`rax` the vtable. -/
theorem vc_0 {cn vt : BitVec 64}
    (hcn : rdq(Vp V g, fb + 40#64) = cn) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hvt : rdq(Vg V g cn, g.rdi) = vt) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (gq g.rsp + 24#64) i)) (w5 : ∀ i < 1, Foot Wl (Addr.add g.rcx i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (gq g.rsp) i)) (w7 : ∀ i < 8, Foot Wl (Addr.add (gq g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 59 ∧ g' = gC g vt ∧ V' = VC V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, Vg, VC, gC, gq] at hcn hvt w1 w2 w3 w4 w5 w6 w7 ⊢
  wpx [W_0, o0, Op.ldf, hcn, hvt, xz, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies,
    implies_true]
  gcl

/-- From 62, `GetProperty`'s answer not 0: to 91. -/
theorem vc_62n (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_62 fb F Wl (fun j' g' _ V' => j' = 91 ∧ (∃ ra, g' = { g with rax := ra, r12 := zl g.rax }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_62, o1, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  gcl
  all_goals exact ⟨_, rfl⟩

/-- From 62, the answer 0, `prop.vt` `VT_EMPTY`: to 91, `r12` the answer. -/
theorem vc_62z (hz : g.rax.setWidth 32 = 0#32) (h11 : vtw V g.rsp ≠ 11#16) (h0 : vtw V g.rsp = 0#16)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsp i)) :
    W_62 fb F Wl (fun j' g' _ V' => j' = 91 ∧ (∃ ra, g' = { g with rax := ra, r12 := zl g.rax }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw] at hz h11 h0 ft ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  have e11 := decide_eq_false h11
  have e0 : (ofBytesLE 16 ((byteAddrs rsp 2).map V) == 0) = true := beq_iff_eq.2 h0
  wpx [W_62, W_69, W_79, o1, o2, o3, e, e11, e0, sw3', BitVec.and_self, decide_false, decide_true,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true, ↓reduceIte]
  gcl
  all_goals exact ⟨_, rfl⟩

/-- From 62, the answer 0, `prop.vt` neither `VT_BOOL` nor `VT_EMPTY`: to 91, `r12` = `E_INVALIDARG`. -/
theorem vc_62e (hz : g.rax.setWidth 32 = 0#32) (h11 : vtw V g.rsp ≠ 11#16) (h0 : vtw V g.rsp ≠ 0#16)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsp i)) :
    W_62 fb F Wl (fun j' g' _ V' => j' = 91 ∧ (∃ ra, g' = { g with rax := ra, r12 := 2147500037#64 }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw] at hz h11 h0 ft ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  have e11 := decide_eq_false h11
  have e0 : (ofBytesLE 16 ((byteAddrs rsp 2).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_62, W_69, W_79, o1, o2, o3, e, e11, e0, sw3', BitVec.and_self, BitVec.reduceSetWidth, decide_false,
    decide_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true, ↓reduceIte]
  gcl
  all_goals exact ⟨_, rfl⟩

/-- From 62, the answer 0, `prop.vt` `VT_BOOL`: `cmp word [rsp + 8], 0`, to the `setne` at 134. -/
theorem vc_62b (hz : g.rax.setWidth 32 = 0#32) (h11 : vtw V g.rsp = 11#16)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsp i)) (f8 : ∀ i < 2, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_62 fb F Wl (fun j' g' f' V' => j' = 134 ∧ (∃ ra, g' = { g with rax := ra, r12 := zl g.rax }) ∧
      f'.zf = decide (vtw V (g.rsp + 8#64) = 0#16) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw] at hz h11 ft f8 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_62, W_69, W_128, o1, o2, o7, Op.cmpmi, e, h11, sw3', BitVec.and_self, decide_false, decide_true,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  gcl
  all_goals exact ⟨_, rfl⟩

/-- 91: `mov rdi, rbp`, to the `call` at 94. -/
theorem vc_91 : W_91 fb F Wl (fun j' g' _ V' => j' = 94 ∧ g' = { g with rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_91, o4]
  gcl

/-- From 99: the stack guard checked, the frame dropped, `eax` = `r12d`, the pops, to the `ret` at 126. -/
theorem vc_99 {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8) i))
    (h : ∀ fl, Q 126
      { g with
          rax := zl g.r12,
          rbx := rdq(V, g.rsp + 32#64),
          rbp := rdq(V, g.rsp + 32#64 + 8),
          rsp := g.rsp + 32#64 + 8 + 8 + 8,
          r12 := rdq(V, g.rsp + 32#64 + 8 + 8) } fl V) :
    W_99 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 l1 l2 l3 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_99, W_115, o5, o6, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 62 (back from `GetProperty`, `rsp` = `&prop`, `rbx` = `result`) to 91: `r12` = `gres`, `rax` some value,
the bytes `gV`. -/
theorem gbp_mid {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L gbp_at gbp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gbp_at.add 62)
    (f0 : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f8 : ∀ i < 2, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (wb : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rbx i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (gV V X.cpu.gpr) →
      Y.cpu.rip = gbp_at.add 91 → (∃ ra, Y.cpu.gpr = { X.cpu.gpr with rax := ra, r12 := gres V X.cpu.gpr }) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- the three ways that store nothing
  have go : ∀ R : BitVec 64, R = gres V X.cpu.gpr → gV V X.cpu.gpr = V →
      W_62 fb F Wl (fun j' g' _ V' => j' = 91 ∧ (∃ ra, g' = { X.cpu.gpr with rax := ra, r12 := R }) ∧ V' = V)
        X.cpu.gpr X.cpu.rflags V → GoG prof L o gev gP gE X t := by
    intro R hR hv hw
    refine (c_62 prof fb).run c hfs hin _ hK hA hrip hw ?_
    rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k Y t₁ hKY (by rw [hv]; exact hAY) hrY ⟨ra, by rw [hgY, hR]⟩
  by_cases hz : X.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases hb : vtw V X.cpu.gpr.rsp = 11#16
    · -- `VT_BOOL`: to the `setne` at 134
      refine (c_62 prof fb).run c hfs hin _ hK hA hrip (vc_62b hz hb f0 f8) ?_
      rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hzf, hV₁⟩ Y t₁ hKY hAY hrY hgY hfY
      subst V₁
      have he : eaD Y 3 0 = X.cpu.gpr.rbx := by
        show Y.cpu.gpr.get (regOf 3) + BitVec.ofNat 64 0 = _
        rw [hgY]
        exact BitVec.add_zero _
      refine c.s_setcc_m8 hKY hAY hin (lt_len (by decide)) hrY (set_134 _) (by rw [he]; exact wb) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
      have hb' : Y.cpu.rflags.cond 5 = !decide (vtw V (X.cpu.gpr.rsp + 8#64) = 0#16) := by
        rw [hfY, cond_5, hzf]
      rw [he, hb'] at hA₂
      refine (c_137 prof fb).run c hfs hin (fun j' g' _ V' => j' = 91 ∧ g' = Y.cpu.gpr ∧
          V' = Vst V X.cpu.gpr.rbx (toBytesLE (bres V X.cpu.gpr.rsp) 1)) hK₂ hA₂ hr₂
        (by unfold W_137; exact ⟨rfl, hg₂, rfl⟩) ?_
      rintro j' g fl' V₂ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
      refine k U t₃ hKU (by unfold gV; rw [if_pos ⟨hz, hb⟩]; exact hAU) hrU ⟨ra, ?_⟩
      rw [hgU, hgY]
      unfold gres
      rw [if_neg fun h => h.2.1 hb]
    · by_cases h0 : vtw V X.cpu.gpr.rsp = 0#16
      · exact go (zl X.cpu.gpr.rax) (by unfold gres; exact (if_neg fun h => h.2.2 h0).symm)
          (by unfold gV; exact if_neg fun h => hb h.2) (vc_62z hz hb h0 f0)
      · exact go 2147500037#64 (by unfold gres; exact (if_pos ⟨hz, hb, h0⟩).symm)
          (by unfold gV; exact if_neg fun h => hb h.2) (vc_62e hz hb h0 f0)
  · exact go (zl X.cpu.gpr.rax) (by unfold gres; exact (if_neg fun h => hz h.1).symm)
      (by unfold gV; exact if_neg fun h => hz h.1) (vc_62n hz)

/-- `Archive_GetItemBoolProp (arc, index, propID, result)` (`rdi`, `esi`, `edx`, `rcx`) from its entry, the stack
guard `cn` (the 8 bytes at `fs:0x28`), the vtable `vt` (the 8 bytes at `arc`) and `GetProperty`'s entry `eF` (the 8
bytes at `vt + 0x30`) as read. At `eF` the registers are `gC` with `rsp` 8 below the frame and the bytes `VC` with the
return address pushed (`kf1`); if `GetProperty` returns to `gbp_at + 62` with `rsp`, `rbp` the frame and `rbx` =
`result`, the run reaches `~CPropVariant`'s entry with `rdi` = `&prop`, `r12` = `gres`, the bytes `gV` and the
return address `gbp_at + 99` pushed (`kf2`); if that returns with `rsp` the frame, `r12` as at its entry, the stack
guard as at `fs:0x28` and the saved registers and the return address as they were, the run reaches the return
address with `eax` = `gres`'s low 32 bits and `rbx`, `rbp`, `r12`, `rsp` restored (`kr`). -/
theorem gbp_ok {fb eF : Addr} {cn vt : BitVec 64} {P1 : State → (Addr → Byte) → Prop}
    {P2 : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L gbp_at gbp)
    (hinP : CodeIn L Pvd.pvd_at Pvd.pvd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gbp_at)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 24#64) i))
    (w5 : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (gq X.cpu.gpr.rsp) i))
    (w7 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 8#64) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcn : rdq(Vp V X.cpu.gpr, fb + 40#64) = cn) (hvt : rdq(Vg V X.cpu.gpr cn, X.cpu.gpr.rdi) = vt)
    (fv : ∀ i < 8, Foot F.data (Addr.add (vt + 48#64) i))
    {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(VC V X.cpu.gpr cn, vt + 48#64) = eF)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VC V X.cpu.gpr cn) (gq X.cpu.gpr.rsp - 8) (toBytesLE (gbp_at.add 62) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC X.cpu.gpr vt).set 4 (gq X.cpu.gpr.rsp - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = gbp_at.add 62 → Z.cpu.gpr.rsp = gq X.cpu.gpr.rsp → Z.cpu.gpr.rbp = gq X.cpu.gpr.rsp →
        Z.cpu.gpr.rbx = X.cpu.gpr.rcx → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), P1 Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (gV V' Z.cpu.gpr) (gq X.cpu.gpr.rsp - 8) (toBytesLE (gbp_at.add 99) 8)) →
      Y.cpu.rip = Pvd.pvd_at →
      (∃ ra, Y.cpu.gpr = ({ Z.cpu.gpr with
          rax := ra,
          rdi := Z.cpu.gpr.rbp,
          r12 := gres V' Z.cpu.gpr }).set 4 (Z.cpu.gpr.rsp - 8)) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = gbp_at.add 99 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp → W.cpu.gpr.r12 = gres V' Z.cpu.gpr →
        rdq(V'', gq X.cpu.gpr.rsp + 24#64) = rdq(V'', fb + 40#64) →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V'', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ →
        P2 Z W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (W : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat),
      P1 Z V' → P2 Z W V'' → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := zl (gres V' Z.cpu.gpr),
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8,
          r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = gbp_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 59 ∧ g' = gC X.cpu.gpr vt ∧
      V' = VC V X.cpu.gpr cn) hK hA hrip' (vc_0 hcn fc hvt fa w1 w2 w3 w4 w5 w6 w7) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = gq X.cpu.gpr.rsp := by rw [hgY]
  have he : eaD Y 0 48 = vt + 48#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 48 = _
    rw [hgY]
    rfl
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_59 _) (by rw [he]; exact fv) hinF hF0
    (by rw [he]; exact htgt) (by rw [hsY]; exact w8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY]; try rfl) ?_
  -- back from `GetProperty`, to 91
  intro Z V' t'' hKZ hAZ hrZ hzs hzp hzb hP1
  have f0 : ∀ i < 2, Foot F.data (Addr.add Z.cpu.gpr.rsp i) := by
    rw [hzs]
    exact fun i hi => c.hws _ (w6 i (by omega))
  have f8 : ∀ i < 2, Foot F.data (Addr.add (Z.cpu.gpr.rsp + 8#64) i) := by
    rw [hzs]
    exact fun i hi => c.hws _ (w7 i (by omega))
  refine gbp_mid c hfs hin hKZ hAZ hrZ f0 f8 (by rw [hzb]; exact w5) ?_
  rintro U t₃ hKU hAU hrU ⟨ra, hgU⟩
  -- `mov rdi, rbp` and the `call` to `~CPropVariant`
  refine (c_91 prof fb).run c hfs hin (fun j' g' _ V₂ => j' = 94 ∧ g' = { U.cpu.gpr with rdi := U.cpu.gpr.rbp } ∧
      V₂ = gV V' Z.cpu.gpr) hKU hAU hrU vc_91 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U₁ t₄ hKU₁ hAU₁ hrU₁ hgU₁ -
  have hsU₁ : U₁.cpu.gpr.rsp = gq X.cpu.gpr.rsp := by
    rw [hgU₁, hgU]
    exact hzs
  refine c.s_call hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (call_94 _) hinP (Pvd.lt_len (j := 0) (by decide)) tgt_94
    (by rw [hsU₁]; exact w8) ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU₁] at hA₃
  refine kf2 Z V' Y₃ t₅ hP1 hK₃ hA₃ hr₃ ⟨ra, by rw [hg₃, hgU₁, hgU]; try rfl⟩ ?_
  -- back from `~CPropVariant`
  intro W V'' t₆ hKW hAW hrW hws hw12 hcw hb1 hb2 hb3 hra hP2
  have f24 : ∀ i < 8, Foot F.data (Addr.add (gq X.cpu.gpr.rsp + 24#64) i) := fun i hi => c.hws _ (w4 i hi)
  have l3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (w3 i hi)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (w2 i hi)
  have l1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (w1 i hi)
  refine (c_99 prof fb).run c hfs hin (fun j' g' _ V₃ => j' = 126 ∧
      g' = { W.cpu.gpr with
          rax := zl (gres V' Z.cpu.gpr),
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp,
          r12 := X.cpu.gpr.r12 } ∧ V₃ = V'') hKW hAW hrW
    (vc_99 (by rw [hws]; exact hcw) (by rw [hws]; exact f24) fc (by rw [hws, g32]; exact l3)
      (by rw [hws, g32, a3s]; exact l2) (by rw [hws, g32, a3s, a2s]; exact l1)
      fun _ => ⟨rfl, by rw [hw12, hws, g32, a3s, a2s, a1s, hb3, hb2, hb1], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₇ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₄
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_126 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hra) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' W V'' Z' t₈ hP1 hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Gbp
