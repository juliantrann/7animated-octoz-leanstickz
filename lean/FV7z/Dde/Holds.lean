import FV7z.Dde.Cuts
import FV7z.Mls.Blocks1
import FV7z.Lemmas.LeafRet
/-!
# `NWindows::NFile::NFind::DoesDirExist` (PLAN.md §M, M1)

7-Zip 26.06's `DoesDirExist (name, followLink)` at `0x455cf0` in `7zzs` (`CPP/Windows/FileFind.cpp`; `objdump -d`),
`S` the stack pointer at the entry: a frame of 168 bytes (`aQ S` = `S - 168`) with the stack guard (`fs:0x28`) at
`aQ S + 152` (`Vo`), the `struct stat` at `aQ S`; `MY_lstat (name, &st, followLink)` (`Mls.mls_at`, call at 37,
`edx` = `followLink`'s byte zero-extended, registers `aG`); back at 42: when its answer (`eax`) is not 0, `al` = 0,
else `al` = 1 exactly when `st.st_mode & S_IFMT` (the 4 bytes at `rsp + 24`) is `S_IFDIR` (`dres`); the stack guard
checked, the frame dropped, the `ret` (95).

- `dde_call`: from the entry to `MY_lstat`'s entry, the return address `dde_at + 42` below the frame;
- `dde_ret`: from 42, the stack guard as at `fs:0x28`, to the return address with `al` = `dres`.

Not covered: the stack guard failing (`__stack_chk_fail`, 96).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dde

theorem dde_37 : ∀ feat, Dec feat dde 37 (FV7z.mk .call 64 [.rel 18446744073709550470] 5) := by intro feat f; rfl
theorem dde_95 : ∀ feat, Dec feat dde 95 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The stack pointer after `sub rsp, 168`. -/
abbrev aQ (S : Addr) : Addr := S - 168#64

/-- The bytes at `MY_lstat`'s call: the stack guard `cn` stored at `aQ S + 152`. -/
abbrev Vo (V : Addr → Byte) (S : Addr) (cn : BitVec 64) : Addr → Byte := Vst V (aQ S + 152#64) (toBytesLE cn 8)

/-- At `MY_lstat`'s call: `rax` 0, `edx` the byte `followLink` (`sil`), `rsi` the `struct stat` (`rsp`). -/
abbrev aG (g : Gprs) : Gprs :=
  { g with
    rax := 0#64
    rdx := ((g.rsi.setWidth 8).setWidth 32).setWidth 64
    rsp := aQ g.rsp
    rsi := aQ g.rsp }

/-- `st.st_mode`, the 4 bytes at `rsp + 24`. -/
abbrev mode (V : Addr → Byte) (S : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs (S + 24#64) 4).map V)

/-- The answer's low byte: 1 when `MY_lstat` answered 0 and `st_mode` is a directory. -/
def dres (V : Addr → Byte) (g : Gprs) : BitVec 8 :=
  if g.rax.setWidth 32 = 0#32 ∧ mode V g.rsp &&& 61440#32 = 16384#32 then 1#8 else 0#8

/-- The registers kept from `g` to `g'`. -/
def K6 (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem pa (S : Addr) : S + 168#64 + 8 = S + 176#64 := by bv_omega

/-- A low byte made of a `wrLo` (`setcc`), bit by bit: equal to a literal. -/
local macro "lob" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry to the call: the frame, the stack guard stored, `edx`, `rsi`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64}
    (hcn : rdq(V, fb + 40#64) = cn) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ g.rsp + 152#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 37 ∧ g' = aG g ∧ V' = Vo V g.rsp cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vo, aQ, aG] at hcn wc ⊢
  wpx [W_0, o0, Op.ldf, Op.zxr, hcn, xz, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies,
    implies_true]
  all_goals vfin

/-- From 42, `MY_lstat`'s answer not 0: `eax` 0, to 69. -/
theorem vc_42n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 69 ∧ (∃ ra rr, g' = { g with rax := ra, r8 := rr } ∧ ra.setWidth 8 = 0#8) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_42, W_52, o1, o2, xz, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin
  all_goals exact ⟨_, _, rfl, rfl⟩

/-- From 42, `MY_lstat`'s answer 0 and `st_mode` a directory: `al` 1, to 69. -/
theorem vc_42d {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 = 0#32)
    (hd : mode V g.rsp &&& 61440#32 = 16384#32) (fm : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 69 ∧ (∃ ra rr, g' = { g with rax := ra, r8 := rr } ∧ ra.setWidth 8 = 1#8) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [mode] at hz hd fm ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_42, W_52, o1, o2, Op.setcc, xz, e, hd, BitVec.and_self, decide_true, BitVec.ofBool_true,
    BitVec.reduceSetWidth, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals vfin
  all_goals exact ⟨_, _, rfl, by lob⟩

/-- From 42, `MY_lstat`'s answer 0 and `st_mode` not a directory: `al` 0, to 69. -/
theorem vc_42f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 = 0#32)
    (hd : mode V g.rsp &&& 61440#32 ≠ 16384#32) (fm : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 69 ∧ (∃ ra rr, g' = { g with rax := ra, r8 := rr } ∧ ra.setWidth 8 = 0#8) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [mode] at hz hd fm ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  have d := decide_eq_false hd
  wpx [W_42, W_52, o1, o2, Op.setcc, xz, e, d, BitVec.and_self, BitVec.ofBool_false, BitVec.reduceSetWidth,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals vfin
  all_goals exact ⟨_, _, rfl, by lob⟩

/-- From 69: the stack guard checked, the frame dropped, to the `ret` (95). -/
theorem vc_69 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 152#64) = rdq(V, fb + 40#64)) (f152 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 152#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) :
    W_69 fb F Wl (fun j' g' _ V' => j' = 95 ∧ (∃ rc, g' = { g with rcx := rc, rsp := g.rsp + 168#64 }) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f152 ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_69, W_88, o3, o4, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin
  all_goals exact ⟨_, rfl⟩

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `DoesDirExist (name, followLink)` from its entry, the stack guard's 8 bytes at `fs:0x28` readable, the guard's
slot and the call's return address's slot below the frame in what the run may store into: at `MY_lstat`'s entry with
the registers `aG` (`rdi` = `name`, `rsi` = `aQ S`), the stack guard stored (`Vo`) and the return address
`dde_at + 42` below the frame. -/
theorem dde_call {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dde_at dde)
    (hinM : CodeIn L Mls.mls_at Mls.mls) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = dde_at) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 152#64) i))
    (wr : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (dde_at.add 42) 8)) →
      Y.cpu.rip = Mls.mls_at → Y.cpu.gpr = (aG X.cpu.gpr).set 4 (aQ X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 37 ∧ g' = aG X.cpu.gpr ∧
      V' = Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 rfl hcl wc) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (dde_37 _) hinM (Mls.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact wr) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From 69 to the return address (at `rsp + 168`): `rax` and the registers `K6` as at 69, `rsp` 176 above. -/
theorem dde_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dde_at dde)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dde_at.add 69)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f152 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 152#64) i))
    (f168 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 168#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 168#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 176#64 → Z.cpu.gpr.rax = X.cpu.gpr.rax → K6 X.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_69 prof fb).run c hfs hin _ hK hA hrip (vc_69 (g := X.cpu.gpr) hc f152 hcl) ?_
  rintro j' g fl V₃ ⟨rfl, ⟨rc, rfl⟩, rfl⟩ Y t₃ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 168#64 := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (dde_95 _) (by rw [hsY]; exact f168) hin₂ h₂
    (by rw [hsY]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₄ hKZ hAZ hrZ (by rw [hgZ]; show Y.cpu.gpr.rsp + 8 = _; rw [hsY, pa]) (by rw [hgZ, hgY]; try rfl) ?_
  rw [hgZ, hgY]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `DoesDirExist` from the return of `MY_lstat` (42), the frame's `st_mode`, stack guard and return address readable,
the stack guard at `rsp + 152` the one at `fs:0x28`: at the return address (at `rsp + 168`) with `al` = `dres`
(`MY_lstat`'s answer 0 and `st_mode` a directory), `rsp` 176 above, the registers `K6` as they were. -/
theorem dde_ret {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dde_at dde)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dde_at.add 42)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f24 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f152 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 152#64) i))
    (f168 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 168#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 168#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 176#64 → Z.cpu.gpr.rax.setWidth 8 = dres V X.cpu.gpr →
      K6 X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- the three ways to 69, each with `al` and `rax`, `r8` changed
  have go : ∀ b : BitVec 8, b = dres V X.cpu.gpr →
      W_42 fb F Wl (fun j' g' _ V' => j' = 69 ∧
        (∃ ra rr, g' = { X.cpu.gpr with rax := ra, r8 := rr } ∧ ra.setWidth 8 = b) ∧ V' = V) X.cpu.gpr
        X.cpu.rflags V → GoG prof L o gev gP gE X t := by
    intro b hb hw
    refine (c_42 prof fb).run c hfs hin _ hK hA hrip hw ?_
    rintro j' g fl V₁ ⟨rfl, ⟨ra, rr, rfl, h8⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine dde_tail c hfs hin hKY hAY hrY hcl (by rw [hsY]; exact f152) (by rw [hsY]; exact f168)
      (by rw [hsY]; exact hc) hin₂ h₂ (by rw [hsY]; exact hra) ?_
    intro Z t' hKZ hAZ hrZ hsZ haZ hkZ
    refine k Z t' hKZ hAZ hrZ (by rw [hsZ, hsY]) (by rw [haZ, hgY]; exact h8.trans hb) ?_
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hkZ
    rw [hgY] at k1 k2 k3 k4 k5 k6
    exact ⟨k1, k2, k3, k4, k5, k6⟩
  by_cases hz : X.cpu.gpr.rax.setWidth 32 = 0#32
  · by_cases hd : mode V X.cpu.gpr.rsp &&& 61440#32 = 16384#32
    · exact go 1#8 (by unfold dres; exact (ite_cond_eq_true _ _ (eq_true ⟨hz, hd⟩)).symm) (vc_42d hz hd f24)
    · exact go 0#8 (by unfold dres; exact (ite_cond_eq_false _ _ (eq_false fun h => hd h.2)).symm) (vc_42f hz hd f24)
  · exact go 0#8 (by unfold dres; exact (ite_cond_eq_false _ _ (eq_false fun h => hz h.1)).symm) (vc_42n hz)

end FV7z.Dde
