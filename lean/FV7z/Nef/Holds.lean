import FV7z.Nef.Cuts
import FV7z.Lemmas.Rmw3
import FV7z.Raf.Holds
/-!
# `__new_exitfn` gives the first place of the first list (PLAN.md G3, startup)

glibc 2.31's `__new_exitfn (listp)` at `0x623430` in `7zzs`, as the first `__cxa_atexit` of a run calls it: no exit
function ran (`__exit_funcs_done` at `0x7a3a94` is 0), the list `l` that `listp` points at has no place taken
(`idx` at `l + 8` is 0) and no list after it (`next` at `l` is 0). The function sets `idx` 1, marks place 0 taken
(its `flavor` at `l + 16` becomes 1, `ef_us`), counts the call in `__new_exitfn_called` at `0x7a8408` and returns the
place's address `l + 16`.

- `ad_156`, `ret_170`: the instructions outside the blocks.
- `vc_*`: the verification conditions of the pieces.
- `nef_first`: the run reaches the return address with `rax = l + 16`, the registers a call keeps as at the entry,
  the bytes outside the frame, the 16 bytes at `l + 8` and the counter as they were.

The ways with places taken, a full list (`calloc`) and the assertion are not ones of this call.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out sk0')
open FV7z.Raf (Out off_ft rd_out2)
namespace FV7z.Nef

/-- `add qword [0x7a8408], 1`. -/
def pad : List Byte := [0x48, 0x83, 0x05, 0x34, 0x4f, 0x18, 0x00, 0x01]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 64 [.mem (mrip 1593140 64), .imm 64 1] 8) := by dec_rfl
theorem w_156 : pad <+: nef.drop 156 := by decide +kernel
theorem ad_156 (feat : Features) : Dec feat nef 156 (FV7z.mk .add 64 [.mem (mrip 1593140 64), .imm 64 1] 8) :=
  Dec.shift (j := 156) (k := 0) (pad_0 feat) w_156 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_170 : pret <+: nef.drop 170 := by decide +kernel
theorem ret_170 (feat : Features) : Dec feat nef 170 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 170) (k := 0) (pret_0 feat) w_170 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- What the bytes `V'` after the pushes have of the bytes `V` at the entry, the stack pointer `sp`, `rbp` and `rbx`
there: all outside the frame, in the frame the two registers. -/
structure F0 (V V' : Addr → Byte) (sp : Addr) (rbp rbx : BitVec 64) : Prop where
  out : Out (sp.toNat - 24) sp.toNat V V'
  sbp : rdq(V', sp - 8) = rbp
  sbx : rdq(V', sp - 16) = rbx

/-- From the entry to the walk of the list `l`: no exit function ran, the frame, `rsi` the list. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {l : BitVec 64} (hsp : 24 < g.rsp.toNat)
    (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24#64) i))
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hflag : rdb(V, 8010388#64) = 0)
    (hp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (hpd : g.rdi.toNat + 8 ≤ g.rsp.toNat - 24)
    (hl : rdq(V, g.rdi) = l) (hl0 : l ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧
      g' = { g with rbx := g.rdi, rbp := l, rsi := l, rdi := 0, rsp := g.rsp - 24#64 } ∧
      F0 V V' g.rsp g.rbp g.rbx) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst hp hpd hl
  wpx [W_0, W_17, W_38, o0, o1, o2, Op.cmpmia]
  have e : rdq(Vst (Vst V (rsp - 8) (toBytesLE rbp 8)) (rsp - 8 - 8) (toBytesLE rbx 8), rdi) = l := by
    repeat pv
    exact hl
  rw [e]
  refine ⟨hfl, fun h => ?_, fun _ => ⟨off_ft hst 16 (by bv_omega) (by decide), off_ft hst 8 (by bv_omega) (by decide),
    hp, fun h => ?_, fun _ => ⟨?_, fun a ha => ?_, ?_, ?_⟩⟩⟩
  · rw [hflag] at h
    exact absurd h (by decide)
  · simp only [BitVec.and_self, beq_iff_eq] at h
    exact absurd h hl0
  · rw [show rsp - 8 - 8 - 8#64 = rsp - 24#64 from by bv_omega, BitVec.xor_self]
    rfl
  · repeat pv
  · pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [show rsp - 16 = rsp - 8 - 8 from by bv_omega, vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The list's count of places taken. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hi : ∀ i < 8, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 86 ∧ g' = { g with rax := rdq(V, g.rsi + 8#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_48, o3]
  exact hi

/-- No place taken and no list after this one: to the list's first place. -/
theorem vc_86 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) (hn : rdq(V, g.rsi) = 0)
    (hs : g.rsi.toNat + 16 ≤ 2 ^ 64) (hr : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rsi + 8#64) i)) :
    W_86 F Wl (fun j' g' _ V' => j' = 208 ∧ g' = { g with rdi := g.rsi } ∧
      Out (g.rsi.toNat + 8) (g.rsi.toNat + 16) V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0 hn hs hr hw
  subst h0
  wpx [W_86, W_91, W_110, o6, o7, o8, hn]
  intro af
  refine ⟨fun h => absurd h (by decide), fun _ => ⟨hr, hw, fun _ a ha => ?_, fun h => absurd h (by decide)⟩⟩
  pv

/-- The first place: the list's count 1. -/
theorem vc_208 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rsi.toNat + 16 ≤ 2 ^ 64)
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rsi + 8#64) i)) :
    W_208 F Wl (fun j' g' _ V' => j' = 146 ∧ g' = { g with r8 := g.rsi + 16#64 } ∧
      Out (g.rsi.toNat + 8) (g.rsi.toNat + 16) V V' ∧ rdq(V', g.rsi + 8#64) = 1) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hw
  wpx [W_208, o14]
  refine ⟨hw, fun a ha => ?_, ?_⟩
  · pv
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The place marked taken, its address the answer. -/
theorem vc_146 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.r8.toNat + 8 ≤ 2 ^ 64)
    (hw : ∀ i < 8, Foot Wl (Addr.add g.r8 i)) :
    W_146 F Wl (fun j' g' _ V' => j' = 156 ∧ g' = { g with rax := g.r8 } ∧
      Out g.r8.toNat (g.r8.toNat + 8) V V' ∧ rdq(V', g.r8) = 1) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hw
  wpx [W_146, o11]
  refine ⟨hw, fun a ha => ?_, ?_⟩
  · pv
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The frame given back, to the `ret`. -/
theorem vc_164 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 16, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_164 F Wl (fun j' g' _ V' => j' = 170 ∧
      g' = { g with rsp := g.rsp + 24#64, rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 16#64) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl
  wpx [W_164, o12]
  refine ⟨off_ft hl 0 (by bv_omega) (by decide), off_ft hl 8 (by bv_omega) (by decide), ?_⟩
  rw [show rsp + 8#64 + 8 + 8 = rsp + 24#64 from by bv_omega, show rsp + 8#64 + 8 = rsp + 16#64 from by bv_omega]

/-- Bytes apart from the three ranges where `V'` is not `V`. -/
theorem rd_out3 {V V' : Addr → Byte} {a1 b1 a2 b2 a3 b3 : Nat}
    (h : ∀ a : Addr, ¬ (a1 ≤ a.toNat ∧ a.toNat < b1) → ¬ (a2 ≤ a.toNat ∧ a.toNat < b2) →
      ¬ (a3 ≤ a.toNat ∧ a.toNat < b3) → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (h1 : x.toNat + n ≤ a1 ∨ b1 ≤ x.toNat)
    (h2 : x.toNat + n ≤ a2 ∨ b2 ≤ x.toNat) (h3 : x.toNat + n ≤ a3 ∨ b3 ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ ?_ <;> (rw [toNat_add_of_fits hj hx]; omega)

/-- What the bytes `V'` at the return have of the bytes `V` at the entry, the stack pointer `sp` there, the list
`l`: all outside the frame, the list's count with its first place's mark and the counter; the count 1, the mark 1,
the counter one more. -/
structure Nx (V V' : Addr → Byte) (sp l : Addr) : Prop where
  out : ∀ a : Addr, ¬ (sp.toNat - 24 ≤ a.toNat ∧ a.toNat < sp.toNat) →
    ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 24) → ¬ (8029192 ≤ a.toNat ∧ a.toNat < 8029200) → V' a = V a
  idx : rdq(V', l + 8#64) = 1
  flv : rdq(V', l + 16#64) = 1
  cnt : rdq(V', 8029192#64) = rdq(V, 8029192#64) + 1

/-- The registers `r12` to `r15` of `g'` are those of `g`. -/
def Kp (g g' : Gprs) : Prop := g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- Addresses in the frame of 24 bytes under `sp`. -/
theorem sp_a (sp : Addr) (h : 24 ≤ sp.toNat) : sp - 24#64 + 24#64 = sp ∧ sp - 24#64 + 8#64 = sp - 16 ∧
    sp - 24#64 + 16#64 = sp - 8 ∧ (sp - 16).toNat = sp.toNat - 16 ∧ (sp - 8).toNat = sp.toNat - 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Addresses in the list at `l`. -/
theorem l_a (l : Addr) (h : l.toNat + 24 ≤ 2 ^ 64) :
    (l + 8#64).toNat = l.toNat + 8 ∧ (l + 16#64).toNat = l.toNat + 16 := by
  refine ⟨?_, ?_⟩ <;> bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__new_exitfn (listp)` with no exit function run, the list `l` at `listp` with no place taken and no list after
it: the run reaches the return address with `rax = l + 16`, the list's count 1, its first place marked. -/
theorem nef_first {l : BitVec 64} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nef_at nef)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nef_at)
    (hst : ∀ i < 24, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24#64) i))
    (hlr : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hflag : rdb(V, 8010388#64) = 0)
    (hp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hpd : X.cpu.gpr.rdi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 24)
    (hl : rdq(V, X.cpu.gpr.rdi) = l) (hl0 : l ≠ 0)
    (hlw : ∀ i < 24, Foot Wl (Addr.add l i)) (hld : l.toNat + 24 ≤ X.cpu.gpr.rsp.toNat - 24)
    (hcw : ∀ i < 8, Foot Wl (Addr.add 8029192#64 i)) (hcd : 8029200 ≤ X.cpu.gpr.rsp.toNat - 24)
    (hlc : l.toNat + 24 ≤ 8029192 ∨ 8029200 ≤ l.toNat)
    (hidx : rdq(V, l + 8#64) = 0) (hnext : rdq(V, l) = 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Nx V V' X.cpu.gpr.rsp l →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = l + 16#64 → Osv.Back X.cpu.gpr g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlf : ∀ i < 24, Foot F.data (Addr.add l i) := fun i hi => c.hws _ (hlw i hi)
  obtain ⟨e8, e16⟩ := l_a l (by omega)
  obtain ⟨s24, s8, s16, t16, t8⟩ := sp_a X.cpu.gpr.rsp (by omega)
  have ec : (8029192#64).toNat = 8029192 := rfl
  -- the frame
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (l := l) (by omega) hst hfl hflag hp hpd hl hl0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsi₁ : Y₁.cpu.gpr.rsi = l := by rw [hg₁]
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₁]
  have hk₁ : Kp X.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl⟩
  -- the count of places taken: none
  refine (c_48 prof).run c hin _ hK₁ hA₁ hr₁ (vc_48 (by rw [hsi₁]; exact off_ft hlf 8 rfl (by decide))) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hsi₂ : Y₂.cpu.gpr.rsi = l := by rw [hg₂]; exact hsi₁
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₂]; exact hsp₁
  have hk₂ : Kp X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact hk₁
  have hax₂ : Y₂.cpu.gpr.rax = 0 := by
    rw [hg₂]
    show rdq(V₂, Y₁.cpu.gpr.rsi + 8#64) = 0
    rw [hsi₁, ← hidx]
    exact congrArg (ofBytesLE 64) (hF.out.rd (by omega) (by omega))
  have hnx : rdq(V₂, Y₂.cpu.gpr.rsi) = 0 := by
    rw [hsi₂, ← hnext]
    exact congrArg (ofBytesLE 64) (hF.out.rd (by omega) (by omega))
  refine (c_86 prof).run c hin _ hK₂ hA₂ hr₂ (vc_86 hax₂ hnx (by rw [hsi₂]; omega)
    (by rw [hsi₂]; exact fun i hi => hlf i (by omega)) (by rw [hsi₂]; exact off_ft hlw 8 rfl (by decide))) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, o3⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hsi₃ : Y₃.cpu.gpr.rsi = l := by rw [hg₃]; exact hsi₂
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₃]; exact hsp₂
  have hk₃ : Kp X.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact hk₂
  rw [hsi₂] at o3
  -- the first place
  refine (c_208 prof).run c hin _ hK₃ hA₃ hr₃
    (vc_208 (by rw [hsi₃]; omega) (by rw [hsi₃]; exact off_ft hlw 8 rfl (by decide))) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, o4, hi4⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hsi₃] at o4 hi4
  have h8₄ : Y₄.cpu.gpr.r8 = l + 16#64 := by
    rw [hg₄]
    show Y₃.cpu.gpr.rsi + 16#64 = _
    rw [hsi₃]
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₄]; exact hsp₃
  have hk₄ : Kp X.cpu.gpr Y₄.cpu.gpr := by rw [hg₄]; exact hk₃
  refine (c_146 prof).run c hin _ hK₄ hA₄ hr₄
    (vc_146 (by rw [h8₄]; omega) (by rw [h8₄]; exact off_ft hlw 16 rfl (by decide))) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, o5, hf5⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  rw [h8₄] at o5 hf5
  rw [e16] at o5
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₅]; exact hsp₄
  have hk₅ : Kp X.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact hk₄
  have hax₅ : Y₅.cpu.gpr.rax = l + 16#64 := by rw [hg₅]; exact h8₄
  -- the counter
  refine c.s_add_rip64 hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ad_156 _) (g := 8029192#64) (by decide) hcw ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  obtain ⟨V₆, o6, hc6, hA₆⟩ : ∃ V₆, Out 8029192 8029200 V₅ V₆ ∧
      rdq(V₆, 8029192#64) = rdq(V₅, 8029192#64) + 1 ∧ Agree F Y₆.proc.mm.mem V₆ :=
    ⟨_, (Out.vst (toBytesLE_length _ _) (by decide)).mono (by decide) (by decide),
      by rw [vs (by ln) (by decide)]; exact ofBytesLE_toBytesLE (n := 8) rfl _, hA₆⟩
  have hb : ∀ a : Addr, ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 24) →
      ¬ (8029192 ≤ a.toNat ∧ a.toNat < 8029200) → V₆ a = V₂ a := fun a h2 h3 =>
    (o6 a h3).trans ((o5 a (by omega)).trans ((o4 a (by omega)).trans (o3 a (by omega))))
  have hout : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 24 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 24) → ¬ (8029192 ≤ a.toNat ∧ a.toNat < 8029200) →
      V₆ a = V a := fun a h1 h2 h3 => (hb a h2 h3).trans (hF.out a h1)
  have hsp₆ : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₆]; exact hsp₅
  -- to the `ret`
  refine (c_164 prof).run c hin _ hK₆ hA₆ hr₆ (vc_164 fun i hi => ?_) ?_
  · rw [hsp₆]
    exact c.hws _ (off_ft hst 8 rfl (by decide) i hi)
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have hsp₇ : Y₇.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₇]
    show Y₆.cpu.gpr.rsp + 24#64 = _
    rw [hsp₆]
    exact s24
  refine c.s_ret hK₇ hA₇ hin (lt_len (by decide)) hr₇ (ret_170 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₇]
    exact hlr i hi
  · rw [hsp₇, ← hra]
    exact congrArg (ofBytesLE 64) (rd_out3 hout hs8 (by omega) (by omega) (by omega))
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have hbx : Y₇.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₇]
    show rdq(V₇, Y₆.cpu.gpr.rsp + 8#64) = _
    rw [hsp₆, s8, ← hF.sbx]
    exact congrArg (ofBytesLE 64) (rd_out2 hb (by omega) (by omega) (by omega))
  have hbp : Y₇.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hg₇]
    show rdq(V₇, Y₆.cpu.gpr.rsp + 16#64) = _
    rw [hsp₆, s16, ← hF.sbp]
    exact congrArg (ofBytesLE 64) (rd_out2 hb (by omega) (by omega) (by omega))
  have keep : Kp X.cpu.gpr Y₇.cpu.gpr := by rw [hg₇, hg₆]; exact hk₅
  have hax : Y₇.cpu.gpr.rax = l + 16#64 := by rw [hg₇, hg₆]; exact hax₅
  refine k V₇ _ Z t' hKZ hAZ ⟨hout, ?_, ?_, ?_⟩ hrZ hgZ hax
    ⟨?_, hbx, hbp, keep.1, keep.2.1, keep.2.2.1, keep.2.2.2⟩
  · rw [← hi4]
    exact congrArg (ofBytesLE 64) ((o6.rd (by omega) (by omega)).trans (o5.rd (by omega) (by omega)))
  · rw [← hf5]
    exact congrArg (ofBytesLE 64) (o6.rd (by omega) (by omega))
  · rw [hc6]
    congr 1
    exact congrArg (ofBytesLE 64) ((o5.rd (by omega) (by omega)).trans ((o4.rd (by omega) (by omega)).trans
      ((o3.rd (by omega) (by omega)).trans (hF.out.rd (by omega) (by omega)))))
  · show Y₇.cpu.gpr.rsp + 8 = _
    rw [hsp₇]
    rfl

end FV7z.Nef
