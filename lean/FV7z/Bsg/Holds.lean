import FV7z.Bsg.Cuts
import FV7z.Raf.Holds
import FV7z.Sgw.Holds
import FV7z.Lemmas.Rmw
import FV7z.Lemmas.Lock2
/-!
# `__bsd_signal.part.0` (PLAN.md §M, M1)

glibc 2.31's `__bsd_signal (sig, handler)` at `0x622510` in `7zzs` (`signal/signal.c`), the part after the check
of `sig`: a frame of 328 bytes `[S - 328, S)` below the entry's stack pointer `S`, the stack guard (`fs:0x28`) at
`S - 16`, a `struct sigaction` at `S - 328`: the handler (`[S - 328]`), the mask zeroed (`rep stos qword`, 57) and
`sig`'s bit set in it (`or`, 75), the flags (`SA_RESTART` unless `sig` is in `_sigintr`, the `test` at 80); then
`__sigaction (sig, &act, &oact)` (the `call` at 103 to `Sgw.sgw_at`), the old handler or -1 in `rax`, the guard
checked, the `ret` (152).

The callee is a hypothesis (`kf`): a continuation at its entry, given the run from its return.

- `Kc`: the registers a call keeps.
- `fill_out`: `Vfill` differs only in the bytes it fills.
- `Fm`: the bytes outside the frame and its 8 bytes below as at the entry, the handler and the guard in the frame;
  `Fm.out`: a change inside the frame apart from those two keeps it.
- `vc_0`, `vc_60`, `vc_80`, `vc_108`: the verification conditions of the pieces (`Bsg/Cuts.lean`).
- `bsg_ok`: from the entry to the return address, with `rsp` 8 above the entry's, `Kc`, and the bytes the callee
  left.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs rd_out)
namespace FV7z.Bsg
set_option maxRecDepth 100000

/-! ## The instructions the pieces stop at -/

/-- `rep stos qword [rdi], rax`. -/
def pstos : List Byte := [0xf3, 0x48, 0xab]
theorem pstos_0 : ∀ feat, Dec feat pstos 0 (repStosq 3) := by dec_rfl
theorem w_57 : pstos <+: bsg.drop 57 := by decide +kernel
theorem stos_57 (feat : Features) : Dec feat bsg 57 (repStosq 3) :=
  Dec.shift (j := 57) (k := 0) (pstos_0 feat) w_57 (Nat.zero_le _)

/-- `or qword [rsp + 8], rax`. -/
def por : List Byte := [0x48, 0x09, 0x44, 0x24, 0x08]
theorem por_0 : ∀ feat, Dec feat por 0 (FV7z.mk .or 64 [.mem (mbd 4 8 64), gr 64 0] 5) := by dec_rfl
theorem w_75 : por <+: bsg.drop 75 := by decide +kernel
theorem or_75 (feat : Features) : Dec feat bsg 75 (FV7z.mk .or 64 [.mem (mbd 4 8 64), gr 64 0] 5) :=
  Dec.shift (j := 75) (k := 0) (por_0 feat) w_75 (Nat.zero_le _)

/-- The `call` to `__sigaction`. -/
def pcall : List Byte := [0xe8, 0x54, 0xec, 0xfd, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709415508] 5) := by dec_rfl
theorem wc_103 : pcall <+: bsg.drop 103 := by decide +kernel
theorem call_103 (feat : Features) : Dec feat bsg 103 (FV7z.mk .call 64 [.rel 18446744073709415508] 5) :=
  Dec.shift (j := 103) (k := 0) (pcall_0 feat) wc_103 (Nat.zero_le _)
theorem tgt_103 : bsg_at.add (103 + 5) + BitVec.ofNat 64 18446744073709415508 = Sgw.sgw_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_152 : pret <+: bsg.drop 152 := by decide +kernel
theorem ret_152 (feat : Features) : Dec feat bsg 152 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 152) (k := 0) (pret_0 feat) w_152 (Nat.zero_le _)

/-! ## Registers and bytes -/

/-- The registers a call keeps, from `g` to `g'`. -/
def Kc (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Kc.trans {g g' g'' : Gprs} (h : Kc g g') (h' : Kc g' g'') : Kc g g'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- `Vfill` differs only in the `8 n` bytes from `a`. -/
theorem fill_out (v : BitVec 64) : ∀ (n : Nat) (V : Addr → Byte) (a : Addr), a.toNat + 8 * n < 2 ^ 64 →
    Raf.Out a.toNat (a.toNat + 8 * n) V (Vfill V a v n)
  | 0, _, _, _ => fun _ _ => rfl
  | n + 1, V, a, h => by
    have e : (a + 8).toNat = a.toNat + 8 := by bv_omega
    have ih := fill_out v n (Vst V a (toBytesLE v 8)) (a + 8) (by rw [e]; omega)
    rw [e] at ih
    rw [Vfill_succ]
    exact ((Raf.Out.vst (toBytesLE_length _ _) (by omega)).mono (Nat.le_refl _) (by omega)).trans
      (ih.mono (by omega) (by omega))

/-- A read of 8 bytes apart from where `V'` is not `V`. -/
theorem rq {lo hi : Nat} {V V' : Addr → Byte} (h : Raf.Out lo hi V V') {x : Addr} (hx : x.toNat + 8 ≤ 2 ^ 64)
    (hd : x.toNat + 8 ≤ lo ∨ hi ≤ x.toNat) : rdq(V', x) = rdq(V, x) :=
  congrArg (ofBytesLE 64) (h.rd hx hd)

/-- `W` is `V` outside `[S - 336, S)`, with the handler `h` at `S - 328` and the guard `c` at `S - 16`. -/
def Fm (S : Addr) (h c : BitVec 64) (V W : Addr → Byte) : Prop :=
  Raf.Out (S.toNat - 336) S.toNat V W ∧ rdq(W, S - 328#64) = h ∧ rdq(W, S - 16#64) = c

/-- A change inside `[S - 336, S)` apart from the handler and the guard keeps `Fm`. -/
theorem Fm.out {S : Addr} {h c : BitVec 64} {V W W' : Addr → Byte} {lo hi : Nat} (hF : Fm S h c V W)
    (hO : Raf.Out lo hi W W') (hS : 336 ≤ S.toNat) (h1 : S.toNat - 336 ≤ lo) (h2 : hi ≤ S.toNat)
    (h3 : hi ≤ S.toNat - 328 ∨ S.toNat - 320 ≤ lo) (h4 : hi ≤ S.toNat - 16 ∨ S.toNat - 8 ≤ lo) :
    Fm S h c V W' := by
  obtain ⟨hO₀, hh, hc⟩ := hF
  have e1 : (S - 328#64).toNat = S.toNat - 328 := by bv_omega
  have e2 : (S - 16#64).toNat = S.toNat - 16 := by bv_omega
  refine ⟨hO₀.trans (hO.mono h1 h2), ?_, ?_⟩
  · rw [← hh]
    exact rq hO (by omega) (by omega)
  · rw [← hc]
    exact rq hO (by omega) (by omega)

variable {F : Footprint} {Wl : List Rgn}

/-- The registers at the `rep stos`. -/
abbrev g1 (g : Gprs) (r : BitVec 64) : Gprs :=
  { g with rax := 0, rcx := 16, rdx := g.rsp - 328#64 + 160#64, rsp := g.rsp - 328#64, rsi := g.rsp - 328#64,
           rdi := g.rsp - 328#64 + 8#64, r8 := r }

/-! ## The pieces -/

/-- To the `rep stos`: the frame, the guard at `S - 16`, the handler at `S - 328`; `rdi` the mask, `rcx` 16,
`rax` 0, `rsi` the action, `rdx` the old action, `r8d` `sig`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hsp : 336 ≤ g.rsp.toNat)
    (hst : ∀ i < 328, Foot Wl (Addr.add (g.rsp - 328#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 57 ∧ (∃ r, g' = g1 g r ∧
      r.setWidth 32 = g.rdi.setWidth 32) ∧ Sga.Fr V V' g.rsp fb g.rsi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst ⊢
  have e16 : rsp - 328#64 + 312#64 = rsp - 16#64 := by bv_omega
  wpx [W_0, o0, Op.ldf, e16]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | exact hfl
    | exact fun i hi => hst i (by omega)
    | exact fun i hi => e16 ▸ Sga.frm_ft hst (d := 312) (by decide) i hi
    | apply And.intro
    | refine ⟨_, rfl, ?_⟩
    | refine ⟨fun a ha => ?_, ?_, ?_⟩
    | intro _)
  all_goals first
    | (repeat pv); done
    | (rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]); done
    | (pv; rw [vs (by ln) (by bv_omega)]; exact ofBytesLE_toBytesLE (n := 8) rfl _)
    | (repeat pv); rw [vs (by ln) (by bv_omega)]; exact ofBytesLE_toBytesLE (n := 8) rfl _
    | (repeat pv); rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]; done
    | bv_omega
    | skip

/-- After the `rep stos`, to the `or`: `ecx` = `sig - 1`, `rax` = `1 << ecx`, `edi` = `sig`. -/
theorem vc_60 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_60 fb F Wl (fun j' g' _ V' => j' = 75 ∧ (∃ a c d, g' = { g with rax := a, rcx := c, rdi := d } ∧
      d.setWidth 32 = g.r8.setWidth 32) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_60, o1, Op.shl64]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | apply And.intro
    | refine ⟨_, _, _, rfl, ?_⟩
    | intro _
    | bv_omega)

/-- After the `or`, to the `call`: the flags into `[rsp + 136]`. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsi : ∀ i < 8, Foot F.data (Addr.add (8029056#64) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 136#64) i)) (hb : g.rsp.toNat + 140 ≤ 2 ^ 64) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 103 ∧ (∃ a, g' = { g with rax := a }) ∧
      Raf.Out (g.rsp.toNat + 136) (g.rsp.toNat + 136 + 4) V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hb ⊢
  have e : (rsp + 136#64).toNat = rsp.toNat + 136 := by bv_omega
  wpx [W_80, o2, Op.testmra, Op.setcc, Op.zxr]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | exact hsi
    | exact hw
    | exact ⟨_, rfl⟩
    | (rw [← e]; exact Raf.Out.vst (toBytesLE_length _ _) (by omega))
    | apply And.intro
    | intro _)

/-- After the `call`, the guard checked, to the `ret`: `rax` the old handler or -1, the frame popped. -/
theorem vc_108 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h160 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 160#64) i))
    (h312 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 312#64) i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 312#64) = rdq(V, fb + 40#64)) :
    W_108 fb F Wl (fun j' g' _ V' => j' = 152 ∧ g'.rsp = g.rsp + 328#64 ∧ Kc g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h160 h312 hc ⊢
  by_cases hm : (!(BitVec.setWidth 32 rax &&& BitVec.setWidth 32 rax).msb) = true
  all_goals wpx [W_108, W_145, o3, o4, Op.xormf, Op.cmovld64, hc, BitVec.xor_self, Kc, hm, ↓reduceIte,
    beq_self_eq_true, Bool.not_true, Bool.false_eq_true, false_implies]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | exact h160
    | exact h312
    | exact hfl
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _)

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__bsd_signal.part.0 (sig, handler)` from its entry, the stack pointer `S`: the frame and the 8 bytes below it
in what the run may store into, the stack guard and the bytes the `test` reads readable. At the callee's entry
(`kf`) the bytes are `V` outside `[S - 336, S)` with the return address `bsg_at + 108` at `S - 336` and the handler
at `S - 328`; `rdi`'s low half is `sig`, `rsi` the action, `rdx` the old action, `rsp` = `S - 336`, `Kc`. If the
callee returns to `bsg_at + 108` with `rsp` = `S - 328`, `Kc`, the guard's bytes in the frame, the return address
and the guard at `fs:0x28` as they were, and `Pc`, then the run reaches the return address with `rsp` = `S + 8`,
`Kc` from the entry, and the callee's bytes (`k`). -/
theorem bsg_ok {fb : Addr} {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hdf : s₀.cpu.rflags.df = false) (hin : CodeIn L bsg_at bsg)
    (hinS : CodeIn L Sgw.sgw_at Sgw.sgw) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = bsg_at) (hsp : 336 ≤ X.cpu.gpr.rsp.toNat)
    (hst : ∀ i < 336, Foot Wl (Addr.add (X.cpu.gpr.rsp - 336#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hsi : ∀ i < 8, Foot F.data (Addr.add (8029056#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kf : ∀ (Y : State) (V₁ : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V₁ →
      Raf.Out (X.cpu.gpr.rsp.toNat - 336) X.cpu.gpr.rsp.toNat V V₁ →
      rdq(V₁, X.cpu.gpr.rsp - 336#64) = bsg_at.add (103 + 5) → rdq(V₁, X.cpu.gpr.rsp - 328#64) = X.cpu.gpr.rsi →
      Y.cpu.rip = Sgw.sgw_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 336#64 →
      Y.cpu.gpr.rsi = X.cpu.gpr.rsp - 328#64 → Y.cpu.gpr.rdx = X.cpu.gpr.rsp - 328#64 + 160#64 →
      Y.cpu.gpr.rdi.setWidth 32 = X.cpu.gpr.rdi.setWidth 32 → Kc X.cpu.gpr Y.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = bsg_at.add 108 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 → Kc Y.cpu.gpr Z.cpu.gpr →
        rdq(V', X.cpu.gpr.rsp - 16#64) = rdq(V₁, X.cpu.gpr.rsp - 16#64) →
        rdq(V', X.cpu.gpr.rsp) = rdq(V₁, X.cpu.gpr.rsp) → rdq(V', fb + 40#64) = rdq(V, fb + 40#64) → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Kc X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hP : (X.cpu.gpr.rsp - 328#64).toNat = X.cpu.gpr.rsp.toNat - 328 := by bv_omega
  have hP8 : (X.cpu.gpr.rsp - 328#64 + 8#64).toNat = X.cpu.gpr.rsp.toNat - 320 := by bv_omega
  have hQ : (X.cpu.gpr.rsp - 336#64).toNat = X.cpu.gpr.rsp.toNat - 336 := by bv_omega
  have hP' : X.cpu.gpr.rsp - 328#64 - 8 = X.cpu.gpr.rsp - 336#64 := by bv_omega
  have h312 : X.cpu.gpr.rsp - 328#64 + 312#64 = X.cpu.gpr.rsp - 16#64 := by bv_omega
  have h328 : X.cpu.gpr.rsp - 328#64 + 328#64 = X.cpu.gpr.rsp := by bv_omega
  have hst' : ∀ i < 328, Foot Wl (Addr.add (X.cpu.gpr.rsp - 328#64) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 336#64) (8 + i) = Addr.add (X.cpu.gpr.rsp - 328#64) i from by
      simp only [Addr.add]; bv_omega] at this
  -- to the `rep stos`
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hsp hst' hfl) ?_
  rintro j' g fl V₀ ⟨rfl, ⟨r₀, rfl, hr8⟩, hF⟩ Y₀ t₀ hK₀ hA₀ hr₀ hg₀ -
  have hFm₀ : Fm X.cpu.gpr.rsp X.cpu.gpr.rsi (rdq(V, fb + 40#64)) V V₀ :=
    ⟨(show Raf.Out _ _ V V₀ from hF.out).mono (by omega) (Nat.le_refl _), hF.hnd, hF.can⟩
  have hs₀ : Y₀.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₀] <;> rfl
  have hsi₀ : Y₀.cpu.gpr.rsi = X.cpu.gpr.rsp - 328#64 := by rw [hg₀] <;> rfl
  have hdx₀ : Y₀.cpu.gpr.rdx = X.cpu.gpr.rsp - 328#64 + 160#64 := by rw [hg₀] <;> rfl
  have hdi₀ : Y₀.cpu.gpr.rdi = X.cpu.gpr.rsp - 328#64 + 8#64 := by rw [hg₀] <;> rfl
  have hax₀ : Y₀.cpu.gpr.rax = 0 := by rw [hg₀] <;> rfl
  have h8₀ : Y₀.cpu.gpr.r8 = r₀ := by rw [hg₀] <;> rfl
  have hk₀ : Kc X.cpu.gpr Y₀.cpu.gpr := by rw [hg₀]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the mask zeroed
  refine c.s_rep_stosq hdf hin (by rw [bsg_length]; decide) (lt_len (by decide)) (stos_57 _) 15 hK₀ hA₀ hr₀
    (by rw [hg₀] <;> rfl) (fun i hi => by rw [hdi₀]; exact Sga.frm_ft hst' (d := 8) (n := 128) (by decide) i hi) ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hdi₀, hax₀] at hA₁
  obtain ⟨V₁, hA₁', hFm₁⟩ : ∃ W, Agree F Y₁.proc.mm.mem W ∧ Fm X.cpu.gpr.rsp X.cpu.gpr.rsi (rdq(V, fb + 40#64)) V W :=
    ⟨_, hA₁, Fm.out hFm₀ (fill_out _ _ _ _ (by omega)) hsp (by omega) (by omega) (by omega) (by omega)⟩
  have hs₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₁]; exact hs₀
  have hsi₁ : Y₁.cpu.gpr.rsi = X.cpu.gpr.rsp - 328#64 := by rw [hg₁]; exact hsi₀
  have hdx₁ : Y₁.cpu.gpr.rdx = X.cpu.gpr.rsp - 328#64 + 160#64 := by rw [hg₁]; exact hdx₀
  have h8₁ : Y₁.cpu.gpr.r8 = r₀ := by rw [hg₁]; exact h8₀
  have hk₁ : Kc Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- to the `or`
  refine (c_60 prof fb).run c hfs hin _ hK₁ hA₁' hr₁ vc_60 ?_
  rintro j' g fl V₂ ⟨rfl, ⟨a₂, c₂, d₂, rfl, hd₂⟩, hV₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  rw [hV₂] at hA₂
  have hs₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₂]; exact hs₁
  have hsi₂ : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsp - 328#64 := by rw [hg₂]; exact hsi₁
  have hdx₂ : Y₂.cpu.gpr.rdx = X.cpu.gpr.rsp - 328#64 + 160#64 := by rw [hg₂]; exact hdx₁
  have hdi₂ : Y₂.cpu.gpr.rdi.setWidth 32 = X.cpu.gpr.rdi.setWidth 32 := by
    rw [hg₂]
    show d₂.setWidth 32 = _
    rw [hd₂, h8₁]
    exact hr8
  have hk₂ : Kc Y₁.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `sig`'s bit into the mask
  have he₂ : eaD Y₂ 4 8 = X.cpu.gpr.rsp - 328#64 + 8#64 := by
    show Y₂.cpu.gpr.get (regOf 4) + BitVec.ofNat 64 8 = _
    rw [show Y₂.cpu.gpr.get (regOf 4) = Y₂.cpu.gpr.rsp from rfl, hs₂]
  refine c.s_or_mr64 hK₂ hA₂ hin (lt_len (by decide)) hr₂ (or_75 _)
    (by rw [he₂]; exact Sga.frm_ft hst' (d := 8) (n := 8) (by decide)) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [he₂] at hA₃
  obtain ⟨V₃, hA₃', hFm₃⟩ : ∃ W, Agree F Y₃.proc.mm.mem W ∧ Fm X.cpu.gpr.rsp X.cpu.gpr.rsi (rdq(V, fb + 40#64)) V W :=
    ⟨_, hA₃, Fm.out hFm₁ (Raf.Out.vst (toBytesLE_length _ _) (by omega)) hsp (by omega) (by omega) (by omega)
      (by omega)⟩
  have hs₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₃]; exact hs₂
  -- to the `call`
  refine (c_80 prof fb).run c hfs hin _ hK₃ hA₃' hr₃
    (vc_80 hsi (by rw [hs₃]; exact Sga.frm_ft hst' (d := 136) (n := 4) (by decide)) (by rw [hs₃]; omega)) ?_
  rintro j' g fl V₄ ⟨rfl, ⟨a₄, rfl⟩, hO₄⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hs₃, hP] at hO₄
  have hFm₄ : Fm X.cpu.gpr.rsp X.cpu.gpr.rsi (rdq(V, fb + 40#64)) V V₄ :=
    Fm.out hFm₃ hO₄ hsp (by omega) (by omega) (by omega) (by omega)
  have hs₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₄]; exact hs₃
  -- the `call`
  refine c.s_call_x hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_103 _) hinS (tgt := 0) (Sgw.lt_len (by decide))
    tgt_103 (by rw [hs₄, hP']; exact fun i hi => hst i (by omega)) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [hs₄, hP'] at hA₅
  obtain ⟨V₅, hA₅', hFm₅, hret₅⟩ : ∃ W, Agree F Y₅.proc.mm.mem W ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr.rsi (rdq(V, fb + 40#64)) V W ∧
      rdq(W, X.cpu.gpr.rsp - 336#64) = bsg_at.add (103 + 5) :=
    ⟨_, hA₅, Fm.out hFm₄ (Raf.Out.vst (toBytesLE_length _ _) (by omega)) hsp (by omega) (by omega) (by omega)
      (by omega), by rw [vs (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]⟩
  have hk₅ : Kc X.cpu.gpr Y₅.cpu.gpr := by
    refine hk₀.trans (hk₁.trans (hk₂.trans ?_))
    rw [hg₅, hg₄, hg₃]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine kf Y₅ V₅ t₅ hK₅ hA₅' hFm₅.1 hret₅ hFm₅.2.1 (by rw [hr₅, addr_add_zero])
    (by rw [hg₅]; show Y₄.cpu.gpr.rsp - 8 = _; rw [hs₄, hP'])
    (by rw [hg₅, hg₄, hg₃]; exact hsi₂) (by rw [hg₅, hg₄, hg₃]; exact hdx₂)
    (by rw [hg₅, hg₄, hg₃]; exact hdi₂) hk₅ ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hsZ hkZ hcan hret hgd hPc
  have hc : rdq(V', Z.cpu.gpr.rsp + 312#64) = rdq(V', fb + 40#64) := by
    rw [hsZ, h312, hcan, hFm₅.2.2, hgd]
  refine (c_108 prof fb).run c hfs hin _ hKZ hAZ hrZ
    (vc_108 (by rw [hsZ]; exact fun i hi => c.hws _ (Sga.frm_ft hst' (d := 160) (n := 8) (by decide) i hi))
      (by rw [hsZ]; exact fun i hi => c.hws _ (Sga.frm_ft hst' (d := 312) (n := 8) (by decide) i hi)) hfl hc) ?_
  rintro j' g fl V₆ ⟨rfl, hs₆, hk₆, hV₆⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  rw [hV₆] at hA₆
  subst hg₆
  have hsY : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hs₆, hsZ, h328]
  refine c.s_ret hK₆ hA₆ hin (lt_len (by decide)) hr₆ (ret_152 _) (by rw [hsY]; exact hl) hin₂ h₂
    (by rw [hsY, hret, rq hFm₅.1 hsp8 (Or.inr (Nat.le_refl _))]; exact hra) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z V' Z' t₇ hPc hKZ' hAZ' hrZ' (by rw [hgZ']; show Y₆.cpu.gpr.rsp + 8 = _; rw [hsY])
    (hk₅.trans (hkZ.trans (hk₆.trans ?_)))
  rw [hgZ']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.Bsg
