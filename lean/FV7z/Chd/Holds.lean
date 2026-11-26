import FV7z.Chd.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `CCtrlHandlerSetter::~CCtrlHandlerSetter` (PLAN.md §M, M1)

7-Zip 26.06's `NConsoleClose::CCtrlHandlerSetter::~CCtrlHandlerSetter ()` at `0x5e77a0` in `7zzs`
(`CPP/7zip/UI/Console/ConsoleClose.cpp`; `objdump -d`), `this` = `rdi`: `push rbx`, `signal (SIGINT, memo_sig_int)`
(`rsi` the 8 bytes at `this`, the `call` at 16 of glibc's `signal` at `0x6225b0`), then `signal (SIGTERM,
memo_sig_term)` (`rsi` the 8 bytes at `this + 8`), `pop rbx` and a tail jump to `signal` (31).

`signal` is a hypothesis, as in `FV7z/Irp/Holds.lean`: a continuation at its entry (`kf`), given the run from its return
(`chd_at + 21`, `rsp` 8 below the entry's, `rbx` = `this` as the ABI keeps it), and a continuation at the tail jump
(`kj`).

- `gC V g`: the registers at the `call`; `gJ V' g gz`: at the tail jump, `gz` those at the return, `V'` the bytes.
- `vc_0`, `vc_21`: the two pieces.
- `chd_ok`: from the entry through the first `signal` to the second.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Chd

/-- The `call`. -/
def pcl : List Byte := [0xe8, 0xfb, 0xad, 0x03, 0x00]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 241147] 5) := by dec_rfl
theorem wc_16 : pcl <+: chd.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat chd 16 (FV7z.mk .call 64 [.rel 241147] 5) :=
  Dec.shift (j := 16) (k := 0) (pcl_0 feat) wc_16 (Nat.zero_le _)

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xec, 0xad, 0x03, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 241132] 5) := by dec_rfl
theorem wj_31 : pjm <+: chd.drop 31 := by decide +kernel
theorem jmp_31 (feat : Features) : Dec feat chd 31 (FV7z.mk .jmp 64 [.rel 241132] 5) :=
  Dec.shift (j := 31) (k := 0) (pjm_0 feat) wj_31 (Nat.zero_le _)

/-- glibc's `signal` (not proved here). -/
abbrev tgt_at : Addr := 0x6225b0
theorem tgt16 : chd_at.add (16 + 5) + BitVec.ofNat 64 241147 = tgt_at := by decide
theorem tgt31 : chd_at.add (31 + 5) + BitVec.ofNat 64 241132 = tgt_at.add 0 := by decide

/-- The registers at the `call`: `rbx` pushed, `rsi` the 8 bytes at `this` (read after the push), `rbx` = `this`,
`edi` = `SIGINT`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rsp := g.rsp - 8, rsi := rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi), rbx := g.rdi, rdi := 2#64 }

/-- The registers at the tail jump, `gz` those at the return of the first `signal`: `rsi` the 8 bytes at `this + 8`,
`edi` = `SIGTERM`, `rbx` popped. -/
abbrev gJ (V' : Addr → Byte) (g gz : Gprs) : Gprs :=
  { gz with rsi := rdq(V', g.rdi + 8#64), rdi := 15#64, rbx := rdq(V', g.rsp - 8), rsp := g.rsp }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rsi, [rdi]; mov rbx, rdi; mov edi, 2`, to the `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 16 ∧ g' = gC V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw fa ⊢
  wpx [W_0, o0, gC]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (congr 1 <;> first | rfl | decide)
    | apply And.intro
    | intro _

/-- Back from `signal`: `mov rsi, [rbx + 8]; mov edi, 15; pop rbx`, to the tail jump. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fb : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    wp F Wl o1 (fun g' _ V' => g' = { g with rsi := rdq(V, g.rbx + 8#64), rdi := 15#64, rbx := rdq(V, g.rsp),
      rsp := g.rsp + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb fp ⊢
  wpx [o1]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (congr 1 <;> first | rfl | decide)
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `~CCtrlHandlerSetter ()` from its entry: at `signal`'s entry the registers `gC` with `rsp` 16 below the entry's and
the bytes `V` with `rbx` and the return address pushed (`kf`); if `signal` returns to `chd_at + 21` with `rsp` as at its
entry and `rbx` = `this`, the run reaches the tail jump to `signal` with the registers `gJ` (`kj`). -/
theorem chd_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L chd_at chd) {cS : List Byte}
    (hinS : CodeIn L tgt_at cS) (hS : 0 < cS.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = chd_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (chd_at.add 21) 8)) →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = chd_at.add 21 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kj : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = gJ V' X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ g' = gC V X.cpu.gpr ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 fa) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_16 _) hinS hS tgt16 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `signal`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb
  have eJ : { Z.cpu.gpr with rsi := rdq(V', Z.cpu.gpr.rbx + 8#64), rdi := 15#64, rbx := rdq(V', Z.cpu.gpr.rsp),
      rsp := Z.cpu.gpr.rsp + 8 } = gJ V' X.cpu.gpr Z.cpu.gpr := by
    rw [hzb, hzs, e8]
  refine (c_21 prof).run c hin (fun j' g' _ V'' => j' = 31 ∧ g' = gJ V' X.cpu.gpr Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
    (wp_mono o1 (fun _ _ _ h => ⟨rfl, h.1.trans eJ, h.2⟩)
      (vc_21 (by rw [hzb]; exact fb) (by rw [hzs]; exact hl1))) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_31 _) hinS hS tgt31 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact kj Z V' Y₃ t₄ hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (hg₃.trans hgU)

end FV7z.Chd
