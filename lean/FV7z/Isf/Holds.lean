import FV7z.Isf.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `__init_sched_fifo_prio ()` (PLAN.md §M, M1)

glibc 2.31's `__init_sched_fifo_prio ()` at `0x5ff620` in `7zzs` (`nptl/tpp.c`; `objdump -d`), `S` the entry's
`rsp`: `sub rsp, 8; mov edi, 1` (`SCHED_FIFO`), `call sched_get_priority_max` (at 13, `0x6650b0`); back at 18
`mov edi, 1; mov [__sched_fifo_max_prio], eax` (`0x792270`), `call sched_get_priority_min` (at 29, `0x6650e0`);
back at 34 `mov [__sched_fifo_min_prio], eax` (`0x792274`), `add rsp, 8`, the `ret` (44).

The callees are hypotheses, as in `FV7z/Lzp/Holds.lean`: each a continuation at its entry (`kf1`, `kf2`), given the
run from its return, `rsp` 8 below the entry's and the return address left as it was; `Pc1`, `Pc2` are what they
leave. The second store is to a fixed address apart from the return address (`hd`).

- `gC`: the registers at the first `call`.
- `vc_0`, `vc_18`, `vc_34`: the pieces from the entry, from 18 and from 34.
- `isf_ok`: through both callees and both stores, at the return address (`kr`), `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Isf

/-- `sched_get_priority_max`. -/
abbrev pmax_at : Addr := 0x6650b0

/-- `sched_get_priority_min`. -/
abbrev pmin_at : Addr := 0x6650e0

/-- The first `call`. -/
def pc1 : List Byte := [0xe8, 0x7e, 0x5a, 0x06, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 416382] 5) := by dec_rfl
theorem wc_13 : pc1 <+: isf.drop 13 := by decide +kernel
theorem call_13 (feat : Features) : Dec feat isf 13 (FV7z.mk .call 64 [.rel 416382] 5) :=
  Dec.shift (j := 13) (k := 0) (pc1_0 feat) wc_13 (Nat.zero_le _)
theorem tgt_13 : isf_at.add (13 + 5) + BitVec.ofNat 64 416382 = pmax_at := by decide

/-- The second `call`. -/
def pc2 : List Byte := [0xe8, 0x9e, 0x5a, 0x06, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 416414] 5) := by dec_rfl
theorem wc_29 : pc2 <+: isf.drop 29 := by decide +kernel
theorem call_29 (feat : Features) : Dec feat isf 29 (FV7z.mk .call 64 [.rel 416414] 5) :=
  Dec.shift (j := 29) (k := 0) (pc2_0 feat) wc_29 (Nat.zero_le _)
theorem tgt_29 : isf_at.add (29 + 5) + BitVec.ofNat 64 416414 = pmin_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_44 : pret <+: isf.drop 44 := by decide +kernel
theorem ret_44 (feat : Features) : Dec feat isf 44 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 44) (k := 0) (pret_0 feat) w_44 (Nat.zero_le _)

/-! ## The frame -/

/-- The registers at the first `call`: `rsp` 8 lower, `edi` = 1. -/
abbrev gC (g : Gprs) : Gprs := { g with rsp := g.rsp - 8#64, rdi := 1#64 }

theorem q16 (s : BitVec 64) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem sa8 (s : BitVec 64) : s - 8#64 + 8#64 = s := BitVec.sub_add_cancel _ _
theorem gT : (7938676#64 : Addr).toNat = 7938676 := by decide

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8; mov edi, 1`, to the first `call` at 13. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl rd, rd = 1#64 → Q 13 { g with rsp := g.rsp - 8#64, rdi := rd } fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ _ (by decide) | apply And.intro | intro _)

/-- `mov edi, 1; mov [0x792270], eax`, to the second `call` at 29. -/
theorem vc_18 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 4, Foot Wl (Addr.add 7938672#64 i))
    (h : ∀ fl rd, rd = 1#64 → Q 29 { g with rdi := rd } fl
      (Vst V 7938672#64 (toBytesLE (g.rax.setWidth 32) 4))) :
    W_18 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_18, o1, Op.sta]
  all_goals repeat' (first | exact h _ _ (by decide) | exact hw | exact trivial | apply And.intro | intro _)

/-- `mov [0x792274], eax; add rsp, 8`, to the `ret` at 44. -/
theorem vc_34 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 4, Foot Wl (Addr.add 7938676#64 i))
    (h : ∀ fl, Q 44 { g with rsp := g.rsp + 8#64 } fl (Vst V 7938676#64 (toBytesLE (g.rax.setWidth 32) 4))) :
    W_34 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_34, o2, Op.sta]
  all_goals repeat' (first | exact h _ | exact hw | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__init_sched_fifo_prio ()` from its entry, the two callees as hypotheses (`kf1`, `kf2`, each with the return
into `__init_sched_fifo_prio` pushed at `S - 16`). The run reaches the return address with the first's `eax` stored
at `0x792270` (before the second `call`) and the second's at `0x792274` (`kr`); `rsp` = `S + 8`. -/
theorem isf_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L isf_at isf)
    {code1 : List Byte} (hin1 : CodeIn L pmax_at code1) (h1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L pmin_at code2) (h2 : 0 < code2.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isf_at)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rsp.toNat + 8 ≤ 7938676 ∨ 7938680 ≤ X.cpu.gpr.rsp.toNat)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw1 : ∀ i < 4, Foot Wl (Addr.add 7938672#64 i))
    (hw2 : ∀ i < 4, Foot Wl (Addr.add 7938676#64 i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (isf_at.add 18) 8)) →
      Y.cpu.rip = pmax_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = isf_at.add 18 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 → Pc1 Z V' →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V' 7938672#64 (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4))
        (X.cpu.gpr.rsp - 16) (toBytesLE (isf_at.add 34) 8)) →
      Y.cpu.rip = pmin_at → Y.cpu.gpr = ({ Z.cpu.gpr with rdi := 1#64 }).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = isf_at.add 34 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ 7938676#64 (toBytesLE (Z₂.cpu.gpr.rax.setWidth 32) 4)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = { Z₂.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have mG : ∀ (W : Addr → Byte) (v : BitVec 32),
      (byteAddrs X.cpu.gpr.rsp 8).map (Vst W 7938676#64 (toBytesLE v 4)) = (byteAddrs X.cpu.gpr.rsp 8).map W :=
    fun W v => Tun.rd_Vst W 7938676#64 (toBytesLE v 4) X.cpu.gpr.rsp 8 (by rw [toBytesLE_length, gT]; omega) hp8
      (by rw [toBytesLE_length, gT]; omega)
  have hrip' : X.cpu.rip = isf_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 13 ∧ g' = gC X.cpu.gpr ∧ V' = V) hK hA hrip'
    (vc_0 fun _ rd hrd => ⟨rfl, by rw [hrd], rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by rw [hgY]; exact q16 _
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_13 _) hin1 h1 tgt_13 (by rw [hsY]; exact hs2) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from the first callee, at 18: to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs _ hP1
  refine (c_18 prof).run c hin (fun j' g' _ V'' => j' = 29 ∧ g' = { Z.cpu.gpr with rdi := 1#64 } ∧
      V'' = Vst V' 7938672#64 (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4)) hKZ hAZ hrZ
    (vc_18 hw1 fun _ rd hrd => ⟨rfl, by rw [hrd], rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 16 := by
    rw [hgU]
    show Z.cpu.gpr.rsp - 8 = _
    rw [hzs]
    exact q16 _
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_29 _) hin2 h2 tgt_29 (by rw [hsU]; exact hs2) ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsU] at hA₄
  refine kf2 Z V' hzs hP1 U₂ t₄ hK₄ hA₄ hr₄ (by rw [hg₄, hsU, hgU]) ?_
  -- back from the second callee, at 34: the store, the `ret` at 44
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s qr hP2
  refine (c_34 prof).run c hin (fun j' g' _ V₃ => j' = 44 ∧ g' = { Z₂.cpu.gpr with rsp := X.cpu.gpr.rsp } ∧
      V₃ = Vst V₂ 7938676#64 (toBytesLE (Z₂.cpu.gpr.rax.setWidth 32) 4)) hKZ₂ hAZ₂ hrZ₂
    (vc_34 hw2 fun _ => ⟨rfl, by rw [hz2s, sa8], rfl⟩) ?_
  rintro j' g fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst V₃
  have hsU₃ : U₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₃]
  refine c.s_ret hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (ret_44 _) (by rw [hsU₃]; exact hl) hin₂ h₂
    (by rw [hsU₃, mG]; exact qr) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V₂ Z' t₇ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₃]
  try rfl

end FV7z.Isf
