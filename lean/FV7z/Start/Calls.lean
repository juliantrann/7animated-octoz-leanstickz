import FV7z.Start.Cuts
import FV7z.Pie.Cuts
import FV7z.Startup.Callees
/-!
# The calls `__libc_start_main` makes first (PLAN.md G3, startup)

To where `init_cpu_features` begins (211), `__libc_start_main` calls `_dl_relocate_static_pie` (at 71),
`_dl_aux_init` (131), `__libc_init_secure` (194) and `__tunables_init` (206). `tools/blk_gen.py` stops at a `call`
and starts again after it; here the `call`s are decoded, and `spC` is the table of the cut points' pieces in a run
that has the five functions' code: the generated ones (`spAll`), and at each `call` the callee's run to its `ret`
(`SpAt.call` with the callee's `FnAt`), for `Seg.cfgAt`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Startup

/-! ## The `call`s and `_dl_relocate_static_pie`'s `ret` -/

def pc71 : List Byte := [0xe8, 0xf4, 0xa2, 0xe0, 0xff]
def pc131 : List Byte := [0xe8, 0x48, 0xc3, 0x05, 0x00]
def pc194 : List Byte := [0xe8, 0x99, 0xd5, 0x05, 0x00]
def pc206 : List Byte := [0xe8, 0xfd, 0xbc, 0x05, 0x00]
theorem pc71_0 : ∀ feat, Dec feat pc71 0 (FV7z.mk .call 64 [.rel 18446744073707496180] 5) := by dec_rfl
theorem pc131_0 : ∀ feat, Dec feat pc131 0 (FV7z.mk .call 64 [.rel 377672] 5) := by dec_rfl
theorem pc194_0 : ∀ feat, Dec feat pc194 0 (FV7z.mk .call 64 [.rel 382361] 5) := by dec_rfl
theorem pc206_0 : ∀ feat, Dec feat pc206 0 (FV7z.mk .call 64 [.rel 376061] 5) := by dec_rfl
set_option maxRecDepth 100000 in
theorem wc71 : pc71 <+: lsm.drop 71 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc131 : pc131 <+: lsm.drop 131 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc194 : pc194 <+: lsm.drop 194 := by decide +kernel
set_option maxRecDepth 100000 in
theorem wc206 : pc206 <+: lsm.drop 206 := by decide +kernel
theorem call_71 (feat : Features) : Dec feat lsm 71 (FV7z.mk .call 64 [.rel 18446744073707496180] 5) :=
  Dec.shift (j := 71) (k := 0) (pc71_0 feat) wc71 (Nat.zero_le _)
theorem call_131 (feat : Features) : Dec feat lsm 131 (FV7z.mk .call 64 [.rel 377672] 5) :=
  Dec.shift (j := 131) (k := 0) (pc131_0 feat) wc131 (Nat.zero_le _)
theorem call_194 (feat : Features) : Dec feat lsm 194 (FV7z.mk .call 64 [.rel 382361] 5) :=
  Dec.shift (j := 194) (k := 0) (pc194_0 feat) wc194 (Nat.zero_le _)
theorem call_206 (feat : Features) : Dec feat lsm 206 (FV7z.mk .call 64 [.rel 376061] 5) :=
  Dec.shift (j := 206) (k := 0) (pc206_0 feat) wc206 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wpie : pret <+: Pie.pie.drop 4 := by decide +kernel
theorem pie_ret (feat : Features) : Dec feat Pie.pie 4 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 4) (k := 0) (pret_0 feat) wpie (Nat.zero_le _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}

/-! ## `_dl_relocate_static_pie`: nothing changes -/

theorem pie_vc (K : Gprs × (Addr → Byte)) (ℓ : Nat) :
    ∀ (n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte), (ℓ = 0 ∧ g = K.1 ∧ V = K.2) → Pie.Wt ℓ F Wl
      (fun j' g' _ V' => (∃ n', n' < n ∧ (j' = 0 ∧ g' = K.1 ∧ V' = K.2)) ∨ (j' = 4 ∧ (g' = K.1 ∧ V' = K.2))) g f V := by
  obtain ⟨g0, V0⟩ := K
  rintro n g f V ⟨rfl, rfl, rfl⟩
  simp only [Pie.Wt, ↓reduceIte]
  wpx [Pie.W_0, Pie.o0]
  exact Or.inr trivial

theorem pie_fnAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L Pie.pie_at Pie.pie) :
    FnAt prof F Wl L s₀ o Pie.pie_at 4 fun R g V => R g V :=
  (fnAt_cfg c hin (fun ℓ => Pie.spAll prof ℓ) 4 (fun (K : Gprs × (Addr → Byte)) ℓ _ g V => ℓ = 0 ∧ g = K.1 ∧ V = K.2)
    (fun K g V => g = K.1 ∧ V = K.2) (fun _ => True) (fun _ => 0) (fun K _ ℓ => pie_vc K ℓ)).mono (by
      rintro R g V hR
      exact ⟨(g, V), trivial, ⟨rfl, rfl, rfl⟩, by rintro g' V' ⟨rfl, rfl⟩; exact hR⟩)

/-! ## The table -/

/-- What the callees need at their entries, for `R` at their `ret`s. -/
abbrev Taux (F : Footprint) (Wl : List Rgn) (R : Gprs → (Addr → Byte) → Prop) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ K : Auxv.Ctx, (K.Ok ∧ Auxv.Env K F Wl) ∧ Auxv.P0 K (3 * K.N + 400) g V ∧ ∀ g' V', Auxv.Ret K g' V' → R g' V'
abbrev Tsec (F : Footprint) (R : Gprs → (Addr → Byte) → Prop) (g : Gprs) (V : Addr → Byte) : Prop :=
  (∀ i, i < 4 → Foot F.data (Addr.add 0x7a85c4#64 i)) ∧
    ofBytesLE 32 (List.map V (byteAddrs 0x7a85c4#64 4)) ≠ 0 ∧ ∀ a, R (g.set 0 a) V
abbrev Ttin (F : Footprint) (Wl : List Rgn) (R : Gprs → (Addr → Byte) → Prop) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ K : Tun.Ctx, (K.Ok ∧ Tun.Env K F Wl) ∧ Tun.P0 K (K.N * K.B + K.B + 1) g V ∧ ∀ g' V', Tun.Ret K g' V' → R g' V'

/-- What the code from a cut point needs for `Q` at the next ones: at a `call`, what the call needs. -/
def WtC (F : Footprint) (Wl : List Rgn) (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 71 then CallW F Wl lsm_at 76 (fun R g V => R g V) else
  if ℓ = 131 then CallW F Wl lsm_at 136 (Taux F Wl) else
  if ℓ = 194 then CallW F Wl lsm_at 199 (Tsec F) else
  if ℓ = 206 then CallW F Wl lsm_at 211 (Ttin F Wl) else
  Wt ℓ F Wl

/-- The cut points' pieces, in a run with the five functions' code. -/
theorem spC (c : Seg prof F Wl L s₀ o) (hl : CodeIn L lsm_at lsm) (hp : CodeIn L Pie.pie_at Pie.pie)
    (ha : CodeIn L Auxv.aux_at Auxv.aux) (hs : CodeIn L Sec.sec_at Sec.sec) (ht : CodeIn L Tun.tin_at Tun.tin)
    (ℓ : Nat) : SpAt prof F Wl L s₀ o lsm_at ℓ (WtC F Wl ℓ) := by
  unfold WtC
  split
  · subst ℓ
    exact SpAt.call c hl (lt_len (by decide)) (call_71 _) (lt_len (by decide)) hp (by decide) (by decide)
      (Pie.lt_len (by decide)) (pie_ret _) (pie_fnAt c hp)
  split
  · subst ℓ
    exact SpAt.call c hl (lt_len (by decide)) (call_131 _) (lt_len (by decide)) ha (Auxv.lt_len (by decide)) (by decide)
      (Auxv.lt_len (by decide)) (Auxv.ret_493 _) (aux_fnAt c ha)
  split
  · subst ℓ
    exact SpAt.call c hl (lt_len (by decide)) (call_194 _) (lt_len (by decide)) hs (Sec.lt_len (by decide)) (by decide)
      (Sec.lt_len (by decide)) (Sec.ret_14 _) (sec_fnAt c hs)
  split
  · subst ℓ
    exact SpAt.call c hl (lt_len (by decide)) (call_206 _) (lt_len (by decide)) ht (Tun.lt_len (by decide)) (by decide)
      (Tun.lt_len (by decide)) (Tun.ret_344 _) (tin_fnAt c ht)
  exact (spAll prof ℓ).at c hl

end FV7z.Start
