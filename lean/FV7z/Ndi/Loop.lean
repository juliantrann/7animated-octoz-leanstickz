import FV7z.Ndi.Env
import FV7z.Ndi.Vc3
import FV7z.Ndi.Vc4
/-!
# `_dl_non_dynamic_init`: the loop over the program headers (PLAN.md G3, startup)

From 2575 to the `call` of `_dl_protect_relro` (2879), for the eight program headers of `7zzs` (`Ph`: four
`PT_LOAD`, `PT_NOTE`, `PT_TLS`, `PT_GNU_STACK` with flags 6, `PT_GNU_RELRO` of `0x1a890` bytes at `0x777770`):
`_dl_stack_flags` becomes 6, the main map's `l_relro_addr` and `l_relro_size` the segment's (`lV`).

- `lp_o`: a header of another type, not the last.
- `body_b`: the whole way.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

/-- What the loop reads of the eight program headers at `0x400040`: the types, the flags of `PT_GNU_STACK`, the
address and the size in memory of `PT_GNU_RELRO`. -/
structure Ph (V : Addr → Byte) : Prop where
  t0 : rdd(V, 4194368#64) = 1#32
  t1 : rdd(V, 4194424#64) = 1#32
  t2 : rdd(V, 4194480#64) = 1#32
  t3 : rdd(V, 4194536#64) = 1#32
  t4 : rdd(V, 4194592#64) = 4#32
  t5 : rdd(V, 4194648#64) = 7#32
  t6 : rdd(V, 4194704#64) = 1685382481#32
  f6 : rdd(V, 4194708#64) = 6#32
  t7 : rdd(V, 4194760#64) = 1685382482#32
  a7 : rdq(V, 4194776#64) = 7829360#64
  m7 : rdq(V, 4194800#64) = 108688#64

/-- The bytes after the loop: `_dl_stack_flags` (`0x7933c8`) 6, the main map's `l_relro_addr` (`0x793948`)
`0x777770` and `l_relro_size` (`0x793950`) `0x1a890`. -/
def lV (M : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst M 7943112#64 (toBytesLE 6#32 4)) 7944520#64 (toBytesLE 7829360#64 8)) 7944528#64
    (toBytesLE 108688#64 8)

theorem lV_gk {V M : Addr → Byte} (h : Gk V M) : Gk V (lV M) :=
  ((h.st (toBytesLE_length _ 4) (by decide)).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 8)
    (by decide)

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

/-- A header of a type other than `PT_GNU_STACK` and `PT_GNU_RELRO`, not the last: to the next header. -/
theorem lp_o {W : Addr → Byte} {a : Addr} {ty : BitVec 32} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ndi_at ndi)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add 2687)
    (hax : X.cpu.gpr.rax = a) (hcx : X.cpu.gpr.rcx = 4194816#64) (hnl : (a + 56#64).toNat < 4194816)
    (hf : ∀ i < 4, Foot F.data (Addr.add a i)) (ht : rdd(W, a) = ty) (h1 : ty ≠ 1685382481#32)
    (h2 : ty ≠ 1685382482#32)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = ndi_at.add 2687 →
      Z.cpu.gpr = { X.cpu.gpr with rax := a + 56#64, rdx := ty.setWidth 64 } → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  subst hax
  refine (c_2687 prof).run c hin _ hK hA hrip (vc_2687_o hf ht h1 h2) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine (c_2678 prof).run c hin _ hK₁ hA₁ hr₁ vc_2678 ?_
  rintro j' g fl V₂ ⟨hj, -, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  obtain rfl := hj (by
    rw [hg₁]
    show (X.cpu.gpr.rax + 56#64).toNat < X.cpu.gpr.rcx.toNat
    rw [hcx]
    exact hnl)
  refine k Y₂ t₂ hK₂ hA₂ hr₂ ?_
  rw [hg₂, hg₁]

/-- From 2575, with the eight program headers of `7zzs`, to the `call` of `_dl_protect_relro (&_dl_main_map)`: the
bytes are `lV M` outside the 72 below `sp`, `r10`, `r8`, `r9` the size of the RELRO segment, 1 and the stack's
flags. -/
theorem body_b {V M W : Addr → Byte} {sp : Addr} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ndi_at ndi)
    (h72 : 8032256 + 72 ≤ sp.toNat) (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph V)
    (hd1 : rdq(V, 8029568#64) = 4194368#64) (hd2 : rdq(V, 8029592#64) = 8#64) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W M) (hG : Gk V M) (hrip : X.cpu.rip = ndi_at.add 2575)
    (hsp : X.cpu.gpr.rsp = sp)
    (k : ∀ Z t' W', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' → Eqo sp W' (lV M) →
      Z.cpu.rip = ndi_at.add 2879 → Z.cpu.gpr.rsp = sp → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      Z.cpu.gpr.rdi = 7943392#64 → Z.cpu.gpr.r10 = 108688#64 → Z.cpu.gpr.r8 = 1#64 → Z.cpu.gpr.r9 = 6#64 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have rd4 : ∀ a : Addr, a.toNat + 4 ≤ 7827456 → rdd(W, a) = rdd(V, a) := fun a ha => by
    rw [hM.rdi h72 _ 4 (by omega), hG.rdl _ 4 ha]
  have rd8 : ∀ a : Addr, a.toNat + 8 ≤ 7827456 → rdq(W, a) = rdq(V, a) := fun a ha => by
    rw [hM.rdi h72 _ 8 (by omega), hG.rdl _ 8 ha]
  have g1 : rdq(W, 8029568#64) = 4194368#64 := by
    rw [hM.rdi h72 _ 8 (by decide), hG.rd _ 8 (by decide) (by decide)]
    exact hd1
  have g2 : rdq(W, 8029592#64) = 8#64 := by
    rw [hM.rdi h72 _ 8 (by decide), hG.rd _ 8 (by decide) (by decide)]
    exact hd2
  have f4 : ∀ a : Addr, 4194368 ≤ a.toNat ∧ a.toNat + 4 ≤ 4194816 → ∀ i < 4, Foot F.data (Addr.add a i) :=
    fun a ha => rf hfp (by decide) a 4 ha
  have f8 : ∀ a : Addr, 4194368 ≤ a.toNat ∧ a.toNat + 8 ≤ 4194816 → ∀ i < 8, Foot F.data (Addr.add a i) :=
    fun a ha => rf hfp (by decide) a 8 ha
  refine (c_2575 prof).run c hin _ hK hA hrip (vc_2575 hr g1 g2) ?_
  rintro j' g fl V₀ ⟨rfl, rfl, rfl⟩ Y₀ t₀ hK₀ hA₀ hr₀ hg₀ -
  -- the four `PT_LOAD`, `PT_NOTE`, `PT_TLS`
  refine lp_o c hin hK₀ hA₀ hr₀ (a := 4194368#64) (by rw [hg₀]) (by rw [hg₀]) (by decide) (f4 _ (by decide))
    ((rd4 _ (by decide)).trans hph.t0) (by decide) (by decide) ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁
  rw [hg₀] at hg₁
  dsimp only at hg₁
  clear hg₀ hK₀ hA₀ hr₀
  refine lp_o c hin hK₁ hA₁ hr₁ (a := 4194424#64) (by rw [hg₁]; rfl) (by rw [hg₁]) (by decide)
    (f4 _ (by decide)) ((rd4 _ (by decide)).trans hph.t1) (by decide) (by decide) ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  rw [hg₁] at hg₂
  dsimp only at hg₂
  clear hg₁ hK₁ hA₁ hr₁
  refine lp_o c hin hK₂ hA₂ hr₂ (a := 4194480#64) (by rw [hg₂]; rfl) (by rw [hg₂]) (by decide)
    (f4 _ (by decide)) ((rd4 _ (by decide)).trans hph.t2) (by decide) (by decide) ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃
  rw [hg₂] at hg₃
  dsimp only at hg₃
  clear hg₂ hK₂ hA₂ hr₂
  refine lp_o c hin hK₃ hA₃ hr₃ (a := 4194536#64) (by rw [hg₃]; rfl) (by rw [hg₃]) (by decide)
    (f4 _ (by decide)) ((rd4 _ (by decide)).trans hph.t3) (by decide) (by decide) ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄
  rw [hg₃] at hg₄
  dsimp only at hg₄
  clear hg₃ hK₃ hA₃ hr₃
  refine lp_o c hin hK₄ hA₄ hr₄ (a := 4194592#64) (by rw [hg₄]; rfl) (by rw [hg₄]) (by decide)
    (f4 _ (by decide)) ((rd4 _ (by decide)).trans hph.t4) (by decide) (by decide) ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅
  rw [hg₄] at hg₅
  dsimp only at hg₅
  clear hg₄ hK₄ hA₄ hr₄
  refine lp_o c hin hK₅ hA₅ hr₅ (a := 4194648#64) (by rw [hg₅]; rfl) (by rw [hg₅]) (by decide)
    (f4 _ (by decide)) ((rd4 _ (by decide)).trans hph.t5) (by decide) (by decide) ?_
  intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆
  rw [hg₅] at hg₆
  dsimp only at hg₆
  clear hg₅ hK₅ hA₅ hr₅
  -- `PT_GNU_STACK`
  have ax₆ : Y₆.cpu.gpr.rax = 4194704#64 := by rw [hg₆]; rfl
  refine (c_2687 prof).run c hin _ hK₆ hA₆ hr₆ (vc_2687_s (by rw [ax₆]; exact f4 _ (by decide))
    (by rw [ax₆]; exact f4 _ (by decide)) (by rw [ax₆]; exact (rd4 _ (by decide)).trans hph.t6)) ?_
  rintro j' g fl V₇ ⟨hj, -, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  obtain rfl := hj (by rw [ax₆, show Y₆.cpu.gpr.rcx = 4194816#64 by rw [hg₆]]; decide)
  rw [ax₆, show rdd(_, 4194704#64 + 4#64) = 6#32 from (rd4 _ (by decide)).trans hph.f6, hg₆] at hg₇
  dsimp only at hg₇
  clear hg₆ hK₆ hA₆ hr₆ ax₆
  -- `PT_GNU_RELRO`, the last
  have ax₇ : Y₇.cpu.gpr.rax = 4194760#64 := by rw [hg₇]; rfl
  refine (c_2687 prof).run c hin _ hK₇ hA₇ hr₇ (vc_2687_r (by rw [ax₇]; exact f4 _ (by decide))
    (by rw [ax₇]; exact f8 _ (by decide)) (by rw [ax₇]; exact f8 _ (by decide))
    (by rw [ax₇]; exact (rd4 _ (by decide)).trans hph.t7)) ?_
  rintro j' g fl V₈ ⟨rfl, rfl, rfl⟩ Y₈ t₈ hK₈ hA₈ hr₈ hg₈ -
  rw [ax₇, show rdq(_, 4194760#64 + 40#64) = 108688#64 from (rd8 _ (by decide)).trans hph.m7,
    show rdq(_, 4194760#64 + 16#64) = 7829360#64 from (rd8 _ (by decide)).trans hph.a7, hg₇] at hg₈
  dsimp only at hg₈
  clear hg₇ hK₇ hA₇ hr₇ ax₇
  refine (c_2678 prof).run c hin _ hK₈ hA₈ hr₈ vc_2678 ?_
  rintro j' g fl V₉ ⟨-, hj, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  obtain rfl := hj (by
    rw [hg₈]
    show ¬ (4194760#64 + 56#64).toNat < (4194816#64).toNat
    decide)
  rw [hg₈] at hg₉
  dsimp only at hg₉
  clear hg₈ hK₈ hA₈ hr₈
  -- `_dl_stack_flags`
  refine (c_2715 prof).run c hin _ hK₉ hA₉ hr₉ (vc_2715 hw (by rw [hg₉])) ?_
  rintro j' g fl Va ⟨rfl, rfl, rfl⟩ Ya ta hKa hAa hra hga -
  rw [show Y₉.cpu.gpr.r9 = 6#64 by rw [hg₉]; rfl] at hAa
  -- the main map's `l_relro_addr`, `l_relro_size`
  refine (c_2727 prof).run c hin _ hKa hAa hra (vc_2727 hw (by rw [hga, hg₉])) ?_
  rintro j' g fl Vb ⟨rfl, rfl, rfl⟩ Yb tb hKb hAb hrb hgb -
  rw [hga, hg₉] at hgb hAb
  dsimp only at hgb hAb
  refine (c_2749 prof).run c hin _ hKb hAb hrb (vc_2749 (by
    rw [hgb]
    show (108688#64 : BitVec 64) ≠ 0#64
    decide)) ?_
  rintro j' g fl Vc ⟨rfl, rfl, rfl⟩ Yc tc hKc hAc hrc hgc -
  rw [hgb] at hgc
  exact k Yc tc _ hKc hAc (((hM.st _ _).st _ _).st _ _) hrc (by rw [hgc]; exact hsp) (by rw [hgc]) (by rw [hgc])
    (by rw [hgc]) (by rw [hgc]) (by rw [hgc]; rfl)
end FV7z.Ndi
