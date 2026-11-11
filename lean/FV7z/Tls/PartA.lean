import FV7z.Tls.Vc
/-!
# `__libc_setup_tls`: from the entry to the `call` of `__sbrk` (PLAN.md G3, startup)

- `Fr`: what the function keeps in its frame (the six registers it saves, the sizes of the image and of the
  memory); `Fr.keep`: stores outside the frame keep it.
- `loop_step`: a turn of the loop over the program headers.
- `tls_a`: the prologue, five turns of the loop, the `PT_TLS` header and the first `div`, to the `call` of
  `__sbrk (4544)` with the registers `gA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Tls
variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces of the run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- Bytes that are the same are read the same. -/
theorem rd_ext {W W' : Addr → Byte} (x : Addr) (n : Nat) (h : ∀ i < n, W' (x.add i) = W (x.add i)) :
    List.map W' (byteAddrs x n) = List.map W (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h j hj

/-- The frame: what the function keeps on the stack, `q` the stack pointer after the prologue and `g₀` the
registers at the entry. -/
structure Fr (q : Addr) (g₀ : Gprs) (W : Addr → Byte) : Prop where
  fs : rdq(W, q + 8#64) = 40#64
  ms : rdq(W, q + 16#64) = 128#64
  bx : rdq(W, q + 40#64) = g₀.rbx
  bp : rdq(W, q + 40#64 + 8) = g₀.rbp
  r12 : rdq(W, q + 40#64 + 8 + 8) = g₀.r12
  r13 : rdq(W, q + 40#64 + 8 + 8 + 8) = g₀.r13
  r14 : rdq(W, q + 40#64 + 8 + 8 + 8 + 8) = g₀.r14
  r15 : rdq(W, q + 40#64 + 8 + 8 + 8 + 8 + 8) = g₀.r15

/-- The frame is kept by stores outside it. -/
theorem Fr.keep {q : Addr} {g₀ : Gprs} {W W' : Addr → Byte} (h : Fr q g₀ W) (hq : q.toNat + 88 ≤ 2 ^ 64)
    (he : ∀ a : Addr, q.toNat + 8 ≤ a.toNat → a.toNat < q.toNat + 88 →
      ¬ (q.toNat + 24 ≤ a.toNat ∧ a.toNat < q.toNat + 40) → W' a = W a) : Fr q g₀ W' := by
  have e : ∀ x : Addr, q.toNat + 8 ≤ x.toNat → x.toNat + 8 ≤ q.toNat + 88 →
      (x.toNat + 8 ≤ q.toNat + 24 ∨ q.toNat + 40 ≤ x.toNat) → rdq(W', x) = rdq(W, x) := by
    intro x h1 h2 h3
    rw [rd_ext x 8 fun i hi => he _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
      (by simp only [Addr.add]; bv_omega)]
  exact ⟨(e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.fs,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.ms,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.bx,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.bp,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.r12,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.r13,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.r14,
    (e _ (by bv_omega) (by bv_omega) (by bv_omega)).trans h.r15⟩

/-- The bytes after the six `push`es. -/
abbrev P6 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

theorem In.p6 (hI : In V) (g : Gprs) (hsp : 0x7a9000 + 128 ≤ g.rsp.toNat) : In (P6 V g) := by
  have e : ∀ (a : Addr) (n : Nat), a.toNat + n ≤ 0x7a9000 →
      List.map (P6 V g) (byteAddrs a n) = List.map V (byteAddrs a n) :=
    fun a n ha => rd_p6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx a n hsp ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e _ _ (by decide)]; exact hI.phdr
  · rw [e _ _ (by decide)]; exact hI.phnum
  · rw [e _ _ (by decide)]; exact hI.map
  · rw [e _ _ (by decide)]; exact hI.laddr
  · rw [e _ _ (by decide)]; exact hI.ssize
  · rw [e _ _ (by decide)]; exact hI.cur
  · rw [e _ _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]; exact hI.nt i hi
  · rw [e _ _ (by decide)]; exact hI.ty
  · rw [e _ _ (by decide)]; exact hI.vaddr
  · rw [e _ _ (by decide)]; exact hI.filesz
  · rw [e _ _ (by decide)]; exact hI.memsz
  · rw [e _ _ (by decide)]; exact hI.align

/-- A program header that is not `PT_TLS`: a turn of the loop. -/
theorem loop_step (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tls_at tls) {Y : State} {W : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = tls_at.add 93) {x : Addr}
    (hx : 0x400000 ≤ x.toNat) (hx' : x.toNat + 56 < 4194816)
    (hax : Y.cpu.gpr.rax = x) (hdx : Y.cpu.gpr.rdx = 4194816#64) (h7 : rdd(W, x) ≠ 7#32)
    (hhd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x401000 → Foot F.data a)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = tls_at.add 93 →
      Z.cpu.gpr = Y.cpu.gpr.set 0 (x + 56#64) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_93 prof).run c hin _ hK hA hr (vc_93n (fun j hj => ?_) (by rw [hax]; exact h7) ?_) ?_
  · rw [hax]
    exact hhd _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [hax, hdx]
    bv_omega
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t' hK' hA' hr' hg' -
  exact k Z t' hK' hA' hr' (by rw [hg', hax])

/-- The registers at the `call` of `__sbrk`. -/
def gA (g : Gprs) : Gprs :=
  { g with rax := 2176#64, rcx := 40#64, rdx := 63#64, rbx := 2176#64, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40,
           rbp := 64#64, rdi := 4544#64, r8 := 7829360#64, r12 := 8#64, r13 := 7829360#64, r14 := 7943392#64,
           r15 := 1#64 }

set_option maxHeartbeats 1600000 in
/-- The frame at the `call` of `__sbrk`. -/
theorem fr_a (V : Addr → Byte) (g : Gprs) (hsp : 0x7a9000 + 128 ≤ g.rsp.toNat) :
    Fr (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40) g (Vst (Vst (P6 V g) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 + 16#64)
      (toBytesLE 128#64 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 + 8#64) (toBytesLE 40#64 8)) := by
  have e1 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 + 40#64 = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 := by bv_omega
  have e2 : g.rsp - 8 - 8 - 8 - 8 - 8 - 8 + 8 = g.rsp - 8 - 8 - 8 - 8 - 8 := by bv_omega
  have e3 : g.rsp - 8 - 8 - 8 - 8 - 8 + 8 = g.rsp - 8 - 8 - 8 - 8 := by bv_omega
  have e4 : g.rsp - 8 - 8 - 8 - 8 + 8 = g.rsp - 8 - 8 - 8 := by bv_omega
  have e5 : g.rsp - 8 - 8 - 8 + 8 = g.rsp - 8 - 8 := by bv_omega
  have e6 : g.rsp - 8 - 8 + 8 = g.rsp - 8 := by bv_omega
  unfold P6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, e2, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, e2, e3, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, e2, e3, e4, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, e2, e3, e4, e5, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [e1, e2, e3, e4, e5, e6, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd

/-- The bytes at the `call` of `__sbrk`, outside the 88 below the stack pointer of the entry. -/
theorem out_a (V : Addr → Byte) (g : Gprs) (hsp : 0x7a9000 + 128 ≤ g.rsp.toNat) (a : Addr)
    (h : ¬ (g.rsp.toNat - 88 ≤ a.toNat ∧ a.toNat < g.rsp.toNat)) :
    Vst (Vst (P6 V g) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 + 16#64) (toBytesLE 128#64 8))
      (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 + 8#64) (toBytesLE 40#64 8) a = V a := by
  unfold P6
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals simp only [toBytesLE_length]
  all_goals bv_omega

set_option maxHeartbeats 1600000 in
/-- From the entry to the `call` of `__sbrk`. -/
theorem tls_a (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tls_at tls) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tls_at) (hI : In V)
    (hst : ∀ i < 88, Foot Wl (Addr.add (X.cpu.gpr.rsp - 88) i))
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a)
    (hhd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x401000 → Foot F.data a)
    (hsp : 0x7a9000 + 128 ≤ X.cpu.gpr.rsp.toNat)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = tls_at.add 184 →
      Z.cpu.gpr = gA X.cpu.gpr → Fr (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40) X.cpu.gpr W →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 88 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → W a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hI₁ := hI.p6 X.cpu.gpr hsp
  have slot : ∀ a : Addr, ∀ k < 88, a = Addr.add (X.cpu.gpr.rsp - 88) k → Foot Wl a := fun a k hk ha => ha ▸ hst k hk
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hI (fun i hi => slot _ (40 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hgl hsp) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine loop_step c hin hK₁ hA₁ hr₁ (x := 4194368#64) (by decide) (by decide) (by rw [hg₁]; rfl)
    (by rw [hg₁]; rfl) (hI₁.nt 0 (by decide)) hhd ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  refine loop_step c hin hK₂ hA₂ hr₂ (x := 4194424#64) (by decide) (by decide) (by rw [hg₂]; rfl)
    (by rw [hg₂, hg₁]; rfl) (hI₁.nt 1 (by decide)) hhd ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃
  refine loop_step c hin hK₃ hA₃ hr₃ (x := 4194480#64) (by decide) (by decide) (by rw [hg₃]; rfl)
    (by rw [hg₃, hg₂, hg₁]; rfl) (hI₁.nt 2 (by decide)) hhd ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄
  refine loop_step c hin hK₄ hA₄ hr₄ (x := 4194536#64) (by decide) (by decide) (by rw [hg₄]; rfl)
    (by rw [hg₄, hg₃, hg₂, hg₁]; rfl) (hI₁.nt 3 (by decide)) hhd ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅
  refine loop_step c hin hK₅ hA₅ hr₅ (x := 4194592#64) (by decide) (by decide) (by rw [hg₅]; rfl)
    (by rw [hg₅, hg₄, hg₃, hg₂, hg₁]; rfl) (hI₁.nt 4 (by decide)) hhd ?_
  intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆
  have hsp₆ : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 := by
    rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; rfl
  refine (c_93 prof).run c hin _ hK₆ hA₆ hr₆ (vc_93e hI₁ (by rw [hg₆]; rfl) (by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; rfl)
    (fun i hi => ?_) hgl hhd) ?_
  · rw [hsp₆]
    exact slot _ (8 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [hsp₆] at hA₇
  have hrv : rv Y₇ 64 5 = 64#64 := by
    show (Y₇.cpu.gpr.get (regOf 5)).setWidth 64 = _
    rw [hg₇]
    rfl
  refine c.s_div64 hK₇ hA₇ hin (lt_len (by decide)) hr₇ (div_166 _) (by rw [hg₇]; rfl)
    (by rw [hrv]; decide) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  have hax₇ : Y₇.cpu.gpr.rax = 2239#64 := by rw [hg₇]; rfl
  have ed : 2239#64 / 64#64 = 34#64 := by decide
  have em : 2239#64 % 64#64 = 63#64 := by decide
  rw [hrv, hax₇, ed, em] at hg₈
  refine (c_169 prof).run c hin _ hK₈ hA₈ hr₈ (vc_169 (by rw [hg₈, hg₇]; rfl) (by rw [hg₈, hg₇]; rfl)) ?_
  rintro j' g fl V₉ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  refine k Y₉ t₉ _ hK₉ hA₉ hr₉ ?_ (fr_a V X.cpu.gpr hsp) (out_a V X.cpu.gpr hsp)
  rw [hg₉, hg₈, hg₇, hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]
  rfl

end FV7z.Tls
