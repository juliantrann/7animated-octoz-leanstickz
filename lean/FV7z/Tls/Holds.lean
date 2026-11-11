import FV7z.Tls.Mem
/-!
# `__libc_setup_tls` sets up the thread control block (PLAN.md G3, startup)

glibc 2.31's `__libc_setup_tls` at `0x613a10` in `7zzs`, as a theorem about the whole function on the one way the
run of `7zzs` takes.

- `CpyAt`: the contract of the `memcpy` it calls through the PLT (`0x401070`, an IFUNC), a hypothesis here; `Pm`
  is what the contract asks of the bytes at the call (the GOT entry the PLT jumps through, say).
- `setup_tls`: from a start with `Base` and the break `b` (a multiple of 4096, above the variables, two pages and
  128 bytes below the stack pointer), the bytes at the entry with `In`, the kernel not refusing memory, the run
  reaches the `ret` (523) from a new start with the two new pages `[b, b + 8192)` in the footprint, `Base` with
  the break `b + 4544` and the `fs` base `b + 2176`. There `rax` is 4480, the registers a call keeps are as at the
  entry (`Saved`), and outside the 128 bytes below the stack pointer the bytes are `TlsMem V b`. The events are the
  two `brk` of `__sbrk` and the `arch_prctl`; of the latter's registers the kernel does not use, four are as
  `__sbrk` and `memcpy` left them.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)

namespace FV7z.Tls
variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- What a call of `memcpy` at `e` does, the bytes at the call with `Pm`: called with a return address in code of
the list, the `rdx` bytes at `rsi` to read, those at `rdi` to store to, the two apart and those at `rdi` apart from
the return address, the run reaches the return address with `rax` the `rdi` of the call, the registers a call
keeps kept, the bytes at `rdi` those at `rsi`, and the other bytes as they were. -/
def CpyAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot F.data (Addr.add X.cpu.gpr.rsi i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
    X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 → X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 →
    (X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsi.toNat) →
    (X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
    (∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < X.cpu.gpr.rdx.toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = V (Addr.add X.cpu.gpr.rsi i)) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat) →
        V₂ a = V a) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- The pages of the break `n`, a multiple of 4096, and of `n + 4544`. -/
theorem pg_up (n : Nat) (h : n % 4096 = 0) :
    pageUp n / 4096 * 4096 = n ∧ pageUp (n + 4544) / 4096 * 4096 = n + 8192 ∧ pageUp n / 4096 = n / 4096 ∧
      pageUp (n + 4544) / 4096 = n / 4096 + 2 := by
  unfold pageUp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- From the return of `memcpy` to the `ret`: `tls_c` and `tls_d`, with the bytes `TlsMem V b` outside the stack the
function uses, `q` the stack pointer after the prologue and `g₀` the registers of the entry. -/
theorem tls_end {G : Footprint} {Wn : List Rgn} {s₁ Y : State} {V₆ : Addr → Byte} {q b : Addr} {lim : Nat}
    {bb fsb : Addr} {ks : Kst} {g₀ : Gprs} (cs : Seg prof G Wn L s₁ o) (hB : Base s₁ lim bb fsb ks)
    (hin : CodeIn L tls_at tls)
    (hK : KeptW Wn s₁ Y) (hA : Agree G Y.proc.mm.mem V₆) (hr : Y.cpu.rip = tls_at.add 304)
    (hsp : Y.cpu.gpr.rsp = q) (hbx : Y.cpu.gpr.rbx = 2176#64) (hbp : Y.cpu.gpr.rbp = 64#64)
    (h12 : Y.cpu.gpr.r12 = 8#64) (h13 : Y.cpu.gpr.r13 = 7829360#64) (h14 : Y.cpu.gpr.r14 = 7943392#64)
    (h15 : Y.cpu.gpr.r15 = 128#64) (h24 : rdq(V₆, q + 24#64) = b) (hfr : Fr q g₀ (WC V₆ b))
    (h6 : Eo (Scr g₀.rsp) V₆ (T4 V b)) (hss : rdq(V, 7938736#64) = 2048#64)
    (hbl : 0x7a9000 ≤ b.toNat) (hb47 : b.toNat + 8192 ≤ 2 ^ 47 - 4096)
    (hsb : b.toNat + 8192 + 128 ≤ g₀.rsp.toNat) (hq : q = g₀.rsp - 88)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wn a)
    (hst : ∀ i < 88, Foot Wn (Addr.add q i))
    (hpg : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < b.toNat + 8192 → Foot Wn a)
    (k : ∀ s₂ Z t' W (d r10 r8 r9 : BitVec 64), Seg prof G Wn L s₂ o → Base s₂ lim bb (b + 2176#64) ks →
      KeptW Wn s₂ Z → Agree G Z.proc.mm.mem W → Z.cpu.rip = tls_at.add 523 → Z.cpu.gpr.rax = 4480#64 →
      Saved g₀ Z.cpu.gpr → Eo (Scr g₀.rsp) W (TlsMem V b) →
      GoG prof L o (gev ++ [⟨158#64, [4098#64, b + 2176#64, d, r10, r8, r9], 0, [], []⟩]) gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hqn : q.toNat + 88 = g₀.rsp.toNat := by rw [hq]; bv_omega
  have slot : ∀ a : Addr, ∀ k < 88, a = Addr.add q k → Foot Wn a := fun a k hk ha => ha ▸ hst k hk
  refine tls_c cs hB hin hK hA hr hsp hbx h24
    (fun i hi => cs.hws _ (slot _ (24 + i) (by omega) (by simp only [Addr.add]; bv_omega)))
    (fun i hi => hpg _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)) (by bv_omega) ?_
  rintro s₂ t₇ c₂ hB₂ hA₇ hr₇ ⟨hax₇, hsp₇, hbp₇, h12₇, h13₇, h14₇, h15₇⟩
  -- to the `ret`
  have h7 : Eo (Scr g₀.rsp) (WC V₆ b) (WC (T4 V b) b) := h6.wc b
  have nscr : ∀ x : Addr, x.toNat < b.toNat + 8192 → ¬ Scr g₀.rsp x := by
    intro x hx hs
    unfold Scr at hs
    omega
  have hs₇ : rdq(WC V₆ b, 7938736#64) = 2048#64 := by
    rw [h7.rd 7938736#64 8 fun i hi => nscr _ (by simp only [Addr.add]; bv_omega), ssize_t V hbl (by omega)]
    exact hss
  refine tls_d (x13 := 7829360#64) c₂ hin (KeptW.refl _ s₂) hA₇ hr₇ hax₇ hsp₇ (hbp₇.trans hbp) (h12₇.trans h12)
    (h13₇.trans h13) (h14₇.trans h14) (h15₇.trans h15) hfr hs₇ (by omega) (by omega) hgl
    (fun i hi => c₂.hws _ (hst i hi)) ?_
  rintro Z₈ t₈ hK₈ hA₈ hr₈ ⟨hsp₈, hax₈, hbx₈, hbp₈, h12₈, h13₈, h14₈, h15₈⟩
  exact k s₂ Z₈ t₈ _ _ _ _ _ c₂ hB₂ hK₈ hA₈ hr₈ hax₈
    ⟨hsp₈.trans (by rw [hq]; bv_omega), hbx₈, hbp₈, h12₈, h13₈, h14₈, h15₈⟩ (h7.wd _)

set_option maxHeartbeats 3200000 in
/-- `__libc_setup_tls` on the way the run of `7zzs` takes: two `brk`, the copy of the image, `arch_prctl`, and the
`ret` with `rax` 4480, the saved registers back, the bytes `TlsMem V b` outside the 128 bytes below the stack
pointer of the entry, from a start with the break `b + 4544` and the `fs` base `b + 2176`. -/
theorem setup_tls {lim : Nat} {b fsb : Addr} {ks : Kst} {Pm : (Addr → Byte) → Prop} {cpy : List Byte}
    (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks) (hin : CodeIn L tls_at tls)
    (hins : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hinc : CodeIn L 4198512#64 cpy) (hc0 : 0 < cpy.length) (hcpy : CpyAt prof L o 4198512#64 Pm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tls_at) (hI : In V)
    (hst : ∀ i < 128, Foot Wl (Addr.add (X.cpu.gpr.rsp - 128) i))
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hhd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x401000 → Foot F.data a)
    (hbl : 0x7a9000 ≤ b.toNat) (hbp : b.toNat % 4096 = 0) (hsp : b.toNat + 8192 + 128 ≤ X.cpu.gpr.rsp.toNat)
    (hmg : ∀ t p, o t (.memFail p) = none) (hlim : b.toNat / 4096 + 2 ≤ lim)
    (hPm : ∀ W, Eo (Scr X.cpu.gpr.rsp) W (T3 V b) → Pm W)
    (k : ∀ s₂ Z t' W (d r10 r8 r9 : BitVec 64), Seg prof (withNew F [⟨b, 8192⟩]) ([⟨b, 8192⟩] ++ Wl) L s₂ o →
      Base s₂ lim (b + 4544#64) (b + 2176#64) ks → KeptW ([⟨b, 8192⟩] ++ Wl) s₂ Z →
      Agree (withNew F [⟨b, 8192⟩]) Z.proc.mm.mem W → Z.cpu.rip = tls_at.add 523 → Z.cpu.gpr.rax = 4480#64 →
      Saved X.cpu.gpr Z.cpu.gpr → Eo (Scr X.cpu.gpr.rsp) W (TlsMem V b) →
      GoG prof L o (gev ++ [⟨12, [0, X.cpu.gpr.rsi, 63#64, X.cpu.gpr.r10, 7829360#64, X.cpu.gpr.r9], b, [], []⟩,
        ⟨12, [b + 4544#64, X.cpu.gpr.rsi, 63#64, X.cpu.gpr.r10, 7829360#64, X.cpu.gpr.r9], b + 4544#64, [], []⟩,
        ⟨158#64, [4098#64, b + 2176#64, d, r10, r8, r9], 0, [], []⟩]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.top
  have hb47 : b.toNat + 8192 ≤ 2 ^ 47 - 4096 := by omega
  have hglD : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a :=
    fun a h1 h2 => c.hws _ (hgl a h1 h2)
  have slot : ∀ a : Addr, ∀ k < 128, a = Addr.add (X.cpu.gpr.rsp - 128) k → Foot Wl a :=
    fun a k hk ha => ha ▸ hst k hk
  refine tls_a c hin hK hA hrip hI
    (fun i hi => slot _ (40 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hglD hhd (by omega) ?_
  intro Z₁ t₁ W₁ hK₁ hA₁ hr₁ hg₁ hfr₁ hout₁
  have hsp₁ : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 := by rw [hg₁]; rfl
  generalize hq : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40 = q at hfr₁ hsp₁
  have hq8 : q = X.cpu.gpr.rsp - 88 := by rw [← hq]; bv_omega
  clear hq
  have hqn : q.toNat + 88 = X.cpu.gpr.rsp.toNat := by rw [hq8]; bv_omega
  -- the `call` of `__sbrk`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_184 _) hins (Sbrk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact slot _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁] at hA₂ hg₂
  have hdi₂ : Y₂.cpu.gpr.rdi = 4544#64 := by rw [hg₂, hg₁]; rfl
  have hsp₂ : Y₂.cpu.gpr.rsp = q - 8 := by rw [hg₂]; rfl
  -- `__sbrk (4544)`
  obtain ⟨ep1, ep2', eg1, eg2⟩ := pg_up b.toNat hbp
  have e4544 : (b + 4544#64).toNat = b.toNat + 4544 := by bv_omega
  have ep2 : pageUp (b + 4544#64).toNat / 4096 * 4096 = b.toNat + 8192 := by rw [e4544]; exact ep2'
  have ev : ∀ a v, Sbrk.sbrkEv Y₂ a v =
      ⟨12, [a, X.cpu.gpr.rsi, 63#64, X.cpu.gpr.r10, 7829360#64, X.cpu.gpr.r9], v, [], []⟩ := by
    intro a v
    simp only [Sbrk.sbrkEv, hg₂, hg₁]
    rfl
  refine Sbrk.sbrk_first c hB hins hinb hK₂ hA₂ hr₂
    (fun i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
    (fun i hi => ?_) (by rw [hsp₂]; bv_omega) ?_ (by rw [hdi₂]; decide) (by rw [hdi₂]; decide) hmg ?_ ?_
    (N := [⟨b, 8192⟩]) ?_ ?_
  · rw [hsp₂]
    exact slot _ i (by omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst, rd_ext curbrk 8 fun i hi => hout₁ _ (by simp only [Addr.add]; bv_omega)]
    · exact hI.cur
    all_goals sd
  · rw [hdi₂, e4544, eg1, eg2]
    omega
  · rw [hdi₂, e4544, eg2]
    exact hlim
  · rw [hdi₂, ep1, ep2]
    intro r hr
    obtain rfl := List.mem_singleton.1 hr
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  rw [hdi₂, ep1, ep2, ev, ev]
  intro g' V₃ s₁ Z₃ t₃ c₁ hB₁ hK₃ hA₃ hr₃ hg₃ hax₃ hsv₃ hz₃ hf₃ hcb₃
  obtain ⟨hs_sp, hs_bx, hs_bp, hs_12, hs_13, hs_14, hs_15⟩ := hsv₃
  subst hg₃
  rw [hsp₂] at hf₃
  have scr8 : ∀ (x : Addr) (v : BitVec 64), X.cpu.gpr.rsp.toNat - 128 ≤ x.toNat → x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat →
      ∀ i < (toBytesLE v 8).length, Scr X.cpu.gpr.rsp (x.add i) := by
    intro x v h1 h2 i hi
    rw [toBytesLE_length] at hi
    unfold Scr
    simp only [Addr.add]
    bv_omega
  have h3 : Eo (Scr X.cpu.gpr.rsp) V₃ (T2 V b) := by
    refine eo_sbrk (r := q - 8) hbl hsp (by bv_omega) (by bv_omega) (fun a ha => ?_) hz₃ hf₃ hcb₃
    unfold Scr at ha
    rw [Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]
    exact hout₁ a (by omega)
  have hfr₃ : Fr q X.cpu.gpr V₃ := by
    refine hfr₁.keep (by omega) fun a h1 h2 _ => ?_
    rw [hf₃ a (by omega) (by bv_omega) (by omega), Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]
  have hra₃ : rdq(V₃, q - 8) = tls_at.add 189 := by
    rw [rd_ext (q - 8) 8 fun i hi => hf₃ _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
      (by simp only [Addr.add]; bv_omega), rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  have hglN : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot ([⟨b, 8192⟩] ++ Wl) a :=
    fun a h1 h2 => foot_append_iff.2 (.inr (hgl a h1 h2))
  have slotN : ∀ a : Addr, ∀ k < 128, a = Addr.add (X.cpu.gpr.rsp - 128) k → Foot ([⟨b, 8192⟩] ++ Wl) a :=
    fun a k hk ha => foot_append_iff.2 (.inr (slot a k hk ha))
  have pgN : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < b.toNat + 8192 → Foot ([⟨b, 8192⟩] ++ Wl) a :=
    fun a h1 h2 => foot_append_iff.2 (.inl ⟨⟨b, 8192⟩, List.mem_singleton.2 rfl, h1, h2⟩)
  have e13 : Z₃.cpu.gpr.r13 = 7829360#64 := hs_13.trans (by rw [hg₂, hg₁]; rfl)
  refine tls_b c₁ hin hins hK₃ hA₃ hr₃ (hs_sp.trans hsp₂) hra₃ hax₃ (by omega) (hs_bx.trans (by rw [hg₂, hg₁]; rfl))
    (hs_bp.trans (by rw [hg₂, hg₁]; rfl)) (hs_12.trans (by rw [hg₂, hg₁]; rfl))
    (hs_14.trans (by rw [hg₂, hg₁]; rfl)) (hs_15.trans (by rw [hg₂, hg₁]; rfl)) hfr₃ (by omega) (by omega) hglN
    (fun i hi => slotN _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega)) ?_
  rintro Z₄ t₄ hK₄ hA₄ hr₄ ⟨hsp₄, hdi₄, hsi₄, hdx₄, hbx₄, hbp₄, h12₄, h13₄, h14₄, h15₄⟩
  rw [e13] at hsi₄ h13₄
  -- the `call` of `memcpy`
  refine c₁.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_299 _) hinc hc0 (by decide) (fun i hi => ?_) ?_
  · rw [hsp₄]
    exact slotN _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [hsp₄] at hA₅ hg₅
  have h5 : Eo (Scr X.cpu.gpr.rsp) (Vst (WB V₃ q b) (q - 8) (toBytesLE (tls_at.add (299 + 5)) 8)) (T3 V b) :=
    (((((h3.st _ _).st_in _ _ (scr8 _ _ (by bv_omega) (by bv_omega))).st _ _).st _ _).st _ _).st_in _ _
      (scr8 _ _ (by bv_omega) (by bv_omega))
  have hdi₅ : Y₅.cpu.gpr.rdi = 2048#64 + b := by rw [hg₅]; exact hdi₄
  have hsi₅ : Y₅.cpu.gpr.rsi = 7829360#64 := by rw [hg₅]; exact hsi₄
  have hdx₅ : Y₅.cpu.gpr.rdx = 40#64 := by rw [hg₅]; exact hdx₄
  have hsp₅ : Y₅.cpu.gpr.rsp = q - 8 := by rw [hg₅]; rfl
  refine hcpy c₁ hK₅ hA₅ hr₅ (hPm _ h5) hin (j := 304) (lt_len (by decide)) ?_ (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) (by rw [hsi₅, hdx₅]; decide) (by rw [hdi₅, hdx₅]; bv_omega)
    (by rw [hsi₅, hdi₅, hdx₅]; left; bv_omega) (by rw [hdi₅, hdx₅, hsp₅]; left; bv_omega) ?_
  · rw [hsp₅, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [hsp₅]
    exact c₁.hws _ (slotN _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · rw [hdx₅] at hi
    have hi' : i < 40 := hi
    rw [hsi₅]
    exact c₁.hws _ (hglN _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
  · rw [hdx₅] at hi
    have hi' : i < 40 := hi
    rw [hdi₅]
    exact pgN _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  intro Z₆ t₆ V₆ hK₆ hA₆ hr₆ hsp₆ hax₆ hbx₆ hbp₆ h12₆ h13₆ h14₆ h15₆ hcp₆ hf₆
  rw [hdi₅, hsi₅, hdx₅] at hcp₆
  rw [hdi₅, hdx₅] at hf₆
  have hsp₆' : Z₆.cpu.gpr.rsp = q := by rw [hsp₆, hsp₅]; bv_omega
  have h6 : Eo (Scr X.cpu.gpr.rsp) V₆ (T4 V b) :=
    eo_cpy hbl (by omega) (fun a ha hs => by unfold Scr at hs; omega) h5 hcp₆ hf₆
  have h24 : rdq(V₆, q + 24#64) = b := by
    rw [rd_ext (q + 24#64) 8 fun i hi => hf₆ _ (by simp only [Addr.add]; bv_omega),
      rd24 _ _ _ _ (by omega) (by omega)]
  have hfr₇ : Fr q X.cpu.gpr (WC V₆ b) := fr_c hfr₃ hbl (by omega) (by omega) hf₆
  -- `arch_prctl (ARCH_SET_FS, b + 2176)` and the end
  refine tls_end c₁ hB₁ hin hK₆ hA₆ hr₆ hsp₆' (hbx₆.trans (by rw [hg₅]; exact hbx₄))
    (hbp₆.trans (by rw [hg₅]; exact hbp₄)) (h12₆.trans (by rw [hg₅]; exact h12₄))
    (h13₆.trans (by rw [hg₅]; exact h13₄)) (h14₆.trans (by rw [hg₅]; exact h14₄))
    (h15₆.trans (by rw [hg₅]; exact h15₄)) h24 hfr₇ h6 hI.ssize hbl hb47 hsp hq8 hglN
    (fun i hi => slotN _ (40 + i) (by omega) (by simp only [Addr.add]; bv_omega)) pgN ?_
  intro s₂ Z₈ t₈ W d r10 r8 r9 c₂ hB₂ hK₈ hA₈ hr₈ hax₈ hsv₈ hE₈
  rw [List.append_assoc]
  exact k s₂ Z₈ t₈ W d r10 r8 r9 c₂ hB₂ hK₈ hA₈ hr₈ hax₈ hsv₈ hE₈

end FV7z.Tls
