import FV7z.Dmc.Cuts
import FV7z.Sbrk.Next
import FV7z.Osv.Holds
/-!
# `__default_morecore` (PLAN.md G3, `malloc`)

glibc 2.31's `__default_morecore (n)` at `0x635ab0` in `7zzs` (`malloc/morecore.c`), `malloc`'s `MORECORE`:
`__sbrk (n)`, and a null pointer in place of `__sbrk`'s `-1`. `sysmalloc` calls it for the bytes of a new top chunk
and for the `correction` that aligns the end of the heap to a page.

- `call_8`, `ret_30`: the instructions outside the blocks; `vc_0`, `vc_13`: the verification conditions.
- `dmc_end`: from `__sbrk`'s `ret`, with `rax` not `-1`, to the caller's return address.
- `dmc_next`, `dmc_same`, `dmc_zero`: the three ways of `Sbrk.sbrk_next`, `sbrk_same`, `sbrk_zero`, with the break
  known: the run reaches the return address with `rax` the old break, `rdx` 0, the registers a call keeps as at the
  entry, and the bytes as at the entry but for the 48 below the stack pointer, `__curbrk` and the new pages.

The way not taken: `__sbrk` failing (`-1`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (sbrkEv rd_eq)
namespace FV7z.Dmc

/-! ## The instructions outside the blocks -/

def pc8 : List Byte := [0xe8, 0xd3, 0x08, 0x03, 0x00]
theorem pc8_0 : ∀ feat, Dec feat pc8 0 (FV7z.mk .call 64 [.rel 198867] 5) := by dec_rfl
theorem w_8 : pc8 <+: dmc.drop 8 := by decide +kernel
theorem w_30 : Sbrk.pret <+: dmc.drop 30 := by decide +kernel
/-- `call __sbrk`. -/
theorem call_8 (feat : Features) : Dec feat dmc 8 (FV7z.mk .call 64 [.rel 198867] 5) :=
  Dec.shift (j := 8) (k := 0) (pc8_0 feat) w_8 (Nat.zero_le _)
theorem ret_30 (feat : Features) : Dec feat dmc 30 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 30) (k := 0) (Sbrk.pret_0 feat) w_30 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: 8 bytes of stack. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 8 ∧ g' = { g with rsp := g.rsp - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]

/-- After `__sbrk`, its answer not `-1`: the answer stays, `rdx` is 0. -/
theorem vc_13 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax.toNat ≤ 2 ^ 47) :
    W_13 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = { g with rdx := 0, rsp := g.rsp + 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  have hne : rax ≠ 18446744073709551615#64 := by bv_omega
  wpx [W_13, o1, Op.cmov64, hne]
  rfl

/-! ## The run -/

theorem b16 (S : Addr) : S - 8#64 - 8 = S - 16#64 := by bv_omega
theorem u8 (S : Addr) : S - 16#64 + 8 + 8#64 = S := by bv_omega

/-- A byte of the 48 below the stack pointer at the entry. -/
theorem slot {sp a : Addr} (hst : ∀ i < 48, Foot Wl (Addr.add (sp - 48) i)) {k : Nat} (hk : k < 48)
    (ha : a = Addr.add (sp - 48) k) : Foot Wl a := ha ▸ hst k hk

/-- The 56 bytes of stack, from a range `[lo, hi)` no byte of the footprint is in. -/
theorem stack_out {P : Addr → Prop} {S : Addr} (hs : 48 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 48, P (Addr.add (S - 48) i)) (hlr : ∀ i < 8, P (Addr.add S i)) {a : Addr}
    (h1 : S.toNat - 48 ≤ a.toNat) (h2 : a.toNat < S.toNat + 8) : P a := by
  by_cases h3 : a.toNat < S.toNat
  · have e : Addr.add (S - 48) (a.toNat - (S.toNat - 48)) = a := by
      simp only [Addr.add]
      bv_omega
    exact e ▸ hst (a.toNat - (S.toNat - 48)) (by omega)
  · have e : Addr.add S (a.toNat - S.toNat) = a := by
      simp only [Addr.add]
      bv_omega
    exact e ▸ hlr (a.toNat - S.toNat) (by omega)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From a `ret` of `__sbrk` (at `r`) with `rax` an address `b`, the stack pointer 16 below `S`: back at 13, `rdx`
0, 8 bytes of stack given back, and the `ret` to the caller. The bytes are as they were. -/
theorem dmc_end {G : Footprint} {Wn : List Rgn} {s₁ Z : State} {V₂ : Addr → Byte} {S b : Addr} {r : Nat}
    (c : Seg prof G Wn L s₁ o) (hin : CodeIn L dmc_at dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wn s₁ Z) (hA : Agree G Z.proc.mm.mem V₂) (hr : Z.cpu.rip = Sbrk.sbk_at.add r) (hlt : r < 160)
    (hd : Dec prof.feat Sbrk.sbk r (FV7z.mk .ret 64 [] 1))
    (hsp : Z.cpu.gpr.rsp = S - 16#64) (hax : Z.cpu.gpr.rax = b) (hb : b.toNat ≤ 2 ^ 47)
    (hl1 : ∀ i < 8, Foot G.data (Addr.add (S - 16#64) i)) (hl2 : ∀ i < 8, Foot G.data (Addr.add S i))
    (h13 : rdq(V₂, S - 16#64) = dmc_at.add 13)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₂, S) = e₂.add j₂)
    (k : ∀ Z' t', KeptW Wn s₁ Z' → Agree G Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rax = b → Z'.cpu.gpr.rdx = 0 →
      (Z'.cpu.gpr.rsp = S + 8#64 ∧ Z'.cpu.gpr.rbx = Z.cpu.gpr.rbx ∧ Z'.cpu.gpr.rbp = Z.cpu.gpr.rbp ∧
        Z'.cpu.gpr.r12 = Z.cpu.gpr.r12 ∧ Z'.cpu.gpr.r13 = Z.cpu.gpr.r13 ∧ Z'.cpu.gpr.r14 = Z.cpu.gpr.r14 ∧
        Z'.cpu.gpr.r15 = Z.cpu.gpr.r15) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  refine c.s_ret hK hA hinS (Sbrk.lt_len hlt) hr hd (fun i hi => ?_) hin (j₂ := 13) (lt_len (by decide)) ?_ ?_
  · rw [hsp]
    exact hl1 i hi
  · rw [hsp]
    exact h13
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hsp] at hg₁
  refine (c_13 prof).run c hin _ hK₁ hA₁ hr₁ (vc_13 (by rw [hg₁]; show Z.cpu.gpr.rax.toNat ≤ _; rw [hax]; exact hb))
    ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₃
  have hsp₂ : Y₂.cpu.gpr.rsp = S := by
    rw [hg₂, hg₁]
    exact u8 S
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_30 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₂]
    exact hl2 i hi
  · rw [hsp₂]
    exact hra
  rintro Z' t' hK' hA' ⟨hr', hg'⟩
  rw [hsp₂] at hg'
  refine k Z' t' hK' hA' hr' ?_ ?_ ?_
  · rw [hg', hg₂, hg₁]
    exact hax
  · rw [hg', hg₂]
    rfl
  · rw [hg', hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `__default_morecore (n)` with the break `b` known and above it new pages to map, the kernel not refusing memory:
the run reaches the return address from a new start with the regions `N` of the new pages and `Base` with the break
`b + n`. There `rax` is `b`, `rdx` is 0, the registers a call keeps are as at the entry, the new pages' bytes are
0, `__curbrk` is `b + n`, and the other bytes are as at the entry but for the 48 below the stack pointer. -/
theorem dmc_next {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L dmc_at dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dmc_at)
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i)) (hlr : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hsp : 0x7a4c40 + 48 ≤ X.cpu.gpr.rsp.toNat) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hn0 : 0 < X.cpu.gpr.rdi.toNat) (hn : X.cpu.gpr.rdi.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hgt : pageUp b.toNat / 4096 < pageUp (b + X.cpu.gpr.rdi).toNat / 4096)
    (hlim : pageUp (b + X.cpu.gpr.rdi).toNat / 4096 ≤ lim)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V₂ s₁ Z t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + X.cpu.gpr.rdi) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = b → Z.cpu.gpr.rdx = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr →
      (∀ a : Addr, pageUp b.toNat / 4096 * 4096 ≤ a.toNat →
        a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096 → V₂ a = 0) →
      (∀ a : Addr, ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧
          a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) →
        ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = V a) →
      rdq(V₂, curbrk) = b + X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  -- the stack is not in the new pages
  have hnew : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) := by
    intro a h1 h2 h
    have h3 : Foot Wl a := stack_out (by omega) hsp8 hst hlr h1 h2
    exact c.foot_below hB (foot_data (c.hws _ h3)) ⟨h.1, by omega⟩
  -- 8 bytes of stack
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hg₁]
  -- `__sbrk (n)`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_8 _) hinS (Sbrk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, b16] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁]; rfl
  have hkp : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ev : ∀ a v, sbrkEv Y₂ a v = sbrkEv X a v := fun a v => by
    simp only [sbrkEv, hg₂, hg₁]
    rfl
  refine Sbrk.sbrk_next c hB hinS hinb hK₂ hA₂ hr₂ hcur hml (fun i hi => ?_) (by rw [hsp₂]; bv_omega) ?_ ?_
    (by rw [hdi₂]; exact hn0) (by rw [hdi₂]; exact hn) hmg (by rw [hdi₂]; exact hgt) (by rw [hdi₂]; exact hlim)
    (by rw [hdi₂]; exact hN) ?_
  · rw [hsp₂]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rw [ev, hdi₂, hsp₂]
  intro g' V₂ s₁ Z t' c' hB' hKz hAz hrz hgz hax hsv hz hfr hq
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsv
  rw [hsp₂] at s1
  have hfr' : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V₂ a = Vst V (X.cpu.gpr.rsp - 16#64) (toBytesLE (dmc_at.add (8 + 5)) 8) a :=
    fun a h1 h2 => hfr a (hnew a (by omega) h2) (by bv_omega) (by omega)
  refine dmc_end (S := X.cpu.gpr.rsp) (b := b) c' hin hinS hKz hAz hrz (by decide) (Sbrk.ret_159 _)
    (by rw [hgz]; exact s1) (by rw [hgz]; exact hax) (by omega) (fun i hi => ?_) (fun i hi => ?_) ?_ hin₂ h₂ ?_ ?_
  · exact c'.hws _ (foot_append_iff.2 (.inr (slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega))))
  · exact c'.hws _ (foot_append_iff.2 (.inr (hlr i hi)))
  · rw [show rdq(V₂, X.cpu.gpr.rsp - 16#64) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [show rdq(V₂, X.cpu.gpr.rsp) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hra
  intro Z' t' hK' hA' hr' hax' hdx' ⟨q1, q2, q3, q4, q5, q6, q7⟩
  rw [hgz] at q2 q3 q4 q5 q6 q7
  refine k V₂ s₁ Z' t' c' hB' hK' hA' hr' hax' hdx' ⟨q1, q2.trans (s2.trans hkp.1), q3.trans (s3.trans hkp.2.1),
    q4.trans (s4.trans hkp.2.2.1), q5.trans (s5.trans hkp.2.2.2.1), q6.trans (s6.trans hkp.2.2.2.2.1),
    q7.trans (s7.trans hkp.2.2.2.2.2)⟩ hz ?_ hq
  intro a h1 h2 h3
  rw [hfr a h1 (by bv_omega) h3, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

/-- `__default_morecore (n)` with the break `b` known and `b + n` ending in the break's page, the kernel not refusing
memory: the run reaches the return address from a new start with the same footprint and `Base` with the break
`b + n`. There `rax` is `b`, `rdx` is 0, the registers a call keeps are as at the entry, `__curbrk` is `b + n`, and
the other bytes are as at the entry but for the 48 below the stack pointer. -/
theorem dmc_same {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L dmc_at dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dmc_at)
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i)) (hlr : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hsp : 0x7a4c40 + 48 ≤ X.cpu.gpr.rsp.toNat) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hn0 : 0 < X.cpu.gpr.rdi.toNat) (hn : X.cpu.gpr.rdi.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (heq : pageUp (b + X.cpu.gpr.rdi).toNat / 4096 = pageUp b.toNat / 4096)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V₂ s₁ Z t', Seg prof F Wl L s₁ o → Base s₁ lim (b + X.cpu.gpr.rdi) fsb ks →
      KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = b → Z.cpu.gpr.rdx = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = V a) →
      rdq(V₂, curbrk) = b + X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  -- 8 bytes of stack
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hg₁]
  -- `__sbrk (n)`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_8 _) hinS (Sbrk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, b16] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁]; rfl
  have hkp : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ev : ∀ a v, sbrkEv Y₂ a v = sbrkEv X a v := fun a v => by
    simp only [sbrkEv, hg₂, hg₁]
    rfl
  refine Sbrk.sbrk_same c hB hinS hinb hK₂ hA₂ hr₂ hcur hml (fun i hi => ?_) (by rw [hsp₂]; bv_omega) ?_ ?_
    (by rw [hdi₂]; exact hn0) (by rw [hdi₂]; exact hn) hmg (by rw [hdi₂]; exact heq) ?_
  · rw [hsp₂]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rw [ev, hdi₂, hsp₂]
  intro g' V₂ s₁ Z t' c' hB' hKz hAz hrz hgz hax hsv hfr hq
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsv
  rw [hsp₂] at s1
  have hfr' : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V₂ a = Vst V (X.cpu.gpr.rsp - 16#64) (toBytesLE (dmc_at.add (8 + 5)) 8) a :=
    fun a h1 h2 => hfr a (by bv_omega) (by omega)
  refine dmc_end (S := X.cpu.gpr.rsp) (b := b) c' hin hinS hKz hAz hrz (by decide) (Sbrk.ret_159 _)
    (by rw [hgz]; exact s1) (by rw [hgz]; exact hax) (by omega) (fun i hi => ?_) (fun i hi => ?_) ?_ hin₂ h₂ ?_ ?_
  · exact c'.hws _ (slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · exact c'.hws _ (hlr i hi)
  · rw [show rdq(V₂, X.cpu.gpr.rsp - 16#64) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [show rdq(V₂, X.cpu.gpr.rsp) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hra
  intro Z' t' hK' hA' hr' hax' hdx' ⟨q1, q2, q3, q4, q5, q6, q7⟩
  rw [hgz] at q2 q3 q4 q5 q6 q7
  refine k V₂ s₁ Z' t' c' hB' hK' hA' hr' hax' hdx' ⟨q1, q2.trans (s2.trans hkp.1), q3.trans (s3.trans hkp.2.1),
    q4.trans (s4.trans hkp.2.2.1), q5.trans (s5.trans hkp.2.2.2.1), q6.trans (s6.trans hkp.2.2.2.2.1),
    q7.trans (s7.trans hkp.2.2.2.2.2)⟩ ?_ hq
  intro a h1 h3
  rw [hfr a (by bv_omega) h3, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

/-- `__default_morecore (0)` with the break `b` known: no system call, the run reaches the return address with `rax`
the break, `rdx` 0, the registers a call keeps as at the entry, the bytes as at the entry but for the 48 below the
stack pointer. -/
theorem dmc_zero {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L dmc_at dmc) (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dmc_at)
    (hcurD : ∀ i < 8, Foot F.data (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i)) (hlr : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hsp : 0x7a4c40 + 48 ≤ X.cpu.gpr.rsp.toNat) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0) (h0 : X.cpu.gpr.rdi = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V₂ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = b → Z.cpu.gpr.rdx = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 48 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  obtain ⟨-, -, hbm0, hlo, -⟩ := c.ready.layout
  have hb0 : b ≠ 0 := fun e => by
    rw [hB.brk, e] at hlo
    have : (0 : Addr).toNat = 0 := rfl
    omega
  -- 8 bytes of stack
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hg₁]
  -- `__sbrk (0)`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_8 _) hinS (Sbrk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, b16] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = 0 := by rw [hg₂, hg₁]; exact h0
  have hkp : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine Sbrk.sbrk_zero (b := b) c hinS hK₂ hA₂ hr₂ hcurD hml (fun i hi => ?_) (by rw [hsp₂]; bv_omega) ?_ hb0 ?_
    hdi₂ ?_
  · rw [hsp₂]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rw [hsp₂]
  intro g' V₂ Z t' hKz hAz hrz hgz hax hsv hfr
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsv
  rw [hsp₂] at s1
  have hfr' : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V₂ a = Vst V (X.cpu.gpr.rsp - 16#64) (toBytesLE (dmc_at.add (8 + 5)) 8) a :=
    fun a h1 h2 => hfr a (by bv_omega)
  refine dmc_end (S := X.cpu.gpr.rsp) (b := b) c hin hinS hKz hAz hrz (by decide) (Sbrk.ret_87 _)
    (by rw [hgz]; exact s1) (by rw [hgz]; exact hax) (by omega) (fun i hi => ?_) (fun i hi => ?_) ?_ hin₂ h₂ ?_ ?_
  · exact c.hws _ (slot hst (k := 32 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · exact c.hws _ (hlr i hi)
  · rw [show rdq(V₂, X.cpu.gpr.rsp - 16#64) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [show rdq(V₂, X.cpu.gpr.rsp) = _ from congrArg (ofBytesLE 64) (rd_eq (n := 8) (by bv_omega)
      fun a h1 h2 => hfr' a (by bv_omega) (by bv_omega)), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hra
  intro Z' t' hK' hA' hr' hax' hdx' ⟨q1, q2, q3, q4, q5, q6, q7⟩
  rw [hgz] at q2 q3 q4 q5 q6 q7
  refine k V₂ Z' t' hK' hA' hr' hax' hdx' ⟨q1, q2.trans (s2.trans hkp.1), q3.trans (s3.trans hkp.2.1),
    q4.trans (s4.trans hkp.2.2.1), q5.trans (s5.trans hkp.2.2.2.1), q6.trans (s6.trans hkp.2.2.2.2.1),
    q7.trans (s7.trans hkp.2.2.2.2.2)⟩ ?_
  intro a h1
  rw [hfr a (by bv_omega), Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

end FV7z.Dmc
