import FV7z.Sbrk.Holds
import FV7z.Brk.Same
/-!
# `__sbrk` once the break is known (PLAN.md G3, `malloc`)

glibc 2.31's `__sbrk (n)` at `0x666390` in `7zzs`, called with `__curbrk` (`0x7a4c38`) the break `b` and
`__libc_multiple_libcs` (`0x7939c0`) 0, as they are once `__libc_setup_tls` has called `__sbrk` and
`__libc_init_first` has run: no `__brk (0)`; this is `malloc`'s `MORECORE` (`sysmalloc`).

- `ret_87`, `vc_0n`, `vc_36z`: the first `ret`; the prologue with the two words read; the way of `n = 0`.
- `tail_mem`: the bytes after the `__brk`, in terms of those at the entry.
- `sbrk_next`: `0 < n < 2 ^ 47`, the page of `b + n` above the break's and not above the `lim`-th, the kernel not
  refusing memory: `__brk (b + n)`, the run reaches the `ret` (159) from a new start with the regions `N` of the new
  pages and `Base` with the break `b + n`; `rax` is `b`, the new pages' bytes are 0, `__curbrk` is `b + n`.
- `sbrk_same`: likewise with `b + n` ending in the break's page: no new page, the same footprint.
- `sbrk_zero`: `n = 0`: no system call, the run reaches the `ret` (87) with `rax` the break.

The ways not taken: `n` below 0, the overflow of `b + n`, `__brk` failing (`ENOMEM`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Sbrk

theorem w_87 : pret <+: sbk.drop 87 := by decide +kernel
/-- The `ret` of the ways without a second `__brk`. -/
theorem ret_87 (feat : Features) : Dec feat sbk 87 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 87) (k := 0) (pret_0 feat) w_87 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The prologue with `__curbrk` not 0 (`cb`) and `__libc_multiple_libcs` 0: on to the test of the increment. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} {cb : BitVec 64}
    (hc : ∀ i < 8, Foot F.data (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hne : cb ≠ 0)
    (hcq : rdq(Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), 8014904#64) = cb)
    (hm : rdd(Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), 7944640#64) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 36 ∧
      g' = { g with rax := 0, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8#64, r12 := cb } ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 hcq hm
  wpx [W_0, W_26, o0, o1, Op.lda, BitVec.and_self, hm, hcq]
  exact ⟨h1, h2, hc, fun h => absurd (by simpa using h) hne, fun _ => ⟨hml, fun h => absurd h (by decide),
    fun _ => rfl⟩⟩

/-- From the test of the increment, 0: to the first `ret`, the break in `rax`. -/
theorem vc_36z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rbx = 0)
    (h1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_36 F Wl (fun j' g' _ V' => j' = 87 ∧
      g' = { g with rax := g.r12, rbx := rdq(V, g.rsp + 8#64), rsp := g.rsp + 8#64 + 8 + 8,
                    r12 := rdq(V, g.rsp + 8#64 + 8) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rbx = 0 := h0
  dsimp only at h1 h2
  wpx [W_36, W_77, o2, o4, BitVec.and_self]
  intro af
  exact ⟨fun _ => ⟨h1, h2⟩, fun h => absurd h (by decide)⟩

/-- Bytes where two memories are the same. -/
theorem rd_eq {V V' : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → V' a = V a) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ <;> rw [toNat_add_of_fits hj hx] <;> omega

/-- The bytes after `__brk` has stored the break, in terms of those at the entry of `__sbrk`: `W` is the memory
`__brk` was called in but for a range `[lo, hi)` apart from the stack (the new pages, if any). -/
theorem tail_mem (V : Addr → Byte) {W : Addr → Byte} {sp : Addr} {lo hi : Nat} (x1 x2 x5 x6 : BitVec 64)
    (hsp : 0x7a4c40 + 32 ≤ sp.toNat)
    (hW : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) →
      W a = Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8)) (sp - 8 - 8 - 8 - 8)
        (toBytesLE x5 8) a)
    (hout : ∀ a : Addr, sp.toNat - 32 ≤ a.toNat → a.toNat < sp.toNat → ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    (∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → ¬ (sp.toNat - 32 ≤ a.toNat ∧ a.toNat < sp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → Vst W curbrk (toBytesLE x6 8) a = V a) ∧
      rdq(Vst W curbrk (toBytesLE x6 8), sp - 8) = x1 ∧ rdq(Vst W curbrk (toBytesLE x6 8), sp - 8 - 8) = x2 ∧
      rdq(Vst W curbrk (toBytesLE x6 8), sp - 8 - 8 - 8 - 8) = x5 ∧
      rdq(Vst W curbrk (toBytesLE x6 8), curbrk) = x6 := by
  refine ⟨fun a h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [Vst_out, hW a h1, Vst_out, Vst_out, Vst_out]
    all_goals simp only [toBytesLE_length]
    all_goals bv_omega
  · rw [rd_Vst, rd_eq (by bv_omega) fun a h1 h2 => hW a (hout a (by bv_omega) (by bv_omega)), rd_Vst, rd_Vst,
      rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [rd_Vst, rd_eq (by bv_omega) fun a h1 h2 => hW a (hout a (by bv_omega) (by bv_omega)), rd_Vst,
      rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [rd_Vst, rd_eq (by bv_omega) fun a h1 h2 => hW a (hout a (by bv_omega) (by bv_omega)), rd_Vst_self,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  · rw [rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd

theorem add_ge {b n : Addr} (hb : b.toNat ≤ 2 ^ 47 - 4096) (hn : n.toNat < 2 ^ 47) : b.toNat ≤ (b + n).toNat := by
  bv_omega

theorem e32 (S : Addr) : S - 8 - 8 - 8 - 8 = S - 32 := by bv_omega
theorem e2 (S : Addr) : S - 8 - 8 - 8 - 8 + 8 + 8 = S - 8 - 8 := by bv_omega
theorem e3 (S : Addr) : S - 8 - 8 - 8 - 8 + 8 + 8 + 8 = S - 8 := by bv_omega
theorem e0 (S : Addr) : S - 8 + 8 = S := by bv_omega
theorem e1 (S : Addr) : S - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8 = S := by rw [e3, e0]
theorem z1 (S : Addr) : S - 8 - 8 - 8#64 + 8#64 = S - 8 - 8 := by bv_omega
theorem z2 (S : Addr) : S - 8 - 8 - 8#64 + 8#64 + 8 = S - 8 := by bv_omega
theorem z3 (S : Addr) : S - 8 - 8 - 8#64 + 8#64 + 8 + 8 = S := by bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__sbrk (n)` with the break `b` known and above it new pages to map, the kernel not refusing memory: the run
reaches the `ret` (159) from a new start with the regions `N` of the new pages and `Base` with the break `b + n`.
There `rax` is `b`, the registers a call keeps are as at the entry, the new pages' bytes are 0, `__curbrk` is
`b + n`, and the other bytes are as at the entry but for the 32 below the stack pointer. -/
theorem sbrk_next {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L sbk_at sbk) (hinb : CodeIn L Brk.brk_at Brk.brk) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbk_at) (hcur : ∀ i < 8, Foot Wl (curbrk.add i))
    (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i)) (hsp : 0x7a4c40 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hn0 : 0 < X.cpu.gpr.rdi.toNat) (hn : X.cpu.gpr.rdi.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hgt : pageUp b.toNat / 4096 < pageUp (b + X.cpu.gpr.rdi).toNat / 4096)
    (hlim : pageUp (b + X.cpu.gpr.rdi).toNat / 4096 ≤ lim)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096))
    (k : ∀ g' V₂ s₁ Z t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + X.cpu.gpr.rdi) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V₂ → Z.cpu.rip = sbk_at.add 159 → Z.cpu.gpr = g' →
      g'.rax = b → Saved X.cpu.gpr g' →
      (∀ a : Addr, pageUp b.toNat / 4096 * 4096 ≤ a.toNat →
        a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096 → V₂ a = 0) →
      (∀ a : Addr, ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧
          a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) →
        ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = V a) →
      rdq(V₂, curbrk) = b + X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hle := hB.le
  have hcurD : ∀ i < 8, Foot F.data (curbrk.add i) := fun i hi => c.hws _ (hcur i hi)
  obtain ⟨-, -, hbm0, hlo, -⟩ := c.ready.layout
  have hb0 : b ≠ 0 := fun e => by
    rw [hB.brk, e] at hlo
    have : (0 : Addr).toNat = 0 := rfl
    omega
  -- the bytes below the stack pointer and `__curbrk` are not in the new pages
  have hout : ∀ k < 32, ¬ (pageUp b.toNat / 4096 * 4096 ≤ (Addr.add (X.cpu.gpr.rsp - 32) k).toNat ∧
      (Addr.add (X.cpu.gpr.rsp - 32) k).toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) :=
    fun k hk h => c.foot_below hB (foot_data (c.hws _ (hst k hk))) ⟨h.1, by omega⟩
  have hcbo : ∀ a : Addr, 0x7a4c38 ≤ a.toNat → a.toNat < 0x7a4c40 →
      ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) := by
    intro a h1 h2 h
    have e : curbrk.add (a.toNat - 0x7a4c38) = a := by simp only [Addr.add]; bv_omega
    have h3 := c.foot_below hB (foot_data (hcurD (a.toNat - 0x7a4c38) (by omega)))
    rw [e] at h3
    exact h3 ⟨h.1, by omega⟩
  have hout' : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat →
      ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) := by
    intro a h1 h2
    have e : Addr.add (X.cpu.gpr.rsp - 32) (a.toNat - (X.cpu.gpr.rsp.toNat - 32)) = a := by
      simp only [Addr.add]
      bv_omega
    have h3 := hout (a.toNat - (X.cpu.gpr.rsp.toNat - 32)) (by omega)
    rw [e] at h3
    exact h3
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0n (cb := b) hcurD hml (fun i hi => slot hst (k := 24 + i) (by omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => slot hst (k := 16 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hb0 ?_ ?_) ?_
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hbx₁ : Y₁.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg₁]
  have h12₁ : Y₁.cpu.gpr.r12 = b := by rw [hg₁]
  refine (c_36 prof).run c hin _ hK₁ hA₁ hr₁
    (vc_36 (by rw [hbx₁]; exact hn0) (by rw [hbx₁]; exact hn) (by rw [h12₁]; omega)) ?_
  rintro j' g fl V₇ ⟨rfl, ⟨ax, rfl⟩, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [h12₁, hbx₁] at hg₇
  have hsp₇ : Y₇.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hg₇, hg₁]; rfl
  -- `__brk (b + n)`
  refine c.s_call hK₇ hA₇ hin (lt_len (by decide)) hr₇ (call_140 _) hinb (Brk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₇]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [hsp₇] at hA₈ hg₈
  have hdi₈ : Y₈.cpu.gpr.rdi = b + X.cpu.gpr.rdi := by rw [hg₈, hg₇]; rfl
  have e₈ : Brk.brkEv Y₈ Y₈.cpu.gpr.rdi = sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi) := by
    simp only [Brk.brkEv, sbrkEv, hg₈, hg₇, hg₁]
    rfl
  refine Brk.brk_grow c hB hinb hK₈ hA₈ hr₈ hcur hmg (by rw [hdi₈]; exact hgt) (by rw [hdi₈]; exact hlim)
    (by rw [hdi₈]; exact hN) ?_
  rw [e₈, hdi₈]
  intro rc' r11' s₁ Y₉ t₉ c' hB' hK₉ hA₉ hr₉ hg₉
  obtain ⟨fr, q1, q2, q5, q6⟩ := tail_mem V (W := Vz _ (pageUp b.toNat / 4096 * 4096)
    (pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096)) X.cpu.gpr.r12 X.cpu.gpr.rbx (sbk_at.add (140 + 5))
    (b + X.cpu.gpr.rdi) hsp (fun a h => Vz_out h) hout'
  have h12₉ : Y₉.cpu.gpr.r12 = b := by rw [hg₉, hg₈, hg₇]; exact h12₁
  have hkeep : Y₉.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₉.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₉.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₉.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₉, hg₈, hg₇, hg₁]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine sbrk_end c' hin hinb hK₉ hA₉ hr₉ (q := X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (by rw [hg₉, hg₈]; rfl)
    (fun i hi => ?_) q5 (by rw [hg₉]; rfl) ?_
  · rw [e32]
    exact c'.hws _ (foot_append_iff.2 (.inr (hst i hi)))
  intro Z t' hKz hAz hrz hgz
  rw [e1, e3, e2, q1, q2] at hgz
  refine k _ _ s₁ Z t' c' hB' hKz hAz hrz hgz h12₉ ⟨rfl, rfl, hkeep.1, rfl, hkeep.2.1, hkeep.2.2.1, hkeep.2.2.2⟩ ?_
    fr q6
  intro a h1 h2
  refine zero_new _ _ h1 h2 ?_
  by_cases h : 0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40
  · exact absurd ⟨h1, h2⟩ (hcbo a h.1 h.2)
  · omega

/-- `__sbrk (n)` with the break `b` known and `b + n` ending in the break's page, the kernel not refusing memory:
the run reaches the `ret` (159) from a new start with the same footprint and `Base` with the break `b + n`. There
`rax` is `b`, the registers a call keeps are as at the entry, `__curbrk` is `b + n`, and the other bytes are as at
the entry but for the 32 below the stack pointer. -/
theorem sbrk_same {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L sbk_at sbk) (hinb : CodeIn L Brk.brk_at Brk.brk) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbk_at) (hcur : ∀ i < 8, Foot Wl (curbrk.add i))
    (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i)) (hsp : 0x7a4c40 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hn0 : 0 < X.cpu.gpr.rdi.toNat) (hn : X.cpu.gpr.rdi.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (heq : pageUp (b + X.cpu.gpr.rdi).toNat / 4096 = pageUp b.toNat / 4096)
    (k : ∀ g' V₂ s₁ Z t', Seg prof F Wl L s₁ o → Base s₁ lim (b + X.cpu.gpr.rdi) fsb ks →
      KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = sbk_at.add 159 → Z.cpu.gpr = g' →
      g'.rax = b → Saved X.cpu.gpr g' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = V a) →
      rdq(V₂, curbrk) = b + X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hge := add_ge hbt hn
  have hcurD : ∀ i < 8, Foot F.data (curbrk.add i) := fun i hi => c.hws _ (hcur i hi)
  obtain ⟨-, -, hbm0, hlo, -⟩ := c.ready.layout
  have hb0 : b ≠ 0 := fun e => by
    rw [hB.brk, e] at hlo
    have : (0 : Addr).toNat = 0 := rfl
    omega
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0n (cb := b) hcurD hml (fun i hi => slot hst (k := 24 + i) (by omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => slot hst (k := 16 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hb0 ?_ ?_) ?_
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hbx₁ : Y₁.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg₁]
  have h12₁ : Y₁.cpu.gpr.r12 = b := by rw [hg₁]
  refine (c_36 prof).run c hin _ hK₁ hA₁ hr₁
    (vc_36 (by rw [hbx₁]; exact hn0) (by rw [hbx₁]; exact hn) (by rw [h12₁]; omega)) ?_
  rintro j' g fl V₇ ⟨rfl, ⟨ax, rfl⟩, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [h12₁, hbx₁] at hg₇
  have hsp₇ : Y₇.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hg₇, hg₁]; rfl
  -- `__brk (b + n)`
  refine c.s_call hK₇ hA₇ hin (lt_len (by decide)) hr₇ (call_140 _) hinb (Brk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₇]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [hsp₇] at hA₈ hg₈
  have hdi₈ : Y₈.cpu.gpr.rdi = b + X.cpu.gpr.rdi := by rw [hg₈, hg₇]; rfl
  have e₈ : Brk.brkEv Y₈ Y₈.cpu.gpr.rdi = sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi) := by
    simp only [Brk.brkEv, sbrkEv, hg₈, hg₇, hg₁]
    rfl
  refine Brk.brk_same c hB hinb hK₈ hA₈ hr₈ hcur hmg (by rw [hdi₈]; exact hge) (by rw [hdi₈]; exact heq) ?_
  rw [e₈, hdi₈]
  intro rc' r11' s₁ Y₉ t₉ c' hB' hK₉ hA₉ hr₉ hg₉
  obtain ⟨fr, q1, q2, q5, q6⟩ := tail_mem V (lo := 0) (hi := 0) X.cpu.gpr.r12 X.cpu.gpr.rbx (sbk_at.add (140 + 5))
    (b + X.cpu.gpr.rdi) hsp (fun a _ => rfl) (fun a _ _ h => by omega)
  have h12₉ : Y₉.cpu.gpr.r12 = b := by rw [hg₉, hg₈, hg₇]; exact h12₁
  have hkeep : Y₉.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₉.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₉.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₉.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₉, hg₈, hg₇, hg₁]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine sbrk_end c' hin hinb hK₉ hA₉ hr₉ (q := X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (by rw [hg₉, hg₈]; rfl)
    (fun i hi => ?_) q5 (by rw [hg₉]; rfl) ?_
  · rw [e32]
    exact c'.hws _ (hst i hi)
  intro Z t' hKz hAz hrz hgz
  rw [e1, e3, e2, q1, q2] at hgz
  exact k _ _ s₁ Z t' c' hB' hKz hAz hrz hgz h12₉ ⟨rfl, rfl, hkeep.1, rfl, hkeep.2.1, hkeep.2.2.1, hkeep.2.2.2⟩
    (fun a h2 h3 => fr a (by omega) h2 h3) q6

/-- `__sbrk (0)` with the break `b` known: no system call, the run reaches the first `ret` (87) with `rax` the
break, the registers a call keeps as at the entry, the bytes as at the entry but for 16 below the stack pointer. -/
theorem sbrk_zero {b : Addr} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sbk_at sbk) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbk_at) (hcurD : ∀ i < 8, Foot F.data (curbrk.add i))
    (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i)) (hsp : 0x7a4c40 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (hcb : rdq(V, curbrk) = b) (hb0 : b ≠ 0) (hm0 : rdd(V, 7944640#64) = 0) (h0 : X.cpu.gpr.rdi = 0)
    (k : ∀ g' V₂ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = sbk_at.add 87 → Z.cpu.gpr = g' →
      g'.rax = b → Saved X.cpu.gpr g' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0n (cb := b) hcurD hml (fun i hi => slot hst (k := 24 + i) (by omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => slot hst (k := 16 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hb0 ?_ ?_) ?_
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd)]
    exact hm0
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hg₁]
  have h12₁ : Y₁.cpu.gpr.r12 = b := by rw [hg₁]
  have hkeep : Y₁.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₁.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₁.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₁]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine (c_36 prof).run c hin _ hK₁ hA₁ hr₁ (vc_36z (by rw [hg₁]; exact h0) (fun i hi => ?_) (fun i hi => ?_)) ?_
  · rw [hsp₁, z1]
    exact c.hws _ (slot hst (k := 16 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  · rw [hsp₁, z2]
    exact c.hws _ (slot hst (k := 24 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine k _ _ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ h12₁ ⟨?_, ?_, hkeep.1, ?_, hkeep.2.1, hkeep.2.2.1, hkeep.2.2.2⟩ ?_
  · show Y₁.cpu.gpr.rsp + 8#64 + 8 + 8 = _
    rw [hsp₁]
    exact z3 _
  · show rdq(_, Y₁.cpu.gpr.rsp + 8#64) = _
    rw [hsp₁, z1, rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · show rdq(_, Y₁.cpu.gpr.rsp + 8#64 + 8) = _
    rw [hsp₁, z2, rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · intro a ha
    rw [Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega),
      Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

end FV7z.Sbrk
