import FV7z.Smm.PartC
/-!
# `sysmalloc`: the first call, from the entry to the return (PLAN.md G3, `malloc`)

The three runs of `Smm/PartA.lean`, `Smm/PartB.lean` and `Smm/PartC.lean`, one after the other.

- `rd_Va_up`, `Va_fr`, `Va_sv`: reads at and above the entry's stack pointer, of the frame's words and of the
  registers the frame holds, in the bytes at the first call.
- `sm_ok`: `sysmalloc (nb, &main_arena)` with the initial top, from the entry to the return address: `rax` is the
  chunk's memory `b + corr b + 16` (`b` the break at the entry), the registers a call keeps are kept, the break is
  `b + size + corr2`, and the bytes are `Ve` over what the second `MORECORE` left (`V₃`), which is `Vb` over what
  the first left (`V₂`), which is `Va` over the bytes at the entry, each but for the stack below and `__curbrk`.
- `Ve_eq`, `Ve_rd`, `Ve_out`: the bytes at the return as seven stores; the top, the two size words and the
  arena's two sizes read from them; the bytes outside those are the bytes under `Ve`.
- `Va_out`, `Vb_out`, `sm_same`: a byte at the return outside the new pages, the stack below the entry's stack
  pointer, `__curbrk` and the words above is as at the entry.
- `Vb_sb`, `sm_brk`: at the return `mp_.sbrk_base` is the break of the entry, `__curbrk` as the second `MORECORE`
  left it.
- `sm_zero`: the new pages' bytes are 0 at the return, but for the two size words.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
namespace FV7z.Smm

/-! ## Reads in the bytes at the first call -/

/-- A read at or above the entry's stack pointer. -/
theorem rd_Va_up {g : Gprs} {V : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hsp : 104 ≤ g.rsp.toNat) (h : g.rsp.toNat ≤ x.toNat) :
    List.map (Va g V) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  unfold Va
  rw [rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd))]

/-- The frame's first three words: the page mask's complement, the old top's end, the page mask. -/
theorem Va_fr (g : Gprs) (V : Addr → Byte) (hsp : 104 ≤ g.rsp.toNat) :
    rdq(Va g V, g.rsp - 104#64) = 4096#64 + 18446744073709551615#64 ∧
    rdq(Va g V, g.rsp - 104#64 + 8#64) = 7940768#64 ∧
    rdq(Va g V, g.rsp - 104#64 + 16#64) = 0 - 4096#64 := by
  rw [← b104]
  unfold Va
  refine ⟨?_, ?_, ?_⟩
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
      rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]

/-- The frame's addresses from the entry's stack pointer. -/
theorem fl (S : Addr) : S - 8 - 8 = S - 16#64 ∧ S - 16#64 - 8 = S - 24#64 ∧ S - 24#64 - 8 = S - 32#64 ∧
    S - 32#64 - 8 = S - 40#64 ∧ S - 40#64 - 8 = S - 48#64 ∧ S - 48#64 - 56#64 = S - 104#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- The addresses the `pop`s read, from the entry's stack pointer. -/
theorem up (S : Addr) : S - 104#64 + 56#64 = S - 48#64 ∧ S - 104#64 + 56#64 + 8 = S - 40#64 ∧
    S - 104#64 + 56#64 + 8 + 8 = S - 32#64 ∧ S - 104#64 + 56#64 + 8 + 8 + 8 = S - 24#64 ∧
    S - 104#64 + 56#64 + 8 + 8 + 8 + 8 = S - 16#64 ∧ S - 104#64 + 56#64 + 8 + 8 + 8 + 8 + 8 = S - 8 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- One store below the read. -/
local macro "below" : tactic => `(tactic| rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd))])

/-- The six registers the frame holds, where the `pop`s read them. -/
theorem Va_sv (g : Gprs) (V : Addr → Byte) (hsp : 104 ≤ g.rsp.toNat) :
    rdq(Va g V, g.rsp - 104#64 + 56#64) = g.rbx ∧ rdq(Va g V, g.rsp - 104#64 + 56#64 + 8) = g.rbp ∧
    rdq(Va g V, g.rsp - 104#64 + 56#64 + 8 + 8) = g.r12 ∧
    rdq(Va g V, g.rsp - 104#64 + 56#64 + 8 + 8 + 8) = g.r13 ∧
    rdq(Va g V, g.rsp - 104#64 + 56#64 + 8 + 8 + 8 + 8) = g.r14 ∧
    rdq(Va g V, g.rsp - 104#64 + 56#64 + 8 + 8 + 8 + 8 + 8) = g.r15 := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := fl g.rsp
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := up g.rsp
  rw [e5, e4, e3, e2, e1, e0]
  unfold Va
  simp only [q1, q2, q3, q4, q5, q6]
  clear q1 q2 q3 q4 q5 q6 e0 e1 e2 e3 e4 e5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · iterate 5 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · iterate 6 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · iterate 7 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · iterate 8 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · iterate 9 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · iterate 10 below
    rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]

/-- The frame's addresses as numbers. -/
theorem off (S : Addr) (h : 104 ≤ S.toNat) :
    (S - 104#64).toNat = S.toNat - 104 ∧ (S - 104#64 + 8#64).toNat = S.toNat - 96 ∧
    (S - 104#64 + 16#64).toNat = S.toNat - 88 ∧ (S - 104#64 + 56#64).toNat = S.toNat - 48 ∧
    (S - 104#64 + 56#64 + 8).toNat = S.toNat - 40 ∧ (S - 104#64 + 56#64 + 8 + 8).toNat = S.toNat - 32 ∧
    (S - 104#64 + 56#64 + 8 + 8 + 8).toNat = S.toNat - 24 ∧
    (S - 104#64 + 56#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧
    (S - 104#64 + 56#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega⟩

theorem e104 (S : Addr) : S - 104#64 + 104#64 = S := by bv_omega
theorem e112 (S : Addr) : S - 104#64 + 112#64 = S + 8#64 := by bv_omega
theorem sub56 (S : Addr) (h : 56 ≤ S.toNat) : (S - 56).toNat = S.toNat - 56 := by bv_omega
theorem add8 (S : Addr) (h : S.toNat + 8 < 2 ^ 64) : (S + 8#64).toNat = S.toNat + 8 := by bv_omega
theorem add_nat {S : Addr} {i : Nat} (h : S.toNat + i < 2 ^ 64) : (Addr.add S i).toNat = S.toNat + i := by
  simp only [Addr.add]
  bv_omega

/-- `av->system_mem` and the aligned break of the frame, in the bytes at 1644. -/
theorem Vb_rd (g : Gprs) (V : Addr → Byte) (sm : BitVec 64) (h1 : 8029888 ≤ g.rsp.toNat)
    (h2 : g.rsp.toNat + 16 ≤ 2 ^ 64) :
    rdq(Vb g V sm, 7942856#64) = sm + g.r14 ∧ rdq(Vb g V sm, g.rsp + 8#64) = g.rax + corr g.rax := by
  unfold Vb
  refine ⟨?_, ?_⟩
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]

/-! ## The run -/

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `sysmalloc (nb, &main_arena)` from the entry to the return address, with the initial top (of size 0),
`nb` below `mp_.mmap_threshold`, the arena contiguous, no `__after_morecore_hook`, `__morecore` the address of
`__default_morecore`, the break `b` above the program's data and the heap to be below the stack: the break moves to
`b + size + corr2` (one `brk`, and one more unless `b` is a page's start), `rax` is the chunk's memory
`b + corr b + 16`, the registers a call keeps are kept. The bytes at the return are `Ve` over `V₃`, the bytes after
the second `MORECORE`: those are `Vb` over `V₂`, the bytes after the first, which are 0 in the new pages and `Va`
elsewhere; each but for the 56 bytes below the frame and `__curbrk`, which holds the break. -/
theorem sm_ok {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L smm_at smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at)
    (hav : X.cpu.gpr.rsi = 7940672#64) (hsp : 8029888 + 160 ≤ X.cpu.gpr.rsp.toNat)
    (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 160, Foot Wl (Addr.add (X.cpu.gpr.rsp - 160) i))
    (hlr : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i))
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : X.cpu.gpr.rdi.toNat < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : X.cpu.gpr.rdi.toNat + pad.toNat + 4127 < 2 ^ 47)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hmx : rdq(V, 7942864#64) = mx) (hms : mx.toNat ≤ sm.toNat) (hsu : sm.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 ≤ lim)
    (hbl : 8029888 ≤ b.toNat)
    (hbs : (b + size pad X.cpu.gpr.rdi).toNat + 4096 ≤ X.cpu.gpr.rsp.toNat - 160)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096))
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + X.cpu.gpr.rdi.toNat + 16 →
      Foot (N ++ Wl) a)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (V₂ V₃ : Addr → Byte) (g₂ g₃ : Gprs) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad X.cpu.gpr.rdi + corr2 b (corr b) (size pad X.cpu.gpr.rdi)) fsb ks →
      KeptW (N ++ Wl) s₁ Z →
      Agree (withNew F N) Z.proc.mm.mem (Ve g₃ V₃ (sm + size pad X.cpu.gpr.rdi) (b + corr b)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = b + corr b + 16#64 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (g₂.rax = b ∧ g₂.r14 = size pad X.cpu.gpr.rdi ∧ g₂.rsp = X.cpu.gpr.rsp - 104#64) →
      (g₃.rax = b + size pad X.cpu.gpr.rdi ∧ g₃.r14 = corr2 b (corr b) (size pad X.cpu.gpr.rdi) ∧
        g₃.rbp = X.cpu.gpr.rdi) →
      (∀ a : Addr, pageUp b.toNat / 4096 * 4096 ≤ a.toNat →
        a.toNat < pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096 → V₂ a = 0) →
      (∀ a : Addr, ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧
          a.toNat < pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096) →
        ¬ (X.cpu.gpr.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 104) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = Va X.cpu.gpr V a) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 104) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb g₂ V₂ sm a) →
      rdq(V₃, curbrk) = b + size pad X.cpu.gpr.rdi + corr2 b (corr b) (size pad X.cpu.gpr.rdi) →
      (evs = [smEv X.cpu.gpr pad b] ∨ evs = [smEv X.cpu.gpr pad b, smEv2 g₂]) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hsn := size_toNat hnb
  have hR : (size pad X.cpu.gpr.rdi).toNat % 4096 = 0 := by rw [hsn]; omega
  have hR1 : (size pad X.cpu.gpr.rdi).toNat < 2 ^ 47 := by rw [hsn]; omega
  have hRn : X.cpu.gpr.rdi.toNat + 32 ≤ (size pad X.cpu.gpr.rdi).toNat := by rw [hsn]; omega
  have hbR : (b + size pad X.cpu.gpr.rdi).toNat = b.toNat + (size pad X.cpu.gpr.rdi).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hcu : curbrk.toNat = 8014904 := by decide
  have hc := corr_toNat b
  have hab : (b + corr b).toNat = b.toNat + (corr b).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hc2 := corr2_toNat b (corr b) (size pad X.cpu.gpr.rdi) (by omega)
  refine sm_a c hB hin hinD hinS hinb hK hA hrip hav hsp hst (fun a h1 h2 => c.hws _ (hW a h1 h2)) hcur
    (fun i hi => c.hws _ (hml i hi)) hps hthr htop hsz hpad hnb hfl hmc hcb hm0 hmg hlim hN ?_
  intro V₂ s₁ Z t₁ c₁ hB₁ hK₁ hA₁ hr₁ hax₁ _ ⟨z1, z2, z3, z4, z5, z6, z7⟩ hzero hfr₂ hq₂
  obtain ⟨o0, o8, o16, o56, o64, o72, o80, o88, o96⟩ := off X.cpu.gpr.rsp (by omega)
  have zs : Z.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 104 := by rw [z1]; exact o0
  have zl := sub56 Z.cpu.gpr.rsp (by omega)
  have za8 := add8 Z.cpu.gpr.rsp (by omega)
  -- reads after the first `MORECORE`
  have T2 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ 8029888 ∨ X.cpu.gpr.rsp.toNat - 104 ≤ x.toNat) →
      (x.toNat + n ≤ 8014904 ∨ 8014912 ≤ x.toNat) →
      List.map V₂ (byteAddrs x n) = List.map (Va X.cpu.gpr V) (byteAddrs x n) := fun x n hx h1 h3 =>
    rd_eq hx fun a ha1 ha2 => hfr₂ a (by unfold pageUp; omega) (by omega) (by omega)
  have fS : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 160 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot (N ++ Wl) a :=
    fun a h1 h2 => foot_append_iff.2 (.inr (stk hst (by omega) h1 h2))
  have hst₁ : ∀ i < 104, Foot (N ++ Wl) (Addr.add Z.cpu.gpr.rsp i) := fun i hi =>
    fS _ (by rw [add_nat (by omega)]; omega) (by rw [add_nat (by omega)]; omega)
  have hlo₁ : ∀ i < 56, Foot (N ++ Wl) (Addr.add (Z.cpu.gpr.rsp - 56) i) := fun i hi =>
    fS _ (by rw [add_nat (by omega)]; omega) (by rw [add_nat (by omega)]; omega)
  have hW₁ : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot (N ++ Wl) a := fun a h1 h2 =>
    foot_append_iff.2 (.inr (hW a h1 h2))
  have hcur₁ : ∀ i < 8, Foot (N ++ Wl) (curbrk.add i) := fun i hi => foot_append_iff.2 (.inr (hcur i hi))
  have r0 : rdq(V₂, Z.cpu.gpr.rsp) = 4096#64 + 18446744073709551615#64 := by
    rw [z1, T2 _ _ (by omega) (.inr (by omega)) (.inr (by omega))]
    exact (Va_fr X.cpu.gpr V (by omega)).1
  have r1 : rdq(V₂, Z.cpu.gpr.rsp + 8#64) = 7940768#64 := by
    rw [z1, T2 _ _ (by omega) (.inr (by omega)) (.inr (by omega))]
    exact (Va_fr X.cpu.gpr V (by omega)).2.1
  have r2 : rdq(V₂, Z.cpu.gpr.rsp + 16#64) = 0 - 4096#64 := by
    rw [z1, T2 _ _ (by omega) (.inr (by omega)) (.inr (by omega))]
    exact (Va_fr X.cpu.gpr V (by omega)).2.2
  have hk₂ : rdq(V₂, 8013152#64) = 0#64 := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hk
  have hsm₂ : rdq(V₂, 7942856#64) = sm := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hsm
  have hsb₂ : rdq(V₂, 7940584#64) = 0#64 := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hsb
  have hmx₂ : rdq(V₂, 7942864#64) = mx := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hmx
  have hfl₂ : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V₂) &&& 2#8 = 0#8 := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hfl
  have hmc₂ : rdq(V₂, 7942872#64) = Dmc.dmc_at := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hmc
  have hm0₂ : rdd(V₂, 7944640#64) = 0 := by
    rw [T2 _ _ (by decide) (.inl (by decide)) (.inl (by decide)), rd_Va (by decide) (by omega)]
    exact hm0
  -- from the return of the second `MORECORE`
  have tail : ∀ (V₃ : Addr → Byte) (s₂ Z₃ : State) (t₃ : Nat) (evs : List Event),
      Seg prof (withNew F N) (N ++ Wl) L s₂ o →
      Base s₂ lim (b + size pad X.cpu.gpr.rdi + corr2 b (corr b) (size pad X.cpu.gpr.rdi)) fsb ks →
      (evs = [smEv X.cpu.gpr pad b] ∨ evs = [smEv X.cpu.gpr pad b, smEv2 Z.cpu.gpr]) →
      KeptW (N ++ Wl) s₂ Z₃ → Agree (withNew F N) Z₃.proc.mm.mem V₃ → Z₃.cpu.rip = smm_at.add 1690 →
      Z₃.cpu.gpr.rax = b + size pad X.cpu.gpr.rdi →
      (Z₃.cpu.gpr.rsp = Z.cpu.gpr.rsp ∧ Z₃.cpu.gpr.rbx = Z.cpu.gpr.rbx ∧ Z₃.cpu.gpr.rbp = Z.cpu.gpr.rbp ∧
        Z₃.cpu.gpr.r12 = 0#64 ∧ Z₃.cpu.gpr.r13 = Z.cpu.gpr.r13 ∧
        Z₃.cpu.gpr.r14 = corr2 b (corr b) (size pad X.cpu.gpr.rdi) ∧ Z₃.cpu.gpr.r15 = Z.cpu.gpr.r15) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 104) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb Z.cpu.gpr V₂ sm a) →
      rdq(V₃, curbrk) = b + size pad X.cpu.gpr.rdi + corr2 b (corr b) (size pad X.cpu.gpr.rdi) →
      GoG prof L o (gev ++ evs) gP gE Z₃ t₃ := by
    intro V₃ s₂ Z₃ t₃ evs c₂ hB₂ hev hK₃ hA₃ hr₃ hax₃ ⟨w1, w2, w3, w4, w5, w6, w7⟩ hfr₃ hq₃
    have hsp₃ : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 104#64 := w1.trans z1
    have zs₃ : Z₃.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 104 := by rw [w1]; exact zs
    have T3 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
        (x.toNat + n ≤ 8029888 ∨ X.cpu.gpr.rsp.toNat - 104 ≤ x.toNat) →
        (x.toNat + n ≤ 8014904 ∨ 8014912 ≤ x.toNat) →
        List.map V₃ (byteAddrs x n) = List.map (Vb Z.cpu.gpr V₂ sm) (byteAddrs x n) := fun x n hx h1 h3 =>
      rd_eq hx fun a ha1 ha2 => hfr₃ a (by omega) (by omega)
    have D3 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 8029888 → (x.toNat + n ≤ 7940584 ∨ 7940592 ≤ x.toNat) →
        (x.toNat + n ≤ 7942856 ∨ 7942864 ≤ x.toNat) → (x.toNat + n ≤ 8014904 ∨ 8014912 ≤ x.toNat) →
        List.map V₃ (byteAddrs x n) = List.map V₂ (byteAddrs x n) := fun x n hx h1 h2 h3 =>
      (T3 x n (by omega) (.inl hx) h3).trans (rd_Vb (by omega) (by omega) h1 h2 (.inl (by omega)))
    have hk₃ : rdq(V₃, 8013152#64) = 0#64 := by
      rw [D3 _ _ (by decide) (.inr (by decide)) (.inr (by decide)) (.inl (by decide))]
      exact hk₂
    have hmx₃ : rdq(V₃, 7942864#64) = mx := by
      rw [D3 _ _ (by decide) (.inr (by decide)) (.inr (by decide)) (.inl (by decide))]
      exact hmx₂
    have hsm₃ : rdq(V₃, 7942856#64) = sm + Z.cpu.gpr.r14 := by
      rw [T3 _ _ (by decide) (.inl (by decide)) (.inl (by decide))]
      exact (Vb_rd Z.cpu.gpr V₂ sm (by omega) (by omega)).1
    have r1₃ : rdq(V₃, Z₃.cpu.gpr.rsp + 8#64) = Z.cpu.gpr.rax + corr Z.cpu.gpr.rax := by
      rw [w1, T3 _ _ (by omega) (.inr (by omega)) (.inr (by omega))]
      exact (Vb_rd Z.cpu.gpr V₂ sm (by omega) (by omega)).2
    have P : ∀ x : Addr, X.cpu.gpr.rsp.toNat - 48 ≤ x.toNat → x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat + 8 →
        List.map V₃ (byteAddrs x 8) = List.map (Va X.cpu.gpr V) (byteAddrs x 8) := fun x h1 h2 =>
      (T3 x 8 (by omega) (.inr (by omega)) (.inr (by omega))).trans
        ((rd_Vb (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))).trans
          (T2 x 8 (by omega) (.inr (by omega)) (.inr (by omega))))
    have sv := Va_sv X.cpu.gpr V (by omega)
    have p0 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64) = X.cpu.gpr.rbx := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.1
    have p1 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64 + 8) = X.cpu.gpr.rbp := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.2.1
    have p2 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64 + 8 + 8) = X.cpu.gpr.r12 := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.2.2.1
    have p3 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64 + 8 + 8 + 8) = X.cpu.gpr.r13 := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.2.2.2.1
    have p4 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8) = X.cpu.gpr.r14 := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.2.2.2.2.1
    have p5 : rdq(V₃, Z₃.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8 + 8) = X.cpu.gpr.r15 := by
      rw [hsp₃, P _ (by omega) (by omega)]
      exact sv.2.2.2.2.2
    have hra₃ : rdq(V₃, Z₃.cpu.gpr.rsp + 104#64) = e₂.add j₂ := by
      rw [hsp₃, e104, P _ (by omega) (by omega), rd_Va_up (by omega) (by omega) (by omega)]
      exact hra
    have h3n : Z₃.cpu.gpr.rax.toNat = b.toNat + (size pad X.cpu.gpr.rdi).toNat := by rw [hax₃]; exact hbR
    have hsum : (sm + size pad X.cpu.gpr.rdi + corr2 b (corr b) (size pad X.cpu.gpr.rdi)).toNat =
        sm.toNat + (size pad X.cpu.gpr.rdi).toNat + (corr2 b (corr b) (size pad X.cpu.gpr.rdi)).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add]
      omega
    refine sm_c (sm := sm + Z.cpu.gpr.r14) (ab := Z.cpu.gpr.rax + corr Z.cpu.gpr.rax) (mx := mx) c₂ hin hK₃ hA₃ hr₃
      (by omega) (by omega)
      (fun i hi => fS _ (by rw [add_nat (by omega)]; omega) (by rw [add_nat (by omega)]; omega))
      (fun i hi => by
        rw [hsp₃, e104]
        exact c₂.hws _ (foot_append_iff.2 (.inr (hlr i hi))))
      hW₁ (fun i hi => c₂.hws _ (foot_append_iff.2 (.inr (hhk i hi))))
      (by rw [hax₁, w3, z3]; exact hh) (by rw [hax₁, w3, z3]; omega) (by rw [hax₁]; omega)
      (by intro h; rw [h] at h3n; have h0 : (0#64 : BitVec 64).toNat = 0 := rfl; omega) w4 (w2.trans z2) hk₃ hsm₃
      r1₃ hmx₃ (by rw [z6, w6, hsum]; omega)
      (by rw [w7, z7, hax₃, hax₁, w6]; exact top_ok hR hRn (by omega))
      p0 p1 p2 p3 p4 p5 hin₂ h₂ hra₃ ?_
    intro Z₄ t₄ hK₄ hA₄ hr₄ hax₄ ⟨u1, u2, u3, u4, u5, u6, u7⟩
    rw [hax₁, z6] at hA₄
    rw [hax₁] at hax₄
    exact k V₂ V₃ Z.cpu.gpr Z₃.cpu.gpr evs s₂ Z₄ t₄ c₂ hB₂ hK₄ hA₄ hr₄ hax₄
      ⟨u1.trans (by rw [hsp₃]; exact e112 _), u2, u3, u4, u5, u6, u7⟩ ⟨hax₁, z6, z1⟩ ⟨hax₃, w6, w3.trans z3⟩ hzero
      hfr₂ hfr₃ hq₃ hev
  have hhk₁ : ∀ i < 8, Foot (withNew F N).data (Addr.add (8013152#64) i) := fun i hi =>
    c₁.hws _ (foot_append_iff.2 (.inr (hhk i hi)))
  have hml₁ : ∀ i < 4, Foot (withNew F N).data (Addr.add (7944640#64) i) := fun i hi =>
    c₁.hws _ (foot_append_iff.2 (.inr (hml i hi)))
  by_cases hbz : b.toNat % 4096 = 0
  · -- the break a page's start: no second `brk`
    have hz := corr2_zero hbz hR (by omega)
    refine sm_b_z (sm := sm) c₁ hB₁ hin hinD hinS hK₁ hA₁ hr₁ (by rw [hax₁]; exact hbl) (by rw [hax₁]; omega)
      (by rw [z6]; exact hR) (by rw [z6]; exact hR1) (by rw [hax₁]; exact hbz) (by omega) (by omega)
      hst₁ hlo₁ hW₁ hhk₁ hcur₁ hml₁ z4 r0 r1 r2 hk₂ hsm₂ hsb₂ hfl₂ hmc₂ hq₂ hm0₂ ?_
    intro V₃ Z₃ t₃ hK₃ hA₃ hr₃ hax₃ _ ⟨w1, w2, w3, w4, w5, w6, w7⟩ hfr₃
    have e3 : List.map V₃ (byteAddrs curbrk 8) = List.map (Vb Z.cpu.gpr V₂ sm) (byteAddrs curbrk 8) :=
      rd_eq (by decide) fun a h1 h2 => hfr₃ a (by omega)
    refine tail V₃ s₁ Z₃ t₃ _ c₁ (by rw [hz, BitVec.add_zero]; exact hB₁) (.inl rfl) hK₃ hA₃ hr₃ hax₃
      ⟨w1, w2, w3, w4, w5, w6.trans hz.symm, w7⟩ (fun a h1 _ => hfr₃ a (by omega)) ?_
    rw [hz, BitVec.add_zero, e3,
      rd_Vb (by decide) (by omega) (.inr (by decide)) (.inr (by decide)) (.inl (by omega))]
    exact hq₂
  · -- the second `brk`, to the end of the break's page
    refine sm_b_s (sm := sm) c₁ hB₁ hin hinD hinS hinb hK₁ hA₁ hr₁ (by rw [hax₁, z6]) (by rw [hax₁]; exact hbl)
      (by rw [hax₁]; omega) (by rw [z6]; exact hR) (by rw [z6]; exact hR1) (by rw [hax₁]; exact hbz) (by omega)
      (by omega) hst₁ hlo₁ hW₁ hhk₁ hcur₁ hml₁ z4 r0 r1 r2 hk₂ hsm₂ hsb₂ hfl₂ hmc₂ hq₂ hm0₂ hmg ?_
    intro V₃ s₂ Z₃ t₃ c₂ hB₂ hK₃ hA₃ hr₃ hax₃ _ hw hfr₃ hq₃
    rw [hax₁, z6] at hB₂ hw hq₃
    rw [List.append_assoc]
    exact tail V₃ s₂ Z₃ t₃ _ c₂ hB₂ (.inr rfl) hK₃ hA₃ hr₃ hax₃ hw (fun a h1 h3 => hfr₃ a (by omega) h3) hq₃

/-! ## The bytes at the return -/

theorem e8 (ab : BitVec 64) : ab + 16#64 + 18446744073709551608#64 = ab + 8#64 := by bv_omega

/-- The bytes at the return as seven stores: four after the second `MORECORE`, three for the chunk. -/
theorem Ve_eq (g : Gprs) (V : Addr → Byte) (sm ab : BitVec 64) : Ve g V sm ab =
    Vst (Vst (Vst (Vst (Vst (Vst (Vst V (7940768#64) (toBytesLE ab 8)) (ab + 8#64)
      (toBytesLE (g.rax - ab + g.r14 ||| 1#64) 8)) (7942856#64) (toBytesLE (sm + g.r14) 8)) (7942864#64)
      (toBytesLE (sm + g.r14) 8)) (7940768#64) (toBytesLE (ab + g.rbp) 8)) (ab + 8#64)
      (toBytesLE (g.rbp ||| 1#64) 8)) (ab + g.rbp + 8#64)
      (toBytesLE (((g.rax - ab + g.r14 ||| 1#64) &&& 18446744073709551608#64) - g.rbp ||| 1#64) 8) := by
  show Vst (Vst (Vst (Vc g V sm ab) (7940768#64) (toBytesLE (ab + g.rbp) 8))
    (ab + 16#64 + 18446744073709551608#64) (toBytesLE (g.rbp ||| 1#64) 8)) (ab + g.rbp + 8#64)
    (toBytesLE (((g.rax - ab + g.r14 ||| 1#64) &&& 18446744073709551608#64) - g.rbp ||| 1#64) 8) = _
  rw [e8]

/-- The arena and the heap at the return: the top is `ab + nb`, the chunk `ab` has the size `nb` and the bit of a
previous chunk in use, the top's size is what is left of the heap, with the same bit, and `av->system_mem` and
`av->max_system_mem` are the heap's size. -/
theorem Ve_rd (g : Gprs) (V : Addr → Byte) (sm ab : BitVec 64) (hab : 8029888 ≤ ab.toNat)
    (hnb : 8 ≤ g.rbp.toNat) (hu : ab.toNat + g.rbp.toNat + 16 ≤ 2 ^ 64) :
    rdq(Ve g V sm ab, 7940768#64) = ab + g.rbp ∧
    rdq(Ve g V sm ab, ab + 8#64) = g.rbp ||| 1#64 ∧
    rdq(Ve g V sm ab, ab + g.rbp + 8#64) =
      ((g.rax - ab + g.r14 ||| 1#64) &&& 18446744073709551608#64) - g.rbp ||| 1#64 ∧
    rdq(Ve g V sm ab, 7942856#64) = sm + g.r14 ∧ rdq(Ve g V sm ab, 7942864#64) = sm + g.r14 := by
  rw [Ve_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
      rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
      rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
      rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
      rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd)), rd_Vst_self _ _ _ (by sd) (by sd),
      ofBytesLE_toBytesLE (n := 8) rfl]

/-- The bytes at the return outside the top's word, the two size words and the two sizes of the arena: those at
1690. -/
theorem Ve_out (g : Gprs) (V : Addr → Byte) (sm ab : BitVec 64) (hu : ab.toNat + g.rbp.toNat + 16 ≤ 2 ^ 64)
    {a : Addr} (h1 : ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776))
    (h2 : ¬ (ab.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + 16))
    (h3 : ¬ (ab.toNat + g.rbp.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + g.rbp.toNat + 16))
    (h4 : ¬ (7942856 ≤ a.toNat ∧ a.toNat < 7942872)) : Ve g V sm ab a = V a := by
  rw [Ve_eq, Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd)]

/-! ## The bytes the call leaves as they were -/

/-- The bytes at the first call outside the frame: those at the entry. -/
theorem Va_out (g : Gprs) (V : Addr → Byte) (hsp : 104 ≤ g.rsp.toNat) {a : Addr}
    (h : ¬ (g.rsp.toNat - 104 ≤ a.toNat ∧ a.toNat < g.rsp.toNat)) : Va g V a = V a := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := fl g.rsp
  unfold Va
  simp only [q1, q2, q3, q4, q5, q6]
  clear q1 q2 q3 q4 q5 q6
  rw [Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd)]

/-- The bytes at 1644 outside `mp_.sbrk_base`, `av->system_mem` and the frame's second word: those at 900. -/
theorem Vb_out (g : Gprs) (V : Addr → Byte) (sm : BitVec 64) (hsp : g.rsp.toNat + 16 ≤ 2 ^ 64) {a : Addr}
    (h1 : ¬ (7940584 ≤ a.toNat ∧ a.toNat < 7940592)) (h2 : ¬ (7942856 ≤ a.toNat ∧ a.toNat < 7942864))
    (h3 : ¬ (g.rsp.toNat + 8 ≤ a.toNat ∧ a.toNat < g.rsp.toNat + 16)) : Vb g V sm a = V a := by
  unfold Vb
  rw [Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd)]

/-- A byte at the return of `sysmalloc` (`sm_ok`) that is not in the new pages, the 160 bytes below the entry's
stack pointer, `__curbrk`, `mp_.sbrk_base`, `av->top`, the arena's two sizes or the two size words in the heap: as
at the entry. -/
theorem sm_same {gX g₂ g₃ : Gprs} {V V₂ V₃ : Addr → Byte} {sm sm' ab : BitVec 64} {lo hi : Nat}
    (hsp : 160 ≤ gX.rsp.toNat) (h2 : g₂.rsp.toNat = gX.rsp.toNat - 104)
    (hu : ab.toNat + g₃.rbp.toNat + 16 ≤ 2 ^ 64)
    (hfr₂ : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) →
      ¬ (gX.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < gX.rsp.toNat - 104) →
      ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = Va gX V a)
    (hfr₃ : ∀ a : Addr, ¬ (gX.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < gX.rsp.toNat - 104) →
      ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb g₂ V₂ sm a)
    {a : Addr} (a1 : ¬ (lo ≤ a.toNat ∧ a.toNat < hi))
    (a2 : ¬ (gX.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < gX.rsp.toNat))
    (a3 : ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40)) (a4 : ¬ (7940584 ≤ a.toNat ∧ a.toNat < 7940592))
    (a5 : ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776)) (a6 : ¬ (7942856 ≤ a.toNat ∧ a.toNat < 7942872))
    (a7 : ¬ (ab.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + 16))
    (a8 : ¬ (ab.toNat + g₃.rbp.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + g₃.rbp.toNat + 16)) :
    Ve g₃ V₃ sm' ab a = V a := by
  rw [Ve_out g₃ V₃ sm' ab hu a5 a7 a8 a6, hfr₃ a (by omega) a3,
    Vb_out g₂ V₂ sm (by omega) a4 (by omega) (by omega), hfr₂ a a1 (by omega) a3,
    Va_out gX V (by omega) (by omega)]

/-- `mp_.sbrk_base` in the bytes at 1644: the break before the first `MORECORE`. -/
theorem Vb_sb (g : Gprs) (V : Addr → Byte) (sm : BitVec 64) (h1 : 8029888 ≤ g.rsp.toNat)
    (h2 : g.rsp.toNat + 16 ≤ 2 ^ 64) : rdq(Vb g V sm, 7940584#64) = g.rax := by
  unfold Vb
  rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inr (by sd)),
    rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]

/-- At the return of `sysmalloc` (`sm_ok`), `mp_.sbrk_base` is the break of the entry and `__curbrk` is as the
second `MORECORE` left it. -/
theorem sm_brk {gX g₂ g₃ : Gprs} {V₂ V₃ : Addr → Byte} {sm sm' ab : BitVec 64}
    (hsp : 8029888 + 160 ≤ gX.rsp.toNat) (h2 : g₂.rsp.toNat = gX.rsp.toNat - 104)
    (hab : 8029888 ≤ ab.toNat) (hu : ab.toNat + g₃.rbp.toNat + 16 ≤ 2 ^ 64)
    (hfr₃ : ∀ a : Addr, ¬ (gX.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < gX.rsp.toNat - 104) →
      ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb g₂ V₂ sm a) :
    rdq(Ve g₃ V₃ sm' ab, 7940584#64) = g₂.rax ∧ rdq(Ve g₃ V₃ sm' ab, curbrk) = rdq(V₃, curbrk) := by
  have e1 : (7940584#64 : BitVec 64).toNat = 7940584 := rfl
  have e2 : curbrk.toNat = 8014904 := by decide
  refine ⟨?_, ?_⟩
  · rw [rd_eq (V := V₃) (by decide) fun a h1 h2 => Ve_out g₃ V₃ sm' ab hu (by omega) (by omega) (by omega) (by omega),
      rd_eq (V := Vb g₂ V₂ sm) (by decide) fun a h1 h2 => hfr₃ a (by omega) (by omega)]
    exact Vb_sb g₂ V₂ sm (by omega) (by omega)
  · rw [rd_eq (V := V₃) (by decide) fun a h1 h2 => Ve_out g₃ V₃ sm' ab hu (by omega) (by omega) (by omega) (by omega)]

/-- A byte of the new pages at the return of `sysmalloc` (`sm_ok`), outside the two size words: 0. The new pages
(`lo` to `hi`) are above the program's data and below the 160 bytes under the entry's stack pointer. -/
theorem sm_zero {gX g₂ g₃ : Gprs} {V₂ V₃ : Addr → Byte} {sm sm' ab : BitVec 64} {lo hi : Nat}
    (hlo : 8029888 ≤ lo) (hhi : hi ≤ gX.rsp.toNat - 160) (hsp : 160 ≤ gX.rsp.toNat)
    (h2 : g₂.rsp.toNat = gX.rsp.toNat - 104) (hu : ab.toNat + g₃.rbp.toNat + 16 ≤ 2 ^ 64)
    (hzero : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → V₂ a = 0)
    (hfr₃ : ∀ a : Addr, ¬ (gX.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < gX.rsp.toNat - 104) →
      ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb g₂ V₂ sm a)
    {a : Addr} (a1 : lo ≤ a.toNat) (a2 : a.toNat < hi)
    (a7 : ¬ (ab.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + 16))
    (a8 : ¬ (ab.toNat + g₃.rbp.toNat + 8 ≤ a.toNat ∧ a.toNat < ab.toNat + g₃.rbp.toNat + 16)) :
    Ve g₃ V₃ sm' ab a = 0 := by
  rw [Ve_out g₃ V₃ sm' ab hu (by omega) a7 a8 (by omega), hfr₃ a (by omega) (by omega),
    Vb_out g₂ V₂ sm (by omega) (by omega) (by omega) (by omega)]
  exact hzero a a1 a2

end FV7z.Smm
