import FV7z.Imm.Top
/-!
# `_int_malloc`: from `use_top` to the return address, the first call (PLAN.md G3, `malloc`)

The three runs one after the other: `im_b` (to the entry of `sysmalloc`), `Smm.sm_ok` (`sysmalloc` with the initial
top), `im_c` (from its return to the return address of `_int_malloc`).

- `Vs`: the bytes at the entry of `sysmalloc`; `Vs_out`, `Vs_ra`: the bytes outside the two stores, the return
  address read back.
- `Out`: the bytes at the return, from those before: the new top and the two size words, the arena's sizes,
  `mp_.sbrk_base`, `__curbrk`; the bytes elsewhere as before, the new pages 0.
- `im_bc`: the run from offset 2549 to the return address, from a new start with the new pages and the new break.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
namespace FV7z.Imm

/-! ## Addresses as numbers -/

theorem sub8 (S : Addr) (h : 8 ≤ S.toNat) : (S - 8).toNat + 8 = S.toNat := by bv_omega
theorem sub160 (S : Addr) (h : 160 ≤ S.toNat) : (S - 160).toNat + 160 = S.toNat := by bv_omega
theorem sub104 (S : Addr) (h : 104 ≤ S.toNat) : (S - 104#64).toNat = S.toNat - 104 := by bv_omega
theorem add_n (S : Addr) (n : Nat) (h : S.toNat + n < 2 ^ 64) : (S + BitVec.ofNat 64 n).toNat = S.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
/-- The new pages' end below the 160 bytes `sysmalloc` stores in (stated apart: `omega` over the run's context
reaches the recursion limit). -/
theorem le_sub {P x z : Nat} (h1 : P + 168 ≤ x) (h2 : z + 8 = x) : P ≤ z - 160 := by omega
theorem e88 (S : Addr) : S - 8 + 8#64 = S := by bv_omega

/-- The address of byte `i` of a range from `S + d`, `S - 8` or `S - 160`, as a number (stated apart: facts on
`toNat` of a sum kept in the run's context make each later `omega` check slowly and with gigabytes in the kernel). -/
theorem at_n (S : Addr) (d i : Nat) (h : S.toNat + d + i < 2 ^ 64) :
    (Addr.add (S + BitVec.ofNat 64 d) i).toNat = S.toNat + d + i := by
  simp only [Addr.add]
  bv_omega
theorem at_s8 (S : Addr) (i : Nat) (h : 8 ≤ S.toNat) (hi : i < 8) : (Addr.add (S - 8) i).toNat + 8 = S.toNat + i := by
  simp only [Addr.add]
  bv_omega
theorem at_s160 (S : Addr) (i : Nat) (h : 160 ≤ S.toNat) (hi : i < 160) :
    (Addr.add (S - 160) i).toNat + 160 = S.toNat + i := by
  simp only [Addr.add]
  bv_omega

/-- Bytes of the range the arena and `mp_` are in. -/
theorem arena {R : List Rgn} (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot R a) (x : Addr)
    (n : Nat) (h1 : 7940480 ≤ x.toNat) (h2 : x.toNat + n ≤ 7943136) : ∀ i < n, Foot R (Addr.add x i) :=
  fun i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)

/-- A byte of the 360 from 168 below the stack pointer at `use_top`: what `sysmalloc` stores in, the return
address, and the frame of `_int_malloc` with the six registers above it. -/
theorem stk {Wl : List Rgn} {S a : Addr} (hst : ∀ i < 360, Foot Wl (Addr.add (S - 168) i)) (hs : 168 ≤ S.toNat)
    (h1 : S.toNat - 168 ≤ a.toNat) (h2 : a.toNat < S.toNat + 192) : Foot Wl a := by
  have e : Addr.add (S - 168) (a.toNat - (S.toNat - 168)) = a := by
    simp only [Addr.add]
    bv_omega
  exact e ▸ hst (a.toNat - (S.toNat - 168)) (by omega)

/-! ## The bytes at the entry of `sysmalloc` -/

/-- The bytes at the entry of `sysmalloc`, from those at `use_top` (`S` the stack pointer there): `r11` in the
frame and the return address below it. -/
abbrev Vs (S r : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst V (S + 24#64) (toBytesLE r 8)) (S - 8) (toBytesLE (imm_at.add (3280 + 5)) 8)

theorem Vs_out (S r : Addr) (V : Addr → Byte) (h1 : 8 ≤ S.toNat) (h2 : S.toNat + 32 ≤ 2 ^ 64) {a : Addr}
    (h : ¬ (S.toNat - 8 ≤ a.toNat ∧ a.toNat < S.toNat))
    (h' : ¬ (S.toNat + 24 ≤ a.toNat ∧ a.toNat < S.toNat + 32)) : Vs S r V a = V a := by
  show Vst (Vst V _ _) _ _ a = _
  rw [Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd)]

/-- The return address `sysmalloc` returns to. -/
theorem Vs_ra (S r : Addr) (V : Addr → Byte) (h1 : 8 ≤ S.toNat) : rdq(Vs S r V, S - 8) = imm_at.add 3285 := by
  show ofBytesLE 64 (List.map (Vst _ _ _) _) = _
  rw [rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]

/-! ## The bytes at the return -/

/-- The bytes `V'` at the return of the first `_int_malloc` from the bytes `V` before it: `b` the break before,
`nb` the chunk's size, `R` the size of the first `MORECORE` and `c` of the second, `sm` the arena's `system_mem`
before, `[lo, hi)` the new pages and `[sl, sh)` the part of the stack the run stores in. The top is what follows the
chunk at the aligned break; `mp_.sbrk_base` is `b` and `__curbrk` the new break; a byte outside those words, the new
pages and that part of the stack is as before, and a byte of the new pages outside the two size words is 0. -/
structure Out (V V' : Addr → Byte) (b nb R c sm : BitVec 64) (lo hi sl sh : Nat) : Prop where
  top : rdq(V', 7940768#64) = b + corr b + nb
  hd : rdq(V', b + corr b + 8#64) = nb ||| 1#64
  tsz : rdq(V', b + corr b + nb + 8#64) =
    ((b + R - (b + corr b) + c ||| 1#64) &&& 18446744073709551608#64) - nb ||| 1#64
  sys : rdq(V', 7942856#64) = sm + R + c
  mxs : rdq(V', 7942864#64) = sm + R + c
  sbb : rdq(V', 7940584#64) = b
  cur : rdq(V', curbrk) = b + R + c
  same : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → ¬ (sl ≤ a.toNat ∧ a.toNat < sh) →
    ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → ¬ (7940584 ≤ a.toNat ∧ a.toNat < 7940592) →
    ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → ¬ (7942856 ≤ a.toNat ∧ a.toNat < 7942872) →
    ¬ ((b + corr b).toNat + 8 ≤ a.toNat ∧ a.toNat < (b + corr b).toNat + 16) →
    ¬ ((b + corr b).toNat + nb.toNat + 8 ≤ a.toNat ∧ a.toNat < (b + corr b).toNat + nb.toNat + 16) → V' a = V a
  zero : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi →
    ¬ ((b + corr b).toNat + 8 ≤ a.toNat ∧ a.toNat < (b + corr b).toNat + 16) →
    ¬ ((b + corr b).toNat + nb.toNat + 8 ≤ a.toNat ∧ a.toNat < (b + corr b).toNat + nb.toNat + 16) → V' a = 0

/-! ## The run -/

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle}
  {t : Nat} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- From offset 2549 (`use_top`) of the first call: `av` the main arena (`rbx`) with the initial top, no fast
chunks, `nb` (`r13`) below `mp_.mmap_threshold`, the conditions of `Smm.sm_ok` on `mp_`, the hooks and the break
`b`, and no `perturb_byte`. The run calls `sysmalloc` and reaches the return address of `_int_malloc` from a new
start with the new pages `N` and `Base` of the new break: `rax` is the chunk's memory `b + corr b + 16`, the frame
is given back, the six registers a call keeps are read from above it, and the bytes are as `Out` says. -/
theorem im_bc {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L imm_at imm) (hinS : CodeIn L Smm.smm_at Smm.smm)
    (hinD : CodeIn L Dmc.dmc_at Dmc.dmc) (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at.add 2549)
    (hbx : X.cpu.gpr.rbx = 7940672#64) (hsp : 8029888 + 168 ≤ X.cpu.gpr.rsp.toNat)
    (hsp2 : X.cpu.gpr.rsp.toNat + 192 < 2 ^ 64)
    (hst : ∀ i < 360, Foot Wl (Addr.add (X.cpu.gpr.rsp - 168) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i))
    (hpb : ∀ i < 4, Foot Wl (Addr.add (8013220#64) i))
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : X.cpu.gpr.r13.toNat < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : X.cpu.gpr.r13.toNat + pad.toNat + 4127 < 2 ^ 47)
    (hn8 : 8 ≤ X.cpu.gpr.r13.toNat)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8) (hfc : rdd(V, 7940680#64) = 0)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hk0 : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hmx : rdq(V, 7942864#64) = mx) (hms : mx.toNat ≤ sm.toNat) (hsu : sm.toNat < 2 ^ 47)
    (hp0 : rdd(V, 8013220#64) = 0)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad X.cpu.gpr.r13).toNat / 4096 ≤ lim)
    (hbl : 8029888 ≤ b.toNat)
    (hbs : (b + size pad X.cpu.gpr.r13).toNat + 4096 + 168 ≤ X.cpu.gpr.rsp.toNat)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096)
      (pageUp (b + size pad X.cpu.gpr.r13).toNat / 4096 * 4096))
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + X.cpu.gpr.r13.toNat + 16 →
      Foot (N ++ Wl) a)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 184#64) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (g₁ g₂ : Gprs) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad X.cpu.gpr.r13 + corr2 b (corr b) (size pad X.cpu.gpr.r13)) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = b + corr b + 16#64 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 192#64 ∧ Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp + 136#64) ∧
        Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 144#64) ∧ Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 152#64) ∧
        Z.cpu.gpr.r13 = rdq(V, X.cpu.gpr.rsp + 160#64) ∧ Z.cpu.gpr.r14 = rdq(V, X.cpu.gpr.rsp + 168#64) ∧
        Z.cpu.gpr.r15 = rdq(V, X.cpu.gpr.rsp + 176#64)) →
      Out V V' b X.cpu.gpr.r13 (size pad X.cpu.gpr.r13) (corr2 b (corr b) (size pad X.cpu.gpr.r13)) sm
        (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad X.cpu.gpr.r13).toNat / 4096 * 4096)
        (X.cpu.gpr.rsp.toNat - 168) (X.cpu.gpr.rsp.toNat + 32) →
      g₁.rdi = X.cpu.gpr.r13 → (g₂.rax = b ∧ g₂.r14 = size pad X.cpu.gpr.r13) →
      (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂]) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hRn : X.cpu.gpr.r13.toNat + 32 ≤ (size pad X.cpu.gpr.r13).toNat ∧
      (size pad X.cpu.gpr.r13).toNat < 2 ^ 47 := by
    rw [Smm.size_toNat hnb]
    omega
  have hbR : (b + size pad X.cpu.gpr.r13).toNat = b.toNat + (size pad X.cpu.gpr.r13).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hc : (corr b).toNat < 16 := by rw [Smm.corr_toNat]; omega
  have hab : (b + corr b).toNat = b.toNat + (corr b).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hlo : 8029888 ≤ pageUp b.toNat / 4096 * 4096 := by unfold pageUp; omega
  have hhi : pageUp (b + size pad X.cpu.gpr.r13).toNat / 4096 * 4096 + 168 ≤ X.cpu.gpr.rsp.toNat := by
    unfold pageUp
    omega
  have fS : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 168 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 192 → Foot Wl a :=
    fun a h1 h2 => stk hst (by omega) h1 h2
  have e776 : (7940768#64 + 8#64 : Addr) = 7940776#64 := by decide
  have z0 : ((0#64 : BitVec 64) &&& 18446744073709551608#64).toNat = 0 := by decide
  -- to the entry of `sysmalloc`
  refine im_b (tp := 7940768#64) (szw := 0#64) (sm := sm) c hB.fsb hin hinS hK hA hrip hbx (by omega) (by omega)
    (fun a h1 h2 => c.hws _ (hW a h1 h2))
    (arena (fun a h1 h2 => c.hws _ (hW a h1 h2)) _ 8 (by decide) (by decide))
    (fun i hi => fS _ (by rw [at_n _ 24 _ (by omega)]; omega) (by rw [at_n _ 24 _ (by omega)]; omega))
    (fun i hi => c.hws _ (fS _ (by rw [Smm.add_nat (by omega)]; omega) (by rw [Smm.add_nat (by omega)]; omega)))
    (fun i hi => fS _ (by have := at_s8 _ i (Nat.le_trans (by decide) hsp) hi; omega)
      (by have := at_s8 _ i (Nat.le_trans (by decide) hsp) hi; omega))
    htop (by rw [e776]; exact hsz) hsm (by rw [z0]; exact Nat.zero_le _)
    (by rw [z0, add_n _ 32 (by omega)]; omega) hfc ?_
  rintro Z t₁ hK₁ hA₁ hr₁ hsi hdi ⟨y1, -, -, -, -, -, -⟩
  have zs : Z.cpu.gpr.rsp.toNat + 8 = X.cpu.gpr.rsp.toNat := by rw [y1]; exact sub8 _ (by omega)
  have hhz := le_sub hhi zs
  have T1 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 8029888 →
      List.map (Vs X.cpu.gpr.rsp X.cpu.gpr.r11 V) (byteAddrs x n) = List.map V (byteAddrs x n) := fun x n hx =>
    rd_eq (by omega) fun a h1 h2 => Vs_out _ _ _ (by omega) (by omega) (by omega) (by omega)
  -- `sysmalloc`
  refine Smm.sm_ok (V := Vs X.cpu.gpr.rsp X.cpu.gpr.r11 V) (pad := pad) (sm := sm) (mx := mx) c hB hinS hinD hinK
    hinb hK₁ hA₁ hr₁ hsi (by omega) (by omega)
    (fun i hi => fS _ (by have := at_s160 _ i (show 160 ≤ Z.cpu.gpr.rsp.toNat by omega) hi; omega)
      (by have := at_s160 _ i (show 160 ≤ Z.cpu.gpr.rsp.toNat by omega) hi; omega))
    (fun i hi => fS _ (by rw [Smm.add_nat (by omega)]; omega) (by rw [Smm.add_nat (by omega)]; omega))
    hW hhk hcur hml (by rw [T1 _ _ (by decide)]; exact hps) (by rw [hdi, T1 _ _ (by decide)]; exact hthr)
    (by rw [T1 _ _ (by decide)]; exact htop) (by rw [T1 _ _ (by decide)]; exact hsz)
    (by rw [T1 _ _ (by decide)]; exact hpad) (by rw [hdi]; exact hnb) (by rw [T1 _ _ (by decide)]; exact hfl)
    (by rw [T1 _ _ (by decide)]; exact hmc) (by rw [T1 _ _ (by decide)]; exact hcb)
    (by rw [T1 _ _ (by decide)]; exact hm0) (by rw [T1 _ _ (by decide)]; exact hk0)
    (by rw [T1 _ _ (by decide)]; exact hsm) (by rw [T1 _ _ (by decide)]; exact hsb)
    (by rw [T1 _ _ (by decide)]; exact hmx) hms hsu hmg (by rw [hdi]; exact hlim) hbl (by rw [hdi]; omega)
    (by rw [hdi]; exact hN) (by rw [hdi]; exact hh) hin (lt_len (j := 3285) (by decide))
    (by rw [y1]; exact Vs_ra _ _ _ (by omega)) ?_
  rintro V₂ V₃ g₂ g₃ evs s₁ Z₂ t₂ c₁ hB₁ hK₂ hA₂ hr₂ hax₂ ⟨u1, -, -, -, -, -, -⟩ ⟨v1, v2, v3⟩
    ⟨w1, w2, w3⟩ hzero hfr₂ hfr₃ hq₃ hev
  rw [hdi] at hB₁ hA₂ v2 w1 w2 w3 hzero hfr₂ hq₃
  have hu : (b + corr b).toNat + g₃.rbp.toNat + 16 ≤ 2 ^ 64 := by rw [w3]; omega
  have rd := Smm.Ve_rd g₃ V₃ (sm + size pad X.cpu.gpr.r13) (b + corr b) (by omega) (by rw [w3]; exact hn8) hu
  rw [w1, w2, w3] at rd
  have br := Smm.sm_brk (gX := Z.cpu.gpr) (g₃ := g₃) (sm' := sm + size pad X.cpu.gpr.r13) (ab := b + corr b)
    (by omega) (by rw [v3]; exact sub104 _ (by omega)) (by omega) hu hfr₃
  have hO : Out V (Smm.Ve g₃ V₃ (sm + size pad X.cpu.gpr.r13) (b + corr b)) b X.cpu.gpr.r13
      (size pad X.cpu.gpr.r13) (corr2 b (corr b) (size pad X.cpu.gpr.r13)) sm (pageUp b.toNat / 4096 * 4096)
      (pageUp (b + size pad X.cpu.gpr.r13).toNat / 4096 * 4096) (X.cpu.gpr.rsp.toNat - 168)
      (X.cpu.gpr.rsp.toNat + 32) :=
    { top := rd.1
      hd := rd.2.1
      tsz := rd.2.2.1
      sys := rd.2.2.2.1
      mxs := rd.2.2.2.2
      sbb := br.1.trans v1
      cur := br.2.trans hq₃
      same := fun a a1 a2 a3 a4 a5 a6 a7 a8 =>
        (Smm.sm_same (gX := Z.cpu.gpr) (V := Vs X.cpu.gpr.rsp X.cpu.gpr.r11 V) (by omega)
          (by rw [v3]; exact sub104 _ (by omega)) hu hfr₂ hfr₃ a1 (by omega) a3 a4 a5 a6 a7
          (by rw [w3]; exact a8)).trans
          (Vs_out _ _ _ (by omega) (by omega) (by omega) (by omega))
      zero := fun a a1 a2 a7 a8 =>
        Smm.sm_zero (gX := Z.cpu.gpr) hlo hhz (by omega) (by rw [v3]; exact sub104 _ (by omega)) hu hzero
          hfr₃ a1 a2 a7 (by rw [w3]; exact a8) }
  generalize Smm.Ve g₃ V₃ (sm + size pad X.cpu.gpr.r13) (b + corr b) = V' at hA₂ hO
  -- from the return of `sysmalloc`
  have r8 : Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [u1, y1]; exact e88 _
  have T : ∀ d : Nat, 32 ≤ d → d + 8 ≤ 192 → rdq(V', X.cpu.gpr.rsp + BitVec.ofNat 64 d) =
      rdq(V, X.cpu.gpr.rsp + BitVec.ofNat 64 d) := fun d h1 h2 =>
    congrArg (ofBytesLE 64) (rd_eq (by rw [add_n _ d (by omega)]; omega) fun a ha1 ha2 => by
      rw [add_n _ d (by omega)] at ha1 ha2
      exact hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  have tp : (8013220#64 : BitVec 64).toNat = 8013220 := rfl
  have hp0' : rdd(V', 8013220#64) = 0 :=
    (congrArg (ofBytesLE 32) (rd_eq (by decide) fun a ha1 ha2 =>
      hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))).trans hp0
  have hnz : b + corr b + 16#64 ≠ 0#64 := fun h => by
    have h' := congrArg BitVec.toNat h
    rw [add_n (b + corr b) 16 (by omega)] at h'
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    omega
  refine im_c (V := V') c₁ hB₁.fsb hin hK₂ hA₂ hr₂ (by rw [hax₂]; exact hnz)
    (fun i hi => c₁.hws _ (foot_append_iff.2 (.inr (hpb i hi)))) hp0'
    (fun i hi => c₁.hws _ (foot_append_iff.2 (.inr (fS _ (by rw [r8, Smm.add_nat (by omega)]; omega)
      (by rw [r8, Smm.add_nat (by omega)]; omega))))) hin₂ h₂
    (by rw [r8, T 184 (by decide) (by decide)]; exact hra) ?_
  rintro Z₃ t₃ hK₃ hA₃ hr₃ hax₃ ⟨q1, q2, q3, q4, q5, q6, q7⟩
  rw [r8] at q1 q2 q3 q4 q5 q6 q7
  exact k V' Z.cpu.gpr g₂ evs s₁ Z₃ t₃ c₁ hB₁ hK₃ hA₃ hr₃ (hax₃.trans hax₂)
    ⟨q1, q2.trans (T 136 (by decide) (by decide)), q3.trans (T 144 (by decide) (by decide)),
      q4.trans (T 152 (by decide) (by decide)), q5.trans (T 160 (by decide) (by decide)),
      q6.trans (T 168 (by decide) (by decide)), q7.trans (T 176 (by decide) (by decide))⟩ hO hdi ⟨v1, v2⟩ hev

end FV7z.Imm
