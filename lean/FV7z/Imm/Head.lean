import FV7z.Imm.Mid
/-!
# `_int_malloc`: from the entry to the return address, the first call (PLAN.md G3, `malloc`)

The first call comes from `tcache_init` with 640 bytes asked for (`nb` = 656) and every bin empty.

- `vc_0`, `im_a`: from the entry to offset 2549 (`use_top`): the frame, the bin index 41, the smallbin, the
  tcache, the unsorted bin and `binmap[1..3]` looked at; `Gi`, `Vi`: the registers and bytes there.
- `Vi_out`, `Vi_lo`, `Vi_hi`, `Vi_regs`: the bytes of `Vi` outside the frame, and the six registers read back.
- `im_first`: `im_a` then `im_bc`, from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
namespace FV7z.Imm
variable {F : Footprint} {Wl : List Rgn}

/-! ## Bytes of the frame -/

/-- A read from `S + d1` past a store at `S + d2` apart from it. -/
theorem rd_off {S : Addr} {d1 d2 n : Nat} {bs : List Byte} (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h1 : d1 + n ≤ 256) (h2 : d2 + bs.length ≤ 256) (h : d1 + n ≤ d2 ∨ d2 + bs.length ≤ d1) :
    List.map (Vst V (S + BitVec.ofNat 64 d2) bs) (byteAddrs (S + BitVec.ofNat 64 d1) n) =
      List.map V (byteAddrs (S + BitVec.ofNat 64 d1) n) := by
  have e1 : (S + BitVec.ofNat 64 d1).toNat = S.toNat + d1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (S + BitVec.ofNat 64 d2).toNat = S.toNat + d2 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact rd_Vst _ _ _ _ _ (by omega) (by omega) (by omega)

/-- A read of what was stored at `S + d`. -/
theorem rd_off_self {S : Addr} {d n : Nat} {bs : List Byte} (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h1 : d + n ≤ 256) (hn : bs.length = n) :
    List.map (Vst V (S + BitVec.ofNat 64 d) bs) (byteAddrs (S + BitVec.ofNat 64 d) n) = bs := by
  have e1 : (S + BitVec.ofNat 64 d).toNat = S.toNat + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact rd_Vst_self _ _ _ hn (by omega)

/-- A read below `S` past a store from `S + d`. -/
theorem rd_below {S x : Addr} {n : Nat} (hx : x.toNat + n ≤ S.toNat) (hS : S.toNat + 256 < 2 ^ 64)
    (V : Addr → Byte) (d : Nat) (bs : List Byte) (h2 : d + bs.length ≤ 256) :
    List.map (Vst V (S + BitVec.ofNat 64 d) bs) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have e2 : (S + BitVec.ofNat 64 d).toNat = S.toNat + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact rd_Vst _ _ _ _ _ (by omega) (by omega) (.inr (by omega))

/-- A range from `S + d` inside one from `S`. -/
theorem stk_f {R : List Rgn} {S : Addr} {m : Nat} (h : ∀ i < m, Foot R (Addr.add S i)) {d n : Nat}
    (hd : d + n ≤ m) : ∀ i < n, Foot R ((S + BitVec.ofNat 64 d).add i) := off_ft h d rfl hd

/-- The stack pointers of the six pushes and the `sub`. -/
theorem pu (S : Addr) : S + 184#64 - 8 = S + 176#64 ∧ S + 176#64 - 8 = S + 168#64 ∧
    S + 168#64 - 8 = S + 160#64 ∧ S + 160#64 - 8 = S + 152#64 ∧ S + 152#64 - 8 = S + 144#64 ∧
    S + 144#64 - 8 = S + 136#64 ∧ S + 136#64 - 136#64 = S :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- The bytes at offset 2549 on the first call (`nb` = 656, every bin empty): the six pushes of `rbx`, `rbp`,
`r12`–`r15` and the fourteen frame stores. -/
def Vi (S : Addr) (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (S + 176#64) (toBytesLE g.r15 8)) (S + 168#64) (toBytesLE g.r14 8)) (S + 160#64) (toBytesLE g.r13 8))
    (S + 152#64) (toBytesLE g.r12 8)) (S + 144#64) (toBytesLE g.rbp 8)) (S + 136#64) (toBytesLE g.rbx 8))
    (S + 40#64) (toBytesLE (41#32) 4)) (S + 112#64) (toBytesLE (110#32) 4)) (S + 64#64) (toBytesLE (10#64) 8))
    (S + 80#64) (toBytesLE (1#64) 8)) (S + 116#64) (toBytesLE (92#32) 4)) (S + 76#64) (toBytesLE (58#32) 4))
    (S + 108#64) (toBytesLE (119#32) 4)) (S + 104#64) (toBytesLE (124#32) 4)) (S + 96#64) (toBytesLE (0#64) 8))
    (S + 88#64) (toBytesLE (0#64) 8)) (S + 16#64) (toBytesLE (0#64) 8)) (S + 8#64) (toBytesLE (0#64) 8))
    (S + 72#64) (toBytesLE (41#32) 4)) (S + 32#64) (toBytesLE (640#64) 8)

/-- The registers at offset 2549 on the first call. -/
abbrev Gi (S : Addr) (g : Gprs) : Gprs :=
  ⟨3#64, 42#64, 3#64, 7940672#64, S, 640#64, 0#64, 1#64, 7941408#64, g.r9, 7940768#64, 7940768#64, g.r12, 656#64,
    41#64, 39#64⟩

/-! ## From the entry to offset 2549 -/

/-- From the entry of `_int_malloc` on the first call (`av` the main arena in `rdi`, 640 bytes asked for in `rsi`,
`S` the stack pointer after the frame is made): with `global_max_fast` below 656, smallbin 41, the unsorted bin and
`binmap[1..3]` empty and no tcache yet, the pieces reach offset 2549 (`use_top`) with `Gi` and `Vi`. -/
theorem vc_0 {fb S : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = 640#64) (hdi : g.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : (rdq(V, 8013224#64)).toNat < 656) (hsb : rdq(V, 7941432#64) = 7941408#64)
    (htc : rdq(V, fb + 18446744073709551576#64) = 0#64) (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g' = Gi S g ∧ V' = Vi S g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7941432#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q4 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7942820#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q6 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q7 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have c0 : (640#64 : BitVec 64).msb = false := by decide
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have t1 : ¬ 656 < (rdq(V, 8013224#64)).toNat := by omega
  have t2 : (656#64 : BitVec 64) ≠ rdq(V, 8013224#64) := fun h => by rw [← h] at hgm; exact absurd hgm (by decide)
  wpx [W_0, W_9, W_304, W_320, W_340, W_848, W_86, W_984, W_1069, W_1115, W_1138, W_1968, W_2012, W_2048, W_2480,
    W_2488, W_2505, W_2513, W_2530, o0, o1, o2, o3, o4, o5, o6, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18,
    Op.cmpma, Op.cmpmif, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q4, q5, q6, q7, rd_off, rd_off_self, hS, hS',
    c0, t1, t2, hsb, htc, hun, hm1, hm2, hm3,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  repeat' first
    | apply And.intro
    | intro (_ : Rflags)
    | intro (_ : Rflags.zf _ = false)
    | rfl
    | with_reducible exact stk_f hsw (by decide)
    | with_reducible exact stk_f hsd (by decide)
    | with_reducible exact hgf
    | with_reducible exact htf
    | with_reducible exact D _ _ (by decide) (by decide)

theorem Vi_out (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) {x : Addr}
    (h : x.toNat < S.toNat + 8 ∨ S.toNat + 184 ≤ x.toNat) : Vi S g V x = V x := by
  unfold Vi
  repeat rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)
    (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)]

theorem Vi_lo {S x : Addr} {n : Nat} (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h : x.toNat + n ≤ S.toNat + 8) : List.map (Vi S g V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_eq (by omega) fun _ _ h2 => Vi_out S g V hS (.inl (by omega))

theorem Vi_hi {S x : Addr} {n : Nat} (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h1 : S.toNat + 184 ≤ x.toNat) (h2 : x.toNat + n ≤ 2 ^ 64) :
    List.map (Vi S g V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_eq h2 fun _ h _ => Vi_out S g V hS (.inr (by omega))

theorem Vi_regs (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(Vi S g V, S + 136#64) = g.rbx ∧ rdq(Vi S g V, S + 144#64) = g.rbp ∧ rdq(Vi S g V, S + 152#64) = g.r12 ∧
      rdq(Vi S g V, S + 160#64) = g.r13 ∧ rdq(Vi S g V, S + 168#64) = g.r14 ∧
      rdq(Vi S g V, S + 176#64) = g.r15 := by
  simp only [Vi, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
    Nat.reduceLeDiff, or_true, and_self]

theorem Vi_low {S x : Addr} {n : Nat} (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (hsp : 8029888 ≤ S.toNat) (h : x.toNat + n ≤ 8029888) :
    List.map (Vi S g V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Vi_lo g V hS (by omega)

theorem Vi_ra (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(Vi S g V, S + 184#64) = rdq(V, S + 184#64) :=
  congrArg (ofBytesLE 64) (Vi_hi g V hS (Nat.le_of_eq (add_n _ _ (by omega)).symm)
    (by rw [add_n _ _ (by omega)]; omega))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle}
  {t : Nat} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- The run from the entry of `_int_malloc` to offset 2549 under `vc_0`'s conditions. -/
theorem im_a {fb S : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = 640#64) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : (rdq(V, 8013224#64)).toNat < 656) (hsb : rdq(V, 7941432#64) = 7941408#64)
    (htc : rdq(V, fb + 18446744073709551576#64) = 0#64) (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i))
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vi S X.cpu.gpr V) → Z.cpu.rip = imm_at.add 2549 →
      Z.cpu.gpr = Gi S X.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
    (vc_0 hrsp hsi hdi hS hlo hfb hgm hsb htc hun hm1 hm2 hm3 hW hgf htf hsw hsd) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  exact k Y t₁ hK₁ hA₁ hr₁ hg₁

/-- The 184 bytes from `S` are among the 360 from `S - 168`. -/
theorem stk_in {R : List Rgn} {S : Addr} (h : ∀ i < 360, Foot R (Addr.add (S - 168) i)) :
    ∀ i < 184, Foot R (Addr.add S i) := fun i hi => by
  have e : Addr.add (S - 168) (168 + i) = Addr.add S i := by simp only [Addr.add]; bv_omega
  exact e ▸ h (168 + i) (by omega)

/-- From the entry of `_int_malloc` on the first call to its return address: `im_a`, then `im_bc` with the
initial top. The six registers come back, `rax` is the chunk's memory, the bytes are `Out` of those at offset 2549
(`Vi`). -/
theorem im_first {lim : Nat} {b fsb S : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L imm_at imm) (hinS : CodeIn L Smm.smm_at Smm.smm)
    (hinD : CodeIn L Dmc.dmc_at Dmc.dmc) (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = 640#64) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hsp : 8029888 + 168 ≤ S.toNat) (hS : S.toNat + 256 < 2 ^ 64)
    (hst : ∀ i < 360, Foot Wl (Addr.add (S - 168) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i))
    (hpb : ∀ i < 4, Foot Wl (Addr.add (8013220#64) i))
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fsb + 18446744073709551576#64) i))
    (hfb : (fsb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : (rdq(V, 8013224#64)).toNat < 656) (hs41 : rdq(V, 7941432#64) = 7941408#64)
    (htc : rdq(V, fsb + 18446744073709551576#64) = 0#64) (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : 656 < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8) (hfc : rdd(V, 7940680#64) = 0)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hk0 : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hmx : rdq(V, 7942864#64) = mx) (hms : mx.toNat ≤ sm.toNat) (hsu : sm.toNat < 2 ^ 47)
    (hp0 : rdd(V, 8013220#64) = 0)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad 656#64).toNat / 4096 ≤ lim)
    (hbl : 8029888 ≤ b.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096))
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 16 → Foot (N ++ Wl) a)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (g₁ g₂ : Gprs) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad 656#64 + corr2 b (corr b) (size pad 656#64)) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = b + corr b + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      Out (Vi S X.cpu.gpr V) V' b 656#64 (size pad 656#64) (corr2 b (corr b) (size pad 656#64)) sm
        (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
        (S.toNat - 168) (S.toNat + 32) →
      g₁.rdi = 656#64 → (g₂.rax = b ∧ g₂.r14 = size pad 656#64) →
      (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂]) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hS8 : 8029888 ≤ S.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hsw := stk_in hst
  refine im_a c hB.fsb hin hK hA hrip hrsp hsi hdi hS hS8 hfb hgm hs41 htc hun hm1 hm2 hm3
    (fun a h1 h2 => c.hws _ (hW a h1 h2)) hgf htf hsw (fun i hi => c.hws _ (hsw i hi)) ?_
  intro Z t₁ hK₁ hA₁ hr₁ hg₁
  have T : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 8029888 →
      List.map (Vi S X.cpu.gpr V) (byteAddrs x n) = List.map V (byteAddrs x n) := fun x n h =>
    Vi_low _ _ hS hS8 h
  have e13 : Z.cpu.gpr.r13 = 656#64 := by rw [hg₁]
  have esp : Z.cpu.gpr.rsp = S := by rw [hg₁]
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := Vi_regs S X.cpu.gpr V hS
  refine im_bc (pad := pad) (sm := sm) (mx := mx) (N := N) c hB hin hinS hinD hinK hinb hK₁ hA₁ hr₁
    (by rw [hg₁]) (by rw [esp]; exact hsp) (by rw [esp]; omega) (by rw [esp]; exact hst) hW hhk hcur hml hpb
    (by rw [T _ _ (by decide)]; exact hps) (by rw [e13, T _ _ (by decide)]; exact hthr)
    (by rw [T _ _ (by decide)]; exact htop) (by rw [T _ _ (by decide)]; exact hsz)
    (by rw [T _ _ (by decide)]; exact hpad) (by rw [e13]; exact hnb) (by rw [e13]; decide)
    (by rw [T _ _ (by decide)]; exact hfl) (by rw [T _ _ (by decide)]; exact hfc)
    (by rw [T _ _ (by decide)]; exact hmc) (by rw [T _ _ (by decide)]; exact hcb)
    (by rw [T _ _ (by decide)]; exact hm0) (by rw [T _ _ (by decide)]; exact hk0)
    (by rw [T _ _ (by decide)]; exact hsm) (by rw [T _ _ (by decide)]; exact hsb)
    (by rw [T _ _ (by decide)]; exact hmx) hms hsu (by rw [T _ _ (by decide)]; exact hp0) hmg
    (by rw [e13]; exact hlim) hbl (by rw [e13, esp]; exact hbs) (by rw [e13]; exact hN) (by rw [e13]; exact hh)
    hin₂ h₂ (by rw [esp, Vi_ra _ _ _ hS]; exact hra) ?_
  intro V' g₁ g₂ evs s₁ Z' t' c' hB' hK' hA' hr' hax ⟨y1, y2, y3, y4, y5, y6, y7⟩ hO hg1 hg2 hev
  rw [e13] at hO hB' hg1 hg2
  rw [esp] at hO
  rw [esp] at y1 y2 y3 y4 y5 y6 y7
  exact k V' g₁ g₂ evs s₁ Z' t' c' hB' hK' hA' hr' hax
    ⟨y1, y2.trans R1, y3.trans R2, y4.trans R3, y5.trans R4, y6.trans R5, y7.trans R6⟩ hO hg1 hg2 hev

end FV7z.Imm
