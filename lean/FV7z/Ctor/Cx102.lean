import FV7z.Ctor.Cx98
import FV7z.Ctor.BlkRet
/-!
# Constructor 102: a 72704-byte buffer from `malloc` (PLAN.md §M, constructors)

`csuTg 102` (`0x41ce70`): `endbr64; sub rsp, 8; pxor xmm0, xmm0; mov edi, 0x11c00; mov qword [0x7a31a0], 0;
mov qword [0x7a31b8], 0x11c00; movaps [0x7a3180], xmm0; movaps [0x7a3190], xmm0; call malloc; mov [0x7a31b0], rax;
test rax, rax; je F; mov [0x7a31a8], rax; mov qword [rax], 0x11c00; mov qword [rax + 8], 0; add rsp, 8; ret`. The
failure branch `F` is not taken: `malloc` returns a chunk of the heap (`Mal.mal_hp` for 72704).

- `st3384`, `st102`: the bytes after the stores before the `call` (the two `movaps` store bytes we do not track) and
  after those past it; what they keep and read back.
- `c102_runs`, `c102_jg`: `csuTg 102` as `Csu.csu_ok` asks, and for `Jg` (its spec `wrSpec c102Wr`, the shared words
  `c102Sh hi`: those `malloc` reads, in the spec of `k₀`).
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## Bytes and registers -/

theorem e296 (sp : Addr) (h : 296 ≤ sp.toNat) : (sp - 80#64 - 216#64).toNat = sp.toNat - 296 := by bv_omega
theorem e80a (sp : Addr) : sp - 80#64 + 8 = sp - 72#64 := by bv_omega
theorem sw72704 : (BitVec.ofNat 32 72704).setWidth 64 = 72704#64 := by decide

theorem ea0 (g : Gprs) : eaG g (some 0) none 1 0 = g.rax := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  simp only [eaG, optV, gk0]
  bv_omega

theorem ea8 (g : Gprs) : eaG g (some 0) none 1 8 = g.rax + 8#64 := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  simp only [eaG, optV, gk0]
  bv_omega

/-- A byte outside a store at the fixed address `A`. -/
theorem vo_at {V : Addr → Byte} {A n : Nat} {bs : List Byte} {x : Addr} (hn : bs.length = n) (hA : A + n < 2 ^ 64)
    (h : x.toNat < A ∨ A + n ≤ x.toNat) : Vst V (BitVec.ofNat 64 A) bs x = V x := by
  have e : (BitVec.ofNat 64 A).toNat = A := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact Sga.vo hn (by rw [e]; omega) (by rw [e]; exact h)

/-- A quad word read back from its store. -/
theorem rdq_self (V : Addr → Byte) (x v : Addr) (hx : x.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst V x (toBytesLE v (64 / 8)), x) = v := by
  rw [Tun.rd_Vst_self (n := 8) _ x _ (toBytesLE_length _ _) hx]
  exact ofBytesLE_toBytesLE (n := 64 / 8) rfl _

/-- The bytes after the stores before the `call`: `[0x7a31a0] = 0`, `[0x7a31b8] = 0x11c00`, any 32 bytes from
`0x7a3180`. -/
def st3384 (V : Addr → Byte) (bs bs' : List Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (BitVec.ofNat 64 8008096) (toBytesLE (BitVec.ofNat 64 0) (64 / 8))) (BitVec.ofNat 64 8008120)
    (toBytesLE (BitVec.ofNat 64 72704) (64 / 8))) (BitVec.ofNat 64 8008064) bs) (BitVec.ofNat 64 8008080) bs'

theorem st3384_out (V : Addr → Byte) {bs bs' : List Byte} (hb : bs.length = 16) (hb' : bs'.length = 16) {a : Addr}
    (h : ¬ (8008064 ≤ a.toNat ∧ a.toNat < 8008128)) : st3384 V bs bs' a = V a := by
  unfold st3384
  rw [vo_at hb' (by omega) (by omega), vo_at hb (by omega) (by omega),
    vo_at (toBytesLE_length _ _) (by omega) (by omega),
    vo_at (toBytesLE_length _ _) (by omega) (by omega)]

theorem st3384_r2 (V : Addr → Byte) {bs bs' : List Byte} (hb : bs.length = 16) (hb' : bs'.length = 16) :
    rdq(st3384 V bs bs', 8008096#64) = 0#64 := by
  have e : (8008096#64 : Addr).toNat = 8008096 := rfl
  refine Eq.trans (rdq_eq (V := Vst V (BitVec.ofNat 64 8008096) (toBytesLE (BitVec.ofNat 64 0) (64 / 8)))
    (by rw [e]; omega) fun a h1 h2 => ?_) (rdq_self _ _ _ (by rw [e]; omega))
  rw [e] at h1 h2
  unfold st3384
  rw [vo_at hb' (by omega) (by omega), vo_at hb (by omega) (by omega),
    vo_at (toBytesLE_length _ _) (by omega) (by omega)]

theorem st3384_r5 (V : Addr → Byte) {bs bs' : List Byte} (hb : bs.length = 16) (hb' : bs'.length = 16) :
    rdq(st3384 V bs bs', 8008120#64) = 72704#64 := by
  have e : (8008120#64 : Addr).toNat = 8008120 := rfl
  refine Eq.trans (rdq_eq (V := Vst (Vst V (BitVec.ofNat 64 8008096) (toBytesLE (BitVec.ofNat 64 0) (64 / 8)))
    (BitVec.ofNat 64 8008120) (toBytesLE (BitVec.ofNat 64 72704) (64 / 8))) (by rw [e]; omega) fun a h1 h2 => ?_)
    (rdq_self _ _ _ (by rw [e]; omega))
  rw [e] at h1 h2
  unfold st3384
  rw [vo_at hb' (by omega) (by omega), vo_at hb (by omega) (by omega)]

/-- The bytes after the stores past the `call`: `[0x7a31b0] = p`, `[0x7a31a8] = p`, `[p] = 0x11c00`, `[p + 8] = 0`. -/
def st102 (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8))) (BitVec.ofNat 64 8008104)
    (toBytesLE p (64 / 8))) p (toBytesLE (BitVec.ofNat 64 72704) (64 / 8))) (p + 8#64)
    (toBytesLE (BitVec.ofNat 64 0) (64 / 8))

theorem st102_out (V : Addr → Byte) {p a : Addr} (hp : p.toNat + 16 < 2 ^ 64)
    (h1 : ¬ (8008104 ≤ a.toNat ∧ a.toNat < 8008120)) (h2 : a.toNat < p.toNat ∨ p.toNat + 16 ≤ a.toNat) :
    st102 V p a = V a := by
  have ep8 := Nst.o8 p hp
  unfold st102
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, ep8]; omega) (by rw [toBytesLE_length, ep8]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    vo_at (toBytesLE_length _ _) (by omega) (by omega), vo_at (toBytesLE_length _ _) (by omega) (by omega)]

theorem st102_r4 (V : Addr → Byte) {p : Addr} (hp1 : 8008128 ≤ p.toNat) (hp : p.toNat + 16 < 2 ^ 64) :
    rdq(st102 V p, 8008112#64) = p := by
  have ep8 := Nst.o8 p hp
  have e : (8008112#64 : Addr).toNat = 8008112 := rfl
  refine Eq.trans (rdq_eq (V := Vst V (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8))) (by rw [e]; omega)
    fun a h1 h2 => ?_) (rdq_self _ _ _ (by rw [e]; omega))
  rw [e] at h1 h2
  unfold st102
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, ep8]; omega) (by rw [toBytesLE_length, ep8]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    vo_at (toBytesLE_length _ _) (by omega) (by omega)]

theorem st102_r3 (V : Addr → Byte) {p : Addr} (hp1 : 8008128 ≤ p.toNat) (hp : p.toNat + 16 < 2 ^ 64) :
    rdq(st102 V p, 8008104#64) = p := by
  have ep8 := Nst.o8 p hp
  have e : (8008104#64 : Addr).toNat = 8008104 := rfl
  refine Eq.trans (rdq_eq (V := Vst (Vst V (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8))) (BitVec.ofNat 64 8008104)
    (toBytesLE p (64 / 8))) (by rw [e]; omega) fun a h1 h2 => ?_) (rdq_self _ _ _ (by rw [e]; omega))
  rw [e] at h1 h2
  unfold st102
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, ep8]; omega) (by rw [toBytesLE_length, ep8]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]

theorem st102_rp (V : Addr → Byte) {p : Addr} (hp : p.toNat + 16 < 2 ^ 64) : rdq(st102 V p, p) = 72704#64 := by
  have ep8 := Nst.o8 p hp
  refine Eq.trans (rdq_eq (V := Vst (Vst (Vst V (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8)))
    (BitVec.ofNat 64 8008104) (toBytesLE p (64 / 8))) p (toBytesLE (BitVec.ofNat 64 72704) (64 / 8))) (by omega)
    fun a h1 h2 => ?_) (rdq_self _ _ _ (by omega))
  unfold st102
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, ep8]; omega) (by rw [toBytesLE_length, ep8]; omega)]

theorem st102_rp8 (V : Addr → Byte) {p : Addr} (hp : p.toNat + 16 < 2 ^ 64) : rdq(st102 V p, p + 8#64) = 0#64 := by
  have ep8 := Nst.o8 p hp
  exact rdq_self _ _ _ (by rw [ep8]; omega)

/-- The bounds of the buffer `p` (standalone: `omega` in the proof's context reaches the recursion limit). -/
theorem pbd {p h s : Nat} (hpn : p + 72704 ≤ h) (hhs : h + 1024 ≤ s) (hs : s < 2 ^ 64) (h1 : 8032256 + 16 ≤ p) :
    p + 16 < 2 ^ 64 ∧ p + 72704 ≤ 2 ^ 64 ∧ 8008128 ≤ p := by omega

/-- A word at `b` (8008096 or 8008120) is outside `[8008104, 8008120)` and below the buffer `q`. -/
theorem rq_side {b x q : Nat} (hb : b = 8008096 ∨ b = 8008120) (h1 : b ≤ x) (h2 : x < b + 8)
    (hq : 8032256 + 16 ≤ q) : ¬ (8008104 ≤ x ∧ x < 8008120) ∧ 7940776 ≤ x ∧ x + 8 < q := by omega

/-- The words of `[0x7a3180, 0x7a31c0)` the stores write, from the footprint of the whole interval. -/
theorem fwg {Wl : List Rgn} (h : ∀ i < 64, Foot Wl (Addr.add (BitVec.ofNat 64 8008064) i)) {x n : Nat}
    (h1 : 8008064 ≤ x) (h2 : x + n ≤ 8008128) : ∀ i < n, Foot Wl (Addr.add (BitVec.ofNat 64 x) i) :=
  ft_in h h1 (by omega) (by omega)

/-! ## `csuTg 102` -/

/-- `csuTg 102`, at `0x41ce70`, to the `ret`. -/
def c3376 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x66, 0x0f, 0xef, 0xc0, 0xbf, 0x00, 0x1c, 0x01,
  0x00, 0x48, 0xc7, 0x05, 0x14, 0x63, 0x38, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x05, 0x21,
  0x63, 0x38, 0x00, 0x00, 0x1c, 0x01, 0x00, 0x0f, 0x29, 0x05, 0xe2, 0x62, 0x38, 0x00, 0x0f, 0x29,
  0x05, 0xeb, 0x62, 0x38, 0x00, 0xe8, 0xb6, 0x62, 0x21, 0x00, 0x48, 0x89, 0x05, 0xff, 0x62, 0x38,
  0x00, 0x48, 0x85, 0xc0, 0x74, 0x1b, 0x48, 0x89, 0x05, 0xeb, 0x62, 0x38, 0x00, 0x48, 0xc7, 0x00,
  0x00, 0x1c, 0x01, 0x00, 0x48, 0xc7, 0x40, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x08,
  0xc3]
theorem c3376_0 : ∀ feat, Dec feat c3376 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c3376_4 : ∀ feat, Dec feat c3376 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3376_8 : ∀ feat, Dec feat c3376 8 (FV7z.mk (.sse (SseMn.pxor)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem c3376_12 : ∀ feat, Dec feat c3376 12 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 72704)] 5) := by dec_rfl
theorem c3376_17 : ∀ feat, Dec feat c3376 17 (FV7z.mk .mov 64 [.mem (mrip 3695380 64), .imm 64 0] 11) := by dec_rfl
theorem c3376_28 : ∀ feat, Dec feat c3376 28 (FV7z.mk .mov 64 [.mem (mrip 3695393 64), .imm 64 72704] 11) := by
  dec_rfl
theorem c3376_39 :
    ∀ feat, Dec feat c3376 39 (FV7z.mk (.sse (SseMn.movaps)) 32 [.mem (mrip 3695330 128), .xmm 0] 7) := by dec_rfl
theorem c3376_46 :
    ∀ feat, Dec feat c3376 46 (FV7z.mk (.sse (SseMn.movaps)) 32 [.mem (mrip 3695339 128), .xmm 0] 7) := by dec_rfl
theorem c3376_53 : ∀ feat, Dec feat c3376 53 (FV7z.mk .call 64 [.rel 2187958] 5) := by dec_rfl
theorem c3376_58 : ∀ feat, Dec feat c3376 58 (FV7z.mk .mov 64 [.mem (mrip 3695359 64), gr 64 0] 7) := by dec_rfl
theorem c3376_65 : ∀ feat, Dec feat c3376 65 (FV7z.mk .test 64 [gr 64 0, gr 64 0] 3) := by dec_rfl
theorem c3376_68 : ∀ feat, Dec feat c3376 68 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl
theorem c3376_70 : ∀ feat, Dec feat c3376 70 (FV7z.mk .mov 64 [.mem (mrip 3695339 64), gr 64 0] 7) := by dec_rfl
theorem c3376_77 : ∀ feat, Dec feat c3376 77 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), .imm 64 72704] 7) := by
  dec_rfl
theorem c3376_84 : ∀ feat, Dec feat c3376 84 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), .imm 64 0] 8) := by
  dec_rfl
theorem c3376_92 : ∀ feat, Dec feat c3376 92 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem c3376_96 : ∀ feat, Dec feat c3376 96 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v3376 : c3376 <+: sti.drop 3376 := by decide +kernel
theorem tg102 : csuTg 102 = sti_at.add 3376 := by decide +kernel

theorem pq3376 (prof : Profile) : BlkA prof c3376 (0x41ce70 : Addr) 0 8 [Op.nop, Op.sub 64 4 (.i 8)] :=
  .cons (c3376_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c3376_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <| .nil 8
theorem pb3376 (prof : Profile) : BlkA prof sti sti_at 3376 3384 [Op.nop, Op.sub 64 4 (.i 8)] :=
  (pq3376 prof).shift (by decide) v3376
/-- The effects of `pxor; mov edi, 0x11c00` and the four stores before the `call`. -/
def o3384 : List Op :=
  [Op.vld 0 fun _ => 0, Op.mov 32 7 (.i 72704), Op.stia 64 8008096 0, Op.stia 64 8008120 72704, Op.vsa 16 8008064,
    Op.vsa 16 8008080]
theorem bq3384 (prof : Profile) : BlkA prof c3376 (0x41ce70 : Addr) 8 53 o3384 :=
  .cons (c3376_8 _) ((OpI.vz_pxor).at _) (by decide) <|
  .cons (c3376_12 _) ((OpI.mov (.i 72704) (.inl rfl)).at _) (by decide) <|
  .cons (c3376_17 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (c3376_28 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (c3376_39 _) (OpIA.vs_movaps_rip (by decide) (by decide)) (by decide) <|
  .cons (c3376_46 _) (OpIA.vs_movaps_rip (by decide) (by decide)) (by decide) <| .nil 53
theorem b3384 (prof : Profile) : BlkA prof sti sti_at 3384 3429 o3384 :=
  (bq3384 prof).shift (by decide) v3376
theorem cd3429 (feat : Features) : Dec feat sti 3429 (FV7z.mk .call 64 [.rel 2187958] 5) :=
  Dec.shift (j := 3376) (k := 53) (c3376_53 feat) v3376 (by decide)
theorem tc3429 : sti_at.add (3429 + 5) + BitVec.ofNat 64 2187958 = Mnx.mnx_at := by decide +kernel
theorem bq3434 (prof : Profile) : BlkA prof c3376 (0x41ce70 : Addr) 58 65 [Op.sta 64 8008112 0] :=
  .cons (c3376_58 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <| .nil 65
theorem b3434 (prof : Profile) : BlkA prof sti sti_at 3434 3441 [Op.sta 64 8008112 0] :=
  (bq3434 prof).shift (by decide) v3376
theorem td3441 (feat : Features) : Dec feat sti 3441 (FV7z.mk .test 64 [gr 64 0, gr 64 0] 3) :=
  Dec.shift (j := 3376) (k := 65) (c3376_65 feat) v3376 (by decide)
theorem jd3444 (feat : Features) : Dec feat sti 3444 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) :=
  Dec.shift (j := 3376) (k := 68) (c3376_68 feat) v3376 (by decide)
/-- `mov [0x7a31a8], rax; mov qword [rax], 0x11c00; mov qword [rax + 8], 0; add rsp, 8`. -/
def o3446 : List Op :=
  [Op.sta 64 8008104 0, Op.sti 64 (some 0) none 1 0 72704, Op.sti 64 (some 0) none 1 8 0, Op.add 64 4 (.i 8)]
theorem bq3446 (prof : Profile) : BlkA prof c3376 (0x41ce70 : Addr) 70 96 o3446 :=
  .cons (c3376_70 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (c3376_77 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (c3376_84 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (c3376_92 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <| .nil 96
theorem b3446 (prof : Profile) : BlkA prof sti sti_at 3446 3472 o3446 :=
  (bq3446 prof).shift (by decide) v3376
theorem rd3472 (feat : Features) : Dec feat sti 3472 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 3376) (k := 96) (c3376_96 feat) v3376 (by decide)

set_option maxHeartbeats 1600000 in
/-- `csuTg 102` is a function as `Csu.csu_ok` asks: `J m` gives the heap with a top of at least 72752 bytes more
(`hpre`), and `J (m + 1)` holds of the bytes after the constructor (`V'`: the four words at `0x7a31a0` … `0x7a31b8`,
`[p] = 0x11c00`, `[p + 8] = 0`, the bytes outside `[0x7a3180, 0x7a31c0)`, the heap's top word, `[p - 8, hi)` and the
frame as before, the heap for every byte map that agrees on `GlR` but for `[p, p + 72704)`). -/
theorem c102_runs {J : Nat → (Addr → Byte) → Prop} {sp fb : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m hi k : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (htg : csuTg m = sti_at.add 3376)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < sp.toNat - 64 → Foot Wl a) (hhs : hi + 1024 ≤ sp.toNat)
    (hk : 16 ≤ k) (hgw : ∀ i < 64, Foot Wl (Addr.add (BitVec.ofNat 64 8008064) i))
    (hpre : ∀ W, J m W → Mal.Hp F Wl fb hi (k + 72752) W)
    (hJ : ∀ W V' (p : Addr), J m W →
      (∀ a : Addr, ¬ (8008064 ≤ a.toNat ∧ a.toNat < 8008128) →
        (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
          hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V' a = W a) →
      rdq(V', 8008112#64) = p → rdq(V', 8008104#64) = p → rdq(V', 8008120#64) = 72704#64 →
      rdq(V', 8008096#64) = 0#64 → rdq(V', p) = 72704#64 → rdq(V', p + 8#64) = 0#64 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 72704 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 72704 → Foot Wl a ∧ Foot F.data a) →
      (∀ U : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 72704 ≤ a.toNat) →
        U a = V' a) → Mal.Hp F Wl fb hi k U) →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra kk
  have hsl := sp.isLt
  have n80 := e80n sp (by omega)
  have n296 := e296 sp (by omega)
  have hH := hpre V hI
  have hhl := hH.hi_ge
  -- `endbr64; sub rsp, 8`
  refine pro (pb3376 prof) c hin hK hA (hr.trans htg) fun Y₀ t₀ hK₀ hA₀ hr₀ hs₀ hc₀ => ?_
  rw [hsp, e72] at hs₀
  -- `pxor xmm0, xmm0; mov edi, 0x11c00` and the four stores
  refine (Sp.blkA (b3384 prof)).run c hin (fun j' g' _ V' => j' = 3429 ∧
    g' = wr Y₀.cpu.gpr 7 ((Src.i 72704).val 32 Y₀.cpu.gpr) ∧
    ∃ bs bs' : List Byte, bs.length = 16 ∧ bs'.length = 16 ∧ V' = st3384 V bs bs') hK₀ hA₀ hr₀ ?_ ?_
  · exact ⟨fun i hi' => absurd hi' (Nat.not_lt_zero _), fun _ _ => ⟨toBytesLE_length _ _,
      fwg hgw (x := 8008096) (n := 64 / 8) (by decide) (by decide), toBytesLE_length _ _,
      fwg hgw (x := 8008120) (n := 64 / 8) (by decide) (by decide),
      fwg hgw (x := 8008064) (n := 16) (by decide) (by decide), fun bs hb =>
        ⟨fwg hgw (x := 8008080) (n := 16) (by decide) (by decide), fun bs' hb' => ⟨rfl, rfl, bs, bs', hb, hb', rfl⟩⟩⟩⟩
  rintro j' g fl V' ⟨rfl, rfl, bs, bs', hb, hb', rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = sp - 72#64 := by rw [hg₁]; exact hs₀
  have hd₁ : Y₁.cpu.gpr.rdi = 72704#64 := by rw [hg₁]; exact sw72704
  have hc₁ : Cs Y₀.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `call malloc`
  refine c.s_call hK₁ hA₁ hin (sti_lt (by decide)) hr₁ (cd3429 _) hinM (by rw [Mnx.mnx_length]; decide) tc3429
    (fun i hi' => by rw [hs₁, e72b]; exact Nst.fw hsw (by omega) hi' (by rw [n80]; omega) (by rw [n80]; omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hs₁, e72b] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = sp - 80#64 := by rw [hg₂]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hs₁, e72b]
  have hdi₂ : Y₂.cpu.gpr.rdi = 72704#64 := by rw [hg₂]; exact hd₁
  have hc₂ : Cs Y₁.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hH₂ : Mal.Hp F Wl fb hi (k + 72752)
      (Vst (st3384 V bs bs') (sp - 80#64) (toBytesLE (sti_at.add (3429 + 5)) 8)) :=
    Mal.Hp.mvR hH (by omega) fun a ha =>
      (Sga.vo (toBytesLE_length _ _) (by rw [n80]; omega) (by rw [n80]; unfold Mal.GlR at ha; omega)).trans
        (st3384_out V hb hb' (by unfold Mal.GlR at ha; omega))
  refine Mal.mal_hp c hfs hinM hinI hK₂ hA₂ hr₂ hH₂ (.inr ⟨hdi₂, rfl⟩) (by rw [hsp₂, n80]; omega)
    (by rw [hsp₂, n80]; omega)
    (fun i hi' => by rw [hsp₂]; exact Nst.fw hsw (by omega) hi' (by rw [n296]; omega) (by rw [n296]; omega))
    hin (j := 3429 + 5) (sti_lt (by decide)) ?_ ?_
  · rw [hsp₂, Sga.vs (a := sp - 80#64) (n := 8) (toBytesLE_length _ _) (by rw [n80]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro Z t₃ V₂ p hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hp1 hp2 hpn hpF hV₂ hHp _ _
  have e7 : (72704#64 : Addr).toNat = 72704 := rfl
  rw [hdi₂, e7] at hpn hpF hHp
  rw [hsp₂, n80] at hV₂
  have hspZ' : Z.cpu.gpr.rsp = sp - 72#64 := by rw [hspZ, hsp₂, e80a]
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by decide)
  obtain ⟨hp16, hpw, hp8⟩ := pbd hpn hhs hsl hp1
  have hcZ : Cs Y₂.cpu.gpr Z.cpu.gpr := ⟨hbxZ, hbpZ, h12Z, h13Z, h14Z, h15Z⟩
  -- `mov [0x7a31b0], rax`
  have hgvZ : gv Z.cpu.gpr 64 0 = p := by show Z.cpu.gpr.rax.setWidth 64 = p; rw [sw_64_64]; exact haxZ
  have hE₃ : Vst V₂ (BitVec.ofNat 64 8008112) (toBytesLE (gv Z.cpu.gpr 64 0) (64 / 8)) =
      Vst V₂ (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8)) := by rw [hgvZ]
  refine (Sp.blkA (b3434 prof)).run c hin (fun j' g' _ V' => j' = 3441 ∧ g' = Z.cpu.gpr ∧
    V' = Vst V₂ (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8))) hKZ hAZ hrZ ?_ ?_
  · exact ⟨toBytesLE_length _ _, fwg hgw (x := 8008112) (n := 64 / 8) (by decide) (by decide), rfl, rfl, hE₃⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  -- `test rax, rax`, `je` not taken
  refine c.s_test_rr64 hK₃ hA₃ hin (sti_lt (by decide)) hr₃ (td3441 _) ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄, hz₄⟩
  refine c.s_jcc_f hK₄ hA₄ hin (sti_lt (by decide)) hr₄ (jd3444 _) (by
    rw [cond_4, hz₄]; simp only [rv, BitVec.setWidth_eq, BitVec.and_self]
    exact beq_false_of_ne (by rw [show Y₃.cpu.gpr.get (regOf 0) = Y₃.cpu.gpr.rax from rfl, hg₃, haxZ]; exact hp0)) ?_
  rintro Y₅ t₆ hK₅ hA₅ ⟨hr₅, hg₅⟩
  have haxY : Y₅.cpu.gpr.rax = p := by rw [hg₅, hg₄, hg₃]; exact haxZ
  -- `mov [0x7a31a8], rax; mov qword [rax], 0x11c00; mov qword [rax + 8], 0; add rsp, 8`
  have ep8 := Nst.o8 p hp16
  have hgv5 : gv Y₅.cpu.gpr 64 0 = p := by show Y₅.cpu.gpr.rax.setWidth 64 = p; rw [sw_64_64]; exact haxY
  have hq0 : p.toNat + 64 / 8 ≤ p.toNat + 72704 := by omega
  have hq1 : p.toNat ≤ (p + 8#64).toNat := by rw [ep8]; omega
  have hq2 : (p + 8#64).toNat + 64 / 8 ≤ p.toNat + 72704 := by rw [ep8]; omega
  have hpW : ∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 72704 → Foot Wl a := fun a h1 h2 => (hpF a h1 h2).1
  have hf0 : ∀ i < 64 / 8, Foot Wl (Addr.add (eaG Y₅.cpu.gpr (some 0) none 1 0) i) := by
    rw [ea0, haxY]
    intro i hi'
    exact Nst.fw hpW hpw hi' (Nat.le_refl _) hq0
  have hf8 : ∀ i < 64 / 8, Foot Wl (Addr.add (eaG Y₅.cpu.gpr (some 0) none 1 8) i) := by
    rw [ea8, haxY]
    intro i hi'
    exact Nst.fw hpW hpw hi' hq1 hq2
  clear hq1 hq2 ep8
  have hE : Vst (Vst (Vst (Vst V₂ (BitVec.ofNat 64 8008112) (toBytesLE p (64 / 8))) (BitVec.ofNat 64 8008104)
      (toBytesLE (gv Y₅.cpu.gpr 64 0) (64 / 8))) (eaG Y₅.cpu.gpr (some 0) none 1 0)
      (toBytesLE (BitVec.ofNat 64 72704) (64 / 8))) (eaG Y₅.cpu.gpr (some 0) none 1 8)
      (toBytesLE (BitVec.ofNat 64 0) (64 / 8)) = st102 V₂ p := by
    unfold st102
    rw [hgv5, ea0, ea8, haxY]
  refine (Sp.blkA (b3446 prof)).run c hin (fun j' g' _ V' => j' = 3472 ∧
    g' = wr Y₅.cpu.gpr 4 (addR (gv Y₅.cpu.gpr 64 4) (BitVec.ofNat 64 8)) ∧ V' = st102 V₂ p) hK₅ hA₅ hr₅ ?_ ?_
  · exact ⟨toBytesLE_length _ _, fwg hgw (x := 8008104) (n := 64 / 8) (by decide) (by decide),
      toBytesLE_length _ _, hf0,
      toBytesLE_length _ _, hf8, fun _ _ => ⟨rfl, rfl, hE⟩⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₇ hK₆ hA₆ hr₆ hg₆ -
  have hs₆ : Y₆.cpu.gpr.rsp = sp - 64#64 := by rw [hg₆, rsp_add8, hg₅, hg₄, hg₃, hspZ', e72a]
  have hc₆ : Cs Z.cpu.gpr Y₆.cpu.gpr := by rw [hg₆, hg₅, hg₄, hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcs : Cs X.cpu.gpr Y₆.cpu.gpr := Cs.trans hc₀ (Cs.trans hc₁ (Cs.trans hc₂ (Cs.trans hcZ hc₆)))
  -- the bytes: as before but for `[0x7a3180, 0x7a31c0)`, `[p, p + 16)` and the heap
  have hv1 : ∀ a : Addr, ¬ (8008104 ≤ a.toNat ∧ a.toNat < 8008120) →
      (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) →
      st102 V₂ p a = st3384 V bs bs' a := fun a h1 h2 =>
    (st102_out V₂ hp16 h1 (by omega)).trans ((hV₂ a (by omega)).trans
      (Sga.vo (toBytesLE_length _ _) (by rw [n80]; omega) (by rw [n80]; omega)))
  have hvf : ∀ a : Addr, ¬ (8008064 ≤ a.toNat ∧ a.toNat < 8008128) →
      (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → st102 V₂ p a = V a :=
    fun a h1 h2 => (hv1 a (by omega) h2).trans (st3384_out V hb hb' h1)
  have r5 : rdq(st102 V₂ p, 8008120#64) = 72704#64 := by
    have e5 : (8008120#64 : Addr).toNat = 8008120 := rfl
    have h8 : (8008120#64 : Addr).toNat + 8 ≤ 2 ^ 64 := by rw [e5]; decide
    refine (rdq_eq h8 fun a h1 h2 => ?_).trans (st3384_r5 V hb hb')
    rw [e5] at h1 h2
    obtain ⟨g1, g2, g3⟩ := rq_side (.inr rfl) h1 h2 hp1
    exact hv1 a g1 (.inr (.inl ⟨g2, g3⟩))
  have r2 : rdq(st102 V₂ p, 8008096#64) = 0#64 := by
    have e2 : (8008096#64 : Addr).toNat = 8008096 := rfl
    have h8 : (8008096#64 : Addr).toNat + 8 ≤ 2 ^ 64 := by rw [e2]; decide
    refine (rdq_eq h8 fun a h1 h2 => ?_).trans (st3384_r2 V hb hb')
    rw [e2] at h1 h2
    obtain ⟨g1, g2, g3⟩ := rq_side (.inl rfl) h1 h2 hp1
    exact hv1 a g1 (.inr (.inl ⟨g2, g3⟩))
  have hU : ∀ U : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 72704 ≤ a.toNat) →
      U a = st102 V₂ p a) → Mal.Hp F Wl fb hi k U := fun U hW => by
    have h0 := hHp (fun a => if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 72704 then U a else V₂ a)
      fun a _ _ h3 => if_neg (by omega)
    refine Mal.Hp.mvR h0 hk fun a ha => ?_
    by_cases hq : p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 72704
    · exact (if_pos hq).symm
    · exact (hW a ha (by omega)).trans ((st102_out V₂ hp16 (by unfold Mal.GlR at ha; omega) (by omega)).trans
        (if_neg hq).symm)
  -- `ret`
  refine ret_tail c hC hin (rd3472 _) (sti_lt (by decide)) hsp hj₂ hra hK₆ hA₆ hr₆
    ⟨hs₆.trans hsp.symm, hcs.1, hcs.2.1, hcs.2.2.1, hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2⟩
    (hJ V (st102 V₂ p) p hI hvf (st102_r4 V₂ hp8 hp16) (st102_r3 V₂ hp8 hp16) r5 r2
      (st102_rp V₂ hp16) (st102_rp8 V₂ hp16) hp1 hp2 hpn hpF hU)
    (fun a ha => hvf a (by omega) (by omega)) kk

/-- The interval of `csuTg 102`: the four words and the two `movaps` stores. -/
def c102Wr : List (Nat × Nat) := [(8008064, 8008128)]

/-- The words `csuTg 102` shares with the constructors before and after it: those `malloc` reads (`Mal.GlR hi`). -/
def c102Sh (hi : Nat) : List (Nat × Nat) := [(7940480, 7943136), (8013220, 8013232), (8029888, hi)]

/-- `c102_runs` for `Jg`, the spec `wrSpec c102Wr`, the shared words `c102Sh hi` in the spec of `k₀`. -/
theorem c102_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m k₀ hi k : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (htg : csuTg m = sti_at.add 3376)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < sp.toNat - 64 → Foot Wl a) (hhs : hi + 1024 ≤ sp.toNat)
    (hS : 8029400 ≤ sp.toNat) (hk : 16 ≤ k) (hgw : ∀ i < 64, Foot Wl (Addr.add (BitVec.ofNat 64 8008064) i))
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec c102Wr) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c102Wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (c102Sh hi) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (c102Sh hi) x)
    (hGx : ∀ W, G m W → Mal.Hp F Wl fb hi (k + 72752) W)
    (hG : ∀ W V' (p : Addr), G m W →
      (∀ a : Addr, ¬ (8008064 ≤ a.toNat ∧ a.toNat < 8008128) →
        (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
          hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V' a = W a) →
      rdq(V', 8008112#64) = p → rdq(V', 8008104#64) = p → rdq(V', 8008120#64) = 72704#64 →
      rdq(V', 8008096#64) = 0#64 → rdq(V', p) = 72704#64 → rdq(V', p + 8#64) = 0#64 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 72704 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 72704 → Foot Wl a ∧ Foot F.data a) →
      (∀ U : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 72704 ≤ a.toNat) →
        U a = V' a) → Mal.Hp F Wl fb hi k U) →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have hsl := sp.isLt
  refine c102_runs c hC hin hfs hinM hinI htg hsw hhs hk hgw (fun W hJ => hGx W hJ.2)
    fun W V' p hJ hv r4 r3 r5 r2 rp rp8 hp1 hp2 hpn hpF hHp => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m
      hSh hP₀ hShD (fun a h1 h2 h3 => ?_) (hG W V' p · hv r4 r3 r5 r2 rp rp8 hp1 hp2 hpn hpF hHp) hJ
  simp only [c102Wr, c102Sh, InR] at h1 h3
  exact hv a (by omega) (by omega)

end FV7z.Ctor
