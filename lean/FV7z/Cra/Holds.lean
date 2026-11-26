import FV7z.Cra.Cuts
import FV7z.Onw
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# The lzma handler's `CreateArc` (PLAN.md §M, M1)

7-Zip 26.06's `CreateArc` of the lzma format at `0x49e9c0` in `7zzs` (`CPP/7zip/Archive/LzmaHandler.cpp`,
`return new CHandler`): `sub rsp, 8`, `p = operator new (0x58)` (the `call` at 13 to the body of `operator new`,
`Onw.onw_at`), then the constructor's stores into the block: the two vtables (`[p] = 0x785fb0`,
`[p + 8] = 0x786030`), `[p + 16] = 0` (4 bytes), `[p + 20] = 0` (1 byte), `[p + 48] = 0`, `[p + 56] = 0`;
`add rsp, 8; ret` (74) with `rax = p`.

- `cS`: the bytes after the stores, from the bytes `V` after `operator new`.
- `vc_0`, `vc_18`: the verification conditions of the two stretches (to the `call`; after it, to the `ret`).
- `cra_ok`: from the entry, with `Mal.Hp` with a top of at least `m + 1072` bytes (as `Onw.onw_hp0`): back at the
  return address with `rax = p`, the registers a call keeps as at the entry, the bytes `cS V₁ p` where `V₁` is
  `V` outside the heap's words and the frame, and `Mal.Hp … m` for every byte map that agrees with `V₁` on the heap
  but for `[p, p + 88)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Cra
set_option maxRecDepth 100000

/-- The `call` to `operator new`'s body. -/
def pcall : List Byte := [0xe8, 0x9e, 0x3f, 0x16, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1458078] 5) := by dec_rfl
theorem wc_13 : pcall <+: cra.drop 13 := by decide +kernel
theorem call_13 (feat : Features) : Dec feat cra 13 (FV7z.mk .call 64 [.rel 1458078] 5) :=
  Dec.shift (j := 13) (k := 0) (pcall_0 feat) wc_13 (Nat.zero_le _)
theorem tgt_13 : cra_at.add (13 + 5) + BitVec.ofNat 64 1458078 = Onw.onw_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_74 : pret <+: cra.drop 74 := by decide +kernel
theorem ret_74 (feat : Features) : Dec feat cra 74 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 74) (k := 0) (pret_0 feat) w_74 (Nat.zero_le _)

/-- The bytes after the constructor's stores into `p`. -/
abbrev cS (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (p + 16#64) (toBytesLE 0#32 4)) (p + 48#64) (toBytesLE 0#64 8)) p
    (toBytesLE 7888816#64 8)) (p + 8#64) (toBytesLE 7888944#64 8)) (p + 56#64) (toBytesLE 0#64 8)) (p + 20#64)
    (toBytesLE 0#8 1)

theorem vc_0 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (hQ : ∀ fl, Q { g with rsp := g.rsp - 8#64, rdi := 88#64 } fl V) :
    wp F Wl o0 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hQ ⊢
  wpx [o0]
  exact hQ _

theorem vc_18 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (h16 : ∀ i < 4, Foot Wl (Addr.add (g.rax + 16#64) i)) (h48 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 48#64) i))
    (h0 : ∀ i < 8, Foot Wl (Addr.add g.rax i)) (h8 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i))
    (h56 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 56#64) i)) (h20 : ∀ i < 1, Foot Wl (Addr.add (g.rax + 20#64) i))
    (hQ : ∀ fl, Q { g with rcx := 7888816#64, rdx := 7888944#64, rsp := g.rsp + 8#64 } fl (cS V g.rax)) :
    wp F Wl o1 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h16 h48 h0 h8 h56 h20 hQ ⊢
  wpx [o1]
  exact ⟨h16, h48, h0, h8, h56, h20, hQ _⟩

/-! ## The run -/

theorem b8 (S : Addr) (h : 248 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega
theorem b16 (S : Addr) (h : 248 ≤ S.toNat) : (S - 8 - 8).toNat = S.toNat - 16 := by bv_omega
theorem u8 (S : Addr) : S - 8 - 8 + 8 = S - 8 := by bv_omega
theorem u16 (S : Addr) : S - 8 + 8 = S := by bv_omega

/-- `p + k` without a wrap. -/
theorem pk (p : Addr) {k : Nat} (h : p.toNat + k < 2 ^ 64) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

/-- A byte of the `n` from `x` inside `[lo, hi)`, all in `Wl`. -/
theorem fw {Wl : List Rgn} {lo hi : Nat} {x : Addr} (hw : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → Foot Wl a)
    (hh : hi ≤ 2 ^ 64) {i n : Nat} (hin : i < n) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) :
    Foot Wl (Addr.add x i) := by
  have e : (Addr.add x i).toNat = x.toNat + i := by
    unfold Addr.add; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact hw _ (by omega) (by omega)

/-- `cS` changes only `[p, p + 64)`. -/
theorem cS_out (V : Addr → Byte) (p a : Addr) (hp : p.toNat + 64 < 2 ^ 64)
    (ha : a.toNat < p.toNat ∨ p.toNat + 64 ≤ a.toNat) : cS V p a = V a := by
  have e8 := pk p (k := 8) (by omega)
  have e16 := pk p (k := 16) (by omega)
  have e20 := pk p (k := 20) (by omega)
  have e48 := pk p (k := 48) (by omega)
  have e56 := pk p (k := 56) (by omega)
  dsimp only [cS]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- The lzma handler's `CreateArc`: see the module doc. -/
theorem cra_ok {fb : Addr} {hi m : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L cra_at cra) (hinW : CodeIn L Onw.onw_at Onw.onw) (hinM : CodeIn L mnx_at mnx)
    (hinI : CodeIn L imm_at imm) {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cra_at) (hH : Mal.Hp F Wl fb hi (m + 1072) V)
    (hhi : hi + 248 ≤ X.cpu.gpr.rsp.toNat) (hR : X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot Wl a)
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (kc : ∀ Z t' (V₁ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (cS V₁ p) →
      Z.cpu.rip = e'.add j → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 88 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 88 → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 240 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) → V₁ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < p.toNat ∨ p.toNat + 88 ≤ a.toNat) → W a = V₁ a) → Mal.Hp F Wl fb hi m W) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hS8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64 := by omega
  have e8 := b8 X.cpu.gpr.rsp (by omega)
  have e16 := b16 X.cpu.gpr.rsp (by omega)
  -- to the `call`
  refine c.s_blk hin (blk_0 prof) hK hA (by rw [hrip]; rfl) ?_
  refine vc_0 fun _ Y1 t1 hK1 hA1 hr1 hg1 _ => ?_
  have hs1 : Y1.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg1]; try rfl
  -- `call operator new`
  refine c.s_call_x hK1 hA1 hin (lt_len (by decide)) hr1 (call_13 _) hinW (tgt := 0) (Onw.lt_len (by decide))
    tgt_13 (fun i hi' => by rw [hs1]; exact fw hsw (by omega) hi' (by rw [e16]; omega) (by rw [e16]; omega)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [hs1] at hA2
  have hsp2 : Y2.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := by rw [hg2, hs1]; try rfl
  have hdi2 : Y2.cpu.gpr.rdi = 88#64 := by rw [hg2, hg1]; try rfl
  have hbx2 : Y2.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [hg2, hg1]; try rfl
  have hbp2 : Y2.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg2, hg1]; try rfl
  have h122 : Y2.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg2, hg1]; try rfl
  have h132 : Y2.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg2, hg1]; try rfl
  have h142 : Y2.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg2, hg1]; try rfl
  have h152 : Y2.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg2, hg1]; try rfl
  -- the bytes at the entry of `operator new`: `V` but for the return address
  have hVe : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ a.toNat) →
      Vst V (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (cra_at.add (13 + 5)) 8) a = V a := fun a ha =>
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (by rw [toBytesLE_length, e16]; omega)
  have hH2 : Mal.Hp F Wl fb hi (m + 1072) (Vst V (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (cra_at.add (13 + 5)) 8)) :=
    Mal.Hp.mv hH (by omega) fun a _ h2 => hVe a (.inl (by omega))
  refine Onw.onw_hp0 c hfs hinW hinM hinI hK2 hA2 (by rw [hr2, addr_add_zero]) hH2 (by rw [hdi2]; decide)
    (by rw [hdi2]; decide) (by rw [hsp2, e16]; omega) (by rw [hsp2, e16]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hsp2, e16] at h2; omega)) hin (j := 18) (lt_len (by decide)) ?_ ?_
  · rw [hsp2, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 8 - 8) _ (toBytesLE_length _ _) (by rw [e16]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  intro Z t3 V₃ p hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hp1 hp2 hpn hpF hV₃ hHp
  rw [hsp2, e16] at hV₃
  rw [hdi2] at hpn hpF hHp
  rw [hsp2] at hspZ
  have e88 : (88#64 : Addr).toNat = 88 := rfl
  rw [e88] at hpn hpF hHp
  have hspZ' : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hspZ]; exact u8 _
  have hpw : ∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 88 → Foot Wl a := fun a h1 h2 => (hpF a h1 h2).1
  have e8p := pk p (k := 8) (by omega)
  have e16p := pk p (k := 16) (by omega)
  have e20p := pk p (k := 20) (by omega)
  have e48p := pk p (k := 48) (by omega)
  have e56p := pk p (k := 56) (by omega)
  -- the stores after the `call`
  refine c.s_blk hin (blk_18 prof) hKZ hAZ hrZ ?_
  rw [haxZ]
  refine vc_18 (fun i hi' => fw hpw (by omega) hi' (by rw [e16p]; omega) (by rw [e16p]; omega))
    (fun i hi' => fw hpw (by omega) hi' (by rw [e48p]; omega) (by rw [e48p]; omega))
    (fun i hi' => fw hpw (by omega) hi' (Nat.le_refl _) (by omega))
    (fun i hi' => fw hpw (by omega) hi' (by rw [e8p]; omega) (by rw [e8p]; omega))
    (fun i hi' => fw hpw (by omega) hi' (by rw [e56p]; omega) (by rw [e56p]; omega))
    (fun i hi' => fw hpw (by omega) hi' (by rw [e20p]; omega) (by rw [e20p]; omega))
    fun _ Y4 t4 hK4 hA4 hr4 hg4 _ => ?_
  have hsp4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg4]; show Z.cpu.gpr.rsp + 8#64 = _; rw [hspZ']; exact u16 _
  -- `ret`
  have hraf : rdq(cS V₃ p, Y4.cpu.gpr.rsp) = e'.add j := by
    have h := Sbrk.rd_eq (V := V) (V' := cS V₃ p) (x := X.cpu.gpr.rsp) (n := 8) (by omega) fun a h1 h2 => by
      rw [cS_out V₃ p a (by omega) (.inr (by omega)), hV₃ a (.inr (.inr ⟨by omega, .inr (by omega)⟩))]
      exact hVe a (.inr (by omega))
    rw [hsp4, h]
    exact hra
  refine c.s_ret hK4 hA4 hin (lt_len (by decide)) hr4 (ret_74 _)
    (fun i hi' => c.hws _ (by rw [hsp4]; exact fw hsw (by omega) hi' (by omega) (by omega))) hin₂ hj hraf ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine kc Y5 t5 V₃ p hK5 hA5 hr5 (by rw [hg5]; show Y4.cpu.gpr.rsp + 8 = _; rw [hsp4])
    (by rw [hg5, hg4]; exact haxZ) (by rw [hg5, hg4]; exact hbxZ.trans hbx2)
    (by rw [hg5, hg4]; exact hbpZ.trans hbp2) (by rw [hg5, hg4]; exact h12Z.trans h122)
    (by rw [hg5, hg4]; exact h13Z.trans h132) (by rw [hg5, hg4]; exact h14Z.trans h142)
    (by rw [hg5, hg4]; exact h15Z.trans h152) hp1 hp2 hpn hpF ?_ hHp
  intro a ha
  rcases ha with ha | ha | ⟨h1, ha | ha⟩
  · rw [hV₃ a (.inl ha)]
    exact hVe a (.inl (by omega))
  · rw [hV₃ a (.inr (.inl ha))]
    exact hVe a (.inl (by omega))
  · rw [hV₃ a (.inr (.inr ⟨h1, .inl (by omega)⟩))]
    exact hVe a (.inl (by omega))
  · rw [hV₃ a (.inr (.inr ⟨h1, .inr (by omega)⟩))]
    exact hVe a (.inr (by omega))

end FV7z.Cra
