import FV7z.Onw
import FV7z.Lemmas.Lock2
/-!
# The string set-up at `0x44c360` (PLAN.md G3, constructors)

The function at `0x44c360` of `7zzs` (called by constructor 98 with `rdi = 0x79ed90`) sets up an empty string `O`:
`[O] = 0`, `p = operator new (4)`, `[O] = p`, `[O + 8] = 0x300000000` (length 0, capacity 3), `[p] = 0`.

- `nst`, `nst_pin`: the 47 bytes, the file's (by the kernel's evaluation of Zellic's ELF reader).
- `blk_0`, `vc_0`: to the `call` (`push rbx`, `rbx = O`, `[O] = 0`, `edi = 4`); `blk_25`, `vc_25`: the stores after
  it.
- `Mal.Hp.hi_ge`: `Hp … k` puts `hi` at least `k` above the heap's start.
- `nst_ok`: from the entry with `rdi = O` (16 bytes outside `GlR` and below the heap) and `Mal.Hp` with a top of at
  least `m + 1072` bytes: back at the return address with the registers a call keeps, `[O] = p`,
  `[O + 8] = 0x300000000`, `[p] = 0`, the bytes outside `O`'s 16, the heap's words and the frame as at the entry, and
  `Mal.Hp … m` for every byte map that agrees on `GlR` but for `[p, p + 4)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)

namespace FV7z.Mal

theorem Hp.hi_ge {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi k : Nat} {V : Addr → Byte}
    (h : Hp F Wl fb hi k V) : 8032256 + k ≤ hi := by
  obtain ⟨_, _, _, _, -, -, -, -, -, hT, hTh, -⟩ := h
  omega

end FV7z.Mal

namespace FV7z.Nst
set_option maxRecDepth 100000

/-! ## The code -/

/-- The function, `0x44c360` to `0x44c38f` of `7zzs`. -/
def nst : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x48, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00, 0xbf,
  0x04, 0x00, 0x00, 0x00, 0xe8, 0x37, 0x66, 0x1b, 0x00, 0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x03,
  0x00, 0x00, 0x00, 0x48, 0x89, 0x03, 0x48, 0x89, 0x53, 0x08, 0xc6, 0x00, 0x00, 0x5b, 0xc3]

theorem nst_pin : Exe.bytesAt V2606.zzs.blob 0x44c360 47 = some nst := by decide +kernel
theorem nst_length : nst.length = 47 := by decide +kernel

/-- Where the code lies in `7zzs`. -/
abbrev nst_at : Addr := 0x44c360

theorem lt_len {j : Nat} (h : j < 47) : j < nst.length := nst_length ▸ h

theorem nst_0 : ∀ feat, Dec feat nst 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem nst_4 : ∀ feat, Dec feat nst 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem nst_5 : ∀ feat, Dec feat nst 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem nst_8 : ∀ feat, Dec feat nst 8 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), .imm 64 0] 7) := by
  dec_rfl
theorem nst_15 : ∀ feat, Dec feat nst 15 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4)] 5) := by dec_rfl
theorem nst_20 : ∀ feat, Dec feat nst 20 (FV7z.mk .call 64 [.rel 1795639] 5) := by dec_rfl
theorem nst_25 : ∀ feat, Dec feat nst 25 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 12884901888)] 10) := by dec_rfl
theorem nst_35 : ∀ feat, Dec feat nst 35 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem nst_38 : ∀ feat, Dec feat nst 38 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem nst_42 : ∀ feat, Dec feat nst 42 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem nst_45 : ∀ feat, Dec feat nst 45 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem nst_46 : ∀ feat, Dec feat nst 46 (FV7z.mk .ret 64 [] 1) := by dec_rfl

theorem tgt_20 : nst_at.add (20 + 5) + BitVec.ofNat 64 1795639 = Onw.onw_at.add 64 := by decide

/-! ## The stretches -/

/-- `endbr64`, `push rbx`, `mov rbx, rdi`, `mov qword [rdi], 0`, `mov edi, 4`. -/
def o0 : List Op := [Op.nop, Op.push 3, Op.mov 64 3 (.r 7), Op.sti 64 (some 7) none 1 0 0, Op.mov 32 7 (.i 4)]

theorem blk_0 (prof : Profile) : Blk prof nst 0 20 o0 :=
  .cons (nst_0 _) OpI.endbr (by decide) <|
  .cons (nst_4 _) OpI.push (by decide) <|
  .cons (nst_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (nst_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (nst_15 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 20

/-- `movabs rdx, 0x300000000`, `mov [rbx], rax`, `mov [rbx + 8], rdx`, `mov byte [rax], 0`. -/
def o25 : List Op :=
  [Op.mov 64 2 (.i 12884901888), Op.st 64 (some 3) none 1 0 0, Op.st 64 (some 3) none 1 8 2,
    Op.sti 8 (some 0) none 1 0 0]

theorem blk_25 (prof : Profile) : Blk prof nst 25 45 o25 :=
  .cons (nst_25 _) (OpI.mov (.i 12884901888) (.inr rfl)) (by decide) <|
  .cons (nst_35 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (nst_38 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (nst_42 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 45

theorem vc_0 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hO : ∀ i < 8, Foot Wl (Addr.add g.rdi i))
    (hQ : ∀ fl, Q { g with rbx := g.rdi, rsp := g.rsp - 8, rdi := 4#64 } fl
      (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE 0#64 8))) :
    wp F Wl o0 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst hO hQ ⊢
  wpx [o0]
  exact ⟨hst, hO, hQ _⟩

theorem vc_25 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (hO1 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (hO2 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (hp : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (hQ : ∀ fl, Q { g with rdx := 12884901888#64 } fl
      (Vst (Vst (Vst V g.rbx (toBytesLE g.rax 8)) (g.rbx + 8#64) (toBytesLE 12884901888#64 8)) g.rax
        (toBytesLE 0#8 1))) :
    wp F Wl o25 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hO1 hO2 hp hQ ⊢
  wpx [o25]
  exact ⟨hO1, hO2, hp, hQ _⟩

/-! ## The run -/

theorem b8 (S : Addr) (h : 248 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega
theorem b16 (S : Addr) (h : 248 ≤ S.toNat) : (S - 8 - 8).toNat = S.toNat - 16 := by bv_omega
theorem u8 (S : Addr) : S - 8 - 8 + 8 = S - 8 := by bv_omega
theorem u16 (S : Addr) : S - 8 + 8 = S := by bv_omega
theorem o8 (O : Addr) (h : O.toNat + 16 < 2 ^ 64) : (O + 8#64).toNat = O.toNat + 8 := by bv_omega

/-- A byte of the `n` from `x` inside `[lo, hi)`, all in `Wl`. -/
theorem fw {Wl : List Rgn} {lo hi : Nat} {x : Addr} (hw : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → Foot Wl a)
    (hh : hi ≤ 2 ^ 64) {i n : Nat} (hin : i < n) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) :
    Foot Wl (Addr.add x i) := by
  have e : (Addr.add x i).toNat = x.toNat + i := by
    unfold Addr.add; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact hw _ (by omega) (by omega)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- The string set-up at `0x44c360`: see the module doc. -/
theorem nst_ok {fb : Addr} {hi m : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L nst_at nst) (hinW : CodeIn L Onw.onw_at Onw.onw) (hinM : CodeIn L mnx_at mnx)
    (hinI : CodeIn L imm_at imm) {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nst_at) (hH : Mal.Hp F Wl fb hi (m + 1072) V)
    (hm : 16 ≤ m) {O : Addr} (hdi : X.cpu.gpr.rdi = O)
    (hOg : ∀ a : Addr, O.toNat ≤ a.toNat → a.toNat < O.toNat + 16 → ¬ Mal.GlR hi a)
    (hO7 : 7940776 ≤ O.toNat) (hOp : O.toNat + 16 ≤ 8032256)
    (hOw : ∀ a : Addr, O.toNat ≤ a.toNat → a.toNat < O.toNat + 16 → Foot Wl a)
    (hhi : hi + 248 ≤ X.cpu.gpr.rsp.toNat) (hR : X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot Wl a)
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (kc : ∀ Z t' (V₂ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + 4 ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + 4 → Foot Wl a ∧ Foot F.data a) →
      rdq(V₂, O) = p → rdq(V₂, O + 8#64) = 12884901888#64 → (byteAddrs p 1).map V₂ = toBytesLE 0#8 1 →
      (∀ a : Addr, ¬ (O.toNat ≤ a.toNat ∧ a.toNat < O.toNat + 16) →
        (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
          hi ≤ a.toNat ∧ (a.toNat + 240 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat)) → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, Mal.GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 4 ≤ a.toNat) → W a = V₂ a) →
        Mal.Hp F Wl fb hi m W) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hS8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64 := by omega
  have hhl := hH.hi_ge
  have e8 := b8 X.cpu.gpr.rsp (by omega)
  have e16 := b16 X.cpu.gpr.rsp (by omega)
  have eO8 := o8 O (by omega)
  -- to the `call`
  refine c.s_blk hin (blk_0 prof) hK hA (by rw [hrip]; rfl) ?_
  refine vc_0 (fun i hi' => fw hsw (by omega) hi' (by rw [e8]; omega) (by rw [e8]; omega))
    (fun i hi' => by rw [hdi]; exact fw hOw (by omega) hi' (Nat.le_refl _) (by omega))
    fun _ Y1 t1 hK1 hA1 hr1 hg1 _ => ?_
  rw [hdi] at hA1
  have hs1 : Y1.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg1]; try rfl
  -- `call operator new`
  refine c.s_call_x hK1 hA1 hin (lt_len (by decide)) hr1 (nst_20 _) hinW (tgt := 64) (Onw.lt_len (by decide)) tgt_20
    (fun i hi' => by rw [hs1]; exact fw hsw (by omega) hi' (by rw [e16]; omega) (by rw [e16]; omega)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [hs1] at hA2
  have hsp2 : Y2.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := by rw [hg2, hs1]; try rfl
  have hdi2 : Y2.cpu.gpr.rdi = 4#64 := by rw [hg2, hg1]; try rfl
  have hbx2 : Y2.cpu.gpr.rbx = O := by rw [hg2, hg1, hdi]; try rfl
  have hbp2 : Y2.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg2, hg1]; try rfl
  have h122 : Y2.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg2, hg1]; try rfl
  have h132 : Y2.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg2, hg1]; try rfl
  have h142 : Y2.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg2, hg1]; try rfl
  have h152 : Y2.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg2, hg1]; try rfl
  -- the bytes at the entry of `operator new`: `V` but for the frame's 16 and `[O, O + 8)`
  have hVe : ∀ a : Addr, ¬ (O.toNat ≤ a.toNat ∧ a.toNat < O.toNat + 8) →
      (a.toNat < X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) O (toBytesLE 0#64 8))
        (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (nst_at.add (20 + 5)) 8) a = V a := fun a hO ha => by
    have h1 : Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) a = V a :=
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)
    have h2 : Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) O (toBytesLE 0#64 8) a = V a := by
      rw [← h1]; exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
    rw [← h2]
    exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (by rw [toBytesLE_length, e16]; omega)
  have hH2 : Mal.Hp F Wl fb hi (m + 1072)
      (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) O (toBytesLE 0#64 8))
        (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (nst_at.add (20 + 5)) 8)) :=
    Mal.Hp.mvR hH (by omega) fun a ha => hVe a (fun h => hOg a h.1 (by omega) ha)
      (.inl (by unfold Mal.GlR at ha; omega))
  refine Onw.onw_hp c hfs hinW hinM hinI hK2 hA2 hr2 hH2 (by rw [hdi2]; decide) (by rw [hdi2]; decide)
    (by rw [hsp2, e16]; omega) (by rw [hsp2, e16]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hsp2, e16] at h2; omega)) hin (j := 25) (lt_len (by decide)) ?_ ?_
  · rw [hsp2, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 8 - 8) _ (toBytesLE_length _ _) (by rw [e16]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  intro Z t3 V₃ p hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hp1 hp2 hpn hpF hV₃ hHp
  rw [hsp2, e16] at hV₃
  rw [hdi2] at hpn hpF hHp
  rw [hsp2] at hspZ
  have e4 : (4#64 : Addr).toNat = 4 := rfl
  rw [e4] at hpn hpF hHp
  have hspZ' : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hspZ]; exact u8 _
  have hbxZ' : Z.cpu.gpr.rbx = O := hbxZ.trans hbx2
  -- the stores after the `call`
  refine c.s_blk hin (blk_25 prof) hKZ hAZ hrZ ?_
  refine vc_25 (fun i hi' => by rw [hbxZ']; exact fw hOw (by omega) hi' (Nat.le_refl _) (by omega))
    (fun i hi' => by rw [hbxZ']; exact fw hOw (by omega) hi' (by rw [eO8]; omega) (by rw [eO8]; omega))
    (fun i hi' => by rw [haxZ]; exact fw (fun a h1 h2 => (hpF a h1 h2).1) (by omega) hi' (Nat.le_refl _) (by omega))
    fun _ Y4 t4 hK4 hA4 hr4 hg4 _ => ?_
  rw [hbxZ', haxZ] at hA4
  have hsp4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg4]; exact hspZ'
  -- the final bytes `Vf`: `V₃` but for `O`'s 16 and `p`
  have hVf : ∀ a : Addr, ¬ (O.toNat ≤ a.toNat ∧ a.toNat < O.toNat + 16) → a ≠ p →
      Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#8 1) a =
        V₃ a := fun a hO hp => by
    have h1 : Vst V₃ O (toBytesLE p 8) a = V₃ a :=
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
    have h2 : Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8) a = V₃ a := by
      rw [← h1]
      exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, eO8]; omega) (by rw [toBytesLE_length, eO8]; omega)
    rw [← h2]
    have hpa : a.toNat ≠ p.toNat := fun h => hp (BitVec.eq_of_toNat_eq h)
    exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
  -- `pop rbx`: the `rbx` of the entry, from the frame
  have hbx : rdq(Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p
      (toBytesLE 0#8 1), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    have h := Sbrk.rd_eq (V := Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))
      (V' := Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#8 1))
      (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [e8]; omega) fun a h1 h2 => by
        rw [e8] at h1 h2
        rw [hVf a (by omega) (fun h => by subst h; omega), hV₃ a (.inr (.inr ⟨by omega, .inr (by omega)⟩))]
        have h3 : Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) O (toBytesLE 0#64 8) a =
            Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) a :=
          Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
        rw [← h3]
        exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (.inr (by rw [toBytesLE_length, e16]; omega))
    rw [h, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 8) _ (toBytesLE_length _ _) (by rw [e8]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
  refine c.s_pop hK4 hA4 hin (lt_len (by decide)) hr4 (nst_45 _)
    (fun i hi' => c.hws _ (by rw [hsp4]; exact fw hsw (by omega) hi' (by rw [e8]; omega) (by rw [e8]; omega))) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hsp5 : Y5.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg5]; show Y4.cpu.gpr.rsp + 8 = _; rw [hsp4]; exact u16 _
  -- `ret`
  have hraf : rdq(Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p
      (toBytesLE 0#8 1), Y5.cpu.gpr.rsp) = e'.add j := by
    have h := Sbrk.rd_eq (V := V)
      (V' := Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#8 1))
      (x := X.cpu.gpr.rsp) (n := 8) (by omega) fun a h1 h2 => by
        rw [hVf a (by omega) (fun h => by subst h; omega), hV₃ a (.inr (.inr ⟨by omega, .inr (by omega)⟩))]
        exact hVe a (by omega) (.inr h1)
    rw [hsp5, h]
    exact hra
  refine c.s_ret hK5 hA5 hin (lt_len (by decide)) hr5 (nst_46 _)
    (fun i hi' => c.hws _ (by rw [hsp5]; exact fw hsw (by omega) hi' (by omega) (by omega))) hin₂ hj hraf ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine kc Y6 t6 _ p hK6 hA6 hr6 (by rw [hg6]; show Y5.cpu.gpr.rsp + 8 = _; rw [hsp5])
    (by rw [hg6, hg5]; show rdq(_, Y4.cpu.gpr.rsp) = _; rw [hsp4]; exact hbx)
    (by rw [hg6, hg5, hg4]; exact hbpZ.trans hbp2) (by rw [hg6, hg5, hg4]; exact h12Z.trans h122)
    (by rw [hg6, hg5, hg4]; exact h13Z.trans h132) (by rw [hg6, hg5, hg4]; exact h14Z.trans h142)
    (by rw [hg6, hg5, hg4]; exact h15Z.trans h152) hp1 hp2 hpn hpF ?_ ?_ ?_ ?_ ?_
  · -- `[O] = p`
    have h := Sbrk.rd_eq (V := Vst V₃ O (toBytesLE p 8))
      (V' := Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#8 1))
      (x := O) (n := 8) (by omega) fun a h1 h2 => by
        have hpa : a.toNat ≠ p.toNat := by omega
        have h3 : Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8) a =
            Vst V₃ O (toBytesLE p 8) a :=
          Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, eO8]; omega) (.inl (by rw [eO8]; omega))
        rw [← h3]
        exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
    rw [h, Tun.rd_Vst_self _ O _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · -- `[O + 8] = 0x300000000`
    have h := Sbrk.rd_eq (V := Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8))
      (V' := Vst (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p (toBytesLE 0#8 1))
      (x := O + 8#64) (n := 8) (by rw [eO8]; omega) fun a h1 h2 => by
        rw [eO8] at h1 h2
        exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
    rw [h, Tun.rd_Vst_self _ (O + 8#64) _ (toBytesLE_length _ _) (by rw [eO8]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
  · -- `[p] = 0`
    exact Tun.rd_Vst_self (Vst (Vst V₃ O (toBytesLE p 8)) (O + 8#64) (toBytesLE 12884901888#64 8)) p
      (toBytesLE 0#8 1) (n := 1) (toBytesLE_length _ _) (by omega)
  · -- the frame
    intro a hO ha
    rw [hVf a hO (fun h => by subst h; omega)]
    rcases ha with ha | ha | ⟨h1, ha | ha⟩
    · rw [hV₃ a (.inl ha)]
      exact hVe a (by omega) (.inl (by omega))
    · rw [hV₃ a (.inr (.inl ha))]
      exact hVe a (by omega) (.inl (by omega))
    · rw [hV₃ a (.inr (.inr ⟨h1, .inl (by omega)⟩))]
      exact hVe a (by omega) (.inl (by omega))
    · rw [hV₃ a (.inr (.inr ⟨h1, .inr (by omega)⟩))]
      exact hVe a (by omega) (.inr ha)
  · -- the heap: from `operator new`'s, by the bytes that agree with `V₃` but on `[p, p + 4)`
    intro W hW
    have h0 := hHp (fun a => if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4 then W a else V₃ a)
      fun a _ _ h3 => if_neg (by omega)
    refine Mal.Hp.mvR h0 hm fun a ha => ?_
    by_cases hp : p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + 4
    · exact (if_pos hp).symm
    · exact (hW a ha (by omega)).trans ((hVf a (fun h => hOg a h.1 h.2 ha) (fun h => by subst h; omega)).trans
        (if_neg hp).symm)

end FV7z.Nst
