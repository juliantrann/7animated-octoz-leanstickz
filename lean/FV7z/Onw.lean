import FV7z.Mal.Ok
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.Wp
/-!
# `operator new (n)` at `0x6029b0` (PLAN.md G3, constructors)

`operator new` of `7zzs` is a `jmp` (`0x6029b0`) to `0x602970`: `push rbx`, `rbx = n` (`1` if `n = 0`),
`malloc (rbx)` (`0x633160`, called directly), and back with the block if it is not null (the null way calls the
new handler: not reached, `malloc` after the first call does not fail on `n ≤ 1024`).

- `Mal.Hp.mvR`: `Hp` for bytes that agree on `GlR` (what it reads), for the callers that store into the
  `.bss` between the allocator's words (the objects of the constructors).
- `onw`, `onw_pin`: the 73 bytes, the file's (by the kernel's evaluation of Zellic's ELF reader).
- `ob`, `blk_0`, `vc_0`: the stretch from `0` to the `call` (the `push`, `test`, `mov`, `cmovne`, `mov`).
- `onw_hp`: from `0x6029b0` with `n ≠ 0`, `n ≤ 1024` and `Mal.Hp` with a top of at least `m + 1072` bytes:
  `Mal.mal_hp` with 16 bytes more of stack (the `push` and the `call`): the run reaches the return address with
  `rax = p` the block, the registers a call keeps as at the entry, the bytes outside the heap's words and the frame as
  at the entry, and `Mal.Hp … m` for every byte map that agrees with the one at the return but for `[p, p + n)`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at mnx_length)

namespace FV7z.Mal

/-- `Hp` (a top of at least 16 bytes) for bytes that agree on `GlR hi`: all it reads (`Gl` on `GlR` below the top,
`main_arena.top`, the top's size word, `system_mem`). -/
theorem Hp.mvR {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V W : Addr → Byte}
    (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) (hW : ∀ a : Addr, GlR hi a → W a = V a) : Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, G.mvR (E := T.toNat) hf1 hf2 hc1 hc2 (by omega) fun a ha _ => hW a (by
      unfold GlR at ha ⊢; omega), hf1, hf2, hc1, hc2, hT, hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
  · rw [Sbrk.rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [et] at a1 a2; omega)]
    exact htop
  · rw [Sbrk.rd_eq (V := V) (x := T + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [e8] at a1 a2; omega)]
    exact hsz
  · rw [Sbrk.rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by unfold GlR; rw [es] at a1 a2; omega)]
    exact hsm

end FV7z.Mal

namespace FV7z.Onw
set_option maxRecDepth 100000

/-! ## The code -/

/-- The function, `0x602970` to `0x6029b9` of `7zzs` (`operator new` at `64`). -/
def onw : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x85, 0xff, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0f, 0x45,
  0xdf, 0x48, 0x89, 0xdf, 0xe8, 0xd7, 0x07, 0x03, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x02, 0x5b, 0xc3,
  0xe8, 0xbb, 0xb6, 0x00, 0x00, 0x48, 0x85, 0xc0, 0x0f, 0x84, 0xc3, 0x8e, 0xe1, 0xff, 0xff, 0xd0,
  0xeb, 0xdf, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xb7, 0xff, 0xff, 0xff]

theorem onw_pin : Exe.bytesAt V2606.zzs.blob 0x602970 73 = some onw := by decide +kernel
theorem onw_length : onw.length = 73 := by decide +kernel

/-- Where the code lies in `7zzs`. -/
abbrev onw_at : Addr := 0x602970

theorem lt_len {j : Nat} (h : j < 73) : j < onw.length := onw_length ▸ h

theorem onw_0 : ∀ feat, Dec feat onw 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem onw_4 : ∀ feat, Dec feat onw 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem onw_5 : ∀ feat, Dec feat onw 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem onw_8 : ∀ feat, Dec feat onw 8 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem onw_13 : ∀ feat, Dec feat onw 13 (FV7z.mk (.cmovcc 5) 64 [gr 64 3, gr 64 7] 4) := by dec_rfl
theorem onw_17 : ∀ feat, Dec feat onw 17 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem onw_20 : ∀ feat, Dec feat onw 20 (FV7z.mk .call 64 [.rel 198615] 5) := by dec_rfl
theorem onw_25 : ∀ feat, Dec feat onw 25 (FV7z.mk .test 64 [gr 64 0, gr 64 0] 3) := by dec_rfl
theorem onw_28 : ∀ feat, Dec feat onw 28 (FV7z.mk (.jcc 4) 64 [.rel 2] 2) := by dec_rfl
theorem onw_30 : ∀ feat, Dec feat onw 30 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem onw_31 : ∀ feat, Dec feat onw 31 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem onw_64 : ∀ feat, Dec feat onw 64 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem onw_68 : ∀ feat, Dec feat onw 68 (FV7z.mk .jmp 64 [.rel 18446744073709551543] 5) := by dec_rfl

theorem tgt_20 : onw_at.add (20 + 5) + BitVec.ofNat 64 198615 = mnx_at := by decide

/-! ## The stretch to the `call` -/

/-- `endbr64`, `push rbx`, `test rdi, rdi`, `mov ebx, 1`, `cmovne rbx, rdi`, `mov rdi, rbx`. -/
def ob : List Op := [Op.nop, Op.push 3, Op.test 64 7 (.r 7), Op.mov 32 3 (.i 1), Op.cmov64 5 3 7, Op.mov 64 7 (.r 3)]

theorem blk_0 (prof : Profile) : Blk prof onw 0 20 ob :=
  .cons (onw_0 _) OpI.endbr (by decide) <|
  .cons (onw_4 _) OpI.push (by decide) <|
  .cons (onw_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .cons (onw_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (onw_13 _) OpI.cmov64 (by decide) <|
  .cons (onw_17 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 20

/-- With `rdi ≠ 0`: `rbx = rdi` (the `cmovne` taken), `rsp` 8 less, the old `rbx` stored below `rsp`. -/
theorem vc_0 {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    {Q : Gprs → Rflags → (Addr → Byte) → Prop} (hn : g.rdi ≠ 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hQ : ∀ fl, Q { g with rbx := g.rdi, rsp := g.rsp - 8 } fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) :
    wp F Wl ob Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hst hQ ⊢
  have hz : (rdi == 0) = false := beq_false_of_ne hn
  wpx [ob, BitVec.and_self, hz, Bool.not_false, ↓reduceIte]
  exact ⟨hst, fun _ => hQ _⟩

/-! ## The run -/

theorem b8 (S : Addr) (h : 232 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega
theorem b16 (S : Addr) (h : 232 ≤ S.toNat) : (S - 8 - 8).toNat = S.toNat - 16 := by bv_omega
theorem b232 (S : Addr) (h : 232 ≤ S.toNat) : (S - 8 - 8 - 216#64).toNat = S.toNat - 232 := by bv_omega
theorem u8 (S : Addr) : S - 8 - 8 + 8 = S - 8 := by bv_omega
theorem u16 (S : Addr) : S - 8 + 8 = S := by bv_omega

/-- A byte of `n` from `x` in the stack from `hi` to the slot of the return address. -/
theorem ft {Wl : List Rgn} {hi : Nat} {S x : Addr} (hS : S.toNat + 8 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < S.toNat + 8 → Foot Wl a) {i n : Nat} (hin : i < n)
    (h1 : hi ≤ x.toNat) (h2 : x.toNat + n ≤ S.toNat + 8) : Foot Wl (Addr.add x i) := by
  have e : (Addr.add x i).toNat = x.toNat + i := by
    unfold Addr.add; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact hsw _ (by omega) (by omega)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 2000000 in
/-- `operator new (n)`, `0 < n ≤ 1024`, after the first `malloc`: see the module doc. -/
theorem onw_hp {fb : Addr} {hi m : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L onw_at onw) (hinM : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = onw_at.add 64) (hH : Mal.Hp F Wl fb hi (m + 1072) V)
    (hn0 : X.cpu.gpr.rdi ≠ 0) (hn : X.cpu.gpr.rdi.toNat ≤ 1024)
    (hhi : hi + 232 ≤ X.cpu.gpr.rsp.toNat) (hR : X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 → Foot Wl a)
    {e' : Addr} {code : List Byte} {j : Nat} (hin₂ : CodeIn L e' code) (hj : j < code.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (kc : ∀ Z t' (V₂ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → fb.toNat + 64 ≤ p.toNat → p.toNat + X.cpu.gpr.rdi.toNat ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + X.cpu.gpr.rdi.toNat → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 224 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < p.toNat ∨ p.toNat + X.cpu.gpr.rdi.toNat ≤ a.toNat) → W a = V₂ a) → Mal.Hp F Wl fb hi m W) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hS8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64 := by omega
  have e8 := b8 X.cpu.gpr.rsp (by omega)
  have e16 := b16 X.cpu.gpr.rsp (by omega)
  have e232 := b232 X.cpu.gpr.rsp (by omega)
  -- `endbr64`, `jmp` to `0`
  refine c.s_endbr hK hA hin (lt_len (by decide)) hrip (onw_64 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jmp hK1 hA1 hin (lt_len (by decide)) hr1 (onw_68 _) (tgt := 0) (by decide) (lt_len (by decide)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  -- the stretch to the `call`
  refine c.s_blk hin (blk_0 prof) hK2 hA2 hr2 ?_
  rw [hg2, hg1]
  refine vc_0 hn0 (fun i hi' => ft hS8 hsw hi' (by rw [e8]; omega) (by rw [e8]; omega))
    fun _ Y3 t3 hK3 hA3 hr3 hg3 _ => ?_
  have hs3 : Y3.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg3]; try rfl
  -- `call malloc`
  refine c.s_call hK3 hA3 hin (lt_len (by decide)) hr3 (onw_20 _) hinM (by rw [mnx_length]; decide) tgt_20
    (fun i hi' => by rw [hs3]; exact ft hS8 hsw hi' (by rw [e16]; omega) (by rw [e16]; omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  rw [hs3] at hA4
  have hdi4 : Y4.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg4, hg3]; try rfl
  have hsp4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 := by rw [hg4, hs3]; try rfl
  have hbp4 : Y4.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg4, hg3]; try rfl
  have h124 : Y4.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg4, hg3]; try rfl
  have h134 : Y4.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg4, hg3]; try rfl
  have h144 : Y4.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg4, hg3]; try rfl
  have h154 : Y4.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg4, hg3]; try rfl
  -- the two stores (the old `rbx`, the return address) lie in `[rsp - 16, rsp)`
  have hV1 : ∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat →
      Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE (onw_at.add (20 + 5)) 8) a = V a := fun a ha => by
    have h1 : Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) a = V a :=
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)
    rw [← h1]
    exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (by rw [toBytesLE_length, e16]; omega)
  have hH4 : Mal.Hp F Wl fb hi (m + 1072) (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))
      (X.cpu.gpr.rsp - 8 - 8) (toBytesLE (onw_at.add (20 + 5)) 8)) :=
    Mal.Hp.mv hH (by omega) fun a _ h2 => hV1 a (.inl (by omega))
  refine Mal.mal_hp c hfs hinM hinI hK4 hA4 hr4 hH4 (by rw [hdi4]; exact hn) (by rw [hsp4, e16]; omega)
    (by rw [hsp4, e16]; omega)
    (fun i hi' => by
      rw [hsp4]
      exact ft hS8 hsw (n := 224) hi' (by rw [e232]; omega) (by rw [e232]; omega))
    hin (j := 25) (lt_len (by decide)) ?_ ?_
  · rw [hsp4, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 8 - 8) _ (toBytesLE_length _ _) (by rw [e16]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  intro Z t5 V₂ p hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z hp1 hp2 hpn hpF hV₂ hHp
  rw [hsp4, e16] at hV₂
  rw [hdi4] at hpn hpF hHp
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by decide)
  have hspZ' : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hspZ, hsp4]; exact u8 _
  -- `test rax, rax`, `je` not taken
  refine c.s_test_rr64 hKZ hAZ hin (lt_len (by decide)) hrZ (onw_25 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hz6⟩
  refine c.s_jcc_f hK6 hA6 hin (lt_len (by decide)) hr6 (onw_28 _) (by
    rw [cond_4, hz6]; simp only [rv, BitVec.setWidth_eq, BitVec.and_self]
    exact beq_false_of_ne (by rw [show Z.cpu.gpr.get (regOf 0) = Z.cpu.gpr.rax from rfl, haxZ]; exact hp0)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hsp7 : Y7.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg7, hg6]; exact hspZ'
  -- `pop rbx`
  refine c.s_pop hK7 hA7 hin (lt_len (by decide)) hr7 (onw_30 _)
    (fun i hi' => c.hws _ (by rw [hsp7]; exact ft hS8 hsw hi' (by rw [e8]; omega) (by rw [e8]; omega))) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hsp8 : Y8.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg8]; show Y7.cpu.gpr.rsp + 8 = _; rw [hsp7]; exact u16 _
  -- `ret`
  have hraZ : rdq(V₂, Y8.cpu.gpr.rsp) = e'.add j := by
    have h := Sbrk.rd_eq (V := V) (V' := V₂) (x := X.cpu.gpr.rsp) (n := 8) (by omega) fun a h1 h2 =>
      (hV₂ a (.inr (.inr ⟨by omega, .inr (by omega)⟩))).trans (hV1 a (.inr h1))
    rw [hsp8, h]
    exact hra
  refine c.s_ret hK8 hA8 hin (lt_len (by decide)) hr8 (onw_31 _)
    (fun i hi' => c.hws _ (by rw [hsp8]; exact ft hS8 hsw hi' (by omega) (by omega))) hin₂ hj hraZ ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hbx : rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    have h := Sbrk.rd_eq (V := Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (V' := V₂)
      (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [e8]; omega) fun a h1 h2 => by
        rw [e8] at h1 h2
        rw [hV₂ a (.inr (.inr ⟨by omega, .inr (by omega)⟩))]
        exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (.inr (by rw [toBytesLE_length, e16]; omega))
    rw [h, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 8) _ (toBytesLE_length _ _) (by rw [e8]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
  have hg8' : Y8.cpu.gpr = (Z.cpu.gpr.set 4 (Z.cpu.gpr.rsp + 8)).set (regOf 3) rdq(V₂, Z.cpu.gpr.rsp) := by
    rw [hg8, hg7, hg6]
  refine kc Y9 t9 V₂ p hK9 hA9 hr9 (by rw [hg9]; show Y8.cpu.gpr.rsp + 8 = _; rw [hsp8])
    (by rw [hg9, hg8']; exact haxZ) (by rw [hg9, hg8']; show rdq(V₂, Z.cpu.gpr.rsp) = _; rw [hspZ']; exact hbx)
    (by rw [hg9, hg8']; exact hbpZ.trans hbp4) (by rw [hg9, hg8']; exact h12Z.trans h124)
    (by rw [hg9, hg8']; exact h13Z.trans h134) (by rw [hg9, hg8']; exact h14Z.trans h144)
    (by rw [hg9, hg8']; exact h15Z.trans h154) hp1 hp2 hpn hpF (fun a ha => ?_) hHp
  have hpS : p.toNat + 232 ≤ X.cpu.gpr.rsp.toNat := by omega
  refine (hV₂ a ?_).trans (hV1 a ?_)
  · rcases ha with ha | ha | ⟨h1, ha | ha⟩
    · exact .inl ha
    · exact .inr (.inl ha)
    · exact .inr (.inr ⟨h1, .inl (by omega)⟩)
    · exact .inr (.inr ⟨h1, .inr (by omega)⟩)
  · rcases ha with ha | ha | ⟨h1, ha | ha⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr ha

end FV7z.Onw
