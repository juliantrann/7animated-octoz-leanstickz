import FV7z.Ctor.CxM
/-!
# Calls to the mutex's set-up and `__cxa_atexit` inside a constructor (PLAN.md §M, constructors)

- `mx_mid`, `cx_mid`: a `call CriticalSection_Init` (`Mxi.mx_ok`) or `call __cxa_atexit` (`Cxa.cxa_ok`) at an offset
  of `sti`, back at the next instruction with the stack pointer as before the call and the registers a call keeps.
- `CxPre.reg`: `__cxa_atexit`'s stores give `CxPre` for one place more.
- `csuTg 99` (`0x41ccf0`): `endbr64; push rbp; lea rdi, M₁; call CriticalSection_Init; mov rbp, D; lea rdx,
  __dso_handle; lea rsi, M₁; mov rdi, rbp; call __cxa_atexit; lea rdi, M₂; call CriticalSection_Init; mov rdi, rbp;
  pop rbp; lea rdx, __dso_handle; lea rsi, M₂; jmp __cxa_atexit` with the mutexes `M₁ = 0x79f060`, `M₂ = 0x79f020`:
  `c99_runs`, `c99_jg`.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)

theorem m8n (R : Addr) (h : 64 ≤ R.toNat) : (R - 8).toNat = R.toNat - 8 := by bv_omega
theorem m8s (R : Addr) : R - 8 = R - 64#64 + BitVec.ofNat 64 56 := by bv_omega
theorem m8l (R : Addr) : R - 8 - 56#64 = R - 64#64 + BitVec.ofNat 64 0 := by bv_omega
theorem m8b (R : Addr) : R - 8 + 8#64 = R := by bv_omega

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## Calls inside a constructor -/

/-- `call CriticalSection_Init` at offset `q` of `sti` with `rdi = M` and the stack pointer `R`: back at `q + 5` with
`rsp = R`, the registers a call keeps, the bytes apart from the 64 below `R` and the mutex as before. -/
theorem mx_mid {R fb : Addr} {M q r : Nat} {X : State} {t : Nat} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L sti_at sti) (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs)
    (hinI : CodeIn L Mxi.mxi_at Mxi.mxi) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sti_at.add q) (hcd : Dec prof.feat sti q (FV7z.mk .call 64 [.rel r] 5))
    (htc : sti_at.add (q + 5) + BitVec.ofNat 64 r = Mxs.mxs_at) (hq : q + 5 < sti.length)
    (hsp : X.cpu.gpr.rsp = R) (hdi : X.cpu.gpr.rdi = BitVec.ofNat 64 M) (hR : 64 ≤ R.toNat)
    (hst : ∀ i < 64, Foot Wl (Addr.add (R - 64#64) i)) (hM0 : 0 < M) (hMn : M + 40 < 2 ^ 64)
    (hmw : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 M) i))
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 56 ≤ R.toNat - 64 ∨ R.toNat ≤ fb.toNat) (hfM : fb.toNat + 56 ≤ M ∨ M + 40 ≤ fb.toNat)
    (hMd : M + 40 ≤ R.toNat - 64 ∨ R.toNat ≤ M)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (R.toNat - 64 ≤ a.toNat ∧ a.toNat < R.toNat) → ¬ (M ≤ a.toNat ∧ a.toNat < M + 40) →
        V' a = V a) →
      Z.cpu.rip = sti_at.add (q + 5) → Z.cpu.gpr.rsp = R → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := R.isLt
  have n8 := m8n R hR
  have eM : (BitVec.ofNat 64 M).toNat = M := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e40 := f40 fb hfn
  refine c.s_call hK hA hin (by omega) hrip hcd hinM (Mxs.lt_len (j := 0) (by decide)) htc
    (by rw [hsp]; exact off_ft hst 56 (m8s R) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = R - 8 := by rw [hg₂]; show X.cpu.gpr.rsp - 8 = _; rw [hsp]
  have hdi₂ : Y₂.cpu.gpr.rdi = BitVec.ofNat 64 M := by rw [hg₂]; exact hdi
  have hc₂ : Cs X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hV₀ : ∀ a : Addr, ¬ (R.toNat - 8 ≤ a.toNat ∧ a.toNat < R.toNat) →
      Vst V (R - 8) (toBytesLE (sti_at.add (q + 5)) 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n8]; omega) (by rw [n8]; omega)
  refine Mxi.mx_ok c hfs hinM hinI hK₂ hA₂ hr₂ (fun h => by
      have := congrArg BitVec.toNat (hdi₂.symm.trans h)
      rw [eM] at this
      simp at this
      omega)
    (by rw [hsp₂, n8]; omega) (by rw [hsp₂, n8]; omega) (by rw [hsp₂]; exact off_ft hst 0 (m8l R) (by omega))
    (by rw [hsp₂]; exact fun i hi => c.hws _ (off_ft hst 56 (m8s R) (by omega) i hi))
    (off_ft hft 40 rfl (by decide)) (by rw [e40]; omega) (by rw [hsp₂, n8, e40]; omega)
    (by rw [hdi₂, eM, e40]; omega) (by rw [hdi₂]; exact hmw) (by rw [hdi₂, eM]; omega)
    (by rw [hdi₂, eM, hsp₂, n8]; omega) (j₂ := q + 5) hin hq
    (by rw [hsp₂, Sga.vs (a := R - 8) (n := 8) (toBytesLE_length _ _) (by rw [n8]; omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro V₁ Z₁ t₃ hKZ hAZ hout hrZ hB
  rw [hsp₂, hdi₂, n8, eM] at hout
  exact k V₁ Z₁ t₃ hKZ hAZ (fun a h1 h2 => (hout a (by omega) h2).trans (hV₀ a (by omega))) hrZ
    (by rw [hB.1, hsp₂, m8b]) (Cs.trans hc₂ hB.2)

/-- `call __cxa_atexit` at offset `q` of `sti` with the stack pointer `R`: back at `q + 5` with `rsp = R` and the
registers a call keeps; the bytes `V₁` with the return address pushed, and `__cxa_atexit`'s stores (`Cxa.Reg`). -/
theorem cx_mid {R fb l : Addr} {q r n : Nat} {fn arg dso : BitVec 64} {X : State} {t : Nat} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti) (hfs : s₀.cpu.seg.fsBase = fb)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sti_at.add q) (hcd : Dec prof.feat sti q (FV7z.mk .call 64 [.rel r] 5))
    (htc : sti_at.add (q + 5) + BitVec.ofNat 64 r = Cxa.cxa_at) (hq : q + 5 < sti.length)
    (hsp : X.cpu.gpr.rsp = R) (hdi : X.cpu.gpr.rdi = fn) (hsi : X.cpu.gpr.rsi = arg) (hdx : X.cpu.gpr.rdx = dso)
    (hR : 64 ≤ R.toNat) (hst : ∀ i < 64, Foot Wl (Addr.add (R - 64#64) i)) (h0 : fn ≠ 0)
    (hX : CxPre fb l n V) (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ R.toNat ∨ R.toNat ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : l ≠ 0) (hn : n < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1104 ≤ R.toNat) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hcR : 8029264 ≤ R.toNat) (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat)
    (k : ∀ V₁ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (R.toNat - 8 ≤ a.toNat ∧ a.toNat < R.toNat) → V₁ a = V a) →
      Cxa.Reg V₁ V' (R - 8) l (l + BitVec.ofNat 64 (16 + 32 * n)) n ((fn ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) arg
        dso →
      Z.cpu.rip = sti_at.add (q + 5) → Z.cpu.gpr.rsp = R → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := R.isLt
  have n8 := m8n R hR
  refine c.s_call hK hA hin (by omega) hrip hcd hinC (Cxa.lt_len (j := 0) (by decide)) htc
    (by rw [hsp]; exact off_ft hst 56 (m8s R) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂
  have hsp₂ : Y₂.cpu.gpr.rsp = R - 8 := by rw [hg₂]; show X.cpu.gpr.rsp - 8 = _; rw [hsp]
  have hc₂ : Cs X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hV₀ : ∀ a : Addr, ¬ (R.toNat - 8 ≤ a.toNat ∧ a.toNat < R.toNat) →
      Vst V (R - 8) (toBytesLE (sti_at.add (q + 5)) 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n8]; omega) (by rw [n8]; omega)
  have hX₁ := hX.kept hn hfn (by omega) fun a ha => hV₀ a (by unfold CxR at ha; omega)
  refine Cxa.cxa_ok (sp := R - 8) (l := l) (p := l + BitVec.ofNat 64 (16 + 32 * n)) (n := n)
    (fn := fn) (arg := arg) (dso := dso) c hfs hinC hinN hK₂ hA₂ hr₂ hsp₂ (by rw [hg₂]; exact hdi)
    (by rw [hg₂]; exact hsi) (by rw [hg₂]; exact hdx) (off_ft hst 0 (m8l R) (by omega))
    (fun i hi => c.hws _ (off_ft hst 56 (m8s R) (by omega) i hi)) hin (j₂ := q + 5) hq ?_ (by rw [n8]; omega) h0
    hft hfn (by rw [n8]; omega) hfld hfcd hX₁.mt hfl hX₁.flag hp hX₁.ptr hl0 hn rfl hlw (by rw [n8]; omega) hkw
    (by rw [n8]; omega) hlc hX₁.lock hX₁.idx hX₁.next hX₁.prev ?_
  · rw [Sga.vs (a := R - 8) (n := 8) (toBytesLE_length _ _) (by rw [n8]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro V' g' Z t' hKZ hAZ hRg hrZ hgZ _ hBk
  exact k _ V' Z t' hKZ hAZ hV₀ hRg hrZ (by rw [hgZ, hBk.1, hsp₂, m8b]) (Cs.trans hc₂ (by rw [hgZ]; exact hBk.2))

theorem pn (l : Addr) (n : Nat) (hn : n + 1 < 32) :
    l + BitVec.ofNat 64 (16 + 32 * (n + 1)) - 32#64 = l + BitVec.ofNat 64 (16 + 32 * n) := by bv_omega

/-- `__cxa_atexit`'s stores (`Cxa.Reg`, the place `n`) give `CxPre` for `n + 1`: the count and the lock from `Reg`,
the last place taken now `n`'s (flavor 4), the other bytes apart from the stores. -/
theorem CxPre.reg {fb l sp : Addr} {n : Nat} {fn arg dso : BitVec 64} {V V' : Addr → Byte} (h : CxPre fb l n V)
    (hR : Cxa.Reg V V' sp l (l + BitVec.ofNat 64 (16 + 32 * n)) n fn arg dso) (hn : n + 1 < 32)
    (hfn : fb.toNat + 56 ≤ 2 ^ 64) (hl : l.toNat + 1040 ≤ 2 ^ 64)
    (hfs : fb.toNat + 56 ≤ sp.toNat - 56 ∨ sp.toNat ≤ fb.toNat) (h56 : 56 ≤ sp.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hgs : 8029200 ≤ sp.toNat - 56) (hls : l.toNat + 1040 ≤ sp.toNat - 56)
    (hlg : 8010389 ≤ l.toNat ∨ l.toNat + 1040 ≤ 7938992) :
    CxPre fb l (n + 1) V' := by
  obtain ⟨f24, -⟩ := Cxa.f_c fb hfn
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) hl
  have hk : ∀ a : Addr, CxR fb l a.toNat → ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 1040) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V' a = V a := fun a h1 h2 h3 =>
    hR.out a (by unfold CxR at h1; omega) (by omega) (by rw [ep]; omega) h3
  refine ⟨?_, ?_, ?_, hR.lock, hR.idx, fun h0 => absurd h0 (by omega), fun _ => ?_⟩
  · exact (rdd_eq (x := fb + 24#64) (by rw [f24]; omega) fun a h1 h2 => hk a
      (by rw [f24] at h1 h2; unfold CxR; omega) (by rw [f24] at h1 h2; omega) (by rw [f24] at h1 h2; omega)).trans
      h.mt
  · exact (congrArg (ofBytesLE 8) (Csu.rd_in (lo := 8010388) (hi := 8010389) (x := 8010388#64) (n := 1)
      (fun a ha => hk a (by unfold CxR; omega) (by omega) (by omega)) (by decide) (by decide) (by decide))).trans
      h.flag
  · exact (rdq_eq (x := 7938992#64) (by decide) fun a h1 h2 => by
      simp only [show (7938992#64 : Addr).toNat = 7938992 from rfl] at h1 h2
      exact hk a (by unfold CxR; omega) (by omega) (by omega)).trans h.ptr
  · rw [pn l n hn, hR.flv]
    decide

/-! ## `csuTg 99` -/

/-- `csuTg 99`, at `0x41ccf0`: the mutexes `0x79f060` and `0x79f020`. -/
def c2992 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x8d, 0x3d, 0x64, 0x23, 0x38, 0x00, 0xe8, 0x3f, 0xbe, 0x02,
  0x00, 0x48, 0xc7, 0xc5, 0x20, 0xa6, 0x59, 0x00, 0x48, 0x8d, 0x15, 0x19, 0x54, 0x37, 0x00, 0x48,
  0x8d, 0x35, 0x4a, 0x23, 0x38, 0x00, 0x48, 0x89, 0xef, 0xe8, 0x72, 0x69, 0x20, 0x00, 0x48, 0x8d,
  0x3d, 0xfb, 0x22, 0x38, 0x00, 0xe8, 0x16, 0xbe, 0x02, 0x00, 0x48, 0x89, 0xef, 0x5d, 0x48, 0x8d,
  0x15, 0xf3, 0x53, 0x37, 0x00, 0x48, 0x8d, 0x35, 0xe4, 0x22, 0x38, 0x00, 0xe9, 0x4f, 0x69, 0x20,
  0x00]
theorem c2992_0 : ∀ feat, Dec feat c2992 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c2992_4 : ∀ feat, Dec feat c2992 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem c2992_5 : ∀ feat, Dec feat c2992 5 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3679076 0)] 7) := by dec_rfl
theorem c2992_12 : ∀ feat, Dec feat c2992 12 (FV7z.mk .call 64 [.rel 179775] 5) := by dec_rfl
theorem c2992_17 : ∀ feat, Dec feat c2992 17 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.i 5875232)] 7) := by dec_rfl
theorem c2992_24 : ∀ feat, Dec feat c2992 24 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3626009 0)] 7) := by dec_rfl
theorem c2992_31 : ∀ feat, Dec feat c2992 31 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3679050 0)] 7) := by dec_rfl
theorem c2992_38 : ∀ feat, Dec feat c2992 38 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem c2992_41 : ∀ feat, Dec feat c2992 41 (FV7z.mk .call 64 [.rel 2124146] 5) := by dec_rfl
theorem c2992_46 : ∀ feat, Dec feat c2992 46 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3678971 0)] 7) := by dec_rfl
theorem c2992_53 : ∀ feat, Dec feat c2992 53 (FV7z.mk .call 64 [.rel 179734] 5) := by dec_rfl
theorem c2992_58 : ∀ feat, Dec feat c2992 58 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem c2992_61 : ∀ feat, Dec feat c2992 61 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem c2992_62 : ∀ feat, Dec feat c2992 62 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3625971 0)] 7) := by dec_rfl
theorem c2992_69 : ∀ feat, Dec feat c2992 69 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3678948 0)] 7) := by dec_rfl
theorem c2992_76 : ∀ feat, Dec feat c2992 76 (FV7z.mk .jmp 64 [.rel 2124111] 5) := by dec_rfl
theorem v2992 : c2992 <+: sti.drop 2992 := by decide +kernel
theorem tg99 : csuTg 99 = sti_at.add 2992 := by decide +kernel

theorem bq2992 (prof : Profile) : BlkA prof c2992 (0x41ccf0 : Addr) 0 12
    [Op.nop, Op.push 5, Op.mov 64 7 (.i 7991392)] :=
  .cons (c2992_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c2992_4 _) ((OpI.push).at _) (by decide) <|
  .cons (c2992_5 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 12
theorem b2992 (prof : Profile) : BlkA prof sti sti_at 2992 3004 [Op.nop, Op.push 5, Op.mov 64 7 (.i 7991392)] :=
  (bq2992 prof).shift (by decide) v2992
theorem cd3004 (feat : Features) : Dec feat sti 3004 (FV7z.mk .call 64 [.rel 179775] 5) :=
  Dec.shift (j := 2992) (k := 12) (c2992_12 feat) v2992 (by decide)
theorem bq3009 (prof : Profile) : BlkA prof c2992 (0x41ccf0 : Addr) 17 41
    [Op.mov 64 5 (.i 5875232), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991392), Op.mov 64 7 (.r 5)] :=
  .cons (c2992_17 _) ((OpI.mov (.i 5875232) (.inr rfl)).at _) (by decide) <|
  .cons (c2992_24 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2992_31 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2992_38 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <| .nil 41
theorem b3009 (prof : Profile) : BlkA prof sti sti_at 3009 3033
    [Op.mov 64 5 (.i 5875232), Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991392), Op.mov 64 7 (.r 5)] :=
  (bq3009 prof).shift (by decide) v2992
theorem cd3033 (feat : Features) : Dec feat sti 3033 (FV7z.mk .call 64 [.rel 2124146] 5) :=
  Dec.shift (j := 2992) (k := 41) (c2992_41 feat) v2992 (by decide)
theorem bq3038 (prof : Profile) : BlkA prof c2992 (0x41ccf0 : Addr) 46 53 [Op.mov 64 7 (.i 7991328)] :=
  .cons (c2992_46 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 53
theorem b3038 (prof : Profile) : BlkA prof sti sti_at 3038 3045 [Op.mov 64 7 (.i 7991328)] :=
  (bq3038 prof).shift (by decide) v2992
theorem cd3045 (feat : Features) : Dec feat sti 3045 (FV7z.mk .call 64 [.rel 179734] 5) :=
  Dec.shift (j := 2992) (k := 53) (c2992_53 feat) v2992 (by decide)
theorem bq3050 (prof : Profile) : BlkA prof c2992 (0x41ccf0 : Addr) 58 76
    [Op.mov 64 7 (.r 5), Op.pop 5, Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991328)] :=
  .cons (c2992_58 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (c2992_61 _) ((OpI.pop).at _) (by decide) <|
  .cons (c2992_62 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (c2992_69 _) (OpIA.lea_rip (by decide)) (by decide) <| .nil 76
theorem b3050 (prof : Profile) : BlkA prof sti sti_at 3050 3068
    [Op.mov 64 7 (.r 5), Op.pop 5, Op.mov 64 2 (.i 7938344), Op.mov 64 6 (.i 7991328)] :=
  (bq3050 prof).shift (by decide) v2992
theorem jd3068 (feat : Features) : Dec feat sti 3068 (FV7z.mk .jmp 64 [.rel 2124111] 5) :=
  Dec.shift (j := 2992) (k := 76) (c2992_76 feat) v2992 (by decide)
theorem tc3004 : sti_at.add (3004 + 5) + BitVec.ofNat 64 179775 = Mxs.mxs_at := by decide +kernel
theorem tc3033 : sti_at.add (3033 + 5) + BitVec.ofNat 64 2124146 = Cxa.cxa_at := by decide +kernel
theorem tc3045 : sti_at.add (3045 + 5) + BitVec.ofNat 64 179734 = Mxs.mxs_at := by decide +kernel
theorem tj3068 : sti_at.add (3068 + 5) + BitVec.ofNat 64 2124111 = Cxa.cxa_at.add 0 := by decide +kernel

theorem e72 (sp : Addr) : sp - 64#64 - 8 = sp - 72#64 := by bv_omega
theorem e72n (sp : Addr) (h : 72 ≤ sp.toNat) : (sp - 72#64).toNat = sp.toNat - 72 := by bv_omega
theorem e72s (sp : Addr) : sp - 72#64 = sp - 136#64 + BitVec.ofNat 64 64 := by bv_omega
theorem e72m (sp : Addr) : sp - 72#64 - 64#64 = sp - 136#64 + BitVec.ofNat 64 0 := by bv_omega
theorem e72a (sp : Addr) : sp - 72#64 + 8 = sp - 64#64 := by bv_omega
theorem e72b (sp : Addr) : sp - 72#64 - 8 = sp - 80#64 := by bv_omega

theorem rdi_r5 (g : Gprs) : (wr g 7 (gv g 64 5)).rdi = g.rbp := by
  show (g.rbp.setWidth 64).setWidth 64 = g.rbp
  rw [sw_64_64, sw_64_64]

/-- `csuTg 99` is a function as `Csu.csu_ok` asks: `J m` gives what `__cxa_atexit` needs (`hpre`), and `J (m + 1)`
holds of the bytes after the first mutex's set-up (`V₁`, below the frame and to `M₁`), `__cxa_atexit`'s stores for
it (place `n`), the second mutex's set-up (`V₃`) and `__cxa_atexit`'s stores for it (place `n + 1`). -/
theorem c99_runs {J : Nat → (Addr → Byte) → Prop} {sp fb l : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m n : Nat} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2992)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfM : fb.toNat + 56 ≤ 7991328 ∨ 7991432 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hm1 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7991392) i))
    (hm2 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7991328) i))
    (hpre : ∀ W, J m W → CxPre fb l n W)
    (hJ : ∀ W V₁ V₂ V₃ V', J m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7991392 ≤ a.toNat ∧ a.toNat < 7991432) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7991392) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7991328 ≤ a.toNat ∧ a.toNat < 7991368) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7991328) 7938344#64 →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have hs8 := hC.s8
  have hsl := sp.isLt
  have n64 := Csu.sp_n hC.s0
  have n72 := e72n sp (by omega)
  have n80 := e80n sp (by omega)
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) (by omega)
  obtain ⟨-, -, ep', -, -, -⟩ := Nef.l_n l (n + 1) hn (by omega)
  have hl0' : l ≠ 0 := by rintro rfl; simp at hl0
  -- `endbr64; push rbp; lea rdi, M₁`
  have hpu : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by
    rw [hsp, e72]; exact off_ft hst 64 (e72s sp) (by omega)
  refine (Sp.blkA (b2992 prof)).run c hin (fun j' g' _ V' => j' = 3004 ∧
    g' = wr (X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) 7 (BitVec.ofNat 64 7991392) ∧
    V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (gv X.cpu.gpr 64 5) 8)) hK hA (hr.trans htg) ?_ ?_
  · intro _ _
    exact ⟨toBytesLE_length _ _, hpu, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₀ t₀ hK₀ hA₀ hr₀ hg₀ -
  have hVp : Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (gv X.cpu.gpr 64 5) 8) =
      Vst V (sp - 72#64) (toBytesLE X.cpu.gpr.rbp 8) := by
    rw [hsp, e72, show gv X.cpu.gpr 64 5 = X.cpu.gpr.rbp from sw_64_64 _]
  rw [hVp] at hA₀
  have hs₀ : Y₀.cpu.gpr.rsp = sp - 72#64 := by rw [hg₀]; show X.cpu.gpr.rsp - 8 = _; rw [hsp, e72]
  have hc₀ : Cs X.cpu.gpr Y₀.cpu.gpr := by rw [hg₀]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd₀ : Y₀.cpu.gpr.rdi = BitVec.ofNat 64 7991392 := by rw [hg₀]; exact sw_64_64 _
  have hpo : ∀ a : Addr, ¬ (sp.toNat - 72 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      Vst V (sp - 72#64) (toBytesLE X.cpu.gpr.rbp 8) a = V a := fun a ha =>
    Sga.vo (toBytesLE_length _ _) (by rw [n72]; omega) (by rw [n72]; omega)
  -- `call CriticalSection_Init` for `M₁`
  refine mx_mid (R := sp - 72#64) (M := 7991392) c hin hfs hinM hinI hK₀ hA₀ hr₀ (cd3004 _) tc3004
    (sti_lt (by decide)) hs₀ hd₀ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) (by decide)
    hm1 hft hfn (by rw [n72]; omega) (by omega) (by rw [n72]; omega) ?_
  intro V₁ Y₁ t₁ hK₁ hA₁ ho₁ hr₁ hs₁ hc₁
  rw [n72] at ho₁
  -- `mov rbp, D; lea rdx, __dso_handle; lea rsi, M₁; mov rdi, rbp`
  refine (Sp.blkA (b3009 prof)).run c hin (fun j' g' _ V' => j' = 3033 ∧
    g' = wr (wr (wr (wr Y₁.cpu.gpr 5 (BitVec.ofNat 64 5875232)) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 7991392)) 7 (gv (wr (wr (wr Y₁.cpu.gpr 5 (BitVec.ofNat 64 5875232)) 2
        (BitVec.ofNat 64 7938344)) 6 (BitVec.ofNat 64 7991392)) 64 5) ∧ V₁ = V') hK₁ hA₁ hr₁ ?_ ?_
  · intro _ _ _ _ _ _ _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hs₂ : Y₂.cpu.gpr.rsp = sp - 72#64 := by rw [hg₂]; exact hs₁
  have hbp₂ : Y₂.cpu.gpr.rbp = BitVec.ofNat 64 5875232 := by rw [hg₂]; exact sw_64_64 _
  have hd₂ : Y₂.cpu.gpr.rdi = BitVec.ofNat 64 5875232 := by rw [hg₂, rdi_r5]; exact sw_64_64 _
  have hx₂ : Y₂.cpu.gpr.rsi = BitVec.ofNat 64 7991392 := by rw [hg₂]; exact sw_64_64 _
  have hdx₂ : Y₂.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₂]; exact sw_64_64 _
  have hb₂ : Y₂.cpu.gpr.rbx = Y₁.cpu.gpr.rbx ∧ Y₂.cpu.gpr.r12 = Y₁.cpu.gpr.r12 ∧ Y₂.cpu.gpr.r13 = Y₁.cpu.gpr.r13 ∧
      Y₂.cpu.gpr.r14 = Y₁.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = Y₁.cpu.gpr.r15 := by
    rw [hg₂]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hX₁ : CxPre fb l n V₁ := (hpre V hI).kept (by omega) hfn (by omega) fun a ha =>
    (ho₁ a (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)).trans (hpo a (by unfold CxR at ha; omega))
  -- `call __cxa_atexit (D, M₁, __dso_handle)`
  refine cx_mid (R := sp - 72#64) c hin hfs hinC hinN hK₂ hA₂ hr₂ (cd3033 _) tc3033 (sti_lt (by decide)) hs₂ hd₂
    hx₂ hdx₂ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) hX₁ hft hfn
    (by rw [n72]; omega) hfld hfcd hfl hp hl0' (by omega) hlw (by rw [n72]; omega) hkw (by rw [n72]; omega)
    (by omega) ?_
  intro V₁' V₂ Y₃ t₃ hK₃ hA₃ hv₁ hR₁ hr₃ hs₃ hc₃
  rw [n72] at hv₁
  rw [e72b] at hR₁
  have hX₂ : CxPre fb l (n + 1) V₂ := (hX₁.kept (by omega) hfn (by omega) fun a ha =>
    hv₁ a (by unfold CxR at ha; omega)).reg hR₁ hn hfn (by omega) (by rw [n80]; omega) (by rw [n80]; omega) hfld
    hfcd (by rw [n80]; omega) (by rw [n80]; omega) (by omega)
  -- `lea rdi, M₂`
  refine (Sp.blkA (b3038 prof)).run c hin (fun j' g' _ V' => j' = 3045 ∧
    g' = wr Y₃.cpu.gpr 7 (BitVec.ofNat 64 7991328) ∧ V₂ = V') hK₃ hA₃ hr₃ ?_ ?_
  · intro _ _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hs₄ : Y₄.cpu.gpr.rsp = sp - 72#64 := by rw [hg₄]; exact hs₃
  have hd₄ : Y₄.cpu.gpr.rdi = BitVec.ofNat 64 7991328 := by rw [hg₄]; exact sw_64_64 _
  have hc₄ : Cs Y₃.cpu.gpr Y₄.cpu.gpr := by rw [hg₄]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `call CriticalSection_Init` for `M₂`
  refine mx_mid (R := sp - 72#64) (M := 7991328) c hin hfs hinM hinI hK₄ hA₄ hr₄ (cd3045 _) tc3045
    (sti_lt (by decide)) hs₄ hd₄ (by rw [n72]; omega) (off_ft hst 0 (e72m sp) (by omega)) (by decide) (by decide)
    hm2 hft hfn (by rw [n72]; omega) (by omega) (by rw [n72]; omega) ?_
  intro V₃ Y₅ t₅ hK₅ hA₅ ho₃ hr₅ hs₅ hc₅
  rw [n72] at ho₃
  -- `mov rdi, rbp; pop rbp; lea rdx, __dso_handle; lea rsi, M₂`
  have hpop : ∀ i < 8, Foot F.data (Addr.add Y₅.cpu.gpr.rsp i) := by
    rw [hs₅]; exact fun i hi => c.hws _ (off_ft hst 64 (e72s sp) (by omega) i hi)
  refine (Sp.blkA (b3050 prof)).run c hin (fun j' g' _ V' => j' = 3068 ∧
    g' = wr (wr (((wr Y₅.cpu.gpr 7 (gv Y₅.cpu.gpr 64 5)).set 4 (Y₅.cpu.gpr.rsp + 8)).set (regOf 5)
      ((ofBytesLE 64 (List.map V₃ (byteAddrs Y₅.cpu.gpr.rsp 8))).setWidth 64)) 2 (BitVec.ofNat 64 7938344)) 6
      (BitVec.ofNat 64 7991328) ∧ V₃ = V') hK₅ hA₅ hr₅ ?_ ?_
  · intro _ _
    exact ⟨hpop, fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  have h72 : rdq(V₃, sp - 72#64) = X.cpu.gpr.rbp := by
    refine (rdq_eq (V := Vst V (sp - 72#64) (toBytesLE X.cpu.gpr.rbp 8)) (x := sp - 72#64) (by rw [n72]; omega)
      fun a h1 h2 => ?_).trans ?_
    · rw [n72] at h1 h2
      rw [ho₃ a (by omega) (by omega), hR₁.out a (by rw [n80]; omega) (by omega) (by rw [ep]; omega) (by omega),
        hv₁ a (by omega)]
      exact ho₁ a (by omega) (by omega)
    · rw [Sga.vs (a := sp - 72#64) (n := 8) (toBytesLE_length _ _) (by rw [n72]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hs₆ : Y₆.cpu.gpr.rsp = sp - 64#64 := by rw [hg₆]; show Y₅.cpu.gpr.rsp + 8 = _; rw [hs₅, e72a]
  have hd₆ : Y₆.cpu.gpr.rdi = BitVec.ofNat 64 5875232 := by
    rw [hg₆]
    show (wr Y₅.cpu.gpr 7 (gv Y₅.cpu.gpr 64 5)).rdi = _
    rw [rdi_r5]
    exact hc₅.2.1.trans (hc₄.2.1.trans (hc₃.2.1.trans hbp₂))
  have hsi₆ : Y₆.cpu.gpr.rsi = BitVec.ofNat 64 7991328 := by rw [hg₆]; exact sw_64_64 _
  have hdx₆ : Y₆.cpu.gpr.rdx = BitVec.ofNat 64 7938344 := by rw [hg₆]; exact sw_64_64 _
  have hbp₆ : Y₆.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hg₆]
    show (ofBytesLE 64 (List.map V₃ (byteAddrs Y₅.cpu.gpr.rsp 8))).setWidth 64 = _
    rw [sw_64_64, hs₅]
    exact h72
  have hk₆ : Y₆.cpu.gpr.rbx = Y₅.cpu.gpr.rbx ∧ Y₆.cpu.gpr.r12 = Y₅.cpu.gpr.r12 ∧
      Y₆.cpu.gpr.r13 = Y₅.cpu.gpr.r13 ∧ Y₆.cpu.gpr.r14 = Y₅.cpu.gpr.r14 ∧ Y₆.cpu.gpr.r15 = Y₅.cpu.gpr.r15 := by
    rw [hg₆]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h25 : Cs Y₂.cpu.gpr Y₅.cpu.gpr := Cs.trans hc₃ (Cs.trans hc₄ hc₅)
  have h01 : Cs X.cpu.gpr Y₁.cpu.gpr := Cs.trans hc₀ hc₁
  have hcs₆ : Cs X.cpu.gpr Y₆.cpu.gpr :=
    ⟨hk₆.1.trans (h25.1.trans (hb₂.1.trans h01.1)), hbp₆,
      hk₆.2.1.trans (h25.2.2.1.trans (hb₂.2.1.trans h01.2.2.1)),
      hk₆.2.2.1.trans (h25.2.2.2.1.trans (hb₂.2.2.1.trans h01.2.2.2.1)),
      hk₆.2.2.2.1.trans (h25.2.2.2.2.1.trans (hb₂.2.2.2.1.trans h01.2.2.2.2.1)),
      hk₆.2.2.2.2.trans (h25.2.2.2.2.2.trans (hb₂.2.2.2.2.trans h01.2.2.2.2.2))⟩
  have hX₃ : CxPre fb l (n + 1) V₃ := hX₂.kept (by omega) hfn (by omega) fun a ha =>
    ho₃ a (by unfold CxR at ha; omega) (by unfold CxR at ha; omega)
  have hall : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7991328 ≤ a.toNat ∧ a.toNat < 7991432) → ¬ (l.toNat + 8 ≤ a.toNat ∧ a.toNat < l.toNat + 16) →
      ¬ (l.toNat + 16 + 32 * n ≤ a.toNat ∧ a.toNat < l.toNat + 48 + 32 * n) →
      ¬ (8029184 ≤ a.toNat ∧ a.toNat < 8029200) → V₃ a = V a := fun a h1 h2 h3 h4 h5 => by
    rw [ho₃ a (by omega) (by omega), hR₁.out a (by rw [n80]; omega) h3 (by rw [ep]; omega) h5, hv₁ a (by omega),
      ho₁ a (by omega) (by omega)]
    exact hpo a (by omega)
  -- `jmp __cxa_atexit (D, M₂, __dso_handle)`
  refine c.s_jmp_x hK₆ hA₆ hin (sti_lt (by decide)) hr₆ (jd3068 _) hinC (Cxa.lt_len (j := 0) (by decide)) tj3068 ?_
  rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
  refine Cxa.cxa_ok (sp := sp - 64#64) (l := l) (p := l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n := n + 1)
    (fn := BitVec.ofNat 64 5875232) (arg := BitVec.ofNat 64 7991328) (dso := 7938344#64) c hfs hinC hinN hK₇ hA₇
    (by rw [hr₇, addr_add_zero]) (by rw [hg₇]; exact hs₆) (by rw [hg₇]; exact hd₆) (by rw [hg₇]; exact hsi₆)
    (by rw [hg₇]; exact hdx₆) (off_ft hst 16 (e120 sp) (by omega)) (fun i hi => c.hws _ (hC.st i (by omega)))
    hC.code hj₂ ?_ (by rw [n64]; omega) (by decide) hft hfn (by rw [n64]; omega) hfld hfcd hX₃.mt hfl hX₃.flag hp
    hX₃.ptr hl0' hn rfl hlw (by rw [n64]; omega) hkw (by rw [n64]; omega) (.inl hlc) hX₃.lock hX₃.idx hX₃.next
    hX₃.prev ?_
  · exact (rdq_eq (V := V) (x := sp - 64#64) (by rw [n64]; omega) fun a h1 h2 => hall a
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)
      (by rw [n64] at h1 h2; omega) (by rw [n64] at h1 h2; omega)).trans hra
  intro V' g' Z t' hKZ' hAZ' hR₂ hrZ' hgZ _ hBk
  have hcs : Cs X.cpu.gpr Z.cpu.gpr := Cs.trans hcs₆ (by rw [hgZ]; rw [hg₇] at hBk; exact hBk.2)
  refine k Z t' V' hKZ' hAZ' (hJ V V₁' V₂ V₃ V' hI (fun a h1 h2 => ?_) hR₁ (fun a h1 h2 => ho₃ a (by omega)
    (by omega)) hR₂) (fun a ha => ?_) (fun a ha => ?_) hrZ' ⟨?_, hcs⟩
  · rw [hv₁ a (by omega), ho₁ a (by omega) (by omega)]
    exact hpo a (by omega)
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega)]
    exact hall a (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hR₂.out a (by rw [n64]; omega) (by omega) (by rw [ep']; omega) (by omega)]
    exact hall a (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [hgZ, hBk.1, hg₇, hs₆, hsp]

/-- The intervals of `csuTg 99`: its mutexes and the list's places `n`, `n + 1`. -/
def c99Wr (l : Addr) (n : Nat) : List (Nat × Nat) :=
  [(7991328, 7991368), (7991392, 7991432), (l.toNat + 16 + 32 * n, l.toNat + 16 + 32 * n + 64)]

/-- `c99_runs` for `Jg`, the spec `wrSpec (c99Wr l n)`, the shared words `cxSh l` in the spec of `k₀`. -/
theorem c99_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb l : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m n k₀ : Nat} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L Mxs.mxs_at Mxs.mxs) (hinI : CodeIn L Mxi.mxi_at Mxi.mxi)
    (hinC : CodeIn L Cxa.cxa_at Cxa.cxa) (hinN : CodeIn L Nef.nef_at Nef.nef) (htg : csuTg m = sti_at.add 2992)
    (hst : ∀ i < 72, Foot Wl (Addr.add (sp - 136#64) i)) (hS : 8029400 ≤ sp.toNat)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 120 ≤ sp.toNat - 136 ∨ sp.toNat ≤ fb.toNat)
    (hfM : fb.toNat + 56 ≤ 7991328 ∨ 7991432 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i))
    (hl0 : 8010389 ≤ l.toNat) (hn : n + 1 < 32) (hlw : ∀ i < 1040, Foot Wl (Addr.add l i))
    (hld : l.toNat + 1096 ≤ sp.toNat - 136) (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (hlc : l.toNat + 1040 ≤ 8029184)
    (hm1 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7991392) i))
    (hm2 : ∀ i < 40, Foot Wl (Addr.add (BitVec.ofNat 64 7991328) i))
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (c99Wr l n)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c99Wr l n, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hk₀ : 3 ≤ k₀) (hk₀m : k₀ < m) (hSh : ∀ x, InR (cxSh l) x → InR (spec k₀).wr x)
    (hP₀ : ∀ U, (spec k₀).post U)
    (hShD : ∀ k, 3 ≤ k → k < m → k ≠ k₀ → ∀ x, InR (spec k).wr x → ¬ InR (cxSh l) x)
    (hGx : ∀ W, G m W → CxPre fb l n W)
    (hG : ∀ W V₁ V₂ V₃ V', G m W →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7991392 ≤ a.toNat ∧ a.toNat < 7991432) → V₁ a = W a) →
      Cxa.Reg V₁ V₂ (sp - 80#64) l (l + BitVec.ofNat 64 (16 + 32 * n)) n
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₁, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7991392) 7938344#64 →
      (∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
        ¬ (7991328 ≤ a.toNat ∧ a.toNat < 7991368) → V₃ a = V₂ a) →
      Cxa.Reg V₃ V' (sp - 64#64) l (l + BitVec.ofNat 64 (16 + 32 * (n + 1))) (n + 1)
        ((BitVec.ofNat 64 5875232 ^^^ rdq(V₃, fb + 48#64)).rotateLeft 17) (BitVec.ofNat 64 7991328) 7938344#64 →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  have n64 := Csu.sp_n hC.s0
  have n80 := e80n sp (by omega)
  have hsl := sp.isLt
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n l n (by omega) (by omega)
  obtain ⟨-, -, ep', -, -, -⟩ := Nef.l_n l (n + 1) hn (by omega)
  refine c99_runs c hC hin hfs hinM hinI hinC hinN htg hst hS hft hfn hfsd hfM hfld hfcd hfl hp hl0 hn hlw hld hkw
    hlc hm1 hm2 (fun W hJ => hGx W hJ.2)
    fun W V₁ V₂ V₃ V' hJ hmo hR₁ ho₃ hR₂ => jg_sh hm hc (by omega) hspec hD hT hB hXw hk₀ hk₀m hSh hP₀ hShD
      (fun a h1 h2 h3 => ?_) (hG W V₁ V₂ V₃ V' · hmo hR₁ ho₃ hR₂) hJ
  rw [hR₂.out a (by rw [n64]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
      (fun h => h1 (by rw [ep'] at h; simp only [c99Wr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega)),
    ho₃ a (by omega) (fun h => h1 (by simp only [c99Wr, InR]; omega)),
    hR₁.out a (by rw [n80]; omega) (fun h => h3 (by simp only [cxSh, InR]; omega))
      (fun h => h1 (by rw [ep] at h; simp only [c99Wr, InR]; omega)) (fun h => h3 (by simp only [cxSh, InR]; omega))]
  exact hmo a (by omega) fun h => h1 (by simp only [c99Wr, InR]; omega)

end FV7z.Ctor
