import FV7z.Start.PtrGuard
import FV7z.Cxa.Holds
/-!
# `__libc_start_main` registers `fini` with `__cxa_atexit` (PLAN.md G3, startup)

glibc 2.31's `__libc_start_main` after `__libc_init_first` returns to `0x613439` (`lsm` 1017): `fini`
(`__libc_csu_fini`, kept in `r12`) is not null, so `__cxa_atexit (fini, NULL, NULL)` is called at `0x613445`
(`lsm` 1029) and returns to `0x61344a` (`lsm` 1034).

- `vc_1017`: the verification condition of the stretch to the call (`StartB/Cuts.lean`).
- `call_1029`: the `call` of `__cxa_atexit`.
- `rd_ra`: a read apart from the return address the `call` stores.
- `lsb_cxa`: the run from `0x613439` to the return of `__cxa_atexit`, with `Cxa.cxa_ok`'s conditions on the bytes
  before the call.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self)
open FV7z.Raf (off_ft)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- From `0x613439` to the call of `__cxa_atexit`, `fini` (`r12`) not null: its arguments `fini`, 0, 0. -/
theorem vc_1017 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h12 : g.r12 ≠ 0#64) :
    W_1017 fb F Wl (fun j' g' _ V' => j' = 1029 ∧ g' = { g with rdx := 0#64, rsi := 0#64, rdi := g.r12 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12
  have hb : (r12 &&& r12 == 0) = false := by rw [BitVec.and_self]; exact beq_false_of_ne h12
  wpx [W_1017, W_1022, o5, o6, Op.test, Op.xor, Op.mov]
  simp only [hb, BitVec.xor_self]
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · first | exact absurd h (by decide) | (rw [hb] at h; exact absurd h (by decide)) | simp_all
  · first | trivial | exact ⟨rfl, trivial⟩ | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩

/-- The `call` of `__cxa_atexit` in `__libc_start_main`. -/
def pc1029 : List Byte := [0xe8, 0x46, 0x02, 0x01, 0x00]
theorem pc1029_0 : ∀ feat, Dec feat pc1029 0 (FV7z.mk .call 64 [.rel 66118] 5) := by dec_rfl
theorem wc1029 : pc1029 <+: lsm.drop 1029 := by decide +kernel
theorem call_1029 (feat : Features) : Dec feat lsm 1029 (FV7z.mk .call 64 [.rel 66118] 5) :=
  Dec.shift (j := 1029) (k := 0) (pc1029_0 feat) wc1029 (Nat.zero_le _)

/-- A read apart from the 8 bytes stored at `s`. -/
theorem rd_ra {V : Addr → Byte} {s : Addr} {bs : List Byte} (x : Addr) (n : Nat) (hb : bs.length = 8)
    (hs : s.toNat + 8 ≤ 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64) (h : s.toNat + 8 ≤ x.toNat ∨ x.toNat + n ≤ s.toNat) :
    List.map (Vst V s bs) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_Vst _ _ _ _ _ (by rw [hb]; exact hs) hx (by rw [hb]; exact h)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- From `0x613439` to the return of `__cxa_atexit (fini, NULL, NULL)` at `0x61344a`, `fini` (`r12`) not null and
`__cxa_atexit`'s stack pointer `sp`: the conditions of `Cxa.cxa_ok` on the bytes `V` before the call (the list `l`
of `__exit_funcs` with `n < 32` places taken), and at the return the place `p` filled (`Cxa.Reg`, from the bytes with
the return address), `rax` 0 and the registers a call keeps as before the call. -/
theorem lsb_cxa {fb sp l p : Addr} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hl : CodeIn L lsm_at lsm) (hin : CodeIn L Cxa.cxa_at Cxa.cxa)
    (hinn : CodeIn L Nef.nef_at Nef.nef) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at.add 1017) (hsp : X.cpu.gpr.rsp = sp + 8#64) (h12 : X.cpu.gpr.r12 ≠ 0#64)
    (hst : ∀ i < 64, Foot Wl (Addr.add (sp - 56#64) i)) (hs56 : 56 ≤ sp.toNat) (hs16 : sp.toNat + 16 ≤ 2 ^ 64)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i)) (hfn : fb.toNat + 56 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 112 ≤ sp.toNat ∨ sp.toNat + 8 ≤ fb.toNat)
    (hfld : fb.toNat + 56 ≤ l.toNat ∨ l.toNat + 1040 ≤ fb.toNat)
    (hfcd : fb.toNat + 56 ≤ 8029184 ∨ 8029200 ≤ fb.toNat) (hmt : rdd(V, fb + 24#64) = 0)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i)) (hflag : rdb(V, 8010388#64) = 0)
    (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i)) (hlq : rdq(V, 7938992#64) = l) (hl0 : l ≠ 0)
    (hn : n < 32) (hpe : p = l + BitVec.ofNat 64 (16 + 32 * n))
    (hlw : ∀ i < 1040, Foot Wl (Addr.add l i)) (hld : l.toNat + 1096 ≤ sp.toNat)
    (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i)) (hcd : 8029256 ≤ sp.toNat)
    (hlc : l.toNat + 1040 ≤ 8029184 ∨ 8029200 ≤ l.toNat)
    (hlock : rdd(V, 8029184#64) = 0) (hidx : rdq(V, l + 8#64) = BitVec.ofNat 64 n)
    (hnext : n = 0 → rdq(V, l) = 0) (hprev : 0 < n → rdq(V, p - 32#64) ≠ 0)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Cxa.Reg (Vst V sp (toBytesLE (lsm_at.add 1034) 8)) V' sp l p n
        ((X.cpu.gpr.r12 ^^^ rdq(V, fb + 48#64)).rotateLeft 17) 0 0 →
      Z.cpu.rip = lsm_at.add 1034 → Z.cpu.gpr = g' → g'.rax = 0 → Osv.Back (X.cpu.gpr.set 4 sp) g' →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  subst hpe
  have e8 : ∀ i < 8, Foot Wl (Addr.add sp i) := off_ft hst 56 (by bv_omega) (by decide)
  have hb8 : (toBytesLE (lsm_at.add 1034) 8).length = 8 := toBytesLE_length _ _
  refine (c_1017 prof fb).run c hfs hl _ hK hA hrip (vc_1017 h12) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYs : Y.cpu.gpr.rsp - 8 = sp := by
    rw [hgY]
    show X.cpu.gpr.rsp - 8 = sp
    rw [hsp]
    bv_omega
  refine c.s_call hKY hAY hl (by rw [lsm_length]; decide) hrY (call_1029 _) hin
    (by rw [Cxa.cxa_length]; decide) (by decide) (fun i hi => by rw [hYs]; exact e8 i hi) ?_
  rintro Z₁ u₁ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hYs] at hAZ hgZ
  refine Cxa.cxa_ok (sp := sp) (l := l) (n := n) (fn := X.cpu.gpr.r12) (arg := 0) (dso := 0) (j₂ := 1034) c hfs hin
    hinn hKZ hAZ hrZ (by rw [hgZ]; rfl) (by rw [hgZ, hgY]; rfl) (by rw [hgZ, hgY]; rfl) (by rw [hgZ, hgY]; rfl)
    (fun i hi => hst i (by omega)) (fun i hi => c.hws _ (e8 i hi)) hl (by rw [lsm_length]; decide)
    (by rw [rd_Vst_self _ _ _ hb8 (by omega), ofBytesLE_toBytesLE (n := 8) rfl]) (by omega) h12 hft hfn
    (by omega) hfld hfcd ?_ hfl ?_ hp ?_ hl0 hn rfl hlw hld hkw hcd hlc ?_ ?_ ?_ ?_ ?_
  · rw [rd_ra (fb + 24#64) 4 hb8 (by omega) (by bv_omega) (by bv_omega)]
    exact hmt
  · rw [rd_ra 8010388#64 1 hb8 (by omega) (by decide) (by simp only [BitVec.toNat_ofNat]; omega)]
    exact hflag
  · rw [rd_ra 7938992#64 8 hb8 (by omega) (by decide) (by simp only [BitVec.toNat_ofNat]; omega)]
    exact hlq
  · rw [rd_ra 8029184#64 4 hb8 (by omega) (by decide) (by simp only [BitVec.toNat_ofNat]; omega)]
    exact hlock
  · rw [rd_ra (l + 8#64) 8 hb8 (by omega) (by bv_omega) (by bv_omega)]
    exact hidx
  · intro h0
    rw [rd_ra l 8 hb8 (by omega) (by omega) (by omega)]
    exact hnext h0
  · intro hn0
    rw [rd_ra (l + BitVec.ofNat 64 (16 + 32 * n) - 32#64) 8 hb8 (by omega) (by bv_omega) (by bv_omega)]
    exact hprev hn0
  intro V₂ g' Z t' hKZ' hAZ' hR hrZ' hgZ' hax hBk
  rw [rd_ra (fb + 48#64) 8 hb8 (by omega) (by bv_omega) (by bv_omega)] at hR
  rw [hgZ, hgY] at hBk
  exact k V₂ g' Z t' hKZ' hAZ' hR hrZ' hgZ' hax hBk

end FV7z.StartB
