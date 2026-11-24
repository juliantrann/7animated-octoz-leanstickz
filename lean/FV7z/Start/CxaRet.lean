import FV7z.Start.ExitKeep
import FV7z.Start.CxaCall
/-!
# `__cxa_atexit (fini)` after the return of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_lif` ends at `0x613439` with the bytes `Cti.CtMem (Lif.bcV W₂ …)`; `StartB.lsb_cxa` runs from there to
the return of `__cxa_atexit (fini, NULL, NULL)`, given what it reads. Here those reads are taken back to the bytes
`W` at `0x613434` (`ExitKeep`) and then to `PtrW`'s bytes: the bss is 0, `__exit_funcs` is `&initial` and the TCB's
`multiple_threads` is 0 (`__sbrk` zeroed the page).

- `ptr_tz`: a byte of `TZ` is 0 at `0x613434`.
- `RetAt`: what the return to `0x613439` gives about the bytes, with the bounds the layers need.
- `ret_eq`, `ret_glob`, `ret_exit0`: the bytes `lsb_cxa` reads are those at `0x613434`; those of `ExitB` are 0.
- `ret_mt`: `multiple_threads` (`fs + 24`) is 0.
- `ret_cxa`: from `0x613439` to the return of `__cxa_atexit` at `0x61344a`, the list `initial` empty.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem WD WC T4 T3 T2 rd_ext)
open FV7z.StartB (GuardMem PtrMem)
open FV7z.Ndi (ExitB)

/-- A byte of `TZ` is 0 at `0x613434` (`PtrW`'s bytes): `__sbrk` zeroed the two pages and no later store reaches
it. -/
theorem ptr_tz {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 8192 + 448 < K.bp.toNat)
    (hW : PtrW K W V b ver D) {a : Addr} (ha : TZ b.toNat a.toNat) : W a = 0 := by
  unfold TZ at ha
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  have h1 : b.toNat ≤ a.toNat := by omega
  have h2 : a.toNat < b.toNat + 8192 := by omega
  rw [hW a (.inr ⟨h1, h2⟩) ?_ ?_]
  · unfold PtrMem VerMem GuardMem TlsMem WD WC T4 T3 T2
    rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
      Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
      Vst_out, Vz_in h1 h2]
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 at hj
    rcases hj with ⟨h3, -⟩ | hj
    · omega
    · exact not_junk2 (by omega) (by unfold CpuVar; omega) hj
  · unfold Pim.PimVar
    omega

/-- At the return of `__libc_init_first` to `0x613439` (`launch_to_lif`): `_dl_non_dynamic_init`'s bytes `W₂` from
`lif_ok`'s, the TLS block at `B` (the break at the launch) and the stacks above it. -/
structure RetAt (W W₂ : Addr → Byte) (Z : State) (B : Addr) (g : Gprs) : Prop where
  nd : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) (B + 4544#64) (B + 2176#64) W₂
  hb : 0x7a9000 ≤ B.toNat
  hb' : B.toNat + 8192 ≤ 2 ^ 63
  hsp : B.toNat + 8192 ≤ (lifSp Z).toNat
  hs : (lifSp Z).toNat + 168 ≤ 2 ^ 64
  he : B.toNat + 8192 ≤ (entG Z).rsp.toNat
  he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64
  hg : B.toNat + 8192 ≤ g.rsp.toNat

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- The bytes of `__cxa_atexit`'s variables, of `[0x791eb8, 0x792980)` and of the TCB's first 56 bytes at
`0x613439` are those at `0x613434`. -/
theorem RetAt.eq (h : RetAt W W₂ Z B g) {x : Addr}
    (hx : ExitB x ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ B.toNat + 2176 ≤ x.toNat ∧ x.toNat < B.toNat + 2232) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x = W x := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  rcases hx with hx | ⟨x1, x2⟩ | ⟨x1, x2⟩
  · exact exit_ret hx h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega) (by omega)
      (by omega)
  · exact glob_ret x1 x2 h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega) (by omega)
      (by omega)
  · exact tcb_ret (by omega) (by omega) h.nd (by omega) (by omega) (by omega) (by omega) h.he' (by omega)
      (by omega) (by omega)

/-- `n` bytes of `[0x791eb8, 0x792980)` from `x` at `0x613439` are those at `0x613434`. -/
theorem RetAt.glob (h : RetAt W W₂ Z B g) {x : Addr} {n : Nat}
    (hx : ∀ i < n, 7937720 ≤ (x.add i).toNat ∧ (x.add i).toNat < 7940480) :
    List.map (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (byteAddrs x n) = List.map W (byteAddrs x n) :=
  rd_ext x n fun i hi => h.eq (.inr (.inl (hx i hi)))

/-- `n` bytes from `x.toNat = c` inside one of `ExitB`'s two ranges are each in `ExitB`. -/
theorem exitB_at {x : Addr} {c n : Nat} (hxt : x.toNat = c)
    (h : 8010388 ≤ c ∧ c + n ≤ 8011440 ∨ 8029184 ≤ c ∧ c + n ≤ 8029200) : ∀ i < n, ExitB (x.add i) := by
  intro i hi
  unfold ExitB
  rw [toNat_add_of_fits hi (by omega), hxt]
  omega

/-- Bytes of `ExitB` at `0x613439` are 0, as in the image's bss. -/
theorem RetAt.exit0 {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} (h : RetAt W W₂ Z B g) (hK : K.Ok)
    (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True)) {x : Addr} {n : Nat}
    (hx : ∀ i < n, ExitB (x.add i)) :
    List.map (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (byteAddrs x n) = List.replicate n 0 :=
  rd_zero fun i hi => by
    rw [h.eq (.inl (hx i hi))]
    exact ptr_exit hK hB hM h.hb h.hb' hW (hx i hi) trivial

/-- `multiple_threads` (`fs + 24`) at `0x613439` is 0. -/
theorem RetAt.mt {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} {D : Addr → Prop} (h : RetAt W W₂ Z B g)
    (hbp : B.toNat + 8192 + 448 < K.bp.toNat) (hW : PtrW K W V B ver D) :
    rdd(Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3, B + 2176#64 + 24#64) = 0 := by
  have := h.hb; have := h.hb'
  have hx : (B + 2176#64 + 24#64).toNat = B.toNat + 2200 := by bv_omega
  have hz : ∀ i < 4, Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 ((B + 2176#64 + 24#64).add i) = 0 := by
    intro i hi
    have t : ((B + 2176#64 + 24#64).add i).toNat = B.toNat + 2200 + i := by
      rw [toNat_add_of_fits hi (by omega), hx]
    rw [h.eq (.inr (.inr ⟨by omega, by omega⟩))]
    exact ptr_tz h.hb h.hb' hbp hW (by rw [t]; unfold TZ; omega)
  rw [rd_zero hz]
  rfl

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

/-- From the return of `__libc_init_first` to `0x613439` (`launch_to_lif`) to the return of `__cxa_atexit (fini,
NULL, NULL)` at `0x61344a`: `fini` (`r12` at `0x613434`) is not null, `__exit_funcs` is `&initial` (`0x7a3aa0`),
`initial` is empty and its lock free, so its first place (`0x7a3ab0`) is filled (`Cxa.Reg`). -/
theorem ret_cxa {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = B + 2176#64) (hl : CodeIn L lsm_at lsm) (hin : CodeIn L Cxa.cxa_at Cxa.cxa)
    (hinn : CodeIn L Nef.nef_at Nef.nef) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3))
    (hrip : X.cpu.rip = lsm_at.add 1017) (hsp : X.cpu.gpr.rsp = lifSp Z + 160#64)
    (h12 : X.cpu.gpr.r12 = rdq(lifW W Z, lifSp Z + 136#64)) (hfin : Z.cpu.gpr.r12 ≠ 0#64)
    (h : RetAt W W₂ Z B g) (hKo : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V)
    (hW : PtrW K W V B ver (fun _ => True)) (hbp : B.toNat + 8192 + 448 < K.bp.toNat)
    (hst : ∀ i < 64, Foot Wl (Addr.add (lifSp Z + 152#64 - 56#64) i))
    (hft : ∀ i < 56, Foot F.data (Addr.add (B + 2176#64) i)) (hfl : ∀ i < 1, Foot F.data (Addr.add 8010388#64 i))
    (hp : ∀ i < 8, Foot F.data (Addr.add 7938992#64 i)) (hlw : ∀ i < 1040, Foot Wl (Addr.add 8010400#64 i))
    (hkw : ∀ i < 16, Foot Wl (Addr.add 8029184#64 i))
    (k : ∀ V' g' Z' t', KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' →
      Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
          (toBytesLE (lsm_at.add 1034) 8)) V' (lifSp Z + 152#64) 8010400#64 8010416#64 0
        ((X.cpu.gpr.r12 ^^^ rdq(Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3, B + 2176#64 + 48#64)).rotateLeft
          17) 0 0 →
      Z'.cpu.rip = lsm_at.add 1034 → Z'.cpu.gpr = g' → g'.rax = 0 →
      Osv.Back (X.cpu.gpr.set 4 (lifSp Z + 152#64)) g' → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he
  have hf : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have hq : (lifSp Z + 152#64).toNat = (lifSp Z).toNat + 152 := by bv_omega
  have tl : (8010400#64 : Addr).toNat = 8010400 := rfl
  have hr12 : X.cpu.gpr.r12 ≠ 0#64 := by
    rw [h12, lif_r12 (by omega)]
    exact hfin
  refine StartB.lsb_cxa (fb := B + 2176#64) (sp := lifSp Z + 152#64) (l := 8010400#64) (p := 8010416#64) (n := 0) c
    hfs hl hin hinn hK hA hrip (by rw [hsp]; bv_omega) hr12 hst (by omega) (by omega) hft (by omega) (by omega)
    (by omega) (by omega) (h.mt hbp hW) hfl ?_ hp ?_ (by decide) (by decide) (by decide) hlw (by omega) hkw
    (by omega) (by omega) ?_ ?_ ?_ (fun h0 => absurd h0 (by decide)) k
  · show ofBytesLE 8 (List.map _ (byteAddrs 8010388#64 1)) = 0
    rw [h.exit0 hKo hB hM hW (exitB_at (x := 8010388#64) (n := 1) (c := 8010388) rfl (.inl ⟨by omega, by omega⟩))]
    rfl
  · have t0 : (7938992#64 : Addr).toNat = 7938992 := rfl
    rw [h.glob (x := 7938992#64) (n := 8) fun i hi => by
      rw [toNat_add_of_fits hi (by omega), t0]; exact ⟨by omega, by omega⟩]
    exact ptr_ef hKo hI hM h.hb h.hb' hW fun _ _ => trivial
  · show ofBytesLE 32 (List.map _ (byteAddrs 8029184#64 4)) = 0
    rw [h.exit0 hKo hB hM hW (exitB_at (x := 8029184#64) (n := 4) (c := 8029184) rfl
      (.inr ⟨by omega, by omega⟩))]
    rfl
  · show ofBytesLE 64 (List.map _ (byteAddrs (8010400#64 + 8#64) 8)) = _
    rw [h.exit0 hKo hB hM hW (exitB_at (x := 8010400#64 + 8#64) (n := 8) (c := 8010408) rfl
      (.inl ⟨by omega, by omega⟩))]
    rfl
  · intro _
    show ofBytesLE 64 (List.map _ (byteAddrs 8010400#64 8)) = 0
    rw [h.exit0 hKo hB hM hW (exitB_at (x := 8010400#64) (n := 8) (c := 8010400) rfl (.inl ⟨by omega, by omega⟩))]
    rfl

end FV7z.Start
