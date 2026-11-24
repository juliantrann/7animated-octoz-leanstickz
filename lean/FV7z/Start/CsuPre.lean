import FV7z.Start.MainRet
import FV7z.Csu.Init
import FV7z.Csu.Fd
/-!
# The first three functions `__libc_csu_init` calls, from the launch (PLAN.md G3, startup)

`__libc_csu_init` calls `elision_init` (`.preinit_array`), `_init` and `frame_dummy` (the first word of
`.init_array`) before the 101 constructors of 7-Zip. `Csu.eli_runs`, `Csu.ini_runs` and `Csu.fd_runs` give their
`Csu.Runs` for an invariant whose `I 0` has the five `glibc.elision.*` tunables unset and the words `frame_dummy`
reads as in the file: `__EH_FRAME_BEGIN__`'s first word (not 0), `__pthread_force_elision`, `object_mutex` and
`any_objects_registered` (0, in `.bss`). Those bytes (`PreB`) are the launch image's at the return of `__cxa_atexit`:
no layer of the start code stores to them.

- `Ndi.CsuB`, `Ndi.ndi_csu`: the `.bss` words; `_dl_non_dynamic_init` keeps them.
- `csu_ret`, `RetAt.pre`, `RetAt.cnt`: a byte of `PreB` or of a registrar's count (`Ndi.CntN`) at `0x61344a` is the
  launch image's.
- `Agr`, `Near`, `preI`: for the first three functions the bytes of `PreB` as the image's and the bytes outside
  their stores as at `0x61344a`, and an invariant `J` of the constructors after them.
- `unset_of`, `pre_rd`, `pre_zero`: the tunables and the words from `Agr`.
- `pre_runs`: `Runs` for the functions 0, 1 and 2 with `preI`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (Lo)

namespace FV7z.Ndi

/-- The counts of the three registrars of 7-Zip's tables (`.bss`), by number: `0x79c8e0`, `0x79cb00`, `0x79f000`. -/
def CntN (n : Nat) : Prop :=
  7981280 ≤ n ∧ n < 7981284 ∨ 7981824 ≤ n ∧ n < 7981828 ∨ 7991296 ≤ n ∧ n < 7991300

/-- A byte of `__pthread_force_elision` (`0x79f14c`), of `object_mutex` up to `any_objects_registered`
(`[0x7a33a0, 0x7a33cc)`), or of a registrar's count (`CntN`). -/
def CsuB (x : Addr) : Prop :=
  7991628 ≤ x.toNat ∧ x.toNat < 7991632 ∨ 8008608 ≤ x.toNat ∧ x.toNat < 8008652 ∨
    (7981280 ≤ x.toNat ∧ x.toNat < 7981284 ∨ 7981824 ≤ x.toNat ∧ x.toNat < 7981828 ∨
      7991296 ≤ x.toNat ∧ x.toNat < 7991300)

theorem lbV_cs {U : Addr → Byte} {m : Nat} {x : Addr} (hx : CsuB x) : lV (bV U m) x = U x := by
  unfold CsuB at hx
  unfold lV bV
  rw [vlt (a := 7944528) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7943112) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029536) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029608) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029584) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029616) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

theorem hV_cs {V' : Addr → Byte} {r ph pn : BitVec 64} {x : Addr} (hx : CsuB x) : hV V' r ph pn x = V' x := by
  unfold CsuB at hx
  unfold hV aV
  rw [vlt (a := 8029532) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937208) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937216) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937224) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937240) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944088) (n := 2) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944072) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- A byte of `CsuB` at the return of `_dl_non_dynamic_init` is the one at its entry. -/
theorem ndi_csu {W W' U W₂ : Addr → Byte} {sp b fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat)
    (hsp : 8032256 + 72 ≤ sp.toNat) (hs : sp.toNat + 120 ≤ 2 ^ 64) (hx : CsuB x) : W₂ x = W x := by
  have hx' := hx
  unfold CsuB at hx'
  have hu : x.toNat < 7937664 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ sp.toNat ≤ x.toNat ∨ Mal.Kf fsb x :=
    .inr (.inr (.inr (Or.inl (by unfold Mal.Kn; omega))))
  have hl : Lo b fsb x := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hn : ¬ Scr sp x := by unfold Scr; omega
  rw [hE x hn, lbV_cs (U := U) (m := m) hx, hU x hu, hV_cs (V' := W') (r := r) (ph := 4194368#64) (pn := 8#64) hx,
    hL x hl, fV_out (W := W) (g := g) (x := x) hs (.inl (by omega))]

end FV7z.Ndi

namespace FV7z.Start
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsVar rd_ext)
open FV7z.Ndi (CsuB)

/-- At the return of `__libc_init_first` to `0x613439`, a byte of `CsuB` is the byte `W` at `0x613434`. -/
theorem csu_ret {W W₂ : Addr → Byte} {Z : State} {b fsb fb a0 s x : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
    (hx : CsuB x) (hN : Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) b fsb W₂)
    (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat) (hsp : 8032256 + 72 ≤ (lifSp Z).toNat)
    (hs : (lifSp Z).toNat + 120 ≤ 2 ^ 64) (he : 0x7a9000 + 32 ≤ (entG Z).rsp.toNat)
    (he' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64) (hg : 0x7a9000 + 40 ≤ g.rsp.toNat) (hfb : 0x7a9000 + 64 ≤ fb.toNat)
    (hfb' : fb.toNat ≤ 2 ^ 63) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) fb a1 a2 a3 x = W x := by
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := hN
  have ha : Away x := by unfold CsuB at hx; unfold Away; omega
  rw [ct_away ha hg hfb hfb', Ndi.ndi_csu hE hU hL hb hf hsp hs hx]
  exact lifW_away ha he he'

/-- The bytes the first three functions of `__libc_csu_init` read, by number: the entries of the tunables 4 to 17
(`[0x791740, 0x791a50)`), the first word of `__EH_FRAME_BEGIN__` (`0x70bb60`), and `CsuB`. -/
def PreN (n : Nat) : Prop :=
  7935808 ≤ n ∧ n < 7936592 ∨ 7388000 ≤ n ∧ n < 7388004 ∨ 7991628 ≤ n ∧ n < 7991632 ∨
    8008608 ≤ n ∧ n < 8008652

/-- A byte the first three functions of `__libc_csu_init` read. -/
def PreB (a : Addr) : Prop := PreN a.toNat

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- A byte of `PreB` at the return of `__cxa_atexit` to `0x61344a` is the launch image's. -/
theorem RetAt.pre {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {ra f0 : BitVec 64} (h : RetAt W W₂ Z B g)
    (hK : K.Ok) (hM : MB K V₀) (hW : PtrW K W V₀ B ver (fun _ => True))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64) (toBytesLE ra 8)) V
      (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0) {x : Addr} (hx : PreB x) : V x = K.V0 x := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  unfold PreB PreN at hx
  rw [h.cxa_lo hR (by omega)]
  have e : Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x = W x := by
    rcases hx with hx | hx | hx | hx
    · exact low_ret (by omega) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega)
        (by omega) (by omega)
    · exact low_ret (by omega) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega)
        (by omega) (by omega)
    · exact csu_ret (.inl hx) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega)
        (by omega) (by omega)
    · exact csu_ret (.inr (.inl hx)) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he' (by omega)
        (by omega) (by omega)
  rw [e]
  have hd : ¬ Foot (d3 ++ AuxInit.globals) x := by
    rcases hx with hx | hx | hx | hx
    · exact not_dg (lo := 7935808) (hi := 7936592) (by decide) hx.1 hx.2
    · exact not_dg (lo := 7388000) (hi := 7388004) (by decide) hx.1 hx.2
    · exact not_dg (lo := 7991628) (hi := 7991632) (by decide) hx.1 hx.2
    · exact not_dg (lo := 8008608) (hi := 8008652) (by decide) hx.1 hx.2
  exact ptr_keep hK hM h.hb h.hb' hW (by omega) (by omega) trivial (by unfold TlsVar; omega) (by omega) hd
    (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)

/-- A byte of a registrar's count at the return of `__cxa_atexit` to `0x61344a` is the launch image's. -/
theorem RetAt.cnt {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {ra f0 : BitVec 64} (h : RetAt W W₂ Z B g)
    (hK : K.Ok) (hM : MB K V₀) (hW : PtrW K W V₀ B ver (fun _ => True))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64) (toBytesLE ra 8)) V
      (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0) {x : Addr} (hx : Ndi.CntN x.toNat) : V x = K.V0 x := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  unfold Ndi.CntN at hx
  rw [h.cxa_lo hR (by omega), csu_ret (.inr (.inr hx)) h.nd (by omega) (by omega) (by omega) (by omega) (by omega)
    h.he' (by omega) (by omega) (by omega)]
  have hd : ¬ Foot (d3 ++ AuxInit.globals) x := by
    rcases hx with hx | hx | hx
    · exact not_dg (lo := 7981280) (hi := 7981284) (by decide) hx.1 hx.2
    · exact not_dg (lo := 7981824) (hi := 7981828) (by decide) hx.1 hx.2
    · exact not_dg (lo := 7991296) (hi := 7991300) (by decide) hx.1 hx.2
  exact ptr_keep hK hM h.hb h.hb' hW (by omega) (by omega) trivial (by unfold TlsVar; omega) (by omega) hd
    (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)

/-- The bytes of `PreB` are `V₀`'s. -/
def Agr (V₀ V : Addr → Byte) : Prop := ∀ a : Addr, PreB a → V a = V₀ a

/-- The bytes outside the stack's `[lo, hi)` and `elision_init`'s word are `Vo`'s. -/
def Near (lo hi : Nat) (Vo V : Addr → Byte) : Prop :=
  ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → ¬ (7938696 ≤ a.toNat ∧ a.toNat < 7938700) → V a = Vo a

/-- The invariant of `__libc_csu_init`'s calls: for the first three functions `Agr V₀`, and the bytes outside the
stack's `[lo, hi)` and `elision_init`'s word `Vo`'s; `J` after them. -/
def preI (V₀ Vo : Addr → Byte) (lo hi : Nat) (J : Nat → (Addr → Byte) → Prop) (m : Nat) (V : Addr → Byte) : Prop :=
  if m < 3 then Agr V₀ V ∧ Near lo hi Vo V else J m V

theorem preI_lt {V₀ Vo V : Addr → Byte} {lo hi : Nat} {J : Nat → (Addr → Byte) → Prop} {m : Nat} (h : m < 3) :
    preI V₀ Vo lo hi J m V ↔ Agr V₀ V ∧ Near lo hi Vo V := by
  unfold preI
  rw [if_pos h]

theorem preI_ge {V₀ Vo V : Addr → Byte} {lo hi : Nat} {J : Nat → (Addr → Byte) → Prop} {m : Nat} (h : ¬ m < 3) :
    preI V₀ Vo lo hi J m V ↔ J m V := by
  unfold preI
  rw [if_neg h]

theorem ofNat_add_toNat {x i n : Nat} (hi : i < n) (hx : x + n ≤ 2 ^ 64) :
    (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := by
  rw [toNat_add_of_fits hi (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- `n` bytes of `PreB` from `x` are `V₀`'s. -/
theorem pre_rd {V₀ V : Addr → Byte} (hV : Agr V₀ V) {x n : Nat} (hx : x + n ≤ 2 ^ 64)
    (h : ∀ i < n, PreN (x + i)) :
    List.map V (byteAddrs (BitVec.ofNat 64 x) n) = List.map V₀ (byteAddrs (BitVec.ofNat 64 x) n) :=
  rd_ext _ n fun i hi => hV _ (by unfold PreB; rw [ofNat_add_toNat hi hx]; exact h i hi)

/-- `n` bytes of `PreB` in `.bss` from `x` are 0. -/
theorem pre_zero {V₀ V : Addr → Byte} (hV : Agr V₀ V) (hB : Bss V₀) {x n : Nat} (h1 : 0x7945d0 ≤ x)
    (h2 : x + n ≤ 0x7a86c0) (h : ∀ i < n, PreN (x + i)) :
    List.map V (byteAddrs (BitVec.ofNat 64 x) n) = List.replicate n 0 := by
  rw [pre_rd hV (by omega) h]
  exact rd_zero fun i hi => hB _ (by rw [ofNat_add_toNat hi (by omega)]; omega)
    (by rw [ofNat_add_toNat hi (by omega)]; omega)

/-- A tunable with its entry at `e` in `[0x791740, 0x791a50)`, of type 0 and not initialized in the file, is unset
in bytes whose `PreB` are the image's. -/
theorem unset_of {F : Footprint} {V₀ V : Addr → Byte} (hI : Img V₀) (hV : Agr V₀ V)
    (hF : ∀ y : Addr, 0x777000 ≤ y.toNat → y.toNat < 0x792000 → Foot F.data y) {d : Addr} {e : Nat}
    (e8 : Tgv.ent d + 8#64 = BitVec.ofNat 64 (e + 8)) (e32 : Tgv.ent d + 32#64 = BitVec.ofNat 64 (e + 32))
    (e40 : Tgv.ent d + 40#64 = BitVec.ofNat 64 (e + 40)) (h1 : 7935808 ≤ e) (h2 : e + 48 ≤ 7936592)
    (hty : Exe.bytesAt V2606.zzs.blob (e + 8) 4 = some [0, 0, 0, 0])
    (hin : Exe.bytesAt V2606.zzs.blob (e + 40) 1 = some [0]) : Tgv.Unset F V d := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [e8]
    exact hF _ (by rw [ofNat_add_toNat hi (by omega)]; omega) (by rw [ofNat_add_toNat hi (by omega)]; omega)
  · rw [e32]
    exact hF _ (by rw [ofNat_add_toNat hi (by omega)]; omega) (by rw [ofNat_add_toNat hi (by omega)]; omega)
  · rw [e40]
    exact hF _ (by rw [ofNat_add_toNat hi (by omega)]; omega) (by rw [ofNat_add_toNat hi (by omega)]; omega)
  · rw [e8, pre_rd hV (x := e + 8) (n := 4) (by omega) fun i hi => by unfold PreN; omega,
      img_rd hI hty rfl (by omega) (by omega)]
    rfl
  · rw [e40, pre_rd hV (x := e + 40) (n := 1) (by omega) fun i hi => by unfold PreN; omega,
      img_rd hI hin rfl (by omega) (by omega)]
    rfl

/-- The first word of `__EH_FRAME_BEGIN__` in the file: 16. -/
theorem eh_pin : Exe.bytesAt V2606.zzs.blob 7388000 4 = some [16, 0, 0, 0] := by decide +kernel

theorem t4_ty : Exe.bytesAt V2606.zzs.blob (7935808 + 8) 4 = some [0, 0, 0, 0] := by decide +kernel
theorem t4_in : Exe.bytesAt V2606.zzs.blob (7935808 + 40) 1 = some [0] := by decide +kernel
theorem t5_ty : Exe.bytesAt V2606.zzs.blob (7935864 + 8) 4 = some [0, 0, 0, 0] := by decide +kernel
theorem t5_in : Exe.bytesAt V2606.zzs.blob (7935864 + 40) 1 = some [0] := by decide +kernel
theorem t7_ty : Exe.bytesAt V2606.zzs.blob (7935976 + 8) 4 = some [0, 0, 0, 0] := by decide +kernel
theorem t7_in : Exe.bytesAt V2606.zzs.blob (7935976 + 40) 1 = some [0] := by decide +kernel
theorem t13_ty : Exe.bytesAt V2606.zzs.blob (7936312 + 8) 4 = some [0, 0, 0, 0] := by decide +kernel
theorem t13_in : Exe.bytesAt V2606.zzs.blob (7936312 + 40) 1 = some [0] := by decide +kernel
theorem t17_ty : Exe.bytesAt V2606.zzs.blob (7936536 + 8) 4 = some [0, 0, 0, 0] := by decide +kernel
theorem t17_in : Exe.bytesAt V2606.zzs.blob (7936536 + 40) 1 = some [0] := by decide +kernel

theorem csuTg_0 : csuTg 0 = Eli.eli_at := by decide +kernel
theorem csuTg_2 : csuTg 2 = Fdm.fdm_at := by decide +kernel

theorem runs_congr {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
    {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {I I' : Nat → (Addr → Byte) → Prop} {sp : Addr} {a₀ a₁ a₂ : BitVec 64} {i : Nat} {f : Addr}
    (h0 : I i = I' i) (h1 : I (i + 1) = I' (i + 1)) (h : Csu.Runs prof F Wl L s₀ o gev gP gE I' sp a₀ a₁ a₂ i f) :
    Csu.Runs prof F Wl L s₀ o gev gP gE I sp a₀ a₁ a₂ i f := by
  intro X t V j₂ hK hA hI hr hsp ha hj hra k
  exact h X t V j₂ hK hA ((congrFun h0 V).mp hI) hr hsp ha hj hra fun Z t' V' hKZ hAZ hI' =>
    k Z t' V' hKZ hAZ ((congrFun h1 V').mpr hI')

set_option maxHeartbeats 800000 in
/-- `Runs` for `elision_init`, `_init` and `frame_dummy` with `preI V₀ Vo (sp - 1024) (sp + 8) J`, when the bytes of
`PreB` are the file's in `V₀`, and `J 3` holds after `frame_dummy`. -/
theorem pre_runs {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
    {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {V₀ Vo : Addr → Byte} {J : Nat → (Addr → Byte) → Prop} {sp fb : Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hC : Csu.Env F Wl L sp csuTg)
    (hE0 : Eli.Env F Wl L fb (sp - 64#64)) (hEi : CodeIn L Ini.ini_at Ini.ini) (hE2 : Fdm.Env F Wl L fb (sp - 64#64))
    (hI : Img V₀) (hB : Bss V₀)
    (hF : ∀ y : Addr, 0x777000 ≤ y.toNat → y.toNat < 0x792000 → Foot F.data y)
    (hJ3 : ∀ V V', Agr V₀ V → Near (sp.toNat - 1024) (sp.toNat + 8) Vo V →
      Rfi.Dat (sp.toNat - 64 - 72) (sp.toNat - 64) 7947808#64 7388000#64 V V' → J 3 V') :
    ∀ m < 3, Csu.Runs prof F Wl L s₀ o gev gP gE (preI V₀ Vo (sp.toNat - 1024) (sp.toNat + 8) J) sp a₀ a₁ a₂ m
      (csuTg m) := by
  have n := Csu.sp_n hC.s0
  have hs2 := hE2.s0
  rw [n] at hs2
  intro m hm
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · refine Csu.eli_runs c hfs hC hE0 csuTg_0 (fun V hV => ?_) (fun V V' hV ho => ?_)
    · have hA := ((preI_lt (by decide)).1 hV).1
      exact ⟨unset_of hI hA hF (e := 7935864) (by decide) (by decide) (by decide) (by omega) (by omega) t5_ty t5_in,
        unset_of hI hA hF (e := 7935976) (by decide) (by decide) (by decide) (by omega) (by omega) t7_ty t7_in,
        unset_of hI hA hF (e := 7936536) (by decide) (by decide) (by decide) (by omega) (by omega) t17_ty t17_in,
        unset_of hI hA hF (e := 7935808) (by decide) (by decide) (by decide) (by omega) (by omega) t4_ty t4_in,
        unset_of hI hA hF (e := 7936312) (by decide) (by decide) (by decide) (by omega) (by omega) t13_ty t13_in⟩
    · obtain ⟨hA, hN⟩ := (preI_lt (by decide)).1 hV
      refine (preI_lt (by decide)).2 ⟨fun a ha => ?_, fun a h1 h2 => (ho a (by omega) h2).trans (hN a h1 h2)⟩
      have ha' := ha
      unfold PreB PreN at ha'
      exact (ho a (by omega) (by omega)).trans (hA a ha)
  · exact Csu.ini_runs c hC hEi fun V hV => (preI_lt (by decide)).2 ((preI_lt (by decide)).1 hV)
  · refine Csu.fd_runs c hfs hC hE2 csuTg_2 (fun V hV => ?_) (fun V V' hV hD => ?_)
    · have hA := ((preI_lt (by decide)).1 hV).1
      have e16 : (8008608#64 + 16#64 : Addr) = 8008624#64 := by decide
      have e8 : (8008608#64 + 8#64 : Addr) = 8008616#64 := by decide
      have z : ∀ x : Nat, 0x7945d0 ≤ x → x + 4 ≤ 0x7a86c0 → (∀ i < 4, PreN (x + i)) →
          ofBytesLE 32 (List.map V (byteAddrs (BitVec.ofNat 64 x) 4)) = 0 := fun x h1 h2 h => by
        rw [pre_zero hA hB h1 h2 h]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pre_rd hA (x := 7388000) (n := 4) (by omega) fun i hi => by unfold PreN; omega,
          img_rd hI eh_pin rfl (by omega) (by omega)]
        decide
      · rw [e16]
        exact z _ (by omega) (by omega) fun i hi => by unfold PreN; omega
      · exact z _ (by omega) (by omega) fun i hi => by unfold PreN; omega
      · exact z _ (by omega) (by omega) fun i hi => by unfold PreN; omega
      · rw [e8]
        exact z _ (by omega) (by omega) fun i hi => by unfold PreN; omega
      · exact z _ (by omega) (by omega) fun i hi => by unfold PreN; omega
    · obtain ⟨hA, hN⟩ := (preI_lt (by decide)).1 hV
      exact (preI_ge (by decide)).2 (hJ3 V V' hA hN hD)

end FV7z.Start
