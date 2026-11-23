import FV7z.Start.EntBytes
import FV7z.Start.StkFoot
import FV7z.Start.MCxEnt
import FV7z.Lif.Ent
import FV7z.Hwc.Head2
/-!
# Names and numbers for `lif_ok` at the call of `__libc_init_first` (PLAN.md G3, startup)

`Lif.ptr_call` takes the state `Z` at `0x613434` to the entry of `__libc_init_first` with `rsp` 8 less and the
return address `0x613429` stored; `Ndi.lif_ok` then speaks of the bytes `lif_a` makes before the `call` of
`_dl_non_dynamic_init` and of `sp`, `rsp` there less 152. The abbreviations name these for bytes `W` at `Z`:

- `entG`, `entV`: registers and bytes at the entry of `__libc_init_first`.
- `lifW`, `lifSp`, `lifY`, `lifM`: `lif_ok`'s `W`, `sp`, `gY` and `fV W sp gY`.

and the lemmas give what `lif_ok` asks of them that is not about the launch:

- `lif_nums`, `bp_num`, `brk_nums`: where the stack words and the TLS block lie, from `rsp` at `0x613434` being
  the layout's `sp` less 288.
- `rd_ra`: the return address of the `call` at `0x613434` in `lifW`.
- `vst_fw`: the two FPU control words are equal past the store of that return address.
- `nv_lo`, `nv_map`: below `sp - 8`, `nV` and `fV` agree.
- `lf_stk1`, `pg_in`: an address of the stack region, and the pages of a string there.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self)
open FV7z.Smm (size)

/-- The registers at the entry of `__libc_init_first`. -/
abbrev entG (Z : State) : Gprs := Z.cpu.gpr.set 4 (Z.cpu.gpr.rsp - 8)

/-- The bytes at the entry of `__libc_init_first`, for bytes `W` at `0x613434`. -/
abbrev entV (W : Addr → Byte) (Z : State) : Addr → Byte := Vst W (entG Z).rsp (toBytesLE (lsm_at.add 1017) 8)

/-- `lif_ok`'s `W`: the bytes at the `call` of `_dl_non_dynamic_init`. -/
abbrev lifW (W : Addr → Byte) (Z : State) : Addr → Byte :=
  Vst (Lif.LifMem (entV W Z) (entG Z)) ((entG Z).rsp - 32#64) (toBytesLE (Lif.lif_at.add 70) 8)

/-- `lif_ok`'s `sp`. -/
abbrev lifSp (Z : State) : Addr := (entG Z).rsp - 152#64

/-- `lif_ok`'s `gY`: the registers at the entry of `_dl_non_dynamic_init`. -/
abbrev lifY (W : Addr → Byte) (Z : State) : Gprs :=
  (Lif.lifG (entG Z) rdw(entV W Z, 7945344#64)).set 4 ((entG Z).rsp - 32#64)

/-- `lif_ok`'s `fV W sp gY`. -/
abbrev lifM (W : Addr → Byte) (Z : State) : Addr → Byte := Ndi.fV (lifW W Z) (lifSp Z) (lifY W Z)

theorem nums_z {z : Addr} {R : Nat} (hz : z.toNat = R - 288) (hR : 2 ^ 40 ≤ R) (hR' : R ≤ 2 ^ 47)
    (h16 : R % 16 = 0) :
    (z - 8#64).toNat = R - 296 ∧ (z - 8#64 - 152#64).toNat = R - 448 ∧ (z - 8#64 - 32#64).toNat = R - 328 ∧
    (z - 8#64 - 152#64 - 8#64 - 4136#64).toNat = R - 4592 ∧
    (z - 8#64 - 152#64 - 8#64 - 32#64).toNat = R - 488 ∧ (z - 8#64 - 152#64 - 72#64).toNat = R - 520 ∧
    (z - 8#64 - 152#64 + 18446744073709551504#64) &&& 15#64 = 0#64 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [Hwc.and15]
  have t : (z - 8#64 - 152#64 + 18446744073709551504#64).toNat = R - 560 := by bv_omega
  rw [t]
  show (R - 560) % 16 = 0
  omega

/-- Where the stack words of `lif_ok` lie, for `rsp` at `0x613434` the layout's `sp` (`R`) less 288. -/
theorem lif_nums {Z : State} {R : Nat} (hz : Z.cpu.gpr.rsp.toNat = R - 288) (hR : 2 ^ 40 ≤ R) (hR' : R ≤ 2 ^ 47)
    (h16 : R % 16 = 0) :
    (entG Z).rsp.toNat = R - 296 ∧ (lifSp Z).toNat = R - 448 ∧ ((entG Z).rsp - 32#64).toNat = R - 328 ∧
    (lifSp Z - 8#64 - 4136#64).toNat = R - 4592 ∧ (lifSp Z - 8#64 - 32#64).toNat = R - 488 ∧
    (lifSp Z - 72#64).toNat = R - 520 ∧ (lifSp Z + 18446744073709551504#64) &&& 15#64 = 0#64 :=
  nums_z (z := Z.cpu.gpr.rsp) hz hR hR' h16

/-- `__libc_start_main`'s frame base, from `Rg`. -/
theorem bp_num {z bp : Addr} {R : Nat} (h : z = bp + 112#64) (hz : z.toNat = R - 288) (hR : 4096 ≤ R)
    (hR' : R ≤ 2 ^ 47) : bp.toNat = R - 400 := by
  subst h
  bv_omega

theorem ne0_of {x : Addr} {c : Nat} (h : x.toNat = c + 8) : x ≠ 0#64 := by
  bv_omega

/-- Where the TLS block's words lie, for the launch's break `B`. -/
theorem brk_nums {B : Addr} (hB : B.toNat + 0x23000 ≤ 2 ^ 47) :
    (B + 4544#64).toNat = B.toNat + 4544 ∧ (B + 2176#64).toNat = B.toNat + 2176 ∧
    (B + 2176#64 - 112#64).toNat = B.toNat + 2064 ∧ (B + 2176#64 - 64#64).toNat = B.toNat + 2112 ∧
    (B + 4544#64 + size 0x20000#64 656#64).toNat = B.toNat + 4544 + 0x21000 := by
  rw [size_mp]
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- The return address of the `call` at `0x613434`, at `rsp` of the entry of `__libc_init_first`, in `lif_ok`'s
bytes: `lif_a`'s stores lie below it or in the variables. -/
theorem rd_ra {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} (hr : 0x7a9000 + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8), g.rsp) = ra₀ := by
  unfold Lif.LifMem Lif.LifStk
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _)]
  · exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- The two FPU control words past a store above the variables. -/
theorem vst_fw {W : Addr → Byte} {y : Addr} {ra₀ : BitVec 64} (hy : 0x7a9000 ≤ y.toNat)
    (hy' : y.toNat + 8 ≤ 2 ^ 64) (h : rdw(W, 7945344#64) = rdw(W, 7943116#64)) :
    rdw(Vst W y (toBytesLE ra₀ 8), 7945344#64) = rdw(Vst W y (toBytesLE ra₀ 8), 7943116#64) := by
  rw [rd_Vst, rd_Vst]
  · exact h
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- A byte of a run below `sp - 8`: `nV` and `fV` agree. -/
theorem nv_lo {W : Addr → Byte} {sp : Addr} {g : Gprs} {x n : Nat} (h8 : 8 ≤ sp.toNat)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (hx : x + n + 8 < sp.toNat) {i : Nat} (hi : i < n) :
    Ndi.nV W sp g (Addr.add (BitVec.ofNat 64 x) i) = Ndi.fV W sp g (Addr.add (BitVec.ofNat 64 x) i) := by
  have t := tg (b := x) hi (by omega)
  exact Ndi.nV_fV h8 hsn (.inl (by omega))

/-- A run below `sp - 8`: `nV` and `fV` agree. -/
theorem nv_map {W : Addr → Byte} {sp : Addr} {g : Gprs} {x n : Nat} (h8 : 8 ≤ sp.toNat)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (hx : x + n + 8 < sp.toNat) :
    (byteAddrs (BitVec.ofNat 64 x) n).map (Ndi.nV W sp g) = (byteAddrs (BitVec.ofNat 64 x) n).map (Ndi.fV W sp g) :=
  List.map_congr_left fun y hy => by
    obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
    exact nv_lo h8 hsn hx hj

/-- An address of the stack region is data of the footprint of `launch_to_ptr`. -/
theorem lf_stk1 {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {y : Addr} (htop : top ≤ 2 ^ 47)
    (h1 : lo ≤ y.toNat) (h2 : y.toNat < top) : Foot (withNew (zzsFoot lo top L) [⟨B, 8192⟩]).data y :=
  foot_writes (foot_append_iff.2 (.inr (zzsFoot_stack htop h1 h2)))

/-- The pages from `p` to `q` lie in `[lo, top)`, `p` a page above `lo` and `q` below the page-aligned `top`. -/
theorem pg_in {lo top p q : Nat} {x : Addr} (ht : top % 4096 = 0) (hp : lo + 4096 ≤ p) (hq : q < top)
    (h1 : p / 4096 ≤ x.toNat / 4096) (h2 : x.toNat / 4096 ≤ q / 4096) : lo ≤ x.toNat ∧ x.toNat < top := by
  omega

end FV7z.Start
