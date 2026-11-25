import FV7z.Start.CxaRet
import FV7z.Ctor.Gs
/-!
# The heap and the exit list at the call of `__libc_csu_init` (PLAN.md §M, `launch_to_main`)

`Ctor.at_ctor_gs` asks for `Gs F Wl fb hi 1 k 3 V` at the call of `__libc_csu_init`: the tables, `CxPre` with one
place of `initial` taken (by `__cxa_atexit (fini, …)`) and `Hp` with the budget `k + 73824`. Here are the last two,
from what `launch_to_main` has at the return of `__cxa_atexit (fini, NULL, NULL)`: the bytes there are `Cxa.Reg` of
those at `0x613439` (`Cti.CtMem (Lif.bcV W₂ …)`, `RetAt`) with the return address stored, and `Hp` of those
(`Ndi.lif_ok`) with the budget `73840 = 16 + 73824`.

- `lif_hpF`, `lif_hpW`: from `0x792980` up, the footprint of `lif_ok`'s `malloc`s is in `lifG`.
- `hp_reg`: `Hp` past the return address and `__cxa_atexit`'s stores (`Cxa.Reg`), all apart from what `Hp` reads.
- `cx_ret`: `CxPre` with no place taken at `0x613439` (as `ret_cxa` shows `__cxa_atexit`'s preconditions).
- `csu_cx_hp`: `CxPre … 1` and `Hp (lifG …) … (kOf 16 3)` after `__cxa_atexit (fini, NULL, NULL)`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)

variable {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {a : Addr}

/-- From `0x792980` up, a byte of the data of `lif_ok`'s footprint (the break's pages and the first `MORECORE`'s
added) is data of `lifG`. -/
theorem lif_hpF (htop : top ≤ 2 ^ 47) (hlt : lo ≤ top) (hbt : B.toNat + 0x23000 ≤ 2 ^ 47) (ha : 7940480 ≤ a.toNat)
    (h : Foot (withNew (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) (brkN B)).data a) :
    Foot (lifG lo top B L).data a := by
  have t8 : (B + 8192#64).toNat = B.toNat + 8192 := by bv_omega
  obtain ⟨r, hr, h1, h2⟩ := h
  simp only [Footprint.data, withNew, zzsFoot, brkN, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rgn_red
  · exact foot_writes ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩
  · exact gd_brk h1 h2
  · exact gd_stack htop (by omega) (by omega)
  · exact gd_var (by omega) (by omega)
  · omega
  · omega

/-- From `0x792980` up, a byte `lif_ok`'s `malloc`s may store into is stored into in `lifG`. -/
theorem lif_hpW (htop : top ≤ 2 ^ 47) (hlt : lo ≤ top) (hbt : B.toNat + 0x23000 ≤ 2 ^ 47) (ha : 7940480 ≤ a.toNat)
    (h : Foot (brkN B ++ ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)) a) : Foot (lifG lo top B L).writes a := by
  have t8 : (B + 8192#64).toNat = B.toNat + 8192 := by bv_omega
  obtain ⟨r, hr, h1, h2⟩ := h
  simp only [zzsFoot, brkN, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rgn_red
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩
  · exact gw_brk h1 h2
  · exact gw_stack htop (by omega) (by omega)
  · exact gw_var (by omega) (by omega)

/-- `Hp` past a stored return address at `q` (above `hi`) and `__cxa_atexit`'s stores into `initial`'s first place
and its lock, none of them where `Hp` reads. -/
theorem hp_reg {F : Footprint} {Wl : List Rgn} {fb q : Addr} {hi m : Nat} {M V : Addr → Byte} {bs : List Byte}
    {fn : BitVec 64} (h : Mal.Hp F Wl fb hi m M) (hm : 16 ≤ m) (hq : hi + 56 ≤ q.toNat) (hbs : bs.length = 8)
    (hq' : q.toNat + 8 ≤ 2 ^ 64) (hR : Cxa.Reg (Vst M q bs) V q 8010400#64 8010416#64 0 fn 0 0) :
    Mal.Hp F Wl fb hi m V := by
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, -, -, hW⟩ := h.cut hm
  have t1 : (8010400#64 : Addr).toNat = 8010400 := rfl
  have t2 : (8010416#64 : Addr).toNat = 8010416 := rfl
  refine hW _ fun a ha => ?_
  unfold Mal.HpF Mal.GlF at ha
  rw [hR.out a (by omega) (by omega) (by omega) (by omega),
    Vst_out _ _ _ _ (by rw [hbs]; omega) (by rw [hbs]; omega)]

variable {W W₂ : Addr → Byte} {Z : State} {a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- At `0x613439` the exit list `initial` is empty, `__exit_funcs` points to it, its flag and lock are clear, and
`multiple_threads` is 0: `CxPre` with no place taken. -/
theorem cx_ret {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} (h : RetAt W W₂ Z B g) (hKo : K.Ok) (hI : Img K.V0)
    (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True)) (hbp : B.toNat + 8192 + 448 < K.bp.toNat) :
    Ctor.CxPre (B + 2176#64) Ctor.xl 0 (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) := by
  have := h.hb; have := h.hb'
  refine ⟨h.mt hbp hW, ?_, ?_, ?_, ?_, fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
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
  · show ofBytesLE 64 (List.map _ (byteAddrs 8010400#64 8)) = 0
    rw [h.exit0 hKo hB hM hW (exitB_at (x := 8010400#64) (n := 8) (c := 8010400) rfl (.inl ⟨by omega, by omega⟩))]
    rfl

/-- After `__cxa_atexit (fini, NULL, NULL)` returns to `0x61344a`: `CxPre` with one place of `initial` taken, and
`Hp` for `lifG` with the budget `kOf 16 3 = 16 + 73824`, the heap at the end of `_dl_non_dynamic_init`. -/
theorem csu_cx_hp {K : Ctx} {V V'' : Addr → Byte} {ver : BitVec 32} {fn : BitVec 64} (h : RetAt W W₂ Z B g)
    (hKo : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True))
    (hbp : B.toNat + 8192 + 448 < K.bp.toNat) (htop : top ≤ 2 ^ 47) (hlt : lo ≤ top)
    (hbt : B.toNat + 0x23000 ≤ 2 ^ 47)
    (hHp : Mal.Hp (withNew (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) (brkN B))
      (brkN B ++ ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)) (B + 2176#64) ((lifSp Z).toNat - 4144)
      (1072 * 0 + 73840) (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V'' (lifSp Z + 152#64) 8010400#64 8010416#64 0 fn 0 0) :
    Ctor.CxPre (B + 2176#64) Ctor.xl 1 V'' ∧
      Mal.Hp (lifG lo top B L) (lifG lo top B L).writes (B + 2176#64) ((lifSp Z).toNat - 4144) (Ctor.kOf 16 3) V'' := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs
  have hf : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have hq : (lifSp Z + 152#64).toNat = (lifSp Z).toNat + 152 := by bv_omega
  have tl : (Ctor.xl : Addr).toNat = 8010400 := rfl
  have tl' : (8010400#64 : Addr).toNat = 8010400 := rfl
  refine ⟨?_, ?_⟩
  · have h1 := (cx_ret (a0 := a0) (s := s) (a1 := a1) (a2 := a2) (a3 := a3) h hKo hI hB hM hW hbp).kept
      (V' := Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
        (toBytesLE (lsm_at.add 1034) 8)) (by decide) (by omega) (by omega) fun a ha => by
        unfold Ctor.CxR at ha
        exact Vst_out _ _ _ _ (by rw [toBytesLE_length, hq]; omega) (by rw [toBytesLE_length, hq]; omega)
    have e : (8010416#64 : Addr) = Ctor.xl + BitVec.ofNat 64 (16 + 32 * 0) := by decide
    rw [e] at hR
    exact Ctor.CxPre.reg h1 hR (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · have e : Ctor.kOf 16 3 = 1072 * 0 + 73840 := by decide
    rw [e]
    exact (hp_reg hHp (by omega) (by rw [hq]; omega) (toBytesLE_length _ _) (by rw [hq]; omega) hR).footHi
      (fun a ha hF => lif_hpF htop hlt hbt ha hF) (fun a ha hW => lif_hpW htop hlt hbt ha hW)

end FV7z.Start
