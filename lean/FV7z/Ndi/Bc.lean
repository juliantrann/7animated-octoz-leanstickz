import FV7z.Ndi.Tail
import FV7z.Ndi.Head
import FV7z.Ndi.Mv
import FV7z.Ipa.Run
/-!
# `_dl_non_dynamic_init`: from after `_dl_get_origin` through `_dl_init_paths` to the return (PLAN.md G3, startup)

`ndi_bc`: `ndi_b` (21 → the `call` of `_dl_init_paths` at 2058), `Ipa.whole` (`_dl_init_paths (NULL)` to its `ret`,
bytes `U`), `ndi_c` (2063 → the caller) on `U`. The hypotheses are on the bytes `V` of `ndi_b`; the bytes at the
entry of `_dl_init_paths` (`VI`, `hV` outside the 72 below `sp`, the return address at `sp - 8`) are `V`'s but for
what `ndi_b` stores (`Hv`), and `U` is `VI` where `whole` keeps the bytes and on `Mal.Kn` (`_dl_pagesize`,
`_dl_phdr`, `_dl_phnum`, `_dl_platform`, `__environ`, …).

- `Hv`, `hV_out`: the bytes `ndi_b` stores (`aV`, `_dl_verbose`).
- `Ph.mv`, `Pl.mv`: `Ph` and `Pl` on bytes that agree below the data segment, resp. from `sp` on and at
  `_dl_platform`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Ndi

/-- The bytes `ndi_b` stores before the `call` of `_dl_init_paths` (`hV`): the main map's `l_origin` (`0x793928`),
`l_phdr` (`0x793888`), `l_phnum` (`0x793898`), the five words from `_dl_sysinfo_dso` (`0x791cb8`), `_dl_verbose`
(`0x7a855c`). -/
def Hv (a : Addr) : Prop :=
  7937208 ≤ a.toNat ∧ a.toNat < 7937248 ∨ 7944072 ≤ a.toNat ∧ a.toNat < 7944080 ∨
    7944088 ≤ a.toNat ∧ a.toNat < 7944090 ∨ 7944232 ≤ a.toNat ∧ a.toNat < 7944240 ∨
    8029532 ≤ a.toNat ∧ a.toNat < 8029536

theorem hV_out (V : Addr → Byte) (org ph pn : BitVec 64) {a : Addr} (h : ¬ Hv a) : hV V org ph pn a = V a := by
  unfold Hv at h
  unfold hV aV
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; ipd)]

/-- `Ph` on bytes that agree below the data segment. -/
theorem Ph.mv {V V' : Addr → Byte} (h : Ph V) (hs : ∀ a : Addr, a.toNat < 7827456 → V' a = V a) : Ph V' := by
  have R : ∀ x n : Nat, x + n ≤ 7827456 →
      List.map V' (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n hx => rd_of (by omega) fun a _ h2 => hs a (by omega)
  exact
    { t0 := by rw [R 4194368 4 (by omega)]; exact h.t0
      t1 := by rw [R 4194424 4 (by omega)]; exact h.t1
      t2 := by rw [R 4194480 4 (by omega)]; exact h.t2
      t3 := by rw [R 4194536 4 (by omega)]; exact h.t3
      t4 := by rw [R 4194592 4 (by omega)]; exact h.t4
      t5 := by rw [R 4194648 4 (by omega)]; exact h.t5
      t6 := by rw [R 4194704 4 (by omega)]; exact h.t6
      f6 := by rw [R 4194708 4 (by omega)]; exact h.f6
      t7 := by rw [R 4194760 4 (by omega)]; exact h.t7
      a7 := by rw [R 4194776 8 (by omega)]; exact h.a7
      m7 := by rw [R 4194800 8 (by omega)]; exact h.m7 }

/-- `Pl` on bytes that agree from `sp` on and at `_dl_platform` (`0x7a8548`). -/
theorem Pl.mv {V V' : Addr → Byte} {F : Footprint} {sp p : Addr} {n : Nat} (h : Pl V F sp p n)
    (hs : ∀ a : Addr, sp.toNat ≤ a.toNat → V' a = V a)
    (hp : ∀ a : Addr, 8029512 ≤ a.toNat → a.toNat < 8029520 → V' a = V a) : Pl V' F sp p n := by
  have hi := h.hi
  have fit := h.fit
  exact
    { hp := by rw [rd_of (by omega) hp]; exact h.hp
      hi := h.hi
      fit := h.fit
      n1 := h.n1
      nnz := fun k hk => by
        rw [hs _ (by rw [toNat_add_of_fits (n := n + 1) (by omega) (by omega)]; omega)]
        exact h.nnz k hk
      nz := by
        rw [hs _ (by rw [toNat_add_of_fits (n := n + 1) (by omega) (by omega)]; omega)]
        exact h.nz
      pg := h.pg }

theorem bc_e8 {sp : Addr} (h : 8 ≤ sp.toNat) : (sp - 8#64).toNat = sp.toNat - 8 := by bv_omega
theorem bc_a112 (sp : Addr) : sp - 8#64 + 18446744073709551512#64 = sp + 18446744073709551504#64 := by bv_omega
theorem bc_q8 (sp : Addr) : sp - 8#64 + 8 = sp := by bv_omega
theorem bc_lt {sp : Addr} {x : Nat} (h : 8 ≤ sp.toNat) (hx : x < sp.toNat - 408) : x < (sp - 8#64).toNat - 400 := by
  rw [bc_e8 h, Nat.sub_sub]; exact hx
theorem bc_ge {sp : Addr} {x : Nat} (h : 8 ≤ sp.toNat) (hx : (sp - 8#64).toNat - 400 ≤ x) : sp.toNat - 408 ≤ x := by
  rw [bc_e8 h, Nat.sub_sub] at hx; exact hx
theorem bc_lt8 {sp : Addr} {x : Nat} (h : 8 ≤ sp.toNat) (hx : x < (sp - 8#64).toNat + 8) : x < sp.toNat := by
  rw [bc_e8 h] at hx; omega

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {fb : Addr}

set_option maxHeartbeats 4000000 in
/-- From the entry of `_dl_init_paths` (bytes `Vst W' (sp - 8) ret`, `W'` the bytes `hV V org` of `ndi_b` but for the
72 below `sp`) to the caller of `_dl_non_dynamic_init`: `_dl_init_paths (NULL)` with `_dl_hwcap` 2 or 6 (`hn`), then
`ndi_c`. `U`, the bytes after `_dl_init_paths`, are `hV V org` where it keeps them and on `Mal.Kn`. -/
theorem ndi_pc {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W' : Addr → Byte} {sp : Addr}
    {org : BitVec 64} {Y : State} {t₁ : Nat}
    (c : Seg prof F Wl L s₀ o) (cx : Cx prof F Wl L o pl pc Pm E V sp) (hfs : s₀.cpu.seg.fsBase = fb)
    (hd1 : rdq(V, 8029568#64) = 4194368#64) (hd2 : rdq(V, 8029592#64) = 8#64)
    (h4 : rdq(V, 8029424#64) = 0#64) (h5 : rdd(V, 7937248#64) = 0#32)
    -- `Ipa.whole`
    (hin : CodeIn L Ipa.ipa_at Ipa.ipa) (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {cpy mlc sl ms : List Byte} {Pq Pa Pk Ps : (Addr → Byte) → Prop}
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pk)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {h : Addr} {cnt Ec H s : Nat}
    (hn : h = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ s = 151 ∨ h = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ s = 320)
    (hPq : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W a = V a) → Pq W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 408 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      ¬ Hv a → W a = V a) → Pa W)
    (hPk : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Hv a → W a = V a) → Pk W)
    (hPs : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W a = V a) → Ps W)
    (he : 8388872 + 408 ≤ sp.toNat) (hal : (sp + 18446744073709551504#64) &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, sp.toNat - 408 ≤ a.toNat → a.toNat < sp.toNat → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) (hx2z : V (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F V 11#64) (hm6 : rdq(V, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(V, 8014536#64) = h) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) (hpl0 : rdq(V, 8029520#64) = 0#64)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i))
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hW7b : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hlenV : ∀ k < 3, rdq(V, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k))
    (hslV : ∀ k < 3, ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8)
    -- `ndi_c`
    {lim : Nat} {b fsb : Addr} {ks : Kst} {G : Footprint} {Wl' : List Rgn} {e₂ : Addr} {code₂ : List Byte}
    {j₂ : Nat} {p : Addr} {n : Nat} (hB : Base s₀ lim b fsb ks) (hpl : Pl V F sp p n)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph V)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, sp + 120#64) = e₂.add j₂)
    (hKZ : KeptW Wl s₀ Y) (hAZ : Agree F Y.proc.mm.mem (Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8)))
    (hMZ : Eqo sp W' (hV V org 4194368#64 8#64)) (hrZ : Y.cpu.rip = 6981872#64) (hspZ : Y.cpu.gpr.rsp = sp - 8#64)
    (hdiZ : Y.cpu.gpr.rdi = 0#64)
    (k : ∀ (U : Addr → Byte) s₁ Z t' W',
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨ Mal.Kn a) →
        U a = hV V org 4194368#64 8#64 a) →
      Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem W' → Eqo sp W' (lV (bV U n)) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = rdq(V, sp + 80#64) → Z.cpu.gpr.rbp = rdq(V, sp + 88#64) →
      Z.cpu.gpr.r12 = rdq(V, sp + 96#64) → Z.cpu.gpr.r13 = rdq(V, sp + 104#64) →
      Z.cpu.gpr.r14 = rdq(V, sp + 112#64) → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 →
      GoG prof L o (gev ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have h72 := cx.h72
  have hpi := hpl.hi
  have h8 : 8 ≤ sp.toNat := by omega
  have hs8 : (sp - 8#64).toNat = sp.toNat - 8 := bc_e8 h8
  -- the bytes at the entry of `_dl_init_paths`
  have vh : ∀ a : Addr, (a.toNat < sp.toNat - 72 ∨ sp.toNat ≤ a.toNat) →
      Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8) a = hV V org 4194368#64 8#64 a :=
    fun a ha => by
      rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hs8]; omega) (by rw [toBytesLE_length, hs8]; omega)]
      exact hMZ a (by unfold Scr; omega)
  have vi : ∀ a : Addr, (a.toNat < sp.toNat - 72 ∨ sp.toNat ≤ a.toNat) → ¬ Hv a →
      Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8) a = V a :=
    fun a ha hv => (vh a ha).trans (hV_out _ _ _ _ hv)
  have vlo : ∀ a : Addr, a.toNat < 7937208 →
      Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8) a = V a :=
    fun a ha => vi a (.inl (by omega)) (by unfold Hv; omega)
  have vmid : ∀ a : Addr, 7944240 ≤ a.toNat ∧ a.toNat < 8029532 →
      Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8) a = V a :=
    fun a ha => vi a (.inl (by omega)) (by unfold Hv; omega)
  -- `_dl_init_paths`
  refine Ipa.whole c hfs hin hinh hinc hc0 hcpy hinm hm0 hmal hinl hl0 hlenA hinz hz0 hset hint
    (V := Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8)) (e := sp - 8#64) (p := p) hn
    (fun W hW => hPq W fun a h1 h2 h3 => (hW a h1 h2).trans (vi a (.inl (by omega)) h3))
    (fun W hW => hPa W fun a h1 h2 h3 => (hW a (bc_lt h8 h1) h2).trans (vi a (.inl (by omega)) h3))
    (fun W hW => hPk W fun a h1 h2 => (hW a h1).trans (vi a (.inl (by omega)) h2))
    (fun W hW => hPs W fun a h1 h2 h3 => (hW a h1 h2).trans (vi a (.inl (by omega)) h3))
    (by rw [hs8]; omega) (by rw [hs8]; omega) (by rw [bc_a112]; exact hal)
    (fun a h1 h2 => hFs a (bc_ge h8 h1) (bc_lt8 h8 h2)) hpg
    (fun i hi => by
      rw [vlo (Addr.add 7288953#64 i) (by rw [toNat_add_of_fits (n := 6) hi (by ipd)]; ipd)]; exact hx1 i hi)
    (by rw [vlo (Addr.add 7288953#64 6) (by rw [toNat_add_of_fits (n := 7) (by decide) (by ipd)]; ipd)]; exact hx1z)
    (fun i hi => by
      rw [vlo (Addr.add 7288962#64 i) (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)]; exact hx2 i hi)
    (by rw [vlo (Addr.add 7288962#64 8) (by rw [toNat_add_of_fits (n := 9) (by decide) (by ipd)]; ipd)]; exact hx2z)
    htls (Tgv.UnsetW.out hU (lo := 7937208) (hi := 2 ^ 64) (by rw [Hwc.eent]; ipd) (by omega)
      fun a ha => by have := a.isLt; exact vlo a (by omega))
    ((Ipa.rdk vlo (lo := 0) (hi := 7937208) (fun a _ h2 => h2) (by omega) (by rw [Hwc.eent]; ipd)
      (by rw [Hwc.eent]; ipd)).trans hm6)
    ((Ipa.rdk vmid (lo := 7944240) (hi := 8029532) (fun a h1 h2 => ⟨h1, h2⟩) (by ipd) (by ipd) (by ipd)).trans hhw)
    hfh
    ((Ipa.rdk vmid (lo := 7944240) (hi := 8029532) (fun a h1 h2 => ⟨h1, h2⟩) (by ipd) (by ipd) (by ipd)).trans h4)
    hfm
    ((Ipa.rdk vmid (lo := 7944240) (hi := 8029532) (fun a h1 h2 => ⟨h1, h2⟩) (by ipd) (by ipd) (by ipd)).trans
      hpl.hp)
    ((Ipa.rdk vmid (lo := 7944240) (hi := 8029532) (fun a h1 h2 => ⟨h1, h2⟩) (by ipd) (by ipd) (by ipd)).trans
      hpl0)
    hf1 hf2 (fun h0 => by rw [h0] at hpi; simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hpi; omega)
    (.inr (by rw [hs8]; omega)) hWb hfN hW7a hW7b hFR
    (fun i hi => by
      rw [Ipa.rdk vlo (lo := 0) (hi := 7937208) (fun a _ h2 => h2) (Nat.zero_le _) (by ipd) (by ipd)]
      exact hlenV i hi)
    (fun i hi => by
      have hb : (BitVec.ofNat 64 (Ipa.sA i)).toNat + 1 ≤ 7937208 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +kernel
      rw [Ipa.kr (fun a (h : a.toNat < 7937208) => vlo a h)
        (Ipa.rgn (p := fun a : Addr => a.toNat < 7937208) (lo := 0) (hi := 7937208) (fun a _ h => h)
          (Nat.zero_le _) hb (by omega))]
      exact hslV i hi)
    (e₂ := ndi_at) (code₂ := ndi) (j₂ := 2063) cx.hin (by rw [ndi_length]; decide)
    (by
      rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hs8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
      try rfl)
    Y t₁ hKZ hAZ (hrZ.trans rfl) hspZ hdiZ ?_
  intro Z₂ t₂ U hK₂ hA₂ hr₂ hs₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂ hkp hkn
  -- the bytes after it
  have uv : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kn a) → U a = hV V org 4194368#64 8#64 a := fun a ha => by
    have hb : a.toNat < sp.toNat - 72 ∨ sp.toNat ≤ a.toNat := by
      rcases ha with ha | ha | ha | ha
      · omega
      · omega
      · omega
      · have := Mal.Kn.lt ha; omega
    rw [← vh a hb]
    rcases ha with ha | ha | ha | ha
    · exact hkp a (.inl ha)
    · exact hkp a (.inr (.inl ha))
    · exact hkp a (.inr (.inr (by rw [hs8]; omega)))
    · exact hkn a ha
  have uV : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kn a) → ¬ Hv a → U a = V a := fun a ha hv => (uv a ha).trans (hV_out _ _ _ _ hv)
  have uK : ∀ a : Addr, Mal.Kn a → ¬ Hv a → U a = V a := fun a ha hv => uV a (.inr (.inr (.inr ha))) hv
  have uS : ∀ a : Addr, sp.toNat ≤ a.toNat → U a = V a :=
    fun a ha => uV a (.inr (.inr (.inl ha))) (by unfold Hv; omega)
  have SU : Same sp V U := fun a ha => by
    rcases ha with ha | ha | ha | ha
    · exact uS a ha
    · exact uV a (.inl (by omega)) (by unfold Hv; omega)
    · exact uV a (.inr (.inl ⟨by omega, ha.2⟩)) (by unfold Hv; omega)
    · exact uK a (by unfold Mal.Kn; omega) (by unfold Hv; omega)
  have rK : ∀ x : Nat, 8029560 ≤ x → x + 8 ≤ 8032256 →
      List.map U (byteAddrs (BitVec.ofNat 64 x) 8) = List.map V (byteAddrs (BitVec.ofNat 64 x) 8) :=
    fun x h1 h2 => rd_of (by omega) fun a a1 a2 => uK a (by unfold Mal.Kn; omega) (by unfold Hv; omega)
  have rS : ∀ j : Nat, j + 8 ≤ 128 → rdq(U, sp + BitVec.ofNat 64 j) = rdq(V, sp + BitVec.ofNat 64 j) :=
    fun j hj => Ipa.rdk uS (lo := sp.toNat) (hi := 2 ^ 64) (fun a h1 _ => h1) (by rw [tp sp j (by omega)]; omega)
      (by rw [tp sp j (by omega)]; omega) (by rw [tp sp j (by omega)]; omega)
  -- `ndi_c` on `U`
  refine ndi_c c hB (cx.mvg (fun _ h => h) (fun _ h => h) SU)
    (hpl.mv uS fun a h1 h2 => uK a (by unfold Mal.Kn; omega) (by unfold Hv; omega))
    (by
      rw [rd_of (by omega) fun a a1 a2 => uV a (.inl (by omega)) (by unfold Hv; omega)]
      exact h5)
    hid him hfp (hph.mv fun a ha => uV a (.inl (by omega)) (by unfold Hv; omega))
    (by rw [rK 8029568 (by omega) (by omega)]; exact hd1) (by rw [rK 8029592 (by omega) (by omega)]; exact hd2) hsn
    (by
      rw [rd_of (by omega) fun a a1 a2 => uK a (by unfold Mal.Kn; omega) (by unfold Hv; omega)]
      exact hps)
    (by
      rw [rd_of (by omega) fun a a1 a2 => uK a (by unfold Mal.Kn; omega) (by unfold Hv; omega)]
      exact hla)
    hmg hB.relro hGo hGc hfit hGw hGr hcode hww hlG hl hin₂ h₂ (by rw [rS 120 (by omega)]; exact hret)
    hK₂ hA₂ (Eqo.refl _ _) hr₂ (by rw [hs₂, bc_q8]) ?_
  intro s₁ Z₃ t₃ W₃ c₁ hB₁ hK₃ hA₃ hM₃ hr₃ hs₃ hbx hbp h12 h13 h14 h15
  exact k U s₁ Z₃ t₃ W₃ uv c₁ hB₁ hK₃ hA₃ hM₃ hr₃ hs₃ (hbx.trans (rS 80 (by omega)))
    (hbp.trans (rS 88 (by omega))) (h12.trans (rS 96 (by omega))) (h13.trans (rS 104 (by omega)))
    (h14.trans (rS 112 (by omega))) (by rw [h15, h15₂])

/-- From after `_dl_get_origin` (21, bytes `V` but for the 72 below `sp`) to the caller of `_dl_non_dynamic_init`:
`_dl_phdr` `0x400040` and `_dl_phnum` 8 (`hd1`, `hd2`), `_dl_init_paths (NULL)` with `_dl_hwcap` 2 or 6 (`hn`).
`U`, the bytes after `_dl_init_paths`, are `hV V` where it keeps them and on `Mal.Kn`. -/
theorem ndi_bc {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W : Addr → Byte} {sp : Addr}
    (c : Seg prof F Wl L s₀ o) (cx : Cx prof F Wl L o pl pc Pm E V sp) (hfs : s₀.cpu.seg.fsBase = fb)
    -- `ndi_b`
    (h1 : rdq(V, 8029448#64) = 0#64) (hd1 : rdq(V, 8029568#64) = 4194368#64) (hd2 : rdq(V, 8029592#64) = 8#64)
    (h4 : rdq(V, 8029424#64) = 0#64) (h5 : rdd(V, 7937248#64) = 0#32)
    -- `Ipa.whole`
    (hin : CodeIn L Ipa.ipa_at Ipa.ipa) (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {cpy mlc sl ms : List Byte} {Pq Pa Pk Ps : (Addr → Byte) → Prop}
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pk)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {h : Addr} {cnt Ec H s : Nat}
    (hn : h = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ s = 151 ∨ h = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ s = 320)
    (hPq : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W a = V a) → Pq W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 408 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      ¬ Hv a → W a = V a) → Pa W)
    (hPk : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Hv a → W a = V a) → Pk W)
    (hPs : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W a = V a) → Ps W)
    (he : 8388872 + 408 ≤ sp.toNat) (hal : (sp + 18446744073709551504#64) &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, sp.toNat - 408 ≤ a.toNat → a.toNat < sp.toNat → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) (hx2z : V (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F V 11#64) (hm6 : rdq(V, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(V, 8014536#64) = h) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) (hpl0 : rdq(V, 8029520#64) = 0#64)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i))
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hW7b : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hlenV : ∀ k < 3, rdq(V, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k))
    (hslV : ∀ k < 3, ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8)
    -- `ndi_c`
    {lim : Nat} {b fsb : Addr} {ks : Kst} {G : Footprint} {Wl' : List Rgn} {e₂ : Addr} {code₂ : List Byte}
    {j₂ : Nat} {p : Addr} {n : Nat} (hB : Base s₀ lim b fsb ks) (hpl : Pl V F sp p n)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph V)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, sp + 120#64) = e₂.add j₂)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W V)
    (hrip : X.cpu.rip = ndi_at.add 21) (hsp : X.cpu.gpr.rsp = sp)
    (k : ∀ (U : Addr → Byte) s₁ Z t' W',
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨ Mal.Kn a) →
        U a = hV V X.cpu.gpr.rax 4194368#64 8#64 a) →
      Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem W' → Eqo sp W' (lV (bV U n)) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = rdq(V, sp + 80#64) → Z.cpu.gpr.rbp = rdq(V, sp + 88#64) →
      Z.cpu.gpr.r12 = rdq(V, sp + 96#64) → Z.cpu.gpr.r13 = rdq(V, sp + 104#64) →
      Z.cpu.gpr.r14 = rdq(V, sp + 112#64) → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  refine ndi_b (ph := 4194368#64) (pn := 8#64) c cx hin (by rw [Ipa.ipa_length]; decide) h1 hd1 hd2 h4 h5 hK hA
    hM hrip hsp ?_
  intro Z t₁ W' hKZ hAZ hMZ hrZ hspZ hdiZ h15Z
  exact ndi_pc c cx hfs hd1 hd2 h4 h5 hin hinh hinc hc0 hcpy hinm hm0 hmal hinl hl0 hlenA hinz hz0 hset hint hn hPq
    hPa hPk hPs he hal hFs hpg hx1 hx1z hx2 hx2z htls hU hm6 hhw hfh hfm hpl0 hf1 hf2 hWb hfN hW7a hW7b hFR hlenV hslV
    hB hpl hid him hfp hph hsn hps hla hmg hGo hGc hfit hGw hGr hcode hww hlG hl hin₂ h₂ hret hKZ hAZ hMZ hrZ hspZ
    hdiZ
    (fun U s₁ Z₃ t₃ W₃ uv c₁ hB₁ hK₃ hA₃ hM₃ hr₃ hs₃ hbx hbp h12 h13 h14 h15 =>
      k U s₁ Z₃ t₃ W₃ uv c₁ hB₁ hK₃ hA₃ hM₃ hr₃ hs₃ hbx hbp h12 h13 h14 (h15.trans h15Z))

end FV7z.Ndi
