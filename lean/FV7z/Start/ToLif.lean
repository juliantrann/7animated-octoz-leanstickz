import FV7z.Start.LifNums
import FV7z.Start.CxEnt
import FV7z.Start.AgreeW
import FV7z.Start.PlCase
import FV7z.Start.Ent
import FV7z.Start.LifFoot
import FV7z.Start.MPreEnt
/-!
# From the call of `__libc_init_first` to its return (PLAN.md G3, startup)

At `0x613434` `__libc_start_main` calls `__libc_init_first (argc, argv, envp)`. `Lif.ptr_call` takes the run to its
entry and `Ndi.lif_ok` from there to its return to `0x613439` (and to the branch where `readlink` of
`/proc/self/exe` fails, `ke`). `lif_ok` asks some hundred and fifty facts; here those not about the code, the
library contracts and the two continuations are given from what holds at `0x613434`:

- the bytes there, `W`, agree with the memory on the footprint of `launch_to_ptr` and are `PtrMem …`'s at every
  address apart from the start code's stores (`ptrW_all`), so every lemma about `lif_ok`'s bytes applies;
- the launch facts (`K.Ok`, `Img`, `Bss`, `MB`, `_dl_aux_init`'s values), the environment and `argv[0]`;
- where `rsp` (the layout's `sp`, `R`, less 288), the stack region `[lo, top)` and the break `B` lie.

- `ptr_lif`: the run from `0x613434` goes on as `lif_ok`'s continuations do.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Smm (size smEv smEv2)
open FV7z.Mhi (C2)
open FV7z.Gor (gEv gor_at)

set_option maxHeartbeats 4000000 in
/-- From the call of `__libc_init_first` at `0x613434` to `lif_ok`'s continuations. -/
theorem ptr_lif {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {s₂ Z : State} {t lim : Nat}
    {ks : Kst} {K : Ctx} {W V : Addr → Byte} {B : Addr} {ver : BitVec 32} {lo top R P : Nat} {a0 : Addr}
    {n : Nat} {Pm Pq Pk Ps Pr : (Addr → Byte) → Prop}
    -- the code and the library contracts
    (hLC : LifCode L) (hMC : MalCode L) (hlsm : CodeIn L lsm_at lsm)
    (hlen : Str.LenAt prof L o 4198664#64 Pm) (hcmp : Str.NcmpAt prof L o 4198472#64 Pm)
    (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm) (hcpq : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hlenA : Str.LenAt prof L o 4198664#64 Pk) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hrchr : Str.RchrAt prof L o 4198480#64 Pr)
    (hPm : ∀ W₁ : Addr → Byte, (∀ x : Addr, 7938048 ≤ x.toNat → x.toNat < 7940480 → W₁ x = lifM W Z x) → Pm W₁)
    (hPq : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      ¬ Ndi.Hv a → W₁ a = lifM W Z a) → Pq W₁)
    (hPk : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Ndi.Hv a → W₁ a = lifM W Z a) → Pk W₁)
    (hPs : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      ¬ Ndi.Hv a → W₁ a = lifM W Z a) → Ps W₁)
    (hPr : ∀ W₁ : Addr → Byte, (∀ a : Addr, (a.toNat < 7937208 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480) →
      W₁ a = lifW W Z a) → Pr W₁)
    (hmg : ∀ t p, o t (.memFail p) = none) (hpse : ProcSelfExe o)
    -- the run to `0x613434`
    (hc : Seg prof (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) L s₂ o)
    (hBs : Base s₂ lim (B + 4544#64) (B + 2176#64) ks)
    (hKZ : KeptW ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) s₂ Z)
    (hAZ : Agree (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) Z.proc.mm.mem W)
    (hrip : Z.cpu.rip = 0x613434) (hRg : Rg K Z.cpu.gpr) (hdx : Z.cpu.gpr.rdx = K.envp)
    (hsi : Z.cpu.gpr.rsi = K.argv) (hHw : CpuFeat.HwW Z.proc.mm.mem.readByte)
    (hPl : CpuFeat.PlW V Z.proc.mm.mem.readByte) (hW : PtrW K W V B ver (fun _ => True))
    -- the launch
    (hK : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V)
    (hps : (K.vs K.M).pagesize = 4096#64) (hph : (K.vs K.M).phdr = 0x400040#64) (hpn : (K.vs K.M).phnum = 8#64)
    (hsd : (K.vs K.M).sysinfoDso = K.w0.sysinfoDso) (hfp : (K.vs K.M).fpuControl = K.w0.fpuControl)
    (hKp : (K.vs K.M).platform = BitVec.ofNat 64 P)
    (hV0 : ∀ k < platformString.length, K.V0 (BitVec.ofNat 64 (P + k)) = platformString.getD k 0)
    (noLD : ∀ i < K.N, ¬ (K.ez i 0 = 0x4c ∧ K.ez i 1 = 0x44 ∧ K.ez i 2 = 0x5f))
    -- where things lie
    (hz : Z.cpu.gpr.rsp.toNat = R - 288) (h16 : R % 16 = 0) (hlo : 2 ^ 40 ≤ lo) (hlR : lo + 5000 ≤ R)
    (hRt : R < top) (htop : top ≤ 2 ^ 47 - 4096) (ht4 : top % 4096 = 0)
    (hbl : 0x7a9000 ≤ B.toNat) (hal : B.toNat % 4096 = 0) (hBl : B.toNat + 2 ^ 32 ≤ lo)
    (hlim : B.toNat + 0x23000 ≤ 4096 * lim) (hL : ∀ p ∈ L, p.1.toNat + p.2.length ≤ 0x6d8000)
    (hPR : R ≤ P) (hPt : P + 7 ≤ top)
    (hle : R ≤ K.envp.toNat) (het : K.envp.toNat + 8 * (K.N + 1) ≤ top)
    (hls : ∀ i < K.N, R ≤ (K.ptr i).toNat) (hlt : ∀ i < K.N, (K.ptr i).toNat + K.len i + 2 ≤ top)
    (hav : K.argv.toNat = R + 8)
    -- `argv[0]`
    (ha0 : rdq(lifW W Z, K.argv) = a0) (hnz : a0 ≠ 0) (nfit : a0.toNat + n < 2 ^ 64)
    (nnz : ∀ k < n, lifW W Z (Addr.add a0 k) ≠ 0) (nz : lifW W Z (Addr.add a0 n) = 0)
    (ha1 : R ≤ a0.toNat) (ha2 : a0.toNat + n < top)
    -- `lif_ok`'s continuations
    (ke : ∀ r Z' t', KeptW ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) s₂ Z' →
      Agree (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) Z'.proc.mm.mem
        (Gor.frV (Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z)) { lifY W Z with rsp := lifSp Z - 8#64 }) →
      Z'.cpu.rip = gor_at.add 271 → Z'.cpu.gpr.rax = 18446744073709551615#64 →
      Z'.cpu.gpr.rsp = lifSp Z - 8#64 → Z'.cpu.gpr.rbx = (lifY W Z).rbx → Z'.cpu.gpr.rbp = (lifY W Z).rbp →
      Z'.cpu.gpr.r12 = (lifY W Z).r12 → Z'.cpu.gpr.r13 = (lifY W Z).r13 → Z'.cpu.gpr.r14 = (lifY W Z).r14 →
      Z'.cpu.gpr.r15 = (lifY W Z).r15 →
      GoG prof L o (gev ++ [gEv { lifY W Z with rsp := lifSp Z - 8#64 } r]) gP gE Z' t')
    (k : ∀ (x : ExePath) (evs : List Event) (s₃ Z₁ Z' : State) (t' : Nat) (s : Addr) (W₂ : Addr → Byte),
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = B + 4544#64 ∧ g₂.r14 = size 0x20000#64 656#64 ∧
        (evs = [smEv g₁ 0x20000#64 (B + 4544#64)] ∨ evs = [smEv g₁ 0x20000#64 (B + 4544#64), smEv2 g₂])) →
      Seg prof (lifG lo top B L) (lifG lo top B L).writes L s₃ o →
      Base s₃ lim (B + 4544#64 + size 0x20000#64 656#64 + C2 (B + 4544#64) 0x20000#64) (B + 2176#64) ks →
      Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) (B + 4544#64) (B + 2176#64) W₂ →
      Z₁.cpu.gpr.rsp = lifSp Z + 128#64 → Z₁.cpu.gpr.rbp = (lifY W Z).rbp → Z₁.cpu.gpr.r12 = (lifY W Z).r12 →
      Z₁.cpu.gpr.r13 = (lifY W Z).r13 →
      KeptW (lifG lo top B L).writes s₃ Z' →
      Agree (lifG lo top B L) Z'.proc.mm.mem
        (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr a0 s) (B + 2176#64) 7299392#64 7296832#64 7295296#64) →
      Mal.Hp (withNew (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) (brkN B))
        (brkN B ++ ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)) (B + 2176#64) ((lifSp Z).toNat - 4144)
        (1072 * 0 + 73840) (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr a0 s) (B + 2176#64) 7299392#64 7296832#64 7295296#64) →
      Ims.Short (lifW W Z) a0 n s → Z'.cpu.rip = lsm_at.add 1017 → Z'.cpu.gpr.rsp = lifSp Z + 160#64 →
      Z'.cpu.gpr.rbx = (lifY W Z).rbx → Z'.cpu.gpr.rbp = rdq(lifW W Z, lifSp Z + 128#64) →
      Z'.cpu.gpr.r12 = rdq(lifW W Z, lifSp Z + 136#64) → Z'.cpu.gpr.r13 = rdq(lifW W Z, lifSp Z + 144#64) →
      Z'.cpu.gpr.r14 = (lifY W Z).r14 → Z'.cpu.gpr.r15 = (lifY W Z).r15 →
      GoG prof L o (gev ++ [gEv { lifY W Z with rsp := lifSp Z - 8#64 } (.procExe x)] ++ evs ++ [Ndi.ndiEv]) gP gE
        Z' t') :
    GoG prof L o gev gP gE Z t := by
  -- numbers
  have htop' : top ≤ 2 ^ 47 := by omega
  obtain ⟨n1, n2, n3, n4, n5, n6, nal⟩ := lif_nums (Z := Z) hz (by omega) (by omega) h16
  have nbp := bp_num hRg.1 hz (by omega) (by omega)
  obtain ⟨b1, b2, b3, b4, b5⟩ := brk_nums (B := B) (by omega)
  have n1' : (Z.cpu.gpr.rsp - 8).toNat = R - 296 := n1
  have hb' : B.toNat + 8192 ≤ 2 ^ 63 := by omega
  have hr : 0x7a9000 + 32 ≤ (entG Z).rsp.toNat := by omega
  have hr' : (entG Z).rsp.toNat + 8 ≤ 2 ^ 64 := by omega
  have hsp : 0x7a9000 ≤ (lifSp Z).toNat := by omega
  have hsn : (lifSp Z).toNat + 128 ≤ 2 ^ 64 := by omega
  have h8 : 8 ≤ (lifSp Z).toNat := by omega
  have hbp : B.toNat + 2072 + 448 < K.bp.toNat := by omega
  have e12 : (lifY W Z).r12 = K.argv := hsi
  have e152 : lifSp Z + 152#64 = (entG Z).rsp := BitVec.sub_add_cancel _ _
  -- footprints
  obtain ⟨l1, l2, lw, la, lb, lE, hpf, hof, hpg, htls, hfh, hfm, hf1, hf2, hWb, hfN, hW7a, hW7b, hFR, hfp'⟩ :=
    lif_foot (lo := lo) (top := top) (L := L) (N := [⟨B, 8192⟩])
  obtain ⟨hpw, hst, hsm, hFs, hlG, hl, hst₂, hl₂⟩ :=
    lif_stk (lo := lo) (top := top) (B := B) (L := L) (sp := lifSp Z) htop' (by omega) (by omega)
  obtain ⟨hGo, hGc, hfit, hGw, hGr, hcode, hww⟩ :=
    lifG_ok (lo := lo) (top := top) (B := B) (L := L) (by omega) (by omega) htop' hbl (by omega) hL
  have hFv : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 →
      Foot (withNew (zzsFoot lo top L) [⟨B, 8192⟩]).data a := fun _ h1 h2 => lf_var h1 h2
  -- code at the PLT entries
  obtain ⟨sl, hinl, hl0⟩ := hLC.plt 4198664 (by decide)
  obtain ⟨pc, hic, hc0⟩ := hLC.plt 4198472 (by decide)
  obtain ⟨cpy, hinc, hcc⟩ := hLC.plt 4198592 (by decide)
  obtain ⟨mlc, hinm, hm0⟩ := hLC.plt 6500704 (by decide)
  obtain ⟨ms, hinz, hz0⟩ := hLC.plt 4198528 (by decide)
  obtain ⟨pr, hir, hr0⟩ := hLC.plt 4198480 (by decide)
  -- the bytes
  have hHw' : CpuFeat.HwW W := agree_hw hAZ (lf_varN (x := 0x7a4ac8) (n := 8) (by omega) (by omega)) hHw
  obtain ⟨h1, h2, h3, h4, h5, pn, pz, pp, oz, x1, x1z, x2, x2z, m6, hhw, pl0, lenV, slV, ph, pgs, la'⟩ :=
    ent_bytes (M := lifM W Z) (g := entG Z) (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017) (sp := lifSp Z)
      (gY := lifY W Z) (W := W) rfl hK hI hB hM hps hph hpn hsd hbl hb' hbp hW (fun _ _ _ => trivial) hHw'
      (by omega) hr' hsp (by omega)
  obtain ⟨hw, cnt, Ec, H, sz, hn, hhw'⟩ : ∃ (hw : Addr) (cnt Ec H sz : Nat),
      (hw = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ sz = 151 ∨ hw = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ sz = 320) ∧
        rdq(lifM W Z, 8014536#64) = hw := by
    rcases hhw with e | e
    · exact ⟨_, _, _, _, _, .inl ⟨rfl, rfl, rfl, rfl, rfl⟩, e⟩
    · exact ⟨_, _, _, _, _, .inr ⟨rfl, rfl, rfl, rfl, rfl⟩, e⟩
  have hpn' : ∀ i < 14, Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z) (Addr.add 7366691#64 i) ≠ 0 := fun i hi => by
    have e := nv_lo (W := lifW W Z) (g := lifY W Z) (x := 7366691) (n := 15) h8 hsn (by omega)
      (show i < 15 by omega)
    rw [e]
    exact pn i hi
  have hpz' : Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z) (Addr.add 7366691#64 14) = 0 := by
    have e := nv_lo (W := lifW W Z) (g := lifY W Z) (x := 7366691) (n := 15) h8 hsn (by omega)
      (show 14 < 15 by omega)
    rw [e]
    exact pz
  have hpp' : (byteAddrs 7366691#64 14).map (Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z)) = Gor.pse := by
    have e := nv_map (W := lifW W Z) (g := lifY W Z) (x := 7366691) (n := 14) h8 hsn (by omega)
    rw [e, Gor.pse_eq]
    exact pp
  have hoz' : rdq(Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z), 8029440#64) = 0#64 := by
    have e := nv_map (W := lifW W Z) (g := lifY W Z) (x := 8029440) (n := 8) h8 hsn (by omega)
    rw [e]
    exact oz
  have tl : 7935584 ≤ (Tgv.ent 11#64).toNat := by decide
  have tu : (Tgv.ent 11#64).toNat + 48 ≤ 7940484 := by decide
  have hU := ent_unset (W := W) (g := entG Z) (ra₀ := lsm_at.add 1017) (ra := Lif.lif_at.add 70)
    (sp := lifSp Z) (gY := lifY W Z) (D := fun _ => True) hK hI hM hbl hb' hW (fun _ _ _ => trivial) (by omega) hr'
    (by omega) (by omega) (fun i hi => tun_foot hFv tl tu (by omega))
    (fun i hi => tun_foot hFv tl tu (by omega)) (fun i hi => tun_foot hFv tl tu (by omega))
  obtain ⟨hlp, hct, hca, hcb, hcc'⟩ := ent_ct (g := entG Z) (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017)
    (D := fun _ => True) hK hI hM hbl hb' hbp hW (fun _ _ _ => trivial) (by omega) hr'
  have hZ : rdq(W, 8029512#64) = rdq(Z.proc.mm.mem.readByte, 8029512#64) :=
    (agree_rdq hAZ (lf_varN (x := 8029512) (n := 8) (by omega) (by omega))).symm
  obtain ⟨q, m, hpl⟩ := ent_plat (g := entG Z) (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017) (sp := lifSp Z)
    (gY := lifY W Z) (F := withNew (zzsFoot lo top L) [⟨B, 8192⟩]) hK hI hM hbl hb' hW hPl hZ
    (fun _ _ _ => trivial) (by omega) hr' (by omega) (by omega) hKp (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ _ => trivial) hV0
    (fun x e1 e2 => by
      obtain ⟨p1, p2⟩ := pg_in (lo := lo) ht4 (by omega) (show P + 6 < top by omega) e1 e2
      exact lf_stk1 htop' p1 p2)
    (fun x e1 e2 => lf_ro (by omega) (by omega))
  have hpre := ent_mpreN (F := withNew (zzsFoot lo top L) [⟨B, 8192⟩]) (g := entG Z) (gY := lifY W Z)
    (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017) (sp := lifSp Z) hK hI hB hM hps hbl hb' hal (by omega) hW
    (fun _ _ _ => trivial) hFv (by omega) hr' (by omega) hsn
  have mc := ent_mcx (prof := prof) (lo := lo) (top := top) hBs hMC hal hbl hlim hmg
  have cx := ent_cx (F := withNew (zzsFoot lo top L) [⟨B, 8192⟩])
    (Wl := [⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (g := entG Z) (gY := lifY W Z) (ra := Lif.lif_at.add 70)
    (ra₀ := lsm_at.add 1017) (sp := lifSp Z) (lo := R) hLC hinl hl0 hlen hic hc0 hcmp hPm hK hI hM hbl hb' hW
    (fun _ _ _ => trivial) (by omega) (by omega) (by omega) (by omega) hle hls (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun i hi => by have := hlt i hi; omega) hdx (by omega) (by omega)
    (lf_stk (x := K.envp) htop' (by omega) het)
    (fun i hi x e1 e2 => by
      have := hls i hi
      have := hlt i hi
      obtain ⟨p1, p2⟩ := pg_in ht4 (show lo + 4096 ≤ (K.ptr i).toNat by omega)
        (show (K.ptr i).toNat + K.len i < top by omega) e1 e2
      exact lf_stk1 htop' p1 p2)
    (fun i hi => by
      have := hls i hi
      have := hlt i hi
      exact lf_stk (x := K.ptr i) (n := 2) htop' (by omega) (by omega) 1 (by omega))
    (fun x e1 e2 => lf_ro (by omega) (by omega)) noLD (by omega)
    (wl_stk htop' (by omega) (by omega)) hFv (fun _ e1 e2 => lw_var e1 e2)
  have hsi' : (lifY W Z).r12 ≠ 0 := by
    rw [e12]
    exact ne0_of hav
  have c46 : (7866080#64 + 64#64 : Addr).toNat = 7866144 := by decide
  -- the call and `lif_ok`
  refine Lif.ptr_call hc hKZ hAZ hlsm (hrip.trans (by decide)) hLC.lif
    (wl_stk (x := Z.cpu.gpr.rsp - 8) htop' (by omega) (by omega)) ?_
  intro Y t' hKY hAY hrY hgY
  have hYr : Y.cpu.gpr.rsp = (entG Z).rsp := congrArg Gprs.rsp hgY
  exact Ndi.lif_ok (ip := []) (X := Y) (t := t') (W := lifW W Z) (V := entV W Z) (sp := lifSp Z) (gY := lifY W Z)
    (G := lifG lo top B L) (Wl' := (lifG lo top B L).writes) (N := brkN B) (b := B + 4544#64)
    (fsb := B + 2176#64) (pad := 0x20000#64) (sm := 0#64) (mx := 0#64) (lp := 7938752#64) (ct := 7866080#64)
    (a0 := a0) (ca := 7299392#64) (cb := 7296832#64) (cc := 7295296#64) (n := n) (e₃ := lsm_at)
    (code₃ := lsm) (j₃ := 1017) (hw := hw) (cnt := cnt) (Ec := Ec) (H := H) (sz := sz) (q := q) (m := m)
    (hinL := hLC.lif) (hK := hKY) (hA := hAY) (hrip := hrY) (hR := hYr.trans e152.symm)
    (hst0 := by rw [hYr]; exact wl_stk htop' (by omega) (by omega)) (hsp0 := by rw [hYr]; omega)
    (l1 := l1) (l2 := l2) (lw := lw) (la := la) (lb := lb) (lE := lE)
    (hfw := vst_fw (by omega) hr' (ptr_fw hK hI hM hfp hbl hb' hbp hW (fun _ _ => trivial) (fun _ _ => trivial)))
    (hW := by rw [hgY]) (hgY := by rw [hgY])
    (c := hc) (mc := mc) (cx := cx) (hgo := hLC.gor) (hsn := hsn)
    (htop := by unfold userPtrMax; split <;> omega)
    (hpw := hpw) (hst := hst) (hsm := hsm) (hlo := by omega) (hbs := by omega)
    (hbuf := lf_stk htop' (by omega) (by omega)) (hfr := lf_stk htop' (by omega) (by omega))
    (hpf := hpf) (hpn := hpn') (hpz := hpz') (hpp := hpp') (hof := hof) (hoz := hoz') (hps := hpse)
    (hpre := hpre) (hinc := hinc) (hc0 := hcc) (hcpy := hcpy)
    (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5) (ke := ke)
    (hin := hLC.ipa) (hinh := hLC.hwc) (hcpq := hcpq) (hinm := hinm) (hm0 := hm0) (hinX := hLC.mnx)
    (hinI := hLC.imm) (hinl := hinl) (hl0 := hl0) (hlenA := hlenA) (hinz := hinz) (hz0 := hz0) (hset := hset)
    (hint := hLC.tgv) (hn := hn) (hPq := hPq) (hPk := hPk) (hPs := hPs) (he := by omega) (hal := nal)
    (hFs := hFs) (hpg := hpg) (hx1 := x1) (hx1z := x1z) (hx2 := x2) (hx2z := x2z) (htls := htls) (hU := hU)
    (hm6 := m6) (hhw := hhw') (hfh := hfh) (hfm := hfm) (hpl0 := pl0) (hf1 := hf1) (hf2 := hf2) (hWb := hWb)
    (hfN := hfN) (hW7a := hW7a) (hW7b := hW7b) (hFR := hFR) (hlenV := lenV) (hslV := slV) (hpl := hpl)
    (hid := hLC.dpr) (him := hLC.mpr) (hfp := hfp') (hph := ph) (hpgs := pgs) (hla := la') (hmg := hmg)
    (hGo := hGo) (hGc := hGc) (hfit := hfit) (hGw := hGw) (hGr := hGr) (hcode := hcode) (hww := hww)
    (hlG := hlG) (hl := hl) (hinS := hLC.ims) (hci := hLC.cti) (hir := hir) (hr0 := hr0) (hrchr := hrchr)
    (hbk := by omega) (hfl := by omega) (hfsp := by omega) (hs := by omega) (hst₂ := hst₂) (hl₂ := hl₂)
    (hgl := fun i hi => by
      have t := tg (b := 7942968) (n := 16) hi (by omega)
      exact gw_var (by omega) (by omega))
    (hsi := hsi') (fa := by rw [e12]; exact gd_stk htop' (by omega) (by omega))
    (ha0 := by rw [e12]; exact ha0) (hnz := hnz) (hrs := by rw [e12]; omega) (hr8 := by rw [e12]; omega)
    (nfit := nfit) (nnz := nnz) (nz := nz) (hns := by omega)
    (npg := fun x e1 e2 => by
      obtain ⟨p1, p2⟩ := pg_in ht4 (show lo + 4096 ≤ a0.toNat by omega) ha2 e1 e2
      exact gd_stack htop' p1 p2)
    (hPr := hPr) (hlp := hlp) (hct := hct) (ha := hca) (hb := hcb) (hc := hcc')
    (hlg := ⟨by decide, by decide⟩) (hcg := by decide)
    (f1 := fun i hi => by
      have t := toNat_add_of_fits (a := B + 2176#64 - 112#64) (n := 8) hi (by omega)
      exact gd_brk (by omega) (by omega))
    (f2 := fun i hi => by
      have t := tg (b := 7938752) (n := 8) hi (by omega)
      exact gd_var (by omega) (by omega))
    (f3 := fun i hi => by
      have t := toNat_add_of_fits (a := 7866080#64 + 64#64) (n := 32) hi (by omega)
      exact gd_relro (by omega) (by omega))
    (fw := fun i hi => by
      have t := toNat_add_of_fits (a := B + 2176#64 - 64#64) (n := 24) hi (by omega)
      exact gw_brk (by omega) (by omega))
    (hin₃ := hlsm) (h₃ := by rw [lsm_length]; decide)
    (hra := by rw [e152]; exact rd_ra hr hr') (k := k)

end FV7z.Start
