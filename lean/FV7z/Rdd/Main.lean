import FV7z.Rdd.Br
import FV7z.Rdd.Loop
/-!
# `__readdir`: the buffer used up, `__getdents` (PLAN.md §M, M1)

`rdd_gd`: from 109 with the offset at the size `n`: `vc_109g`, the `call __getdents (fd, buf, allocation)` at 128
(`s_call`), then `Gdn.gdn_ok` with the return address `rdd_at + 133`. After it, on the segment from the state after
the `syscall`: an error goes to `gd_err`; else the answer is the size of the entries (`dn_ret`, at most the
allocation by `dentsRes_sum`), 0 to `gd_zero`, positive to `gd_pos`.

Next: `rdd_ok` (`vc_0`, `s_cmpxchg_bd32` at 52, `vc_56`, then `scan` with `Hgd := rdd_gd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Rdd

variable {F : Footprint} {Wl : List Rgn} {S p fb : Addr} {A : Nat}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem s4r (G : Gprs) (v : BitVec 64) : (G.set 4 v).rsi = G.rsi ∧ (G.set 4 v).rdx = G.rdx := by
  cases G; exact ⟨rfl, rfl⟩

theorem s0r (G : Gprs) (v : BitVec 64) : (G.set 0 v).rdx = G.rdx := by cases G; rfl

/-- From 109 with the buffer used up: `__getdents`, then the ways after it. -/
theorem rdd_gd {g0 : Gprs} {V₀ W : Addr → Byte} {Y : State} {t : Nat} {n : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (hinG : CodeIn L Gdn.gdn_at Gdn.gdn) (C : RdC F Wl S p fb A)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = rdd_at.add 109)
    (R : LR S p g0 n Y.cpu.gpr) (M : LM S p fb A g0 V₀ W n n) (hD : Dir W p A 1#32 n n)
    (hdx : Y.cpu.gpr.rdx.toNat = n) (hni : NzIno o) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A g0 V₀ e₂ j₂ gev) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨b5, b6, b7, -, -, -, -⟩ := stR S C.h48
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have hA31 := C.hA
  have dS := C.dS
  have eS := C.eS
  have eD := C.eD
  have hfe := C.hfe
  have t8 : (p + 8#64).toNat = p.toNat + 8 := Opd.tAdd p 8 (by omega)
  have t48 : (p.add 48).toNat = p.toNat + 48 := tna p 48 (by omega)
  have t48' : (p + 48#64).toNat = p.toNat + 48 := Opd.tAdd p 48 (by omega)
  have p48 : p + 48#64 = Addr.add p 48 := Opd.fa (B := p) (d := 48) (by omega) t48'
  have pd : ∀ i < 48 + A, Foot F.data (Addr.add p i) := fun i hi => c.hws _ (C.pw i hi)
  -- 109 to 128
  have hl : ¬ Y.cpu.gpr.rdx.toNat < Y.cpu.gpr.rax.toNat := by rw [hdx, R.ax]; exact Nat.lt_irrefl n
  have f8 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.r14 + 8#64) i) := by
    rw [R.di]; exact Opd.frw pd (Opd.fa (B := p) (d := 8) (by omega) t8) (by omega)
  have f0 : ∀ i < 4, Foot F.data (Addr.add Y.cpu.gpr.r14 i) := by
    rw [R.di]; exact Opd.frw pd (addr_add_zero p).symm (by omega)
  refine (c_109 prof fb).run c hfs hin _ hK hA hrip (vc_109g (g := Y.cpu.gpr) hl f8 f0) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have y1 : Y₁.cpu.gpr.rsp - 8 = S - 8 - 8 - 8 - 8 - 8 - 8 := by
    rw [hg₁]; show Y.cpu.gpr.rsp - 8 = _; rw [R.sp]
  have sl : S - 8 - 8 - 8 - 8 - 8 - 8 = Addr.add (S - 48#64) 0 :=
    Opd.fa (B := S - 48#64) (d := 0) (by omega) (by omega)
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y₁.cpu.gpr.rsp - 8) i) := by
    rw [y1]; exact Opd.frw C.sw sl (by omega)
  -- the call
  refine c.s_call hK₁ hA₁ hin (lt_len (j := 128) (by decide)) hr₁ (call_128 _) hinG
    (Gdn.lt_len (j := 0) (by decide)) tgt_128 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [y1] at hA₂
  have hal2 : (S - 8 - 8 - 8 - 8 - 8 - 8).toNat + (toBytesLE (rdd_at.add (128 + 5)) 8).length ≤ 2 ^ 64 := by
    rw [toBytesLE_length]; omega
  have hra2 : ofBytesLE 64 ((byteAddrs (S - 8 - 8 - 8 - 8 - 8 - 8) 8).map
      (Vst W (S - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE (rdd_at.add (128 + 5)) 8))) = rdd_at.add 133 := by
    rw [rd_Vst_self W (S - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE (rdd_at.add (128 + 5)) 8) (toBytesLE_length _ _)
      (by omega), ofBytesLE_toBytesLE (by decide)]
    try rfl
  obtain ⟨s2, r2, d2⟩ := gst (g0 := g0) (V₀ := V₀) (S - 8 - 8 - 8 - 8 - 8 - 8)
    (toBytesLE (rdd_at.add (128 + 5)) 8) C hal2 (by rw [toBytesLE_length]; omega)
    (fun x x1 x2 => Or.inl ⟨by omega, by rw [toBytesLE_length] at x2; omega⟩)
    (by rw [toBytesLE_length]; omega) M.sv M.fr hD
  generalize Vst W (S - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE (rdd_at.add (128 + 5)) 8) = W₂ at hA₂ hra2 s2 r2 d2
  -- the registers at `__getdents`
  have rsp2 : Y₂.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8 - 8 := by rw [hg₂, Opd.set4_rsp, y1]
  have rsi2 : Y₂.cpu.gpr.rsi = p + 48#64 := by
    rw [hg₂, (s4r _ _).1, hg₁]; exact R.bx
  have rdx2 : Y₂.cpu.gpr.rdx = rdq(W, p + 8#64) := by
    rw [hg₂, (s4r _ _).2, hg₁]; show rdq(W, Y.cpu.gpr.r14 + 8#64) = _; rw [R.di]
  have hdA : Y₂.cpu.gpr.rdx.toNat = A := by rw [rdx2]; exact hD.al
  have k1 : Opd.Keeps Y.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have k12 : Opd.Keeps Y.cpu.gpr Y₂.cpu.gpr := k1.trans (by rw [hg₂]; exact Opd.set4K _ _)
  refine Gdn.gdn_ok c hfs hrs hinG hK₂ hA₂ hr₂ (by rw [hdA]; exact hA31)
    (by rw [hdA, rsi2, p48]; exact Opd.frw C.pw (Opd.fa (B := p) (d := 48) (by omega) t48) (by omega))
    (by rw [hdA, rsi2, t48']; omega) (by rw [hdA, rsi2, t48', rsp2]; omega) C.fe hfe
    (by rw [rsp2, sl]; exact fun i hi => c.hws _ (Opd.frw C.sw rfl (by omega) i hi))
    (by rw [rsp2]; omega) (by rw [rsp2]; omega) (hin₂ := hin) (h₂ := lt_len (j := 133) (by decide))
    (by rw [rsp2]; exact hra2) ?_
  intro S' t₃ r hr hKS hAS hgS c' Z t' hKZ hrZ hok herr
  have hfs' : (Gdn.gdS S' r).cpu.seg.fsBase = fb := by
    show S'.cpu.seg.fsBase = fb
    rw [hKS.seg]; exact hfs
  have hrs' : (Gdn.gdS S' r).thread.rseq = none := by
    show S'.thread.rseq = none
    rw [hKS.thread]; exact hrs
  have k3 : Opd.Keeps Y.cpu.gpr S'.cpu.gpr := k12.trans (by rw [hgS]; exact (set0K _ _).1)
  have hT : RdT gev (gev ++ [Gdn.gdE Y₂.cpu.gpr r]) := Or.inr ⟨_, _, rfl⟩
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := gdZ (dnSt S' r) r.ret (Y₂.cpu.gpr.rsp + 8)
  by_cases hce : CloseErr r.ret
  · obtain ⟨hAZ, hgZ⟩ := herr hce
    have hgZ' : Z.cpu.gpr = (Lseek.lsErrG ((sysGpr (dnSt S' r) 2).set 0 r.ret)).set 4 (Y₂.cpu.gpr.rsp + 8) := hgZ
    have kk : Opd.Keeps Y.cpu.gpr Z.cpu.gpr := k3.trans (by rw [hgZ']; exact z5)
    rw [rsi2, hdA, p48] at hAZ
    have hbl : (dnBuf W₂ (p.add 48) A r).length = A := by rw [List.length_map, byteAddrs_len]
    obtain ⟨s3, r3, d3⟩ := gst (g0 := g0) (V₀ := V₀) (p.add 48) (dnBuf W₂ (p.add 48) A r) C
      (by rw [hbl]; omega) (by rw [hbl]; omega) (fun x x1 x2 => Or.inr (Or.inl ⟨by omega, by omega⟩))
      (by rw [hbl]; omega) s2 r2 d2
    have hel : (toBytesLE (0 - r.ret.setWidth 32) 4).length = 4 := toBytesLE_length _ _
    obtain ⟨s4, r4, d4⟩ := gst (g0 := g0) (V₀ := V₀) (errnoAt fb) (toBytesLE (0 - r.ret.setWidth 32) 4) C
      (by rw [hel]; exact hfe) (by rw [hel]; omega)
      (fun x x1 x2 => Or.inr (Or.inr ⟨x1, by rw [hel] at x2; exact x2⟩)) (by rw [hel]; omega) s3 r3 d3
    exact gd_err c' hfs' hrs' hin C hKZ hAZ hrZ (by rw [hgZ', z4, rsp2, BitVec.sub_add_cancel])
      (kk.2.2.2.2.1.trans R.di) (kk.2.2.2.2.2.trans R.r15) (kk.2.1.trans R.bp) (by rw [hgZ']; exact z6)
      s4 r4 d4 hT hmt0 hin₂ h₂ hra K
  · obtain ⟨hAZ, hgZ⟩ := hok hce
    have hgZ' : Z.cpu.gpr = ((sysGpr (dnSt S' r) 2).set 0 r.ret).set 4 (Y₂.cpu.gpr.rsp + 8) := hgZ
    have kk : Opd.Keeps Y.cpu.gpr Z.cpu.gpr := k3.trans (by rw [hgZ']; exact z2)
    rw [rsi2, hdA, p48] at hAZ
    have hbl : (dnBuf W₂ (p.add 48) A r).length = A := by rw [List.length_map, byteAddrs_len]
    obtain ⟨s3, r3, d3⟩ := gst (g0 := g0) (V₀ := V₀) (p.add 48) (dnBuf W₂ (p.add 48) A r) C
      (by rw [hbl]; omega) (by rw [hbl]; omega) (fun x x1 x2 => Or.inr (Or.inl ⟨by omega, by omega⟩))
      (by rw [hbl]; omega) s2 r2 d2
    have hret : r.ret = BitVec.ofNat 64 (r.es.map Dirent.reclen).sum := by
      rw [hr] at hce ⊢; exact dn_ret hce
    have hsum : (r.es.map Dirent.reclen).sum ≤ A := by
      have h1 := dentsRes_sum (o := o) (t := t₃) (s := S')
      rw [← hr] at h1
      have h32 : arg32 Y₂.cpu.gpr.rdx = Y₂.cpu.gpr.rdx.toNat :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show Y₂.cpu.gpr.rdx.toNat ≤ 2147483647 by rw [hdA]; exact hA31)
          (by decide))
      have h2 : arg32 S'.cpu.gpr.rdx = A := by rw [hgS, s0r, h32, hdA]
      omega
    have haxZ : Z.cpu.gpr.rax = BitVec.ofNat 64 (r.es.map Dirent.reclen).sum := by rw [hgZ', z3, hret]
    have hspZ : Z.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8 := by rw [hgZ', z1, rsp2, BitVec.sub_add_cancel]
    by_cases h0 : (r.es.map Dirent.reclen).sum = 0
    · exact gd_zero c' hfs' hrs' hin C hKZ hAZ hrZ hspZ (kk.2.2.2.2.1.trans R.di) (kk.2.2.2.2.2.trans R.r15)
        (kk.2.1.trans R.bp) (by rw [haxZ, h0]; try rfl) s3 r3 d3 hT hmt0 hin₂ h₂ hra K
    · exact gd_pos c' hfs' hrs' hin C hKZ hAZ hrZ hspZ (kk.2.2.2.2.1.trans R.di) (kk.2.2.2.2.2.trans R.r15)
        (kk.2.1.trans R.bp) (kk.1.trans R.bx) rfl hsum (by omega)
        (fun e he => hni t₃ S' e (by rw [← hr]; exact he)) haxZ s3 r3 d3 hT hmt0 hin₂ h₂ hra K

end FV7z.Rdd
