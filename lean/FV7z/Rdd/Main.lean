import FV7z.Rdd.Br
import FV7z.Rdd.Loop
/-!
# `__readdir`: the buffer used up, `__getdents` (PLAN.md §M, M1)

`rdd_gd`: from 109 with the offset at the size `n`: `vc_109g`, the `call __getdents (fd, buf, allocation)` at 128
(`s_call`), then `Gdn.gdn_ok` with the return address `rdd_at + 133`. After it, on the segment from the state after
the `syscall`: an error goes to `gd_err`; else the answer is the size of the entries (`dn_ret`, at most the
allocation by `dentsRes_sum`), 0 to `gd_zero`, positive to `gd_pos`.

`rdd_ok`: from the entry, `vc_0` (the pushes, `P5_out`, `P5_sv`), the lock taken at 52 (`s_cmpxchg_bd32`,
`Dir_mk`), `vc_56`, then `scan` from the offset `k` with `Hgd := rdd_gd`.
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

/-! ## From the entry to 109 -/

/-- A byte the five pushes did not store. -/
theorem P5_out (V : Addr → Byte) (g : Gprs) (h : 48 ≤ g.rsp.toNat) (a : Addr)
    (ha : a.toNat < g.rsp.toNat - 40 ∨ g.rsp.toNat ≤ a.toNat) : P5 V g a = V a := by
  have hS := g.rsp.isLt
  have b1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := Opd.tSub g.rsp 8 (by omega)
  have b2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := (Opd.tSub (g.rsp - 8) 8 (by omega)).trans (by omega)
  have b3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 :=
    (Opd.tSub (g.rsp - 8 - 8) 8 (by omega)).trans (by omega)
  have b4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 :=
    (Opd.tSub (g.rsp - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b5 : (g.rsp - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 40 :=
    (Opd.tSub (g.rsp - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  dsimp only [P5]
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length])
  all_goals omega

/-- The five pushes are where the pops read them. -/
theorem P5_sv (V : Addr → Byte) (g : Gprs) (h : 48 ≤ g.rsp.toNat) : RSv g.rsp g (P5 V g) := by
  have hS := g.rsp.isLt
  have b1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := Opd.tSub g.rsp 8 (by omega)
  have b2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := (Opd.tSub (g.rsp - 8) 8 (by omega)).trans (by omega)
  have b3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 :=
    (Opd.tSub (g.rsp - 8 - 8) 8 (by omega)).trans (by omega)
  have b4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 :=
    (Opd.tSub (g.rsp - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b5 : (g.rsp - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 40 :=
    (Opd.tSub (g.rsp - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have e : ∀ (x : Addr) (v : BitVec 64) (W : Addr → Byte), x.toNat + 8 ≤ 2 ^ 64 →
      rdq(Vst W x (toBytesLE v 8), x) = v := fun x v W h1 => by
    rw [rd_Vst_self W x (toBytesLE v 8) (toBytesLE_length v 8) h1, ofBytesLE_toBytesLE (by decide)]
  unfold RSv
  simp only [BitVec.sub_add_cancel]
  dsimp only [P5]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact e (g.rsp - 8 - 8 - 8 - 8 - 8) g.rbx _ (by omega)
  · rw [rdS 64 _ (g.rsp - 8 - 8 - 8 - 8 - 8) g.rbx (g.rsp - 8 - 8 - 8 - 8) 8 (by omega) (by omega) (by omega)]
    exact e (g.rsp - 8 - 8 - 8 - 8) g.rbp _ (by omega)
  · rw [rdS 64 _ (g.rsp - 8 - 8 - 8 - 8 - 8) g.rbx (g.rsp - 8 - 8 - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8 - 8 - 8) g.rbp (g.rsp - 8 - 8 - 8) 8 (by omega) (by omega) (by omega)]
    exact e (g.rsp - 8 - 8 - 8) g.r12 _ (by omega)
  · rw [rdS 64 _ (g.rsp - 8 - 8 - 8 - 8 - 8) g.rbx (g.rsp - 8 - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8 - 8 - 8) g.rbp (g.rsp - 8 - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8 - 8) g.r12 (g.rsp - 8 - 8) 8 (by omega) (by omega) (by omega)]
    exact e (g.rsp - 8 - 8) g.r13 _ (by omega)
  · rw [rdS 64 _ (g.rsp - 8 - 8 - 8 - 8 - 8) g.rbx (g.rsp - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8 - 8 - 8) g.rbp (g.rsp - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8 - 8) g.r12 (g.rsp - 8) 8 (by omega) (by omega) (by omega),
      rdS 64 _ (g.rsp - 8 - 8) g.r13 (g.rsp - 8) 8 (by omega) (by omega) (by omega)]
    exact e (g.rsp - 8) g.r14 _ (by omega)

/-- The `DIR`'s fields through bytes that agree on `[p + 8, p + 32)`, with the lock word `w'`. -/
theorem Dir_mk {V V' : Addr → Byte} {w w' : BitVec 32} {n k : Nat} (hpA : p.toNat + 48 + A < 2 ^ 64)
    (hD : Dir V p A w n k) (hl : rdd(V', p + 4#64) = w')
    (h : ∀ a : Addr, p.toNat + 8 ≤ a.toNat → a.toNat < p.toNat + 32 → V' a = V a) : Dir V' p A w' n k := by
  have t8 : (p + 8#64).toNat = p.toNat + 8 := Opd.tAdd p 8 (by omega)
  have t16 : (p + 16#64).toNat = p.toNat + 16 := Opd.tAdd p 16 (by omega)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  refine ⟨hl, ?_, ?_, hD.nA, ?_⟩
  · rw [rdE 64 (V := V) (V' := V') (x := p + 8#64) (n := 8) (by omega) fun a x1 x2 => h a (by omega) (by omega)]
    exact hD.al
  · rw [rdE 64 (V := V) (V' := V') (x := p + 16#64) (n := 8) (by omega) fun a x1 x2 => h a (by omega) (by omega)]
    exact hD.sz
  · rw [rdE 64 (V := V) (V' := V') (x := p + 24#64) (n := 8) (by omega) fun a x1 x2 => h a (by omega) (by omega)]
    exact hD.of

/-- `__readdir (p)` from its entry, one thread, the `DIR` unlocked with the size `n` and the offset `k`, a chain of
entries from `k` to `n` in its buffer: the run after the return (`K`). -/
theorem rdd_ok {V₀ : Addr → Byte} {X : State} {t : Nat} {n k : Nat} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L rdd_at rdd) (hinG : CodeIn L Gdn.gdn_at Gdn.gdn) (C : RdC F Wl S p fb A)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V₀) (hrip : X.cpu.rip = rdd_at)
    (hsp : X.cpu.gpr.rsp = S) (hdi : X.cpu.gpr.rdi = p) (hD : Dir V₀ p A 0#32 n k) (hch : Ch V₀ p n k)
    (hni : NzIno o) (hmt0 : rdd(V₀, fb + 24#64) = 0#32)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V₀, S) = e₂.add j₂)
    (K : RddK prof F Wl L o gP gE S p fb A X.cpu.gpr V₀ e₂ j₂ gev) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, -, b7, -, -, -, -⟩ := stR S C.h48
  have hS := S.isLt
  have h48 := C.h48
  have hS8 := C.hS8
  have hpA := C.hpA
  have dS := C.dS
  have mS := C.mS
  have hspN : X.cpu.gpr.rsp.toNat = S.toNat := by rw [hsp]
  have h48' : 48 ≤ X.cpu.gpr.rsp.toNat := by rw [hspN]; exact h48
  have c1 : (S - 8).toNat = S.toNat - 8 := Opd.tSub S 8 (by omega)
  have c2 : (S - 8 - 8).toNat = S.toNat - 16 := (Opd.tSub (S - 8) 8 (by omega)).trans (by omega)
  have c3 : (S - 8 - 8 - 8).toNat = S.toNat - 24 := (Opd.tSub (S - 8 - 8) 8 (by omega)).trans (by omega)
  have c4 : (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 := (Opd.tSub (S - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have c5 : (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 :=
    (Opd.tSub (S - 8 - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have t4 : (p + 4#64).toNat = p.toNat + 4 := Opd.tAdd p 4 (by omega)
  have t16 : (p + 16#64).toNat = p.toNat + 16 := Opd.tAdd p 16 (by omega)
  have t24 : (p + 24#64).toNat = p.toNat + 24 := Opd.tAdd p 24 (by omega)
  have pd : ∀ i < 48 + A, Foot F.data (Addr.add p i) := fun i hi => c.hws _ (C.pw i hi)
  have sw : ∀ (x : Addr) (d : Nat), d + 8 ≤ 48 → x.toNat = S.toNat - 48 + d →
      ∀ i < 8, Foot Wl (Addr.add x i) :=
    fun x d hd hx => Opd.frw C.sw (Opd.fa (B := S - 48#64) (d := d) (by omega) (by rw [hx, b7])) (by omega)
  have po : ∀ a : Addr, (a.toNat < S.toNat - 40 ∨ S.toNat ≤ a.toNat) → P5 V₀ X.cpu.gpr a = V₀ a :=
    fun a ha => P5_out V₀ X.cpu.gpr h48' a (by rw [hspN]; exact ha)
  have hmt : rdd(P5 V₀ X.cpu.gpr, fb + 24#64) = 0#32 := by
    rw [rdE 32 (V := V₀) (V' := P5 V₀ X.cpu.gpr) (x := fb + 24#64) (n := 4) C.hfm fun a x1 x2 => po a (by omega)]
    exact hmt0
  -- 0 to 52: the pushes, `errno` saved
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (g := X.cpu.gpr) (V := V₀) (fb := fb) (e0 := rdd(P5 V₀ X.cpu.gpr, errnoAt fb)) rfl hmt
      (by rw [hsp]; exact sw (S - 8) 40 (by omega) (by omega))
      (by rw [hsp]; exact sw (S - 8 - 8) 32 (by omega) (by omega))
      (by rw [hsp]; exact sw (S - 8 - 8 - 8) 24 (by omega) (by omega))
      (by rw [hsp]; exact sw (S - 8 - 8 - 8 - 8) 16 (by omega) (by omega))
      (by rw [hsp]; exact sw (S - 8 - 8 - 8 - 8 - 8) 8 (by omega) (by omega))
      (fun i hi => c.hws _ (C.fe i hi)) C.fm) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  -- 52: the lock taken
  have ea₁ : eaD Y₁ 7 4 = p + 4#64 := by
    rw [eaD, hg₁]
    show X.cpu.gpr.rdi + _ = _
    rw [hdi]
  have rv0 : rv Y₁ 32 0 = 0#32 := by rw [rv, hg₁]; rfl
  have rv2 : rv Y₁ 32 2 = 1#32 := by rw [rv, hg₁]; rfl
  have lk0 : ofBytesLE 32 ((byteAddrs (eaD Y₁ 7 4) 4).map (P5 V₀ X.cpu.gpr)) = rv Y₁ 32 0 := by
    rw [ea₁, rv0, rdE 32 (V := V₀) (V' := P5 V₀ X.cpu.gpr) (x := p + 4#64) (n := 4) (by omega)
      fun a x1 x2 => po a (by omega)]
    exact hD.lk
  refine c.s_cmpxchg_bd32 hK₁ hA₁ hin (lt_len (j := 52) (by decide)) hr₁ (cx_52 _)
    (by rw [ea₁]; exact Opd.frw C.pw (Opd.fa (B := p) (d := 4) (by omega) t4) (by omega)) lk0 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
  rw [ea₁, rv2] at hA₂
  -- the bytes with the lock taken
  have r0 : RFr S p fb A V₀ (P5 V₀ X.cpu.gpr) := by
    unfold RFr
    intro a x1 x2 x3
    exact po a (by omega)
  have s0 : RSv S X.cpu.gpr (P5 V₀ X.cpu.gpr) := by
    have h := P5_sv V₀ X.cpu.gpr h48'
    rw [hsp] at h
    exact h
  obtain ⟨s1, r1, b1⟩ := dst (g0 := X.cpu.gpr) (V₀ := V₀) (p + 4#64) (toBytesLE 1#32 4) C (by omega)
    (by rw [toBytesLE_length]; omega) s0 r0
  have lk1 : rdd(Vst (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4), p + 4#64) = 1#32 := by
    rw [rd_Vst_self (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4) (toBytesLE_length _ _) (by omega),
      ofBytesLE_toBytesLE (by decide)]
  have D₁ : Dir (Vst (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4)) p A 1#32 n k :=
    Dir_mk hpA hD lk1 fun a x1 x2 => by
      rw [Vst_out (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4) a (by rw [toBytesLE_length]; omega)
        (by rw [toBytesLE_length]; omega)]
      exact po a (by omega)
  have M₁ : LM S p fb A X.cpu.gpr V₀ (Vst (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4)) n k :=
    ⟨s1, r1, ⟨k, D₁⟩, Ch.congr (fun i hi => by
      have hnA := hD.nA
      have hx := tna p (48 + i) (by omega)
      rw [b1 i (by omega)]
      exact po _ (by omega)) hch⟩
  generalize Vst (P5 V₀ X.cpu.gpr) (p + 4#64) (toBytesLE 1#32 4) = W₁ at hA₂ D₁ M₁
  -- 56 to 109: the offset, the size, the buffer
  have r14₂ : Y₂.cpu.gpr.r14 = p := by rw [hg₂, hg₁]; exact hdi
  refine (c_56 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_56 (g := Y₂.cpu.gpr)
    (by rw [r14₂]; exact Opd.frw pd (Opd.fa (B := p) (d := 24) (by omega) t24) (by omega))
    (by rw [r14₂]; exact Opd.frw pd (Opd.fa (B := p) (d := 16) (by omega) t16) (by omega))) ?_
  rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have a3 : Y₃.cpu.gpr.rax = rdq(W₁, p + 16#64) := by
    rw [hg₃]; show rdq(W₁, Y₂.cpu.gpr.r14 + 16#64) = _; rw [r14₂]
  have d3 : Y₃.cpu.gpr.rdx = rdq(W₁, p + 24#64) := by
    rw [hg₃]; show rdq(W₁, Y₂.cpu.gpr.r14 + 24#64) = _; rw [r14₂]
  have R₃ : LR S p X.cpu.gpr n Y₃.cpu.gpr :=
    { sp := ((congrArg Gprs.rsp hg₃).trans ((congrArg Gprs.rsp hg₂).trans (congrArg Gprs.rsp hg₁))).trans
        (congrArg (fun x : Addr => x - 8 - 8 - 8 - 8 - 8) hsp)
      bx := (congrArg Gprs.rbx hg₃).trans (congrArg (fun x : Addr => x + 48#64) r14₂)
      bp := (congrArg Gprs.rbp hg₃).trans ((congrArg Gprs.rbp hg₂).trans (congrArg Gprs.rbp hg₁))
      di := (congrArg Gprs.r14 hg₃).trans r14₂
      r15 := (congrArg Gprs.r15 hg₃).trans ((congrArg Gprs.r15 hg₂).trans (congrArg Gprs.r15 hg₁))
      ax := by rw [a3]; exact D₁.sz }
  exact scan (g0 := X.cpu.gpr) (V₀ := V₀) (tr := gev) (n := n) c hfs hrs hin C (Or.inl rfl) hmt0 hin₂ h₂ hra K
    (fun Y W t hK hA hr R M hD hdx => rdd_gd c hfs hrs hin hinG C hK hA hr R M hD hdx hni hmt0 hin₂ h₂ hra K)
    (n - k) k Y₃ W₁ t₃ (Nat.le_refl _) hch.le hK₃ hA₃ hr₃ R₃ M₁ D₁ (by rw [d3]; exact D₁.of)

end FV7z.Rdd
