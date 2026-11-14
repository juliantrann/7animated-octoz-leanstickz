import FV7z.Hwc.Head
import FV7z.Tgv.Holds
import FV7z.Lemmas.Rmw5
import Std.Tactic.BVDecide
/-!
# `_dl_important_hwcaps`: the entry → the `ret` (PLAN.md G3, startup)

From the entry (`rsp = bp + 8`, `bp` 16-aligned): the prologue (`vc_0`), `__tunable_get_val (11, rbp - 0x38, NULL)`
for `glibc.cpu.hwcap_mask` (not set: its default 6, `Tgv.tgv64_ok`), the mask and `_dl_hwcap` (`vc_66`), the loop
that counts the bits (`vc_112`, `vc_132n`, `vc_132`: `cnt` 3 or 4), the `alloca` and the stack probe of the slot of
the return address of 61 (1772, `Seg.s_or_mi64i`: the bytes as they were, `Gor.probe_same`), then `from1778_3`,
`from1778_4`.

- `vc_132n`: a bit of the loop that is not the last (`vc_132` takes the count, for the last).
- `At0`: what the caller gets at the `ret` (1681).
- `from0`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Hwc

set_option maxRecDepth 100000

/-! ## Small facts -/

theorem tgt_61 : hwc_at.add (61 + 5) + BitVec.ofNat 64 18446744073709298206 = Tgv.tgv_at := by decide
theorem eent : Tgv.ent 11#64 = 7936200#64 := by decide

section
variable {bp : Addr} (h1 : 264 ≤ bp.toNat) (h2 : bp.toNat + 8 ≤ 2 ^ 64)
include h1 h2
theorem fbb : (bp + 18446744073709551448#64).toNat + 168 = bp.toNat := by bv_omega
theorem f440 : (bp + 18446744073709551440#64).toNat + 176 = bp.toNat := by bv_omega
theorem f432 : (bp + 18446744073709551432#64).toNat + 184 = bp.toNat := by bv_omega
theorem f560 : (bp + 18446744073709551560#64).toNat + 56 = bp.toNat := by bv_omega
theorem f376 : (bp + 18446744073709551376#64).toNat + 240 = bp.toNat := by bv_omega
theorem f360 : (bp + 18446744073709551360#64).toNat + 256 = bp.toNat := by bv_omega
end

theorem bp8 {bp : Addr} (h : bp.toNat + 16 ≤ 2 ^ 64) : (bp + 8#64).toNat = bp.toNat + 8 := by bv_omega

/-- The registers other than `rsp` after a `call` (`set 4`), by `rfl` on a variable (with the value a literal sum
the unifier goes down `BitVec.add`). -/
theorem set4_rsi (g : Gprs) (v : Addr) : (g.set 4 v).rsi = g.rsi := rfl
theorem set4_rdi (g : Gprs) (v : Addr) : (g.set 4 v).rdi = g.rdi := rfl
theorem set4_rbp (g : Gprs) (v : Addr) : (g.set 4 v).rbp = g.rbp := rfl
theorem set4_r15 (g : Gprs) (v : Addr) : (g.set 4 v).r15 = g.r15 := rfl

theorem n1 (bp : Addr) : bp + 8#64 - 8 = bp := by bv_omega
theorem n2 (bp : Addr) : bp + 8#64 - 8 - 8 = bp + 18446744073709551608#64 := by bv_omega
theorem n3 (bp : Addr) : bp + 8#64 - 8 - 8 - 8 = bp + 18446744073709551600#64 := by bv_omega
theorem n4 (bp : Addr) : bp + 8#64 - 8 - 8 - 8 - 8 = bp + 18446744073709551592#64 := by bv_omega
theorem n5 (bp : Addr) : bp + 8#64 - 8 - 8 - 8 - 8 - 8 = bp + 18446744073709551584#64 := by bv_omega
theorem n6 (bp : Addr) : bp + 8#64 - 8 - 8 - 8 - 8 - 8 - 8 = bp + 18446744073709551576#64 := by bv_omega
theorem n7 (bp : Addr) : bp + 8#64 - 8 - 8 - 8 - 8 - 8 - 8 - 136#64 = bp + 18446744073709551440#64 := by bv_omega
theorem n184 (bp : Addr) : bp + 8#64 - 184#64 = bp + 18446744073709551440#64 := by bv_omega
theorem n8 (bp : Addr) : bp + 18446744073709551440#64 - 8 = bp + 18446744073709551432#64 := by bv_omega
theorem n9 (bp : Addr) : bp + 18446744073709551432#64 + 8#64 = bp + 18446744073709551440#64 := by bv_omega
theorem nR3 (bp : Addr) :
    bp + 18446744073709551440#64 - BitVec.ofNat 64 (16 * 3 + 16) = bp + 18446744073709551376#64 := by bv_omega
theorem nR4 (bp : Addr) :
    bp + 18446744073709551440#64 - BitVec.ofNat 64 (16 * 4 + 16) = bp + 18446744073709551360#64 := by bv_omega
theorem np3 (bp : Addr) : bp + 18446744073709551376#64 + BitVec.ofNat 64 (16 * 3 + 16) +
    BitVec.ofNat 64 18446744073709551608 = bp + 18446744073709551432#64 := by bv_omega
theorem np4 (bp : Addr) : bp + 18446744073709551360#64 + BitVec.ofNat 64 (16 * 4 + 16) +
    BitVec.ofNat 64 18446744073709551608 = bp + 18446744073709551432#64 := by bv_omega

/-- `temp` is 16-aligned when `bp` is. -/
theorem al3 {bp : Addr} (h : bp &&& 15#64 = 0#64) :
    (bp + 18446744073709551376#64 + 15#64) &&& 18446744073709551600#64 = bp + 18446744073709551376#64 := by
  bv_decide
theorem al4 {bp : Addr} (h : bp &&& 15#64 = 0#64) :
    (bp + 18446744073709551360#64 + 15#64) &&& 18446744073709551600#64 = bp + 18446744073709551360#64 := by
  bv_decide

/-- The prologue's bytes (`hV0`) with the slots as offsets from `bp`. -/
theorem hV0_bp (V : Addr → Byte) (g : Gprs) {bp : Addr} (h : g.rsp = bp + 8#64) : hV0 V g =
    Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
      bp (toBytesLE g.rbp 8)) (bp + 18446744073709551608#64) (toBytesLE g.r15 8))
      (bp + 18446744073709551600#64) (toBytesLE g.r14 8)) (bp + 18446744073709551592#64) (toBytesLE g.r13 8))
      (bp + 18446744073709551584#64) (toBytesLE g.r12 8)) (bp + 18446744073709551576#64) (toBytesLE g.rbx 8))
      (bp + 18446744073709551520#64) (toBytesLE g.rdi 8)) (bp + 18446744073709551512#64) (toBytesLE g.rsi 8))
      (bp + 18446744073709551528#64) (toBytesLE g.rdx 8))
      (bp + 18446744073709551488#64) (toBytesLE (bp + 18446744073709551560#64) 8))
      (bp + 18446744073709551504#64) (toBytesLE g.rcx 8) := by
  rw [hV0, h, n6, n5, n4, n3, n2, n1]

variable {F : Footprint} {Wl : List Rgn} {fb : Addr}

/-- A bit `c` of the loop that is not the last (bits of `r8` above it): `rcx = c + 1`, back to 112. -/
theorem vc_132n {g : Gprs} {f : Rflags} {V : Addr → Byte} {c : Nat} (hc : c < 63)
    (hcx : g.rcx = BitVec.ofNat 64 c) (hsi : g.rsi = 1#64) (hz : (0#64 - 1#64 <<< (c + 1)) &&& g.r8 ≠ 0#64) :
    W_132 fb F Wl (fun j' g' _ V' => V' = V ∧ j' = 112 ∧
      g' = { g with rax := 0#64 - 1#64 <<< (c + 1), rcx := BitVec.ofNat 64 (c + 1) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hcx hsi hz ⊢
  subst hcx hsi
  have e1 : BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es : (BitVec.setWidth 8 (BitVec.ofNat 64 (c + 1))).toNat % 64 = c + 1 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hz' : ((0#64 - 1#64 <<< (c + 1)) &&& r8 == 0#64) = false := by simp only [beq_eq_false_iff_ne]; exact hz
  wpx [W_132, o5, Op.shl64, e1, es, hz', Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies,
    true_implies, BitVec.ofNat_eq_ofNat, Bool.true_eq_false, Nat.reduceEqDiff, false_and, and_false, or_false,
    false_or, ne_eq, hz, not_false_eq_true]
  hcl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {cpy mlc sl : List Byte} {Pm Pa Pl : (Addr → Byte) → Prop}

/-- What the caller gets at the `ret` (1681): `rsp` on the return address, the registers a call keeps those of the
entry (`g`), the table at `P` (`Tab`), `ncapstr` (`*N = E`), `max_capstrlen` (`*Q`), the bytes below the
allocator's (`0x792980`) and above the frame as at the entry but for `*N`. -/
def At0 (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (V : Addr → Byte) (g : Gprs) (bp R Q N : Addr) (cnt E H s : Nat) : Prop :=
  ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (hl_ln cnt) cnt (fun _ => 0#64) 0) 8)) →
    Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ R.toNat - 8 →
    (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
    Y.cpu.gpr.rsp = bp + 8#64 → Y.cpu.gpr.rbx = g.rbx → Y.cpu.gpr.r12 = g.r12 → Y.cpu.gpr.r13 = g.r13 →
    Y.cpu.gpr.r14 = g.r14 → Y.cpu.gpr.r15 = g.r15 → Y.cpu.gpr.rbp = g.rbp →
    Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) H
      (hl_ln cnt (cnt - 1))) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) →
    SameO V W 0 7940480 N → SameO V W (bp.toNat + 8) (2 ^ 64) N →
    rdq(W, N) = BitVec.ofNat 64 E → GoG prof L o gev gP gE Y t'

set_option maxHeartbeats 16000000 in
/-- `_dl_important_hwcaps (p, 0, N, Q)` from its entry (`rsp = bp + 8`) to its `ret`: `h = _dl_hwcap` 2 or 6,
`glibc.cpu.hwcap_mask` not set (6), no vDSO; `cnt`, `E`, `H`, `s` and `temp` (`R`) as `h` gives them. -/
theorem from0 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hins : CodeIn L 4198664#64 sl) (hs0 : 0 < sl.length) (hlen : Str.LenAt prof L o 4198664#64 Pl)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {V : Addr → Byte} {h R bp Q N p : Addr} {cnt E H s : Nat}
    (hn : h = 2#64 ∧ cnt = 3 ∧ E = 8 ∧ H = 4 ∧ s = 151 ∧ R = bp + 18446744073709551376#64 ∨
      h = 6#64 ∧ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ s = 320 ∧ R = bp + 18446744073709551360#64)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < N.toNat ∨ N.toNat + 8 ≤ a.toNat) →
      W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < R.toNat - 8 → (a.toNat < N.toNat ∨ N.toNat + 8 ≤ a.toNat) →
      W a = V a) → Pa W)
    (hPl : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pl W)
    (hbl : 8388872 ≤ bp.toNat) (hbh : bp.toNat + 16 ≤ 2 ^ 64) (hal : bp &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, bp.toNat - 264 ≤ a.toNat → a.toNat < bp.toNat + 8 → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) (hx2z : V (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F V 11#64) (hm6 : rdq(V, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(V, 8014536#64) = h) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hsm : rdq(V, 8029424#64) = 0#64) (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i))
    (hp0 : p ≠ 0#64) (hpd : p.toNat ≤ 7940480 ∨ R.toNat ≤ p.toNat)
    (hND : N.toNat + 8 ≤ 7940480 ∨ bp.toNat + 8 ≤ N.toNat) (hN64 : N.toNat + 8 ≤ 2 ^ 64)
    (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i)) (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ bp.toNat - 40 ∨ bp.toNat + 8 ≤ Q.toNat) :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at →
      X.cpu.gpr.rsp = bp + 8#64 → X.cpu.gpr.rdi = p → X.cpu.gpr.rsi = 0#64 → X.cpu.gpr.rdx = N →
      X.cpu.gpr.rcx = Q → At0 prof L o gev gP gE F Wl s₀ V X.cpu.gpr bp R Q N cnt E H s →
      GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip hsp hdi hsi hdx hcx k
  have eF := fbb (bp := bp) (by omega) (by omega)
  have hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64 := by omega
  have e440 := f440 (bp := bp) (by omega) (by omega)
  have e432 := f432 (bp := bp) (by omega) (by omega)
  have e560 := f560 (bp := bp) (by omega) (by omega)
  have e8 := bp8 hbh
  have ehw : (8014536#64 : Addr).toNat = 8014536 := rfl
  have esm : (8029424#64 : Addr).toNat = 8029424 := rfl
  have een : (Tgv.ent 11#64 + 32#64).toNat = 7936232 := by rw [eent]; rfl
  have een40 : (Tgv.ent 11#64 + 40#64).toNat = 7936240 := by rw [eent]; rfl
  have hFW : ∀ a : Addr, bp.toNat - 264 ≤ a.toNat → a.toNat < bp.toNat + 8 → Foot Wl a :=
    fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, bp.toNat - 264 ≤ a.toNat → a.toNat < bp.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hFs a h1 h2).2
  have hh : h = 2#64 ∨ h = 6#64 := hn.imp (fun h => h.1) (fun h => h.1)
  -- 0: the prologue
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by rw [hsp, n184]; exact rng hFW (by fomega) (by fomega) (by fomega)) (by rw [hsp]; omega)) ?_
  rintro j' g' fl V' ⟨rfl, hsp', hbp', hr15', hdi', hsi', hdx', rfl⟩ Y₀ t₁ hK₀ hA₀ hr₀ hg₀ -
  rw [hV0_bp V X.cpu.gpr hsp, hdi, hsi, hdx, hcx] at hA₀
  have s₀ : Y₀.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₀, hsp', hsp]; exact n7 bp
  have b₀ : Y₀.cpu.gpr.rbp = bp := by rw [hg₀, hbp', hsp]; exact n1 bp
  have r15₀ : Y₀.cpu.gpr.r15 = p := by rw [hg₀, hr15', hdi]
  have di₀ : Y₀.cpu.gpr.rdi = 11#64 := by rw [hg₀, hdi']
  have si₀ : Y₀.cpu.gpr.rsi = bp + 18446744073709551560#64 := by rw [hg₀, hsi', hsp, n1]
  -- 61: `__tunable_get_val (11, rbp - 0x38, NULL)`
  refine c.s_call hK₀ hA₀ hin (lt_len (by omega)) hr₀ (call_61 _) hint (Tgv.lt_len (by decide)) tgt_61
    (fun i hi => by rw [s₀, n8]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
  rintro Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [s₀, n8] at hA₁ hg₁
  have s₁ : Y₁.cpu.gpr.rsp = bp + 18446744073709551432#64 := by rw [hg₁]; rfl
  have si₁ : Y₁.cpu.gpr.rsi = bp + 18446744073709551560#64 := by rw [hg₁, set4_rsi]; exact si₀
  have di₁ : Y₁.cpu.gpr.rdi = 11#64 := by rw [hg₁, set4_rdi]; exact di₀
  refine Tgv.tgv64_ok (d := 11#64) c hint hK₁ hA₁ hr₁ (by rw [di₁]; decide) hU.ty hU.va hU.ini
    (hU.out (lo := (bp + 18446744073709551432#64).toNat) (hi := bp.toNat + 8)
      (by rw [eent]; simp only [BitVec.reduceToNat]; omega) (by omega) (fun a ha => by vout)).tw
    (hU.out (lo := (bp + 18446744073709551432#64).toNat) (hi := bp.toNat + 8)
      (by rw [eent]; simp only [BitVec.reduceToNat]; omega) (by omega) (fun a ha => by vout)).z
    (fun i hi => by rw [si₁]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi)
    (by rw [si₁]; fomega) (by rw [si₁, een40]; fomega)
    (fun i hi => by rw [s₁]; exact rng hFD (by fomega) (by fomega) (by fomega) i hi)
    hin (j₂ := 66) (lt_len (by omega)) (by rw [s₁]; vself) (by rw [s₁]; fomega) (by rw [s₁, si₁]; fomega) ?_
  intro g₂ Z t₃ hK₂ hA₂ hr₂ hg₂ hbk
  rw [si₁] at hA₂
  obtain ⟨k1, -, k3, -, -, -, k7⟩ := hbk
  have sZ : Z.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₂, k1, s₁]; exact n9 bp
  have bZ : Z.cpu.gpr.rbp = bp := by rw [hg₂, k3, hg₁, set4_rbp]; exact b₀
  have r15Z : Z.cpu.gpr.r15 = p := by rw [hg₂, k7, hg₁, set4_r15]; exact r15₀
  -- 66: the mask (6) and `_dl_hwcap`, to the loop
  refine (c_66 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
    (vc_66 (h := h) hh (by rw [bZ]; vself; vpeel; exact hm6) (by vpeel; exact hhw) (by rw [r15Z]; exact hp0)
      (by rw [bZ]; exact rng hFD (by fomega) (by fomega) (by fomega)) hfh
      (by rw [bZ]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [bZ]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  rw [bZ] at hA₃
  have b₃ : Y₃.cpu.gpr.rbp = bp := by rw [hg₃]; exact bZ
  have s₃ : Y₃.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₃]; exact sZ
  have rcx₃ : Y₃.cpu.gpr.rcx = 0#64 := by rw [hg₃]; try rfl
  have rdx₃ : Y₃.cpu.gpr.rdx = 1#64 := by rw [hg₃]; try rfl
  have rsi₃ : Y₃.cpu.gpr.rsi = 1#64 := by rw [hg₃]; try rfl
  have r8₃ : Y₃.cpu.gpr.r8 = h := by rw [hg₃]; try rfl
  rcases hn with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- `h = 2`: 112 with bit 0 clear
    have e376 := f376 (bp := bp) (by omega) (by omega)
    refine (c_112 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ vc_112 ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₄ t₅ hK₄ hA₄ hr₄ hg₄ -
    rw [if_neg (show ¬ (Y₃.cpu.gpr.r8.getLsbD (Y₃.cpu.gpr.rcx.toNat % 64) = true) by
      rw [r8₃, rcx₃]; decide)] at hg₄
    have b₄ : Y₄.cpu.gpr.rbp = bp := by rw [hg₄]; exact b₃
    have s₄ : Y₄.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₄]; exact s₃
    have rcx₄ : Y₄.cpu.gpr.rcx = 0#64 := by rw [hg₄]; exact rcx₃
    have rdx₄ : Y₄.cpu.gpr.rdx = 1#64 := by rw [hg₄]; exact rdx₃
    have rsi₄ : Y₄.cpu.gpr.rsi = 1#64 := by rw [hg₄]; exact rsi₃
    have r8₄ : Y₄.cpu.gpr.r8 = 2#64 := by rw [hg₄]; exact r8₃
    -- 132: bit 1 above
    refine (c_132 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
      (vc_132n (c := 0) (by decide) (by rw [rcx₄]; try rfl) rsi₄ (by rw [r8₄]; decide)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₅ t₆ hK₅ hA₅ hr₅ hg₅ -
    have b₅ : Y₅.cpu.gpr.rbp = bp := by rw [hg₅]; exact b₄
    have s₅ : Y₅.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₅]; exact s₄
    have rcx₅ : Y₅.cpu.gpr.rcx = BitVec.ofNat 64 (0 + 1) := by rw [hg₅]; try rfl
    have rdx₅ : Y₅.cpu.gpr.rdx = 1#64 := by rw [hg₅]; exact rdx₄
    have rsi₅ : Y₅.cpu.gpr.rsi = 1#64 := by rw [hg₅]; exact rsi₄
    have r8₅ : Y₅.cpu.gpr.r8 = 2#64 := by rw [hg₅]; exact r8₄
    -- 112: bit 1 set
    refine (c_112 prof fb).run c hfs hin _ hK₅ hA₅ hr₅ vc_112 ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₇ hK₆ hA₆ hr₆ hg₆ -
    rw [if_pos (show Y₅.cpu.gpr.r8.getLsbD (Y₅.cpu.gpr.rcx.toNat % 64) = true by
      rw [r8₅, rcx₅]; decide)] at hg₆
    have b₆ : Y₆.cpu.gpr.rbp = bp := by rw [hg₆]; exact b₅
    have s₆ : Y₆.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₆]; exact s₅
    have rcx₆ : Y₆.cpu.gpr.rcx = BitVec.ofNat 64 1 := by rw [hg₆]; exact rcx₅
    have rsi₆ : Y₆.cpu.gpr.rsi = 1#64 := by rw [hg₆]; exact rsi₅
    have r8₆ : Y₆.cpu.gpr.r8 = 2#64 := by rw [hg₆]; exact r8₅
    have r12₆ : Y₆.cpu.gpr.r12 = BitVec.ofNat 64 3 := by
      rw [hg₆]
      show Y₅.cpu.gpr.rdx + 2#64 = _
      rw [rdx₅]
      try decide
    -- 132: bit 1 the last; the `alloca` of 64 bytes
    refine (c_132 prof fb).run c hfs hin _ hK₆ hA₆ hr₆
      (vc_132 (c := 1) (n := 3) (by decide) rcx₆ rsi₆ r12₆ (.inl rfl) (by vpeel; exact hsm) hfm) ?_
    rintro j' g fl V' ⟨rfl, ⟨-, -, hnz⟩ | ⟨rfl, -, rfl⟩⟩ Y₇ t₈ hK₇ hA₇ hr₇ hg₇ -
    · exact (hnz (by rw [r8₆]; try decide)).elim
    have b₇ : Y₇.cpu.gpr.rbp = bp := by rw [hg₇]; exact b₆
    have r8₇ : Y₇.cpu.gpr.r8 = 2#64 := by rw [hg₇]; exact r8₆
    have r12₇ : Y₇.cpu.gpr.r12 = BitVec.ofNat 64 3 := by rw [hg₇]; exact r12₆
    have ax₇ : Y₇.cpu.gpr.rax = BitVec.ofNat 64 (16 * 3 + 16) := by rw [hg₇]; try rfl
    have s₇ : Y₇.cpu.gpr.rsp = bp + 18446744073709551376#64 := by
      rw [hg₇]
      show Y₆.cpu.gpr.rsp - BitVec.ofNat 64 (16 * 3 + 16) = _
      rw [s₆]
      exact nR3 bp
    -- 1772: the probe of the slot of the return address of 61
    have ea : eaI Y₇ 4 0 18446744073709551608 = bp + 18446744073709551432#64 := by
      show Y₇.cpu.gpr.rsp + Y₇.cpu.gpr.rax + BitVec.ofNat 64 18446744073709551608 = _
      rw [s₇, ax₇]
      exact np3 bp
    refine c.s_or_mi64i hK₇ hA₇ hin (lt_len (by omega)) hr₇ (or_1772 _)
      (fun i hi => by rw [ea]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
    rintro Y₈ t₉ hK₈ hA₈ ⟨hr₈, hg₈⟩
    rw [Gor.probe_same] at hA₈
    refine from1778_3 c hfs hin hinc hc0 hcpy hinm hm0 hmal hins hs0 hlen (V := _)
      (R := bp + 18446744073709551376#64) (bp := bp) (Q := Q) (N := N) (p := p)
      (fun W hW => hPm W fun a ha hn => (hW a ha hn).trans (by vout))
      (fun W hW => hPa W fun a ha hn => (hW a ha hn).trans (by vout))
      (fun W hW => hPl W fun a ha => (hW a ha).trans (by vout))
      (by omega) (by omega) hfb (al3 hal) (fun a h1 h2 => hFs a (by omega) (by omega)) hpg
      (fun q hq => by
        have := lit_add (c := 7288953) (n := 6) (k := q) (by omega) (by decide)
        vout
        exact hx1 q hq)
      (by
        have := lit_add (c := 7288953) (n := 6) (k := 6) (by omega) (by decide)
        vout
        exact hx1z)
      htls (by vpeel; vself) hp0 (by vpeel; vself) hpd (by vpeel; vself) (by omega) hN64 hsN (by vpeel; vself)
      hsQ hQ64 (by omega) ?_ Y₈ t₉ hK₈ hA₈ hr₈ (by rw [hg₈]; exact r8₇) (by rw [hg₈]; exact r12₇)
      (by rw [hg₈]; exact b₇) (by rw [hg₈]; exact s₇)
    intro Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 hSs hNE
    exact k Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY (hbxY.trans (by vpeel; vself))
      (h12Y.trans (by vpeel; vself)) (h13Y.trans (by vpeel; vself)) (h14Y.trans (by vpeel; vself))
      (h15Y.trans (by vpeel; vself)) (hbpY.trans (by vpeel; vself)) hTab (SameO.trans (fun a _ h2 => by vout) hS0)
      (SameO.trans (fun a h1 h2 => by vout) (hSs.mono (by omega) (Nat.le_refl _))) hNE
  · -- `h = 6`: 112 with bit 0 clear
    have e360 := f360 (bp := bp) (by omega) (by omega)
    refine (c_112 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ vc_112 ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₄ t₅ hK₄ hA₄ hr₄ hg₄ -
    rw [if_neg (show ¬ (Y₃.cpu.gpr.r8.getLsbD (Y₃.cpu.gpr.rcx.toNat % 64) = true) by
      rw [r8₃, rcx₃]; decide)] at hg₄
    have b₄ : Y₄.cpu.gpr.rbp = bp := by rw [hg₄]; exact b₃
    have s₄ : Y₄.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₄]; exact s₃
    have rcx₄ : Y₄.cpu.gpr.rcx = 0#64 := by rw [hg₄]; exact rcx₃
    have rdx₄ : Y₄.cpu.gpr.rdx = 1#64 := by rw [hg₄]; exact rdx₃
    have rsi₄ : Y₄.cpu.gpr.rsi = 1#64 := by rw [hg₄]; exact rsi₃
    have r8₄ : Y₄.cpu.gpr.r8 = 6#64 := by rw [hg₄]; exact r8₃
    -- 132: bits 1, 2 above
    refine (c_132 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
      (vc_132n (c := 0) (by decide) (by rw [rcx₄]; try rfl) rsi₄ (by rw [r8₄]; decide)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₅ t₆ hK₅ hA₅ hr₅ hg₅ -
    have b₅ : Y₅.cpu.gpr.rbp = bp := by rw [hg₅]; exact b₄
    have s₅ : Y₅.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₅]; exact s₄
    have rcx₅ : Y₅.cpu.gpr.rcx = BitVec.ofNat 64 (0 + 1) := by rw [hg₅]; try rfl
    have rdx₅ : Y₅.cpu.gpr.rdx = 1#64 := by rw [hg₅]; exact rdx₄
    have rsi₅ : Y₅.cpu.gpr.rsi = 1#64 := by rw [hg₅]; exact rsi₄
    have r8₅ : Y₅.cpu.gpr.r8 = 6#64 := by rw [hg₅]; exact r8₄
    -- 112: bit 1 set
    refine (c_112 prof fb).run c hfs hin _ hK₅ hA₅ hr₅ vc_112 ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₆ t₇ hK₆ hA₆ hr₆ hg₆ -
    rw [if_pos (show Y₅.cpu.gpr.r8.getLsbD (Y₅.cpu.gpr.rcx.toNat % 64) = true by
      rw [r8₅, rcx₅]; decide)] at hg₆
    have b₆ : Y₆.cpu.gpr.rbp = bp := by rw [hg₆]; exact b₅
    have s₆ : Y₆.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₆]; exact s₅
    have rcx₆ : Y₆.cpu.gpr.rcx = BitVec.ofNat 64 1 := by rw [hg₆]; exact rcx₅
    have rsi₆ : Y₆.cpu.gpr.rsi = 1#64 := by rw [hg₆]; exact rsi₅
    have r8₆ : Y₆.cpu.gpr.r8 = 6#64 := by rw [hg₆]; exact r8₅
    have rdx₆ : Y₆.cpu.gpr.rdx = 2#64 := by
      rw [hg₆]
      show Y₅.cpu.gpr.rdx + 1#64 = _
      rw [rdx₅]
      try decide
    -- 132: bit 2 above
    refine (c_132 prof fb).run c hfs hin _ hK₆ hA₆ hr₆
      (vc_132n (c := 1) (by decide) rcx₆ rsi₆ (by rw [r8₆]; decide)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₇ t₈ hK₇ hA₇ hr₇ hg₇ -
    have b₇ : Y₇.cpu.gpr.rbp = bp := by rw [hg₇]; exact b₆
    have s₇ : Y₇.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₇]; exact s₆
    have rcx₇ : Y₇.cpu.gpr.rcx = BitVec.ofNat 64 (1 + 1) := by rw [hg₇]; try rfl
    have rdx₇ : Y₇.cpu.gpr.rdx = 2#64 := by rw [hg₇]; exact rdx₆
    have rsi₇ : Y₇.cpu.gpr.rsi = 1#64 := by rw [hg₇]; exact rsi₆
    have r8₇ : Y₇.cpu.gpr.r8 = 6#64 := by rw [hg₇]; exact r8₆
    -- 112: bit 2 set
    refine (c_112 prof fb).run c hfs hin _ hK₇ hA₇ hr₇ vc_112 ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₈ t₉ hK₈ hA₈ hr₈ hg₈ -
    rw [if_pos (show Y₇.cpu.gpr.r8.getLsbD (Y₇.cpu.gpr.rcx.toNat % 64) = true by
      rw [r8₇, rcx₇]; decide)] at hg₈
    have b₈ : Y₈.cpu.gpr.rbp = bp := by rw [hg₈]; exact b₇
    have s₈ : Y₈.cpu.gpr.rsp = bp + 18446744073709551440#64 := by rw [hg₈]; exact s₇
    have rcx₈ : Y₈.cpu.gpr.rcx = BitVec.ofNat 64 2 := by rw [hg₈]; exact rcx₇
    have rsi₈ : Y₈.cpu.gpr.rsi = 1#64 := by rw [hg₈]; exact rsi₇
    have r8₈ : Y₈.cpu.gpr.r8 = 6#64 := by rw [hg₈]; exact r8₇
    have r12₈ : Y₈.cpu.gpr.r12 = BitVec.ofNat 64 4 := by
      rw [hg₈]
      show Y₇.cpu.gpr.rdx + 2#64 = _
      rw [rdx₇]
      try decide
    -- 132: bit 2 the last; the `alloca` of 80 bytes
    refine (c_132 prof fb).run c hfs hin _ hK₈ hA₈ hr₈
      (vc_132 (c := 2) (n := 4) (by decide) rcx₈ rsi₈ r12₈ (.inr rfl) (by vpeel; exact hsm) hfm) ?_
    rintro j' g fl V' ⟨rfl, ⟨-, -, hnz⟩ | ⟨rfl, -, rfl⟩⟩ Y₉ t₁₀ hK₉ hA₉ hr₉ hg₉ -
    · exact (hnz (by rw [r8₈]; try decide)).elim
    have b₉ : Y₉.cpu.gpr.rbp = bp := by rw [hg₉]; exact b₈
    have r8₉ : Y₉.cpu.gpr.r8 = 6#64 := by rw [hg₉]; exact r8₈
    have r12₉ : Y₉.cpu.gpr.r12 = BitVec.ofNat 64 4 := by rw [hg₉]; exact r12₈
    have ax₉ : Y₉.cpu.gpr.rax = BitVec.ofNat 64 (16 * 4 + 16) := by rw [hg₉]; try rfl
    have s₉ : Y₉.cpu.gpr.rsp = bp + 18446744073709551360#64 := by
      rw [hg₉]
      show Y₈.cpu.gpr.rsp - BitVec.ofNat 64 (16 * 4 + 16) = _
      rw [s₈]
      exact nR4 bp
    -- 1772: the probe of the slot of the return address of 61
    have ea : eaI Y₉ 4 0 18446744073709551608 = bp + 18446744073709551432#64 := by
      show Y₉.cpu.gpr.rsp + Y₉.cpu.gpr.rax + BitVec.ofNat 64 18446744073709551608 = _
      rw [s₉, ax₉]
      exact np4 bp
    refine c.s_or_mi64i hK₉ hA₉ hin (lt_len (by omega)) hr₉ (or_1772 _)
      (fun i hi => by rw [ea]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
    rintro Y₁₀ t₁₁ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀⟩
    rw [Gor.probe_same] at hA₁₀
    refine from1778_4 c hfs hin hinc hc0 hcpy hinm hm0 hmal hins hs0 hlen (V := _)
      (R := bp + 18446744073709551360#64) (bp := bp) (Q := Q) (N := N) (p := p)
      (fun W hW => hPm W fun a ha hn => (hW a ha hn).trans (by vout))
      (fun W hW => hPa W fun a ha hn => (hW a ha hn).trans (by vout))
      (fun W hW => hPl W fun a ha => (hW a ha).trans (by vout))
      (by omega) (by omega) hfb (al4 hal) (fun a h1 h2 => hFs a (by omega) (by omega)) hpg
      (fun q hq => by
        have := lit_add (c := 7288953) (n := 6) (k := q) (by omega) (by decide)
        vout
        exact hx1 q hq)
      (by
        have := lit_add (c := 7288953) (n := 6) (k := 6) (by omega) (by decide)
        vout
        exact hx1z)
      (fun q hq => by
        have := lit_add (c := 7288962) (n := 8) (k := q) (by omega) (by decide)
        vout
        exact hx2 q hq)
      (by
        have := lit_add (c := 7288962) (n := 8) (k := 8) (by omega) (by decide)
        vout
        exact hx2z)
      htls (by vpeel; vself) hp0 (by vpeel; vself) hpd (by vpeel; vself) (by omega) hN64 hsN (by vpeel; vself)
      hsQ hQ64 (by omega) ?_ Y₁₀ t₁₁ hK₁₀ hA₁₀ hr₁₀ (by rw [hg₁₀]; exact r8₉) (by rw [hg₁₀]; exact r12₉)
      (by rw [hg₁₀]; exact b₉) (by rw [hg₁₀]; exact s₉)
    intro Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 hSs hNE
    exact k Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY (hbxY.trans (by vpeel; vself))
      (h12Y.trans (by vpeel; vself)) (h13Y.trans (by vpeel; vself)) (h14Y.trans (by vpeel; vself))
      (h15Y.trans (by vpeel; vself)) (hbpY.trans (by vpeel; vself)) hTab (SameO.trans (fun a _ h2 => by vout) hS0)
      (SameO.trans (fun a h1 h2 => by vout) (hSs.mono (by omega) (Nat.le_refl _))) hNE

end FV7z.Hwc
