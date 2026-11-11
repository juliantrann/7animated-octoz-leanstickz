import FV7z.Smm.PartB
/-!
# `sysmalloc`: from the second `MORECORE` to the return (PLAN.md G3, `malloc`)

- `ret_398`: the `ret`.
- `rd_Vc`, `rd_Vd`: reads outside what was stored after the second `MORECORE`.
- `Ve`: the bytes at the return.
- `sm_c`: the run from offset 1690, the break before the second `MORECORE` in `rax`, to the return address: the top
  is the aligned break `ab` of the frame, the chunk its first `nb` bytes, `rax` the chunk's memory `ab + 16`, and
  the registers a call keeps are those the frame held.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Smm

/-! ## The instruction outside the blocks -/

theorem w_398 : Sbrk.pret <+: smm.drop 398 := by decide +kernel
theorem ret_398 (feat : Features) : Dec feat smm 398 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 398) (k := 0) (Sbrk.pret_0 feat) w_398 (Nat.zero_le _)

/-! ## The bytes -/

/-- A read that is not of `av->top`, the top's size word, `av->system_mem` or `av->max_system_mem`, in the bytes
at 312. -/
theorem rd_Vc {g : Gprs} {V : Addr → Byte} {sm ab : BitVec 64} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hab : ab.toNat + 16 ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat) (h2 : x.toNat + n ≤ ab.toNat + 8 ∨ ab.toNat + 16 ≤ x.toNat)
    (h3 : x.toNat + n ≤ 7942856 ∨ 7942872 ≤ x.toNat) :
    List.map (Vc g V sm ab) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  show List.map (Vst (Vst (Vst (Vst V _ _) _ _) _ _) _ _) _ = _
  rw [rd_Vst _ _ _ _ _ (by sd) hx (h3.elim (fun h => .inr (by sd)) fun h => .inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (h3.elim (fun h => .inr (by sd)) fun h => .inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (h2.elim (fun h => .inr (by sd)) fun h => .inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (h1.elim (fun h => .inr (by sd)) fun h => .inl (by sd))]

/-- A read above the chunk and the rest's size word, in the bytes at the `ret`. -/
theorem rd_Vd {g : Gprs} {V : Addr → Byte} {szw : BitVec 64} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h0 : 7940776 ≤ g.r8.toNat) (h1 : g.r8.toNat + g.rbp.toNat + 16 ≤ x.toNat) :
    List.map (Vd g V szw) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  show List.map (Vst (Vst (Vst V _ _) _ _) _ _) _ = _
  rw [rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd)),
    rd_Vst _ _ _ _ _ (by sd) hx (.inl (by sd))]

/-- The registers at 312. -/
abbrev gc (g : Gprs) (sm ab : BitVec 64) : Gprs :=
  { g with rax := g.rax - ab + g.r14 ||| 1#64, rcx := sm + g.r14, rdx := 0#64, r8 := ab }

/-- The bytes at the return, from those at 1690: the top `ab + nb` with its size, the chunk `ab` of size `nb`,
`av->system_mem` and `av->max_system_mem`. -/
abbrev Ve (g : Gprs) (V : Addr → Byte) (sm ab : BitVec 64) : Addr → Byte :=
  Vd (gc g sm ab) (Vc g V sm ab) (g.rax - ab + g.r14 ||| 1#64)

theorem a104 (S : Addr) : S + 56#64 + 8 + 8 + 8 + 8 + 8 + 8 = S + 104#64 := by bv_omega

/-! ## The run -/

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From offset 1690 with the break before the second `MORECORE` in `rax` (not 0), no `__after_morecore_hook`,
`av` the main arena, the old size 0, the aligned break `ab` in the frame, the new top not smaller than
`nb + MINSIZE`: the run reaches the return address with `rax` the chunk's memory `ab + 16`, the frame given back
and the registers a call keeps those the frame held (`v0` … `v5`); the bytes are `Ve`. -/
theorem sm_c {sm ab mx v0 v1 v2 v3 v4 v5 : BitVec 64} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L smm_at smm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at.add 1690)
    (hsp : 8029888 ≤ X.cpu.gpr.rsp.toNat) (hsp2 : X.cpu.gpr.rsp.toNat + 112 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hrt : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 104#64) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hh : ∀ a : Addr, ab.toNat ≤ a.toNat → a.toNat < ab.toNat + X.cpu.gpr.rbp.toNat + 16 → Foot Wl a)
    (hh1 : ab.toNat + X.cpu.gpr.rbp.toNat + 16 ≤ X.cpu.gpr.rsp.toNat) (hab : 8029888 ≤ ab.toNat)
    (hs0 : X.cpu.gpr.rax ≠ 0#64) (h12 : X.cpu.gpr.r12 = 0#64) (hbx : X.cpu.gpr.rbx = 7940672#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (r1 : rdq(V, X.cpu.gpr.rsp + 8#64) = ab)
    (hmx : rdq(V, 7942864#64) = mx) (hlt : mx.toNat < (sm + X.cpu.gpr.r14).toNat)
    (hle : X.cpu.gpr.r15.toNat ≤
      ((X.cpu.gpr.rax - ab + X.cpu.gpr.r14 ||| 1#64) &&& 18446744073709551608#64).toNat)
    (p0 : rdq(V, X.cpu.gpr.rsp + 56#64) = v0) (p1 : rdq(V, X.cpu.gpr.rsp + 56#64 + 8) = v1)
    (p2 : rdq(V, X.cpu.gpr.rsp + 56#64 + 8 + 8) = v2) (p3 : rdq(V, X.cpu.gpr.rsp + 56#64 + 8 + 8 + 8) = v3)
    (p4 : rdq(V, X.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8) = v4)
    (p5 : rdq(V, X.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8 + 8) = v5)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 104#64) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Ve X.cpu.gpr V sm ab) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = ab + 16#64 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 112#64 ∧ Z.cpu.gpr.rbx = v0 ∧ Z.cpu.gpr.rbp = v1 ∧ Z.cpu.gpr.r12 = v2 ∧
        Z.cpu.gpr.r13 = v3 ∧ Z.cpu.gpr.r14 = v4 ∧ Z.cpu.gpr.r15 = v5) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- the top
  refine (c_1690 prof).run c hin _ hK hA hrip
    (vc_1690 (sm := sm) (ab := ab) (mx := mx) hsp (by omega) hst c.hws hW hhk
      (fun i hi => hh _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
      hs0 h12 hbx hk hsm r1 hab (by omega) hmx hlt) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hszw : rdq(Vc X.cpu.gpr V sm ab, ab + 8#64) = X.cpu.gpr.rax - ab + X.cpu.gpr.r14 ||| 1#64 := by
    show ofBytesLE 64 (List.map (Vst (Vst (Vst (Vst V _ _) _ _) _ _) _ _) _) = _
    rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd)), rd_Vst _ _ _ _ _ (by sd) (by sd) (.inl (by sd)),
      rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  have q : ∀ x : Addr, X.cpu.gpr.rsp.toNat + 56 ≤ x.toNat → x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat + 112 →
      List.map (Vc X.cpu.gpr V sm ab) (byteAddrs x 8) = List.map V (byteAddrs x 8) := fun x h1 h2 =>
    rd_Vc (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))
  -- the chunk
  refine (c_312 prof).run c hin _ hK₁ hA₁ hr₁
    (vc_312 (szw := X.cpu.gpr.rax - ab + X.cpu.gpr.r14 ||| 1#64) (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3)
      (v4 := v4) (v5 := v5) (by rw [hg₁]; exact hsp) (by rw [hg₁]; show X.cpu.gpr.rsp.toNat + 104 ≤ _; omega)
      (by rw [hg₁]; exact hst) c.hws hW (by rw [hg₁]; exact hh) (by rw [hg₁]; exact hh1) (by rw [hg₁]; exact hab)
      (by rw [hg₁]; exact hbx) (by rw [hg₁]; exact hszw) (by rw [hg₁]; exact hle)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p0)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p1)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p2)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p3)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p4)
      (by rw [hg₁]; exact (congrArg (ofBytesLE 64) (q _ (by bv_omega) (by bv_omega))).trans p5)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  rw [hg₁] at hA₂
  have e₂' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp + 104#64 := by
    rw [hg₂, hg₁]
    exact a104 _
  -- the `ret`
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_398 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [e₂']
    exact hrt i hi
  · rw [e₂', rd_Vd (g := gc X.cpu.gpr sm ab) (by bv_omega) (by show 7940776 ≤ ab.toNat; omega)
      (by show ab.toNat + X.cpu.gpr.rbp.toNat + 16 ≤ _; bv_omega), q _ (by bv_omega) (by bv_omega)]
    exact hra
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg', hg₂, hg₁]; rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg', e₂']
    show X.cpu.gpr.rsp + 104#64 + 8 = _
    bv_omega
  all_goals
    rw [hg', hg₂]
    rfl

end FV7z.Smm
