import FV7z.Dde.Holds
import FV7z.Raf.Holds
/-!
# `DoesDirExist` from its entry to its return address (PLAN.md §M, M1)

`dde_call` and `dde_ret` joined through a contract for `MY_lstat` (`kf`): called with the registers `aG` and the
return address `dde_at + 42` at `rsp`, it returns there with `rsp` 8 above, `rbx`, `rbp`, `r12` … `r15` kept (`K6`),
some events after `gev`, and bytes that differ from those at its entry only in the `struct stat`'s 144 bytes and in
one more range `[elo, ehi)` (`errno`). The stack guard's check is not assumed: the guard read at the entry (`fs:0x28`)
is stored at `aQ S + 152`, which `MY_lstat` does not write, and `fs:0x28` itself is not written, so the second read
at 69 gives the same 8 bytes.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dde

theorem tq (S : Addr) (h : 176 ≤ S.toNat) :
    (aQ S).toNat = S.toNat - 168 ∧ (aQ S - 8).toNat = S.toNat - 176 ∧ (aQ S + 152#64).toNat = S.toNat - 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [aQ] <;> bv_omega

theorem e168 (S : Addr) : aQ S + 168#64 = S := by simp only [aQ]; bv_omega
theorem e176 (S : Addr) : aQ S + 176#64 = S + 8 := by simp only [aQ]; bv_omega
theorem e8 (S : Addr) : aQ S - 8 + 8 = aQ S := BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `DoesDirExist (name, followLink)` from its entry (`S` = `rsp`, at least 176) to its return address (at `S`):
the stack guard's 8 bytes at `fs:0x28` readable and apart from the frame `[S - 176, S - 8)` and from `[elo, ehi)`,
the guard's slot and the return address's slot apart from `[elo, ehi)`; `MY_lstat` by its contract `kf`. At the
return address with `rsp` = `S + 8`, `al` = `dres` of the bytes after `MY_lstat` and its answer `r`, the registers
`K6` as at the entry. -/
theorem dde_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dde_at dde)
    (hinM : CodeIn L Mls.mls_at Mls.mls) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = dde_at) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64) (hS : 176 ≤ X.cpu.gpr.rsp.toNat)
    (hSb : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 152#64) i))
    (wr : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (f24 : ∀ i < 4, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 24#64) i))
    (f152 : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 152#64) i))
    (f168 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 176 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ (fb + 40#64).toNat)
    {elo ehi : Nat} (hce : (fb + 40#64).toNat + 8 ≤ elo ∨ ehi ≤ (fb + 40#64).toNat)
    (hge : X.cpu.gpr.rsp.toNat - 8 ≤ elo ∨ ehi ≤ X.cpu.gpr.rsp.toNat - 16)
    (hse : X.cpu.gpr.rsp.toNat + 8 ≤ elo ∨ ehi ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kf : ∀ (Y : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = Mls.mls_at → Y.cpu.gpr = (aG X.cpu.gpr).set 4 (aQ X.cpu.gpr.rsp - 8) →
      (∀ (ev : List Event) (Z : State) (t'' : Nat) (W' : Addr → Byte), KeptW Wl s₀ Z →
        Agree F Z.proc.mm.mem W' →
        (∀ a : Addr, ¬ ((aQ X.cpu.gpr.rsp).toNat ≤ a.toNat ∧ a.toNat < (aQ X.cpu.gpr.rsp).toNat + 144) →
          ¬ (elo ≤ a.toNat ∧ a.toNat < ehi) → W' a = W a) →
        Z.cpu.rip = rdq(W, Y.cpu.gpr.rsp) → Z.cpu.gpr.rsp = Y.cpu.gpr.rsp + 8 → K6 Y.cpu.gpr Z.cpu.gpr →
        GoG prof L o (gev ++ ev) gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k : ∀ (ev : List Event) (Z : State) (t' : Nat) (W' : Addr → Byte) (r : BitVec 64), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W' → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z.cpu.gpr.rax.setWidth 8 = dres W' { X.cpu.gpr with rax := r, rsp := aQ X.cpu.gpr.rsp } →
      K6 X.cpu.gpr Z.cpu.gpr → GoG prof L o (gev ++ ev) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  obtain ⟨q0, q8, q152⟩ := tq X.cpu.gpr.rsp hS
  refine dde_call c hfs hin hinM hK hA hrip hcl wc wr ?_
  intro Y t₁ hKY hAY hrY hgY
  refine kf Y t₁ _ hKY hAY hrY hgY ?_
  intro ev Z t₂ W' hKZ hAZ hfr hrZ hsZ hkZ
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp - 8 := by rw [hgY]; try rfl
  have hs1 : Z.cpu.gpr.rsp = aQ X.cpu.gpr.rsp := by rw [hsZ, hsY]; exact e8 _
  -- reads apart from `MY_lstat`'s stores
  have rdW : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ (aQ X.cpu.gpr.rsp).toNat ∨ (aQ X.cpu.gpr.rsp).toNat + 144 ≤ x.toNat) →
      (x.toNat + 8 ≤ elo ∨ ehi ≤ x.toNat) →
      rdq(W', x) = rdq(Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (dde_at.add 42) 8), x) := fun x hx h1 h2 =>
    congrArg (ofBytesLE 64) (Raf.rd_out2 hfr hx h1 h2)
  -- reads apart from the return address's slot and the guard's slot
  have rd0 : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 176 ∨ X.cpu.gpr.rsp.toNat - 168 ≤ x.toNat) →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ x.toNat) →
      rdq(Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8) (toBytesLE (dde_at.add 42) 8), x) =
        rdq(V, x) := fun x hx h1 h2 =>
    congrArg (ofBytesLE 64)
      ((Tun.rd_Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8) (toBytesLE (dde_at.add 42) 8)
        x 8 (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)).trans
      (Tun.rd_Vst V (aQ X.cpu.gpr.rsp + 152#64) (toBytesLE rdq(V, fb + 40#64) 8) x 8
        (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)))
  have hra42 : rdq(Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (dde_at.add 42) 8), aQ X.cpu.gpr.rsp - 8) = dde_at.add 42 := by
    rw [Tun.rd_Vst_self (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (dde_at.add 42) 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  -- the stack guard: the stored copy and `fs:0x28` both as at the entry
  have hcan : rdq(W', Z.cpu.gpr.rsp + 152#64) = rdq(W', fb + 40#64) := by
    rw [hs1, rdW (aQ X.cpu.gpr.rsp + 152#64) (by omega) (by omega) (by omega), rdW (fb + 40#64) hcb (by omega) hce,
      rd0 (fb + 40#64) hcb (by omega) (by omega),
      congrArg (ofBytesLE 64) (Tun.rd_Vst (Vo V X.cpu.gpr.rsp rdq(V, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (dde_at.add 42) 8) (aQ X.cpu.gpr.rsp + 152#64) 8 (by rw [toBytesLE_length]; omega) (by omega)
        (by rw [toBytesLE_length]; omega))]
    dsimp only [Vo]
    rw [Tun.rd_Vst_self V (aQ X.cpu.gpr.rsp + 152#64) (toBytesLE rdq(V, fb + 40#64) 8) (toBytesLE_length _ _)
      (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hraZ : rdq(W', Z.cpu.gpr.rsp + 168#64) = e₂.add j₂ := by
    rw [hs1, e168, rdW X.cpu.gpr.rsp hSb (by omega) hse, rd0 X.cpu.gpr.rsp hSb (by omega) (by omega)]
    exact hra
  refine dde_ret c hfs hin hKZ hAZ (by rw [hrZ, hsY]; exact hra42) hcl (by rw [hs1]; exact f24)
    (by rw [hs1]; exact f152) (by rw [hs1, e168]; exact f168) hcan hin₂ h₂ hraZ ?_
  intro Z' t' hKZ' hAZ' hrZ' hsZ' haZ' hkZ'
  refine k ev Z' t' W' Z.cpu.gpr.rax hKZ' hAZ' hrZ' (by rw [hsZ', hs1, e176]) ?_ ?_
  · rw [haZ']
    unfold dres
    rw [hs1]
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hkZ'
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hkZ
    rw [hgY] at b1 b2 b3 b4 b5 b6
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6⟩

end FV7z.Dde
