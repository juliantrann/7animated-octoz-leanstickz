import FV7z.Lpb.Holds
import FV7z.Lpd.Holds
/-!
# `LzmaDec_AllocateProbs` from its entry to its return address (PLAN.md §M, M1)

`lpb_call` and `lpb_ret` joined through `Lpd.lpd_ok` (`LzmaProps_Decode`, called at 36 with `rdi` = `&propNew` =
`aQ S`, back at 41). `LzmaProps_Decode` stores only into `propNew`'s 8 bytes (`Lpd.Res`, `res_out`), so at 41 the
stack guard's copy at `aQ S + 8` and the return address at `aQ S + 40` = `S` are as `lpb_call` left them; `fs:0x28`
is apart from the frame `[S - 48, S)`, so its 8 bytes are those at the entry, and the check at 45 passes.
`LzmaDec_AllocateProbs2` stays a hypothesis (`k2`, with `kn`, `kz` for its return), stated for every answer `r`,
`rcx`, `rdx` and bytes `V'` that `LzmaProps_Decode` may give (`Lpd.Res`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lpb

theorem qq (S : Addr) (h : 48 ≤ S.toNat) :
    (aQ S).toNat = S.toNat - 40 ∧ (aQ S - 8).toNat = S.toNat - 48 ∧ (aQ S + 8#64).toNat = S.toNat - 32 ∧
      (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [aQ]) <;> bv_omega

theorem e40 (S : Addr) : aQ S + 40#64 = S := by simp only [aQ]; bv_omega
theorem e8 (S : Addr) : aQ S - 8 + 8 = aQ S := BitVec.sub_add_cancel _ _

/-- `LzmaProps_Decode`'s stores are inside `propNew`'s 8 bytes at `p`. -/
theorem res_out {V₀ V : Addr → Byte} {p : Addr} {r : BitVec 64} (h : Lpd.Res V₀ p V r)
    (hp : p.toNat + 8 ≤ 2 ^ 64) {x : Addr} (hx : x.toNat + 8 ≤ 2 ^ 64)
    (hd : x.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 ≤ x.toNat) :
    List.map V (byteAddrs x 8) = List.map V₀ (byteAddrs x 8) := by
  have t1 : (p + 1#64).toNat = p.toNat + 1 := tA p 1 (by omega)
  have t2 : (p + 2#64).toNat = p.toNat + 2 := tA p 2 (by omega)
  have t4 : (p + 4#64).toNat = p.toNat + 4 := tA p 4 (by omega)
  rcases h with ⟨-, rfl | ⟨w, rfl⟩⟩ | ⟨-, w, b0, b2, b1, rfl⟩
  · rfl
  · exact Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t4]; omega) hx (by rw [toBytesLE_length, t4]; omega)
  · exact (Tun.rd_Vst _ (p + 1#64) _ x 8 (by rw [toBytesLE_length, t1]; omega) hx
        (by rw [toBytesLE_length, t1]; omega)).trans
      ((Tun.rd_Vst _ (p + 2#64) _ x 8 (by rw [toBytesLE_length, t2]; omega) hx
        (by rw [toBytesLE_length, t2]; omega)).trans
      ((Tun.rd_Vst _ p _ x 8 (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)).trans
      (Tun.rd_Vst _ (p + 4#64) _ x 8 (by rw [toBytesLE_length, t4]; omega) hx
        (by rw [toBytesLE_length, t4]; omega))))

/-- The bytes at `LzmaProps_Decode`'s entry: the pushes, the stack guard's copy, the return address `lpb_at + 41`. -/
abbrev Wd (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst (Vo V g rdq(P2 V g, fb + 40#64)) (aQ g.rsp - 8) (toBytesLE (lpb_at.add 41) 8)

/-- The registers at 41: `aG` with `LzmaProps_Decode`'s answer `r` and its `rcx`, `rdx`. -/
abbrev g41 (g : Gprs) (r c d : BitVec 64) : Gprs := { aG g with rax := r, rcx := c, rdx := d }

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_AllocateProbs (p, props, propsSize, alloc)` from its entry (`S` = `rsp`, at least 48), `LzmaProps_Decode`
by `Lpd.lpd_ok`: the stack guard's 8 bytes at `fs:0x28` readable and apart from `[S - 48, S)`, the frame's slots in
what the run may store into, `props`' 5 bytes readable, `p`'s 8 bytes storable and apart from `[S - 32, S + 8)` and
from the guard. `LzmaProps_Decode`'s answer not 0: at the return address with the registers `tl` (`k0`); else at
`LzmaDec_AllocateProbs2`'s entry (`k2`) and from its return as in `lpb_ret` (`kn`, `kz`). -/
theorem lpb_ok {fb : Addr} {P : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lpb_at lpb) (hinD : CodeIn L Lpd.lpd_at Lpd.lpd)
    (hinA : CodeIn L Lap.lap_at Lap.lap) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lpb_at) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64) (hS : 48 ≤ X.cpu.gpr.rsp.toNat)
    (hSb : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 8#64) i))
    (wr : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (fl : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (fr1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 1#64) i))
    (fr0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw4 : ∀ i < 4, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 4#64) i))
    (fw0 : ∀ i < 1, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp) i))
    (fw2 : ∀ i < 1, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 2#64) i))
    (fw1 : ∀ i < 1, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 1#64) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp) i))
    (f1 : ∀ i < 1, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 1#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 8#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 32#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (wb : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hbb : X.cpu.gpr.rdi.toNat + 8 ≤ 2 ^ 64)
    (hbd : X.cpu.gpr.rdi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hbc : X.cpu.gpr.rdi.toNat + 8 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : ∀ (r cx d : BitVec 64) (V' : Addr → Byte), Lpd.Res (Wd V X.cpu.gpr fb) (aQ X.cpu.gpr.rsp) V' r →
      r.setWidth 32 ≠ 0#32 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = tl (g41 X.cpu.gpr r cx d) V' →
      GoG prof L o gev gP gE Z t')
    (k2 : ∀ (r cx d : BitVec 64) (V' : Addr → Byte), Lpd.Res (Wd V X.cpu.gpr fb) (aQ X.cpu.gpr.rsp) V' r →
      r.setWidth 32 = 0#32 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (aQ X.cpu.gpr.rsp - 8) (toBytesLE (lpb_at.add 92) 8)) →
      Y.cpu.rip = Lap.lap_at → Y.cpu.gpr = (g72 (g41 X.cpu.gpr r cx d) V').set 4 (aQ X.cpu.gpr.rsp - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = lpb_at.add 92 → Z₂.cpu.gpr.rsp = aQ X.cpu.gpr.rsp → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V₂, aQ X.cpu.gpr.rsp + 8#64) = rdq(V₂, fb + 40#64) → rdq(V₂, aQ X.cpu.gpr.rsp + 40#64) = e₂.add j₂ →
        P Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kn : ∀ (Z₂ : State) (V₂ : Addr → Byte), P Z₂ V₂ → Z₂.cpu.gpr.rax.setWidth 32 ≠ 0#32 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = tl Z₂.cpu.gpr V₂ → GoG prof L o gev gP gE Z t')
    (kz : ∀ (Z₂ : State) (V₂ : Addr → Byte), P Z₂ V₂ → Z₂.cpu.gpr.rax.setWidth 32 = 0#32 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V₂ X.cpu.gpr.rdi (toBytesLE rdq(V₂, aQ X.cpu.gpr.rsp) 8)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = tl { Z₂.cpu.gpr with rdx := rdq(V₂, Z₂.cpu.gpr.rsp) }
        (Vst V₂ X.cpu.gpr.rdi (toBytesLE rdq(V₂, aQ X.cpu.gpr.rsp) 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  obtain ⟨q0, q8m, q8, qs8, qs16⟩ := qq X.cpu.gpr.rsp hS
  refine lpb_call c hfs hin hinD hK hA hrip hcl w1 w2 wc wr ?_
  intro Y t₁ hKY hAY hrY hgY
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp - 8 := by rw [hgY]; try rfl
  have hdY : Y.cpu.gpr.rdi = aQ X.cpu.gpr.rsp := by rw [hgY]; try rfl
  have hiY : Y.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hgY]; try rfl
  have hra41 : rdq(Wd V X.cpu.gpr fb, aQ X.cpu.gpr.rsp - 8) = lpb_at.add 41 := by
    dsimp only [Wd]
    rw [Tun.rd_Vst_self (Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (lpb_at.add 41) 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  refine Lpd.lpd_ok c hinD hKY hAY hrY (by rw [hiY]; exact fr1) (by rw [hiY]; exact fr0) (by rw [hdY]; exact fw4)
    (by rw [hdY]; exact fw0) (by rw [hdY]; exact fw2) (by rw [hdY]; exact fw1) (by rw [hdY]; omega)
    (by rw [hsY]; exact fl) (by rw [hsY]; omega) (by rw [hdY, hsY]; omega) hin (lt_len (j := 41) (by decide))
    (by rw [hsY]; exact hra41) ?_
  intro Z t₂ V' r cx d hres hKZ hAZ hrZ hgZ
  rw [hdY] at hres
  have hg41 : Z.cpu.gpr = g41 X.cpu.gpr r cx d := by
    rw [hgZ, hsY, e8, hgY]
    try rfl
  -- reads apart from `propNew`
  have rdR : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ (aQ X.cpu.gpr.rsp).toNat ∨ (aQ X.cpu.gpr.rsp).toNat + 8 ≤ x.toNat) →
      rdq(V', x) = rdq(Wd V X.cpu.gpr fb, x) := fun x hx hd =>
    congrArg (ofBytesLE 64) (res_out hres (by omega) hx hd)
  -- reads apart from the frame's four stores
  have rd0 : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat - 40 ≤ x.toNat) →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat - 24 ≤ x.toNat) →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      rdq(Wd V X.cpu.gpr fb, x) = rdq(V, x) := fun x hx h1 h2 h3 =>
    congrArg (ofBytesLE 64)
      ((Tun.rd_Vst _ (aQ X.cpu.gpr.rsp - 8) _ x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega)).trans
      ((Tun.rd_Vst _ (aQ X.cpu.gpr.rsp + 8#64) _ x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega)).trans
      ((Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8) _ x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega)).trans
      (Tun.rd_Vst _ (X.cpu.gpr.rsp - 8) _ x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega)))))
  -- the stack guard's copy: the 8 bytes read at `fs:0x28` after the pushes, those at the entry
  have hcn : rdq(Wd V X.cpu.gpr fb, aQ X.cpu.gpr.rsp + 8#64) = rdq(V, fb + 40#64) := by
    dsimp only [Wd]
    rw [congrArg (ofBytesLE 64) (Tun.rd_Vst (Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (lpb_at.add 41) 8) (aQ X.cpu.gpr.rsp + 8#64) 8 (by rw [toBytesLE_length]; omega) (by omega)
      (by rw [toBytesLE_length]; omega))]
    dsimp only [Vo]
    rw [Tun.rd_Vst_self (P2 V X.cpu.gpr) (aQ X.cpu.gpr.rsp + 8#64) (toBytesLE rdq(P2 V X.cpu.gpr, fb + 40#64) 8)
      (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl _]
    dsimp only [P2]
    exact congrArg (ofBytesLE 64)
      ((Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8) _ (fb + 40#64) 8 (by rw [toBytesLE_length]; omega) hcb
        (by rw [toBytesLE_length]; omega)).trans
      (Tun.rd_Vst _ (X.cpu.gpr.rsp - 8) _ (fb + 40#64) 8 (by rw [toBytesLE_length]; omega) hcb
        (by rw [toBytesLE_length]; omega)))
  have hc : rdq(V', aQ X.cpu.gpr.rsp + 8#64) = rdq(V', fb + 40#64) := by
    rw [rdR (aQ X.cpu.gpr.rsp + 8#64) (by omega) (by omega), rdR (fb + 40#64) hcb (by omega), hcn,
      rd0 (fb + 40#64) hcb (by omega) (by omega) (by omega)]
  have hraZ : rdq(V', aQ X.cpu.gpr.rsp + 40#64) = e₂.add j₂ := by
    rw [e40, rdR X.cpu.gpr.rsp hSb (by omega), rd0 X.cpu.gpr.rsp hSb (by omega) (by omega) (by omega)]
    exact hra
  refine lpb_ret (P := P) c hfs hin hinA hKZ hAZ hrZ hcl hcb
    (by rw [hg41]; show (aQ X.cpu.gpr.rsp).toNat + 48 ≤ 2 ^ 64; omega)
    (by rw [hg41]; exact wr) (by rw [hg41]; exact f0) (by rw [hg41]; exact f1) (by rw [hg41]; exact f8)
    (by rw [hg41]; exact f24) (by rw [hg41]; exact f32) (by
      rw [hg41]; show ∀ i < 8, Foot F.data (Addr.add (aQ X.cpu.gpr.rsp + 40#64) i); rw [e40]; exact f40)
    (by rw [hg41]; exact wb) (by rw [hg41]; exact hbb)
    (by rw [hg41]; show X.cpu.gpr.rdi.toNat + 8 ≤ (aQ X.cpu.gpr.rsp).toNat + 8 ∨
      (aQ X.cpu.gpr.rsp).toNat + 48 ≤ X.cpu.gpr.rdi.toNat; omega)
    (by rw [hg41]; exact hbc) (by rw [hg41]; exact hc) hin₂ h₂ (by rw [hg41]; exact hraZ) ?_ ?_ ?_ ?_
  · rw [hg41]; exact k0 r cx d V' hres
  · rw [hg41]; exact k2 r cx d V' hres
  · exact kn
  · rw [hg41]; exact kz

end FV7z.Lpb
