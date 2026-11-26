import FV7z.Ldf.Cuts
import FV7z.Lfp.Holds
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `LzmaDec_Free` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_Free (p, alloc)` at `0x42be70` in `7zzs` (`C/LzmaDec.c`):
`LzmaDec_FreeProbs (p, alloc); ISzAlloc_Free (alloc, p->dic); p->dic = NULL`. `push rbp; push rbx` (`rbp` =
`alloc`, `rbx` = `p`), `sub rsp, 8`, `call LzmaDec_FreeProbs` (16, `Lfp.lfp_ok`), `rsi` = `p->dic` (the 8 bytes at
`p + 24`), `rdi` = `alloc`, `call qword [alloc + 8]` (28, `Seg.s_callM`), `p->dic` = 0, `add rsp, 8; pop rbx; pop
rbp; ret` (45). With `s` the entry's `rsp`, the frame is `[s - 48, s)`: `rbp` at `s - 8`, `rbx` at `s - 16`, the
return address into `LzmaDec_Free` at `s - 32` (both calls), `LzmaDec_FreeProbs`'s `rbx` and return address at
`s - 40` and `s - 48`.

The callee `alloc->Free` (the 8 bytes at `alloc + 8`) is a hypothesis, as in `Lfp.lfp_ok`: `kf1` for the call from
`LzmaDec_FreeProbs` (its post `Pc1`, which has to give back `rbp` and the second target, `hP1`), `kf2` for the
call at 28 (its post `Pc2`), `kr` from the return.

- `vc_0`, `vc_21`, `vc_31`: the verification conditions of the three pieces.
- `ldf_ok`: from the entry, through both calls, to the return address with `p->probs` = `p->dic` = 0 and `rbx`,
  `rbp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ldf

/-- The call of `LzmaDec_FreeProbs`. -/
def pcl : List Byte := [0xe8, 0x5b, 0xff, 0xff, 0xff]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 18446744073709551451] 5) := by dec_rfl
theorem wl_16 : pcl <+: ldf.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat ldf 16 (FV7z.mk .call 64 [.rel 18446744073709551451] 5) :=
  Dec.shift (j := 16) (k := 0) (pcl_0 feat) wl_16 (Nat.zero_le _)

/-- The call through `alloc->Free`. -/
def pcall : List Byte := [0xff, 0x55, 0x08]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 5 8 64)] 3) := by dec_rfl
theorem wc_28 : pcall <+: ldf.drop 28 := by decide +kernel
theorem call_28 (feat : Features) : Dec feat ldf 28 (FV7z.mk .call 64 [.mem (mbd 5 8 64)] 3) :=
  Dec.shift (j := 28) (k := 0) (pcall_0 feat) wc_28 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_45 : pret <+: ldf.drop 45 := by decide +kernel
theorem ret_45 (feat : Features) : Dec feat ldf 45 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 45) (k := 0) (pret_0 feat) w_45 (Nat.zero_le _)

/-! ## Offsets from the entry's `rsp` -/

theorem m8_8 (x : BitVec 64) : x - 8 - 8 = x - 16 := by bv_omega
theorem m16_8 (x : BitVec 64) : x - 16 - 8#64 = x - 24 := by bv_omega
theorem m24_8 (x : BitVec 64) : x - 24 - 8 = x - 32 := by bv_omega
theorem m32_8 (x : BitVec 64) : x - 32 - 8 = x - 40 := by bv_omega
theorem m32_16 (x : BitVec 64) : x - 32 - 16 = x - 48 := by bv_omega
theorem p32_8 (x : BitVec 64) : x - 32 + 8 = x - 24 := by bv_omega
theorem p24_8 (x : BitVec 64) : x - 24 + 8#64 = x - 16 := by bv_omega
theorem p16_8 (x : BitVec 64) : x - 16 + 8 = x - 8 := by bv_omega
theorem p8_8 (x : BitVec 64) : x - 8 + 8 = x := by bv_omega

/-- The registers at 16: `rbp` = `alloc`, `rbx` = `p`, `rsp` 24 below. -/
abbrev g16 (g : Gprs) : Gprs := { g with rbp := g.rsi, rbx := g.rdi, rsp := g.rsp - 24 }
/-- The bytes at 16: `rbp` and `rbx` pushed. -/
abbrev V16 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 16) (toBytesLE g.rbx 8)
/-- The bytes at `alloc->Free`'s entry from `LzmaDec_FreeProbs`. -/
abbrev M1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (V16 V g) (g.rsp - 32) (toBytesLE (ldf_at.add 21) 8)) (g.rsp - 40) (toBytesLE g.rdi 8))
    (g.rsp - 48) (toBytesLE (Lfp.lfp_at.add 21) 8)
/-- The registers at `alloc->Free`'s entry from `LzmaDec_FreeProbs`. -/
abbrev G1 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := g.rsi, rbx := g.rdi, rbp := g.rsi, rsp := g.rsp - 48, rsi := rdq(V, g.rdi + 8#64), rdi := g.rsi }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov rbp, rsi; push rbx; mov rbx, rdi; sub rsp, 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 16) i)) :
    wp F Wl o0 (fun g' _ V' => g' = g16 g ∧ V' = V16 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs8 hs16 ⊢
  wpx [o0, g16, V16, m8_8, m16_8]
  repeat' (first | exact hs8 | exact hs16 | apply And.intro | intro _)
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- `mov rsi, [rbx + 24]; mov rdi, rbp`. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 24#64) i))
    (h : ∀ fl, Q 28 { g with rsi := rdq(V, g.rbx + 24#64), rdi := g.rbp } fl V) :
    W_21 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_21, o1]
  repeat' (first | exact hl | apply And.intro | intro _)
  all_goals first | exact h _ | (simp only [BitVec.setWidth_eq]; exact h _)

/-- `mov qword [rbx + 24], 0; add rsp, 8; pop rbx; pop rbp`. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 24#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 45 { g with rbx := rdq(Vst V (g.rbx + 24#64) (toBytesLE 0#64 8), g.rsp + 8#64),
      rbp := rdq(Vst V (g.rbx + 24#64) (toBytesLE 0#64 8), g.rsp + 8#64 + 8), rsp := g.rsp + 8#64 + 8 + 8 } fl
      (Vst V (g.rbx + 24#64) (toBytesLE 0#64 8))) :
    W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl1 hl2 h ⊢
  wpx [W_31, o2]
  repeat' (first | exact hw | exact hl1 | exact hl2 | apply And.intro | intro _)
  all_goals first | exact h _ | (simp only [BitVec.setWidth_eq]; exact h _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_Free (p, alloc)` (`p` = `rdi`, `alloc` = `rsi`) from its entry, `s` its `rsp`. At `alloc->Free`'s entry
from `LzmaDec_FreeProbs` the registers are `G1` and the bytes `M1` (`kf1`); its return (`Pc1`, with `hP1`) leads to
the second call, whose entry has `rbx` = `p`, `rsp` = `s - 32`, `rsi` = `p->dic`, `rdi` = `alloc` and the return
address `ldf_at + 31` at `s - 32` (`kf2`); from its return (`Pc2`) the run reaches the return address with
`p->probs` and `p->dic` 0 and `rbx`, `rbp` restored (`kr`). -/
theorem ldf_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L ldf_at ldf) (hinL : CodeIn L Lfp.lfp_at Lfp.lfp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ldf_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs40 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs48 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (hpn : X.cpu.gpr.rdi.toNat + 32 ≤ 2 ^ 64)
    (hps : X.cpu.gpr.rdi.toNat + 32 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (han : X.cpu.gpr.rsi.toNat + 16 ≤ 2 ^ 64)
    (has : X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hpa : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat + 8 ∨ X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rdi.toNat + 8)
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(V, X.cpu.gpr.rsi + 8#64) = eF)
    {eF₂ : Addr} {codeF₂ : List Byte} (hinF₂ : CodeIn L eF₂ codeF₂) (hF₂0 : 0 < codeF₂.length)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (M1 V X.cpu.gpr) →
      Y.cpu.rip = eF → Y.cpu.gpr = G1 V X.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Lfp.lfp_at.add 21 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 40) = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 32) = ldf_at.add 21 → Pc1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (hP1 : ∀ (Z : State) (V' : Addr → Byte), Pc1 Z V' → Z.cpu.gpr.rbp = X.cpu.gpr.rsi ∧
      rdq(V', X.cpu.gpr.rsi + 8#64) = eF₂)
    (kf2 : ∀ (Zc : State) (V' : Addr → Byte), Pc1 Zc V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (ldf_at.add 31) 8)) →
      Y.cpu.rip = eF₂ →
      Y.cpu.gpr = { Zc.cpu.gpr with rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 32,
        rsi := rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rdi + 24#64),
        rdi := X.cpu.gpr.rsi } →
      (∀ (Z : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V'' →
        Z.cpu.rip = ldf_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V'', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z V'' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V'' (X.cpu.gpr.rdi + 24#64) (toBytesLE 0#64 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have t8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tp8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have tp24 : (X.cpu.gpr.rdi + 24#64).toNat = X.cpu.gpr.rdi.toNat + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ta8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- a read of 8 bytes past a store of 8 bytes, apart
  have rd : ∀ (W : Addr → Byte) (a x : Addr) (bs : List Byte), bs.length = 8 → a.toNat + 8 ≤ 2 ^ 64 →
      x.toNat + 8 ≤ 2 ^ 64 → (a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) →
      rdq(Vst W a bs, x) = rdq(W, x) := fun W a x bs hb ha hx h => by
    rw [Tun.rd_Vst W a bs x 8 (by rw [hb]; exact ha) hx (by rw [hb]; exact h)]
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs8 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs16 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs32 i hi)
  -- to the first call
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ g' = g16 X.cpu.gpr ∧ V' = V16 V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 hs8 hs16)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_16 _) hinL (Lfp.lt_len (by decide)) (by decide)
    (by rw [hsY, m24_8]; exact hs32) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, m24_8] at hA₂
  have hA₂' : Agree F Y₂.proc.mm.mem (Vst (V16 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ldf_at.add 21) 8)) :=
    hA₂
  have hs₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hg₂, hsY, m24_8]; rfl
  have hb₂ : Y₂.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg₂, hgY]; rfl
  have hd₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hgY]; rfl
  have hi₂ : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg₂, hgY]; rfl
  -- the reads of `p->probs` and of the target past the three stores of the frame
  have rp8 : rdq(Vst (V16 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ldf_at.add 21) 8), X.cpu.gpr.rdi + 8#64) =
      rdq(V, X.cpu.gpr.rdi + 8#64) := by
    simp only [V16]
    rw [rd _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rdi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega),
      rd _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rdi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega),
      rd _ (X.cpu.gpr.rsp - 8) (X.cpu.gpr.rdi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega)]
  have ra8 : rdq(Vst (V16 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ldf_at.add 21) 8), X.cpu.gpr.rsi + 8#64) =
      rdq(V, X.cpu.gpr.rsi + 8#64) := by
    simp only [V16]
    rw [rd _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega),
      rd _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rsi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega),
      rd _ (X.cpu.gpr.rsp - 8) (X.cpu.gpr.rsi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega) (by omega)]
  refine Lfp.lfp_ok (Pc := Pc1) (e₂ := ldf_at) (j₂ := 21) c hinL hK₂ hA₂' hr₂
    (by rw [hs₂, t32]; omega) (by rw [hs₂, t32]; omega)
    (by rw [hs₂, m32_8]; exact hs40) (by rw [hs₂, m32_16]; exact hs48)
    (fun i hi => by rw [hs₂]; exact h32 i hi)
    (by rw [hd₂]; exact fw8) (by rw [hd₂, tp8]; omega) (by rw [hd₂, hs₂, tp8, t32]; omega)
    (by rw [hi₂]; exact fb) (by rw [hi₂, ta8]; omega) (by rw [hi₂, hs₂, ta8, t32]; omega)
    hinF hF0 (by rw [hi₂, ra8]; exact htgt) hin (lt_len (by decide)) ?_ ?_
  · -- into `alloc->Free` from `LzmaDec_FreeProbs`
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ k₃
    rw [hs₂, m32_8, m32_16, hb₂] at hA₃
    refine kf1 Y₃ t₃ hK₃ hA₃ hr₃ ?_ ?_
    · rw [hg₃, hg₂, hgY]
      simp only [Lfp.gC, g16, G1, sk4', rsp_mk, m24_8, m32_16, rp8]
    · intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
      exact k₃ Z V' t'' hKZ hAZ hrZ (by rw [hzs, hs₂, m32_8]) (by rw [hzb, hd₂])
        (by rw [hs₂, m32_8, hb₂]; exact hb) (by rw [hs₂]; exact hr') hPc
  · -- back in `LzmaDec_Free` at 21
    intro Z V' Z' t₃ hPc hKZ' hAZ' hrZ' hgZ'
    obtain ⟨hzp, hvt⟩ := hP1 Z V' hPc
    rw [hd₂] at hAZ'
    have hz'b : Z'.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgZ', hb₂]
    have hz's : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgZ', hs₂, p32_8]
    have hz'p : Z'.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hgZ']; exact hzp
    refine (c_21 prof).run c hin (fun j' g' _ V'' => j' = 28 ∧
        g' = { Z'.cpu.gpr with rsi := rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rdi + 24#64),
          rdi := X.cpu.gpr.rsi } ∧ V'' = Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) hKZ' hAZ' hrZ'
      (vc_21 (by rw [hz'b]; exact fun i hi => c.hws _ (fw24 i hi)) fun _ => ⟨rfl, by rw [hz'b, hz'p], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₄ hKU hAU hrU hgU -
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hz's
    have he : eaD U 5 8 = X.cpu.gpr.rsi + 8#64 := by
      show U.cpu.gpr.get (regOf 5) + BitVec.ofNat 64 8 = _
      rw [hgU]
      show Z'.cpu.gpr.rbp + 8#64 = _
      rw [hz'p]
    have rt : rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rsi + 8#64) = eF₂ := by
      rw [rd _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsi + 8#64) _ (toBytesLE_length _ _) (by omega) (by omega)
        (by omega)]
      exact hvt
    refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_28 _) (by rw [he]; exact fb) hinF₂ hF₂0
      (by rw [he]; exact rt) (by rw [hsU, m24_8]; exact hs32) ?_
    rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hsU, m24_8] at hA₄
    refine kf2 Z V' hPc Y₄ t₅ hK₄ hA₄ hr₄ ?_ ?_
    · rw [hg₄, hsU, m24_8, hgU, hgZ']
      simp only [sk4', hb₂]
    · -- back at 31
      intro Z₂ V'' t'' hKZ₂ hAZ₂ hrZ₂ hz2s hz2b hb16 hb8 hret hPc2
      have r16 : rdq(Vst V'' (X.cpu.gpr.rdi + 24#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
        rw [rd _ (X.cpu.gpr.rdi + 24#64) (X.cpu.gpr.rsp - 16) _ (toBytesLE_length _ _) (by omega) (by omega)
          (by omega)]
        exact hb16
      have r8 : rdq(Vst V'' (X.cpu.gpr.rdi + 24#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
        rw [rd _ (X.cpu.gpr.rdi + 24#64) (X.cpu.gpr.rsp - 8) _ (toBytesLE_length _ _) (by omega) (by omega)
          (by omega)]
        exact hb8
      have r0 : rdq(Vst V'' (X.cpu.gpr.rdi + 24#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
        rw [rd _ (X.cpu.gpr.rdi + 24#64) X.cpu.gpr.rsp _ (toBytesLE_length _ _) (by omega) hp8 (by omega)]
        exact hret
      refine (c_31 prof).run c hin (fun j' g' _ V₃ => j' = 45 ∧
          g' = { Z₂.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp } ∧
          V₃ = Vst V'' (X.cpu.gpr.rdi + 24#64) (toBytesLE 0#64 8)) hKZ₂ hAZ₂ hrZ₂
        (vc_31 (by rw [hz2b]; exact fw24) (by rw [hz2s, p24_8]; exact h16) (by rw [hz2s, p24_8, p16_8]; exact h8)
          fun _ => ⟨rfl, by rw [hz2b, hz2s, p24_8, p16_8, p8_8, r16, r8], by rw [hz2b]⟩) ?_
      rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ W t₆ hKW hAW hrW hgW -
      have hsW : W.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgW]
      refine c.s_ret hKW hAW hin (lt_len (by decide)) hrW (ret_45 _) (by rw [hsW]; exact hl) hin₂ h₂
        (by rw [hsW]; exact r0) ?_
      rintro Z₃ t₇ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
      refine kr Z₂ V'' Z₃ t₇ hPc2 hKZ₃ hAZ₃ hrZ₃ ?_
      rw [hgZ₃, hgW]
      try rfl

end FV7z.Ldf
