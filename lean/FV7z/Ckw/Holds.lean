import FV7z.Ckw.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NCrypto::N7z::CKey::Wipe` (PLAN.md §M, M1)

7-Zip 26.06's `CKey::Wipe ()` at `0x59ea70` in `7zzs` (`CPP/7zip/Crypto/7zAes.h`): with `this` in `rdi`, if the
password's size (the 8 bytes at `this + 80`) is not 0, `memset (Password._items, 0, size)` (the 8 bytes at
`this + 72`; `call` at 62 to the PLT entry at `0x401080`); then `NumCyclesPower = 0` (the 8 bytes at `this + 64`) and
`Salt`, `Key` zeroed (16 bytes each at `this + 96`, `this`, `+ 16`, `+ 32`, `+ 48`, through `xmm0`; the stored bytes
are not followed). `push rbx`, `rbx` = `this` across the call, `pop rbx; ret` (49).

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`.

- `ckV`: the bytes after the stores at 17; `gN`: the registers at the `call`.
- `vc_z`, `vc_n`, `vc_17`: the verification conditions of the pieces (the size 0; not 0, to the `call`; the stores).
- `ckw_ok`: from the entry to the return address (`kz`), or through the callee (`kf`, `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ckw

/-- The `call` to `memset`'s PLT entry. -/
def pcall : List Byte := [0xe8, 0xcd, 0x25, 0xe6, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073707857357] 5) := by dec_rfl
theorem wc_62 : pcall <+: ckw.drop 62 := by decide +kernel
theorem call_62 (feat : Features) : Dec feat ckw 62 (FV7z.mk .call 64 [.rel 18446744073707857357] 5) :=
  Dec.shift (j := 62) (k := 0) (pcall_0 feat) wc_62 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_49 : pret <+: ckw.drop 49 := by decide +kernel
theorem ret_49 (feat : Features) : Dec feat ckw 49 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)

/-- The bytes after `mov qword [rbx + 64], 0` and the five 16-byte stores of `xmm0` (`b1` … `b5`). -/
abbrev ckV (W : Addr → Byte) (p : Addr) (b1 b2 b3 b4 b5 : List Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst W (p + 64#64) (toBytesLE 0#64 8)) (p + 96#64) b1) p b2) (p + 16#64) b3)
    (p + 32#64) b4) (p + 48#64) b5

/-- The registers at the `call`: `rdx` = the size, `rbx` = `this`, `rbx` pushed, `rdi` = the password's bytes,
`rsi` = 0. -/
abbrev gN (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rdx := rdq(V, g.rdi + 80#64), rbx := g.rdi, rsp := g.rsp - 8, rdi := rdq(V, g.rdi + 72#64), rsi := 0#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- The size 0: `push rbx; mov rdx, [rdi + 80]; mov rbx, rdi; test rdx, rdx; jne` to 17. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (f80 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 80#64) i))
    (hx : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 80#64) = rdq(V, g.rdi + 80#64))
    (hz : rdq(V, g.rdi + 80#64) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 17 ∧ g' = { g with rdx := 0, rbx := g.rdi, rsp := g.rsp - 8 } ∧
      V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst f80 hx hz ⊢
  wpx [W_0, W_56, o0, o2, hx, hz, BitVec.and_self, beq_self_eq_true, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- The size not 0: `push rbx; mov rdx, [rdi + 80]; mov rbx, rdi; test rdx, rdx; jne`, then
`mov rdi, [rdi + 72]; xor esi, esi` to the `call` at 62. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (f80 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 80#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 72#64) i))
    (hx : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 80#64) = rdq(V, g.rdi + 80#64))
    (hx72 : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 72#64) = rdq(V, g.rdi + 72#64))
    (hb : (rdq(V, g.rdi + 80#64) == 0) = false) :
    W_0 F Wl (fun j' g' _ V' => j' = 62 ∧ g' = gN V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst f80 f72 hx hx72 hb ⊢
  wpx [W_0, W_56, o0, o2, gN, hx, hx72, hb, BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `pxor xmm0, xmm0; mov qword [rbx + 64], 0; movups [rbx + 96], xmm0; movups [rbx], xmm0; movups [rbx + 16], xmm0;
movups [rbx + 32], xmm0; movups [rbx + 48], xmm0; pop rbx` to the `ret` at 49. -/
theorem vc_17 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p s : Addr} (hbx : g.rbx = p) (hsx : g.rsp = s)
    (w64 : ∀ i < 8, Foot Wl (Addr.add (p + 64#64) i)) (w96 : ∀ i < 16, Foot Wl (Addr.add (p + 96#64) i))
    (w0 : ∀ i < 16, Foot Wl (Addr.add p i)) (w16 : ∀ i < 16, Foot Wl (Addr.add (p + 16#64) i))
    (w32 : ∀ i < 16, Foot Wl (Addr.add (p + 32#64) i)) (w48 : ∀ i < 16, Foot Wl (Addr.add (p + 48#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add s i))
    (h : ∀ b1 b2 b3 b4 b5 : List Byte, b1.length = 16 → b2.length = 16 → b3.length = 16 → b4.length = 16 →
      b5.length = 16 → ∀ fl, Q 49 { g with rbx := rdq(ckV V p b1 b2 b3 b4 b5, s), rsp := s + 8 } fl
        (ckV V p b1 b2 b3 b4 b5)) :
    W_17 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx hsx h ⊢
  subst hbx hsx
  wpx [W_17, o1, Op.vs]
  all_goals repeat'
    first
    | exact h _ _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) _
    | assumption
    | exact trivial
    | (intro i hi; exact absurd hi (Nat.not_lt_zero _))
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CKey::Wipe ()` (`this` = `rdi`) from its entry. The size 0: at the return address with the bytes `ckV` over
`V` with `rbx` pushed, `rdx` = 0, the other registers as at the entry (`kz`). Not 0: at `memset`'s PLT entry the
registers are `gN` with `rsp` 16 below the entry's and the bytes `V` with `rbx` and the return address into
`CKey::Wipe` pushed (`kf`); if the callee returns to `ckw_at + 67` with `rsp` and `rbx` as at its entry, and the saved
`rbx` and the return address of `CKey::Wipe` as they were, the run reaches that return address with the bytes `ckV`
over the callee's and `rbx`, `rsp` restored (`kr`). -/
theorem ckw_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ckw_at ckw)
    {codeM : List Byte} (hinM : CodeIn L 0x401080#64 codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ckw_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f80 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 80#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 72#64) i))
    (w64 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (w96 : ∀ i < 16, Foot Wl (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (w0 : ∀ i < 16, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w16 : ∀ i < 16, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (w32 : ∀ i < 16, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (w48 : ∀ i < 16, Foot Wl (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 112 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 112 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : rdq(V, X.cpu.gpr.rdi + 80#64) = 0#64 → ∀ (b1 b2 b3 b4 b5 : List Byte) (Z : State) (t' : Nat),
      b1.length = 16 → b2.length = 16 → b3.length = 16 → b4.length = 16 → b5.length = 16 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem
        (ckV (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi b1 b2 b3 b4 b5) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : rdq(V, X.cpu.gpr.rdi + 80#64) ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (ckw_at.add 67) 8)) →
      Y.cpu.rip = 0x401080#64 → Y.cpu.gpr = (gN V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ckw_at.add 67 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (b1 b2 b3 b4 b5 : List Byte) (Z' : State) (t' : Nat),
      b1.length = 16 → b2.length = 16 → b3.length = 16 → b4.length = 16 → b5.length = 16 → Pc Z V' →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (ckV V' X.cpu.gpr.rdi b1 b2 b3 b4 b5) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  have tk : ∀ k : Nat, k < 112 → (X.cpu.gpr.rdi + BitVec.ofNat 64 k).toNat = X.cpu.gpr.rdi.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have t48 := tk 48 (by omega)
  have t32 := tk 32 (by omega)
  have t16 := tk 16 (by omega)
  have t96 := tk 96 (by omega)
  have t64 := tk 64 (by omega)
  have t72 := tk 72 (by omega)
  have t80 := tk 80 (by omega)
  -- the bytes stored by `push rbx`
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  -- the bytes stored at 17
  have ck : ∀ (W : Addr → Byte) (x : Addr) (b1 b2 b3 b4 b5 : List Byte), b1.length = 16 → b2.length = 16 →
      b3.length = 16 → b4.length = 16 → b5.length = 16 → x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 112 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (ckV W X.cpu.gpr.rdi b1 b2 b3 b4 b5) = (byteAddrs x 8).map W := by
    intro W x b1 b2 b3 b4 b5 h1 h2 h3 h4 h5 hx h
    dsimp only [ckV]
    rw [Tun.rd_Vst _ (X.cpu.gpr.rdi + 48#64) b5 x 8 (by rw [h5, t48]; omega) hx (by rw [h5, t48]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 32#64) b4 x 8 (by rw [h4, t32]; omega) hx (by rw [h4, t32]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 16#64) b3 x 8 (by rw [h3, t16]; omega) hx (by rw [h3, t16]; omega),
      Tun.rd_Vst _ X.cpu.gpr.rdi b2 x 8 (by rw [h2]; omega) hx (by rw [h2]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 96#64) b1 x 8 (by rw [h1, t96]; omega) hx (by rw [h1, t96]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 64#64) (toBytesLE 0#64 8) x 8 (by rw [toBytesLE_length, t64]; omega) hx
        (by rw [toBytesLE_length, t64]; omega)]
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 17 to the return address
  have tail : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = ckw_at.add 17 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Y.cpu.gpr.rbx = X.cpu.gpr.rdi →
      rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ →
      (∀ (b1 b2 b3 b4 b5 : List Byte) (Z : State) (t'' : Nat), b1.length = 16 → b2.length = 16 →
        b3.length = 16 → b4.length = 16 → b5.length = 16 → KeptW Wl s₀ Z →
        Agree F Z.proc.mm.mem (ckV W X.cpu.gpr.rdi b1 b2 b3 b4 b5) → Z.cpu.rip = e₂.add j₂ →
        Z.cpu.gpr = { Y.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hsY hbY hb hr k
    refine (c_17 prof).run c hin (fun j' g' _ V'' => j' = 49 ∧ ∃ b1 b2 b3 b4 b5 : List Byte, b1.length = 16 ∧
        b2.length = 16 ∧ b3.length = 16 ∧ b4.length = 16 ∧ b5.length = 16 ∧
        g' = { Y.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V'' = ckV W X.cpu.gpr.rdi b1 b2 b3 b4 b5) hKY hAY hrY
      (vc_17 hbY hsY w64 w96 w0 w16 w32 w48 h8 fun b1 b2 b3 b4 b5 h1 h2 h3 h4 h5 _ =>
        ⟨rfl, b1, b2, b3, b4, b5, h1, h2, h3, h4, h5,
          by rw [ck W (X.cpu.gpr.rsp - 8) b1 b2 b3 b4 b5 h1 h2 h3 h4 h5 hq8 (by rw [tn8]; omega), hb, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, b1, b2, b3, b4, b5, h1, h2, h3, h4, h5, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_49 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU, ck W X.cpu.gpr.rsp b1 b2 b3 b4 b5 h1 h2 h3 h4 h5 hp8 (by omega)]; exact hr) ?_
    rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k b1 b2 b3 b4 b5 Z t₄ h1 h2 h3 h4 h5 hKZ hAZ hrZ ?_
    rw [hgZ, hgU]
    try rfl
  have hrip' : X.cpu.rip = ckw_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hx : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 80#64) =
      rdq(V, X.cpu.gpr.rdi + 80#64) := by
    rw [m8 (X.cpu.gpr.rdi + 80#64) 8 (by rw [t80]; omega) (by rw [t80]; omega)]
  have hsb : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8, ofBytesLE_toBytesLE (n := 8) rfl]
  have hr1 : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m8 X.cpu.gpr.rsp 8 hp8 (by omega)]
    exact hra
  by_cases hz : rdq(V, X.cpu.gpr.rdi + 80#64) = 0#64
  · -- the size 0: to 17
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 17 ∧
        g' = { X.cpu.gpr with rdx := 0#64, rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8 } ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip' (vc_z hs1 f80 hx hz) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine tail Y _ t₁ hKY hAY hrY (by rw [hgY]) (by rw [hgY]) hsb hr1 ?_
    intro b1 b2 b3 b4 b5 Z t'' h1 h2 h3 h4 h5 hKZ hAZ hrZ hgZ
    refine kz hz b1 b2 b3 b4 b5 Z t'' h1 h2 h3 h4 h5 hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- not 0: to the `call`
    have hb : (rdq(V, X.cpu.gpr.rdi + 80#64) == 0) = false := beq_eq_false_iff_ne.2 hz
    have hx72 : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 72#64) =
        rdq(V, X.cpu.gpr.rdi + 72#64) := by
      rw [m8 (X.cpu.gpr.rdi + 72#64) 8 (by rw [t72]; omega) (by rw [t72]; omega)]
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 62 ∧ g' = gN V X.cpu.gpr ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip' (vc_n hs1 f80 f72 hx hx72 hb) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_62 _) hinM hM (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gN V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gN V X.cpu.gpr).set 4 v) e16
    refine kf hz Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee: the jump at 67 to 17
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb' hr' hPc
    refine (c_67 prof).run c hin (fun j' g' _ V'' => j' = 17 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (by unfold W_67; exact ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    refine tail Y₃ V' t₃ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hzs) (by rw [hg₃]; exact hzb) hb' hr' ?_
    intro b1 b2 b3 b4 b5 Z' t₄ h1 h2 h3 h4 h5 hKZ' hAZ' hrZ' hgZ'
    refine kr Z V' b1 b2 b3 b4 b5 Z' t₄ h1 h2 h3 h4 h5 hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hg₃]

end FV7z.Ckw
