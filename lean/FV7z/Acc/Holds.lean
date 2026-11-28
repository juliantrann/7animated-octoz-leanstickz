import FV7z.Acc.Loop
import FV7z.Acp.Holds
/-!
# `AString::AString (const char *)` (PLAN.md §M, M1)

7-Zip's `AString (const char *s)` at `0x44c3c0` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi` and `s`
in `rsi`, `push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 8`, the length loop (`FV7z/Acc/Loop.lean`) to
44, `mov rdi, rbp` and `SetStartLen (len)` (`call` at 47 to `Asl.asl_at`, proved in `FV7z/Asl/Holds.lean`), then
`mov rcx, [rbp]; xor eax, eax` and the copy loop at 64 through the 0, the `pop`s and the `ret` at 85.

`SetStartLen` is run by `Asl.asl_ok`; its own callee (`operator new`) is a hypothesis (`kf`) in the form `asl_ok`
takes, for any registers at `SetStartLen`'s entry with `rsp`, `rdi` = `this`, `rsi` = `n`, `rbx` = `s`, `rbp` =
`this` and `r12` … `r15` as they are; its post is `Pk`: the frame (the saved `rbx`, `rbp`, the return address) and
`r12` … `r15` as they were, the `n + 1` bytes of the string as they were, the new buffer (`rax`) writable, apart from
the string and from the frame, and `P1`.

- `Pk`: the post of `operator new` in `SetStartLen`.
- `vc_44`, `vc_52`: the verification conditions of the pieces around the `call`.
- `acc_ok`: from the entry, through the length loop, `SetStartLen` and the copy loop, to the return.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Acc

/-- The `call` of `SetStartLen`. -/
def pcs : List Byte := [0xe8, 0x6c, 0xfc, 0xff, 0xff]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 18446744073709550700] 5) := by dec_rfl
theorem wc_47 : pcs <+: acc.drop 47 := by decide +kernel
theorem call_47 (feat : Features) : Dec feat acc 47 (FV7z.mk .call 64 [.rel 18446744073709550700] 5) :=
  Dec.shift (j := 47) (k := 0) (pcs_0 feat) wc_47 (Nat.zero_le _)

/-- The `ret`. -/
theorem w_85 : Asl.pret <+: acc.drop 85 := by decide +kernel
theorem ret_85 (feat : Features) : Dec feat acc 85 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 85) (k := 0) (Asl.pret_0 feat) w_85 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The post of `operator new` in `SetStartLen`, for the registers `g` and the bytes `V` at the entry, the string of
`n` bytes not 0 and a 0 at `s` (`rsi`), the return address `ra`: the frame and `r12` … `r15` as they were, the
string as it was, the buffer `rax` writable, apart from the string and from the frame, and `P1`. -/
def Pk (g : Gprs) (V : Addr → Byte) (n : Nat) (ra : Addr) (P1 : State → (Addr → Byte) → Prop) (Z : State)
    (V' : Addr → Byte) : Prop :=
  rdq(V', g.rsp - 16) = g.rbx ∧ rdq(V', g.rsp - 8) = g.rbp ∧ rdq(V', g.rsp) = ra ∧
    Z.cpu.gpr.r12 = g.r12 ∧ Z.cpu.gpr.r13 = g.r13 ∧ Z.cpu.gpr.r14 = g.r14 ∧ Z.cpu.gpr.r15 = g.r15 ∧
    (∀ i, i ≤ n → V' (Addr.add g.rsi i) = V (Addr.add g.rsi i)) ∧
    (∀ i, i ≤ n → Foot Wl (Addr.add Z.cpu.gpr.rax i)) ∧ Z.cpu.gpr.rax.toNat + n + 1 ≤ 2 ^ 64 ∧
    (Z.cpu.gpr.rax.toNat + n + 1 ≤ g.rsi.toNat ∨ g.rsi.toNat + n + 1 ≤ Z.cpu.gpr.rax.toNat) ∧
    (Z.cpu.gpr.rax.toNat + n + 1 ≤ g.rsp.toNat - 16 ∨ g.rsp.toNat + 8 ≤ Z.cpu.gpr.rax.toNat) ∧ P1 Z V'

/-- `mov rdi, rbp`, to the `call` at 47. -/
theorem vc_44 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_44 F Wl (fun j' g' _ V' => j' = 47 ∧ g' = { g with rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_44, o3]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `SetStartLen`: `mov rcx, [rbp]; xor eax, eax`, to the copy loop at 64. -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) :
    W_52 F Wl (fun j' g' _ V' => j' = 64 ∧ g' = { g with rcx := rdq(V, g.rbp), rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 ⊢
  wpx [W_52, o4, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString (const char *s)` (`this` = `rdi`, `s` = `rsi`) from its entry, for `s` with `n` bytes not 0 and a 0.
The length loop gives `n`; `SetStartLen (n)` runs with `this` and `n`; its callee is `kf`, in the form `Asl.asl_ok`
takes for any registers at its entry with `rsp`, `rdi`, `rsi`, `rbx`, `rbp` and `r12` … `r15` as the code has them,
with the post `Pk`. Back at 52, the copy loop copies the `n + 1` bytes to the new buffer (the callee's `rax`), and the
run returns with the registers a call keeps as at the entry, the bytes `_chars`, `_len`, `_limit` as `SetStartLen`
stores them (`Asl.V1`) and the string copied (`Acp.Cp`) (`k`). -/
theorem acc_ok {P1 : State → (Addr → Byte) → Prop} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L acc_at acc) (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acc_at)
    (hp : 64 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hn : n < 2 ^ 32) (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rsi i) ≠ 0#8)
    (hz : V (Addr.add X.cpu.gpr.rsi n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hpw : X.cpu.gpr.rsi.toNat + n + 1 ≤ 2 ^ 64)
    (hpf : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    (hpt : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (G : Gprs), G.rsp = X.cpu.gpr.rsp - 32 → G.rdi = X.cpu.gpr.rdi → G.rsi = BitVec.ofNat 64 n →
      G.rbx = X.cpu.gpr.rsi → G.rbp = X.cpu.gpr.rdi → G.r12 = X.cpu.gpr.r12 → G.r13 = X.cpu.gpr.r13 →
      G.r14 = X.cpu.gpr.r14 → G.r15 = X.cpu.gpr.r15 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V0 (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8)) G) (G.rsp - 32)
          (toBytesLE (Asl.asl_at.add 34) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (Asl.gC G).set 4 (G.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Asl.asl_at.add 34 → Z.cpu.gpr.rsp = G.rsp - 24 → Z.cpu.gpr.rbx = G.rdi →
        Z.cpu.gpr.rbp = Asl.zl G → rdq(V', G.rsp - 16) = G.rbx → rdq(V', G.rsp - 8) = G.rbp →
        rdq(V', G.rsp) = acc_at.add 52 → Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k : ∀ (Z : State) (V' : Addr → Byte), Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1 Z V' →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Acp.Cp (Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax) X.cpu.gpr.rsi Z.cpu.gpr.rax (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn64 : (X.cpu.gpr.rsp - 64).toNat = X.cpu.gpr.rsp.toNat - 64 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 32 - 8 = X.cpu.gpr.rsp - 40 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have e48 : X.cpu.gpr.rsp - 32 - 16 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn48]
    simp <;> omega
  have e64 : X.cpu.gpr.rsp - 32 - 32 = X.cpu.gpr.rsp - 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn64]
    simp <;> omega
  have q24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have q16 : X.cpu.gpr.rsp - 24 + 8#64 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have q8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have q0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hrip' : X.cpu.rip = acc_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hpw' : X.cpu.gpr.rsi.toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have tp : ∀ i, i ≤ n → (Addr.add X.cpu.gpr.rsi i).toNat = X.cpu.gpr.rsi.toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hpw'
  -- the string after the two pushes
  have hV0 : ∀ i, i ≤ n → V0 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) :=
      fun i hi => by
    show Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (Addr.add X.cpu.gpr.rsi i) = _
    rw [e16, Tun.Vst_out _ (X.cpu.gpr.rsp - 16) _ _ (by rw [toBytesLE_length, tn16]; omega)
        (by rw [toBytesLE_length, tn16, tp i hi]; omega),
      Tun.Vst_out _ (X.cpu.gpr.rsp - 8) _ _ (by rw [toBytesLE_length, tn8]; omega)
        (by rw [toBytesLE_length, tn8, tp i hi]; omega)]
  have hl32 : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp <;> omega
  -- from 44: `mov rdi, rbp`, `SetStartLen`, the copy loop and the return
  have h44 : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V0 V X.cpu.gpr) →
      Y.cpu.rip = acc_at.add 44 → Y.cpu.gpr.rsi = BitVec.ofNat 64 n → Kp (gS X.cpu.gpr) Y.cpu.gpr →
      GoG prof L o gev gP gE Y t₁ := by
    intro Y t₁ hKY hAY hrY hsiY hkpY
    obtain ⟨ksp, kbx, kbp, k12, k13, k14, k15⟩ := hkpY
    refine (c_44 prof).run c hin _ hKY hAY hrY vc_44 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y' t₂ hKY' hAY' hrY' hgY' -
    have hY's : Y'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by
      rw [hgY']; show Y.cpu.gpr.rsp = _; rw [ksp]; exact e24
    have hst4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24 - 8) i) := by rw [e32]; exact hs4
    refine c.s_call hKY' hAY' hin (lt_len (by decide)) hrY' (call_47 _) hinS (by decide) (by decide)
      (by rw [hY's]; exact hst4) ?_
    rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY's, e32] at hA₂
    have hY2s : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by
      rw [hg₂]; show Y'.cpu.gpr.rsp - 8 = _; rw [hY's, e32]
    have hY2di : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by
      rw [hg₂]; show Y'.cpu.gpr.rdi = _; rw [hgY']; show Y.cpu.gpr.rbp = _; rw [kbp] <;> rfl
    have hY2si : Y₂.cpu.gpr.rsi = BitVec.ofNat 64 n := by
      rw [hg₂]; show Y'.cpu.gpr.rsi = _; rw [hgY']; exact hsiY
    have hY2bx : Y₂.cpu.gpr.rbx = X.cpu.gpr.rsi := by
      rw [hg₂]; show Y'.cpu.gpr.rbx = _; rw [hgY']; show Y.cpu.gpr.rbx = _; rw [kbx] <;> rfl
    have hY2bp : Y₂.cpu.gpr.rbp = X.cpu.gpr.rdi := by
      rw [hg₂]; show Y'.cpu.gpr.rbp = _; rw [hgY']; show Y.cpu.gpr.rbp = _; rw [kbp] <;> rfl
    have y12 : Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 := by
      rw [hg₂]; show Y'.cpu.gpr.r12 = _; rw [hgY']; show Y.cpu.gpr.r12 = _; rw [k12] <;> rfl
    have y13 : Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 := by
      rw [hg₂]; show Y'.cpu.gpr.r13 = _; rw [hgY']; show Y.cpu.gpr.r13 = _; rw [k13] <;> rfl
    have y14 : Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 := by
      rw [hg₂]; show Y'.cpu.gpr.r14 = _; rw [hgY']; show Y.cpu.gpr.r14 = _; rw [k14] <;> rfl
    have y15 : Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
      rw [hg₂]; show Y'.cpu.gpr.r15 = _; rw [hgY']; show Y.cpu.gpr.r15 = _; rw [k15] <;> rfl
    -- `SetStartLen`
    refine Asl.asl_ok (Pc := Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1) c hinS hinW hK₂ hA₂ hr₂
      (by rw [hY2s, tn32]; omega) (by rw [hY2s, tn32]; omega)
      (by rw [hY2s, e40]; exact hs5) (by rw [hY2s, e48]; exact hs6) (by rw [hY2s, e64]; exact hs8)
      (by rw [hY2s]; exact fun i hi => c.hws _ (hs4 i hi))
      (by rw [hY2di]; exact fw0) (by rw [hY2di]; exact fw8) (by rw [hY2di]; exact fw12) (by rw [hY2di]; exact hq)
      (by rw [hY2di, hY2s, tn32]; omega) (e₂ := acc_at) hin (j₂ := 52) (by decide)
      (kf Y₂.cpu.gpr hY2s hY2di hY2si hY2bx hY2bp y12 y13 y14 y15) ?_
    -- back from `SetStartLen`, to the copy loop
    rintro Z V' Z' t₄ hPk hKZ' hAZ' hrZ' hgZ'
    rw [hY2di, hY2si, hl32] at hAZ'
    have hPk0 := hPk
    obtain ⟨f16, f8, f0, z12, z13, z14, z15, hstr, hwd, hdw, hdp, hdf, -⟩ := hPk0
    have hZ'rbx : Z'.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hgZ']; exact hY2bx
    have hZ'rbp : Z'.cpu.gpr.rbp = X.cpu.gpr.rdi := by rw [hgZ']; exact hY2bp
    have hZ's : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by
      rw [hgZ']; show Y₂.cpu.gpr.rsp + 8 = _; rw [hY2s]; exact q24
    refine (c_52 prof).run c hin _ hKZ' hAZ' hrZ'
      (vc_52 (by rw [hZ'rbp]; exact fun i hi => c.hws _ (fw0 i hi))) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₅ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hdst : rdq(Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax, X.cpu.gpr.rdi) =
        Z.cpu.gpr.rax := Acs.rd1 _ _ _ _ (by omega)
    have hci : Y₃.cpu.gpr.rcx = Z.cpu.gpr.rax := by
      rw [hg₃]
      show rdq(Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax, Z'.cpu.gpr.rbp) = _
      rw [hZ'rbp]; exact hdst
    have hax : Y₃.cpu.gpr.rax = BitVec.ofNat 64 0 := by rw [hg₃] <;> rfl
    have hY3s : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact hZ's
    have hY3b : Y₃.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hg₃]; exact hZ'rbx
    have w12 : Y₃.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg₃, hgZ']; exact z12
    have w13 : Y₃.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg₃, hgZ']; exact z13
    have w14 : Y₃.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg₃, hgZ']; exact z14
    have w15 : Y₃.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg₃, hgZ']; exact z15
    have hdw' : Z.cpu.gpr.rax.toNat + (n + 1) ≤ 2 ^ 64 := by omega
    have td : ∀ i, i ≤ n → (Addr.add Z.cpu.gpr.rax i).toNat = Z.cpu.gpr.rax.toNat + i :=
      fun i hi => toNat_add_of_fits (by omega) hdw'
    have hWp : ∀ i, i ≤ n → Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax
        (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
      rw [Acp.byV1 _ _ _ _ _ hq (by rw [tp i hi]; omega), hstr i hi]
    have fr : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat →
        a.toNat ≤ X.cpu.gpr.rsp.toNat →
        rdq(Acp.Cp (Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax) X.cpu.gpr.rsi Z.cpu.gpr.rax (n + 1),
          a) = rdq(V', a) := fun a ha h1 h2 => by
      rw [Acp.rdCp _ _ _ _ a ha hdw' (by omega), Acp.rdV1 V' X.cpu.gpr.rdi _ _ a hq ha (by omega)]
    -- the copy loop, the `pop`s and the `ret`
    refine loop c hin (W := Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax)
      (p := X.cpu.gpr.rsi) (d := Z.cpu.gpr.rax) (n := n) (g₀ := Y₃.cpu.gpr) (by omega)
      (fun i hi => by rw [hWp i (by omega)]; exact hnz i hi) (by rw [hWp n (Nat.le_refl _)]; exact hz) hf hwd
      (fun i hi j hj e => by
        have := congrArg BitVec.toNat e
        rw [tp i hi, td j hj] at this
        omega) hY3b
      (by rw [hY3s, q16]; exact fun i hi => c.hws _ (hs2 i hi))
      (by rw [hY3s, q16, q8]; exact fun i hi => c.hws _ (hs1 i hi)) ?_ n 0 (by omega) Y₃ t₅ hK₃ hA₃ hr₃
      hax hci (Kp.refl _)
    intro Z₄ t₆ hK₄ hA₄ hr₄ hbx hbp hsp4 h12 h13 h14 h15
    rw [hY3s, q16] at hbx hbp hsp4
    rw [q8] at hbp hsp4
    rw [q0] at hsp4
    have hkp : Kp X.cpu.gpr Z₄.cpu.gpr := by
      refine ⟨hsp4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbx, fr _ (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact f16
      · rw [hbp, fr _ (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact f8
      · rw [h12, w12]
      · rw [h13, w13]
      · rw [h14, w14]
      · rw [h15, w15]
    have hra : rdq(Acp.Cp (Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax) X.cpu.gpr.rsi
        Z.cpu.gpr.rax (n + 1), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [fr _ hp8 (by omega) (by omega)]; exact f0
    exact ret_back c hin (lt_len (by decide)) (ret_85 _) hK₄ hA₄ hr₄ hkp hl hin₂ h₂ hra
      fun Z'' t'' hK'' hA'' hr'' hB _ => k Z V' hPk Z'' t'' hK'' hA'' hr'' hB
  -- the length loop
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => hf i (by omega)
  have hb0 : Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsi = V (Addr.add X.cpu.gpr.rsi 0) := by
    have := hV0 0 (Nat.zero_le _)
    rw [addr_add_zero] at this ⊢
    exact this
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hs1 (by rw [e16]; exact hs2) hf0 (by rw [hb0]; exact hz)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact h44 Y t₁ hKY hAY hrY (by rw [hgY] <;> rfl) (Kp.of_eq hgY (Kp.refl _))
  · refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0n hs1 (by rw [e16]; exact hs2) hf0 (by rw [hb0]; exact hnz 0 h0)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine slen c hin (W := V0 V X.cpu.gpr) (p := X.cpu.gpr.rsi) (n := n) (g₀ := gS X.cpu.gpr) hn
      (fun i hi => by rw [hV0 i (by omega)]; exact hnz i hi) (by rw [hV0 n (Nat.le_refl _)]; exact hz) hf rfl h44
      (n - 1) 0 (by omega) Y t₁ hKY hAY hrY (by rw [hgY] <;> rfl) (Kp.of_eq hgY (Kp.refl _))

end FV7z.Acc
