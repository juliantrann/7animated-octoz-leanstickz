import FV7z.Acp.Loop
import FV7z.Acs.Holds
/-!
# `AString::AString (const AString &)` (PLAN.md §M, M1)

7-Zip's `AString (const AString &s)` at `0x44c420` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi` and
`&s` in `rsi`, `push rbp; mov rbp, rsi; push rbx; mov rbx, rdi; sub rsp, 8; mov esi, [rsi + 8]`, then
`SetStartLen (s._len)` (`call` at 19 to `Asl.asl_at`, proved in `FV7z/Asl/Holds.lean`), then `mov rsi, [rbp];
mov rcx, [rbx]; xor eax, eax` and the copy loop at 40 (`FV7z/Acp/Loop.lean`) through the 0, the `pop`s and the `ret`
at 61.

`SetStartLen` is run by `Asl.asl_ok`; its own callee (`operator new`) is a hypothesis (`kf`) in the form `asl_ok`
takes, whose post is `Pk`: the frame (the saved `rbx`, `rbp`, the return address) and `r12` … `r15` as they were,
`s._chars` and the `n + 1` bytes of the string as they were, the new buffer (`rax`) writable, apart from the string
and from the frame, and `P1`.

- `gS`, `V0`: the registers and the bytes at the `call` of `SetStartLen`; `gY`, `VY`: at its entry.
- `Pk`: the post of `operator new` in `SetStartLen`.
- `rdV1`, `byV1`, `rdCp`: reads through what `SetStartLen` stores and through the copy.
- `vc_0`, `vc_24`: the verification conditions of the pieces before the loop.
- `acp_ok`: from the entry, through `SetStartLen` and the loop, to the return.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Acp

/-- The `call` of `SetStartLen`. -/
def pcs : List Byte := [0xe8, 0x28, 0xfc, 0xff, 0xff]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 18446744073709550632] 5) := by dec_rfl
theorem wc_19 : pcs <+: acp.drop 19 := by decide +kernel
theorem call_19 (feat : Features) : Dec feat acp 19 (FV7z.mk .call 64 [.rel 18446744073709550632] 5) :=
  Dec.shift (j := 19) (k := 0) (pcs_0 feat) wc_19 (Nat.zero_le _)

/-- The `ret`. -/
theorem w_61 : Asl.pret <+: acp.drop 61 := by decide +kernel
theorem ret_61 (feat : Features) : Dec feat acp 61 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 61) (k := 0) (Asl.pret_0 feat) w_61 (Nat.zero_le _)

/-- The registers at the `call` of `SetStartLen`: `rbp` = `&s`, `rbx` = `this`, `esi` = `v` (`s._len`), two pushed
and 8 more. -/
abbrev gS (g : Gprs) (v : BitVec 32) : Gprs :=
  { g with rbp := g.rsi, rbx := g.rdi, rsi := v.setWidth 64, rsp := g.rsp - 8 - 8 - 8 }

/-- The bytes at the `call` of `SetStartLen`: `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at `SetStartLen`'s entry. -/
abbrev gY (g : Gprs) (v : BitVec 32) : Gprs := (gS g v).set 4 (g.rsp - 32)
/-- The bytes at `SetStartLen`'s entry: the return address `acp_at + 24` pushed. -/
abbrev VY (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 32) (toBytesLE (acp_at.add 24) 8)

variable {F : Footprint} {Wl : List Rgn}

/-- The post of `operator new` in `SetStartLen`, for the registers `g` and the bytes `V` at the entry, the string of
`n` bytes not 0 and a 0 at `s._chars`, the return address `ra`: the frame and `r12` … `r15` as they were, `s._chars`
and the string as they were, the buffer `rax` writable, apart from the string and from the frame, and `P1`. -/
def Pk (g : Gprs) (V : Addr → Byte) (n : Nat) (ra : Addr) (P1 : State → (Addr → Byte) → Prop) (Z : State)
    (V' : Addr → Byte) : Prop :=
  rdq(V', g.rsp - 16) = g.rbx ∧ rdq(V', g.rsp - 8) = g.rbp ∧ rdq(V', g.rsp) = ra ∧
    Z.cpu.gpr.r12 = g.r12 ∧ Z.cpu.gpr.r13 = g.r13 ∧ Z.cpu.gpr.r14 = g.r14 ∧ Z.cpu.gpr.r15 = g.r15 ∧
    rdq(V', g.rsi) = rdq(V, g.rsi) ∧ (∀ i, i ≤ n → V' ((rdq(V, g.rsi)).add i) = V ((rdq(V, g.rsi)).add i)) ∧
    (∀ i, i ≤ n → Foot Wl (Z.cpu.gpr.rax.add i)) ∧ Z.cpu.gpr.rax.toNat + n + 1 ≤ 2 ^ 64 ∧
    (Z.cpu.gpr.rax.toNat + n + 1 ≤ (rdq(V, g.rsi)).toNat ∨
      (rdq(V, g.rsi)).toNat + n + 1 ≤ Z.cpu.gpr.rax.toNat) ∧
    (Z.cpu.gpr.rax.toNat + n + 1 ≤ g.rsp.toNat - 16 ∨ g.rsp.toNat + 8 ≤ Z.cpu.gpr.rax.toNat) ∧ P1 Z V'

/-- 8 bytes apart from the object at `b`: as before `SetStartLen` stored it. -/
theorem rdV1 (V : Addr → Byte) (b : Addr) (v : BitVec 32) (p : BitVec 64) (x : Addr) (hb : b.toNat + 16 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : x.toNat + 8 ≤ b.toNat ∨ b.toNat + 16 ≤ x.toNat) :
    rdq(Asl.V1 V b v p, x) = rdq(V, x) := by
  have t8 : (b + 8#64).toNat = b.toNat + 8 := by rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (b + 12#64).toNat = b.toNat + 12 := by rw [BitVec.toNat_add]; simp <;> omega
  show ofBytesLE 64 (List.map (Vst (Vst (Vst V (b + 8#64) (toBytesLE v 4)) (b + 12#64) (toBytesLE v 4)) b
    (toBytesLE p 8)) (byteAddrs x 8)) = _
  rw [Tun.rd_Vst (Vst (Vst V (b + 8#64) (toBytesLE v 4)) (b + 12#64) (toBytesLE v 4)) b (toBytesLE p 8) x 8
      (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst (Vst V (b + 8#64) (toBytesLE v 4)) (b + 12#64) (toBytesLE v 4) x 8
      (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega),
    Tun.rd_Vst V (b + 8#64) (toBytesLE v 4) x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)]

/-- A byte apart from the object at `b`: as before `SetStartLen` stored it. -/
theorem byV1 (V : Addr → Byte) (b : Addr) (v : BitVec 32) (p : BitVec 64) (x : Addr) (hb : b.toNat + 16 ≤ 2 ^ 64)
    (h : x.toNat < b.toNat ∨ b.toNat + 16 ≤ x.toNat) : Asl.V1 V b v p x = V x := by
  have t8 : (b + 8#64).toNat = b.toNat + 8 := by rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (b + 12#64).toNat = b.toNat + 12 := by rw [BitVec.toNat_add]; simp <;> omega
  show Vst (Vst (Vst V (b + 8#64) (toBytesLE v 4)) (b + 12#64) (toBytesLE v 4)) b (toBytesLE p 8) x = V x
  rw [Tun.Vst_out _ b _ x (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ (b + 12#64) _ x (by rw [toBytesLE_length, t12]; omega) (by rw [toBytesLE_length, t12]; omega),
    Tun.Vst_out _ (b + 8#64) _ x (by rw [toBytesLE_length, t8]; omega) (by rw [toBytesLE_length, t8]; omega)]

/-- 8 bytes apart from the `k` copied to `d`: as before the copy. -/
theorem rdCp (W : Addr → Byte) (p d : Addr) (k : Nat) (a : Addr) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hd : d.toNat + k ≤ 2 ^ 64) (h : d.toNat + k ≤ a.toNat ∨ a.toNat + 8 ≤ d.toNat) :
    rdq(Cp W p d k, a) = rdq(W, a) := by
  show ofBytesLE 64 (List.map (Cp W p d k) (byteAddrs a 8)) = ofBytesLE 64 (List.map W (byteAddrs a 8))
  rw [rd_far W p d (k := k) (a := a) (m := 8) fun b hb i hi e => by
    have := congrArg BitVec.toNat e
    rw [toNat_add_of_fits hb ha, toNat_add_of_fits hi hd] at this
    omega]

/-- `push rbp; mov rbp, rsi; push rbx; mov rbx, rdi; sub rsp, 8; mov esi, [rsi + 8]`, to the `call` at 19. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 19 ∧ g' = gS g rdd(V0 V g, g.rsi + 8#64) ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 f8 ⊢
  wpx [W_0, o0, gS, V0]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `SetStartLen`: `mov rsi, [rbp]; mov rcx, [rbx]; xor eax, eax`, to the loop at 40. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (f1 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) :
    W_24 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = { g with rsi := rdq(V, g.rbp), rcx := rdq(V, g.rbx), rax := 0#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 ⊢
  wpx [W_24, o1, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString (const AString &s)` (`this` = `rdi`, `&s` = `rsi`) from its entry, for `s._chars` (`rdq(V, rsi)`) with
`n` bytes not 0 and a 0. `SetStartLen (s._len)` runs with the registers `gY` and the bytes `VY` at its entry; its
callee is `kf`, in the form `Asl.asl_ok` takes, with the post `Pk`. Back at 24, the loop copies the `n + 1` bytes to
the new buffer (the callee's `rax`), and the run returns with the registers a call keeps as at the entry, the bytes
`_chars`, `_len`, `_limit` as `SetStartLen` stores them (`Asl.V1`) and the string copied (`Cp`) (`k`). -/
theorem acp_ok {P1 : State → (Addr → Byte) → Prop} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L acp_at acp) (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acp_at)
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
    (fs0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hsq : X.cpu.gpr.rsi.toNat + 12 ≤ 2 ^ 64)
    (hsf : X.cpu.gpr.rsi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    (hst : X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    (hn : n < 2 ^ 63) (hnz : ∀ i < n, V ((rdq(V, X.cpu.gpr.rsi)).add i) ≠ 0)
    (hz : V ((rdq(V, X.cpu.gpr.rsi)).add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data ((rdq(V, X.cpu.gpr.rsi)).add i))
    (hpw : (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ 2 ^ 64)
    (hpt : (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + 16 ≤ (rdq(V, X.cpu.gpr.rsi)).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V0 (VY V X.cpu.gpr) (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)))
          ((gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp - 32) (toBytesLE (Asl.asl_at.add 34) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 →
      Y.cpu.gpr = (Asl.gC (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64))).set 4
        ((gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Asl.asl_at.add 34 → Z.cpu.gpr.rsp = (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp - 24 →
        Z.cpu.gpr.rbx = (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rdi →
        Z.cpu.gpr.rbp = Asl.zl (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)) →
        rdq(V', (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp - 16) =
          (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rbx →
        rdq(V', (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp - 8) =
          (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rbp →
        rdq(V', (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp) = acp_at.add 24 →
        Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k : ∀ (Z : State) (V' : Addr → Byte), Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1 Z V' →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Cp (Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax) (rdq(V, X.cpu.gpr.rsi))
          Z.cpu.gpr.rax (n + 1)) →
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
  have ts8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by rw [BitVec.toNat_add]; simp <;> omega
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
  have hrip' : X.cpu.rip = acp_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- `s._len`, read after the two pushes
  have hln : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) = rdd(V, X.cpu.gpr.rsi + 8#64) := by
    show ofBytesLE 32 (List.map (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8)) (byteAddrs (X.cpu.gpr.rsi + 8#64) 4)) = _
    rw [e16, Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsi + 8#64) 4 (by rw [toBytesLE_length, tn16]; omega)
        (by rw [ts8]; omega) (by rw [toBytesLE_length, tn16, ts8]; omega),
      Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rsi + 8#64) 4
        (by rw [toBytesLE_length, tn8]; omega) (by rw [ts8]; omega) (by rw [toBytesLE_length, tn8, ts8]; omega)]
  -- to the `call` of `SetStartLen`
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 19 ∧ g' = gS X.cpu.gpr rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) ∧ V' = V0 V X.cpu.gpr)
    hK hA hrip' (vc_0 hs1 (by rw [e16]; exact hs2) fs8) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24 - 8) i) := by rw [e32]; exact hs4
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_19 _) hinS (by decide) (by decide)
    (by rw [hsY]; exact hst4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e32] at hA₂
  have hg2 : Y₂.cpu.gpr = gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64) := by rw [hg₂, hsY, e32, hgY, hln]
  have hY2s : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hg2]; rfl
  have hrdi : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg2]; rfl
  have hrbx : Y₂.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg2]; rfl
  have hrbp : Y₂.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hg2]; rfl
  have hrsi : BitVec.setWidth 32 Y₂.cpu.gpr.rsi = rdd(V, X.cpu.gpr.rsi + 8#64) := by rw [hg2]; exact sw_64_32 _
  -- `SetStartLen`
  refine Asl.asl_ok (Pc := Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) P1) c hinS hinW hK₂ hA₂ hr₂
    (by rw [hY2s, tn32]; omega) (by rw [hY2s, tn32]; omega)
    (by rw [hY2s, e40]; exact hs5) (by rw [hY2s, e48]; exact hs6) (by rw [hY2s, e64]; exact hs8)
    (by rw [hY2s]; exact fun i hi => c.hws _ (hs4 i hi))
    (by rw [hrdi]; exact fw0) (by rw [hrdi]; exact fw8) (by rw [hrdi]; exact fw12) (by rw [hrdi]; exact hq)
    (by rw [hrdi, hY2s, tn32]; omega) (e₂ := acp_at) hin (j₂ := 24) (by decide)
    (by rw [hg2]; exact kf) ?_
  -- back from `SetStartLen`, to the loop
  rintro Z V' Z' t₃ hPk hKZ' hAZ' hrZ' hgZ'
  rw [hrdi, hrsi] at hAZ'
  have hPk0 := hPk
  obtain ⟨f16, f8, f0, k12, k13, k14, k15, hsrc, hstr, hwd, hdw, hdp, hdf, -⟩ := hPk0
  have hZ'rbx : Z'.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgZ']; exact hrbx
  have hZ'rbp : Z'.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hgZ']; exact hrbp
  have hZ's : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgZ', hg2]; exact q24
  refine (c_24 prof).run c hin _ hKZ' hAZ' hrZ'
    (vc_24 (by rw [hZ'rbp]; exact fs0) (by rw [hZ'rbx]; exact fun i hi => c.hws _ (fw0 i hi))) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hsrc' : rdq(Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax, X.cpu.gpr.rsi) =
      rdq(V, X.cpu.gpr.rsi) := by
    rw [rdV1 V' X.cpu.gpr.rdi _ _ X.cpu.gpr.rsi hq (by omega) hst]; exact hsrc
  have hdst : rdq(Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax, X.cpu.gpr.rdi) =
      Z.cpu.gpr.rax := Acs.rd1 _ _ _ _ (by omega)
  have hsi : Y₃.cpu.gpr.rsi = rdq(V, X.cpu.gpr.rsi) := by
    rw [hg₃]
    show rdq(Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax, Z'.cpu.gpr.rbp) = _
    rw [hZ'rbp]; exact hsrc'
  have hci : Y₃.cpu.gpr.rcx = Z.cpu.gpr.rax := by
    rw [hg₃]
    show rdq(Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax, Z'.cpu.gpr.rbx) = _
    rw [hZ'rbx]; exact hdst
  have hax : Y₃.cpu.gpr.rax = BitVec.ofNat 64 0 := by rw [hg₃] <;> rfl
  have hY3s : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact hZ's
  have y12 : Y₃.cpu.gpr.r12 = X.cpu.gpr.r12 := by rw [hg₃, hgZ']; exact k12
  have y13 : Y₃.cpu.gpr.r13 = X.cpu.gpr.r13 := by rw [hg₃, hgZ']; exact k13
  have y14 : Y₃.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg₃, hgZ']; exact k14
  have y15 : Y₃.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg₃, hgZ']; exact k15
  have hpw' : (rdq(V, X.cpu.gpr.rsi)).toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have hdw' : Z.cpu.gpr.rax.toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have tp : ∀ i, i ≤ n → ((rdq(V, X.cpu.gpr.rsi)).add i).toNat = (rdq(V, X.cpu.gpr.rsi)).toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hpw'
  have td : ∀ i, i ≤ n → (Z.cpu.gpr.rax.add i).toNat = Z.cpu.gpr.rax.toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hdw'
  have hWp : ∀ i, i ≤ n → Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax
      ((rdq(V, X.cpu.gpr.rsi)).add i) = V ((rdq(V, X.cpu.gpr.rsi)).add i) := fun i hi => by
    rw [byV1 _ _ _ _ _ hq (by rw [tp i hi]; omega), hstr i hi]
  have fr : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat →
      a.toNat ≤ X.cpu.gpr.rsp.toNat →
      rdq(Cp (Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax) (rdq(V, X.cpu.gpr.rsi))
        Z.cpu.gpr.rax (n + 1), a) = rdq(V', a) := fun a ha h1 h2 => by
    rw [rdCp _ _ _ _ a ha hdw' (by omega), rdV1 V' X.cpu.gpr.rdi _ _ a hq ha (by omega)]
  -- the loop, the `pop`s and the `ret`
  refine loop c hin (W := Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax)
    (p := rdq(V, X.cpu.gpr.rsi)) (d := Z.cpu.gpr.rax) (n := n) (g₀ := Y₃.cpu.gpr) hn
    (fun i hi => by rw [hWp i (by omega)]; exact hnz i hi) (by rw [hWp n (Nat.le_refl _)]; exact hz) hf hwd
    (fun i hi j hj e => by
      have := congrArg BitVec.toNat e
      rw [tp i hi, td j hj] at this
      omega)
    (by rw [hY3s, q16]; exact fun i hi => c.hws _ (hs2 i hi))
    (by rw [hY3s, q16, q8]; exact fun i hi => c.hws _ (hs1 i hi)) ?_ n 0 (by omega) Y₃ t₄ hK₃ hA₃ hr₃
    hax hsi hci (Kp.refl _)
  intro Z₄ t₅ hK₄ hA₄ hr₄ hbx hbp hsp4 h12 h13 h14 h15
  rw [hY3s, q16] at hbx hbp hsp4
  rw [q8] at hbp hsp4
  rw [q0] at hsp4
  have hkp : Kp X.cpu.gpr Z₄.cpu.gpr := by
    refine ⟨hsp4, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbx, fr _ (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact f16
    · rw [hbp, fr _ (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact f8
    · rw [h12, y12]
    · rw [h13, y13]
    · rw [h14, y14]
    · rw [h15, y15]
  have hra : rdq(Cp (Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax) (rdq(V, X.cpu.gpr.rsi))
      Z.cpu.gpr.rax (n + 1), X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [fr _ hp8 (by omega) (by omega)]; exact f0
  exact ret_back c hin (lt_len (by decide)) (ret_61 _) hK₄ hA₄ hr₄ hkp hl hin₂ h₂ hra
    fun Z'' t'' hK'' hA'' hr'' hB _ => k Z V' hPk Z'' t'' hK'' hA'' hr'' hB

end FV7z.Acp
