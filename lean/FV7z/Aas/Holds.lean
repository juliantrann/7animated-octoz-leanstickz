import FV7z.Aas.Loop
import FV7z.Acp.Holds
/-!
# `AString::operator= (const AString &)` (PLAN.md §M, M1)

7-Zip's `AString::operator= (const AString &s)` at `0x44c550` in `7zzs` (`CPP/Common/MyString.cpp`), the pieces and the
copy loop in `FV7z/Aas/Loop.lean`: at `&s == this` the run returns at once; else with `_limit` (the 4 bytes at
`this + 12`) not below `s._len` the bytes go in place into `_chars`, else through `operator new [] (s._len + 1)`
(`call` at 95 to `0x6029b0`) and `delete [] _chars` (`call` at 112 to `0x6014f0`) unless null, `_chars` = the new
buffer and `_limit` = `s._len` (117); then (38) `_len` = `s._len`, the copy of `s._chars` through the 0 (56), `rax` =
`this`, the `pop`s and the `ret` at 84.

The callees are hypotheses (`kn`, `kd`), as in `FV7z/Aac/Holds.lean`: their posts give the frame, `s._chars` and its
bytes as they were and the buffer writable and apart (`Pn`), and `P1`, `P2`.

- `Sv`: the saved `r13`, `r12`, `rbp`, `rbx` and the return address; `Bf`: the buffer of `n + 1` bytes writable and
  apart from the bytes copied and from the frame; `Pn`: the post of a callee; `W2`: the bytes after `_chars` = `p`,
  `_limit` = `v`.
- `aas_ok`: from the entry to the return with `rax` = `this`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Aas

/-- The `call`s to `operator new []` and `operator delete []`. -/
def pcn : List Byte := [0xe8, 0xfc, 0x63, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1795068] 5) := by dec_rfl
theorem wc_95 : pcn <+: aas.drop 95 := by decide +kernel
theorem call_95 (feat : Features) : Dec feat aas 95 (FV7z.mk .call 64 [.rel 1795068] 5) :=
  Dec.shift (j := 95) (k := 0) (pcn_0 feat) wc_95 (Nat.zero_le _)
def pcd : List Byte := [0xe8, 0x2b, 0x4f, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1789739] 5) := by dec_rfl
theorem wc_112 : pcd <+: aas.drop 112 := by decide +kernel
theorem call_112 (feat : Features) : Dec feat aas 112 (FV7z.mk .call 64 [.rel 1789739] 5) :=
  Dec.shift (j := 112) (k := 0) (pcd_0 feat) wc_112 (Nat.zero_le _)

/-- The `ret`. -/
theorem w_84 : Asl.pret <+: aas.drop 84 := by decide +kernel
theorem ret_84 (feat : Features) : Dec feat aas 84 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 84) (k := 0) (Asl.pret_0 feat) w_84 (Nat.zero_le _)

/-- The saved `r13`, `r12`, `rbp`, `rbx` and the return address, for the registers `g` at the entry. -/
def Sv (V : Addr → Byte) (g : Gprs) (ra : Addr) : Prop :=
  rdq(V, g.rsp - 8) = g.r13 ∧ rdq(V, g.rsp - 16) = g.r12 ∧ rdq(V, g.rsp - 24) = g.rbp ∧ rdq(V, g.rsp - 32) = g.rbx ∧
    rdq(V, g.rsp) = ra

/-- The bytes after `_chars` = `p` and `_limit` = `v` for the object at `b`. -/
abbrev W2 (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)

variable {F : Footprint} {Wl : List Rgn}

/-- The buffer `d` of `n + 1` bytes: writable, apart from the bytes `p` copied and from the frame. -/
def Bf (g : Gprs) (p : Addr) (n : Nat) (d : Addr) : Prop :=
  (∀ i, i ≤ n → Foot Wl (Addr.add d i)) ∧ d.toNat + n + 1 ≤ 2 ^ 64 ∧
    (d.toNat + n + 1 ≤ p.toNat ∨ p.toNat + n + 1 ≤ d.toNat) ∧
    (d.toNat + n + 1 ≤ g.rsp.toNat - 40 ∨ g.rsp.toNat + 8 ≤ d.toNat)

/-- The post of a callee, for the registers `g` and the bytes `V` at the entry: the frame, `s._chars` (`p`) and its
`n` bytes and the 0 as they were, the buffer `d` as `Bf`. -/
def Pn (g : Gprs) (V : Addr → Byte) (p : Addr) (n : Nat) (ra d : Addr) (V' : Addr → Byte) : Prop :=
  Sv V' g ra ∧ rdq(V', g.rsi) = p ∧ (∀ i, i ≤ n → V' (Addr.add p i) = V (Addr.add p i)) ∧ Bf (Wl := Wl) g p n d

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::operator= (const AString &s)` (`this` = `rdi`, `&s` = `rsi`) from its entry, for `s._chars` (`P`) with
`s._len` (`Ln`, `n`) bytes not 0 and a 0, apart from the object and the frame. At `&s == this` the run returns with
the bytes as after the pushes (`ks`). Else with `_limit` not below `n` the bytes go in place into `_chars` (`Bf` by
`hbi`) and the run returns (`ki`); else at `operator new []`'s entry (`kn`, `rdi` = `n + 1`), back at 100 with the
buffer `rax` (`Pn`, `P1`); with `_chars` null the run returns (`kz`); else at `operator delete []`'s entry (`kd`) and
back at 117 (`Pn`, `P2`), then the run returns (`kr`). At the return the registers a call keeps are as at the entry,
`rax` = `this`, and the bytes are `_chars`, `_limit` as stored (`W2`), `_len` = `Ln` and the bytes copied
(`Acp.Cp`). -/
theorem aas_ok {P1 P2 : State → (Addr → Byte) → Prop} {P : Addr} {Ln : BitVec 32} {n : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aas_at aas) {codeN codeD : List Byte}
    (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aas_at)
    (hp : 64 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (fs0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hqs : X.cpu.gpr.rsi.toNat + 16 ≤ 2 ^ 64)
    (hds : X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hso : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi →
      X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    (hP : rdq(V, X.cpu.gpr.rsi) = P) (hLn : rdd(V, X.cpu.gpr.rsi + 8#64) = Ln) (hn : Ln.toNat = n)
    (hnz : ∀ i < n, V (Addr.add P i) ≠ 0#8) (hz : V (Addr.add P n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add P i))
    (hpw : P.toNat + n + 1 ≤ 2 ^ 64)
    (hpf : P.toNat + n + 1 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ P.toNat)
    (hpt : P.toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ P.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (ks : X.cpu.gpr.rsi = X.cpu.gpr.rdi → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Aac.V0 V X.cpu.gpr) → Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr →
      Z'.cpu.gpr.rax = X.cpu.gpr.rdi → GoG prof L o gev gP gE Z' t')
    (hbi : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n →
      Bf (Wl := Wl) X.cpu.gpr P n rdq(V, X.cpu.gpr.rdi))
    (ki : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (Aac.V0 V X.cpu.gpr) (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4)) P
        rdq(V, X.cpu.gpr.rdi) (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kn : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (G : Gprs),
      G.rsp = X.cpu.gpr.rsp - 40 → G.rdi = BitVec.ofNat 64 (n + 1) → G.rbx = X.cpu.gpr.rbx →
      G.rbp = X.cpu.gpr.rsi → G.r12 = X.cpu.gpr.rdi → G.r13 = BitVec.setWidth 64 Ln → G.r14 = X.cpu.gpr.r14 →
      G.r15 = X.cpu.gpr.r15 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Aac.V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (aas_at.add 100) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = aas_at.add 100 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbp = X.cpu.gpr.rsi →
        Z.cpu.gpr.r12 = X.cpu.gpr.rdi → Z.cpu.gpr.r13 = BitVec.setWidth 64 Ln → Z.cpu.gpr.r14 = X.cpu.gpr.r14 →
        Z.cpu.gpr.r15 = X.cpu.gpr.r15 → Pn (Wl := Wl) X.cpu.gpr V P n (e₂.add j₂) Z.cpu.gpr.rax V' → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) = 0 → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 V' X.cpu.gpr.rdi Z.cpu.gpr.rax Ln) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE Ln 4)) P Z.cpu.gpr.rax (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kd : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) ≠ 0 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48) (toBytesLE (aas_at.add 117) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.r12), rbx := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = aas_at.add 117 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = Z.cpu.gpr.rax →
        Z₂.cpu.gpr.rbp = X.cpu.gpr.rsi → Z₂.cpu.gpr.r12 = X.cpu.gpr.rdi → Z₂.cpu.gpr.r13 = BitVec.setWidth 64 Ln →
        Z₂.cpu.gpr.r14 = X.cpu.gpr.r14 → Z₂.cpu.gpr.r15 = X.cpu.gpr.r15 →
        Pn (Wl := Wl) X.cpu.gpr V P n (e₂.add j₂) Z.cpu.gpr.rax V'' → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 V'' X.cpu.gpr.rdi Z₂.cpu.gpr.rbx Ln) (X.cpu.gpr.rdi + 8#64)
        (toBytesLE Ln 4)) P Z₂.cpu.gpr.rbx (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hLt := Ln.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have e48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have q32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have q24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have q16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have q8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have q0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have ts8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have hrip' : X.cpu.rip = aas_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hpw' : P.toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have tp : ∀ i, i ≤ n → (Addr.add P i).toNat = P.toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hpw'
  have hrd : BitVec.setWidth 64 Ln + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40 - 8) i) := by rw [e48]; exact hs6
  -- a quad word read through a store apart from it, and read back from its own store
  have pk : ∀ (W : Addr → Byte) (a x : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 → x.toNat + 8 ≤ 2 ^ 64 →
      (a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) → rdq(Vst W a (toBytesLE v 8), x) = rdq(W, x) :=
    fun W a x v ha hx h => congrArg (ofBytesLE 64)
      (Tun.rd_Vst W a (toBytesLE v 8) x 8 (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))
  have rq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 →
      rdq(Vst W a (toBytesLE v 8), a) = v := fun W a v ha => by
    rw [Tun.rd_Vst_self (n := 8) _ a _ (toBytesLE_length _ _) ha]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have mq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr) (m : Nat), a.toNat + 8 ≤ 2 ^ 64 →
      x.toNat + m ≤ 2 ^ 64 → (a.toNat + 8 ≤ x.toNat ∨ x.toNat + m ≤ a.toNat) →
      List.map (Vst W a (toBytesLE v 8)) (byteAddrs x m) = List.map W (byteAddrs x m) :=
    fun W a v x m ha hx h =>
      Tun.rd_Vst W a (toBytesLE v 8) x m (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h)
  have vq : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr), a.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat < a.toNat ∨ a.toNat + 8 ≤ x.toNat) → Vst W a (toBytesLE v 8) x = W x :=
    fun W a v x ha h =>
      Tun.Vst_out W a (toBytesLE v 8) x (by rw [toBytesLE_length]; exact ha) (by rw [toBytesLE_length]; exact h)
  -- the bytes after the four pushes, apart from them
  have m0 : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ 2 ^ 64 →
      (x.toNat + m ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x m).map (Aac.V0 V X.cpu.gpr) = (byteAddrs x m).map V := by
    intro x m hx h
    show List.map (Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8)) (byteAddrs x m) = _
    rw [e32, e24, e16,
      mq _ (X.cpu.gpr.rsp - 32) _ x m (by rw [tn32]; omega) hx (by rw [tn32]; omega),
      mq _ (X.cpu.gpr.rsp - 24) _ x m (by rw [tn24]; omega) hx (by rw [tn24]; omega),
      mq _ (X.cpu.gpr.rsp - 16) _ x m (by rw [tn16]; omega) hx (by rw [tn16]; omega),
      mq _ (X.cpu.gpr.rsp - 8) _ x m (by rw [tn8]; omega) hx (by rw [tn8]; omega)]
  have hV0 : ∀ i, i ≤ n → Aac.V0 V X.cpu.gpr (Addr.add P i) = V (Addr.add P i) := fun i hi => by
    show Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (Addr.add P i) = _
    rw [e32, e24, e16,
      vq _ (X.cpu.gpr.rsp - 32) _ (Addr.add P i) (by rw [tn32]; omega) (by rw [tn32, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 24) _ (Addr.add P i) (by rw [tn24]; omega) (by rw [tn24, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 16) _ (Addr.add P i) (by rw [tn16]; omega) (by rw [tn16, tp i hi]; omega),
      vq _ (X.cpu.gpr.rsp - 8) _ (Addr.add P i) (by rw [tn8]; omega) (by rw [tn8, tp i hi]; omega)]
  have hT0 : rdq(Aac.V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by
    rw [m0 X.cpu.gpr.rdi 8 (by omega) (by omega)]
  have hT12 : rdd(Aac.V0 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = rdd(V, X.cpu.gpr.rdi + 12#64) := by
    rw [m0 (X.cpu.gpr.rdi + 12#64) 4 (by rw [t12]; omega) (by rw [t12]; omega)]
  have hS0 : rdq(Aac.V0 V X.cpu.gpr, X.cpu.gpr.rsi) = P := by
    rw [m0 X.cpu.gpr.rsi 8 (by omega) (by omega)]; exact hP
  have hS8 : rdd(Aac.V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) = Ln := by
    rw [m0 (X.cpu.gpr.rsi + 8#64) 4 (by rw [ts8]; omega) (by rw [ts8]; omega)]; exact hLn
  -- the frame after the four pushes
  have sv0 : Sv (Aac.V0 V X.cpu.gpr) X.cpu.gpr (e₂.add j₂) := by
    refine ⟨?_, ?_, ?_, ?_, by rw [m0 X.cpu.gpr.rsp 8 hp8 (by omega)]; exact hra⟩
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 8) = _
      rw [e32, e24, e16, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 8) _ (by rw [tn32]; omega) (by rw [tn8]; omega)
          (by rw [tn32, tn8]; omega),
        pk _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 8) _ (by rw [tn24]; omega) (by rw [tn8]; omega)
          (by rw [tn24, tn8]; omega),
        pk _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rsp - 8) _ (by rw [tn16]; omega) (by rw [tn8]; omega)
          (by rw [tn16, tn8]; omega),
        rq _ (X.cpu.gpr.rsp - 8) _ (by rw [tn8]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 16) = _
      rw [e32, e24, e16, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 16) _ (by rw [tn32]; omega) (by rw [tn16]; omega)
          (by rw [tn32, tn16]; omega),
        pk _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 16) _ (by rw [tn24]; omega) (by rw [tn16]; omega)
          (by rw [tn24, tn16]; omega),
        rq _ (X.cpu.gpr.rsp - 16) _ (by rw [tn16]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 24) = _
      rw [e32, e24, pk _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rsp - 24) _ (by rw [tn32]; omega) (by rw [tn24]; omega)
          (by rw [tn32, tn24]; omega),
        rq _ (X.cpu.gpr.rsp - 24) _ (by rw [tn24]; omega)]
    · show rdq(Vst (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 32) = _
      rw [e32, rq _ (X.cpu.gpr.rsp - 32) _ (by rw [tn32]; omega)]
  -- the bytes after `_chars` and `_limit`, apart from the object
  have m2 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (W2 W X.cpu.gpr.rdi p v) = (byteAddrs x 8).map W := by
    intro W p v x hx h
    have a1 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) x 8
      (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega)
    have a2 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    exact a1.trans a2
  have b2 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (i : Nat), i ≤ n →
      W2 W X.cpu.gpr.rdi p v (Addr.add P i) = W (Addr.add P i) := fun W p v i hi => by
    show Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) (Addr.add P i) = _
    rw [Tun.Vst_out _ (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) (Addr.add P i)
        (by rw [toBytesLE_length, t12]; omega)
        (by rw [toBytesLE_length, t12, tp i hi]; omega),
      vq _ X.cpu.gpr.rdi _ (Addr.add P i) (by omega) (by rw [tp i hi]; omega)]
  -- from 71: `add rsp, 8; mov rax, r12`, the `pop`s and the `ret`
  have ep : ∀ (U : State) (M : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
      U.cpu.rip = aas_at.add 71 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.r12 = X.cpu.gpr.rdi →
      U.cpu.gpr.r14 = X.cpu.gpr.r14 → U.cpu.gpr.r15 = X.cpu.gpr.r15 → Sv M X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem M → Z'.cpu.rip = e₂.add j₂ →
        Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi → GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U M t' hKU hAU hrU hus hu12 hu14 hu15 hSv k
    obtain ⟨f13, f12, fbp, fbx, fra⟩ := hSv
    refine (c_71 prof).run c hin _ hKU hAU hrU
      (vc_71 (by rw [hus, q32]; exact fun i hi => c.hws _ (hs4 i hi))
        (by rw [hus, q32, q24]; exact fun i hi => c.hws _ (hs3 i hi))
        (by rw [hus, q32, q24, q16]; exact fun i hi => c.hws _ (hs2 i hi))
        (by rw [hus, q32, q24, q16, q8]; exact fun i hi => c.hws _ (hs1 i hi))) ?_
    rintro j' g fl V₁ ⟨rfl, hbx, hbp, h12, h13, hsp, hax, h14, h15, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    rw [hus, q32] at hbx hbp h12 h13 hsp
    rw [q24] at hbp h12 h13 hsp
    rw [q16] at h12 h13 hsp
    rw [q8] at h13 hsp
    rw [q0] at hsp
    have hkp : Kp X.cpu.gpr Y.cpu.gpr := by
      refine ⟨by rw [hgY]; exact hsp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hgY, hbx]; exact fbx
      · rw [hgY, hbp]; exact fbp
      · rw [hgY, h12]; exact f12
      · rw [hgY, h13]; exact f13
      · rw [hgY, h14, hu14]
      · rw [hgY, h15, hu15]
    exact ret_back c hin (lt_len (by decide)) (ret_84 _) hKY hAY hrY hkp hl hin₂ h₂ fra
      fun Z'' t'' hK'' hA'' hr'' hB hax'' => k Z'' t'' hK'' hA'' hr'' hB (by rw [hax'', hgY, hax, hu12])
  -- from 38 (`&s != this`): `_len` = `Ln`, the copy loop, on from 71
  have fin : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → ∀ (U : State) (M : Addr → Byte) (d : Addr) (t' : Nat),
      KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
      U.cpu.rip = aas_at.add 38 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.rbx = d →
      U.cpu.gpr.rbp = X.cpu.gpr.rsi → U.cpu.gpr.r12 = X.cpu.gpr.rdi → U.cpu.gpr.r13 = BitVec.setWidth 64 Ln →
      U.cpu.gpr.r14 = X.cpu.gpr.r14 → U.cpu.gpr.r15 = X.cpu.gpr.r15 → Sv M X.cpu.gpr (e₂.add j₂) →
      rdq(M, X.cpu.gpr.rsi) = P → (∀ i, i ≤ n → M (Addr.add P i) = V (Addr.add P i)) →
      Bf (Wl := Wl) X.cpu.gpr P n d →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Acp.Cp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4)) P d (n + 1)) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro hne U M d t' hKU hAU hrU hus hubx hubp hu12 hu13 hu14 hu15 hSv hMS hstr hbf k
    have hso' := hso hne
    obtain ⟨f13, f12, fbp, fbx, fra⟩ := hSv
    obtain ⟨hwd, hdw, hdp, hdf⟩ := hbf
    refine (c_38 prof).run c hin _ hKU hAU hrU (vc_38 (by rw [hu12]; exact fw8) (by rw [hubp]; exact fs0)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    rw [hu12, hu13, sw_64_32] at hAY
    have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact hus
    have hYbx : Y.cpu.gpr.rbx = d := by rw [hgY]; exact hubx
    have hY12 : Y.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgY]; exact hu12
    have hY14 : Y.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hgY]; exact hu14
    have hY15 : Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgY]; exact hu15
    have hYdx : Y.cpu.gpr.rdx = BitVec.ofNat 64 0 := by rw [hgY] <;> rfl
    have hYax : Y.cpu.gpr.rax = P := by
      rw [hgY]
      show rdq(Vst M (U.cpu.gpr.r12 + 8#64) (toBytesLE (BitVec.setWidth 32 U.cpu.gpr.r13) 4), U.cpu.gpr.rbp) = P
      rw [hu12, hu13, hubp, sw_64_32]
      exact (congrArg (ofBytesLE 64) (Tun.rd_Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4) X.cpu.gpr.rsi 8
        (by rw [toBytesLE_length, t8]; omega) (by omega) (by rw [toBytesLE_length, t8]; omega))).trans hMS
    have hdw' : d.toNat + (n + 1) ≤ 2 ^ 64 := by omega
    have td : ∀ i, i ≤ n → (Addr.add d i).toNat = d.toNat + i := fun i hi => toNat_add_of_fits (by omega) hdw'
    have hW8 : ∀ i, i ≤ n → Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4) (Addr.add P i) = V (Addr.add P i) :=
        fun i hi => by
      rw [Tun.Vst_out M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4) (Addr.add P i)
        (by rw [toBytesLE_length, t8]; omega) (by rw [toBytesLE_length, t8, tp i hi]; omega), hstr i hi]
    have fr : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat →
        a.toNat ≤ X.cpu.gpr.rsp.toNat →
        rdq(Acp.Cp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4)) P d (n + 1), a) = rdq(M, a) := fun a ha h1 h2 => by
      rw [Acp.rdCp (Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4)) P d (n + 1) a ha hdw' (by omega)]
      exact congrArg (ofBytesLE 64) (Tun.rd_Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4) a 8
        (by rw [toBytesLE_length, t8]; omega) ha (by rw [toBytesLE_length, t8]; omega))
    refine loop c hin (W := Vst M (X.cpu.gpr.rdi + 8#64) (toBytesLE Ln 4)) (p := P) (d := d) (n := n)
      (g₀ := Y.cpu.gpr) (fun i hi => by rw [hW8 i (by omega)]; exact hnz i hi)
      (by rw [hW8 n (Nat.le_refl _)]; exact hz) hf hwd
      (fun i hi j hj e => by
        have := congrArg BitVec.toNat e
        rw [tp i hi, td j hj] at this
        omega) hYbx ?_ n 0 (by omega) Y t₁ hKY hAY hrY hYdx hYax (Kp.refl _)
    intro Z t₂ hKZ hAZ hrZ hkp
    obtain ⟨zsp, -, -, z12, -, z14, z15⟩ := hkp
    exact ep Z _ t₂ hKZ hAZ hrZ (by rw [zsp, hYs]) (by rw [z12, hY12]) (by rw [z14, hY14]) (by rw [z15, hY15])
      ⟨by rw [fr (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact f13,
        by rw [fr (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact f12,
        by rw [fr (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact fbp,
        by rw [fr (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega) (by rw [tn32]; omega)]; exact fbx,
        by rw [fr X.cpu.gpr.rsp hp8 (by omega) (by omega)]; exact fra⟩ k
  by_cases hne : X.cpu.gpr.rsi = X.cpu.gpr.rdi
  · -- `&s == this`
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0s hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) hne) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact ep Y _ t₁ hKY hAY hrY (by rw [hgY]; exact e40) (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl)
      (by rw [hgY] <;> rfl) sv0 (ks hne)
  have hso' := hso hne
  by_cases hc : rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n
  · -- `_limit` below `s._len`: `operator new []`, then `delete [] _chars` unless null, the stores at 117
    have hL : (rdd(V, X.cpu.gpr.rdi + 12#64)).toNat < Ln.toNat := by rw [hn]; exact hc
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0b hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) hne fs8
        (fun i hi => c.hws _ (fw12 i hi)) hS8 hT12 hL) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₂ t₃ hK₂ hA₂ hr₂ hg₂ -
    have hs2' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₂]; exact e40
    refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_95 _) hinN hN (by decide) (by rw [hs2']; exact hst) ?_
    rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [hs2', e48] at hA₃
    have hg₃' : Y₃.cpu.gpr = Y₂.cpu.gpr.set 4 (X.cpu.gpr.rsp - 48) := by rw [hg₃, hs2', e48]
    refine kn hne hc Y₂.cpu.gpr hs2' (by rw [hg₂]; exact hrd) (by rw [hg₂] <;> rfl) (by rw [hg₂] <;> rfl)
      (by rw [hg₂] <;> rfl) (by rw [hg₂] <;> rfl) (by rw [hg₂] <;> rfl) (by rw [hg₂] <;> rfl) Y₃ t₄ hK₃ hA₃ hr₃
      hg₃' ?_
    -- back from `operator new []`
    intro Z V' t₅ hKZ hAZ hrZ hzs hzp hz12 hz13 hz14 hz15 hPn hP1
    -- at 117 with the bytes `M`: the stores of `_chars` and `_limit`, then on from 38
    have h117 : ∀ (U : State) (M : Addr → Byte) (t₇ : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
        U.cpu.rip = aas_at.add 117 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.rbx = Z.cpu.gpr.rax →
        U.cpu.gpr.rbp = X.cpu.gpr.rsi → U.cpu.gpr.r12 = X.cpu.gpr.rdi → U.cpu.gpr.r13 = BitVec.setWidth 64 Ln →
        U.cpu.gpr.r14 = X.cpu.gpr.r14 → U.cpu.gpr.r15 = X.cpu.gpr.r15 →
        Pn (Wl := Wl) X.cpu.gpr V P n (e₂.add j₂) Z.cpu.gpr.rax M →
        (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
          Agree F Z'.proc.mm.mem (Acp.Cp (Vst (W2 M X.cpu.gpr.rdi Z.cpu.gpr.rax Ln) (X.cpu.gpr.rdi + 8#64)
            (toBytesLE Ln 4)) P Z.cpu.gpr.rax (n + 1)) →
          Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
          GoG prof L o gev gP gE Z' t'') →
        GoG prof L o gev gP gE U t₇ := by
      intro U M t₇ hKU hAU hrU hus hubx hubp hu12 hu13 hu14 hu15 hPnU kU
      obtain ⟨⟨f13, f12, fbp, fbx, fra⟩, hMS, hstrU, hbfU⟩ := hPnU
      refine (c_117 prof).run c hin _ hKU hAU hrU (vc_117 (by rw [hu12]; exact fw0) (by rw [hu12]; exact fw12)) ?_
      rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ U' t₈ hKU' hAU' hrU' hgU' -
      rw [hu12, hubx, hu13, sw_64_32] at hAU'
      refine fin hne U' (W2 M X.cpu.gpr.rdi Z.cpu.gpr.rax Ln) Z.cpu.gpr.rax t₈ hKU' hAU' hrU'
        (by rw [hgU']; exact hus) (by rw [hgU']; exact hubx) (by rw [hgU']; exact hubp) (by rw [hgU']; exact hu12)
        (by rw [hgU']; exact hu13) (by rw [hgU']; exact hu14) (by rw [hgU']; exact hu15) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
        (fun i hi => by rw [b2 M _ _ i hi]; exact hstrU i hi) hbfU kU
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact f13
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact f12
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact fbp
      · rw [m2 _ _ _ (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega)]; exact fbx
      · rw [m2 _ _ _ X.cpu.gpr.rsp hp8 (by omega)]; exact fra
      · rw [m2 _ _ _ X.cpu.gpr.rsi (by omega) (by omega)]; exact hMS
    refine (c_100 prof).run c hin (fun j' g' _ V'' =>
        g' = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.r12), rbx := Z.cpu.gpr.rax } ∧ V'' = V' ∧
        ((j' = 117 ∧ rdq(V', X.cpu.gpr.rdi) = 0) ∨ (j' = 112 ∧ rdq(V', X.cpu.gpr.rdi) ≠ 0))) hKZ hAZ hrZ
      (vc_100 (by rw [hz12]; exact fun i hi => c.hws _ (fw0 i hi))
        (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, by rw [← hz12]; exact h0⟩⟩)
        (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, by rw [← hz12]; exact h0⟩⟩)) ?_
    rintro j' g fl V₃ ⟨rfl, hV₃, h⟩ Y₄ t₆ hK₄ hA₄ hr₄ hg₄ -
    subst V₃
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- `_chars` null
      exact h117 Y₄ V' t₆ hK₄ hA₄ hr₄ (by rw [hg₄]; exact hzs) (by rw [hg₄] <;> rfl) (by rw [hg₄]; exact hzp)
        (by rw [hg₄]; exact hz12) (by rw [hg₄]; exact hz13) (by rw [hg₄]; exact hz14) (by rw [hg₄]; exact hz15) hPn
        (kz Z V' hP1 h0)
    · -- `operator delete [] (_chars)`
      have hs4' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₄]; exact hzs
      refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_112 _) hinD hD (by decide)
        (by rw [hs4']; exact hst) ?_
      rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hs4', e48] at hA₅
      have hg₅' : Y₅.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.r12), rbx := Z.cpu.gpr.rax }.set 4
          (X.cpu.gpr.rsp - 48) := by
        rw [hg₅, hs4', e48, hg₄]
      refine kd Z V' hP1 h0 Y₅ t₇ hK₅ hA₅ hr₅ hg₅' ?_
      intro Z₂ V'' t₈ hK₆ hA₆ hr₆ h2s h2b h2p h212 h213 h214 h215 hPn₂ hP2
      exact h117 Z₂ V'' t₈ hK₆ hA₆ hr₆ h2s h2b h2p h212 h213 h214 h215 hPn₂
        fun Z' t'' hK' hA' hr' hB hax => kr Z₂ V'' hP2 Z' t'' hK' (by rw [h2b]; exact hA') hr' hB hax
  · -- in place
    have hL : ¬ (rdd(V, X.cpu.gpr.rdi + 12#64)).toNat < Ln.toNat := by rw [hn]; exact hc
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0c hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) hne fs8
        (fun i hi => c.hws _ (fw12 i hi)) (fun i hi => c.hws _ (fw0 i hi)) hS8 hT12 hT0 hL) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact fin hne Y _ rdq(V, X.cpu.gpr.rdi) t₁ hKY hAY hrY (by rw [hgY]; exact e40) (by rw [hgY] <;> rfl)
      (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl)
      sv0 hS0 hV0 (hbi hne hc) (ki hne hc)

end FV7z.Aas
