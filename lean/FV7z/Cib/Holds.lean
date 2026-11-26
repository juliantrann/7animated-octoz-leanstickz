import FV7z.Cib.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NCompress::NLzma::CDecoder::CreateInputBuffer` (PLAN.md §M, M1)

7-Zip 26.06's `CDecoder::CreateInputBuffer ()` at `0x57fcc0` in `7zzs` (`CPP/7zip/Compress/LzmaDecoder.cpp`): with
`this` in `rdi`, if `_inBuf` (the 8 bytes at `this + 96`) is not null and `_inBufSize` (the 4 bytes at `this + 80`) is
`_inBufSizeAllocated` (the 4 bytes at `this + 76`) (`cOk`), `S_OK` (0; the `ret` at 65); else `MyFree (_inBuf)`
(`call` at 27 to `0x41f3f0`), `_inBufSizeAllocated = 0`, `_inBuf = MyAlloc (_inBufSize)` (`call` at 42 to
`0x41f3c0`); a null result gives `E_OUTOFMEMORY` (`0x8007000e`; the `ret` at 72), else `_inBufSizeAllocated =
_inBufSize` and `S_OK` (65). `push rbx`, `rbx` = `this` across the calls, `pop rbx; ret`.

The callees are hypotheses (`kf`, `ka`), as in `FV7z/Vcl/Holds.lean`.

- `cOk`: no new buffer; `gF`: the registers at the first `call` (`rax`, `rdx` as the way there left them); `g64`:
  at 64 with no new buffer.
- `vc_0`, `vc_32`, `vc_47`, `vc_64`: the verification conditions of the pieces.
- `cib_ok`: from the entry to the return address (`kn`), or through the callees (`kf`, `ka`, then `kz` or `ks`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cib

/-- The `call`s to `MyFree` and `MyAlloc`. -/
def pcf : List Byte := [0xe8, 0x10, 0xf7, 0xe9, 0xff]
theorem pcf_0 : ∀ feat, Dec feat pcf 0 (FV7z.mk .call 64 [.rel 18446744073708107536] 5) := by dec_rfl
theorem wc_27 : pcf <+: cib.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat cib 27 (FV7z.mk .call 64 [.rel 18446744073708107536] 5) :=
  Dec.shift (j := 27) (k := 0) (pcf_0 feat) wc_27 (Nat.zero_le _)
def pca : List Byte := [0xe8, 0xd1, 0xf6, 0xe9, 0xff]
theorem pca_0 : ∀ feat, Dec feat pca 0 (FV7z.mk .call 64 [.rel 18446744073708107473] 5) := by dec_rfl
theorem wc_42 : pca <+: cib.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat cib 42 (FV7z.mk .call 64 [.rel 18446744073708107473] 5) :=
  Dec.shift (j := 42) (k := 0) (pca_0 feat) wc_42 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_65 : pret <+: cib.drop 65 := by decide +kernel
theorem ret_65 (feat : Features) : Dec feat cib 65 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 65) (k := 0) (pret_0 feat) w_65 (Nat.zero_le _)
theorem w_72 : pret <+: cib.drop 72 := by decide +kernel
theorem ret_72 (feat : Features) : Dec feat cib 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)

/-- A buffer, and of the size wanted. -/
abbrev cOk (V : Addr → Byte) (p : Addr) : Prop :=
  rdq(V, p + 96#64) ≠ 0 ∧ rdd(V, p + 80#64) = rdd(V, p + 76#64)

/-- The registers at the `call` to `MyFree`: `rbx` = `this` (pushed), `rdi` = `_inBuf`. -/
abbrev gF (V : Addr → Byte) (g : Gprs) (ax dx : BitVec 64) : Gprs :=
  { g with
    rax := ax, rdx := dx, rbx := g.rdi, rsp := g.rsp - 8, rdi := rdq(V, g.rdi + 96#64) }

/-- The registers at 64 with no new buffer. -/
abbrev g64 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := 0, rdx := (rdd(V, g.rdi + 76#64)).setWidth 64, rbx := g.rdi, rsp := g.rsp - 8,
    rdi := rdq(V, g.rdi + 96#64) }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rbx, rdi; mov rdi, [rdi + 96]; test rdi, rdi; je 27; mov edx, [rbx + 76]; xor eax, eax;
cmp [rbx + 80], edx; je 64`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i))
    (f76 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 76#64) i))
    (f80 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 80#64) i))
    (x96 : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 96#64) = rdq(V, g.rdi + 96#64))
    (x76 : rdd(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 76#64) = rdd(V, g.rdi + 76#64))
    (x80 : rdd(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 80#64) = rdd(V, g.rdi + 80#64))
    (h27 : ¬ cOk V g.rdi → ∀ ax dx fl, Q 27 (gF V g ax dx) fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)))
    (h64 : cOk V g.rdi → ∀ fl, Q 64 (g64 V g) fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst f96 f76 f80 x96 x76 x80 ⊢
  by_cases h1 : rdq(V, rdi + 96#64) = 0
  · have hn : ¬ cOk V rdi := fun hk => hk.1 h1
    have hb : (rdq(V, rdi + 96#64) == 0) = true := beq_iff_eq.2 h1
    wpx [W_0, o0, x96, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h27 hn _ _ _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  have hb : (rdq(V, rdi + 96#64) == 0) = false := beq_eq_false_iff_ne.2 h1
  by_cases h2 : rdd(V, rdi + 80#64) = rdd(V, rdi + 76#64)
  · have hy : cOk V rdi := ⟨h1, h2⟩
    wpx [W_0, W_17, o0, o1, Op.cmpmr, x96, x76, x80, hb, h2, BitVec.and_self, BitVec.xor_self,
      BitVec.setWidth_zero, decide_true, decide_false, eq_self_iff_true, Bool.false_eq_true, Bool.true_eq_false,
      false_implies, implies_true]
    all_goals repeat'
      first
      | exact h64 hy _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hn : ¬ cOk V rdi := fun hk => h2 hk.2
    wpx [W_0, W_17, o0, o1, Op.cmpmr, x96, x76, x80, hb, h2, BitVec.and_self, BitVec.xor_self,
      BitVec.setWidth_zero, decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat'
      first
      | exact h27 hn _ _ _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- Back from `MyFree`: `mov dword [rbx + 76], 0; mov edi, [rbx + 80]` to the `call` at 42. -/
theorem vc_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (w76 : ∀ i < 4, Foot Wl (Addr.add (p + 76#64) i)) (f80 : ∀ i < 4, Foot F.data (Addr.add (p + 80#64) i))
    (x80 : rdd(Vst V (p + 76#64) (toBytesLE 0#32 4), p + 80#64) = rdd(V, p + 80#64))
    (h : ∀ fl, Q 42 { g with rdi := (rdd(V, p + 80#64)).setWidth 64 } fl (Vst V (p + 76#64) (toBytesLE 0#32 4))) :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h ⊢
  subst hbx
  wpx [W_32, o2, x80]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `MyAlloc`: `mov [rbx + 96], rax; test rax, rax; je 66`, then `mov eax, 0x8007000e; pop rbx` to the
`ret` at 72, or `mov eax, [rbx + 80]; mov [rbx + 76], eax; xor eax, eax` to 64. -/
theorem vc_47 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p s : Addr} (hbx : g.rbx = p) (hsx : g.rsp = s)
    (w96 : ∀ i < 8, Foot Wl (Addr.add (p + 96#64) i)) (w76 : ∀ i < 4, Foot Wl (Addr.add (p + 76#64) i))
    (f80 : ∀ i < 4, Foot F.data (Addr.add (p + 80#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add s i))
    (x80 : rdd(Vst V (p + 96#64) (toBytesLE g.rax 8), p + 80#64) = rdd(V, p + 80#64))
    (h72 : g.rax = 0 → ∀ fl, Q 72
      { g with rax := 0x8007000e#64, rbx := rdq(Vst V (p + 96#64) (toBytesLE g.rax 8), s), rsp := s + 8 } fl
      (Vst V (p + 96#64) (toBytesLE g.rax 8)))
    (h64 : g.rax ≠ 0 → ∀ fl, Q 64 { g with rax := 0 } fl
      (Vst (Vst V (p + 96#64) (toBytesLE g.rax 8)) (p + 76#64) (toBytesLE (rdd(V, p + 80#64)) 4))) :
    W_47 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx hsx x80 h72 h64 ⊢
  subst hbx hsx
  by_cases h0 : rax = 0
  · have hb : (rax == 0) = true := beq_iff_eq.2 h0
    wpx [W_47, W_66, o3, o6, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat'
      first
      | exact h72 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rax == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_47, W_56, o3, o4, hb, x80, BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h64 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `pop rbx` to the `ret` at 65. -/
theorem vc_64 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {s : Addr} (hsx : g.rsp = s)
    (hl : ∀ i < 8, Foot F.data (Addr.add s i)) (h : ∀ fl, Q 65 { g with rbx := rdq(V, s), rsp := s + 8 } fl V) :
    W_64 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsx h ⊢
  subst hsx
  wpx [W_64, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDecoder::CreateInputBuffer ()` (`this` = `rdi`) from its entry. `cOk`: at the return address with `rax` = 0
and the bytes `V` with `rbx` pushed (`kn`). Else at `MyFree`'s entry with the registers `gF`, `rsp` 16 below the
entry's (`kf`); back at `cib_at + 32` with `rsp`, `rbx` and the two stack slots as they were (and `P1`), at `MyAlloc`'s
entry with `rdi` = `_inBufSize` (`ka`); back at `cib_at + 47` likewise (and `P2`), at the return address with
`E_OUTOFMEMORY` for a null result (`kz`), else with `rax` = 0 and the size stored (`ks`). -/
theorem cib_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cib_at cib)
    {codeF codeA : List Byte} (hinF : CodeIn L 0x41f3f0#64 codeF) (hF : 0 < codeF.length)
    (hinA : CodeIn L 0x41f3c0#64 codeA) (hA0 : 0 < codeA.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cib_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (f76 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 76#64) i))
    (f80 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 80#64) i))
    (w96 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (w76 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 76#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 104 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 104 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : cOk V X.cpu.gpr.rdi → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rax := 0, rdx := (rdd(V, X.cpu.gpr.rdi + 76#64)).setWidth 64, rdi := rdq(V, X.cpu.gpr.rdi + 96#64),
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : ¬ cOk V X.cpu.gpr.rdi → ∀ (ax dx : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (cib_at.add 32) 8)) →
      Y.cpu.rip = 0x41f3f0#64 → Y.cpu.gpr = (gF V X.cpu.gpr ax dx).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = cib_at.add 32 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (ka : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V' (X.cpu.gpr.rdi + 76#64) (toBytesLE 0#32 4)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (cib_at.add 47) 8)) →
      Y.cpu.rip = 0x41f3c0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := (rdd(V', X.cpu.gpr.rdi + 80#64)).setWidth 64 }.set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = cib_at.add 47 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V'' → Z₂.cpu.gpr.rax = 0 →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rax := 0x8007000e#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (ks : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V'' → Z₂.cpu.gpr.rax ≠ 0 →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8))
        (X.cpu.gpr.rdi + 76#64) (toBytesLE (rdd(V'', X.cpu.gpr.rdi + 80#64)) 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rax := 0, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
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
  have tk : ∀ k : Nat, k < 104 → (X.cpu.gpr.rdi + BitVec.ofNat 64 k).toNat = X.cpu.gpr.rdi.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have t96 := tk 96 (by omega)
  have t80 := tk 80 (by omega)
  have t76 := tk 76 (by omega)
  -- the bytes stored by `push rbx`
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  -- a store into `this` does not change the stack's bytes
  have st : ∀ (W : Addr → Byte) (x : Addr) (k n : Nat) (bs : List Byte), bs.length = n → k < 104 →
      k + n ≤ 104 → x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 104 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + BitVec.ofNat 64 k) bs) = (byteAddrs x 8).map W := by
    intro W x k n bs hn hk hkn hx h
    have e := tk k hk
    exact Tun.rd_Vst W (X.cpu.gpr.rdi + BitVec.ofNat 64 k) bs x 8 (by rw [hn, e]; omega) hx (by rw [hn, e]; omega)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = cib_at.add 0 := by rw [addr_add_zero]; exact hrip
  have x96 : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 96#64) =
      rdq(V, X.cpu.gpr.rdi + 96#64) := by
    rw [m8 (X.cpu.gpr.rdi + 96#64) 8 (by rw [t96]; omega) (by rw [t96]; omega)]
  have x76 : rdd(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 76#64) =
      rdd(V, X.cpu.gpr.rdi + 76#64) := by
    rw [m8 (X.cpu.gpr.rdi + 76#64) 4 (by rw [t76]; omega) (by rw [t76]; omega)]
  have x80 : rdd(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 80#64) =
      rdd(V, X.cpu.gpr.rdi + 80#64) := by
    rw [m8 (X.cpu.gpr.rdi + 80#64) 4 (by rw [t80]; omega) (by rw [t80]; omega)]
  have hsb : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8, ofBytesLE_toBytesLE (n := 8) rfl]
  have hr1 : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m8 X.cpu.gpr.rsp 8 hp8 (by omega)]
    exact hra
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) ∧
      ((j' = 27 ∧ (∃ ax dx, g' = gF V X.cpu.gpr ax dx) ∧ ¬ cOk V X.cpu.gpr.rdi) ∨
        (j' = 64 ∧ g' = g64 V X.cpu.gpr ∧ cOk V X.cpu.gpr.rdi))) hK hA hrip'
    (vc_0 hs1 f96 f76 f80 x96 x76 x80 (fun hn ax dx _ => ⟨rfl, .inl ⟨rfl, ⟨ax, dx, rfl⟩, hn⟩⟩)
      (fun hy _ => ⟨rfl, .inr ⟨rfl, rfl, hy⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, ⟨ax, dx, rfl⟩, hn⟩ | ⟨rfl, rfl, hy⟩
  · -- `MyFree (_inBuf)`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_27 _) hinF hF (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gF V X.cpu.gpr ax dx).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gF V X.cpu.gpr ax dx).set 4 v) e16
    refine kf hn ax dx Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb' hr' hP1
    -- `_inBufSizeAllocated = 0`, `MyAlloc (_inBufSize)`
    have x80' : rdd(Vst V' (X.cpu.gpr.rdi + 76#64) (toBytesLE 0#32 4), X.cpu.gpr.rdi + 80#64) =
        rdd(V', X.cpu.gpr.rdi + 80#64) := by
      rw [Tun.rd_Vst V' (X.cpu.gpr.rdi + 76#64) (toBytesLE 0#32 4) (X.cpu.gpr.rdi + 80#64) 4
        (by rw [toBytesLE_length, t76]; omega) (by rw [t80]; omega) (by rw [toBytesLE_length, t76, t80]; omega)]
    refine (c_32 prof).run c hin (fun j' g' _ V'' => j' = 42 ∧
        g' = { Z.cpu.gpr with rdi := (rdd(V', X.cpu.gpr.rdi + 80#64)).setWidth 64 } ∧
        V'' = Vst V' (X.cpu.gpr.rdi + 76#64) (toBytesLE 0#32 4)) hKZ hAZ hrZ
      (vc_32 hzb w76 f80 x80' fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hs3 : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₃]; exact hzs
    have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3, e16]; exact hs2
    refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_42 _) hinA hA0 (by decide) hst3 ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hs3, e16] at hA₄
    have hg₄' : Y₄.cpu.gpr =
        { Z.cpu.gpr with rdi := (rdd(V', X.cpu.gpr.rdi + 80#64)).setWidth 64 }.set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₄, hs3, e16, hg₃]
    refine ka Z V' hP1 Y₄ t₄ hK₄ hA₄ hr₄ hg₄' ?_
    intro Z₂ V'' t₅ hK₅ hA₅ hr₅ hz2s hz2b hb₂ hr₂'' hP2
    -- `_inBuf = …`
    have x80'' : rdd(Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8), X.cpu.gpr.rdi + 80#64) =
        rdd(V'', X.cpu.gpr.rdi + 80#64) := by
      rw [Tun.rd_Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8) (X.cpu.gpr.rdi + 80#64) 4
        (by rw [toBytesLE_length, t96]; omega) (by rw [t80]; omega) (by rw [toBytesLE_length, t96, t80]; omega)]
    have s96 : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
        (X.cpu.gpr.rdi.toNat + 104 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
        (byteAddrs x 8).map (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) =
          (byteAddrs x 8).map V'' :=
      fun x hx h => st V'' x 96 8 _ (toBytesLE_length _ _) (by omega) (by omega) hx h
    by_cases h0 : Z₂.cpu.gpr.rax = 0
    · -- `E_OUTOFMEMORY`
      refine (c_47 prof).run c hin (fun j' g' _ V₃ => j' = 72 ∧
          g' = { Z₂.cpu.gpr with rax := 0x8007000e#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
          V₃ = Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) hK₅ hA₅ hr₅
        (vc_47 hz2b hz2s w96 w76 f80 h8 x80''
          (fun _ _ => ⟨rfl, by rw [s96 _ hq8 (by rw [tn8]; omega), hb₂, e8], rfl⟩) (fun h => absurd h0 h)) ?_
      rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₆ hKU hAU hrU hgU -
      subst V₃
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_72 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU, s96 _ hp8 (by omega)]; exact hr₂'') ?_
      rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine kz Z₂ V'' Z' t₇ hP2 h0 hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU]
      try rfl
    · -- `_inBufSizeAllocated = _inBufSize`, `S_OK`
      have hsb4 : rdq(Vst (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 76#64)
          (toBytesLE (rdd(V'', X.cpu.gpr.rdi + 80#64)) 4), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
        rw [st _ (X.cpu.gpr.rsp - 8) 76 4 _ (toBytesLE_length _ _) (by omega) (by omega) hq8 (by rw [tn8]; omega),
          s96 _ hq8 (by rw [tn8]; omega)]
        exact hb₂
      have hr4 : rdq(Vst (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 76#64)
          (toBytesLE (rdd(V'', X.cpu.gpr.rdi + 80#64)) 4), X.cpu.gpr.rsp) = e₂.add j₂ := by
        rw [st _ X.cpu.gpr.rsp 76 4 _ (toBytesLE_length _ _) (by omega) (by omega) hp8 (by omega),
          s96 _ hp8 (by omega)]
        exact hr₂''
      refine (c_47 prof).run c hin (fun j' g' _ V₃ => j' = 64 ∧ g' = { Z₂.cpu.gpr with rax := 0 } ∧
          V₃ = Vst (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 76#64)
            (toBytesLE (rdd(V'', X.cpu.gpr.rdi + 80#64)) 4)) hK₅ hA₅ hr₅
        (vc_47 hz2b hz2s w96 w76 f80 h8 x80'' (fun h => absurd h h0) (fun _ _ => ⟨rfl, rfl, rfl⟩)) ?_
      rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₆ hKU hAU hrU hgU -
      subst V₃
      refine (c_64 prof).run c hin (fun j' g' _ V₄ => j' = 65 ∧
          g' = { U.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
          V₄ = Vst (Vst V'' (X.cpu.gpr.rdi + 96#64) (toBytesLE Z₂.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 76#64)
            (toBytesLE (rdd(V'', X.cpu.gpr.rdi + 80#64)) 4)) hKU hAU hrU
        (vc_64 (s := X.cpu.gpr.rsp - 8) (by rw [hgU]; exact hz2s) h8 fun _ => ⟨rfl, by rw [hsb4, e8], rfl⟩) ?_
      rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₈ hKU' hAU' hrU' hgU' -
      subst V₄
      have hsU' : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
      refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_65 _) (by rw [hsU']; exact hl) hin₂ h₂
        (by rw [hsU']; exact hr4) ?_
      rintro Z' t₉ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine ks Z₂ V'' Z' t₉ hP2 h0 hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU', hgU]
      try rfl
  · -- no new buffer: `pop rbx; ret`
    refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 65 ∧
        g' = { Y.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hKY hAY hrY
      (vc_64 (s := X.cpu.gpr.rsp - 8) (by rw [hgY]) h8 fun _ => ⟨rfl, by rw [hsb, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_65 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr1) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hy Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU, hgY]
    try rfl

end FV7z.Cib
