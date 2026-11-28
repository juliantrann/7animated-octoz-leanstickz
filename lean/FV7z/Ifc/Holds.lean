import FV7z.Ifc.Cuts
import FV7z.Uct.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CInFileStream::CInFileStream ()` (PLAN.md §M, M1)

7-Zip 26.06's `CInFileStream::CInFileStream ()` at `0x5a3f70` in `7zzs` (`CPP/7zip/Common/FileStreams.h`;
`objdump -d`): `rbp`, `rbx` saved, `rbx` = `this`, `rdi` = `this + 208`, `rsp` 8 lower; the byte at `this + 48`
(`File`'s handle state) and the 8 bytes at `this + 200` (`Callback`) 0, the five vtable pointers (`0x78e748` + 16,
+ 112, + 160, + 208, + 256 at `this`, `this + 8`, `this + 16`, `this + 24`, `this + 32`) and the 8 bytes at
`this + 40` `0xffffffff00000000`; then the `UString` at `this + 208` (`call` at 122 to `UString::UString ()`,
`Uct.uct_at`) and the one at `this + 224` (`call` at 134, the same callee); after them the 4 bytes at `this + 240`
and the 8 bytes at `this + 248` and `this + 256` 0, the frame given back (139 to 176) and `ret` (177).

The callees are hypotheses (`kf1`, `kf2`), as in `FV7z/Cpc/Holds.lean`: each a continuation at its entry, given the
run from its return (`ifc_at + 127`, `ifc_at + 139`, `rsp` as at the `call`) on. The second's run also gives `rbx`
(= `this`), the saved registers and the return address back as they were (`kf2`), and its own post `P2`; `kr` takes
the run on from the return address. The three stores after the second `call` lie apart from the saved `rbx`, `rbp`
and the return address (`hr`, `hs`, `hs8`, `hd`), so the pops read them back (`rd_vb`).

- `gA`, `VA`: the registers and the bytes at the first `call`; `VB`: the bytes after the three last stores.
- `vc_0`, `vc_127`, `vc_139`: the verification conditions of the three pieces.
- `ifc_ok`: from the entry, through the two callees, to the return address with `rbx`, `rbp` restored and `rsp` 8
  up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ifc

/-- The `call`s to `UString::UString ()`. -/
def pcall1 : List Byte := [0xe8, 0xf1, 0x93, 0xea, 0xff]
theorem pcall1_0 : ∀ feat, Dec feat pcall1 0 (FV7z.mk .call 64 [.rel 18446744073708147697] 5) := by dec_rfl
theorem wc_122 : pcall1 <+: ifc.drop 122 := by decide +kernel
theorem call_122 (feat : Features) : Dec feat ifc 122 (FV7z.mk .call 64 [.rel 18446744073708147697] 5) :=
  Dec.shift (j := 122) (k := 0) (pcall1_0 feat) wc_122 (Nat.zero_le _)
def pcall2 : List Byte := [0xe8, 0xe5, 0x93, 0xea, 0xff]
theorem pcall2_0 : ∀ feat, Dec feat pcall2 0 (FV7z.mk .call 64 [.rel 18446744073708147685] 5) := by dec_rfl
theorem wc_134 : pcall2 <+: ifc.drop 134 := by decide +kernel
theorem call_134 (feat : Features) : Dec feat ifc 134 (FV7z.mk .call 64 [.rel 18446744073708147685] 5) :=
  Dec.shift (j := 134) (k := 0) (pcall2_0 feat) wc_134 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_177 : pret <+: ifc.drop 177 := by decide +kernel
theorem ret_177 (feat : Features) : Dec feat ifc 177 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 177) (k := 0) (pret_0 feat) w_177 (Nat.zero_le _)

/-- The stores' addresses `rdi + 208 - 160`, `- 8`, `- 208`, `- 200`, `- 192`, `- 176`, `- 184`, `- 168`. -/
theorem ea48 (x : Addr) : x + 208#64 + 18446744073709551456#64 = x + 48#64 := by bv_omega
theorem ea200 (x : Addr) : x + 208#64 + 18446744073709551608#64 = x + 200#64 := by bv_omega
theorem ea0 (x : Addr) : x + 208#64 + 18446744073709551408#64 = x := by bv_omega
theorem ea8 (x : Addr) : x + 208#64 + 18446744073709551416#64 = x + 8#64 := by bv_omega
theorem ea16 (x : Addr) : x + 208#64 + 18446744073709551424#64 = x + 16#64 := by bv_omega
theorem ea32 (x : Addr) : x + 208#64 + 18446744073709551440#64 = x + 32#64 := by bv_omega
theorem ea24 (x : Addr) : x + 208#64 + 18446744073709551432#64 = x + 24#64 := by bv_omega
theorem ea40 (x : Addr) : x + 208#64 + 18446744073709551448#64 = x + 40#64 := by bv_omega

theorem b3s (S : Addr) : S - 8 - 8 - 8#64 + 8#64 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem b2s (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem b1s (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The registers at the first `call`: `rax` the last constant, `rdx` the fourth vtable pointer, `rbx` = `this`,
`rdi` = `this + 208`, two pushes and 8 more. -/
abbrev gA (g : Gprs) : Gprs :=
  { g with
      rax := 18446744069414584320#64,
      rdx := 7923528#64 + 208#64,
      rbx := g.rdi,
      rdi := g.rdi + 208#64,
      rsp := g.rsp - 8 - 8 - 8#64 }

/-- The bytes at the first `call`: the two pushes and the ten stores, in their order. -/
abbrev VA (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8)
    (toBytesLE g.rbx 8)) (g.rdi + 48#64) (toBytesLE 0#8 1)) (g.rdi + 200#64) (toBytesLE 0#64 8))
    g.rdi (toBytesLE (7923528#64 + 16#64) 8)) (g.rdi + 8#64) (toBytesLE (7923528#64 + 112#64) 8))
    (g.rdi + 16#64) (toBytesLE (7923528#64 + 160#64) 8)) (g.rdi + 32#64) (toBytesLE (7923528#64 + 256#64) 8))
    (g.rdi + 24#64) (toBytesLE (7923528#64 + 208#64) 8)) (g.rdi + 40#64) (toBytesLE 18446744069414584320#64 8)

/-- The bytes after the three stores at `r + 240`, `r + 248`, `r + 256` (`r` = `this`). -/
abbrev VB (V : Addr → Byte) (r : Addr) : Addr → Byte :=
  Vst (Vst (Vst V (r + 240#64) (toBytesLE 0#32 4)) (r + 248#64) (toBytesLE 0#64 8)) (r + 256#64) (toBytesLE 0#64 8)

theorem n240 {r : Addr} (h : r.toNat + 264 ≤ 2 ^ 64) : (r + 240#64).toNat = r.toNat + 240 := by
  rw [BitVec.toNat_add]; simp <;> omega
theorem n248 {r : Addr} (h : r.toNat + 264 ≤ 2 ^ 64) : (r + 248#64).toNat = r.toNat + 248 := by
  rw [BitVec.toNat_add]; simp <;> omega
theorem n256 {r : Addr} (h : r.toNat + 264 ≤ 2 ^ 64) : (r + 256#64).toNat = r.toNat + 256 := by
  rw [BitVec.toNat_add]; simp <;> omega
theorem n8 {S : Addr} (h : 8 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by
  have := S.isLt
  rw [BitVec.toNat_sub]; simp <;> omega
theorem n16 {S : Addr} (h : 16 ≤ S.toNat) : (S - 8 - 8).toNat = S.toNat - 16 := by
  have := S.isLt
  rw [BitVec.toNat_sub, n8 (by omega)]; simp <;> omega

/-- A load apart from the three last stores. -/
theorem rd_vb {W : Addr → Byte} {r x : Addr} (hr : r.toNat + 264 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : r.toNat + 264 ≤ x.toNat ∨ x.toNat + 8 ≤ r.toNat + 240) : rdq(VB W r, x) = rdq(W, x) := by
  show ofBytesLE 64 (List.map (Vst (Vst (Vst W (r + 240#64) (toBytesLE 0#32 4)) (r + 248#64) (toBytesLE 0#64 8))
    (r + 256#64) (toBytesLE 0#64 8)) (byteAddrs x 8)) = _
  rw [Tun.rd_Vst (Vst (Vst W (r + 240#64) (toBytesLE 0#32 4)) (r + 248#64) (toBytesLE 0#64 8)) (r + 256#64)
      (toBytesLE 0#64 8) x 8 (by rw [toBytesLE_length, n256 hr]; omega) hx
      (by rw [toBytesLE_length, n256 hr]; omega),
    Tun.rd_Vst (Vst W (r + 240#64) (toBytesLE 0#32 4)) (r + 248#64) (toBytesLE 0#64 8) x 8
      (by rw [toBytesLE_length, n248 hr]; omega) hx (by rw [toBytesLE_length, n248 hr]; omega),
    Tun.rd_Vst W (r + 240#64) (toBytesLE 0#32 4) x 8
      (by rw [toBytesLE_length, n240 hr]; omega) hx (by rw [toBytesLE_length, n240 hr]; omega)]

variable {F : Footprint} {Wl : List Rgn}

/-- The two pushes, `mov rbx, rdi; lea rdi, [rdi + 208]; sub rsp, 8`, the constants and the ten stores, to the
`call` at 122. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fw48 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 48#64) i))
    (fw200 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 200#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (fw32 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 32#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 24#64) i))
    (fw40 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 40#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 122 ∧ g' = gA g ∧ V' = VA V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 fw48 fw200 fw0 fw8 fw16 fw32 fw24 fw40 ⊢
  wpx [W_0, o0, gA, VA, ea48, ea200, ea0, ea8, ea16, ea32, ea24, ea40]
  all_goals repeat'
    first
    | with_reducible rfl
    | with_reducible assumption
    | exact trivial
    | exact rfl
    | apply And.intro
    | intro _

/-- Back from the first callee: `lea rdi, [rbx + 224]`, to the `call` at 134. -/
theorem vc_127 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_127 F Wl (fun j' g' _ V' => j' = 134 ∧ g' = { g with rdi := g.rbx + 224#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only
  wpx [W_127, o1]
  all_goals repeat'
    first
    | with_reducible rfl
    | exact trivial
    | exact rfl
    | apply And.intro
    | intro _

/-- Back from the second callee: the three stores, `add rsp, 8` and the two pops, to the `ret` at 177. -/
theorem vc_139 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 240#64) i)) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 248#64) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 256#64) i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 177
      { g with
          rbx := rdq(VB V g.rbx, g.rsp + 8#64),
          rbp := rdq(VB V g.rbx, g.rsp + 8#64 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 } fl (VB V g.rbx)) :
    W_139 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w1 w2 p0 p1 h ⊢
  wpx [W_139, o2]
  all_goals repeat'
    first
    | exact h _
    | with_reducible assumption
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CInFileStream::CInFileStream ()` (`this` = `rdi`) from its entry. At the first callee's entry the registers are
`gA` with the return address `ifc_at + 127` pushed and the bytes `VA` (`kf1`); back at `ifc_at + 127` with `rsp` as
at the `call` and `P1`, the run goes to the second callee's entry with `rdi` = `rbx + 224` and the return address
`ifc_at + 139` pushed (`kf2`); back at `ifc_at + 139` with `rsp` as at the `call`, `rbx` = `this`, the saved
registers and the return address as they were and `P2`, the run reaches the return address with the bytes `VB`,
`rbx`, `rbp` restored and `rsp` 8 up (`kr`). -/
theorem ifc_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ifc_at ifc)
    (hinU : CodeIn L Uct.uct_at Uct.uct)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifc_at)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (h2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw48 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (fw200 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 200#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fw32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (fw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (fw40 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (fw240 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 240#64) i))
    (fw248 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 248#64) i))
    (fw256 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 256#64) i))
    (hr : X.cpu.gpr.rdi.toNat + 264 ≤ 2 ^ 64) (hs : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 264 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 240)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VA V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8)
        (toBytesLE (ifc_at.add 127) 8)) →
      Y.cpu.rip = Uct.uct_at → Y.cpu.gpr = (gA X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ifc_at.add 127 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
        P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) (toBytesLE (ifc_at.add 139) 8)) →
      Y.cpu.rip = Uct.uct_at →
      Y.cpu.gpr = ({ Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 224#64 }).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8#64 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = ifc_at.add 139 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 →
        Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VB V'' X.cpu.gpr.rdi) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = ifc_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 122 ∧ g' = gA X.cpu.gpr ∧ V' = VA V X.cpu.gpr) hK hA hrip'
    (vc_0 h1 h2 fw48 fw200 fw0 fw8 fw16 fw32 fw24 fw40) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_122 _) hinU (Uct.lt_len (by decide)) (by decide)
    (by rw [hsY]; exact h4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from the first callee, to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs hP1
  refine (c_127 prof).run c hin (fun j' g' _ V'' => j' = 134 ∧ g' = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 224#64 } ∧
    V'' = V') hKZ hAZ hrZ vc_127 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgU]; exact hzs
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_134 _) hinU (Uct.lt_len (by decide)) (by decide)
    (by rw [hsU]; exact h4) ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU] at hA₃
  refine kf2 Z V' hP1 Y₃ t₄ hK₃ hA₃ hr₃ (by rw [hg₃, hsU, hgU]) ?_
  -- back from the second callee: the stores, to the `ret`
  intro Z₂ V'' t₅ hKZ₂ hAZ₂ hrZ₂ hzs₂ hzb hb2 hb1 hra hP2
  have q2 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64) i) := by
    rw [hzs₂, b3s]; exact fun i hi => c.hws _ (h2 i hi)
  have q1 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64 + 8) i) := by
    rw [hzs₂, b3s, b2s]; exact fun i hi => c.hws _ (h1 i hi)
  have rv2 : rdq(VB V'' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbx := by
    rw [rd_vb hr (by rw [n16 hs]; omega) (by rw [n16 hs]; omega)]; exact hb2
  have rv1 : rdq(VB V'' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
    rw [rd_vb hr (by rw [n8 (by omega)]; omega) (by rw [n8 (by omega)]; omega)]; exact hb1
  have rv0 : rdq(VB V'' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [rd_vb hr hs8 (by omega)]; exact hra
  refine (c_139 prof).run c hin (fun j' g' _ V₃ => j' = 177 ∧
      g' = { Z₂.cpu.gpr with
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp } ∧ V₃ = VB V'' X.cpu.gpr.rdi) hKZ₂ hAZ₂ hrZ₂
    (vc_139 (by rw [hzb]; exact fw240) (by rw [hzb]; exact fw248) (by rw [hzb]; exact fw256) q2 q1
      fun _ => ⟨rfl, by rw [hzs₂, hzb, b3s, b2s, b1s, rv2, rv1], by rw [hzb]⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₃
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_177 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact rv0) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V'' Z' t₇ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Ifc
