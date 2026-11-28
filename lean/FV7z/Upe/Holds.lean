import FV7z.Upe.Cuts
import FV7z.Ugr.Code
import FV7z.Ugr.Blocks
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.Fr24
import FV7z.Tun.Inv
/-!
# `UString::operator+=` (PLAN.md §M, M1)

7-Zip 26.06's `UString::operator+= (const UString &s)` at `0x44db90` in `7zzs` (`CPP/Common/MyString.cpp`), `this` =
`rdi`, `s` = `rsi`: `push r12; mov r12, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, [rsi + 8]`; at 20 the `call`
of `Grow (s._len)` (`Ugr.ugr_at`, `rel` 18446744073709548855); at 25 `mov eax, [rbx + 8]; mov ecx, [r12 + 8];
mov rsi, [rbx]; lea edx, [rax + 1]; mov rax, [r12]; lea rdi, [rax + rcx * 4]`; at 47 the `call` of
`wmemcpy (_chars + _len, s._chars, s._len + 1)` (`Wmc.wmc_at`, `rel` 2160444); at 52 `mov eax, [rbx + 8]`; at 55
`add dword [r12 + 8], eax` (`Seg.s_add_mr32`: `_len += s._len`); at 60 `mov rax, r12; add rsp, 8; pop rbx; pop r12`;
the `ret` (70).

Design as `FV7z/Efn/Holds.lean` (the same 24-byte frame, `FV7z/Lemmas/Fr24.lean`): both callees are hypotheses, each a
continuation at its entry given the run from its return (`rsp` 24 below the entry's, `rbx` = `s`, `r12` = `this`, the
saved `rbx`, `r12` and the return address left as they were, and the callee's own post `P1`, `P2`): `k1` at `Grow`
(registers `gE`, the bytes `V0` of the two `push`es; `esi` is read after them), `k2` at `wmemcpy` (registers `g47`
from the bytes then), `kr` at the return address with the bytes `V3` (the new `_len`). The 4 bytes of `_len` lie
apart from the frame (`hd`).

- `V0`, `gE`: the bytes and the registers at the first `call`; `g47`: at the second; `V3`: the bytes after the `add`.
- `vc_0`, `vc_25`, `vc_52`, `vc_60`: the verification conditions of the pieces.
- `upe_ok`: from the entry to the return address with `rax` = `this` and `rbx`, `r12`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Upe

/-- The `call` to `UString::Grow`. -/
def pcg : List Byte := [0xe8, 0x37, 0xf5, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709548855] 5) := by dec_rfl
theorem wg_20 : pcg <+: upe.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat upe 20 (FV7z.mk .call 64 [.rel 18446744073709548855] 5) :=
  Dec.shift (j := 20) (k := 0) (pcg_0 feat) wg_20 (Nat.zero_le _)
theorem tgt_20 : upe_at.add (20 + 5) + BitVec.ofNat 64 18446744073709548855 = Ugr.ugr_at.add 0 := by decide

/-- The `call` to `wmemcpy`. -/
def pcm : List Byte := [0xe8, 0x3c, 0xf7, 0x20, 0x00]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 2160444] 5) := by dec_rfl
theorem wm_47 : pcm <+: upe.drop 47 := by decide +kernel
theorem call_47 (feat : Features) : Dec feat upe 47 (FV7z.mk .call 64 [.rel 2160444] 5) :=
  Dec.shift (j := 47) (k := 0) (pcm_0 feat) wm_47 (Nat.zero_le _)
theorem tgt_47 : upe_at.add (47 + 5) + BitVec.ofNat 64 2160444 = Wmc.wmc_at.add 0 := by decide

/-- `add dword [r12 + 8], eax`. -/
def pad : List Byte := [0x41, 0x01, 0x44, 0x24, 0x08]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 0] 5) := by dec_rfl
theorem wa_55 : pad <+: upe.drop 55 := by decide +kernel
theorem add_55 (feat : Features) : Dec feat upe 55 (FV7z.mk .add 32 [.mem (mbd 12 8 32), gr 32 0] 5) :=
  Dec.shift (j := 55) (k := 0) (pad_0 feat) wa_55 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_70 : pret <+: upe.drop 70 := by decide +kernel
theorem ret_70 (feat : Features) : Dec feat upe 70 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 70) (k := 0) (pret_0 feat) w_70 (Nat.zero_le _)

/-- The bytes after `push r12; push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `r12` = `this`, `rbx` = `s`, `esi` = `s._len` (read from `V0`), `rsp` 24
down. -/
abbrev gE (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8#64
    rsi := BitVec.setWidth 64 rdd(V0 V g, g.rsi + 8#64)
    r12 := g.rdi }

/-- The registers at the second `call`: `rdi` = `_chars + _len` (4 bytes a character), `rsi` = `s._chars`, `edx` =
`s._len + 1`. -/
abbrev g47 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rax := rdq(V, g.r12)
    rcx := BitVec.setWidth 64 rdd(V, g.r12 + 8#64)
    rdx := ((BitVec.setWidth 64 rdd(V, g.rbx + 8#64) + 1#64).setWidth 32).setWidth 64
    rsi := rdq(V, g.rbx)
    rdi := rdq(V, g.r12) + BitVec.setWidth 64 rdd(V, g.r12 + 8#64) * 4#64 }

/-- The bytes after `_len += s._len` (`this` = `g.rdi`, `s` = `g.rsi`). -/
abbrev V3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V (g.rdi + 8#64) (toBytesLE (rdd(V, g.rdi + 8#64) + rdd(V, g.rsi + 8#64)) 4)

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, [rsi + 8]`, to the `call` at 20. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h : ∀ fl, Q 20 (gE g V) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gE, V0] at hs1 hs2 fn h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov eax, [rbx + 8]; mov ecx, [r12 + 8]; mov rsi, [rbx]; lea edx, [rax + 1]; mov rax, [r12];
lea rdi, [rax + rcx * 4]`, to the `call` at 47. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f2 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (f4 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ fl, Q 47 (g47 g V) fl V) : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g47] at f1 f2 f3 f4 h ⊢
  wpx [W_25, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov eax, [rbx + 8]`, to the `add` at 55. -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h : ∀ fl, Q 55 { g with rax := BitVec.setWidth 64 rdd(V, g.rbx + 8#64) } fl V) : W_52 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 h ⊢
  wpx [W_52, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov rax, r12; add rsp, 8; pop rbx; pop r12`, to the `ret` at 70. -/
theorem vc_60 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 70
      { g with
        rax := g.r12
        rbx := rdq(V, g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_60 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_60, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::operator+= (s)` (`this` = `rdi`, `s` = `rsi`) from its entry, `r12` and `rbx` saved at `rsp - 8` and
`rsp - 16`: at `Grow`'s entry with the registers `gE`, the return address `upe_at + 25` at `rsp - 32` (`k1`); from its
return, at `wmemcpy`'s with the registers `g47` (`k2`); from that return, at the return address with `_len` (the 4
bytes at `this + 8`) `_len + s._len` (`V3`), `rax` = `this`, `rbx`, `r12`, `rsp` restored (`kr`). -/
theorem upe_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L upe_at upe)
    (hinG : CodeIn L Ugr.ugr_at Ugr.ugr) (hinM : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = upe_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (upe_at.add 25) 8)) →
      Y.cpu.rip = Ugr.ugr_at → Y.cpu.gpr = (gE X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = upe_at.add 25 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.r12 = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE' Z t'') →
      GoG prof L o gev gP gE' Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (upe_at.add 52) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (g47 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = upe_at.add 52 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z₂.cpu.gpr.r12 = X.cpu.gpr.rdi → rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V₂ →
        GoG prof L o gev gP gE' Z₂ t'') →
      GoG prof L o gev gP gE' Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V3 V₂ X.cpu.gpr) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have fl8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i) := fun i hi => c.hws _ (fw i hi)
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := pt8 _ hp
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := pt16 _ hp
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the frame's bytes as they were after the `add` to `_len`
  have m3 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (V3 W X.cpu.gpr) = (byteAddrs x 8).map W := fun W x hx h =>
    Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, t8]; omega) hx (by rw [toBytesLE_length, t8]; omega)
  have hrip' : X.cpu.rip = upe_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gE X.cpu.gpr V ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) fn fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, pe32]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_20 _) hinG (tgt := 0) (Ugr.lt_len (by decide))
    tgt_20 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gE X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
  refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `Grow`, at 25: to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hz12 hb hr12 hr' hP1
  refine (c_25 prof).run c hin (fun j' g' _ V'' => j' = 47 ∧ g' = g47 Z.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
    (vc_25 (by rw [hzb]; exact fn) (by rw [hz12]; exact fl8) (by rw [hzb]; exact fb) (by rw [hz12]; exact fc)
      fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
  have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsU, peD]
  have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hU32]; exact hs4
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_47 _) hinM (tgt := 0) (Wmc.lt_len (by decide))
    tgt_47 hst2 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hU32] at hA₃
  have hg₃' : Y₃.cpu.gpr = (g47 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₃, hU32, hgU]
  refine k2 Z V' hP1 Y₃ t₄ hK₃ hA₃ (by rw [hr₃, addr_add_zero]) hg₃' ?_
  -- back from `wmemcpy`, at 52: `mov eax, [rbx + 8]`, then the `add` at 55
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2b hz2r hb2 h12b hr2 hP2
  refine (c_52 prof).run c hin (fun j' g' _ V'' => j' = 55 ∧
      g' = { Z₂.cpu.gpr with rax := BitVec.setWidth 64 rdd(V₂, Z₂.cpu.gpr.rbx + 8#64) } ∧ V'' = V₂)
    hKZ₂ hAZ₂ hrZ₂ (vc_52 (by rw [hz2b]; exact fn) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₁ t₆ hKU₁ hAU₁ hrU₁ hgU₁ -
  subst V₃
  have hU12 : U₁.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgU₁]; exact hz2r
  have e12 : eaD U₁ 12 8 = X.cpu.gpr.rdi + 8#64 := by
    show U₁.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 8 = _
    rw [show U₁.cpu.gpr.get (regOf 12) = U₁.cpu.gpr.r12 from rfl, hU12]
  have erv : rv U₁ 32 0 = rdd(V₂, X.cpu.gpr.rsi + 8#64) := by
    show BitVec.setWidth 32 (U₁.cpu.gpr.get (regOf 0)) = _
    rw [show U₁.cpu.gpr.get (regOf 0) = U₁.cpu.gpr.rax from rfl, hgU₁]
    show BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V₂, Z₂.cpu.gpr.rbx + 8#64)) = _
    rw [hz2b]
    exact sw_64_32 _
  refine c.s_add_mr32 hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (add_55 _) (by rw [e12]; exact fw) ?_
  rw [e12, erv]
  rintro Y₆ t₇ hK₆ hA₆ ⟨hr₆, hg₆⟩
  replace hA₆ : Agree F Y₆.proc.mm.mem (V3 V₂ X.cpu.gpr) := hA₆
  have hg6' : Y₆.cpu.gpr = { Z₂.cpu.gpr with rax := BitVec.setWidth 64 rdd(V₂, Z₂.cpu.gpr.rbx + 8#64) } :=
    hg₆.trans hgU₁
  have hY6s : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg6']; exact hz2s
  have hY6r : Y₆.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hg6']; exact hz2r
  have hb2' : rdq(V3 V₂ X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [m3 V₂ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hb2
  have h12b' : rdq(V3 V₂ X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
    rw [m3 V₂ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact h12b
  have hr2' : rdq(V3 V₂ X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m3 V₂ X.cpu.gpr.rsp hp8 (by omega)]
    exact hr2
  -- the epilogue at 60, then the `ret` at 70
  refine (c_60 prof).run c hin (fun j' g' _ V'' => j' = 70 ∧
      g' = { Y₆.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp
        r12 := X.cpu.gpr.r12 } ∧ V'' = V3 V₂ X.cpu.gpr) hK₆ hA₆ hr₆
    (vc_60 (by rw [hY6s, peA']; exact h16) (by rw [hY6s, peA', peB]; exact h8)
      fun _ => ⟨rfl, by rw [hY6s, hY6r, peA', peB, peC, hb2', h12b'], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₈ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₄
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_70 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hr2') ?_
  rintro Z' t₉ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V₂ Z' t₉ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂, hg6']
  try rfl

end FV7z.Upe
