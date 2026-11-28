import FV7z.Tfr.Cuts
import FV7z.Rmf.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `NWindows::NFile::NDir::CTempFile::Remove ()` (PLAN.md §M, M1)

7-Zip 26.06's `CTempFile::Remove ()` at `0x455030` in `7zzs` (`CPP/Windows/FileDir.cpp`; `objdump -d`), `this` in
`rdi`: `if (!_mustBeDeleted) return true; _mustBeDeleted = !DeleteFileAlways (_path); return !_mustBeDeleted;` as
`cmp byte [rdi], 0; jne` (4, 7): for 0, `mov eax, 1; ret` (9, 14); else `push rbx; mov rbx, rdi; mov rdi, [rdi + 8]`,
the `call` at 24 to `DeleteFileAlways` (`Rmf.rmf_at`), then `mov edx, eax; xor edx, 1; mov [rbx], dl; pop rbx; ret`
(29, 37) with `rax` as the callee left it.

The callee is a hypothesis, as `umask` in `FV7z/Cum/Holds.lean`: `kf` is a continuation at its entry, given the run
from its return (`rsp` 8 below the entry's, `rbx` = `this`, the saved `rbx` and the return address as they were:
`Sv`) and its own post `Pr`. The store `_mustBeDeleted` (the byte at `this`) needs `this` clear of the 16 bytes from
the saved `rbx` to the return address (`hd`): no hypothesis on the bytes after the store.

- `b0`: the byte `_mustBeDeleted`; `V0`, `gC`: the bytes and the registers at the `call`; `Vm`: the bytes after the
  store.
- `vc_0`, `vc_29`: the verification conditions of the pieces.
- `tfr_ok`: from the entry to the return address (`kz` for `_mustBeDeleted` 0, else through `DeleteFileAlways`, `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tfr

/-- The `call` to `DeleteFileAlways`. -/
def pcr : List Byte := [0xe8, 0xc3, 0xff, 0xff, 0xff]
theorem pcr_0 : ∀ feat, Dec feat pcr 0 (FV7z.mk .call 64 [.rel 18446744073709551555] 5) := by dec_rfl
theorem wc_24 : pcr <+: tfr.drop 24 := by decide +kernel
theorem call_24 (feat : Features) : Dec feat tfr 24 (FV7z.mk .call 64 [.rel 18446744073709551555] 5) :=
  Dec.shift (j := 24) (k := 0) (pcr_0 feat) wc_24 (Nat.zero_le _)
theorem tgt_24 : tfr_at.add (24 + 5) + BitVec.ofNat 64 18446744073709551555 = Rmf.rmf_at.add 0 := by decide

theorem rmf_lt : 0 < Rmf.rmf.length := by rw [Rmf.rmf_length]; decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_14 : pret <+: tfr.drop 14 := by decide +kernel
theorem ret_14 (feat : Features) : Dec feat tfr 14 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 14) (k := 0) (pret_0 feat) w_14 (Nat.zero_le _)
theorem w_37 : pret <+: tfr.drop 37 := by decide +kernel
theorem ret_37 (feat : Features) : Dec feat tfr 37 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 37) (k := 0) (pret_0 feat) w_37 (Nat.zero_le _)

/-- `_mustBeDeleted`: the byte at `p`. -/
abbrev b0 (V : Addr → Byte) (p : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs p 1).map V)

/-- The bytes at the `call`: `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call`: `rbx` = `this`, `rdi` = `_path` (read after the push), 8 below the entry. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rbx := g.rdi, rdi := rdq(V0 V g, g.rdi + 8#64), rsp := g.rsp - 8 }

/-- The bytes after `mov [rbx], dl` for the registers `g` back from `DeleteFileAlways`. -/
abbrev Vm (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V g.rbx (toBytesLE ((BitVec.setWidth 32 g.rax ^^^ 1#32).setWidth 8) 1)

/-- The saved `rbx` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop := rdq(V, x.rsp - 8) = x.rbx ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp byte [rdi], 0; jne`: to the `ret` at 14 by `mov eax, 1`, or by `push rbx; mov rbx, rdi;
mov rdi, [rdi + 8]` to the `call` at 24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 1, Foot F.data (Addr.add g.rdi i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hz : b0 V g.rdi = 0#8 → ∀ fl, Q 14 { g with rax := BitVec.setWidth 64 1#32 } fl V)
    (hn : b0 V g.rdi ≠ 0#8 → ∀ fl, Q 24 (gC V g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f8 hs1 hz hn ⊢
  wpx [W_0, W_9, W_16, o0, o1, o2, Op.cmpmi, V0, gC, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact f0
    | with_reducible exact f8
    | with_reducible exact hs1
    | exact hz (by assumption) _
    | exact hn (by assumption) _
    | apply And.intro
    | intro)

/-- Back from `DeleteFileAlways`: `mov edx, eax; xor edx, 1; mov [rbx], dl; pop rbx` to the `ret` at 37. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 1, Foot Wl (Addr.add g.rbx i)) (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 37
      { g with
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax ^^^ 1#32),
          rbx := rdq(Vm V g, g.rsp), rsp := g.rsp + 8 } fl (Vm V g)) :
    W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw hl0 h ⊢
  wpx [W_29, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CTempFile::Remove ()` (`this` = `rdi`) from its entry. `_mustBeDeleted` 0: at the return address with
`eax` = 1, the bytes as they were (`kz`). Else at `DeleteFileAlways`'s entry with the registers `gC`, `rsp` 16 below
the entry's, the bytes `V0` with the return address pushed (`kf`); back at `tfr_at + 29` (`Sv`, `Pr`), at the return
address with `_mustBeDeleted` stored (`Vm`), `edx` its value, the entry's `rbx`, `rsp` 8 above the entry's (`kr`). -/
theorem tfr_ok {Pr : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tfr_at tfr) (hinR : CodeIn L Rmf.rmf_at Rmf.rmf)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tfr_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (f0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 1 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 1 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : ∀ (Z' : State) (t' : Nat), b0 V X.cpu.gpr.rdi = 0#8 → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := BitVec.setWidth 64 1#32, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kf : ∀ (Y : State) (t' : Nat), b0 V X.cpu.gpr.rdi ≠ 0#8 → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (tfr_at.add 29) 8)) →
      Y.cpu.rip = Rmf.rmf_at → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = tfr_at.add 29 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Sv V₁ X.cpu.gpr (e₂.add j₂) → Pr Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), Pr Z V₁ →
      Z.cpu.gpr.rbx = X.cpu.gpr.rdi → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vm V₁ Z.cpu.gpr) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax ^^^ 1#32),
          rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have c16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = tfr_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      (j' = 14 ∧ b0 V X.cpu.gpr.rdi = 0#8 ∧ g' = { X.cpu.gpr with rax := BitVec.setWidth 64 1#32 } ∧ V' = V) ∨
      (j' = 24 ∧ b0 V X.cpu.gpr.rdi ≠ 0#8 ∧ g' = gC V X.cpu.gpr ∧ V' = V0 V X.cpu.gpr)) hK hA hrip'
    (vc_0 f0 f8 hs1 (fun hb _ => Or.inl ⟨rfl, hb, rfl, rfl⟩) (fun hb _ => Or.inr ⟨rfl, hb, rfl, rfl⟩)) ?_
  rintro j' g fl V₁ (⟨rfl, hb, rfl, hV₁⟩ | ⟨rfl, hb, rfl, hV₁⟩) Y t₁ hKY hAY hrY hgY -
  · -- `_mustBeDeleted` 0: the `ret` at 14
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_14 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kz Z' t₂ hb hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgY]
    try rfl
  -- the `call` of `DeleteFileAlways`
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_24 _) hinR (tgt := 0) rmf_lt tgt_24 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hsY, c16, hgY]
  refine kf Y₂ t₂ hb hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `DeleteFileAlways`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzb hsv hPr
  have mz : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 1 ≤ y.toNat ∨ y.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs y 8).map (Vm V₁ Z.cpu.gpr) = (byteAddrs y 8).map V₁ :=
    fun y hy h => Tun.rd_Vst V₁ _ (toBytesLE ((BitVec.setWidth 32 Z.cpu.gpr.rax ^^^ 1#32).setWidth 8) 1) y 8
      (by rw [toBytesLE_length, hzb]; omega) hy (by rw [toBytesLE_length, hzb]; omega)
  have hb1 : rdq(Vm V₁ Z.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [mz (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hsv.1
  have hra' : rdq(Vm V₁ Z.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [mz X.cpu.gpr.rsp hp8 (by omega)]; exact hsv.2
  refine (c_29 prof).run c hin (fun j' g' _ V' => j' = 37 ∧
      g' = { Z.cpu.gpr with
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax ^^^ 1#32),
          rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
      V' = Vm V₁ Z.cpu.gpr) hKZ hAZ hrZ
    (vc_29 (by rw [hzb]; exact fw) (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, e8, hb1], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_37 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra') ?_
  rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V₁ Z' t₅ hPr hzb hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Tfr
