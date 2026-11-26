import FV7z.Cld.Cuts
import FV7z.Close.Holds
import FV7z.Fre.Blocks
import FV7z.Cnc.Blocks
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `__closedir` (PLAN.md §M, M1)

glibc 2.31's `__closedir (dirp)` at `0x663860` in `7zzs` (`sysdeps/posix/closedir.c`; `objdump -d`): a null `dirp`,
`errno` (`Close.errnoAt`) set to `EINVAL` (22) and -1 in `eax` (25 to the `ret` at 44); else `push rbp`, `ebp` =
`dirp->fd` (the 4 bytes at `dirp`), `call free` (12, `Fre.fre_at`), then `edi` = `ebp`, `pop rbp` and a tail jump to
`__close_nocancel` (20, `Cnc.cnc_at`).

`free` is a hypothesis (`kf`), as `alloc->Free` in `Lfp.lfp_ok`: a continuation at its entry, given the run from its
return (`cld_at + 17`, `rsp` 8 below the entry's, `rbp` = `dirp->fd`, the saved `rbp` as it was, and the callee's own
post `Pc`) on; `__close_nocancel`'s entry is `kc`'s.

- `gC`: the registers at the `call`; `fdv`: the 4 bytes at `dirp`.
- `vc_0`, `vc_9`, `vc_17`, `vc_25`: the verification conditions of the pieces.
- `cld_ok`: from the entry to the return address (null) or through `free` to `__close_nocancel`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Cld

/-- The `call` of `free`. -/
def pcall : List Byte := [0xe8, 0xdf, 0xfe, 0xfc, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709354719] 5) := by dec_rfl
theorem wc_12 : pcall <+: cld.drop 12 := by decide +kernel
theorem call_12 (feat : Features) : Dec feat cld 12 (FV7z.mk .call 64 [.rel 18446744073709354719] 5) :=
  Dec.shift (j := 12) (k := 0) (pcall_0 feat) wc_12 (Nat.zero_le _)

/-- The jump to `__close_nocancel`. -/
def pjm : List Byte := [0xe9, 0xa7, 0x26, 0x00, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 9895] 5) := by dec_rfl
theorem wj_20 : pjm <+: cld.drop 20 := by decide +kernel
theorem jmp_20 (feat : Features) : Dec feat cld 20 (FV7z.mk .jmp 64 [.rel 9895] 5) :=
  Dec.shift (j := 20) (k := 0) (pjm_0 feat) wj_20 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_44 : pret <+: cld.drop 44 := by decide +kernel
theorem ret_44 (feat : Features) : Dec feat cld 44 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 44) (k := 0) (pret_0 feat) w_44 (Nat.zero_le _)

/-- `EINVAL` as `errno`'s bytes. -/
abbrev einval : List Byte := toBytesLE (22#32) 4

/-- `dirp->fd`: the 4 bytes at `dirp`. -/
abbrev fdv (V : Addr → Byte) (a : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs a 4).map V)

/-- The registers at the `call`: `rbp` = `dirp->fd`, `rbp` pushed. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs := { g with rbp := (fdv V g.rdi).setWidth 64, rsp := g.rsp - 8 }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov ebp, [rdi]`. -/
theorem vc_9 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (hx : (byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) = (byteAddrs g.rdi 4).map V) :
    W_9 fb F Wl (fun j g' _ V' => j = 12 ∧ g' = gC V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst fa hx ⊢
  wpx [W_9, o1, gC, fdv, hx]
  repeat' (first | exact hst | exact fa | apply And.intro | intro _)
  all_goals first | rfl | simp only [hx]

/-- `mov edi, ebp; pop rbp`. -/
theorem vc_17 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 20 { g with rdi := (g.rbp.setWidth 32).setWidth 64, rbp := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) :
    W_17 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_17, o2]
  repeat' (first | exact hl | exact h _ | apply And.intro | intro _)

/-- The null `dirp`: `errno` = `EINVAL`, `eax` -1. -/
theorem vc_25 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 44 ∧ g' = { g with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) einval)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, o3, Op.stfi]
  first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, by rw [show BitVec.setWidth 64 4294967295#32 = 4294967295#64 by decide]⟩

-- The pieces past the branch stay folded: `apply And.intro` would otherwise unfold them.
attribute [local irreducible] W_9 W_25

/-- `test rdi, rdi; je`: to 25 when `dirp` is null, else to 9. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h25 : g.rdi = 0#64 → ∀ fl, W_25 fb F Wl Q g fl V) (h9 : g.rdi ≠ 0#64 → ∀ fl, W_9 fb F Wl Q g fl V) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h25 h9 ⊢
  wpx [W_0, o0, BitVec.and_self]
  all_goals (try intro _)
  refine ⟨fun hc => h25 ?_ _, fun hc => h9 ?_ _⟩ <;> simpa using hc

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__closedir (dirp)` from its entry. Null: at the return address, the return address popped, `errno` = `EINVAL`
and `eax` -1 (`k0`). Else at `free`'s entry with the registers `gC` (`rdi` = `dirp`), `rsp` 16 below the entry's and
`rbp` and the return address into `__closedir` pushed (`kf`); if `free` returns to `cld_at + 17` with `rsp` and `rbp`
as at its entry and the saved `rbp` as it was, the run reaches `__close_nocancel`'s entry with `edi` = `dirp->fd`
and `rbp`, `rsp` restored (`kc`). -/
theorem cld_ok {fb : Addr} {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L cld_at cld) (hinF : CodeIn L Fre.fre_at Fre.fre)
    (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = cld_at)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k0 : X.cpu.gpr.rdi = 0#64 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) einval) →
      Z.cpu.gpr = { X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hdp : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (kf : X.cpu.gpr.rdi ≠ 0#64 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (cld_at.add 17) 8)) →
      Y.cpu.rip = Fre.fre_at → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = cld_at.add 17 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 →
        Z.cpu.gpr.rbp = (fdv V X.cpu.gpr.rdi).setWidth 64 → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kc : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V' → Y.cpu.rip = Cnc.cnc_at →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := (Z.cpu.gpr.rbp.setWidth 32).setWidth 64, rbp := X.cpu.gpr.rbp,
        rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = cld_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : X.cpu.gpr.rdi = 0#64
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 44 ∧ g' = { X.cpu.gpr with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) einval)
      hK hA hrip' (vc_0 (fun _ _ => vc_25 fe) fun h => absurd h0 h) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_44 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : einval.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + einval.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + einval.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) einval X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact k0 h0 Z' t₃ hKZ' hrZ' hAZ' (by rw [hgZ', hgZ] <;> rfl)
  -- not null
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hx : (byteAddrs X.cpu.gpr.rdi 4).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) =
      (byteAddrs X.cpu.gpr.rdi 4).map V :=
    Tun.rd_Vst V _ _ _ 4 (by rw [toBytesLE_length, tn8]; omega) hq (by rw [toBytesLE_length, tn8]; omega)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- to the `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 12 ∧ g' = gC V X.cpu.gpr ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) hK hA hrip'
    (vc_0 (fun h => absurd h h0) fun _ _ => vc_9 hs1 fa hx) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_12 _) hinF (Fre.lt_len (j := 0) (by decide))
    (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
  refine kf h0 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `free`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hPc
  refine (c_17 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 20 ∧
      g' = { Z.cpu.gpr with rdi := (Z.cpu.gpr.rbp.setWidth 32).setWidth 64, rbp := X.cpu.gpr.rbp,
        rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKZ hAZ hrZ
    (vc_17 (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, hb, e8], rfl⟩) ?_
  rintro j' g₃ fl₃ V₃ ⟨rfl, rfl, hV₃⟩ U t₃ hKU hAU hrU hgU -
  subst V₃
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_20 _) hinC (Cnc.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  exact kc Z V' Y₄ t₄ hPc hK₄ hA₄ (by rw [hr₄, addr_add_zero]) (by rw [hg₄, hgU])

end FV7z.Cld
