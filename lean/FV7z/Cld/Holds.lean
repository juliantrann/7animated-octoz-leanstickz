import FV7z.Cld.Cuts
import FV7z.Close.Holds
import FV7z.Sgw.Holds
/-!
# `__closedir` (PLAN.md §M, M1)

glibc 2.31's `__closedir (d)` at `0x663860` in `7zzs` (`sysdeps/posix/closedir.c`): a null `d` sets `errno`
(`fs:-0x48`, `Close.errnoAt`) to `EINVAL` (22) and returns -1 in `eax`; else `push rbp`, `ebp` = `d->fd` (the 4 bytes
at `d`), `call free` (`0x633750`, 12), `mov edi, ebp; pop rbp` and a tail jump (20) to `__close_nocancel`
(`0x665f20`, `Cnc`) with `rdi` = `fd`.

The callees are hypotheses: `free` a continuation at its entry (`kf`), given the run from its return (`cld_at + 17`,
`rsp` 8 below the entry's, `rbp` = `fd`, the saved `rbp` as it was, and the callee's own post `Pc`);
`__close_nocancel` a continuation at its entry (`kc`).

- `fdOf V g`: `d->fd`, zero-extended; `gC V g`: the registers at the `call`.
- `vc_z`, `vc_n`, `vc_17`: the verification conditions of the pieces.
- `cld_ok`: with `d` null to the return address with `errno` = `EINVAL` and `eax` -1 (`ke`); else through `free` to
  `__close_nocancel`'s entry with `rdi` = `fd`, `rsp` and `rbp` as at the entry (`kf`, `kc`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Close (errnoAt)
namespace FV7z.Cld

theorem cld_12 : ∀ feat, Dec feat cld 12 (FV7z.mk .call 64 [.rel 18446744073709354719] 5) := by intro feat f; rfl
theorem cld_20 : ∀ feat, Dec feat cld 20 (FV7z.mk .jmp 64 [.rel 9895] 5) := by intro feat f; rfl
theorem cld_44 : ∀ feat, Dec feat cld 44 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

theorem lt_len {j : Nat} (h : j < 45) : j < cld.length := cld_length ▸ h

/-- `d->fd`, the 4 bytes at `d`, zero-extended. -/
abbrev fdOf (V : Addr → Byte) (g : Gprs) : BitVec 64 := (ofBytesLE 32 ((byteAddrs g.rdi 4).map V)).setWidth 64

/-- The registers at the `call`: `rbp` pushed, `rbp` = `d->fd`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rsp := g.rsp - 8
    rbp := fdOf V g }

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide)),
    Nat.mod_eq_of_lt x.isLt]

variable {F : Footprint} {Wl : List Rgn}

/-- `d` null: to the `ret`, `errno` = `EINVAL`, `eax` -1. -/
theorem vc_z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi = 0)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 44 ∧ g' = { g with rax := 4294967295#64 } ∧
      V' = Vst V (errnoAt fb) Sgw.einval) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_0, W_25, W_9, o0, o1, o3, Op.stfi]
  first
  | done
  | exact ⟨fun _ => ⟨fe, rfl⟩, fun hh => absurd hh (by decide)⟩
  | exact fun _ => ⟨fe, rfl⟩
  | exact ⟨fe, rfl⟩
  | repeat' (first | rfl | exact fe | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh (by decide)) | intro _)

/-- `d` not null: `push rbp; mov ebp, [rdi]`, to the `call`. -/
theorem vc_n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi ≠ 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (hx : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbp 8))) =
      ofBytesLE 32 ((byteAddrs g.rdi 4).map V)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 12 ∧ g' = gC V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hst fa hx ⊢
  wpx [W_0, W_25, W_9, o0, o1, o3, Op.stfi, BitVec.and_self, beq_iff_eq, h, gC, fdOf, hx]
  first
  | done
  | exact ⟨hst, fa⟩
  | exact ⟨fun hh => absurd hh h, hst, fa⟩
  | exact fun _ => ⟨hst, fa⟩
  | repeat' (first | rfl | exact hst | exact fa | (simpa using fa) | (refine ⟨?_, ?_⟩) |
      (intro hh; exact absurd hh h) | intro _)

/-- Back from `free`: `mov edi, ebp; pop rbp`, to the jump. -/
theorem vc_17 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_17 fb F Wl (fun j' g' _ V' => j' = 20 ∧
      g' = { g with
        rdi := (g.rbp.setWidth 32).setWidth 64
        rsp := g.rsp + 8
        rbp := ofBytesLE 64 ((byteAddrs g.rsp 8).map V) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  wpx [W_17, o2]
  first
  | done
  | exact hl
  | exact ⟨hl, rfl⟩
  | repeat' (first | rfl | exact hl | (refine ⟨?_, ?_⟩) | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__closedir (d)` from its entry. `d` null: at the return address, the return address popped, `errno` = `EINVAL`
and `eax` -1 (`ke`). `d` not null: at `free`'s entry with the registers `gC` (`rsp` 16 below the entry's) and the
bytes with `rbp` and the return address into `__closedir` pushed (`kf`); if `free` returns to `cld_at + 17` with `rsp`
as at its entry, `rbp` = `fd` and the saved `rbp` as it was, the run reaches `__close_nocancel`'s entry with
`rdi` = `fd`, `rsp` and `rbp` as at the entry of `__closedir` (`kc`). -/
theorem cld_ok {fb : Addr} {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L cld_at cld) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = cld_at) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (ke : X.cpu.gpr.rdi = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) Sgw.einval) →
      Z.cpu.gpr = { X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hda : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {codeF : List Byte} (hinF : CodeIn L 0x633750#64 codeF) (hF0 : 0 < codeF.length)
    {codeC : List Byte} (hinC : CodeIn L 0x665f20#64 codeC) (hC0 : 0 < codeC.length)
    (kf : X.cpu.gpr.rdi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (cld_at.add 17) 8)) →
      Y.cpu.rip = 0x633750#64 → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = cld_at.add 17 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbp = fdOf V X.cpu.gpr →
        ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp - 8) 8).map V') = X.cpu.gpr.rbp → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kc : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = 0x665f20#64 →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rdi := fdOf V X.cpu.gpr
        rsp := X.cpu.gpr.rsp
        rbp := X.cpu.gpr.rbp } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  by_cases h0 : X.cpu.gpr.rdi = 0
  · -- `d` null: `errno`, `ret`
    refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 44 ∧ g' = { X.cpu.gpr with rax := 4294967295#64 } ∧
        V' = Vst V (errnoAt fb) Sgw.einval) hK hA (by rw [addr_add_zero]; exact hrip) (vc_z h0 fe) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V₁
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (cld_44 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : Sgw.einval.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + Sgw.einval.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + Sgw.einval.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) Sgw.einval X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact ke h0 Z' t₂ hKZ' hrZ' hAZ' (by rw [hgZ', hgZ] <;> rfl)
  · -- `d` not null
    have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
    have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
    have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, tn8, tn16]
      simp <;> omega
    have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
    have hx : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map
        (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8))) =
        ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V) := by
      rw [Tun.rd_Vst V _ _ X.cpu.gpr.rdi 4 (by rw [toBytesLE_length, tn8]; omega) hq
        (by rw [toBytesLE_length, tn8]; omega)]
    -- to the `call`
    refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 12 ∧ g' = gC V X.cpu.gpr ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_n h0 hs1 fa hx) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY] <;> rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (cld_12 _) hinF hF0 (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
    refine kf h0 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `free`
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hPc
    have h8 : ∀ i < 8, Foot F.data (Addr.add Z.cpu.gpr.rsp i) := fun i hi => by rw [hzs]; exact c.hws _ (hs1 i hi)
    have h17 := vc_17 (fb := fb) (F := F) (Wl := Wl) (f := Z.cpu.rflags) (V := V') h8
    refine (c_17 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 20 ∧
        g' = { Z.cpu.gpr with
          rdi := fdOf V X.cpu.gpr
          rsp := X.cpu.gpr.rsp
          rbp := X.cpu.gpr.rbp } ∧ V'' = V') hKZ hAZ hrZ (wp_mono o2 ?_ h17) ?_
    · rintro g' fl V'' ⟨hj, hg, hv⟩
      exact ⟨hj, by rw [hg, hzb, sw32, hzs, e8, hb], hv⟩
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (cld_20 _) hinC (tgt := 0) hC0 (by decide) ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact kc Z V' Z' t₄ hPc hKZ' hAZ' (by rw [hrZ', addr_add_zero]) (hgZ'.trans hgU)

end FV7z.Cld
