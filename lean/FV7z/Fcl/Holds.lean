import FV7z.Fcl.Cuts
import FV7z.Close.Holds
import FV7z.Startup.StrAt
/-!
# `CFileBase::Close` closes its descriptor (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NIO::CFileBase::Close ()` at `0x456030` in `7zzs`: `push rbx`, `rbx` = `this`,
`edi` = `_handle` (the 4 bytes at `this`), `eax` = 1; if `_handle` is -1, `pop rbx; ret` (46); else `call __close`
(20, `Close.close_ok`), after which the run goes on from its own start; `eax` = 0 when `close`'s `eax` is not 0,
else `_handle` = -1 and `eax` = 1 (25, 35); `pop rbx; ret` (46).

- `vc_0`, `vc_25`, `vc_46`: the verification conditions of the three pieces, for any `Q`.
- `tail`: from 46 (`pop rbx; ret`) to the return address.
- `mid`: from 25, after `__close`, to the return address.
- `fclose_ok`: called with `_handle` -1 the run reaches the return address with `eax` 1; else after `close` of
  `_handle` it reaches it with `Str.Back` of the registers at the entry and either `_handle` = -1 and `eax` 1 (the
  kernel's answer 0) or `eax` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fcl

/-- The `call` of `__close`. -/
def pcall : List Byte := [0xe8, 0x67, 0x93, 0x1a, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1741671] 5) := by dec_rfl
theorem wc_20 : pcall <+: fcl.drop 20 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat fcl 20 (FV7z.mk .call 64 [.rel 1741671] 5) :=
  Dec.shift (j := 20) (k := 0) (pcall_0 feat) wc_20 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_47 : pret <+: fcl.drop 47 := by decide +kernel
theorem ret_47 (feat : Features) : Dec feat fcl 47 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 47) (k := 0) (pret_0 feat) w_47 (Nat.zero_le _)

theorem xz (w : BitVec 32) : BitVec.setWidth 64 (w ^^^ w) = 0#64 := by
  first | simp | (rw [BitVec.xor_self]; decide)

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rbx, rdi; mov edi, [rdi]; mov eax, 1; cmp edi, -1; je`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (hm1 : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) = 4294967295#32 →
      ∀ fl, Q 46 { g with rax := BitVec.setWidth 64 1#32, rbx := g.rdi, rsp := g.rsp - 8,
        rdi := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)))) }
        fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)))
    (hne : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) ≠ 4294967295#32 →
      ∀ fl, Q 20 { g with rax := BitVec.setWidth 64 1#32, rbx := g.rdi, rsp := g.rsp - 8,
        rdi := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)))) }
        fl (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.ld]
  exact ⟨hst, fa, fun h => hm1 (of_decide_eq_true h) _, fun h => hne (of_decide_eq_false h) _⟩

/-- `mov r8d, eax; xor eax, eax; test r8d, r8d; jne`, then `mov [rbx], -1; mov eax, 1`. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h0 : BitVec.setWidth 32 g.rax = 0 → (∀ i < 4, Foot Wl (Addr.add g.rbx i)) ∧
      ∀ fl, Q 46 { g with rax := BitVec.setWidth 64 1#32, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) } fl
        (Vst V g.rbx (toBytesLE (4294967295#32) 4)))
    (h1 : BitVec.setWidth 32 g.rax ≠ 0 → ∀ fl, Q 46 { g with
      rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax ^^^ BitVec.setWidth 32 g.rax),
      r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) } fl V) :
    W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, W_35, o1, o2, Op.sti]
  intro af af1
  refine ⟨fun h => h1 ?_ _, fun h => ?_⟩
  · intro e
    rw [e] at h
    exact absurd h (by decide)
  · have e : BitVec.setWidth 32 rax = 0 := by
      first
      | simpa using h
      | (simp only [BitVec.and_self, Bool.not_eq_false', beq_iff_eq] at h; exact h)
    exact ⟨(h0 e).1, (h0 e).2 _⟩

/-- `pop rbx`. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl8 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 47 { g with rbx := ofBytesLE 64 ((byteAddrs g.rsp 8).map V), rsp := g.rsp + 8 } fl V) :
    W_46 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_46, o3]
  exact ⟨hl8, h _⟩

/-- What `fclose_ok`'s continuation gets back of the registers. -/
theorem back_of {g Zg g' : Gprs} {a r8v : BitVec 64}
    (h : g' = { Zg with rax := a, rbx := g.rbx, rsp := g.rsp + 8, r8 := r8v })
    (h1 : Zg.rbp = g.rbp) (h2 : Zg.r12 = g.r12) (h3 : Zg.r13 = g.r13) (h4 : Zg.r14 = g.r14) (h5 : Zg.r15 = g.r15) :
    Str.Back g g' := by
  subst h
  unfold Str.Back
  exact ⟨rfl, rfl, h1, h2, h3, h4, h5⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 46 (`pop rbx; ret`), `rsp` = `p - 8`, to the return address at `p`. -/
theorem tail {s₁ Y : State} {t : Nat} {V' : Addr → Byte} (c' : Seg prof F Wl L s₁ o) (hin : CodeIn L fcl_at fcl)
    (hK : KeptW Wl s₁ Y) (hA : Agree F Y.proc.mm.mem V') (hr : Y.cpu.rip = fcl_at.add 46) {p : Addr}
    (hsp : Y.cpu.gpr.rsp = p - 8) (h8 : ∀ i < 8, Foot F.data (Addr.add (p - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add p i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs p 8).map V') = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { Y.cpu.gpr with rbx := ofBytesLE 64 ((byteAddrs (p - 8) 8).map V'), rsp := p + 8 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have e8 : p - 8 + 8 = p := BitVec.sub_add_cancel p 8
  refine (c_46 prof).run c' hin (fun j' g' _ V'' => j' = 47 ∧
      g' = { Y.cpu.gpr with rbx := ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V'), rsp := Y.cpu.gpr.rsp + 8 } ∧
      V'' = V') hK hA hr (vc_46 (by rw [hsp]; exact h8) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₁ hKU hAU hrU hgU -
  subst V₂
  have hgU' : U.cpu.gpr = { Y.cpu.gpr with rbx := ofBytesLE 64 ((byteAddrs (p - 8) 8).map V'), rsp := p } := by
    rw [hgU, hsp, e8]
  have hlU : ∀ i < 8, Foot F.data (Addr.add U.cpu.gpr.rsp i) := by
    rw [hgU']
    exact hl
  have hrU' : ofBytesLE 64 ((byteAddrs U.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hgU']
    exact hra
  refine c'.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_47 _) hlU hin₂ h₂ hrU' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hgU']
  try rfl

/-- From 25, after `__close` (`rsp` = `p - 8`, `rbx` = `this` = `d`), to the return address at `p`: `_handle` = -1
and `eax` = 1 when `close`'s `eax` is 0 (`k0`), else `eax` = 0 (`k1`); `rbx` popped. -/
theorem mid {s₁ Z : State} {t : Nat} {Vz : Addr → Byte} (c' : Seg prof F Wl L s₁ o) (hin : CodeIn L fcl_at fcl)
    (hK : KeptW Wl s₁ Z) (hA : Agree F Z.proc.mm.mem Vz) (hr : Z.cpu.rip = fcl_at.add 25) {p d b : Addr}
    (hp : 8 ≤ p.toNat) (hp8 : p.toNat + 8 ≤ 2 ^ 64) (hsp : Z.cpu.gpr.rsp = p - 8) (hbx : Z.cpu.gpr.rbx = d)
    (hd8 : d.toNat + 4 ≤ 2 ^ 64) (hdp : d.toNat + 4 ≤ p.toNat - 8 ∨ p.toNat + 8 ≤ d.toNat)
    (fw : ∀ i < 4, Foot Wl (Addr.add d i)) (h8 : ∀ i < 8, Foot F.data (Addr.add (p - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add p i)) (hb : ofBytesLE 64 ((byteAddrs (p - 8) 8).map Vz) = b)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs p 8).map Vz) = e₂.add j₂)
    (k0 : BitVec.setWidth 32 Z.cpu.gpr.rax = 0 → ∀ Z' t', KeptW Wl s₁ Z' →
      Agree F Z'.proc.mm.mem (Vst Vz d (toBytesLE (4294967295#32) 4)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := BitVec.setWidth 64 1#32, rbx := b, rsp := p + 8,
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) } →
      GoG prof L o gev gP gE Z' t')
    (k1 : BitVec.setWidth 32 Z.cpu.gpr.rax ≠ 0 → ∀ Z' t', KeptW Wl s₁ Z' → Agree F Z'.proc.mm.mem Vz →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := b, rsp := p + 8,
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  have hlt := p.isLt
  have tn8 : (p - 8).toNat = p.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have hbl : (toBytesLE (4294967295#32) 4).length = 4 := toBytesLE_length _ _
  have hq8 : (p - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  have hd1 : d.toNat + (toBytesLE (4294967295#32) 4).length ≤ 2 ^ 64 := by rw [hbl]; exact hd8
  have hd2 : d.toNat + (toBytesLE (4294967295#32) 4).length ≤ (p - 8).toNat ∨ (p - 8).toNat + 8 ≤ d.toNat := by
    rw [hbl, tn8]; omega
  have hd3 : d.toNat + (toBytesLE (4294967295#32) 4).length ≤ p.toNat ∨ p.toNat + 8 ≤ d.toNat := by
    rw [hbl]; omega
  refine (c_25 prof).run c' hin (fun j' g' _ V' => j' = 46 ∧ ∃ a, g' = { Z.cpu.gpr with rax := a,
      r8 := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) } ∧
      ((BitVec.setWidth 32 Z.cpu.gpr.rax = 0 ∧ a = BitVec.setWidth 64 1#32 ∧
        V' = Vst Vz Z.cpu.gpr.rbx (toBytesLE (4294967295#32) 4)) ∨
       (BitVec.setWidth 32 Z.cpu.gpr.rax ≠ 0 ∧ a = 0#64 ∧ V' = Vz))) hK hA hr
    (vc_25 (fun hw => ⟨by rw [hbx]; exact fw, fun _ => ⟨rfl, _, rfl, .inl ⟨hw, rfl, rfl⟩⟩⟩)
      (fun hw _ => ⟨rfl, _, rfl, .inr ⟨hw, xz _, rfl⟩⟩)) ?_
  rintro j' g fl V' ⟨rfl, a, rfl, ⟨hw, rfl, rfl⟩ | ⟨hw, rfl, hv⟩⟩ Y t₁ hKY hAY hrY hgY -
  · rw [hbx] at hAY
    have hsY : Y.cpu.gpr.rsp = p - 8 := by rw [hgY]; exact hsp
    have hb' : ofBytesLE 64 ((byteAddrs (p - 8) 8).map (Vst Vz d (toBytesLE (4294967295#32) 4))) = b := by
      rw [Tun.rd_Vst Vz d (toBytesLE (4294967295#32) 4) (p - 8) 8 hd1 hq8 hd2]
      exact hb
    have hra' : ofBytesLE 64 ((byteAddrs p 8).map (Vst Vz d (toBytesLE (4294967295#32) 4))) = e₂.add j₂ := by
      rw [Tun.rd_Vst Vz d (toBytesLE (4294967295#32) 4) p 8 hd1 hp8 hd3]
      exact hra
    refine tail c' hin hKY hAY hrY hsY h8 hl hin₂ h₂ hra' fun Z' t' hK' hA' hr' hg' => k0 hw Z' t' hK' hA' hr' ?_
    rw [hg', hb', hgY]
    try rfl
  · subst V'
    have hsY : Y.cpu.gpr.rsp = p - 8 := by rw [hgY]; exact hsp
    refine tail c' hin hKY hAY hrY hsY h8 hl hin₂ h₂ hra fun Z' t' hK' hA' hr' hg' => k1 hw Z' t' hK' hA' hr' ?_
    rw [hg', hb, hgY]
    try rfl

variable {s₀ X : State} {t : Nat} {V : Addr → Byte}

/-- `CFileBase::Close ()` from its entry to the return address. With `_handle` (the 4 bytes at `this` = `rdi`) -1:
`eax` = 1 (`kn`). Else (`kc`): `close (_handle)` from `Y` answers `r`, the run goes on from the state after it, `S`,
its own start, to the return address with `Str.Back` of the registers at the entry and, by `r`, `errno` set and
`eax` 0, or `_handle` = -1 and `eax` 1 (`r`'s low 32 bits 0), or `eax` 0; below `rsp` the return address into
`CFileBase::Close` and `rbx` are left. -/
theorem fclose_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L fcl_at fcl) (hinc : CodeIn L cls_at cls) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fcl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hd8 : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hdp : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hmt : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map V) = 0) (fm : ∀ i < 4, Foot F.data ((fb + 24#64).add i))
    (hfb : (fb + 24#64).toNat + 4 ≤ 2 ^ 64)
    (hfd : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 24#64).toNat)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hse : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kn : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V) = 4294967295#32 → ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := BitVec.setWidth 64 1#32,
        rdi := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V)), rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kc : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V) ≠ 4294967295#32 →
      ∀ (Y S Z : State) (r : BitVec 64) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y →
      Y.cpu.gpr.rdi = BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V)) →
      (∃ t₁, (closeRes o t₁ Y).1 = r) → S = sysSt (closeSt Y) 2 r → Seg prof F Wl L S o → KeptW Wl S Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr →
      (CloseErr r → V' = Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (fcl_at.add 25) 8)) (errnoAt fb) (errnoB r) ∧ Z.cpu.gpr.rax = 0#64) →
      (¬ CloseErr r → BitVec.setWidth 32 r = 0 → V' = Vst (Vst (Vst V (X.cpu.gpr.rsp - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add 25) 8)) X.cpu.gpr.rdi
        (toBytesLE (4294967295#32) 4) ∧ Z.cpu.gpr.rax = BitVec.setWidth 64 1#32) →
      (¬ CloseErr r → BitVec.setWidth 32 r ≠ 0 → V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))
        (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add 25) 8) ∧ Z.cpu.gpr.rax = 0#64) →
      GoG prof L o (gev ++ [clsEv { X.cpu.gpr with
        rdi := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V)) } r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e3 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have hp' : 8 ≤ X.cpu.gpr.rsp.toNat := by omega
  have hdp' : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat := by
    omega
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the bytes stored by `push rbx` and the `call`
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  have m16 : ∀ (W : Addr → Byte) (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ x.toNat) →
      (byteAddrs x n).map (Vst W (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8)) =
        (byteAddrs x n).map W :=
    fun W x n hx h => Tun.rd_Vst W _ _ x n (by rw [toBytesLE_length, tn16]; omega) hx
      (by rw [toBytesLE_length, tn16]; omega)
  have hx : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) =
      ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V) := by
    rw [m8 X.cpu.gpr.rdi 4 hd8 (by omega)]
  have hb1 : ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp - 8) 8).map
      (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) = X.cpu.gpr.rbx := by
    have hq : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
    rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) (toBytesLE_length _ _) hq]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hr1 : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map
      (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) = e₂.add j₂ := by
    rw [m8 X.cpu.gpr.rsp 8 hp8 (by omega)]
    exact hra
  -- to the `je`
  refine (c_0 prof).run c hin (fun j' g' _ V' => g' = { X.cpu.gpr with rax := BitVec.setWidth 64 1#32,
      rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8, rdi := BitVec.setWidth 64 (ofBytesLE 32
        ((byteAddrs X.cpu.gpr.rdi 4).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)))) } ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) ∧
      ((j' = 46 ∧ ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map
          (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) = 4294967295#32) ∨
       (j' = 20 ∧ ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map
          (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) ≠ 4294967295#32)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 fa (fun h _ => ⟨rfl, rfl, .inl ⟨rfl, h⟩⟩) (fun h _ => ⟨rfl, rfl, .inr ⟨rfl, h⟩⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, ⟨rfl, hm⟩ | ⟨rfl, hm⟩⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  · -- `_handle` is -1
    have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₁]
    refine tail c hin hK₁ hA₁ hr₁ hsp₁ h8 hl hin₂ h₂ hr1 fun Z t' hKZ hAZ hrZ hgZ => ?_
    refine kn (by rw [← hx]; exact hm) Z t' hKZ hAZ hrZ ?_
    rw [hgZ, hb1, hg₁, hx]
    try rfl
  -- `call __close`
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₁]
  have hs₁ : ∀ i < 8, Foot Wl (Addr.add (Y₁.cpu.gpr.rsp - 8) i) := by rw [hsp₁, e16]; exact hs2
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_20 _) hinc (Close.lt_len (by decide)) (by decide) hs₁ ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, e16] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 16 := by rw [hg₂]; rfl
  have hf1 : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat - 8 ≤ (fb + 24#64).toNat := by
    omega
  have hf2 : (fb + 24#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 24#64).toNat := by
    omega
  have hmt₂ : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map (Vst (Vst V (X.cpu.gpr.rsp - 8)
      (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8))) = 0 := by
    rw [m16 _ (fb + 24#64) 4 hfb hf1, m8 (fb + 24#64) 4 hfb hf2]
    exact hmt
  have hl₂ : ∀ i < 8, Foot F.data (Addr.add Y₂.cpu.gpr.rsp i) := by
    rw [hsp₂]; exact fun i hi => c.hws _ (hs2 i hi)
  have hq₂ : Y₂.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by rw [hsp₂, tn16]; omega
  have hsa₂ : (errnoAt fb).toNat + 4 ≤ Y₂.cpu.gpr.rsp.toNat ∨ Y₂.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by
    rw [hsp₂, tn16]; omega
  have hra₂ : ofBytesLE 64 ((byteAddrs Y₂.cpu.gpr.rsp 8).map (Vst (Vst V (X.cpu.gpr.rsp - 8)
      (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8))) = fcl_at.add 25 := by
    have hq : (X.cpu.gpr.rsp - 16).toNat + 8 ≤ 2 ^ 64 := by rw [tn16]; omega
    rw [hsp₂, Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8) (toBytesLE_length _ _) hq]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  refine Close.close_ok c hfs hrs hinc hK₂ hA₂ hr₂ hmt₂ fm fe hfe hl₂ hq₂ hsa₂ hin (j₂ := 25) (lt_len (by decide))
    hra₂ ?_
  intro Y S Z r t' hKY hAY hgY hrY hrr hS cS hKZ hrZ hok herr
  have hev : clsEv Y₂.cpu.gpr r = clsEv { X.cpu.gpr with
      rdi := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V)) } r := by
    rw [hg₂, hg₁, hx]
    try rfl
  rw [hev]
  have hm' : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V) ≠ 4294967295#32 := by rw [← hx]; exact hm
  have hYdi : Y.cpu.gpr.rdi = BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map V)) := by
    rw [hgY, hg₂, hg₁, hx]
    try rfl
  have hyb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by
    rw [hgY, hg₂, hg₁]
    try rfl
  have hyr : Y.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hgY, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the bytes `rbx` and the return address are read back from
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  have hb2 : ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp - 8) 8).map (Vst (Vst V (X.cpu.gpr.rsp - 8)
      (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8))) = X.cpu.gpr.rbx := by
    rw [m16 _ (X.cpu.gpr.rsp - 8) 8 hq8 (by rw [tn8]; omega)]
    exact hb1
  have hr2 : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (Vst (Vst V (X.cpu.gpr.rsp - 8)
      (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16) (toBytesLE (fcl_at.add (20 + 5)) 8))) = e₂.add j₂ := by
    rw [m16 _ X.cpu.gpr.rsp 8 hp8 (by omega)]
    exact hr1
  by_cases he : CloseErr r
  · obtain ⟨hAZ, hgZ⟩ := herr he
    have hzs : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by
      rw [hgZ]; show Y₂.cpu.gpr.rsp + 8 = _; rw [hsp₂]; exact e3
    have hzb : Z.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgZ]; exact hyb
    have hzr : Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
        Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgZ]; exact hyr
    have hzax : Z.cpu.gpr.rax = 4294967295#64 := by rw [hgZ]; rfl
    have hbe : (errnoB r).length = 4 := toBytesLE_length _ _
    have hE : ∀ (W : Addr → Byte) (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
        ((errnoAt fb).toNat + 4 ≤ x.toNat ∨ x.toNat + n ≤ (errnoAt fb).toNat) →
        (byteAddrs x n).map (Vst W (errnoAt fb) (errnoB r)) = (byteAddrs x n).map W :=
      fun W x n hx' h => Tun.rd_Vst W _ _ x n (by rw [hbe]; exact hfe) hx' (by rw [hbe]; exact h)
    refine mid (p := X.cpu.gpr.rsp) (d := X.cpu.gpr.rdi) (b := X.cpu.gpr.rbx) cS hin hKZ hAZ hrZ hp' hp8 hzs hzb
      hd8 hdp' fw h8 hl ?_ hin₂ h₂ ?_ ?_ ?_
    · rw [hE _ (X.cpu.gpr.rsp - 8) 8 hq8 (by rw [tn8]; omega)]
      exact hb2
    · rw [hE _ X.cpu.gpr.rsp 8 hp8 (by omega)]
      exact hr2
    · intro hw
      exact absurd hw (by rw [hzax]; decide)
    · intro _ Z' t'' hK' hA' hr' hg'
      refine kc hm' Y S Z' r _ t'' hKY hYdi hrr hS cS hK' hA' hr'
        (back_of (Zg := Z.cpu.gpr) hg' hzr.1 hzr.2.1 hzr.2.2.1 hzr.2.2.2.1 hzr.2.2.2.2) (fun _ => ⟨rfl, ?_⟩)
        (fun h => absurd he h) (fun h => absurd he h)
      exact (congrArg Gprs.rax hg').trans rfl
  · obtain ⟨hAZ, hgZ⟩ := hok he
    have hzs : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by
      rw [hgZ]; show Y₂.cpu.gpr.rsp + 8 = _; rw [hsp₂]; exact e3
    have hzb : Z.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgZ]; exact hyb
    have hzr : Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
        Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgZ]; exact hyr
    have hzax : Z.cpu.gpr.rax = r := by rw [hgZ]; rfl
    refine mid (p := X.cpu.gpr.rsp) (d := X.cpu.gpr.rdi) (b := X.cpu.gpr.rbx) cS hin hKZ hAZ hrZ hp' hp8 hzs hzb
      hd8 hdp' fw h8 hl hb2 hin₂ h₂ hr2 ?_ ?_
    · intro hw Z' t'' hK' hA' hr' hg'
      have hw' : BitVec.setWidth 32 r = 0 := by rw [← hzax]; exact hw
      refine kc hm' Y S Z' r _ t'' hKY hYdi hrr hS cS hK' hA' hr'
        (back_of (Zg := Z.cpu.gpr) hg' hzr.1 hzr.2.1 hzr.2.2.1 hzr.2.2.2.1 hzr.2.2.2.2) (fun h => absurd h he)
        (fun _ _ => ⟨rfl, ?_⟩) (fun _ h => absurd hw' h)
      exact (congrArg Gprs.rax hg').trans rfl
    · intro hw Z' t'' hK' hA' hr' hg'
      have hw' : BitVec.setWidth 32 r ≠ 0 := by rw [← hzax]; exact hw
      refine kc hm' Y S Z' r _ t'' hKY hYdi hrr hS cS hK' hA' hr'
        (back_of (Zg := Z.cpu.gpr) hg' hzr.1 hzr.2.1 hzr.2.2.1 hzr.2.2.2.1 hzr.2.2.2.2) (fun h => absurd h he)
        (fun _ h => absurd h hw') (fun _ _ => ⟨rfl, ?_⟩)
      exact (congrArg Gprs.rax hg').trans rfl

end FV7z.Fcl
