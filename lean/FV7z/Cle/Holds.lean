import FV7z.Cle.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CArcErrorInfo::ClearErrors` (PLAN.md §M, M1)

7-Zip 26.06's `CArcErrorInfo::ClearErrors ()` at `0x5d2b40` in `7zzs` (`CPP/7zip/UI/Common/OpenArchive.h`;
`objdump -d`): for the object at `p` = `rdi`, 0 in the 8 bytes at `p` (the flags), the 4 at `p + 8`, the 8 at
`p + 16` (the tail size); the two `UString`s (characters at `p + 24` and `p + 40`, lengths at `p + 32` and `p + 48`)
emptied: length 0 and the first character 0. `rax` is left with the second string's characters. One `ret` (60).

- `s1`, `s2`: the strings' characters as read; `V5`: the bytes before the second read; `M`: the bytes at the end.
- `vc_0`: from the entry to the `ret`; `cle_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cle

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_60 : pret <+: cle.drop 60 := by decide +kernel
theorem ret_60 (feat : Features) : Dec feat cle 60 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 60) (k := 0) (pret_0 feat) w_60 (Nat.zero_le _)

/-- The first string's characters. -/
abbrev s1 (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 24#64)
/-- The bytes after the first five stores. -/
abbrev V5 (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V
    p (toBytesLE 0#64 8))
    (p + 8#64) (toBytesLE 0#32 4))
    (p + 16#64) (toBytesLE 0#64 8))
    (p + 32#64) (toBytesLE 0#32 4))
    (s1 V p) (toBytesLE 0#32 4)
/-- The second string's characters, read after the five stores. -/
abbrev s2 (V : Addr → Byte) (p : Addr) : Addr := rdq(V5 V p, p + 40#64)
/-- The bytes at the end. -/
abbrev M (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (V5 V p) (p + 48#64) (toBytesLE 0#32 4)) (s2 V p) (toBytesLE 0#32 4)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The loads and stores, from the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i)) (w0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i)) (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (w32 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 32#64) i)) (ws1 : ∀ i < 4, Foot Wl (Addr.add (s1 V g.rdi) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 40#64) i)) (w48 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 48#64) i))
    (ws2 : ∀ i < 4, Foot Wl (Addr.add (s2 V g.rdi) i)) :
    wp F Wl o0 (fun g' _ V' => g' = { g with rax := s2 V g.rdi } ∧ V' = M V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 w0 w8 w16 w32 ws1 f40 w48 ws2 ⊢
  wpx [o0, M, V5, s1, s2]
  all_goals first
  | exact ⟨f24, w0, w8, w16, w32, ws1, f40, w48, ws2⟩
  | exact ⟨f24, w0, w8, w16, w32, ws1, f40, w48, ws2, rfl, rfl⟩
  | (refine ⟨f24, w0, w8, w16, w32, ws1, f40, w48, ws2, ?_⟩; done)

/-- `CArcErrorInfo::ClearErrors ()` from its entry to the return address: the bytes `M` of the object at `rdi`, `rax`
the second string's characters. -/
theorem cle_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cle_at cle) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cle_at)
    (f24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (w32 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (w48 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (ws1 : ∀ i < 4, Foot Wl (Addr.add (s1 V X.cpu.gpr.rdi) i))
    (ws2 : ∀ i < 4, Foot Wl (Addr.add (s2 V X.cpu.gpr.rdi) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(M V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (M V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := s2 V X.cpu.gpr.rdi }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 60 ∧ g' = { X.cpu.gpr with rax := s2 V X.cpu.gpr.rdi } ∧ V' = M V X.cpu.gpr.rdi) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 f24 w0 w8 w16 w32 ws1 f40 w48 ws2)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_60 _) (by rw [hspY]; exact hl) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hspY, hgY])

end FV7z.Cle
