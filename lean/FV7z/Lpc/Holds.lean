import FV7z.Lpc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CLocalProgress::CLocalProgress` (PLAN.md §M, M1)

7-Zip 26.06's `CLocalProgress::CLocalProgress ()` at `0x461fa0` in `7zzs` (`CPP/7zip/Common/ProgressUtils.cpp`;
`objdump -d`): the object at `rdi` gets its vtable pointer (`0x783be0`) at 0, 0 in the 4 bytes at 8 and in the 8
bytes at 16, 24, 32, 40 and 48, and 1 in the bytes at 12 and 13; `rax` is left with 257. One `ret` (74).

- `M`: the bytes after the constructor; `vc_0`: from the entry to the `ret`.
- `lpc_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lpc

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_74 : pret <+: lpc.drop 74 := by decide +kernel
theorem ret_74 (feat : Features) : Dec feat lpc 74 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 74) (k := 0) (pret_0 feat) w_74 (Nat.zero_le _)

/-- The bytes after the constructor of the object at `p`, in the order of the stores. -/
abbrev M (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (p + 8#64) (toBytesLE 0#32 4))
    (p + 16#64) (toBytesLE 0#64 8))
    (p + 24#64) (toBytesLE 0#64 8))
    p (toBytesLE 7879648#64 8))
    (p + 12#64) (toBytesLE 257#16 2))
    (p + 32#64) (toBytesLE 0#64 8))
    (p + 40#64) (toBytesLE 0#64 8))
    (p + 48#64) (toBytesLE 0#64 8)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The stores, from the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (w12 : ∀ i < 2, Foot Wl (Addr.add (g.rdi + 12#64) i)) (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 24#64) i)) (w32 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 32#64) i))
    (w40 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 40#64) i)) (w48 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 48#64) i)) :
    wp F Wl o0 (fun g' _ V' => (∃ a, g' = { g with rax := a }) ∧ V' = M V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w8 w12 w16 w24 w32 w40 w48 ⊢
  wpx [o0, M]
  all_goals first
  | exact ⟨w8, w16, w24, w0, w12, w32, w40, w48, ⟨_, rfl⟩⟩
  | exact ⟨w8, w16, w24, w0, w12, w32, w40, w48, ⟨_, rfl⟩, rfl⟩
  | exact ⟨w8, w16, w24, w0, w12, w32, w40, w48⟩
  | (refine ⟨w8, w16, w24, w0, w12, w32, w40, w48, ?_⟩; done)

/-- `CLocalProgress::CLocalProgress ()` from its entry to the return address: the bytes `M` of the object at `rdi`,
`rax` changed. -/
theorem lpc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lpc_at lpc) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lpc_at)
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w12 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (w40 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (w48 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(M V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (M V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ → (∃ a, Z.cpu.gpr = { X.cpu.gpr with rax := a }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 74 ∧ (∃ a, g' = { X.cpu.gpr with rax := a }) ∧ V' = M V X.cpu.gpr.rdi) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 w0 w8 w12 w16 w24 w32 w40 w48)) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_74 _) (by rw [hspY]; exact hl) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ ⟨a, by rw [hgZ, hspY, hgY]⟩

end FV7z.Lpc
