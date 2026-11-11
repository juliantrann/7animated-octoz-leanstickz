import FV7z.Gts.Cuts
import FV7z.Tun.Inv
/-!
# `_dl_get_tls_static_info` (PLAN.md G3, startup)

glibc 2.31's `_dl_get_tls_static_info (sizep, alignp)` at `0x66e6c0` in `7zzs`: `*sizep = _dl_tls_static_size`
(`0x7922b0`), `*alignp = _dl_tls_static_align` (`0x7a7ed0`). One stretch of code, to the `ret` (24).

- `gts_ok`: called with the two variables in the footprint's data and the two quadwords in what the run may store
  into, the run reaches the `ret` with the quadwords stored; `rax` is the second, the registers else are as at the
  entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gts

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_24 : pret <+: gts.drop 24 := by decide +kernel
theorem ret_24 (feat : Features) : Dec feat gts 24 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 24) (k := 0) (pret_0 feat) w_24 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the first store. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V g.rdi (toBytesLE rdq(V, 7938736#64) 8)
/-- The bytes at the `ret`. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (V1 V g) g.rsi (toBytesLE rdq(V1 V g, 8027856#64) 8)

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : ∀ i < 8, Foot F.data (Addr.add 7938736#64 i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add 8027856#64 i)) (hs1 : ∀ i < 8, Foot Wl (Addr.add g.rdi i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧ g' = g.set 0 rdq(V1 V g, 8027856#64) ∧ V' = V2 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.lda]
  exact ⟨h1, hs1, h2, hs2, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `_dl_get_tls_static_info (sizep, alignp)` from its entry to its `ret`: `_dl_tls_static_size` is at `sizep`, then
`_dl_tls_static_align` at `alignp` and in `rax`; the registers else are as at the entry. -/
theorem gts_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gts_at gts) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gts_at)
    (h1 : ∀ i < 8, Foot F.data (Addr.add 7938736#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add 8027856#64 i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (V2 V X.cpu.gpr) → Z.cpu.rip = gts_at.add 24 →
      Z.cpu.gpr = X.cpu.gpr.set 0 rdq(V1 V X.cpu.gpr, 8027856#64) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 24 ∧ g' = X.cpu.gpr.set 0 rdq(V1 V X.cpu.gpr, 8027856#64) ∧
    V' = V2 V X.cpu.gpr) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 h1 h2 hs1 hs2) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY hgY

end FV7z.Gts
