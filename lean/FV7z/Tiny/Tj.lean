import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Lemmas.FnFar
/-!
# Tail jumps of `7zzs` (PLAN.md §M, M1)

Ten functions of 7-Zip 26.06 in `7zzs` that are a tail jump: `endbr64; jmp rel32` (9 bytes: `0x41c160`, `0x41c180`,
`0x41c1a0`, `0x41c220`, `0x41c860`, `0x41cb70`, `0x41f3f0`, `0x60dfc0`) or `endbr64; mov rdi, rsi; jmp rel32`
(12 bytes: `0x41f3b0`, `0x41f3e0`). The callee is the caller's: a continuation at the target.

- `JmpAt prof L o e e₂ f`: from `e`, the run reaches `e₂` with the registers `f` of the entry's and the bytes as they
  were (the flags as well).
- `ej_go`, `emj_go`: the two shapes, given the decoding of each instruction.
- `t41c160_ok` … `t60dfc0_ok`: each function's `JmpAt`, given its bytes and some code at the target.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tiny

/-- From `e`, the run reaches `e₂` with the registers `f` of the entry's, the bytes as they were. -/
def JmpAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e e₂ : Addr) (f : Gprs → Gprs) : Prop :=
  ∀ (F : Footprint) (Wl : List Rgn) (s₀ : State) (gev : List Event) (gP : State → Nat → List Event → Prop)
    (gE : Outcome → List Event → Prop) (X : State) (t : Nat) (V : Addr → Byte), Seg prof F Wl L s₀ o →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e →
    ContG prof F Wl L s₀ o gev gP gE V (fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = f X.cpu.gpr) →
    GoG prof L o gev gP gE X t

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}

/-- `endbr64; jmp rel32`. -/
theorem ej_go {e : Addr} {code : List Byte} (hin : CodeIn L e code) (hn : 9 ≤ code.length)
    (d0 : Dec prof.feat code 0 (FV7z.mk .endbr64 32 [] 4)) {rel : Nat}
    (d4 : Dec prof.feat code 4 (FV7z.mk .jmp 64 [.rel rel] 5))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e.add 9 + BitVec.ofNat 64 rel = e₂) : JmpAt prof L o e e₂ id := by
  intro F Wl s₀ gev gP gE X t V c hK hA hrip k'
  refine c.s_endbr hK hA hin (j := 0) (by omega) (by rw [hrip, addr_add_zero]) d0 ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine c.s_jmp_x hKY hAY hin (j := 4) (by omega) hrY d4 hin₂ (tgt := 0) h₂ (by rw [addr_add_zero]; exact htgt) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k' Z t₂ hKZ hAZ ⟨by rw [hrZ, addr_add_zero], hgZ.trans hgY⟩

/-- `endbr64; mov rdi, rsi; jmp rel32`. -/
theorem emj_go {e : Addr} {code : List Byte} (hin : CodeIn L e code) (hn : 12 ≤ code.length)
    (d0 : Dec prof.feat code 0 (FV7z.mk .endbr64 32 [] 4))
    (d4 : Dec prof.feat code 4 (FV7z.mk .mov 64 [gr 64 7, gr 64 6] 3)) {rel : Nat}
    (d7 : Dec prof.feat code 7 (FV7z.mk .jmp 64 [.rel rel] 5))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e.add 12 + BitVec.ofNat 64 rel = e₂) : JmpAt prof L o e e₂ fun g => { g with rdi := g.rsi } := by
  intro F Wl s₀ gev gP gE X t V c hK hA hrip k'
  refine c.s_endbr hK hA hin (j := 0) (by omega) (by rw [hrip, addr_add_zero]) d0 ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine c.s_mov_rr64 hKY hAY hin (j := 4) (by omega) hrY d4 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine c.s_jmp_x hK₂ hA₂ hin (j := 7) (by omega) hr₂ d7 hin₂ (tgt := 0) h₂ (by rw [addr_add_zero]; exact htgt) ?_
  rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k' Z t₃ hKZ hAZ ⟨by rw [hrZ, addr_add_zero], ?_⟩
  rw [hgZ, hg₂, hgY] <;> rfl

/-! ## The functions -/

/-- `0x41c160`: to `0x427de0`. -/
def c41c160 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x77, 0xbc, 0x00, 0x00]
theorem c41c160_pin : Exe.bytesAt V2606.zzs.blob 0x41c160 9 = some c41c160 := by decide +kernel

theorem t41c160_ok {code₂ : List Byte} (hin : CodeIn L 0x41c160#64 c41c160) (hin₂ : CodeIn L 0x427de0#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41c160#64 0x427de0#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 48247) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41c180`: to `0x43a740`. -/
def c41c180 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xb7, 0xe5, 0x01, 0x00]
theorem c41c180_pin : Exe.bytesAt V2606.zzs.blob 0x41c180 9 = some c41c180 := by decide +kernel

theorem t41c180_ok {code₂ : List Byte} (hin : CodeIn L 0x41c180#64 c41c180) (hin₂ : CodeIn L 0x43a740#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41c180#64 0x43a740#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 124343) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41c1a0`: to `0x43b3e0`. -/
def c41c1a0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x37, 0xf2, 0x01, 0x00]
theorem c41c1a0_pin : Exe.bytesAt V2606.zzs.blob 0x41c1a0 9 = some c41c1a0 := by decide +kernel

theorem t41c1a0_ok {code₂ : List Byte} (hin : CodeIn L 0x41c1a0#64 c41c1a0) (hin₂ : CodeIn L 0x43b3e0#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41c1a0#64 0x43b3e0#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 127543) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41c220`: to `0x443e70`. -/
def c41c220 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x47, 0x7c, 0x02, 0x00]
theorem c41c220_pin : Exe.bytesAt V2606.zzs.blob 0x41c220 9 = some c41c220 := by decide +kernel

theorem t41c220_ok {code₂ : List Byte} (hin : CodeIn L 0x41c220#64 c41c220) (hin₂ : CodeIn L 0x443e70#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41c220#64 0x443e70#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 162887) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41c860`: to `0x56c470`. -/
def c41c860 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x07, 0xfc, 0x14, 0x00]
theorem c41c860_pin : Exe.bytesAt V2606.zzs.blob 0x41c860 9 = some c41c860 := by decide +kernel

theorem t41c860_ok {code₂ : List Byte} (hin : CodeIn L 0x41c860#64 c41c860) (hin₂ : CodeIn L 0x56c470#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41c860#64 0x56c470#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 1375239) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41cb70`: to `0x41e540`. -/
def c41cb70 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0xc7, 0x19, 0x00, 0x00]
theorem c41cb70_pin : Exe.bytesAt V2606.zzs.blob 0x41cb70 9 = some c41cb70 := by decide +kernel

theorem t41cb70_ok {code₂ : List Byte} (hin : CodeIn L 0x41cb70#64 c41cb70) (hin₂ : CodeIn L 0x41e540#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41cb70#64 0x41e540#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 6599) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41f3f0`: to `free` (`0x633750`). -/
def c41f3f0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x57, 0x43, 0x21, 0x00]
theorem c41f3f0_pin : Exe.bytesAt V2606.zzs.blob 0x41f3f0 9 = some c41f3f0 := by decide +kernel

theorem t41f3f0_ok {code₂ : List Byte} (hin : CodeIn L 0x41f3f0#64 c41f3f0) (hin₂ : CodeIn L 0x633750#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41f3f0#64 0x633750#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 2179927) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x60dfc0`: to `free` (`0x633750`). -/
def c60dfc0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x87, 0x57, 0x02, 0x00]
theorem c60dfc0_pin : Exe.bytesAt V2606.zzs.blob 0x60dfc0 9 = some c60dfc0 := by decide +kernel

theorem t60dfc0_ok {code₂ : List Byte} (hin : CodeIn L 0x60dfc0#64 c60dfc0) (hin₂ : CodeIn L 0x633750#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x60dfc0#64 0x633750#64 id :=
  ej_go hin (by decide) (by intro f; rfl) (rel := 153479) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41f3b0`: `rdi` = `rsi`, to `free` (`0x633750`). -/
def c41f3b0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf7, 0xe9, 0x94, 0x43, 0x21, 0x00]
theorem c41f3b0_pin : Exe.bytesAt V2606.zzs.blob 0x41f3b0 12 = some c41f3b0 := by decide +kernel

theorem t41f3b0_ok {code₂ : List Byte} (hin : CodeIn L 0x41f3b0#64 c41f3b0) (hin₂ : CodeIn L 0x633750#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41f3b0#64 0x633750#64 fun g => { g with rdi := g.rsi } :=
  emj_go hin (by decide) (by intro f; rfl) (by intro f; rfl) (rel := 2179988) (by intro f; rfl) hin₂ h₂ (by decide)

/-- `0x41f3e0`: `rdi` = `rsi`, to `0x41f3c0`. -/
def c41f3e0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf7, 0xe9, 0xd4, 0xff, 0xff, 0xff]
theorem c41f3e0_pin : Exe.bytesAt V2606.zzs.blob 0x41f3e0 12 = some c41f3e0 := by decide +kernel

theorem t41f3e0_ok {code₂ : List Byte} (hin : CodeIn L 0x41f3e0#64 c41f3e0) (hin₂ : CodeIn L 0x41f3c0#64 code₂)
    (h₂ : 0 < code₂.length) : JmpAt prof L o 0x41f3e0#64 0x41f3c0#64 fun g => { g with rdi := g.rsi } :=
  emj_go hin (by decide) (by intro f; rfl) (by intro f; rfl) (rel := 18446744073709551572) (by intro f; rfl) hin₂
    h₂ (by decide)

end FV7z.Tiny
