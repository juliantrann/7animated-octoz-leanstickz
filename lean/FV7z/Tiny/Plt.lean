import FV7z.Strlen.Plt
/-!
# PLT entries of `7zzs` (PLAN.md §M, M1)

Seven entries of `7zzs`'s PLT, each `jmp qword [rip + 0x390ff2]; xchg ax, ax` (`Strlen.pltLen`), through a GOT slot
that `apply_irel` filled with what an IFUNC resolver returned (`GotOkB`):

| entry      | slot       | resolver   |
|------------|------------|------------|
| `0x401020` | `0x792018` | `0x636a60` |
| `0x401040` | `0x792038` | `0x635ca0` |
| `0x401078` | `0x792070` | `0x637480` |
| `0x4010b0` | `0x7920a8` | `0x65d1f0` |
| `0x4010b8` | `0x7920b0` | `0x6369b0` |
| `0x401100` | `0x7920f8` | `0x65d650` |
| `0x401110` | `0x792108` | `0x635cf0` |

- `resV res`: the variants of the resolver at `res` (`V2606.resolvers`); `got_resV`: with `GotOkB`, a slot of
  `V2606.irel` holds one of its resolver's variants the processor has.
- `PltAt prof L o p res`: a run at `p` goes to one of the variants `r` of `resV res` the processor has, the registers
  and the bytes as they were.
- `plt_go`: `PltAt` of an entry, given its slot; `plt401020_ok` … `plt401110_ok` the seven entries.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start
namespace FV7z.Tiny

/-- The variants of the resolver at `res`, as `V2606.resolvers` lists them. -/
def resV (res : Nat) : Variants :=
  match V2606.resolvers.find? (fun r => r.1 == res) with
  | some r => r.2.2
  | none => []

/-- With `GotOkB`, a slot of `V2606.irel` holds one of its resolver's variants that the processor has. -/
theorem got_resV {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W) {q res : Nat}
    (hq : (q, res) ∈ V2606.irel) (hs : (V2606.resolvers.find? (fun r => r.1 == res)).isSome = true) :
    Returns prof (resV res) (ofBytesLE 64 ((byteAddrs (BitVec.ofNat 64 q) 8).map W)) := by
  unfold resV
  cases h : V2606.resolvers.find? (fun r => r.1 == res) with
  | none => simp [h] at hs
  | some r =>
    try dsimp only
    exact hG _ hq r (List.mem_of_find?_eq_some h) (by simpa using List.find?_some h)

/-- A run at `p` goes to one of the variants `r` of the resolver at `res` that the processor has, the registers and
the bytes as they were. -/
def PltAt (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (p : Addr) (res : Nat) : Prop :=
  ∀ (F : Footprint) (Wl : List Rgn) (s₀ : State) (gev : List Event) (gP : State → Nat → List Event → Prop)
    (gE : Outcome → List Event → Prop) (X : State) (t : Nat) (V : Addr → Byte), Seg prof F Wl L s₀ o → GotF F →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = p → GotOkB prof V →
    (∀ (r : Addr) (Y : State) (t' : Nat), Returns prof (resV res) r → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = r → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}

/-- `PltAt` of an entry `p` through the slot `q` of `V2606.irel`, given code at each variant. -/
theorem plt_go {p : Addr} {q res : Nat} (hq : (q, res) ∈ V2606.irel)
    (hs : (V2606.resolvers.find? (fun r => r.1 == res)).isSome = true)
    (he : p.add 6 + BitVec.ofNat 64 3739634 = BitVec.ofNat 64 q) (hinP : CodeIn L p Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV res) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o p res := by
  intro F Wl s₀ gev gP gE X t V c hgf hK hA hrip hG K
  have hR := got_resV hG hq hs
  obtain ⟨code₂, hin₂, h₂⟩ := hv _ hR
  have hea : eaR X 6 3739634 = BitVec.ofNat 64 q := by
    show X.cpu.rip.add 6 + BitVec.ofNat 64 3739634 = _
    rw [hrip]
    exact he
  have hb : 0x792018 ≤ q ∧ q + 8 ≤ 0x792110 := irel_bd _ hq
  refine c.s_jmp_mrip hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (Strlen.pd0 prof.feat)
    (fun i hi => ?_) hin₂ h₂ (by rw [hea]) ?_
  · rw [hea]
    apply hgf.got
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  · rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact K _ Y t' hR hKY hAY hrY hgY

theorem pin401020 : Exe.bytesAt V2606.zzs.blob 0x401020 8 = some Strlen.pltLen := by decide +kernel
theorem pin401040 : Exe.bytesAt V2606.zzs.blob 0x401040 8 = some Strlen.pltLen := by decide +kernel
theorem pin401078 : Exe.bytesAt V2606.zzs.blob 0x401078 8 = some Strlen.pltLen := by decide +kernel
theorem pin4010b0 : Exe.bytesAt V2606.zzs.blob 0x4010b0 8 = some Strlen.pltLen := by decide +kernel
theorem pin4010b8 : Exe.bytesAt V2606.zzs.blob 0x4010b8 8 = some Strlen.pltLen := by decide +kernel
theorem pin401100 : Exe.bytesAt V2606.zzs.blob 0x401100 8 = some Strlen.pltLen := by decide +kernel
theorem pin401110 : Exe.bytesAt V2606.zzs.blob 0x401110 8 = some Strlen.pltLen := by decide +kernel

theorem plt401020_ok (hinP : CodeIn L 0x401020#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x636a60) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x401020#64 0x636a60 :=
  plt_go (q := 0x792018) (by decide) (by decide) (by decide) hinP hv

theorem plt401040_ok (hinP : CodeIn L 0x401040#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x635ca0) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x401040#64 0x635ca0 :=
  plt_go (q := 0x792038) (by decide) (by decide) (by decide) hinP hv

theorem plt401078_ok (hinP : CodeIn L 0x401078#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x637480) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x401078#64 0x637480 :=
  plt_go (q := 0x792070) (by decide) (by decide) (by decide) hinP hv

theorem plt4010b0_ok (hinP : CodeIn L 0x4010b0#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x65d1f0) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x4010b0#64 0x65d1f0 :=
  plt_go (q := 0x7920a8) (by decide) (by decide) (by decide) hinP hv

theorem plt4010b8_ok (hinP : CodeIn L 0x4010b8#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x6369b0) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x4010b8#64 0x6369b0 :=
  plt_go (q := 0x7920b0) (by decide) (by decide) (by decide) hinP hv

theorem plt401100_ok (hinP : CodeIn L 0x401100#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x65d650) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x401100#64 0x65d650 :=
  plt_go (q := 0x7920f8) (by decide) (by decide) (by decide) hinP hv

theorem plt401110_ok (hinP : CodeIn L 0x401110#64 Strlen.pltLen)
    (hv : ∀ r, Returns prof (resV 0x635cf0) r → ∃ code, CodeIn L r code ∧ 0 < code.length) :
    PltAt prof L o 0x401110#64 0x635cf0 :=
  plt_go (q := 0x792108) (by decide) (by decide) (by decide) hinP hv

end FV7z.Tiny
