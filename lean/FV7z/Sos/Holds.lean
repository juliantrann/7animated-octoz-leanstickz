import FV7z.Sos.Cuts
import FV7z.Lzi.Code
import FV7z.Lzi.Blocks
import FV7z.Lemmas.SetccM
import FV7z.Tun.Inv
/-!
# `NCompress::NLzma::CDecoder::SetOutStreamSizeResume` (PLAN.md §M, M1)

7-Zip 26.06's `CDecoder::SetOutStreamSizeResume (outSize)` at `0x57fd80` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`), `this` in `rdi`, `outSize` in `rsi`: `_outSize` (the 8 bytes at `this + 104`)
= 0, `_outSizeDefined` (the byte at `this + 70`) = `outSize != NULL` (`setne`, a step of its own:
`Seg.s_setcc_m8`), `_outSize` = `*outSize` if `outSize` is not null (21), `_outProcessed` (`this + 120`) = 0,
`_state.decoder.dicPos`'s neighbour `_lzmaStatus` (the 4 bytes at `this + 84`) = 0, then a tail jump (47) to
`LzmaDec_Init (&_state)` (`Lzi.lzi_at`, `rdi` = `this + 128`).

The callee is a hypothesis (`kf`), as in `FV7z/Ifs/Holds.lean`; `Lzi.lzi_ok` is its contract.

- `sV1`, `sV`: the bytes after the `setne` and at the jump; `sG`: the registers at the jump.
- `vc_0`, `vc_19`, `vc_28`: the verification conditions of the pieces.
- `sos_ok`: from the entry to `LzmaDec_Init`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sos

/-- The `setne byte [rdi + 70]`. -/
def pset : List Byte := [0x0f, 0x95, 0x47, 0x46]
theorem pset_0 : ∀ feat, Dec feat pset 0 (FV7z.mk (.setcc 5) 8 [.mem (mbd 7 70 8)] 4) := by dec_rfl
theorem ws_15 : pset <+: sos.drop 15 := by decide +kernel
theorem set_15 (feat : Features) : Dec feat sos 15 (FV7z.mk (.setcc 5) 8 [.mem (mbd 7 70 8)] 4) :=
  Dec.shift (j := 15) (k := 0) (pset_0 feat) ws_15 (Nat.zero_le _)

/-- The jump to `LzmaDec_Init`. -/
def pjm : List Byte := [0xe9, 0x8c, 0xb8, 0xea, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073708157068] 5) := by dec_rfl
theorem wj_47 : pjm <+: sos.drop 47 := by decide +kernel
theorem jmp_47 (feat : Features) : Dec feat sos 47 (FV7z.mk .jmp 64 [.rel 18446744073708157068] 5) :=
  Dec.shift (j := 47) (k := 0) (pjm_0 feat) wj_47 (Nat.zero_le _)

theorem e128 (x : BitVec 64) : x - 18446744073709551488#64 = x + 128#64 := by bv_omega
theorem e84 (x : BitVec 64) : x + 128#64 + 18446744073709551572#64 = x + 84#64 := by bv_omega

/-- The bytes after the `setne`: `_outSize` = 0, `_outSizeDefined` = `outSize != NULL`. -/
abbrev sV1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rdi + 104#64) (toBytesLE 0#64 8)) (g.rdi + 70#64)
    (toBytesLE ((BitVec.ofBool (!(g.rsi == 0))).setWidth 8) 1)

/-- At 28: `rax` = `*outSize` if `outSize` is not null. -/
abbrev s28G (V : Addr → Byte) (g : Gprs) : Gprs := if g.rsi = 0 then g else { g with rax := rdq(V, g.rsi) }

/-- At 28: `_outSize` = `*outSize` if `outSize` is not null. -/
abbrev s28V (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if g.rsi = 0 then V else Vst V (g.rdi + 104#64) (toBytesLE rdq(V, g.rsi) 8)

/-- The registers at the jump. -/
abbrev sG (V : Addr → Byte) (g : Gprs) : Gprs := { s28G (sV1 V g) g with rdi := g.rdi + 128#64 }

/-- The bytes at the jump: `_outProcessed` = 0, `_lzmaStatus` = 0. -/
abbrev sV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (s28V (sV1 V g) g) (g.rdi + 120#64) (toBytesLE 0#64 8)) (g.rdi + 84#64) (toBytesLE 0#32 4)

variable {F : Footprint} {Wl : List Rgn}

/-- `test rsi, rsi; mov qword [rdi + 104], 0` to the `setne` at 15. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 104#64) i)) :
    W_0 F Wl (fun j' g' f' V' => j' = 15 ∧ g' = g ∧ f'.zf = (g.rsi == 0) ∧
      V' = Vst V (g.rdi + 104#64) (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw ⊢
  wpx [W_0, o0, BitVec.and_self]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `je 28`, or `mov rax, [rsi]; mov [rdi + 104], rax`. -/
theorem vc_19 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : f.zf = (g.rsi == 0))
    (hr : g.rsi ≠ 0 → ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 104#64) i)) :
    W_19 F Wl (fun j' g' _ V' => j' = 28 ∧ g' = s28G V g ∧ V' = s28V V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hr hw ⊢
  have hz' : f.zf = decide (rsi = 0) := by
    rw [hz]
    by_cases h : rsi = 0 <;> simp [h]
  by_cases h0 : rsi = 0
  · wpx [W_19, s28G, s28V, hz', h0, decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true, ↓reduceIte]
    all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  · have fr := hr h0
    dsimp only at fr
    wpx [W_19, W_21, o1, s28G, s28V, hz', h0, decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false,
      false_implies, implies_true, ↓reduceIte]
    all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `mov qword [rdi + 120], 0; sub rdi, -128; mov dword [rdi - 44], 0` to the jump at 47. -/
theorem vc_28 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw1 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 120#64) i)) (hw2 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 84#64) i)) :
    W_28 F Wl (fun j' g' _ V' => j' = 47 ∧ g' = { g with rdi := g.rdi + 128#64 } ∧
      V' = Vst (Vst V (g.rdi + 120#64) (toBytesLE 0#64 8)) (g.rdi + 84#64) (toBytesLE 0#32 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw1 hw2 ⊢
  wpx [W_28, o2, e128, e84]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDecoder::SetOutStreamSizeResume (outSize)` (`this` = `rdi`, `outSize` = `rsi`) from its entry: at
`LzmaDec_Init`'s entry with the registers `sG` and the bytes `sV` (`kf`). -/
theorem sos_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sos_at sos) (hinL : CodeIn L Lzi.lzi_at Lzi.lzi)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sos_at)
    (w104 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 104#64) i))
    (w70 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 70#64) i))
    (w120 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 120#64) i))
    (w84 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 84#64) i))
    (hr : X.cpu.gpr.rsi ≠ 0 → ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (sV V X.cpu.gpr) →
      Y.cpu.rip = Lzi.lzi_at → Y.cpu.gpr = sG V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' f' V' => j' = 15 ∧ g' = X.cpu.gpr ∧ f'.zf = (X.cpu.gpr.rsi == 0) ∧
      V' = Vst V (X.cpu.gpr.rdi + 104#64) (toBytesLE 0#64 8)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 w104) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hz, hV₁⟩ Y t₁ hKY hAY hrY hgY hfY
  subst V₁
  -- the `setne`
  have he : eaD Y 7 70 = X.cpu.gpr.rdi + 70#64 := by
    show Y.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 70 = _
    rw [hgY]
    rfl
  refine c.s_setcc_m8 hKY hAY hin (lt_len (by decide)) hrY (set_15 _) (by rw [he]; exact w70) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hf₂⟩
  have hb : Y.cpu.rflags.cond 5 = !(X.cpu.gpr.rsi == 0) := by rw [hfY, cond_5, hz]
  rw [he, hb] at hA₂
  have hz₂ : Y₂.cpu.rflags.zf = (X.cpu.gpr.rsi == 0) := by
    rw [hf₂]
    show Y.cpu.rflags.zf = _
    rw [hfY]
    exact hz
  have hg₂' : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, hgY]
  -- `je 28`, or the copy of `*outSize`
  refine (c_19 prof).run c hin (fun j' g' _ V' => j' = 28 ∧ g' = s28G (sV1 V X.cpu.gpr) X.cpu.gpr ∧
      V' = s28V (sV1 V X.cpu.gpr) X.cpu.gpr) hK₂ hA₂ hr₂
    (by
      rw [hg₂']
      exact vc_19 hz₂ (fun h i hi => hr h i hi) w104) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hdi : (s28G (sV1 V X.cpu.gpr) X.cpu.gpr).rdi = X.cpu.gpr.rdi := by
    by_cases h0 : X.cpu.gpr.rsi = 0 <;> simp only [s28G, h0, ↓reduceIte]
  -- the last stores
  refine (c_28 prof).run c hin (fun j' g' _ V' => j' = 47 ∧ g' = sG V X.cpu.gpr ∧ V' = sV V X.cpu.gpr) hKU hAU hrU
    (by
      rw [hgU]
      have h := vc_28 (F := F) (f := U.cpu.rflags) (V := s28V (sV1 V X.cpu.gpr) X.cpu.gpr)
        (g := s28G (sV1 V X.cpu.gpr) X.cpu.gpr) (by rw [hdi]; exact w120) (by rw [hdi]; exact w84)
      rw [hdi] at h
      exact h) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₃
  refine c.s_jmp_x hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (jmp_47 _) hinL (Lzi.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact kf Y₃ t₅ hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (by rw [hg₃, hgU₂])

end FV7z.Sos
