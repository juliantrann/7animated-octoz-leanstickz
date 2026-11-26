import FV7z.Isb.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnJt
/-!
# `InStream_SeekToBegin` (PLAN.md §M, M1)

7-Zip 26.06's `InStream_SeekToBegin (stream)` at `0x4631e0` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`):
`stream->Seek (0, STREAM_SEEK_SET, NULL)`, a tail jump through the vtable (`jmp rax`, the vtable's entry at 32) with
`ecx`, `edx` and `esi` 0. The callee's code is a hypothesis (`hin₂`).

- `isb_ok`: the run at the vtable's entry, `rax` that entry, `rcx`, `rdx` and `rsi` 0, the other registers those of
  the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Isb

/-- The jump through `rax`. -/
def pjm : List Byte := [0xff, 0xe0]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem wj_17 : pjm <+: isb.drop 17 := by decide +kernel
theorem jmp_17 (feat : Features) : Dec feat isb 17 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 17) (k := 0) (pjm_0 feat) wj_17 (Nat.zero_le _)

/-- The registers at the jump: `rax` the vtable's entry at 32, `rcx`, `rdx` and `rsi` 0. -/
abbrev gJ (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V, rdq(V, g.rdi) + 32#64), rcx := 0, rdx := 0, rsi := 0 }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov rax, [rdi]; xor ecx, ecx; xor edx, edx; xor esi, esi; mov rax, [rax + 32]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rdi) + 32#64) i)) :
    wp F Wl o0 (fun g' _ V' => g' = gJ V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa fb ⊢
  wpx [o0, lf_xz]
  first
  | rfl
  | exact ⟨fa, fb⟩
  | exact ⟨fa, fb, rfl⟩
  | exact ⟨fa, fb, rfl, rfl⟩
  | exact ⟨fa, fun _ => ⟨fb, fun _ => rfl⟩⟩
  | repeat' (first | exact fa | exact fb | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `InStream_SeekToBegin (stream)` from its entry: at the vtable's entry (`e₂.add tgt`), the registers `gJ`. -/
theorem isb_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L isb_at isb) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isb_at)
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (rdq(V, X.cpu.gpr.rdi) + 32#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, rdq(V, X.cpu.gpr.rdi) + 32#64) = e₂.add tgt)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = gJ V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 17 ∧ g' = gJ V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 fa fb)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_jmp_rx hKY hAY hin (lt_len (by decide)) hrY (jmp_17 _) hin₂ ht (by rw [hgY]; exact htgt) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (hg₂.trans hgY)

end FV7z.Isb
