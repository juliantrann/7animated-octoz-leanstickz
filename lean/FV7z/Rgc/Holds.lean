import FV7z.Rgc.Cuts
import FV7z.Ctor.Reg
/-!
# `RegisterCodec` (PLAN.md §M, constructors)

7-Zip's `RegisterCodec` at `0x458e60` in `7zzs`
(`CPP/7zip/Common/CreateCoder.cpp`): `if (g_NumCodecs < 64) g_Codecs[g_NumCodecs++] = p;`,
the table at `0x79c900`, the count at `0x79cb00`. Two stretches of code, to the `ret` (34).

- `vc_0`: the code to the `ret`, `RegOut` of the bytes, the registers a call keeps unchanged.
- `rgc_ok`: `RegSpec`, with the count and the table in the footprint.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Ctor
namespace FV7z.Rgc

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_34 : pret <+: rgc.drop 34 := by decide +kernel
theorem ret_34 (feat : Features) : Dec feat rgc 34 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 34) (k := 0) (pret_0 feat) w_34 (Nat.zero_le _)

/-- Where the table and its count lie. -/
theorem lay : Lay 7981824#64 7981312#64 64 := ⟨by decide, by decide, by decide⟩

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : ∀ i < 4, Foot F.data (Addr.add 7981824#64 i))
    (hcw : ∀ i < 4, Foot Wl (Addr.add 7981824#64 i)) (ht : ∀ i < 512, Foot Wl (Addr.add 7981312#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 34 ∧ Kp g g' ∧ RegOut 7981824#64 7981312#64 64 g.rdi V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_18, o0, o1, Kp]
  refine ⟨hc, fun h => RegOut.full (ja_t h (by decide)), fun h => ⟨hcw, ?_, ?_⟩⟩
  · have hm := ja_f h
    exact Raf.off_ft ht (8 * (ofBytesLE 32 (List.map V (byteAddrs 7981824#64 4))).toNat)
      (BitVec.eq_of_toNat_eq ((slot_toNat _ _ (by decide)).trans (by simp; omega))) (by omega)
  · exact RegOut.st (ja_f h) (inc32 _) (slot_toNat _ _ (by decide)) lay

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

/-- `RegisterCodec (p)`: `RegSpec`, the count in the footprint's data and, with the table, in what the run may store
into. -/
theorem rgc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rgc_at rgc)
    (hc : ∀ i < 4, Foot F.data (Addr.add 7981824#64 i)) (hcw : ∀ i < 4, Foot Wl (Addr.add 7981824#64 i))
    (ht : ∀ i < 512, Foot Wl (Addr.add 7981312#64 i)) :
    RegSpec prof F Wl L s₀ o rgc_at 7981824#64 7981312#64 64 := by
  unfold RegSpec
  intro gev gP gE X t V hK hA hrip hl hd e₂ code₂ j₂ hin₂ h₂ hra k
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hc hcw ht) ?_
  rintro j' g fl V' ⟨rfl, ⟨h1, h2, h3, h4, h5, h6, h7⟩, hR⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; exact h1
  have h8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by have := X.cpu.gpr.rsp.isLt; omega
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_34 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp]
    exact hl i hi
  · rw [hsp, hR.rd lay h8 hd]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k V' Z t' hKZ hAZ hR hrZ ?_
  rw [hgZ, hgY]
  exact ⟨by show g.rsp + 8 = _; rw [h1]; rfl, h2, h3, h4, h5, h6, h7⟩

end FV7z.Rgc
