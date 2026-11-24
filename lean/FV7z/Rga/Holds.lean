import FV7z.Rga.Cuts
import FV7z.Ctor.Reg
/-!
# `RegisterArc` (PLAN.md §M, constructors)

7-Zip's `RegisterArc` at `0x5ceb20` in `7zzs`
(`CPP/7zip/Archive/ArchiveExports.cpp`): `if (g_NumArcs < 72) g_Arcs[g_NumArcs++] = p;`,
the table at `0x79edc0`, the count at `0x79f000`. Two stretches of code, to the `ret` (37).

- `vc_0`: the code to the `ret`, `RegOut` of the bytes, the registers a call keeps unchanged.
- `rga_ok`: `RegSpec`, with the count and the table in the footprint.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Ctor
namespace FV7z.Rga

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_37 : pret <+: rga.drop 37 := by decide +kernel
theorem ret_37 (feat : Features) : Dec feat rga 37 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 37) (k := 0) (pret_0 feat) w_37 (Nat.zero_le _)

/-- Where the table and its count lie. -/
theorem lay : Lay 7991296#64 7990720#64 72 := ⟨by decide, by decide, by decide⟩

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : ∀ i < 4, Foot F.data (Addr.add 7991296#64 i))
    (hcw : ∀ i < 4, Foot Wl (Addr.add 7991296#64 i)) (ht : ∀ i < 576, Foot Wl (Addr.add 7990720#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 37 ∧ Kp g g' ∧ RegOut 7991296#64 7990720#64 72 g.rdi V V') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_15, o0, o1, Kp, Op.lda, Op.sta]
  refine ⟨hc, fun h => RegOut.full (ja_t h (by decide)), fun h => ⟨?_, hcw, ?_⟩⟩
  · have hm := ja_f h
    exact Raf.off_ft ht (8 * (ofBytesLE 32 (List.map V (byteAddrs 7991296#64 4))).toNat)
      (BitVec.eq_of_toNat_eq ((slot_toNat _ _ (by decide)).trans (by simp; omega))) (by omega)
  · exact RegOut.st' (ja_f h) rfl (slot_toNat _ _ (by decide)) lay

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

/-- `RegisterArc (p)`: `RegSpec`, the count in the footprint's data and, with the table, in what the run may store
into. -/
theorem rga_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rga_at rga)
    (hc : ∀ i < 4, Foot F.data (Addr.add 7991296#64 i)) (hcw : ∀ i < 4, Foot Wl (Addr.add 7991296#64 i))
    (ht : ∀ i < 576, Foot Wl (Addr.add 7990720#64 i)) :
    RegSpec prof F Wl L s₀ o rga_at 7991296#64 7990720#64 72 := by
  unfold RegSpec
  intro gev gP gE X t V hK hA hrip hl h8 hd e₂ code₂ j₂ hin₂ h₂ hra k
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hc hcw ht) ?_
  rintro j' g fl V' ⟨rfl, ⟨h1, h2, h3, h4, h5, h6, h7⟩, hR⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; exact h1
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_37 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp]
    exact hl i hi
  · rw [hsp, hR.rd lay h8 hd]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k V' Z t' hKZ hAZ hR hrZ ?_
  rw [hgZ, hgY]
  exact ⟨by show g.rsp + 8 = _; rw [h1]; rfl, h2, h3, h4, h5, h6, h7⟩

end FV7z.Rga
