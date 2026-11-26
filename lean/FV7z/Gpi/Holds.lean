import FV7z.Gpi.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CHandler::GetArchivePropertyInfo` (PLAN.md §M, M1)

7-Zip 26.06's `GetArchivePropertyInfo (index, name, propID, varType)` at `0x49e900` in `7zzs`, by the symbol table
`NArchive::NGz::CHandler`'s (the code `Base64Handler.o` has; `objdump -d`): for an index (`esi`) past 1,
`E_INVALIDARG` (`0x80070057`) in `eax` (`ret` at 61); else the property's id, the byte at `0x6ddc2c + index`, in the
4 bytes at `propID` (`rcx`), its type, the byte at `0x6d9ba0 + id`, in the 2 bytes at `varType` (`r8`), NULL in the
8 bytes at `name` (`rdx`) and 0 (`S_OK`) in `rax` (`ret` at 48).

- `Big`: the index past 1, as `cmp esi, 1; ja` has it; `ix`, `pid`, `vt`: the index, the id, the type.
- `MG`: the bytes after the three stores.
- `vc_big`, `vc_small`: from the entry to the `ret`s; `gpi_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gpi

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: gpi.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat gpi 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)
theorem w_61 : pret <+: gpi.drop 61 := by decide +kernel
theorem ret_61 (feat : Features) : Dec feat gpi 61 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 61) (k := 0) (pret_0 feat) w_61 (Nat.zero_le _)

/-- The index past 1: `cmp esi, 1; ja` taken, as the model has it. -/
def Big (g : Gprs) : Prop :=
  (!(decide ((BitVec.setWidth 32 g.rsi).toNat < 1) || decide (BitVec.setWidth 32 g.rsi = 1#32))) = true
/-- The index, zero-extended. -/
abbrev ix (g : Gprs) : Addr := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)
/-- The property's id, the byte at `0x6ddc2c + index`, zero-extended. -/
abbrev pid (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 ((byteAddrs (7199788#64 + ix g) 1).map V)))
/-- The bytes after the store of the id. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V g.rcx (toBytesLE (BitVec.setWidth 32 (pid V g)) 4)
/-- The property's type, the byte at `0x6d9ba0 + id` (read after the store of the id), zero-extended. -/
abbrev vt (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 ((byteAddrs (7183264#64 + pid V g) 1).map (V1 V g))))
/-- The bytes after the three stores. -/
abbrev MG (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (V1 V g) g.r8 (toBytesLE (BitVec.setWidth 16 (vt V g)) 2)) g.rdx (toBytesLE 0#64 8)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- An index past 1: `E_INVALIDARG`. -/
theorem vc_big {g : Gprs} {f : Rflags} (h : Big g) :
    W_0 F Wl (fun j' g' _ V' => j' = 61 ∧ g' = { g with rax := BitVec.setWidth 64 2147942487#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold Big at h
  dsimp only at h ⊢
  wpx [W_0, W_9, W_56, o0, o1, o2]
  all_goals first
  | exact ⟨fun _ => trivial, fun hc => absurd (h.symm.trans hc) (by decide)⟩
  | exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun hc => absurd (h.symm.trans hc) (by decide)⟩
  | (refine ⟨fun _ => ?_, fun hc => absurd (h.symm.trans hc) (by decide)⟩; done)

/-- An index 0 or 1: the id and the type from the tables, `name` NULL, `S_OK`. -/
theorem vc_small {g : Gprs} {f : Rflags} (h : ¬ Big g)
    (ft1 : ∀ i < 1, Foot F.data (Addr.add (7199788#64 + ix g) i)) (wc : ∀ i < 4, Foot Wl (Addr.add g.rcx i))
    (ft2 : ∀ i < 1, Foot F.data (Addr.add (7183264#64 + pid V g) i)) (w8 : ∀ i < 2, Foot Wl (Addr.add g.r8 i))
    (wd : ∀ i < 8, Foot Wl (Addr.add g.rdx i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = { g with rax := 0#64, rcx := 7183264#64, rsi := ix g } ∧
      V' = MG V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold Big at h
  dsimp only at h ft1 wc ft2 w8 wd ⊢
  wpx [W_0, W_9, W_56, o0, o1, o2, ix, pid, V1, vt, MG, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals first
  | exact ⟨fun hc => (h hc).elim, fun _ => ⟨ft1, wc, ft2, w8, wd⟩⟩
  | exact ⟨fun hc => (h hc).elim, fun _ => ⟨ft1, wc, ft2, w8, wd, rfl, rfl⟩⟩
  | (refine ⟨fun hc => (h hc).elim, fun _ => ⟨ft1, wc, ft2, w8, wd, ?_⟩⟩; done)

/-- `GetArchivePropertyInfo (index, name, propID, varType)` from its entry to the return address: for an index past
1 (`kb`) `E_INVALIDARG` in `rax`; else (`ks`) the bytes `MG`, `rax` 0, `rcx` and `rsi` changed. -/
theorem gpi_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gpi_at gpi) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gpi_at)
    (ft1 : ¬ Big X.cpu.gpr → ∀ i < 1, Foot F.data (Addr.add (7199788#64 + ix X.cpu.gpr) i))
    (ft2 : ¬ Big X.cpu.gpr → ∀ i < 1, Foot F.data (Addr.add (7183264#64 + pid V X.cpu.gpr) i))
    (wc : ¬ Big X.cpu.gpr → ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (w8 : ¬ Big X.cpu.gpr → ∀ i < 2, Foot Wl (Addr.add X.cpu.gpr.r8 i))
    (wd : ¬ Big X.cpu.gpr → ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : Big X.cpu.gpr → rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hra' : ¬ Big X.cpu.gpr → rdq(MG V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (kb : Big X.cpu.gpr → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := BitVec.setWidth 64 2147942487#32 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (ks : ¬ Big X.cpu.gpr → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (MG V X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rcx := 7183264#64, rsi := ix X.cpu.gpr }.set 4
        (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases hb : Big X.cpu.gpr
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 61 ∧
        g' = { X.cpu.gpr with rax := BitVec.setWidth 64 2147942487#32 } ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_big hb) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_61 _) (by rw [hspY]; exact hl) hin₂ h₂
      (by rw [hspY]; exact hra hb) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kb hb Z t₂ hKZ hAZ hrZ (by rw [hgZ, hspY, hgY])
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 48 ∧
        g' = { X.cpu.gpr with rax := 0#64, rcx := 7183264#64, rsi := ix X.cpu.gpr } ∧ V' = MG V X.cpu.gpr)
      hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_small hb (ft1 hb) (wc hb) (ft2 hb) (w8 hb) (wd hb)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_48 _) (by rw [hspY]; exact hl) hin₂ h₂
      (by rw [hspY]; exact hra' hb) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact ks hb Z t₂ hKZ hAZ hrZ (by rw [hgZ, hspY, hgY])

end FV7z.Gpi
