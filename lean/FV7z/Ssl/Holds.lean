import FV7z.Ssl.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `SysStringLen` (PLAN.md §M, M1)

7-Zip 26.06's `SysStringLen (bstr)` at `0x5a0100` in `7zzs` (`CPP/Common/MyWindows.cpp`; `objdump -d`): 0 for a
null `bstr`, else the byte length stored before it (`[bstr - 4]`) over 4, in `eax`. Two `ret`s: 15 (not null) and
18 (null).

- `sLen`: the length returned for a `bstr` not null; `vc_z`, `vc_n`: from the entry to the `ret`s.
- `ssl_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ssl

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_15 : pret <+: ssl.drop 15 := by decide +kernel
theorem ret_15 (feat : Features) : Dec feat ssl 15 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 15) (k := 0) (pret_0 feat) w_15 (Nat.zero_le _)
theorem w_18 : pret <+: ssl.drop 18 := by decide +kernel
theorem ret_18 (feat : Features) : Dec feat ssl 18 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 18) (k := 0) (pret_0 feat) w_18 (Nat.zero_le _)

/-- The length of a `bstr` `p` not null: the 4 bytes before it, over 4. -/
abbrev sLen (V : Addr → Byte) (p : Addr) : BitVec 32 :=
  ofBytesLE 32 ((byteAddrs (p + 18446744073709551612#64) 4).map V) >>> 2

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- A null `bstr`: `test rdi, rdi; je`, `xor eax, eax`. -/
theorem vc_z {g : Gprs} {f : Rflags} (h : g.rdi = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 18 ∧ g' = g.set 0 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_0, W_16, W_9, o0, o1, o2, lf_xz, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies]
  first
  | rfl
  | exact ⟨rfl, rfl⟩
  | exact fun _ => rfl
  | exact ⟨fun _ => rfl, fun hh => absurd hh (by decide)⟩
  | repeat' (first | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh (by decide)) | intro _)

/-- A `bstr` not null: `test rdi, rdi; je`, `mov eax, [rdi - 4]; shr eax, 2`. -/
theorem vc_n {g : Gprs} {f : Rflags} (h : g.rdi ≠ 0)
    (fa : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 18446744073709551612#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 15 ∧ g' = g.set 0 ((sLen V g.rdi).setWidth 64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h fa ⊢
  wpx [W_0, W_16, W_9, o0, o1, o2, sLen, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, h,
    not_true_eq_false, not_false_eq_true, false_implies]
  first
  | exact fa
  | exact ⟨fa, rfl⟩
  | exact ⟨fa, fun _ => rfl⟩
  | exact ⟨fa, fun _ => ⟨rfl, rfl⟩⟩
  | repeat' (first | exact fa | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh h) | intro _)

/-- `SysStringLen (bstr)` from its entry to the return address: `rax` 0 for a null `bstr`, else `sLen`. -/
theorem ssl_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ssl_at ssl) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ssl_at)
    (fa : X.cpu.gpr.rdi ≠ 0 → ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 18446744073709551612#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = (X.cpu.gpr.set 0 (if X.cpu.gpr.rdi = 0 then 0 else (sLen V X.cpu.gpr.rdi).setWidth 64)).set 4
        (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases h0 : X.cpu.gpr.rdi = 0
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = X.cpu.gpr.set 0 0 ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_z h0) ?_
    rintro j' g fl V₁ ⟨hj', hg, hV⟩ Y t₁ hKY hAY hrY hgY -
    have hgY' : Y.cpu.gpr = X.cpu.gpr.set 0 0 := hgY.trans hg
    have hAY' : Agree F Y.proc.mm.mem V := hV ▸ hAY
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY']; rfl
    have hrY' : Y.cpu.rip = ssl_at.add 18 := by rw [← hj']; exact hrY
    refine c.s_ret hKY hAY' hin (lt_len (by decide)) hrY' (ret_18 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t' hKZ hAZ hrZ (by rw [hgZ, hspY, hgY', if_pos h0])
  · refine (c_0 prof).run c hin
      (fun j' g' _ V' => j' = 15 ∧ g' = X.cpu.gpr.set 0 ((sLen V X.cpu.gpr.rdi).setWidth 64) ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_n h0 (fa h0)) ?_
    rintro j' g fl V₁ ⟨hj', hg, hV⟩ Y t₁ hKY hAY hrY hgY -
    have hgY' : Y.cpu.gpr = X.cpu.gpr.set 0 ((sLen V X.cpu.gpr.rdi).setWidth 64) := hgY.trans hg
    have hAY' : Agree F Y.proc.mm.mem V := hV ▸ hAY
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY']; rfl
    have hrY' : Y.cpu.rip = ssl_at.add 15 := by rw [← hj']; exact hrY
    refine c.s_ret hKY hAY' hin (lt_len (by decide)) hrY' (ret_15 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t' hKZ hAZ hrZ (by rw [hgZ, hspY, hgY', if_neg h0])

end FV7z.Ssl
