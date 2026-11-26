import FV7z.Caa.Cuts
import FV7z.Aaa.Code
import FV7z.Aaa.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensorNode::AreAllAllowed` (PLAN.md §M, M1)

7-Zip 26.06's `CCensorNode::AreAllAllowed ()` at `0x452b20` in `7zzs` (`CPP/Common/Wildcard.cpp`): with `this` in
`rdi`, unless `Name` is empty (its length, the 4 bytes at `this + 16`), there are no `SubNodes` (`+ 32`), no
`ExcludeItems` (`+ 64`) and one item of `IncludeItems` (`+ 48`) (`cOk`), 0 in `rax` (`xor eax, eax` at 31, the `ret`
at 33); else a tail jump (47) to `CItem::AreAllAllowed` (`Aaa.aaa_at`) with `rdi` = `IncludeItems._items[0]` (the
8 bytes at the 8 bytes at `this + 40`).

The callee is a hypothesis (`kf`), as in `FV7z/Aaa/Holds.lean`.

- `cOk`: the condition; `cG`: the registers at the jump.
- `vc_0`, `vc_31`: the verification conditions of the pieces.
- `caa_ok`: from the entry to the return address with `rax` = 0 (`kn`), or to the callee's entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Caa

/-- The jump to `CItem::AreAllAllowed`. -/
def pjm : List Byte := [0xe9, 0x3c, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551164] 5) := by dec_rfl
theorem wj_47 : pjm <+: caa.drop 47 := by decide +kernel
theorem jmp_47 (feat : Features) : Dec feat caa 47 (FV7z.mk .jmp 64 [.rel 18446744073709551164] 5) :=
  Dec.shift (j := 47) (k := 0) (pjm_0 feat) wj_47 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: caa.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat caa 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)

/-- `Name` empty, no `SubNodes`, no `ExcludeItems`, one item of `IncludeItems`. -/
abbrev cOk (V : Addr → Byte) (p : Addr) : Prop :=
  rdd(V, p + 16#64) = 0#32 ∧ rdd(V, p + 32#64) = 0#32 ∧ rdd(V, p + 64#64) = 0#32 ∧ rdd(V, p + 48#64) = 1#32

/-- The registers at the jump: `rax` = `IncludeItems._items`, `rdi` = its first. -/
abbrev cG (V : Addr → Byte) (g : Gprs) (c d : BitVec 64) : Gprs :=
  { g with
    rax := rdq(V, g.rdi + 40#64),
    rcx := c,
    rdx := d,
    rdi := rdq(V, rdq(V, g.rdi + 40#64)) }

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- `mov ecx, [rdi + 16]; test; jne; mov edx, [rdi + 32]; test; jne; mov eax, [rdi + 64]; test; jne;
cmp dword [rdi + 48], 1; je`, then to 31, or `mov rax, [rdi + 40]; mov rdi, [rax]` to the jump at 47. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 16#64) i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 32#64) i))
    (f64 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 64#64) i))
    (f48 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 48#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 40#64) i))
    (fp : cOk V g.rdi → ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rdi + 40#64) i))
    (h31 : ∀ a c d, ¬ cOk V g.rdi → ∀ fl, Q 31 { g with rax := a, rcx := c, rdx := d } fl V)
    (h47 : ∀ c d, cOk V g.rdi → ∀ fl, Q 47 (cG V g c d) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 f32 f64 f48 f40 fp h31 h47 ⊢
  wpx [W_0, W_11, W_18, W_25, W_40, o0, o1, o2, o3, o5, Op.cmpmi, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact f16
    | with_reducible exact f32
    | with_reducible exact f64
    | with_reducible exact f48
    | with_reducible exact f40
    | exact fp ⟨by assumption, by assumption, by assumption, by assumption⟩
    | apply And.intro
    | intro)
  all_goals first
    | exact h31 _ _ _ (fun hk => absurd hk.1 (by assumption)) _
    | exact h31 _ _ _ (fun hk => absurd hk.2.1 (by assumption)) _
    | exact h31 _ _ _ (fun hk => absurd hk.2.2.1 (by assumption)) _
    | exact h31 _ _ _ (fun hk => absurd hk.2.2.2 (by assumption)) _
    | exact h47 _ _ ⟨by assumption, by assumption, by assumption, by assumption⟩ _

/-- `xor eax, eax` to the `ret` at 33. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_31 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_31, o4, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CCensorNode::AreAllAllowed ()` (`this` = `rdi`) from its entry, no byte written. Not `cOk`: at the return
address with `rax` = 0 (`kn`). `cOk`: at `CItem::AreAllAllowed`'s entry with the registers `cG` (`kf`). -/
theorem caa_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L caa_at caa) (hinA : CodeIn L Aaa.aaa_at Aaa.aaa)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = caa_at)
    (f16 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (f64 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (f48 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (fp : cOk V X.cpu.gpr.rdi → ∀ i < 8, Foot F.data (Addr.add rdq(V, X.cpu.gpr.rdi + 40#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : ¬ cOk V X.cpu.gpr.rdi → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → (∃ c d, Z.cpu.gpr = { X.cpu.gpr with
                                                    rax := 0#64, rcx := c, rdx := d,
                                                    rsp := X.cpu.gpr.rsp + 8 }) →
      GoG prof L o gev gP gE Z t')
    (kf : cOk V X.cpu.gpr.rdi → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Aaa.aaa_at → (∃ c d, Y.cpu.gpr = cG V X.cpu.gpr c d) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 31 ∧ (∃ a c d, g' = { X.cpu.gpr with rax := a, rcx := c, rdx := d }) ∧ ¬ cOk V X.cpu.gpr.rdi) ∨
        (j' = 47 ∧ (∃ c d, g' = cG V X.cpu.gpr c d) ∧ cOk V X.cpu.gpr.rdi)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f16 f32 f64 f48 f40 fp (fun a c d hn _ => ⟨rfl, Or.inl ⟨rfl, ⟨a, c, d, rfl⟩, hn⟩⟩)
      (fun c d hy _ => ⟨rfl, Or.inr ⟨rfl, ⟨c, d, rfl⟩, hy⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, ⟨a, c', d, rfl⟩, hn⟩ | ⟨rfl, ⟨c', d, rfl⟩, hy⟩
  · -- `xor eax, eax; ret`
    refine (c_31 prof).run c hin (fun j' g' _ V' => j' = 33 ∧
        g' = { { X.cpu.gpr with rax := a, rcx := c', rdx := d } with rax := 0#64 } ∧ V' = V)
      hKY hAY hrY (by rw [hgY]; exact vc_31) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_33 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hra) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hn Z t₃ hKZ hAZ hrZ ⟨c', d, ?_⟩
    rw [hgZ, hgU]
    try rfl
  · -- the jump to `CItem::AreAllAllowed`
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_47 _) hinA (Aaa.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf hy Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) ⟨c', d, by rw [hg₂, hgY]⟩

end FV7z.Caa
