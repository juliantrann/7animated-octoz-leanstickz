import FV7z.Ids.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NWindows::NFile::NFind::CDirEntry::IsDots ()` (PLAN.md §M, M1)

7-Zip 26.06's `CDirEntry::IsDots () const` at `0x455df0` in `7zzs` (`CPP/Windows/FileFind.h`; `objdump -d`), `this`
in `rdi`: a directory (the attribute byte at `this + 8`, `&` 0xfb, is 0) whose name (`Name`: its chars at `this + 16`,
its length at `this + 24`) is `.` or `..`. A leaf without a loop that writes no byte; `ret` at 23 and at 58.

- `isd`: what the code computes, as a proposition.
- `vc_0`: the code to a `ret`, `rax` = 1 if `isd`, else 0 (`rcx`, `rdx` changed).
- `ids_ok`: from the entry to the return address, only `rax`, `rcx`, `rdx` changed (and `rsp` popped).

Note: `rw`/`simpa` miss the `decide`s and literals of the `wpx` goal (another instance, `BitVec.ofNat` forms); take
facts by unification instead (`nd0`, `nd1`, `dt` with `{inst}`; `exact (sete1 _).trans (if_pos …)` for `sete`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ids

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_23 : pret <+: ids.drop 23 := by decide +kernel
theorem w_58 : pret <+: ids.drop 58 := by decide +kernel
theorem ret_23 (feat : Features) : Dec feat ids 23 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 23) (k := 0) (pret_0 feat) w_23 (Nat.zero_le _)
theorem ret_58 (feat : Features) : Dec feat ids 58 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)

/-- `CDirEntry::IsDots` of the entry at `p`: the attribute byte (`& 0xfb`) is 0, the name's length (4 bytes at
`p + 24`) is 1 or 2, its first char (at the pointer at `p + 16`) is `.`, and the second is `.` if the length is 2. -/
def isd (V : Addr → Byte) (p : Addr) : Prop :=
  ofBytesLE 8 ((byteAddrs (p + 8#64) 1).map V) &&& 251#8 = 0#8 ∧
  (rdd(V, p + 24#64) = 1#32 ∨ rdd(V, p + 24#64) = 2#32) ∧
  ofBytesLE 8 ((byteAddrs rdq(V, p + 16#64) 1).map V) = 46#8 ∧
  (rdd(V, p + 24#64) = 1#32 ∨ ofBytesLE 8 ((byteAddrs (rdq(V, p + 16#64) + 1#64) 1).map V) = 46#8)

instance (V : Addr → Byte) (p : Addr) : Decidable (isd V p) := by unfold isd; infer_instance

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

/-- `lea ecx, [rdx - 1]; cmp ecx, 1; jbe`: taken only for a length of 1 or 2. -/
theorem lc (n : BitVec 32)
    (h : (decide ((BitVec.setWidth 32 (BitVec.setWidth 64 n + 18446744073709551615#64)).toNat < 1) ||
      decide (BitVec.setWidth 32 (BitVec.setWidth 64 n + 18446744073709551615#64) = 1#32)) = true) :
    n = 1#32 ∨ n = 2#32 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · left; bv_omega
  · right; bv_omega

/-! `decide` with whatever instance the code's `wpx` goal carries (`rw [decide_eq_true h]` misses it). -/
theorem nd1 {p : Prop} {inst : Decidable p} (h : (!@decide p inst) = true) : ¬p :=
  of_decide_eq_false (by simpa using h)
theorem nd0 {p : Prop} {inst : Decidable p} (h : (!@decide p inst) = false) : p :=
  of_decide_eq_true (by simpa using h)
theorem dt {p : Prop} {inst : Decidable p} (h : p) : @decide p inst = true := @decide_eq_true p inst h
theorem df {p : Prop} {inst : Decidable p} (h : ¬p) : @decide p inst = false := @decide_eq_false p inst h

/-- `mov eax, 1; …; sete al` of a flag `b`. -/
theorem sete1 (b : Bool) :
    BitVec.setWidth 64 1#32 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.ofBool b)) <<< 0 = if b then 1#64 else 0#64 := by
  cases b <;> decide

variable {F : Footprint} {Wl : List Rgn}

/-- The code from the entry to the `ret` at 23 or at 58. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i))
    (fs0 : ∀ i < 1, Foot F.data (Addr.add rdq(V, g.rdi + 16#64) i))
    (fs1 : ∀ i < 1, Foot F.data (Addr.add (rdq(V, g.rdi + 16#64) + 1#64) i))
    (h : ∀ j ra rc rd fl, (j = 23 ∨ j = 58) → ra = (if isd V g.rdi then 1#64 else 0#64) →
      Q j { g with rax := ra, rcx := rc, rdx := rd } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f24 f16 fs0 fs1 h ⊢
  wpx [W_0, W_12, W_32, W_41, W_51, o0, o1, o2, o3, o4, Op.cmpmi, Op.testmi, Op.setcc]
  refine fun _ => ⟨f8, fun _ => ⟨fun hA => ?_, fun hA => ⟨f24, fun hB => ⟨f16, fs0, fun hC => ?_,
    fun hC => ⟨fun hD => ?_, fun hD => ⟨fs1, ?_⟩⟩⟩, fun hB => ?_⟩⟩⟩
  · have ha : ¬ ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) &&& 251#8 = 0#8 := by simpa using hA
    exact h 23 _ _ _ _ (.inl rfl) (by rw [if_neg fun hd => ha hd.1]; exact xz _)
  · have hc : ¬ ofBytesLE 8 ((byteAddrs rdq(V, rdi + 16#64) 1).map V) = 46#8 := nd1 hC
    exact h 23 _ _ _ _ (.inl rfl) (by rw [if_neg fun hd => hc hd.2.2.1]; exact xz _)
  · have ha : ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) &&& 251#8 = 0#8 := by simpa using hA
    have hc : ofBytesLE 8 ((byteAddrs rdq(V, rdi + 16#64) 1).map V) = 46#8 := nd0 hC
    have hn : rdd(V, rdi + 24#64) = 1#32 := of_decide_eq_true hD
    exact h 23 _ _ _ _ (.inl rfl) (by rw [if_pos ⟨ha, .inl hn, hc, .inl hn⟩]; decide)
  · have ha : ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) &&& 251#8 = 0#8 := by simpa using hA
    have hc : ofBytesLE 8 ((byteAddrs rdq(V, rdi + 16#64) 1).map V) = 46#8 := nd0 hC
    have hn : ¬ rdd(V, rdi + 24#64) = 1#32 := of_decide_eq_false hD
    have hb := lc rdd(V, rdi + 24#64) hB
    refine h 58 _ _ _ _ (.inr rfl) ?_
    by_cases hy : ofBytesLE 8 ((byteAddrs (rdq(V, rdi + 16#64) + 1#64) 1).map V) = 46#8
    · rw [if_pos ⟨ha, hb, hc, .inr hy⟩]; exact (sete1 _).trans (if_pos (dt hy))
    · rw [if_neg fun hd => hy (hd.2.2.2.resolve_left hn)]
      exact (sete1 _).trans (if_neg fun e => hy (of_decide_eq_true e))
  · have hn : ¬ (rdd(V, rdi + 24#64) = 1#32 ∨ rdd(V, rdi + 24#64) = 2#32) := by
      rintro (hn | hn) <;> rw [hn] at hB <;> exact absurd hB (by decide)
    exact h 23 _ _ _ _ (.inl rfl) (by rw [if_neg fun hd => hn hd.2.1]; exact xz _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDirEntry::IsDots ()` (`this` = `rdi`) from its entry: at the return address with the bytes as they were,
`rax` = 1 if `isd`, else 0, `rcx` and `rdx` some values, the other registers as at the entry and `rsp` 8 above
(`kr`). It reads the 5 places of `isd` (`f8` … `fs1`). -/
theorem ids_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ids_at ids)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ids_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f8 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f24 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fs0 : ∀ i < 1, Foot F.data (Addr.add rdq(V, X.cpu.gpr.rdi + 16#64) i))
    (fs1 : ∀ i < 1, Foot F.data (Addr.add (rdq(V, X.cpu.gpr.rdi + 16#64) + 1#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr : ∀ (Z' : State) (t' : Nat) (ra rc rd : BitVec 64),
      ra = (if isd V X.cpu.gpr.rdi then 1#64 else 0#64) → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := ra, rcx := rc, rdx := rd, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => (j' = 23 ∨ j' = 58) ∧
      (∃ ra rc rd : BitVec 64, g' = { X.cpu.gpr with rax := ra, rcx := rc, rdx := rd } ∧
        ra = (if isd V X.cpu.gpr.rdi then 1#64 else 0#64)) ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f8 f24 f16 fs0 fs1 fun j ra rc rd _ hj hr => ⟨hj, ⟨ra, rc, rd, rfl, hr⟩, rfl⟩) ?_
  rintro j' g fl V₂ ⟨hj, ⟨ra, rc, rd, rfl, hr⟩, hV₂⟩ U t₁ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  have hlt : j' < ids.length := lt_len (by rcases hj with rfl | rfl <;> decide)
  have hdec : ∀ feat, Dec feat ids j' (FV7z.mk .ret 64 [] 1) := by
    rcases hj with rfl | rfl
    · exact ret_23
    · exact ret_58
  refine c.s_ret hKU hAU hin hlt hrU (hdec _) (by rw [hsU]; exact hl) hin₂ h₂ (by rw [hsU]; exact hra) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z' t₂ ra rc rd hr hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Ids
