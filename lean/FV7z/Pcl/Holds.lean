import FV7z.Pcl.Cuts
import FV7z.Vcl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.BlkOps16
import FV7z.Tun.Inv
/-!
# `NWindows::NCOM::PropVariant_Clear` (PLAN.md §M, M1)

7-Zip 26.06's `PropVariant_Clear (PROPVARIANT *prop)` at `0x456fb0` in `7zzs` (`CPP/Windows/PropVariant.cpp`;
`objdump -d`), with `prop` = `p` in `rdi`. `push rbx; rbx = p`, then on the tag `vt` (the 2 bytes at `p`, read after the
push):

- a "simple" tag (`Simple`: 0..7, by `cmp ax, 7; jbe`, or 10, 11, 16..23, 64, by `sub eax, 10; cmp ax, 54; ja` and
  `bt` of the mask `0x40000000003fc3`): `vt` = 0 (62), then `wReserved1..3` = 0 (the 2 bytes at `p + 2`, the 4 at
  `p + 4`), the 8 bytes at `p + 8` = 0, `rax` = 0, `pop rbx; ret` (91);
- else `call VariantClear (p)` (45, `Vcl.vcl_at`), a hypothesis `kf` as in `FV7z/Act/Holds.lean`: a continuation at
  its entry, given the run from its return (`pcl_at + 50`, `rsp` 8 below the entry's, `rbx` = `p`, the saved `rbx` and
  the return address as they were, and the callee's own post `Pc`). Back from it: if `eax` ≠ 0 or `vt` ≠ 0, `pop rbx;
  ret` (61, `kr1`); else the same zeroing as above and the `ret` at 91 (`kr2`).

`rax`, `rdx` on the way to the `call` (the tag and the mask) are left open (`gA`). The object (16 bytes at `p`) lies
outside the frame (`hd`).

- `Simple`, `s_jbe`, `s_ja`, `s_bt`, `s_nbt`: the tag test, from the flags `wpx` leaves (`bt_tab`: the mask's bits).
- `gA`, `V0`, `V1`: the registers after the test, the bytes after the push, the bytes after the zeroing.
- `vc_0`, `vc_42`, `vc_50`, `vc_60`, `vc_62`, `vc_67`: the verification conditions of the pieces.
- `pcl_ok`: from the entry: simple, to the return address (`kn`); else through `VariantClear` (`kf`) to the return
  address (`kr1`, `kr2`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pcl

/-- The `call` to `VariantClear`. -/
def pcall : List Byte := [0xe8, 0x3e, 0x91, 0x14, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1347902] 5) := by dec_rfl
theorem wc_45 : pcall <+: pcl.drop 45 := by decide +kernel
theorem call_45 (feat : Features) : Dec feat pcl 45 (FV7z.mk .call 64 [.rel 1347902] 5) :=
  Dec.shift (j := 45) (k := 0) (pcall_0 feat) wc_45 (Nat.zero_le _)
theorem tgt_45 : pcl_at.add (45 + 5) + BitVec.ofNat 64 1347902 = Vcl.vcl_at.add 0 := by decide

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_61 : pret <+: pcl.drop 61 := by decide +kernel
theorem ret_61 (feat : Features) : Dec feat pcl 61 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 61) (k := 0) (pret_0 feat) w_61 (Nat.zero_le _)
theorem w_91 : pret <+: pcl.drop 91 := by decide +kernel
theorem ret_91 (feat : Features) : Dec feat pcl 91 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 91) (k := 0) (pret_0 feat) w_91 (Nat.zero_le _)

/-- The tag of the variant at `p`. -/
abbrev vt (V : Addr → Byte) (p : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs p 2).map V)

/-- The tags the code clears by itself: 0..7, 10, 11, 16..23 and 64. -/
def Simple (v : BitVec 16) : Prop :=
  v.toNat < 8 ∨ v.toNat = 10 ∨ v.toNat = 11 ∨ (16 ≤ v.toNat ∧ v.toNat < 24) ∨ v.toNat = 64

/-- The bits of the mask `0x40000000003fc3`. -/
theorem bt_tab : ∀ k < 55, ((18014398509498307#64).getLsbD k = true ↔ (k < 2 ∨ (6 ≤ k ∧ k < 14) ∨ k = 54)) := by
  decide +kernel

theorem tn_t (v : BitVec 16) : (BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat = v.toNat := by
  have := v.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  simp only [Nat.reducePow] at this ⊢
  omega

theorem tn_u (v : BitVec 16) :
    (BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32)).toNat = (v.toNat + 4294967286) % 4294967296 % 65536 := by
  have := v.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this ⊢
  omega

theorem tn_w (v : BitVec 16) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 v - 10#32)).toNat = (v.toNat + 4294967286) % 4294967296 := by
  have := v.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this ⊢
  omega

/-- `cmp ax, 7; jbe` taken. -/
theorem s_jbe (v : BitVec 16)
    (h : (decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat < 7) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v) = 7#16)) = true) : Simple v := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, BitVec.toNat_eq, tn_t, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at h
  unfold Simple
  omega

/-- `jbe` not taken, `cmp ax, 54; ja` taken. -/
theorem s_ja (v : BitVec 16)
    (h1 : (decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat < 7) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v) = 7#16)) = false)
    (h2 : (!(decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32)).toNat < 54) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32) = 54#16))) = true) : ¬ Simple v := by
  have := v.isLt
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, BitVec.toNat_eq, tn_t, tn_u,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1 h2 this
  unfold Simple
  omega

/-- Neither `jbe` nor `ja` taken: the tag minus 10 is below 55. -/
theorem s_rng (v : BitVec 16)
    (h1 : (decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat < 7) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v) = 7#16)) = false)
    (h2 : (!(decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32)).toNat < 54) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32) = 54#16))) = false) :
    10 ≤ v.toNat ∧ v.toNat < 65 ∧
      (BitVec.setWidth 64 (BitVec.setWidth 32 v - 10#32)).toNat % 64 = v.toNat - 10 := by
  have := v.isLt
  rw [tn_w]
  simp only [Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
    BitVec.toNat_eq, tn_t, tn_u, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1 h2 this
  omega

/-- `bt` sets `cf`: `jb` taken. -/
theorem s_bt (v : BitVec 16)
    (h1 : (decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat < 7) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v) = 7#16)) = false)
    (h2 : (!(decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32)).toNat < 54) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32) = 54#16))) = false)
    (h3 : (18014398509498307#64).getLsbD ((BitVec.setWidth 64 (BitVec.setWidth 32 v - 10#32)).toNat % 64) = true) :
    Simple v := by
  obtain ⟨r1, r2, r3⟩ := s_rng v h1 h2
  rw [r3] at h3
  have := (bt_tab _ (by omega)).mp h3
  unfold Simple
  omega

/-- `bt` clears `cf`: `jb` not taken. -/
theorem s_nbt (v : BitVec 16)
    (h1 : (decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v)).toNat < 7) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v) = 7#16)) = false)
    (h2 : (!(decide ((BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32)).toNat < 54) ||
      decide (BitVec.setWidth 16 (BitVec.setWidth 32 v - 10#32) = 54#16))) = false)
    (h3 : (18014398509498307#64).getLsbD ((BitVec.setWidth 64 (BitVec.setWidth 32 v - 10#32)).toNat % 64) = false) :
    ¬ Simple v := by
  obtain ⟨r1, r2, r3⟩ := s_rng v h1 h2
  rw [r3] at h3
  have h4 : ¬ (v.toNat - 10 < 2 ∨ (6 ≤ v.toNat - 10 ∧ v.toNat - 10 < 14) ∨ v.toNat - 10 = 54) := by
    intro hh
    have h5 := (bt_tab _ (by omega)).mpr hh
    rw [h3] at h5
    exact absurd h5 (by decide)
  unfold Simple
  omega

/-- `test eax, eax` gave not zero. -/
theorem tz1 (x : BitVec 32) (h : (!x &&& x == 0) = true) : ¬ x = 0 := by
  simp only [BitVec.and_self, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact h

/-- `test eax, eax` gave zero. -/
theorem tz0 (x : BitVec 32) (h : (!x &&& x == 0) = false) : x = 0 := by
  simp only [BitVec.and_self, Bool.not_eq_false', beq_iff_eq] at h
  exact h

/-- The registers after the test: `rbx` = `p`, `rbx` pushed, `rax` and `rdx` as the test left them. -/
abbrev gA (g : Gprs) (a d : BitVec 64) : Gprs :=
  { g with rax := a, rdx := d, rbx := g.rdi, rsp := g.rsp - 8 }

/-- The bytes after `push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The bytes after `wReserved1..3` = 0 and the 8 bytes at `b + 8` = 0. -/
abbrev V1 (V : Addr → Byte) (b : Addr) : Addr → Byte :=
  Vst (Vst (Vst V (b + 4#64) (toBytesLE (0#32) 4)) (b + 2#64) (toBytesLE (0#16) 2)) (b + 8#64) (toBytesLE (0#64) 8)

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; movzx eax, word [rdi]; mov rbx, rdi`, the tag test: a simple tag to 62, else to 42. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (f0 : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h62 : Simple (vt (V0 V g) g.rdi) → ∀ a d fl, Q 62 (gA g a d) fl (V0 V g))
    (h42 : ¬ Simple (vt (V0 V g) g.rdi) → ∀ a d fl, Q 42 (gA g a d) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vt, V0, gA] at hs1 f0 h62 h42 ⊢
  wpx [W_0, W_17, W_26, o0, o1, o2, Op.bt64]
  exact ⟨hs1, f0, fun h1 => h62 (s_jbe _ h1) _ _ _, fun h1 => ⟨fun h2 => h42 (s_ja _ h1 h2) _ _ _,
    fun h2 fl hb => ⟨fun h3 => h62 (s_bt _ h1 h2 (hb.symm.trans h3)) _ _ _,
      fun h3 => h42 (s_nbt _ h1 h2 (hb.symm.trans h3)) _ _ _⟩⟩⟩

/-- `mov rdi, rbx` to the `call` at 45. -/
theorem vc_42 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 45 { g with rdi := g.rbx } fl V) : W_42 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_42, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `VariantClear`: `test eax, eax; jne` to 60, else `cmp word [rbx], 0; je` to 67, else to 60. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : BitVec.setWidth 32 g.rax = 0 → ∀ i < 2, Foot F.data (Addr.add g.rbx i))
    (h60 : (¬ BitVec.setWidth 32 g.rax = 0 ∨ ¬ vt V g.rbx = 0#16) → ∀ fl, Q 60 g fl V)
    (h67 : BitVec.setWidth 32 g.rax = 0 → vt V g.rbx = 0#16 → ∀ fl, Q 67 g fl V) :
    W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vt] at f0 h60 h67 ⊢
  wpx [W_50, W_54, o4, o5, Op.cmpmi]
  intro af
  exact ⟨fun h => h60 (Or.inl (tz1 _ h)) _, fun h => ⟨f0 (tz0 _ h), fun h' => h67 (tz0 _ h) (of_decide_eq_true h') _,
    fun h' => h60 (Or.inr (of_decide_eq_false h')) _⟩⟩

/-- `pop rbx` to the `ret` at 61. -/
theorem vc_60 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 61 { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) : W_60 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_60, o6]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor edx, edx; mov [rbx], dx` to 67. -/
theorem vc_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 2, Foot Wl (Addr.add g.rbx i))
    (h : ∀ fl, Q 67 { g with rdx := 0#64 } fl (Vst V g.rbx (toBytesLE 0#16 2))) : W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_62, o7, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax; mov dword [rbx + 4], 0; mov [rbx + 2], ax; xor eax, eax; mov qword [rbx + 8], 0; pop rbx` to the
`ret` at 91. -/
theorem vc_67 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw4 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 4#64) i)) (fw2 : ∀ i < 2, Foot Wl (Addr.add (g.rbx + 2#64) i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 91 { g with rax := 0#64, rbx := rdq(V1 V g.rbx, g.rsp), rsp := g.rsp + 8 } fl (V1 V g.rbx)) :
    W_67 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw4 fw2 fw8 hl h ⊢
  wpx [W_67, o8, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `PropVariant_Clear (prop)` (`prop` = `rdi`) from its entry. A simple tag: at the return address with the tag,
`wReserved1..3` and the 8 bytes at `p + 8` = 0, `rax` = `rdx` = 0 (`kn`). Else: at `VariantClear`'s entry with `rsp`
16 below the entry's, `rbx` = `p` and `rbx` and the return address into `PropVariant_Clear` pushed (`kf`); if the
callee returns to `pcl_at + 50` with `rsp`, `rbx`, the saved `rbx` and the return address as they were, the run reaches
that return address: `eax` ≠ 0 or the tag ≠ 0 with the bytes as the callee left them (`kr1`), else with the zeroing
above and `rax` = 0 (`kr2`); `rbx`, `rsp` restored. -/
theorem pcl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pcl_at pcl)
    (hinV : CodeIn L Vcl.vcl_at Vcl.vcl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pcl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 2, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw2 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (fw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 4#64) i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : Simple (vt V X.cpu.gpr.rdi) → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (V1 (Vst (V0 V X.cpu.gpr) X.cpu.gpr.rdi (toBytesLE 0#16 2)) X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : ¬ Simple (vt V X.cpu.gpr.rdi) → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (pcl_at.add 50) 8)) →
      Y.cpu.rip = Vcl.vcl_at → (∃ a d, Y.cpu.gpr = (gA X.cpu.gpr a d).set 4 (X.cpu.gpr.rsp - 16)) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pcl_at.add 50 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' →
      (¬ BitVec.setWidth 32 Z.cpu.gpr.rax = 0 ∨ ¬ vt V' X.cpu.gpr.rdi = 0#16) → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr2 : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' →
      BitVec.setWidth 32 Z.cpu.gpr.rax = 0 → vt V' X.cpu.gpr.rdi = 0#16 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V1 V' X.cpu.gpr.rdi) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  have t2 : (X.cpu.gpr.rdi + 2#64).toNat = X.cpu.gpr.rdi.toNat + 2 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t4 : (X.cpu.gpr.rdi + 4#64).toNat = X.cpu.gpr.rdi.toNat + 4 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes stored by `push rbx`, by `mov [rbx], dx` and by the zeroing
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  have mz : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 2 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (Vst W X.cpu.gpr.rdi (toBytesLE 0#16 2)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; exact h)
  have m1 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (V1 W X.cpu.gpr.rdi) = (byteAddrs x 8).map W := by
    intro W x hx h
    have a1 := Tun.rd_Vst (Vst (Vst W (X.cpu.gpr.rdi + 4#64) (toBytesLE (0#32) 4)) (X.cpu.gpr.rdi + 2#64)
      (toBytesLE (0#16) 2)) (X.cpu.gpr.rdi + 8#64) (toBytesLE (0#64) 8) x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)
    have a2 := Tun.rd_Vst (Vst W (X.cpu.gpr.rdi + 4#64) (toBytesLE (0#32) 4)) (X.cpu.gpr.rdi + 2#64)
      (toBytesLE (0#16) 2) x 8 (by rw [toBytesLE_length, t2]; omega) hx (by rw [toBytesLE_length, t2]; omega)
    have a3 := Tun.rd_Vst W (X.cpu.gpr.rdi + 4#64) (toBytesLE (0#32) 4) x 8 (by rw [toBytesLE_length, t4]; omega) hx
      (by rw [toBytesLE_length, t4]; omega)
    exact a1.trans (a2.trans a3)
  have htg : vt (V0 V X.cpu.gpr) X.cpu.gpr.rdi = vt V X.cpu.gpr.rdi := by
    show ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8))) =
      ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map V)
    rw [m8 X.cpu.gpr.rdi 2 (by omega) (by omega)]
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have f0 : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => c.hws _ (fw0 i hi)
  have hrip' : X.cpu.rip = pcl_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the tag test
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V0 V X.cpu.gpr ∧
      ((j' = 62 ∧ Simple (vt (V0 V X.cpu.gpr) X.cpu.gpr.rdi) ∧ ∃ a d, g' = gA X.cpu.gpr a d) ∨
       (j' = 42 ∧ ¬ Simple (vt (V0 V X.cpu.gpr) X.cpu.gpr.rdi) ∧ ∃ a d, g' = gA X.cpu.gpr a d))) hK hA hrip'
    (vc_0 hs1 f0 (fun hs a d _ => ⟨rfl, Or.inl ⟨rfl, hs, a, d, rfl⟩⟩)
      (fun hn a d _ => ⟨rfl, Or.inr ⟨rfl, hn, a, d, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, ⟨rfl, hs, a, d, rfl⟩ | ⟨rfl, hn, a, d, rfl⟩⟩ Y t₁ hKY hAY hrY hgY -
  · -- a simple tag: `vt` = 0, the zeroing, the `ret` at 91
    subst V₁
    rw [htg] at hs
    have hsb : rdq(V1 (Vst (V0 V X.cpu.gpr) X.cpu.gpr.rdi (toBytesLE 0#16 2)) X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) =
        X.cpu.gpr.rbx := by
      rw [m1 _ _ hq8 (by rw [tn8]; omega), mz _ _ hq8 (by rw [tn8]; omega),
        Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8, ofBytesLE_toBytesLE (n := 8) rfl]
    have hrs : rdq(V1 (Vst (V0 V X.cpu.gpr) X.cpu.gpr.rdi (toBytesLE 0#16 2)) X.cpu.gpr.rdi, X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [m1 _ _ hp8 (by omega), mz _ _ hp8 (by omega), m8 _ 8 hp8 (by omega)]
      exact hra
    refine (c_62 prof).run c hin (fun j' g' _ V'' => j' = 67 ∧ g' = { gA X.cpu.gpr a d with rdx := 0#64 } ∧
        V'' = Vst (V0 V X.cpu.gpr) X.cpu.gpr.rdi (toBytesLE 0#16 2)) hKY hAY hrY
      (by rw [hgY]; exact vc_62 fw0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    refine (c_67 prof).run c hin (fun j' g' _ V'' => j' = 91 ∧ g' = { X.cpu.gpr with rax := 0#64, rdx := 0#64 } ∧
        V'' = V1 (Vst (V0 V X.cpu.gpr) X.cpu.gpr.rdi (toBytesLE 0#16 2)) X.cpu.gpr.rdi) hKU hAU hrU
      (by
        rw [hgU]
        exact vc_67 fw4 fw2 fw8 h8 fun _ => ⟨rfl, (by dsimp only [gA]; rw [hsb, e8]; try rfl), rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₃
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_91 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hrs) ?_
    rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hs Z t₄ hKZ hAZ hrZ ?_
    rw [hgZ, hgU₂]
    try rfl
  · -- else: `mov rdi, rbx; call VariantClear`
    subst V₁
    rw [htg] at hn
    refine (c_42 prof).run c hin (fun j' g' _ V'' => j' = 45 ∧ g' = gA X.cpu.gpr a d ∧ V'' = V0 V X.cpu.gpr)
      hKY hAY hrY (by rw [hgY]; exact vc_42 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₁ t₂ hK₁ hA₁ hr₁ hg₁ -
    subst V₂
    have hs₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₁]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y₁.cpu.gpr.rsp - 8) i) := by rw [hs₁, e16]; exact hs2
    refine c.s_call_x hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_45 _) hinV (tgt := 0) (Vcl.lt_len (by decide))
      tgt_45 hst ?_
    rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hs₁, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gA X.cpu.gpr a d).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hg₁]
      exact congrArg (fun v => (gA X.cpu.gpr a d).set 4 v) e16
    refine kf hn Y₂ t₃ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) ⟨a, d, hg₂'⟩ ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
    have hb1 : rdq(V1 V' X.cpu.gpr.rdi, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [m1 V' _ hq8 (by rw [tn8]; omega)]
      exact hb
    have hr1 : rdq(V1 V' X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [m1 V' _ hp8 (by omega)]
      exact hr'
    refine (c_50 prof).run c hin (fun j' g' _ V'' => g' = Z.cpu.gpr ∧ V'' = V' ∧
        ((j' = 60 ∧ (¬ BitVec.setWidth 32 Z.cpu.gpr.rax = 0 ∨ ¬ vt V' X.cpu.gpr.rdi = 0#16)) ∨
         (j' = 67 ∧ BitVec.setWidth 32 Z.cpu.gpr.rax = 0 ∧ vt V' X.cpu.gpr.rdi = 0#16))) hKZ hAZ hrZ
      (vc_50 (fun _ => by rw [hzb]; exact f0)
        (fun hh _ => ⟨rfl, rfl, Or.inl ⟨rfl, by rw [hzb] at hh; exact hh⟩⟩)
        (fun h1 h2 _ => ⟨rfl, rfl, Or.inr ⟨rfl, h1, by rw [hzb] at h2; exact h2⟩⟩)) ?_
    rintro j' g fl V₃ ⟨rfl, hV₃, ⟨rfl, hc⟩ | ⟨rfl, hz, hv⟩⟩ U t₃ hKU hAU hrU hgU -
    · -- `pop rbx; ret` (61)
      subst V₃
      refine (c_60 prof).run c hin (fun j' g' _ V'' => j' = 61 ∧
          g' = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKU hAU hrU
        (by rw [hgU]; exact vc_60 (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, hb, e8], rfl⟩) ?_
      rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₄
      have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
      refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_61 _) (by rw [hsU₂]; exact hl) hin₂ h₂
        (by rw [hsU₂]; exact hr') ?_
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine kr1 Z V' Z' t₅ hPc hc hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU₂]
      try rfl
    · -- the zeroing, the `ret` at 91
      subst V₃
      refine (c_67 prof).run c hin (fun j' g' _ V'' => j' = 91 ∧
          g' = { Z.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
          V'' = V1 V' X.cpu.gpr.rdi) hKU hAU hrU
        (by
          rw [hgU]
          exact vc_67 (by rw [hzb]; exact fw4) (by rw [hzb]; exact fw2) (by rw [hzb]; exact fw8)
            (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzb, hzs, hb1, e8], by rw [hzb]⟩) ?_
      rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₄
      have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
      refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_91 _) (by rw [hsU₂]; exact hl) hin₂ h₂
        (by rw [hsU₂]; exact hr1) ?_
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine kr2 Z V' Z' t₅ hPc hz hv hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU₂]
      try rfl

end FV7z.Pcl
