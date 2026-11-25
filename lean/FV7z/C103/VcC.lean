import FV7z.C103.VcB
/-!
# `init_cacheinfo`: the entry, the exit and the flag-heavy cut points (PLAN.md M, ctor 103)

The entry's six `push`es and the dispatch on the vendor, the exit's store of `rep_movsb_stop_threshold` and the
six `pop`s, the leaf-`0xB` loop's setup (`threads_l2`/`threads_l3` flags by `setg`/`sete`), its exits on the
level type, the `threads` adjustment by `cmp`/`sbb` and the jump table on the family.
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
open FV7z.Hin (tc t8)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-! ## Flag and byte facts -/

/-- `test r, r; je` taken: `r` is 0. -/
theorem sz (x : BitVec 32) (h : (x &&& x == 0) = true) : x = 0#32 := by
  rw [BitVec.and_self] at h
  first | exact beq_iff_eq.mp h | simpa using h

/-- `test r, r; jg` taken: `r` is not 0 ... -/
theorem c15 {f : Rflags} {r : BitVec 32} {af : Bool} (h : (f.arith (r &&& r) false false af).cond 15 = true) :
    r ≠ 0#32 := by
  intro e
  change (!((r &&& r == 0) || ((r &&& r).msb != false))) = true at h
  rw [e] at h
  exact absurd h (by decide)

/-- ... and not -1. -/
theorem c15m {f : Rflags} {r : BitVec 32} {af : Bool} (h : (f.arith (r &&& r) false false af).cond 15 = true) :
    r ≠ 4294967295#32 := by
  intro e
  change (!((r &&& r == 0) || ((r &&& r).msb != false))) = true at h
  rw [e] at h
  exact absurd h (by decide)

/-- `setg` after `test r, r` set: `r` is not 0. -/
theorem c15r {f : Rflags} {r : BitVec 32} {af : Bool}
    (h : (rfz (f.arith (r &&& r) false false af)).cond 15 = true) : r ≠ 0#32 := by
  intro e
  change (!((r &&& r == 0) || ((r &&& r).msb != false))) = true at h
  rw [e] at h
  exact absurd h (by decide)

theorem r15_2d {r : BitVec 64} (h : R15 r) (hb : decide (r.setWidth 32 = 2#32) = true) : r = 2#64 := by
  rcases h with e | e
  · exact e
  · rw [e] at hb
    exact absurd hb (by decide)

theorem r15_3d {r : BitVec 64} (h : R15 r) (hb : decide (r.setWidth 32 = 3#32) = true) : r = 3#64 := by
  rcases h with e | e
  · rw [e] at hb
    exact absurd hb (by decide)
  · exact e

theorem r15_2 {r : BitVec 64} (h : R15 r) (hb : decide (r.setWidth 32 = 2#32) = false) : r = 3#64 := by
  rcases h with e | e
  · rw [e] at hb
    exact absurd hb (by decide)
  · exact e

/-- `xor r32, r32; setcc r8l`. -/
theorem stz (x : BitVec 32) (b : Bool) :
    (x ^^^ x).setWidth 64 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool b).setWidth 8).setWidth 64 <<< 0 =
      (BitVec.ofBool b).setWidth 64 := by
  rw [BitVec.xor_self]
  cases b <;> decide

/-- A flag (0 or 1) and the low byte set by `setcc`. -/
theorem andc (b c : Bool) (r : BitVec 64) :
    ((BitVec.ofBool b).setWidth 64).setWidth 32 &&&
      (r &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool c).setWidth 8).setWidth 64 <<< 0).setWidth 32 =
      (BitVec.ofBool (b && c)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    cases b <;> cases c <;> first | simp | simp +decide | simp [Nat.testBit]
  · simp [h0]

/-- The two flags before the leaf-`0xB` loop: `setcc` into a cleared register, `and` with `setg`'s byte. -/
theorem fv (x : BitVec 32) (b c : Bool) (r : BitVec 64) :
    (((x ^^^ x).setWidth 64 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      ((BitVec.ofBool b).setWidth 8).setWidth 64 <<< 0).setWidth 32 &&&
      (r &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool c).setWidth 8).setWidth 64 <<< 0).setWidth 32
      ).setWidth 64 = ((BitVec.ofBool (b && c)).setWidth 32).setWidth 64 := by
  rw [stz, andc]

theorem fv01 (x : BitVec 32) (b c : Bool) (r : BitVec 64) :
    (((x ^^^ x).setWidth 64 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      ((BitVec.ofBool b).setWidth 8).setWidth 64 <<< 0).setWidth 32 &&&
      (r &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool c).setWidth 8).setWidth 64 <<< 0).setWidth 32
      ).setWidth 64 = 0#64 ∨
    (((x ^^^ x).setWidth 64 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      ((BitVec.ofBool b).setWidth 8).setWidth 64 <<< 0).setWidth 32 &&&
      (r &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool c).setWidth 8).setWidth 64 <<< 0).setWidth 32
      ).setWidth 64 = 1#64 := by
  rw [fv]
  cases b <;> cases c <;> decide

theorem fv1 {x : BitVec 32} {b c : Bool} {r : BitVec 64}
    (h : (((x ^^^ x).setWidth 64 &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      ((BitVec.ofBool b).setWidth 8).setWidth 64 <<< 0).setWidth 32 &&&
      (r &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) ||| ((BitVec.ofBool c).setWidth 8).setWidth 64 <<< 0).setWidth 32
      ).setWidth 64 = 1#64) : b = true ∧ c = true := by
  rw [fv] at h
  cases b <;> cases c <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- `cmp r9d, 1; sbb r9d, -1`: `threads` plus 1 unless 0. -/
theorem sbb9 (x : BitVec 32) (h : x.toNat ≤ 1023) :
    (((x - 4294967295#32 - (BitVec.ofBool (decide (x.toNat < 1))).setWidth 32).setWidth 64).setWidth 32).toNat ≤
      1024 := by
  rw [sw_64_32]
  by_cases h1 : x.toNat < 1
  · rw [decide_eq_true h1]
    have e : (BitVec.ofBool true).setWidth 32 = 1#32 := by decide
    rw [e]
    bv_omega
  · rw [decide_eq_false h1]
    have e : (BitVec.ofBool false).setWidth 32 = 0#32 := by decide
    rw [e]
    bv_omega

/-- The jump table's index at most 38. -/
theorem ja_le {k : BitVec 32} (h : (!(decide (k.toNat < 38) || decide (k = 38#32))) = false) : k.toNat ≤ 38 := by
  by_cases h1 : k.toNat < 38
  · omega
  · by_cases h2 : k = 38#32
    · rw [h2]
      decide
    · rw [decide_eq_false h1, decide_eq_false h2] at h
      exact absurd h (by decide)

theorem r8_2 {r8 : BitVec 64} (h : r8 = 0#64 ∨ r8 = 1#64 ∨ r8 = 2#64 ∨ r8 = 3#64)
    (h2 : (r8.setWidth 8 &&& 2#8 == 0) = false) : r8 = 2#64 ∨ r8 = 3#64 := by
  rcases h with e | e | e | e <;> rw [e] at h2 ⊢ <;> first | exact absurd h2 (by decide) | decide

theorem r8_1 {r8 : BitVec 64} (h : r8 = 0#64 ∨ r8 = 1#64 ∨ r8 = 2#64 ∨ r8 = 3#64)
    (h1 : (r8.setWidth 8 &&& 1#8 == 0) = false) : r8 = 1#64 ∨ r8 = 3#64 := by
  rcases h with e | e | e | e <;> rw [e] at h1 ⊢ <;> first | exact absurd h1 (by decide) | decide

/-- `ebx & 0xff`, not 0. -/
theorem lo255 (y : BitVec 32) : (((y &&& 255#32).setWidth 64).setWidth 32).toNat ≤ 255 := by
  rw [sw_64_32]
  exact and_le_r _ _

theorem pos255 (y : BitVec 32) (h : (y &&& 255#32 == 0) = false) :
    1 ≤ (((y &&& 255#32).setWidth 64).setWidth 32).toNat := by
  rw [sw_64_32]
  have h0 : (y &&& 255#32).toNat ≠ 0 := fun e => by
    have e' : y &&& 255#32 = 0#32 := BitVec.eq_of_toNat_eq e
    rw [e'] at h
    exact absurd h (by decide)
  omega

theorem dec255 (y : BitVec 32) (h : (y &&& 255#32 == 0) = false) :
    ((((y &&& 255#32) - 1#32).setWidth 64).setWidth 32).toNat ≤ 255 := by
  rw [sw_64_32]
  have h1 := and_le_r y 255#32
  have h0 : (y &&& 255#32).toNat ≠ 0 := fun e => by
    have e' : y &&& 255#32 = 0#32 := BitVec.eq_of_toNat_eq e
    rw [e'] at h
    exact absurd h (by decide)
  generalize y &&& 255#32 = a at h1 h0 ⊢
  have h1' : a.toNat ≤ 255 := h1
  bv_omega

/-! ## The entry and the exit -/

theorem vc_3504 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3504 n g V) : W_3504 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ent_foot hT
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_3504, W_3746, W_3537, W_4035, W_3546, W_3732, W_3744, W_3562, o0, o15, o1, o43, o2, o14, o3, Op.lda, Op.sta,
    Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma,
    Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  refine ⟨f1, f2, f3, f4, f5, f6, fC hT (by decide) (by decide),
    fun _ => ⟨fC hT (by decide) (by decide), Or.inl ⟨_, by decide, rfl, ⟨rfl, fun _ _ => rfl⟩, by d_ec⟩⟩,
    fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨rfl, fun _ _ => rfl⟩, by d_ec⟩,
    fun _ => ⟨fC hT (by decide) (by decide), fun _ => ⟨fun _ => ⟨fC hT (by decide) (by decide),
      fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, rfl, fun _ _ => rfl⟩,
        fun _ => Or.inl ⟨_, by decide, rfl, rfl, fun _ _ => rfl⟩⟩⟩,
      fun _ _ => Or.inl ⟨_, by decide, rfl, rfl, fun _ _ => rfl⟩⟩⟩⟩⟩

theorem vc_3710 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 3710 n g V) : W_3710 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨-, hs, hm⟩ := h
  try dsimp only at hs
  wpx [W_3710, o13, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia,
    Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  subst hs
  have lo := hT.lo
  have hi := hT.hi
  have e0 := t_fr g₀.rsp (by omega)
  have a0 := tc 8 e0 (by omega)
  have a1 := t8 a0 (by omega)
  have a2 := t8 a1 (by omega)
  have a3 := t8 a2 (by omega)
  have a4 := t8 a3 (by omega)
  have a5 := t8 a4 (by omega)
  have hm' := st_G hm (8029224#64) (toBytesLE rax 8) (Or.inr ⟨by decide, by rw [toBytesLE_length]; decide⟩)
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pops hT hm'
  obtain ⟨q, -⟩ := q_all g₀.rsp (by omega)
  exact ⟨fGw hT (Or.inr ⟨by decide, by decide⟩), fD hT (by omega) (by omega), fD hT (by omega) (by omega),
    fD hT (by omega) (by omega), fD hT (by omega) (by omega), fD hT (by omega) (by omega),
    fD hT (by omega) (by omega), Or.inr ⟨rfl, q, p1, p2, p3, p4, p5, p6, kd_of hT hm'⟩⟩

/-! ## The leaf-`0xB` loop's setup -/

theorem vc_3921 (h : Ih g₀ V₀ 3921 n g V) : W_3921 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨hs, hm⟩, hL, h8⟩ := h
  try dsimp only at hn hs h8
  subst hn
  obtain ⟨h15, h9, h10, h2⟩ := id hL
  try dsimp only at h9 h10 h2
  wpx [W_3921, W_4254, W_4264, W_4295, o30, o64, o65, o66, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc,
    Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr,
    Op.xormf, Op.ldf, Op.shr32z]
  intro _
  refine ⟨fun hz => ⟨fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, h9⟩, fun _ => ?_⟩,
    fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, hL, h8⟩⟩
  have h0 := sz _ hz
  intro _ _ _ _
  refine ⟨fun hd => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, h15, h9, h0,
      Or.inr (show BitVec.setWidth 64 1#32 = 1#64 by decide), fv01 _ _ _ _, fun e => ?_,
      fun _ => ⟨fun _ => c15 hd, fun e2 => absurd (h2 e2).1 (c15m hd)⟩⟩,
    fun _ _ _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, h15, h9, h0, fv01 _ _ _ _, fv01 _ _ _ _, fun e => ?_,
      fun e => ?_⟩⟩
  · obtain ⟨hb, hc⟩ := fv1 e
    exact ⟨r15_3d h15 hb, c15r hc⟩
  · obtain ⟨hb, hc⟩ := fv1 e
    exact ⟨r15_3d h15 hb, c15r hc⟩
  · obtain ⟨hb, hc⟩ := fv1 e
    have e2 := r15_2d h15 hb
    exact ⟨fun e3 => absurd (e2.symm.trans e3) (by decide), fun _ => c15r hc⟩

/-! ## `handle_amd`'s leaf `0x80000008` -/

theorem vc_4143 (h : Ih g₀ V₀ 4143 n g V) : W_4143 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hs, hm⟩ := h
  wpx [W_4143, W_4231, W_4239, o54, o62, Op.lda, Op.sta, Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx,
    Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf,
    Op.shr32z]
  intro _
  exact ⟨fun _ _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, hs, hm⟩, fun _ => Or.inl ⟨_, by decide, rfl, hs, hm⟩⟩,
    fun _ => Or.inl ⟨_, by decide, rfl, hs, hm⟩⟩

/-! ## The leaf-`0xB` loop's level types -/

theorem vc_4348 (h : Ih g₀ V₀ 4348 n g V) : W_4348 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨hs, hm⟩, hL, h10, hx⟩ := h
  try dsimp only at hn hs h10 hx
  subst hn
  obtain ⟨h15, h9, h13, h8, hb2, hb3⟩ := id hL
  try dsimp only at h9 h13 h8 hb2 hb3
  wpx [W_4348, W_4362, W_4366, W_4321, W_4435, W_4441, W_4374, o72, o73, o74, o68, o80, o81, o75, Op.lda, Op.sta,
    Op.sar64, Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma,
    Op.zxr, Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  refine ⟨fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, h9⟩, fun hb => ?_⟩
  intro _
  refine ⟨fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, h9⟩, fun hz => ?_⟩
  have r10le : (r10.setWidth 32).toNat ≤ 64 := by
    refine Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h10 fun e => ?_)
    rw [hx e] at hz
    exact absurd hz (by decide)
  refine ⟨fun _ => ⟨fun _ _ => ⟨fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, hL, r10le⟩,
      fun h2 => ⟨fun e15 => ?_, fun e15 => ?_⟩⟩, fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, hL, r10le⟩⟩,
    fun _ _ => ⟨fun _ => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, hL, r10le⟩,
      fun h1 => Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, hL, r10le, r8_1 h8 h1, pos255 _ hb, lo255 _⟩⟩⟩
  · have e2 := r15_2d h15 e15
    have e8 : r8 = 2#64 := by
      rcases r8_2 h8 h2 with e | e
      · exact e
      · exact absurd (e2.symm.trans (hb2 (Or.inr e)).1) (by decide)
    exact Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, ⟨h15, h9, h13, r10le, Or.inl e8⟩, e8, (hb3 (Or.inl e8)).2 e2,
      dec255 _ hb⟩
  · have e3 := r15_2 h15 e15
    rcases r8_2 h8 h2 with e | e
    · exact Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, ⟨h15, h9, h13, r10le, Or.inl e⟩, e3, (hb3 (Or.inl e)).1 e3⟩
    · exact Or.inl ⟨_, by c_om, rfl, ⟨hs, hm⟩, ⟨h15, h9, h13, r10le, Or.inr ⟨e, hb2 (Or.inr e)⟩⟩, e3,
        (hb3 (Or.inr e)).1 e3⟩

/-! ## `threads` after the loops, and the jump table on the family -/

theorem vc_4409 (h : Ih g₀ V₀ 4409 n g V) : W_4409 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, ⟨hs, hm⟩, h9⟩ := h
  try dsimp only at hs h9
  have h9' := sbb9 _ h9
  wpx [W_4409, W_4478, W_4484, W_4492, W_4421, W_4427, o77, o78, o35, o84, o79, Op.lda, Op.sta, Op.sar64, Op.cqo,
    Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr, Op.cmpmi,
    Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  intro _ _
  exact ⟨fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9'⟩,
      fun _ _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9'⟩,
        fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9', show (BitVec.setWidth 64 4294967295#32).toNat < 2 ^ 32 by
          decide⟩⟩⟩,
    fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9'⟩,
      fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9', sw_lt _⟩⟩⟩

theorem vc_4502 (hT : Te F Wl L fb g₀ V₀) (h : Ih g₀ V₀ 4502 n g V) : W_4502 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, ⟨hs, hm⟩, h9⟩ := h
  try dsimp only at hs
  -- `N9` on `r9` alone: unifying the whole register file would compute the jump table's read
  have h9 : (r9.setWidth 32).toNat ≤ 1024 := h9
  wpx [W_4502, W_4580, W_4589, W_4519, W_4532, W_4541, W_4553, o85, o37, o86, o87, o88, o89, Op.lda, Op.sta, Op.sar64,
    Op.cqo, Op.not32, Op.setcc, Op.xor8, Op.sxr, Op.ldsx, Op.andh, Op.testmia, Op.stia, Op.ldzxa, Op.imul3ma, Op.zxr,
    Op.cmpmi, Op.cmpmia, Op.cmpmr, Op.xormf, Op.ldf, Op.shr32z]
  refine ⟨fC hT (by decide) (by decide), fC hT (by decide) (by decide), fun _ => ⟨fun _ _ =>
      ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩⟩, fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩⟩⟩,
    fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9, sw_lt _⟩,
      fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9, sw_lt _⟩,
        fun _ => ⟨fun _ => Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9, sw_lt _⟩, fun hc => ?_⟩⟩⟩⟩⟩
  have hk := ja_le hc
  rcases jt_ent hT hm _ hk with e | e
  · exact ⟨ft_ent hT _ hk, 3967, lt_len (by decide), e, Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9, sw_lt _⟩⟩
  · exact ⟨ft_ent hT _ hk, 4570, lt_len (by decide), e, Or.inl ⟨_, by decide, rfl, ⟨hs, hm⟩, h9⟩⟩

end FV7z.C103
