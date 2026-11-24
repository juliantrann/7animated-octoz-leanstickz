import FV7z.Icw.Inv
/-!
# `intel_check_word`: the entry, the byte loop and the way out (PLAN.md M, ctor 103)

The cut points' conditions from `Inv.lean` for the entry (464), the byte loop (558, 567, 630, 752), the binary search
in `intel_02_known` (640, 656, 682) and the way out (717, 719).
-/
namespace FV7z.Icw
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length lt_len)
set_option linter.unusedSimpArgs false

variable {prof : Profile} {L : List (Addr × List Byte)} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

theorem vc_464 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 464 n g V) : W_464 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hr := hT.rdi
  obtain ⟨f1, f2, f3, f4⟩ := st4 hT.st
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hr' : rdi = 188#64 ∨ rdi = 191#64 ∨ rdi = 194#64 := hr
  wpx [W_464, W_472, W_525, W_763, o0, o1, o2, o19, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc,
    Op.shr32z]
  intro _
  refine ⟨fun _ _ => Or.inr ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨f1, f2, f3, f4, ?_⟩⟩
  intros
  refine ⟨fun _ => Or.inl ⟨2, by decide, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩,
    fun _ => Or.inl ⟨_, m464 _, rfl, ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  first
  | exact rd464 hr'
  | rcases hr' with rfl | rfl | rfl <;> (try simp -implicitDefEqProofs only []) <;> decide +kernel

theorem vc_558 (h : Ih g₀ V₀ 558 n g V) : W_558 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd
  subst hn
  wpx [W_558, o4, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro fl hz
  have hz' : fl.zf = (BitVec.setWidth 32 rsi >>> 8 == 0) := by first | exact hz (by decide) | exact hz
  exact ⟨fun _ => Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, m4⟩,
    fun h0 => Or.inl ⟨_, m_shr _ hz' h0 900 1 (by decide), rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩⟩

theorem vc_567 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 567 n g V) : W_567 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd
  subst hn
  have w4 := st1 m4 (Or.inr b2) 1#8
  wpx [W_567, W_577, W_588, W_593, W_599, W_610, W_621, W_766, W_544, o5, o6, o7, o8, o9, o10, o11, o23, o3,
    Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  refine ⟨fun _ => ⟨fun i hi => by rw [b2]; exact hT.p3 i hi, fun _ => Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, w4⟩,
      fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, w4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩⟩,
    fun _ => ⟨fun _ _ => Or.inl ⟨995, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, hrd⟩,
      fun _ => ⟨fun _ => ?_, fun _ => ⟨fun _ => ?_, fun h9 => ⟨fun i hi => by rw [b3]; exact hT.fam i hi,
        fun _ => ?_, fun _ => ⟨fun i hi => by rw [b4]; exact hT.mdl i hi, fun _ => ?_, fun _ => ?_⟩⟩⟩⟩⟩⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, r194 hrd h9⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, r194 hrd h9⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, r621 hrd h9⟩

theorem vc_630 (h : Ih g₀ V₀ 630 n g V) : W_630 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd
  subst hn
  wpx [W_630, o12, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro _
  exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, by icw_om, by icw_om⟩

theorem vc_752 (h : Ih g₀ V₀ 752 n g V) : W_752 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, -⟩, hd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hd
  subst hn
  wpx [W_752, o22, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, Or.inr (Or.inr ⟨hd, sw9⟩)⟩

theorem vc_640 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 640 n g V) : W_640 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, hl, hd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd hl hd
  subst hn b5
  obtain ⟨k1, k2⟩ := mid1 r10 rdx hl hd
  have hx := ix1 ((r10 + rdx) >>> 1) (by omega)
  wpx [W_640, o13, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro fl _
  exact ⟨tabB hT _ 1 (by rw [hx]; omega) (by rw [hx]; omega),
    fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩, _, by omega, hx⟩,
    fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩, k1, k2, hd⟩⟩

theorem vc_656 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 656 n g V) : W_656 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, h1, h2, hd⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd h1 h2 hd
  subst hn b5
  have hi := inc64 rax (by omega)
  wpx [W_656, W_658, W_663, W_736, W_745, o14, o15, o21, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc,
    Op.shr32z]
  refine ⟨fun _ => ⟨fun hc => ?_, fun _ => ?_⟩, fun _ => ⟨fun _ => ?_, fun ho => ?_⟩⟩
  · have hc' := of_decide_eq_true hc
    exact Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩, hc', hd⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩
  · exact Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩
  · have hlt := orf ho
    obtain ⟨k1, k2⟩ := mid1 r10 rax hlt (by omega)
    have hx := ix1 ((r10 + rax) >>> 1) (by omega)
    intro fl _
    exact ⟨tabB hT _ 1 (by rw [hx]; omega) (by rw [hx]; omega),
      fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩, k1, k2, by omega⟩,
      fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, rfl⟩, hrd⟩, _, by omega, hx⟩⟩

theorem vc_682 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 682 n g V) : W_682 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, ⟨⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, k, hk, hr⟩ := h
  try dsimp only at hn m1 m2 m3 b1 b2 b3 b4 b5 hrd hr
  subst hn
  have h3 := ixc r11 3 (by decide) (by omega)
  have h4 := ixc r11 4 (by decide) (by omega)
  have w4 := st1 m4 (Or.inl b1) 1#8
  wpx [W_682, W_696, W_705, W_929, W_940, W_945, W_954, W_964, W_1024, o16, o17, o18, o34, o35, o32, o37, o38, o40,
    Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  refine ⟨tabB hT _ 1 (by rw [h3]; omega) (by rw [h3]; omega),
    fun _ => ⟨fun _ => ⟨tabB hT _ 4 (by rw [h4]; omega) (by rw [h4]; omega),
        Or.inl ⟨1, by icw_om, rfl, m1, m2, m3, m4⟩⟩,
      fun h => absurd h (by rcases hrd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)⟩,
    fun _ => ⟨fun _ => Or.inl ⟨_, by icw_om, rfl, ⟨m1, m2, m3, m4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩, fun _ => ?_⟩⟩
  intro fl hz
  have hz' : fl.zf = (BitVec.setWidth 32 rsi >>> 8 == 0) := by first | exact hz (by decide) | exact hz
  exact ⟨fun i hi => by rw [b1]; exact hT.p2 i hi,
    fun h0 => Or.inl ⟨_, m_shr _ hz' (nt h0) 900 5 (by decide), rfl, ⟨m1, m2, m3, w4⟩, ⟨b1, b2, b3, b4, b5⟩, hrd⟩,
    fun _ => Or.inl ⟨2, by icw_om, rfl, m1, m2, m3, w4⟩⟩

theorem vc_717 (h : Ih g₀ V₀ 717 n g V) : W_717 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, m1, m2, m3, m4⟩ := h
  try dsimp only at hn m1 m2 m3
  subst hn
  wpx [W_717, o19, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  intro _
  exact Or.inl ⟨1, by decide, rfl, m1, m2, m3, m4⟩

theorem vc_719 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 719 n g V) : W_719 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hn, m1, m2, m3, m4⟩ := h
  try dsimp only at hn m1 m2 m3
  subst hn
  obtain ⟨l1, l2, l3, l4, -⟩ := ld5 hT.ld
  obtain ⟨p1, p2, p3, p4⟩ := pops hT m4
  wpx [W_719, o20, Op.zxr, Op.sxr, Op.imul3, Op.shr64, Op.cmpmi, Op.setcc, Op.shr32z]
  subst m1
  simp only [BitVec.sub_add_cancel]
  exact ⟨l1, l2, l3, l4, Or.inr ⟨Or.inl rfl, rfl, p1, p2, p3, p4, m2, m3, keep_of hT m4⟩⟩

end FV7z.Icw
