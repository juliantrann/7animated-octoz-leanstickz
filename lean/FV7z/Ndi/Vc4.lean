import FV7z.Ndi.Mem
/-!
# `_dl_non_dynamic_init`: the conditions of the loop over the program headers and of the end (PLAN.md G3, startup)

The loop (cut points 2687, 2678) reads `p_type` of the header at `rax`, up to the end `rcx`: `PT_GNU_STACK`
(`0x6474e551`) gives `p_flags` in `r9d` and sets `esi`; `PT_GNU_RELRO` (`0x6474e552`) gives `p_vaddr` in `r11`,
`p_memsz` in `rdi` and sets `r8d`. After it the function stores what it found (2715, 2727) and, with a RELRO segment,
calls `_dl_protect_relro` (2749); 2884 is the epilogue.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

variable {F : Footprint} {Wl : List Rgn}

/-- A header that is neither `PT_GNU_STACK` nor `PT_GNU_RELRO`. -/
theorem vc_2687_o {g : Gprs} {f : Rflags} {V : Addr → Byte} {ty : BitVec 32}
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i))
    (ht : rdd(V, g.rax) = ty) (h1 : ty ≠ 1685382481#32) (h2 : ty ≠ 1685382482#32) :
    W_2687 F Wl (fun j' g' _ V' => j' = 2678 ∧ g' = { g with rdx := ty.setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf ht
  wpx [W_2687, W_2656, W_2664, W_2697, o27, o24, o25, o28, Op.ld, Op.cmp, Op.mov, Op.add]
  simp only [ht, h1, h2, decide_false, Bool.not_false]
  exact ⟨hf, fun _ => ⟨fun _ => trivial, fun h => absurd h (by decide)⟩, fun h => absurd h (by decide)⟩

/-- The `PT_GNU_RELRO` header. -/
theorem vc_2687_r {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i))
    (hf16 : ∀ i < 8, Foot F.data (Addr.add (g.rax + 16#64) i))
    (hf40 : ∀ i < 8, Foot F.data (Addr.add (g.rax + 40#64) i))
    (ht : rdd(V, g.rax) = 1685382482#32) :
    W_2687 F Wl (fun j' g' _ V' => j' = 2678 ∧
      g' = { g with rdx := 1685382482#64, rdi := rdq(V, g.rax + 40#64), r8 := 1#64, r11 := rdq(V, g.rax + 16#64) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hf16 hf40 ht
  wpx [W_2687, W_2656, W_2664, W_2697, o27, o24, o25, o28, Op.ld, Op.cmp, Op.mov, Op.add]
  simp only [ht]
  exact ⟨hf, fun _ => ⟨fun h => absurd h (by decide), fun _ => ⟨hf16, hf40, rfl⟩⟩, fun h => absurd h (by decide)⟩

/-- The `PT_GNU_STACK` header. -/
theorem vc_2687_s {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) (hf4 : ∀ i < 4, Foot F.data (Addr.add (g.rax + 4#64) i))
    (ht : rdd(V, g.rax) = 1685382481#32) :
    W_2687 F Wl (fun j' g' _ V' => ((g.rax + 56#64).toNat < g.rcx.toNat → j' = 2687) ∧
      (¬ (g.rax + 56#64).toNat < g.rcx.toNat → j' = 2715) ∧
      g' = { g with rax := g.rax + 56#64, rdx := 1685382481#64, rsi := 1#64,
                    r9 := (rdd(V, g.rax + 4#64)).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hf4 ht ⊢
  wpx [W_2687, W_2656, W_2664, W_2697, o27, o24, o25, o28, Op.ld, Op.cmp, Op.mov, Op.add]
  simp only [ht]
  refine ⟨hf, fun h => absurd h (by decide), fun _ => ⟨hf4, ?_⟩⟩
  exact ⟨fun h => ⟨fun _ => trivial, fun hn => absurd (of_decide_eq_true h) hn, rfl⟩,
    fun h => ⟨fun hp => absurd hp (of_decide_eq_false h), fun _ => trivial, rfl⟩⟩

/-- The next header, or the end of the table. -/
theorem vc_2678 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_2678 F Wl (fun j' g' _ V' => ((g.rax + 56#64).toNat < g.rcx.toNat → j' = 2687) ∧
      (¬ (g.rax + 56#64).toNat < g.rcx.toNat → j' = 2715) ∧ g' = { g with rax := g.rax + 56#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only
  wpx [W_2678, o26, Op.cmp, Op.add]
  exact ⟨fun h => ⟨fun hp => absurd hp (by simpa using h), fun _ => trivial⟩,
    fun h => ⟨fun _ => trivial, fun hn => absurd (by simpa using h) hn⟩⟩

/-- With a `PT_GNU_STACK` header: `_dl_stack_flags := p_flags` (`0x793408`). -/
theorem vc_2715 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (hs : g.rsi = 1#64) :
    W_2715 F Wl (fun j' g' _ V' => j' = 2727 ∧ g' = g ∧
      V' = Vst V 7943112#64 (toBytesLE (g.r9.setWidth 32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst hs
  wpx [W_2715, W_2720, o29, o30, Op.test, Op.sta]
  exact ⟨fun h => absurd h (by decide), fun _ => gf hw _ 4 (by decide)⟩

/-- With a `PT_GNU_RELRO` header: `l_relro_addr`, `l_relro_size` of the main map (`0x793988`, `0x793990`). -/
theorem vc_2727 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (h8 : g.r8 = 1#64) :
    W_2727 F Wl (fun j' g' _ V' => j' = 2749 ∧ g' = { g with r10 := g.rdi } ∧
      V' = Vst (Vst V 7944520#64 (toBytesLE g.r11 8)) 7944528#64 (toBytesLE g.rdi 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h8
  wpx [W_2727, W_2732, o31, o32, Op.test, Op.sta, Op.mov]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨gf hw _ 8 (by decide), gf hw _ 8 (by decide)⟩⟩

/-- A RELRO segment of a size other than 0: the argument of `_dl_protect_relro` (the main map, `0x793520`). -/
theorem vc_2749 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hn : g.r10 ≠ 0#64) :
    W_2749 F Wl (fun j' g' _ V' => j' = 2879 ∧ g' = { g with rdi := 7943392#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn
  have hb : (r10 &&& r10 == 0) = false := by rw [BitVec.and_self]; exact beq_false_of_ne hn
  wpx [W_2749, W_2872, W_2754, o33, o41, o34, Op.test, Op.mov, Op.add, Op.pop]
  simp only [hb, Bool.not_false]
  exact ⟨fun _ => trivial, fun h => absurd h (by decide)⟩

/-- The epilogue: to the `ret`. -/
theorem vc_2884 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 40, Foot F.data (Addr.add (g.rsp + 80#64) i)) :
    W_2884 F Wl (fun j' g' _ V' => j' = 2896 ∧
      g' = { g with rbx := rdq(V, g.rsp + 80#64), rbp := rdq(V, g.rsp + 88#64), r12 := rdq(V, g.rsp + 96#64),
                    r13 := rdq(V, g.rsp + 104#64), r14 := rdq(V, g.rsp + 112#64), rsp := g.rsp + 120#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  have w : ∀ (k : Nat) (b : BitVec 64), k + 8 ≤ 40 → rsp + 80#64 + BitVec.ofNat 64 k = b →
      ∀ i < 8, Foot F.data (Addr.add b i) := fun k b hk hb i hi => by
    have := hl (k + i) (by omega)
    rwa [show Addr.add (rsp + 80#64) (k + i) = Addr.add b i by subst hb; simp only [Addr.add]; bv_omega] at this
  have e1 : rsp + 80#64 + 8 = rsp + 88#64 := by bv_omega
  have e2 : rsp + 88#64 + 8 = rsp + 96#64 := by bv_omega
  have e3 : rsp + 96#64 + 8 = rsp + 104#64 := by bv_omega
  have e4 : rsp + 104#64 + 8 = rsp + 112#64 := by bv_omega
  have e5 : rsp + 112#64 + 8 = rsp + 120#64 := by bv_omega
  wpx [W_2884, o34, Op.add, Op.pop]
  rw [e1, e2, e3, e4, e5]
  exact ⟨w 0 _ (by omega) (by bv_omega), w 8 _ (by omega) (by bv_omega), w 16 _ (by omega) (by bv_omega),
    w 24 _ (by omega) (by bv_omega), w 32 _ (by omega) (by bv_omega), rfl⟩

end FV7z.Ndi
