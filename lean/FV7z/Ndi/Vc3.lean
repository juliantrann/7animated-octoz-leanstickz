import FV7z.Ndi.Mem
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

variable {F : Footprint} {Wl : List Rgn}

theorem vc_2281 {g : Gprs} {f : Rflags} {V : Addr → Byte} {p : BitVec 64}
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (h0 : g.rax = 0#64) (hp : rdq(V, 8029512#64) = p) :
    W_2281 F Wl (fun j' g' _ V' => (p = 0#64 → j' = 2575) ∧ (p ≠ 0#64 → j' = 2563) ∧
      g' = { g with rbp := 0#64, rdi := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2281, W_2551, o18, o19, Op.test, Op.mov, Op.lda]
  simp only [hp, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne]
  exact ⟨fun _ => ⟨gf hr _ 8 (by decide), fun h => ⟨fun _ => trivial, fun hne => absurd h hne, trivial⟩,
    fun h => ⟨fun h0 => absurd h0 h, fun _ => trivial, trivial⟩⟩, fun h => absurd h (by decide)⟩

theorem vc_2575 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (h1 : rdq(V, 8029568#64) = 4194368#64) (h2 : rdq(V, 8029592#64) = 8#64) :
    W_2575 F Wl (fun j' g' _ V' => j' = 2687 ∧
      g' = { g with rax := 4194368#64, rcx := 4194816#64, rdx := 56#64, r10 := rdq(V, 7944528#64),
                    r11 := rdq(V, 7944520#64), rdi := rdq(V, 7944528#64), r8 := 0#64, rsi := 0#64,
                    r9 := (rdd(V, 7943112#64)).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2575, W_2598, W_2625, o21, o22, o23, Op.test, Op.mov, Op.lda, Op.lea, Op.sub, Op.cmp, Op.xor]
  simp only [h1, h2, BitVec.xor_self]
  exact ⟨gf hr _ 8 (by decide), gf hr _ 8 (by decide), fun h => absurd h (by decide), fun _ =>
    ⟨gf hr _ 8 (by decide), fun h => absurd h (by decide), fun _ =>
      ⟨gf hr _ 8 (by decide), gf hr _ 4 (by decide), rfl⟩⟩⟩

/-- The second store into `_dl_profile_output` (`0x7a85a0`) and the test of `_dl_platform` (`0x7a8548`), after a
`getenv` that returned 0: not secure, so the directory is the string at `0x6f369c`; the platform string, when there
is one, is not empty. -/
theorem vc_2194 {g : Gprs} {f : Rflags} {V : Addr → Byte} {p : BitVec 64}
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x)
    (h0 : g.rax = 0#64) (h5 : rdd(V, 7937248#64) = 0#32) (hp : rdq(V, 8029512#64) = p)
    (hpl : p = 0#64 ∨ Foot F.data p ∧ (p.toNat + 1 ≤ 8029600 ∨ 8029608 ≤ p.toNat) ∧ rdb(V, p) ≠ 0#8) :
    W_2194 F Wl (fun j' g' _ V' => j' = 2269 ∧ g' = { g with rax := p, rdx := 7288540#64 } ∧
      V' = Vst (Vst V 8029600#64 (toBytesLE (0#64) 8)) 8029600#64 (toBytesLE (7288540#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2194, W_2211, W_2241, W_2253, o13, o14, o15, o16, Op.test, Op.mov, Op.lda, Op.sta, Op.lea, Op.cmov64,
    Op.cmpmi]
  have z32 : (0#32 == (0 : BitVec 32)) = true := by decide
  simp (disch := decide) only [rq, h5, hp, BitVec.and_self, BitVec.reduceAdd, z32, ↓reduceIte]
  wpx [W_2194]
  refine ⟨gf hw _ 8 (by decide), fun _ => ⟨gf hr _ 4 (by decide), gf hw _ 8 (by decide), gf hr _ 8 (by decide),
    ?_, ?_⟩, fun h => absurd h (by decide)⟩
  · exact fun _ => trivial
  · intro hne
    rcases hpl with rfl | ⟨hf, hd, hb⟩
    · exact absurd hne (by decide)
    · have hx : p.toNat + 1 ≤ 2 ^ 64 := by have := p.isLt; omega
      have hd' : (8029600#64).toNat + 8 ≤ p.toNat ∨ p.toNat + 1 ≤ (8029600#64).toNat := by
        rw [show (8029600#64).toNat = 8029600 from rfl]; omega
      have e : ∀ (W : Addr → Byte) (v : BitVec 64), List.map (Vst W 8029600#64 (toBytesLE v 8)) (byteAddrs p 1) =
          List.map W (byteAddrs p 1) := fun W v => rq ⟨by decide, hx, hd'⟩
      simp only [e]
      refine ⟨fun i hi => ?_, fun _ => trivial, fun h => ?_⟩
      · obtain rfl : i = 0 := by omega
        rw [addr_add_zero]; exact hf
      · simp only [hb, decide_false, Bool.not_false] at h
        exact absurd h (by decide)

end FV7z.Ndi
