import FV7z.Stl.Vc1
/-!
# `____strtoul_l_internal`: the digit loop at a byte neither a digit nor a letter (PLAN.md §M, M1)

`vc_296x`: at 296, a byte that is not a digit (`cl - '0' > 9`) and whose `CB` entry has no letter bit goes to 368.
The two tests are hypotheses in the form the `wp` prints them (`Stl/notes/Wp.lean`, cut 296), so that they rewrite
the goal as they stand; the loop (`Stl/Loop.lean`) proves them for the NUL from `CB[0]`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace FV7z.Stl
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- Neither a digit nor a letter: to 368. -/
theorem vc_296x {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = 0#64)
    (hd : (decide ((BitVec.setWidth 8 (BitVec.setWidth 32 (g.rcx + 18446744073709551568#64))).toNat < 9) ||
      decide (BitVec.setWidth 8 (BitVec.setWidth 32 (g.rcx + 18446744073709551568#64)) = 9#8)) = false)
    (fC : ∀ i < 1, Foot F.data
      (Addr.add (g.r11 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rcx)) * 2#64 + 1#64) i))
    (ha : (rb V (g.r11 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rcx)) * 2#64 + 1#64) &&& 4#8
      == 0) = true) :
    W_296 fb F Wl (fun j g' _ V' => j = 368 ∧ V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg, rb] at hbp hd fC ha ⊢
  stlx +contextual [W_296, W_305, W_314, W_317, W_325, o20, o21, o22, o23, o24, hbp, hd, fC, ha]

end FV7z.Stl
