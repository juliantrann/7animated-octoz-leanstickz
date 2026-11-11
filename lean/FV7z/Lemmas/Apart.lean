import ZellicX86.Spec.Statement
/-!
# Regions apart, in numbers

What `Disjoint` of two regions with a byte each says of their bounds: the form in which a precondition's apartness
(a stack frame from the buffers) reaches the arithmetic of a proof.
-/
namespace FV7z
open ZellicX86

/-- Two regions with a byte each, apart: one ends where the other begins, or before. -/
theorem ends_of_disjoint {r q : Rgn} (h : Disjoint r q) (hr : 0 < r.len) (hq : 0 < q.len) :
    r.base.toNat + r.len ≤ q.base.toNat ∨ q.base.toNat + q.len ≤ r.base.toNat := by
  by_cases h1 : r.base.toNat ≤ q.base.toNat
  · have := h q.base
    simp only [Rgn.Mem] at this
    omega
  · have := h r.base
    simp only [Rgn.Mem] at this
    omega

end FV7z
