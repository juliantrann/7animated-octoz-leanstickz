import FV7z.U16.Adr
import FV7z.U8c.Holds
/-! # `Utf8_To_Utf16`: the memory after the `push`es and the `destLen` and `flags & 4` stores (PLAN.md §M, M1) -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

/-! ## The stack -/

/-- The memory after the six `push`es and `mov [rsp-8], rsi`. -/
def Vs0 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (S6 g.rsp) (toBytesLE g.rbx 8))
    (S6 g.rsp + 18446744073709551608#64) (toBytesLE g.rsi 8)

/-- And `mov [rsp-0xc], r8d` with `flags & 4`. -/
def Vs1 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vs0 g V) (S6 g.rsp + 18446744073709551604#64) (toBytesLE (BitVec.setWidth 32 g.r8 &&& 4#32) 4)

/-- Past one store in a load, the bounds by `tsl`; a failing bound stops a `repeat`. -/
macro "skv" : tactic => `(tactic| focus (rw [rd_Vst _ _ _ _ _ ?_ ?_ ?_]; rotate_left; iterate 3 tsl))
/-- Past one store at a byte. -/
macro "sko" : tactic => `(tactic| focus (rw [Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 tsl))

section stk
variable {g : Gprs} {V : Addr → Byte} (hs : 64 ≤ g.rsp.toNat)
include hs

/-- The memory in the forms `s - c`. -/
theorem vs0_eq : Vs0 g V =
    Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - BitVec.ofNat 64 8) (toBytesLE g.r15 8))
      (g.rsp - BitVec.ofNat 64 16) (toBytesLE g.r14 8)) (g.rsp - BitVec.ofNat 64 24) (toBytesLE g.r13 8))
      (g.rsp - BitVec.ofNat 64 32) (toBytesLE g.r12 8)) (g.rsp - BitVec.ofNat 64 40) (toBytesLE g.rbp 8))
      (g.rsp - BitVec.ofNat 64 48) (toBytesLE g.rbx 8)) (g.rsp - BitVec.ofNat 64 56) (toBytesLE g.rsi 8) := by
  rw [Vs0, k56, k48, k40, k32, k24, k16, k8]

/-- The bytes outside the 60 below the stack pointer. -/
theorem vs0_out {x : Addr} (hx : x.toNat + 60 < g.rsp.toNat ∨ g.rsp.toNat ≤ x.toNat) : Vs0 g V x = V x := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [vs0_eq hs]
  repeat sko

theorem vs1_out {x : Addr} (hx : x.toNat + 60 < g.rsp.toNat ∨ g.rsp.toNat ≤ x.toNat) : Vs1 g V x = V x := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60]
  sko
  exact vs0_out hs hx

/-- What the six `push`es and the `destLen` store left. -/
theorem vs0_rd : rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 8) = g.r15 ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 16) = g.r14 ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 24) = g.r13 ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 32) = g.r12 ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 40) = g.rbp ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 48) = g.rbx ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 56) = g.rsi := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [vs0_eq hs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · repeat skv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by tsl)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- The `flags & 4` store is apart from the 56 bytes. -/
theorem vs1_rd {c : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 24 ∨ c = 32 ∨ c = 40 ∨ c = 48 ∨ c = 56) :
    rdq(Vs1 g V, g.rsp - BitVec.ofNat 64 c) = rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 c) := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60]
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> skv

/-- `flags & 4`, read back. -/
theorem vs1_fl : rdd(Vs1 g V, S6 g.rsp + 18446744073709551604#64) = BitVec.setWidth 32 g.r8 &&& 4#32 := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by tsl)]
  exact ofBytesLE_toBytesLE (w := 32) (n := 4) rfl _

end stk

end FV7z.U16
