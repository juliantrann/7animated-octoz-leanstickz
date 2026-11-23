import FV7z.Lif.Holds
import FV7z.Start.Code
/-!
# The call of `__libc_init_first` (PLAN.md G3, startup)

`Start.launch_to_ptr` ends at `0x613434` in `__libc_start_main` (`lsm` 1012), the `call` of `__libc_init_first`;
`Ndi.lif_ok` starts at the entry of `__libc_init_first` (`0x672160`). `ptr_call` is the step between them: the
return address `0x613439` (`lsm` 1017) is stored below `rsp`, and `rsp` goes down by 8.

- `ent_rd`: 8 bytes below `0x793ac0` or from `0x7a85d8` up, and apart from the 40 stack bytes the `call` and
  `lif_a` store, are in the bytes at the call of `_dl_non_dynamic_init` (`lif_ok`'s `W`) those at `0x613434`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Start (lsm lsm_at lsm_length)
open FV7z.Tun (rd_Vst)
namespace FV7z.Lif

/-- The `call` of `__libc_init_first` in `__libc_start_main`. -/
def pc1012 : List Byte := [0xe8, 0x27, 0xed, 0x05, 0x00]
theorem pc1012_0 : ∀ feat, Dec feat pc1012 0 (FV7z.mk .call 64 [.rel 388391] 5) := by dec_rfl
theorem wc1012 : pc1012 <+: lsm.drop 1012 := by decide +kernel
theorem call_1012 (feat : Features) : Dec feat lsm 1012 (FV7z.mk .call 64 [.rel 388391] 5) :=
  Dec.shift (j := 1012) (k := 0) (pc1012_0 feat) wc1012 (Nat.zero_le _)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From the `call` at `0x613434` to the entry of `__libc_init_first`: the bytes get the return address `0x613439`
below `rsp`, and `rsp` goes down by 8. -/
theorem ptr_call (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L lsm_at lsm) (hrip : X.cpu.rip = lsm_at.add 1012) (hinL : CodeIn L lif_at lif)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lsm_at.add 1017) 8)) →
      Y.cpu.rip = lif_at → Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine c.s_call hK hA hin (by rw [lsm_length]; decide) hrip (call_1012 _) hinL (by rw [lif_length]; decide)
    (by decide) hst ?_
  rintro Y t' hKY hAY ⟨hr, hg⟩
  exact k Y t' hKY hAY hr hg

/-- 8 bytes apart from the variables `lif_a` stores and from the stack bytes stored since `0x613434` (the return
address of the `call`, three `push`es, the return address of the next `call`) are as at `0x613434`; `g` is the
registers at the entry of `__libc_init_first`. -/
theorem ent_rd {V : Addr → Byte} {g : Gprs} {y : Addr} {ra ra₀ : BitVec 64} (hr : 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hy : y.toNat + 8 ≤ 7944640 ∨ 8029656 ≤ y.toNat)
    (hy' : y.toNat + 8 ≤ 2 ^ 64)
    (hs : y.toNat + 8 ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat + 8 ≤ y.toNat) :
    rdq(Vst (LifMem (Vst V g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8), y) = rdq(V, y) := by
  unfold LifMem LifStk
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

end FV7z.Lif
