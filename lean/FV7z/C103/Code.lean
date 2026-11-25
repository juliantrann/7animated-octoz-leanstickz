import FV7z.C103.Cuts
import FV7z.Lemmas.SpDiv
import FV7z.Hin.Holds
/-!
# `init_cacheinfo`: the instructions the pieces stop at (PLAN.md M, ctor 103)

The three calls of `handle_intel` (3758, 3771, 3784) and of `handle_amd` (4040, 4053, 4066), the six `cpuid`s, the
four `idiv`s (3707, 3981, 4005, 4223), the three `bsr`s (4380, 4454, 4594) and the `ret` at 3731, decoded.
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
open FV7z.Hca (hca hca_at pcp pcp_0 prt prt_0)
set_option maxRecDepth 100000

def pdc : List Byte := [0x48, 0xf7, 0xf9]
def pdi : List Byte := [0x48, 0xf7, 0xff]
def pd9 : List Byte := [0x49, 0xf7, 0xf9]
def pb9 : List Byte := [0x41, 0x0f, 0xbd, 0xc9]
def pbi : List Byte := [0x0f, 0xbd, 0xcf]
theorem pdc_0 : ∀ feat, Dec feat pdc 0 (FV7z.mk .idiv 64 [gr 64 1] 3) := by dec_rfl
theorem pdi_0 : ∀ feat, Dec feat pdi 0 (FV7z.mk .idiv 64 [gr 64 7] 3) := by dec_rfl
theorem pd9_0 : ∀ feat, Dec feat pd9 0 (FV7z.mk .idiv 64 [gr 64 9] 3) := by dec_rfl
theorem pb9_0 : ∀ feat, Dec feat pb9 0 (FV7z.mk (.bit .bsr) 32 [gr 32 1, gr 32 9] 4) := by dec_rfl
theorem pbi_0 : ∀ feat, Dec feat pbi 0 (FV7z.mk (.bit .bsr) 32 [gr 32 1, gr 32 7] 3) := by dec_rfl

def ph1 : List Byte := [0xe8, 0x1d, 0x00, 0x24, 0x00]
def ph2 : List Byte := [0xe8, 0x10, 0x00, 0x24, 0x00]
def ph3 : List Byte := [0xe8, 0x03, 0x00, 0x24, 0x00]
def pa1 : List Byte := [0xe8, 0x03, 0xfa, 0x23, 0x00]
def pa2 : List Byte := [0xe8, 0xf6, 0xf9, 0x23, 0x00]
def pa3 : List Byte := [0xe8, 0xe9, 0xf9, 0x23, 0x00]
theorem ph1_0 : ∀ feat, Dec feat ph1 0 (FV7z.mk .call 64 [.rel 2359325] 5) := by dec_rfl
theorem ph2_0 : ∀ feat, Dec feat ph2 0 (FV7z.mk .call 64 [.rel 2359312] 5) := by dec_rfl
theorem ph3_0 : ∀ feat, Dec feat ph3 0 (FV7z.mk .call 64 [.rel 2359299] 5) := by dec_rfl
theorem pa1_0 : ∀ feat, Dec feat pa1 0 (FV7z.mk .call 64 [.rel 2357763] 5) := by dec_rfl
theorem pa2_0 : ∀ feat, Dec feat pa2 0 (FV7z.mk .call 64 [.rel 2357750] 5) := by dec_rfl
theorem pa3_0 : ∀ feat, Dec feat pa3 0 (FV7z.mk .call 64 [.rel 2357737] 5) := by dec_rfl

theorem w3707 : pdc <+: sti.drop 3707 := by decide +kernel
theorem w3981 : pdi <+: sti.drop 3981 := by decide +kernel
theorem w4005 : pd9 <+: sti.drop 4005 := by decide +kernel
theorem w4223 : pdc <+: sti.drop 4223 := by decide +kernel
theorem w4380 : pb9 <+: sti.drop 4380 := by decide +kernel
theorem w4454 : pbi <+: sti.drop 4454 := by decide +kernel
theorem w4594 : pb9 <+: sti.drop 4594 := by decide +kernel
theorem w3758 : ph1 <+: sti.drop 3758 := by decide +kernel
theorem w3771 : ph2 <+: sti.drop 3771 := by decide +kernel
theorem w3784 : ph3 <+: sti.drop 3784 := by decide +kernel
theorem w4040 : pa1 <+: sti.drop 4040 := by decide +kernel
theorem w4053 : pa2 <+: sti.drop 4053 := by decide +kernel
theorem w4066 : pa3 <+: sti.drop 4066 := by decide +kernel
theorem w3865 : pcp <+: sti.drop 3865 := by decide +kernel
theorem w4079 : pcp <+: sti.drop 4079 := by decide +kernel
theorem w4100 : pcp <+: sti.drop 4100 := by decide +kernel
theorem w4141 : pcp <+: sti.drop 4141 := by decide +kernel
theorem w4197 : pcp <+: sti.drop 4197 := by decide +kernel
theorem w4346 : pcp <+: sti.drop 4346 := by decide +kernel
theorem w3731 : prt <+: sti.drop 3731 := by decide +kernel

theorem dv3707 (feat : Features) : Dec feat sti 3707 (FV7z.mk .idiv 64 [gr 64 1] 3) :=
  Dec.shift (j := 3707) (k := 0) (pdc_0 feat) w3707 (Nat.zero_le _)
theorem dv3981 (feat : Features) : Dec feat sti 3981 (FV7z.mk .idiv 64 [gr 64 7] 3) :=
  Dec.shift (j := 3981) (k := 0) (pdi_0 feat) w3981 (Nat.zero_le _)
theorem dv4005 (feat : Features) : Dec feat sti 4005 (FV7z.mk .idiv 64 [gr 64 9] 3) :=
  Dec.shift (j := 4005) (k := 0) (pd9_0 feat) w4005 (Nat.zero_le _)
theorem dv4223 (feat : Features) : Dec feat sti 4223 (FV7z.mk .idiv 64 [gr 64 1] 3) :=
  Dec.shift (j := 4223) (k := 0) (pdc_0 feat) w4223 (Nat.zero_le _)
theorem bs4380 (feat : Features) : Dec feat sti 4380 (FV7z.mk (.bit .bsr) 32 [gr 32 1, gr 32 9] 4) :=
  Dec.shift (j := 4380) (k := 0) (pb9_0 feat) w4380 (Nat.zero_le _)
theorem bs4454 (feat : Features) : Dec feat sti 4454 (FV7z.mk (.bit .bsr) 32 [gr 32 1, gr 32 7] 3) :=
  Dec.shift (j := 4454) (k := 0) (pbi_0 feat) w4454 (Nat.zero_le _)
theorem bs4594 (feat : Features) : Dec feat sti 4594 (FV7z.mk (.bit .bsr) 32 [gr 32 1, gr 32 9] 4) :=
  Dec.shift (j := 4594) (k := 0) (pb9_0 feat) w4594 (Nat.zero_le _)
theorem cl3758 (feat : Features) : Dec feat sti 3758 (FV7z.mk .call 64 [.rel 2359325] 5) :=
  Dec.shift (j := 3758) (k := 0) (ph1_0 feat) w3758 (Nat.zero_le _)
theorem cl3771 (feat : Features) : Dec feat sti 3771 (FV7z.mk .call 64 [.rel 2359312] 5) :=
  Dec.shift (j := 3771) (k := 0) (ph2_0 feat) w3771 (Nat.zero_le _)
theorem cl3784 (feat : Features) : Dec feat sti 3784 (FV7z.mk .call 64 [.rel 2359299] 5) :=
  Dec.shift (j := 3784) (k := 0) (ph3_0 feat) w3784 (Nat.zero_le _)
theorem cl4040 (feat : Features) : Dec feat sti 4040 (FV7z.mk .call 64 [.rel 2357763] 5) :=
  Dec.shift (j := 4040) (k := 0) (pa1_0 feat) w4040 (Nat.zero_le _)
theorem cl4053 (feat : Features) : Dec feat sti 4053 (FV7z.mk .call 64 [.rel 2357750] 5) :=
  Dec.shift (j := 4053) (k := 0) (pa2_0 feat) w4053 (Nat.zero_le _)
theorem cl4066 (feat : Features) : Dec feat sti 4066 (FV7z.mk .call 64 [.rel 2357737] 5) :=
  Dec.shift (j := 4066) (k := 0) (pa3_0 feat) w4066 (Nat.zero_le _)
theorem cp3865 (feat : Features) : Dec feat sti 3865 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 3865) (k := 0) (pcp_0 feat) w3865 (Nat.zero_le _)
theorem cp4079 (feat : Features) : Dec feat sti 4079 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 4079) (k := 0) (pcp_0 feat) w4079 (Nat.zero_le _)
theorem cp4100 (feat : Features) : Dec feat sti 4100 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 4100) (k := 0) (pcp_0 feat) w4100 (Nat.zero_le _)
theorem cp4141 (feat : Features) : Dec feat sti 4141 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 4141) (k := 0) (pcp_0 feat) w4141 (Nat.zero_le _)
theorem cp4197 (feat : Features) : Dec feat sti 4197 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 4197) (k := 0) (pcp_0 feat) w4197 (Nat.zero_le _)
theorem cp4346 (feat : Features) : Dec feat sti 4346 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 4346) (k := 0) (pcp_0 feat) w4346 (Nat.zero_le _)
theorem rt3731 (feat : Features) : Dec feat sti 3731 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 3731) (k := 0) (prt_0 feat) w3731 (Nat.zero_le _)

/-- The calls' targets: `handle_intel` at `hca`'s 1280th byte, `handle_amd` at its start. -/
theorem tg3758 : Addr.add sti_at (3758 + 5) + BitVec.ofNat 64 2359325 = Addr.add hca_at 1280 := by decide
theorem tg3771 : Addr.add sti_at (3771 + 5) + BitVec.ofNat 64 2359312 = Addr.add hca_at 1280 := by decide
theorem tg3784 : Addr.add sti_at (3784 + 5) + BitVec.ofNat 64 2359299 = Addr.add hca_at 1280 := by decide
theorem tg4040 : Addr.add sti_at (4040 + 5) + BitVec.ofNat 64 2357763 = Addr.add hca_at 0 := by decide
theorem tg4053 : Addr.add sti_at (4053 + 5) + BitVec.ofNat 64 2357750 = Addr.add hca_at 0 := by decide
theorem tg4066 : Addr.add sti_at (4066 + 5) + BitVec.ofNat 64 2357737 = Addr.add hca_at 0 := by decide
theorem hca_at0 : Addr.add hca_at 0 = hca_at := by decide

end FV7z.C103
