import FV7z.Ndi.Cuts
import FV7z.Lemmas.FnFar
/-!
# `_dl_non_dynamic_init`: its `call`s and its `ret` (PLAN.md G3, startup)

The eleven `call`s the way without a vDSO goes through (`call_16` … `call_2879`: `_dl_get_origin`, `getenv` seven
times, `_dl_init_paths`, `strlen`, `_dl_protect_relro`) and the `ret` after `_dl_protect_relro` (`ret_2896`), decoded
at their offsets.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ndi

/-- The `call` of `_dl_get_origin`. -/
def pc16 : List Byte := [0xe8, 0x5b, 0xf7, 0x03, 0x00]
theorem pc16_0 : ∀ feat, Dec feat pc16 0 (FV7z.mk .call 64 [.rel 259931] 5) := by dec_rfl
theorem wc16 : pc16 <+: ndi.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat ndi 16 (FV7z.mk .call 64 [.rel 259931] 5) :=
  Dec.shift (j := 16) (k := 0) (pc16_0 feat) wc16 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_WARN")`. -/
def pc2018 : List Byte := [0xe8, 0x59, 0x30, 0xfb, 0xff]
theorem pc2018_0 : ∀ feat, Dec feat pc2018 0 (FV7z.mk .call 64 [.rel 18446744073709236313] 5) := by dec_rfl
theorem wc2018 : pc2018 <+: ndi.drop 2018 := by decide +kernel
theorem call_2018 (feat : Features) : Dec feat ndi 2018 (FV7z.mk .call 64 [.rel 18446744073709236313] 5) :=
  Dec.shift (j := 2018) (k := 0) (pc2018_0 feat) wc2018 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_LIBRARY_PATH")`. -/
def pc2050 : List Byte := [0xe8, 0x39, 0x30, 0xfb, 0xff]
theorem pc2050_0 : ∀ feat, Dec feat pc2050 0 (FV7z.mk .call 64 [.rel 18446744073709236281] 5) := by dec_rfl
theorem wc2050 : pc2050 <+: ndi.drop 2050 := by decide +kernel
theorem call_2050 (feat : Features) : Dec feat ndi 2050 (FV7z.mk .call 64 [.rel 18446744073709236281] 5) :=
  Dec.shift (j := 2050) (k := 0) (pc2050_0 feat) wc2050 (Nat.zero_le _)

/-- The `call` of `_dl_init_paths`. -/
def pc2058 : List Byte := [0xe8, 0xb1, 0x88, 0x03, 0x00]
theorem pc2058_0 : ∀ feat, Dec feat pc2058 0 (FV7z.mk .call 64 [.rel 231601] 5) := by dec_rfl
theorem wc2058 : pc2058 <+: ndi.drop 2058 := by decide +kernel
theorem call_2058 (feat : Features) : Dec feat ndi 2058 (FV7z.mk .call 64 [.rel 231601] 5) :=
  Dec.shift (j := 2058) (k := 0) (pc2058_0 feat) wc2058 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_BIND_NOW")`. -/
def pc2084 : List Byte := [0xe8, 0x17, 0x30, 0xfb, 0xff]
theorem pc2084_0 : ∀ feat, Dec feat pc2084 0 (FV7z.mk .call 64 [.rel 18446744073709236247] 5) := by dec_rfl
theorem wc2084 : pc2084 <+: ndi.drop 2084 := by decide +kernel
theorem call_2084 (feat : Features) : Dec feat ndi 2084 (FV7z.mk .call 64 [.rel 18446744073709236247] 5) :=
  Dec.shift (j := 2084) (k := 0) (pc2084_0 feat) wc2084 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_BIND_NOT")`. -/
def pc2120 : List Byte := [0xe8, 0xf3, 0x2f, 0xfb, 0xff]
theorem pc2120_0 : ∀ feat, Dec feat pc2120 0 (FV7z.mk .call 64 [.rel 18446744073709236211] 5) := by dec_rfl
theorem wc2120 : pc2120 <+: ndi.drop 2120 := by decide +kernel
theorem call_2120 (feat : Features) : Dec feat ndi 2120 (FV7z.mk .call 64 [.rel 18446744073709236211] 5) :=
  Dec.shift (j := 2120) (k := 0) (pc2120_0 feat) wc2120 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_DYNAMIC_WEAK")`. -/
def pc2153 : List Byte := [0xe8, 0xd2, 0x2f, 0xfb, 0xff]
theorem pc2153_0 : ∀ feat, Dec feat pc2153 0 (FV7z.mk .call 64 [.rel 18446744073709236178] 5) := by dec_rfl
theorem wc2153 : pc2153 <+: ndi.drop 2153 := by decide +kernel
theorem call_2153 (feat : Features) : Dec feat ndi 2153 (FV7z.mk .call 64 [.rel 18446744073709236178] 5) :=
  Dec.shift (j := 2153) (k := 0) (pc2153_0 feat) wc2153 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_PROFILE_OUTPUT")`. -/
def pc2189 : List Byte := [0xe8, 0xae, 0x2f, 0xfb, 0xff]
theorem pc2189_0 : ∀ feat, Dec feat pc2189 0 (FV7z.mk .call 64 [.rel 18446744073709236142] 5) := by dec_rfl
theorem wc2189 : pc2189 <+: ndi.drop 2189 := by decide +kernel
theorem call_2189 (feat : Features) : Dec feat ndi 2189 (FV7z.mk .call 64 [.rel 18446744073709236142] 5) :=
  Dec.shift (j := 2189) (k := 0) (pc2189_0 feat) wc2189 (Nat.zero_le _)

/-- The `call` of `getenv ("LD_ASSUME_KERNEL")`. -/
def pc2276 : List Byte := [0xe8, 0x57, 0x2f, 0xfb, 0xff]
theorem pc2276_0 : ∀ feat, Dec feat pc2276 0 (FV7z.mk .call 64 [.rel 18446744073709236055] 5) := by dec_rfl
theorem wc2276 : pc2276 <+: ndi.drop 2276 := by decide +kernel
theorem call_2276 (feat : Features) : Dec feat ndi 2276 (FV7z.mk .call 64 [.rel 18446744073709236055] 5) :=
  Dec.shift (j := 2276) (k := 0) (pc2276_0 feat) wc2276 (Nat.zero_le _)

/-- The `call` of `strlen` (PLT). -/
def pc2563 : List Byte := [0xe8, 0xd0, 0x0e, 0xd9, 0xff]
theorem pc2563_0 : ∀ feat, Dec feat pc2563 0 (FV7z.mk .call 64 [.rel 18446744073706999504] 5) := by dec_rfl
theorem wc2563 : pc2563 <+: ndi.drop 2563 := by decide +kernel
theorem call_2563 (feat : Features) : Dec feat ndi 2563 (FV7z.mk .call 64 [.rel 18446744073706999504] 5) :=
  Dec.shift (j := 2563) (k := 0) (pc2563_0 feat) wc2563 (Nat.zero_le _)

/-- The `call` of `_dl_protect_relro`. -/
def pc2879 : List Byte := [0xe8, 0x2c, 0xb3, 0x03, 0x00]
theorem pc2879_0 : ∀ feat, Dec feat pc2879 0 (FV7z.mk .call 64 [.rel 242476] 5) := by dec_rfl
theorem wc2879 : pc2879 <+: ndi.drop 2879 := by decide +kernel
theorem call_2879 (feat : Features) : Dec feat ndi 2879 (FV7z.mk .call 64 [.rel 242476] 5) :=
  Dec.shift (j := 2879) (k := 0) (pc2879_0 feat) wc2879 (Nat.zero_le _)

/-- The `ret` after `_dl_protect_relro`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_2896 : pret <+: ndi.drop 2896 := by decide +kernel
theorem ret_2896 (feat : Features) : Dec feat ndi 2896 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 2896) (k := 0) (pret_0 feat) w_2896 (Nat.zero_le _)

end FV7z.Ndi
