import FV7z.Cpv.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Env
import FV7z.Hca.Holds
/-!
# `ConvertPropVariantToShortString (prop, dest)` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertPropVariantToShortString` at `0x457b10` in `7zzs` (`CPP/Windows/PropVariantConv.cpp`;
`objdump -d`). `rdi` is the `PROPVARIANT`: its type tag `vt` (16 bits) at `[rdi]`, its value at `[rdi + 8]`; `rsi` is
`dest`. `*dest = 0` first; then `vt` above 64 (`ja`), or by the jump table at `0x6d9570` (65 entries, `cpv_cases`):
`VT_EMPTY` the `ret` at 40; `VT_BOOL` '-' or '+' and 0 stored, the `ret` at 91; `VT_BSTR` "?" and 0 stored, the `ret`
at 168; the numbers: a tail jump to `ConvertUInt32ToString` (`0x44ab70`), `ConvertInt64ToString` (`0x44aea0`) or
`ConvertUInt64ToString` (`0x44ac30`) with the value in `rdi`; `VT_FILETIME` a tail jump to `0x457a10` with `rdi` at the
value, `rdx` = 0; every other tag: "?:" stored, a tail jump to `ConvertUInt64ToString (vt, dest + 2)`.

The callees are hypotheses: continuations at their entries (`kj`), with `Jt` of the registers and the bytes.

- `clw`: the case of a tag, as the code picks it (48 above 64, else the table's entry); `Vz`, `Vq`, `Vb`, `Vs`: the
  bytes after the stores; `Jt`: the tail jumps; `Ex`: the exits; `Inv`: the cut points (the entry, then a case with
  `*dest = 0` stored and only `rax`, `rdx` written).
- `vc_*`: the verification conditions of the pieces; `vcAll` by the case.
- `cpv_ok`: from the entry to a `ret` (`kr`, the bytes `Rv`, the registers a call keeps) or a tail jump (`kj`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Cpv

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_40 : pret <+: cpv.drop 40 := by decide +kernel
theorem w_91 : pret <+: cpv.drop 91 := by decide +kernel
theorem w_168 : pret <+: cpv.drop 168 := by decide +kernel
theorem ret_40 (feat : Features) : Dec feat cpv 40 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 40) (k := 0) (pret_0 feat) w_40 (Nat.zero_le _)
theorem ret_91 (feat : Features) : Dec feat cpv 91 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 91) (k := 0) (pret_0 feat) w_91 (Nat.zero_le _)
theorem ret_168 (feat : Features) : Dec feat cpv 168 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 168) (k := 0) (pret_0 feat) w_168 (Nat.zero_le _)

/-! The tail jumps: to `ConvertUInt64ToString` (`4500528` = `0x44ac30`), `ConvertUInt32ToString` (`4500336` =
`0x44ab70`), `ConvertInt64ToString` (`4501152` = `0x44aea0`), `0x457a10` (`4553232`). -/
def pj64 : List Byte := [0xe9, 0xdb, 0x30, 0xff, 0xff]
theorem pj64_0 : ∀ feat, Dec feat pj64 0 (FV7z.mk .jmp 64 [.rel 18446744073709498587] 5) := by dec_rfl
theorem wj64 : pj64 <+: cpv.drop 64 := by decide +kernel
theorem jmp_64 (feat : Features) : Dec feat cpv 64 (FV7z.mk .jmp 64 [.rel 18446744073709498587] 5) :=
  Dec.shift (j := 64) (k := 0) (pj64_0 feat) wj64 (Nat.zero_le _)
theorem tgt_64 : cpv_at.add (64 + 5) + BitVec.ofNat 64 18446744073709498587 = (4500528#64).add 0 := by decide
def pj100 : List Byte := [0xe9, 0xf7, 0x2f, 0xff, 0xff]
theorem pj100_0 : ∀ feat, Dec feat pj100 0 (FV7z.mk .jmp 64 [.rel 18446744073709498359] 5) := by dec_rfl
theorem wj100 : pj100 <+: cpv.drop 100 := by decide +kernel
theorem jmp_100 (feat : Features) : Dec feat cpv 100 (FV7z.mk .jmp 64 [.rel 18446744073709498359] 5) :=
  Dec.shift (j := 100) (k := 0) (pj100_0 feat) wj100 (Nat.zero_le _)
theorem tgt_100 : cpv_at.add (100 + 5) + BitVec.ofNat 64 18446744073709498359 = (4500336#64).add 0 := by decide
def pj116 : List Byte := [0xe9, 0xe7, 0x2f, 0xff, 0xff]
theorem pj116_0 : ∀ feat, Dec feat pj116 0 (FV7z.mk .jmp 64 [.rel 18446744073709498343] 5) := by dec_rfl
theorem wj116 : pj116 <+: cpv.drop 116 := by decide +kernel
theorem jmp_116 (feat : Features) : Dec feat cpv 116 (FV7z.mk .jmp 64 [.rel 18446744073709498343] 5) :=
  Dec.shift (j := 116) (k := 0) (pj116_0 feat) wj116 (Nat.zero_le _)
theorem tgt_116 : cpv_at.add (116 + 5) + BitVec.ofNat 64 18446744073709498343 = (4500336#64).add 0 := by decide
def pj131 : List Byte := [0xe9, 0xd8, 0x2f, 0xff, 0xff]
theorem pj131_0 : ∀ feat, Dec feat pj131 0 (FV7z.mk .jmp 64 [.rel 18446744073709498328] 5) := by dec_rfl
theorem wj131 : pj131 <+: cpv.drop 131 := by decide +kernel
theorem jmp_131 (feat : Features) : Dec feat cpv 131 (FV7z.mk .jmp 64 [.rel 18446744073709498328] 5) :=
  Dec.shift (j := 131) (k := 0) (pj131_0 feat) wj131 (Nat.zero_le _)
theorem tgt_131 : cpv_at.add (131 + 5) + BitVec.ofNat 64 18446744073709498328 = (4500336#64).add 0 := by decide
def pj148 : List Byte := [0xe9, 0xf7, 0x32, 0xff, 0xff]
theorem pj148_0 : ∀ feat, Dec feat pj148 0 (FV7z.mk .jmp 64 [.rel 18446744073709499127] 5) := by dec_rfl
theorem wj148 : pj148 <+: cpv.drop 148 := by decide +kernel
theorem jmp_148 (feat : Features) : Dec feat cpv 148 (FV7z.mk .jmp 64 [.rel 18446744073709499127] 5) :=
  Dec.shift (j := 148) (k := 0) (pj148_0 feat) wj148 (Nat.zero_le _)
theorem tgt_148 : cpv_at.add (148 + 5) + BitVec.ofNat 64 18446744073709499127 = (4501152#64).add 0 := by decide
def pj181 : List Byte := [0xe9, 0xd6, 0x32, 0xff, 0xff]
theorem pj181_0 : ∀ feat, Dec feat pj181 0 (FV7z.mk .jmp 64 [.rel 18446744073709499094] 5) := by dec_rfl
theorem wj181 : pj181 <+: cpv.drop 181 := by decide +kernel
theorem jmp_181 (feat : Features) : Dec feat cpv 181 (FV7z.mk .jmp 64 [.rel 18446744073709499094] 5) :=
  Dec.shift (j := 181) (k := 0) (pj181_0 feat) wj181 (Nat.zero_le _)
theorem tgt_181 : cpv_at.add (181 + 5) + BitVec.ofNat 64 18446744073709499094 = (4501152#64).add 0 := by decide
def pj198 : List Byte := [0xe9, 0x35, 0xfe, 0xff, 0xff]
theorem pj198_0 : ∀ feat, Dec feat pj198 0 (FV7z.mk .jmp 64 [.rel 18446744073709551157] 5) := by dec_rfl
theorem wj198 : pj198 <+: cpv.drop 198 := by decide +kernel
theorem jmp_198 (feat : Features) : Dec feat cpv 198 (FV7z.mk .jmp 64 [.rel 18446744073709551157] 5) :=
  Dec.shift (j := 198) (k := 0) (pj198_0 feat) wj198 (Nat.zero_le _)
theorem tgt_198 : cpv_at.add (198 + 5) + BitVec.ofNat 64 18446744073709551157 = (4553232#64).add 0 := by decide
def pj212 : List Byte := [0xe9, 0xb7, 0x32, 0xff, 0xff]
theorem pj212_0 : ∀ feat, Dec feat pj212 0 (FV7z.mk .jmp 64 [.rel 18446744073709499063] 5) := by dec_rfl
theorem wj212 : pj212 <+: cpv.drop 212 := by decide +kernel
theorem jmp_212 (feat : Features) : Dec feat cpv 212 (FV7z.mk .jmp 64 [.rel 18446744073709499063] 5) :=
  Dec.shift (j := 212) (k := 0) (pj212_0 feat) wj212 (Nat.zero_le _)
theorem tgt_212 : cpv_at.add (212 + 5) + BitVec.ofNat 64 18446744073709499063 = (4501152#64).add 0 := by decide
def pj228 : List Byte := [0xe9, 0x37, 0x30, 0xff, 0xff]
theorem pj228_0 : ∀ feat, Dec feat pj228 0 (FV7z.mk .jmp 64 [.rel 18446744073709498423] 5) := by dec_rfl
theorem wj228 : pj228 <+: cpv.drop 228 := by decide +kernel
theorem jmp_228 (feat : Features) : Dec feat cpv 228 (FV7z.mk .jmp 64 [.rel 18446744073709498423] 5) :=
  Dec.shift (j := 228) (k := 0) (pj228_0 feat) wj228 (Nat.zero_le _)
theorem tgt_228 : cpv_at.add (228 + 5) + BitVec.ofNat 64 18446744073709498423 = (4500528#64).add 0 := by decide

/-! ## What the function does -/

/-- The type tag `vt`. -/
abbrev vtg (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 (List.map V (byteAddrs g.rdi 2))
/-- The value's first `n` bytes. -/
abbrev vqb (V : Addr → Byte) (g : Gprs) (n : Nat) : List Byte := List.map V (byteAddrs (g.rdi + 8#64) n)

/-- The case of a tag: 48 above 64 (`ja`), else the table's entry. -/
def clw (w : BitVec 16) : Nat := if 64 < w.toNat then 48 else cpv_cases.getD w.toNat 0

/-- The cut points after the entry. -/
abbrev Cs (ℓ : Nat) : Prop :=
  ℓ = 48 ∨ ℓ = 72 ∨ ℓ = 96 ∨ ℓ = 112 ∨ ℓ = 128 ∨ ℓ = 144 ∨ ℓ = 160 ∨ ℓ = 176 ∨ ℓ = 192 ∨ ℓ = 208 ∨ ℓ = 224

/-- `VT_BOOL`: '-' for `VARIANT_FALSE` (0), else '+'. -/
def sgc (w : BitVec 16) : BitVec 8 := if w = 0#16 then 45#8 else 43#8

/-- After `*dest = 0`. -/
def Vz (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V g.rsi (toBytesLE 0#8 1)
/-- After "?:" (`0x3a3f`) at `dest`. -/
def Vq (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (Vz V g) g.rsi (toBytesLE 14911#16 2)
/-- After '-' or '+' and 0 at `dest`. -/
def Vb (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vz V g) (g.rsi + 1#64) (toBytesLE 0#8 1)) g.rsi (toBytesLE (sgc (ofBytesLE 16 (vqb V g 2))) 1)
/-- After "?" and 0 (`0x3f`, 16 bits) at `dest`. -/
def Vs (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (Vz V g) g.rsi (toBytesLE 63#16 2)

/-- The registers at the entry with `rax` and `rdx` written. -/
abbrev Rg (g₀ g : Gprs) : Prop := ∃ a b : BitVec 64, g = { g₀ with rax := a, rdx := b }

/-- What the function needs: the bytes it reads in the footprint's data, `dest` and `dest + 1` in what it may store
into and apart from what it reads, the table's bytes. -/
structure Pc (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (g : Gprs) : Prop where
  fP : ∀ i < 2, Foot F.data (Addr.add g.rdi i)
  fQ : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i)
  fT : ∀ i < 260, Foot F.data (Addr.add 7181680#64 i)
  wD : ∀ i < 2, Foot Wl (Addr.add g.rsi i)
  jt : List.map V (byteAddrs 7181680#64 260) = cpv_jt
  sP : ∀ i < 2, ∀ j < 2, Addr.add g.rdi i ≠ Addr.add g.rsi j
  sQ : ∀ i < 8, ∀ j < 2, Addr.add (g.rdi + 8#64) i ≠ Addr.add g.rsi j
  sT : ∀ i < 260, ∀ j < 2, Addr.add 7181680#64 i ≠ Addr.add g.rsi j

/-- The tail jumps to `T`: the case, the registers, the bytes. -/
def Jt (V0 : Addr → Byte) (g0 : Gprs) (T : Addr) (g : Gprs) (V : Addr → Byte) : Prop :=
  (clw (vtg V0 g0) = 48 ∧ T = 4500528#64 ∧
      g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (vtg V0 g0)) ∧ g.rsi = g0.rsi + 2#64 ∧ V = Vq V0 g0) ∨
  (clw (vtg V0 g0) = 96 ∧ T = 4500336#64 ∧
      g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 (vqb V0 g0 1))) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 112 ∧ T = 4500336#64 ∧
      g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 16 (vqb V0 g0 2))) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 128 ∧ T = 4500336#64 ∧
      g.rdi = BitVec.setWidth 64 (ofBytesLE 32 (vqb V0 g0 4)) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 144 ∧ T = 4501152#64 ∧
      g.rdi = BitVec.signExtend 64 (ofBytesLE 32 (vqb V0 g0 4)) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 176 ∧ T = 4501152#64 ∧
      g.rdi = BitVec.signExtend 64 (ofBytesLE 16 (vqb V0 g0 2)) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 192 ∧ T = 4553232#64 ∧
      g.rdi = g0.rdi + 8#64 ∧ g.rdx = 0 ∧ g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 208 ∧ T = 4501152#64 ∧
      g.rdi = ofBytesLE 64 (vqb V0 g0 8) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0) ∨
  (clw (vtg V0 g0) = 224 ∧ T = 4500528#64 ∧
      g.rdi = ofBytesLE 64 (vqb V0 g0 8) ∧
      g.rsi = g0.rsi ∧ V = Vz V0 g0)

/-- At an exit: the registers a call keeps as at the entry; the `ret`s with what is stored, the tail jumps (`Jt`). -/
def Ex (V0 : Addr → Byte) (g0 : Gprs) (j : Nat) (g : Gprs) (_fl : Rflags) (V : Addr → Byte) : Prop :=
  Kp g0 g ∧ ((j = 40 ∧ clw (vtg V0 g0) = 40 ∧ V = Vz V0 g0) ∨
    (j = 91 ∧ clw (vtg V0 g0) = 72 ∧ V = Vb V0 g0) ∨
    (j = 168 ∧ clw (vtg V0 g0) = 160 ∧ V = Vs V0 g0) ∨
    (j = 64 ∧ Jt V0 g0 4500528#64 g V) ∨
    (j = 100 ∧ Jt V0 g0 4500336#64 g V) ∨
    (j = 116 ∧ Jt V0 g0 4500336#64 g V) ∨
    (j = 131 ∧ Jt V0 g0 4500336#64 g V) ∨
    (j = 148 ∧ Jt V0 g0 4501152#64 g V) ∨
    (j = 181 ∧ Jt V0 g0 4501152#64 g V) ∨
    (j = 198 ∧ Jt V0 g0 4553232#64 g V) ∨
    (j = 212 ∧ Jt V0 g0 4501152#64 g V) ∨
    (j = 228 ∧ Jt V0 g0 4500528#64 g V))

/-- The invariant at the cut points: the entry; a case, `*dest = 0` stored, `rax` and `rdx` written. -/
def Inv (V0 : Addr → Byte) (g0 : Gprs) (ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = 2 ∧ g = g0 ∧ V = V0) ∨ (Cs ℓ ∧ ℓ = clw (vtg V0 g0) ∧ m = 1 ∧ Rg g0 g ∧ V = Vz V0 g0)

/-- At an exit of a piece: a cut point's invariant with a smaller measure, or an exit of the function. -/
def Nx (V0 : Addr → Byte) (g0 : Gprs) (m : Nat) (j : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) : Prop :=
  (∃ m' < m, Inv V0 g0 j m' g V) ∨ Ex V0 g0 j g f V

/-- The bytes at a `ret`. -/
def Rv (V0 : Addr → Byte) (g0 : Gprs) (V : Addr → Byte) : Prop :=
  (clw (vtg V0 g0) = 40 ∧ V = Vz V0 g0) ∨ (clw (vtg V0 g0) = 72 ∧ V = Vb V0 g0) ∨
    (clw (vtg V0 g0) = 160 ∧ V = Vs V0 g0)

/-! ## Memory -/

/-- Bytes apart from a store: as they were. -/
theorem rdv {W : Addr → Byte} {d a : Addr} {bs : List Byte} {n : Nat}
    (h : ∀ i < n, ∀ j < bs.length, Addr.add a i ≠ Addr.add d j) :
    List.map (Vst W d bs) (byteAddrs a n) = List.map W (byteAddrs a n) :=
  List.map_congr_left fun y hy => by
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
    exact Vst_apart bs W d _ fun j hj => h i hi j hj

/-- Bytes apart from `d` and `d + 1`: as they were after a store of at most 2 bytes at `d`. -/
theorem svx {a d : Addr} {n : Nat} (h : ∀ i < n, ∀ j < 2, Addr.add a i ≠ Addr.add d j) :
    ∀ (W : Addr → Byte) (bs : List Byte), bs.length ≤ 2 →
      List.map (Vst W d bs) (byteAddrs a n) = List.map W (byteAddrs a n) :=
  fun _ _ hb => rdv fun i hi j hj => h i hi j (by omega)

/-- `svx` for a store of 1 byte. -/
theorem sv1 {a d : Addr} {n : Nat} (h : ∀ i < n, ∀ j < 2, Addr.add a i ≠ Addr.add d j) (W : Addr → Byte) {w : Nat}
    (x : BitVec w) : List.map (Vst W d (toBytesLE x 1)) (byteAddrs a n) = List.map W (byteAddrs a n) :=
  svx h W _ (by rw [toBytesLE_length] <;> omega)

/-- `svx` for a store of 2 bytes. -/
theorem sv2 {a d : Addr} {n : Nat} (h : ∀ i < n, ∀ j < 2, Addr.add a i ≠ Addr.add d j) (W : Addr → Byte) {w : Nat}
    (x : BitVec w) : List.map (Vst W d (toBytesLE x 2)) (byteAddrs a n) = List.map W (byteAddrs a n) :=
  svx h W _ (by rw [toBytesLE_length] <;> omega)

/-- `rsi + 2 - 2`. -/
theorem m2 (x : BitVec 64) : x + 2#64 + 18446744073709551614#64 = x := by
  have h : (2#64 : BitVec 64) + 18446744073709551614#64 = 0#64 := by decide
  rw [BitVec.add_assoc, h, BitVec.add_zero]

/-! ## The jump table -/

theorem jt_addr (w : BitVec 32) (_h : w.toNat ≤ 64) :
    7181680#64 + BitVec.setWidth 64 w * 4#64 = Addr.add 7181680#64 (4 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem jt_case : ∀ k < 65, (ofBytesLE 32 ((cpv_jt.drop (4 * k)).take 4)).signExtend 64 + 7181680#64 =
    Addr.add cpv_at (cpv_cases.getD k 0) := by decide +kernel

theorem cs_ok : ∀ k < 65, (cpv_cases.getD k 0 = 40 ∨ Cs (cpv_cases.getD k 0)) ∧ cpv_cases.getD k 0 < 233 := by
  decide +kernel

variable {F : Footprint} {Wl : List Rgn} {V0 : Addr → Byte} {g0 g : Gprs} {m : Nat} {f : Rflags}

/-- The table's entries, `*dest = 0` stored. -/
theorem jt_V (hP : Pc F Wl V0 g0) : ∀ bs : List Byte, bs.length ≤ 2 → ∀ k < 65,
    List.map (Vst V0 g0.rsi bs) (byteAddrs (Addr.add 7181680#64 (4 * k)) 4) = (cpv_jt.drop (4 * k)).take 4 := by
  intro bs hb k hk
  refine (rdv (n := 4) (a := Addr.add 7181680#64 (4 * k)) (d := g0.rsi) (bs := bs) (W := V0) ?_).trans
    (Hca.sub_rd V0 _ cpv_jt 260 hP.jt (4 * k) 4 (by omega))
  intro i hi j hj
  rw [addr_add_add']
  exact hP.sT (4 * k + i) (by omega) j (by omega)

theorem jt_foot (fT : ∀ i < 260, Foot F.data (Addr.add 7181680#64 i)) (w : BitVec 32) (hw : w.toNat ≤ 64) :
    ∀ i < 4, Foot F.data (Addr.add (7181680#64 + BitVec.setWidth 64 w * 4#64) i) := by
  intro i hi
  rw [jt_addr w hw, addr_add_add']
  exact fT _ (by omega)

/-- The table's target, a case. -/
theorem tg {P : Nat → Prop} (V : Addr → Byte) (w : BitVec 32) (hw : w.toNat ≤ 64)
    (hrd : ∀ k < 65, List.map V (byteAddrs (Addr.add 7181680#64 (4 * k)) 4) = (cpv_jt.drop (4 * k)).take 4)
    (hq : P (cpv_cases.getD w.toNat 0)) :
    ∃ tgt, tgt < cpv.length ∧ BitVec.signExtend 64 (ofBytesLE 32 (List.map V
      (byteAddrs (7181680#64 + BitVec.setWidth 64 w * 4#64) 4))) + 7181680#64 = Addr.add cpv_at tgt ∧ P tgt := by
  have hk : w.toNat < 65 := by omega
  rw [jt_addr w hw, hrd _ hk]
  exact ⟨_, lt_len (cs_ok w.toNat hk).2, jt_case w.toNat hk, hq⟩

/-- `ja` taken after `cmp word [rdi], 64`. -/
theorem cl_ja {v : BitVec 16} (h : (!(decide (v.toNat < 64) || decide (v = 64#16))) = true) : 48 = clw v := by
  have h3 : 64 < v.toNat := by
    by_cases h1 : v.toNat < 64
    · simp [h1] at h
    · by_cases h2 : v = 64#16
      · subst h2
        simp at h
      · have h4 : v.toNat ≠ 64 := fun e => h2 (BitVec.eq_of_toNat_eq (by rw [e]; decide))
        omega
  unfold clw
  rw [if_pos h3]

/-- `ja` not taken: the index in the table. -/
theorem ja_w {v : BitVec 16} (h : (!(decide (v.toNat < 64) || decide (v = 64#16))) = false) :
    (BitVec.setWidth 32 v).toNat ≤ 64 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
  by_cases h1 : v.toNat < 64
  · omega
  · by_cases h2 : v = 64#16
    · subst h2
      decide
    · simp [h1, h2] at h

/-- The character of `VT_BOOL`, as `cmp word [rdi + 8], 1; sbb eax, eax; and eax, 2; add eax, 43` computes it. -/
theorem sgc_eq (w : BitVec 16) (a : BitVec 64) :
    BitVec.setWidth 8 (((BitVec.setWidth 32 a - BitVec.setWidth 32 a -
      BitVec.setWidth 32 (BitVec.ofBool (decide (w.toNat < 1)))) &&& 2#32) + 43#32) = sgc w := by
  rw [BitVec.sub_self]
  unfold sgc
  by_cases hw : w.toNat < 1
  · rw [decide_eq_true hw,
      if_pos (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega))]
    decide
  · rw [decide_eq_false hw, if_neg fun h => hw (by rw [h]; decide)]
    decide

/-! ## The exits -/

local macro "rK" : term => `(⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem eI {ℓ : Nat} (hc : Cs ℓ) (h : ℓ = clw (vtg V0 g0)) (hR : Rg g0 g) (hm : 1 < m) :
    Nx V0 g0 m ℓ g f (Vz V0 g0) := by
  unfold Nx Inv
  exact Or.inl ⟨1, hm, Or.inr ⟨hc, h, rfl, hR, rfl⟩⟩

/-! The exits of the pieces. -/

theorem x40 (h : 40 = clw (vtg V0 g0)) (hk : Kp g0 g) : Nx V0 g0 m 40 g f (Vz V0 g0) := by
  unfold Nx Ex
  refine Or.inr ⟨hk, ?_⟩
  refine Or.inl ⟨rfl, h.symm, rfl⟩
theorem x91 {c : BitVec 8} (h : 72 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hc : c = sgc (ofBytesLE 16 (vqb V0 g0 2))) :
    Nx V0 g0 m 91 g f (Vst (Vst (Vz V0 g0) (g0.rsi + 1#64) (toBytesLE 0#8 1)) g0.rsi (toBytesLE c 1)) := by
  subst hc
  unfold Nx Ex
  refine Or.inr ⟨hk, ?_⟩
  iterate 1 apply Or.inr
  refine Or.inl ⟨rfl, h.symm, rfl⟩
theorem x168 {c : BitVec 16} (h : 160 = clw (vtg V0 g0)) (hk : Kp g0 g) (hc : c = 63#16) :
    Nx V0 g0 m 168 g f (Vst (Vz V0 g0) g0.rsi (toBytesLE c 2)) := by
  subst hc
  unfold Nx Ex
  refine Or.inr ⟨hk, ?_⟩
  iterate 2 apply Or.inr
  refine Or.inl ⟨rfl, h.symm, rfl⟩
theorem x64 {c : BitVec 16} (h : 48 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (vtg V0 g0))) (hs : g.rsi = g0.rsi + 2#64)
    (hc : c = 14911#16) : Nx V0 g0 m 64 g f (Vst (Vz V0 g0) g0.rsi (toBytesLE c 2)) := by
  subst hc
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 3 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x100 (h : 96 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 8 (vqb V0 g0 1)))) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 100 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 4 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 1 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x116 (h : 112 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 16 (vqb V0 g0 2)))) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 116 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 5 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 2 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x131 (h : 128 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.setWidth 64 (ofBytesLE 32 (vqb V0 g0 4))) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 131 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 6 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 3 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x148 (h : 144 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.signExtend 64 (ofBytesLE 32 (vqb V0 g0 4))) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 148 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 7 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 4 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x181 (h : 176 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = BitVec.signExtend 64 (ofBytesLE 16 (vqb V0 g0 2))) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 181 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 8 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 5 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x198 (h : 192 = clw (vtg V0 g0)) (hk : Kp g0 g) (hd : g.rdi = g0.rdi + 8#64)
    (hx : g.rdx = 0) (hs : g.rsi = g0.rsi) : Nx V0 g0 m 198 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 9 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 6 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hx, hs, rfl⟩
theorem x212 (h : 208 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = ofBytesLE 64 (vqb V0 g0 8)) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 212 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 10 apply Or.inr
  refine Or.inl ⟨rfl, ?_⟩
  iterate 7 apply Or.inr
  refine Or.inl ⟨h.symm, rfl, hd, hs, rfl⟩
theorem x228 (h : 224 = clw (vtg V0 g0)) (hk : Kp g0 g)
    (hd : g.rdi = ofBytesLE 64 (vqb V0 g0 8)) (hs : g.rsi = g0.rsi) :
    Nx V0 g0 m 228 g f (Vz V0 g0) := by
  unfold Nx Ex Jt
  refine Or.inr ⟨hk, ?_⟩
  iterate 11 apply Or.inr
  refine ⟨rfl, ?_⟩
  iterate 8 apply Or.inr
  refine ⟨h.symm, rfl, hd, hs, rfl⟩

/-- A case from the table: a cut point's invariant, or the `ret` at 40. -/
theorem eT (hw : (BitVec.setWidth 32 (vtg V0 g0)).toNat ≤ 64) (hR : Rg g0 g) :
    Nx V0 g0 2 (cpv_cases.getD (BitVec.setWidth 32 (vtg V0 g0)).toNat 0) g f (Vz V0 g0) := by
  have h1 : (BitVec.setWidth 32 (vtg V0 g0)).toNat = (vtg V0 g0).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (vtg V0 g0).isLt (by decide))]
  have hk : (BitVec.setWidth 32 (vtg V0 g0)).toNat < 65 := by omega
  have hc : clw (vtg V0 g0) = cpv_cases.getD (BitVec.setWidth 32 (vtg V0 g0)).toNat 0 := by
    unfold clw
    rw [if_neg (by omega), h1]
  rcases (cs_ok _ hk).1 with h40 | hcs
  · rw [h40]
    obtain ⟨a, b, rfl⟩ := hR
    exact x40 (hc.trans h40).symm rK
  · exact eI hcs hc.symm hR (by decide)

/-! ## The cut points -/

set_option hygiene false in
/-- What is left of a piece's condition: the exit `t`, the footprint facts. -/
local macro "cfin" t:term : tactic =>
  `(tactic| all_goals repeat' (first
    | exact $t
    | assumption
    | exact fun i hi => fP i (by omega)
    | exact fun i hi => fQ i (by omega)
    | exact fun i hi => wD i (by omega)
    | rfl
    | apply And.intro
    | intro _))

set_option maxHeartbeats 1000000 in
/-- From the entry: `*dest = 0`; `vt` above 64, to 48; else by the table. -/
theorem vc_0 (hP : Pc F Wl V0 g0) : W_0 F Wl (Nx V0 g0 2) g0 f V0 := by
  have fP := hP.fP
  have fT := hP.fT
  have wD := hP.wD
  have sp := sv1 hP.sP
  have hjv := jt_V hP
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP wD sp hjv
  wpx [W_0, W_13, o0, o1, Op.cmpmi, Op.ldsx, sp]
  all_goals repeat' (first
    | assumption
    | exact fun i hi => wD i (by omega)
    | exact eI (by decide) (cl_ja ‹_›) ⟨_, _, rfl⟩ (by decide)
    | exact jt_foot fT _ (ja_w ‹_›)
    | exact tg _ _ (ja_w ‹_›) (hjv _ (by simp [toBytesLE_length])) (eT (ja_w ‹_›) ⟨_, _, rfl⟩)
    | refine tg _ _ (ja_w ‹_›) (hjv _ (by simp [toBytesLE_length])) ?_
    | exact (show Nx _ _ _ (cpv_cases.getD _ _) _ _ _ from eT (ja_w ‹_›) ⟨_, _, rfl⟩)
    | rfl
    | apply And.intro
    | intro _)

/-- The "?:" for an unknown `vt`, `vt` and `dest + 2` for `ConvertUInt64ToString`. -/
theorem vc_48 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 48 = clw (vtg V0 g0)) :
    W_48 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have sp := sv1 hP.sP
  have sq := sv2 hP.sP
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD sp sq ⊢
  wpx [W_48, o2, Vz, sp, sq, m2]
  cfin x64 hℓ rK rfl rfl (by decide)

/-- `VT_BOOL`: '-' or '+', then 0. -/
theorem vc_72 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 72 = clw (vtg V0 g0)) :
    W_72 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s2 := sv1 (n := 2) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s2 ⊢
  have wD1 : ∀ i < 1, Foot Wl (Addr.add (rsi + 1#64) i) := fun i hi => by
    have h := wD (1 + i) (by omega)
    rw [← addr_add_add'] at h
    exact h
  wpx [W_72, o3, Vz, s2, Op.cmpmi]
  cfin x91 hℓ rK (sgc_eq _ _)

/-- `VT_UI1`: `movzx edi, byte [rdi + 8]`, to `ConvertUInt32ToString`. -/
theorem vc_96 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 96 = clw (vtg V0 g0)) :
    W_96 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s1 := sv1 (n := 1) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s1 ⊢
  wpx [W_96, o4, Vz, s1]
  cfin x100 hℓ rK rfl rfl

/-- `VT_UI2`. -/
theorem vc_112 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 112 = clw (vtg V0 g0)) :
    W_112 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s2 := sv1 (n := 2) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s2 ⊢
  wpx [W_112, o5, Vz, s2]
  cfin x116 hℓ rK rfl rfl

/-- `VT_UI4`. -/
theorem vc_128 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 128 = clw (vtg V0 g0)) :
    W_128 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s4 := sv1 (n := 4) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s4 ⊢
  wpx [W_128, o6, Vz, s4]
  cfin x131 hℓ rK rfl rfl

/-- `VT_I4`. -/
theorem vc_144 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 144 = clw (vtg V0 g0)) :
    W_144 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s4 := sv1 (n := 4) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s4 ⊢
  wpx [W_144, o7, Vz, s4, Op.ldsx]
  cfin x148 hℓ rK rfl rfl

/-- `VT_BSTR`: "?", then 0. -/
theorem vc_160 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 160 = clw (vtg V0 g0)) :
    W_160 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD ⊢
  wpx [W_160, o8, Vz]
  cfin x168 hℓ rK (by decide)

/-- `VT_I2`. -/
theorem vc_176 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 176 = clw (vtg V0 g0)) :
    W_176 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s2 := sv1 (n := 2) fun i hi => hP.sQ i (by omega)
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s2 ⊢
  wpx [W_176, o9, Vz, s2, Op.ldsxw]
  cfin x181 hℓ rK rfl rfl

/-- `VT_FILETIME`: `rdi` at the value, `edx` = 0. -/
theorem vc_192 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 192 = clw (vtg V0 g0)) :
    W_192 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD ⊢
  wpx [W_192, o10, Vz, lf_xz]
  cfin x198 hℓ rK rfl rfl rfl

/-- `VT_I8`. -/
theorem vc_208 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 208 = clw (vtg V0 g0)) :
    W_208 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s8 := sv1 (n := 8) hP.sQ
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s8 ⊢
  wpx [W_208, o11, Vz, s8]
  cfin x212 hℓ rK rfl rfl

/-- `VT_UI8`. -/
theorem vc_224 (hP : Pc F Wl V0 g0) (hR : Rg g0 g) (hℓ : 224 = clw (vtg V0 g0)) :
    W_224 F Wl (Nx V0 g0 1) g f (Vz V0 g0) := by
  have fP := hP.fP
  have fQ := hP.fQ
  have wD := hP.wD
  have s8 := sv1 (n := 8) hP.sQ
  obtain ⟨a, b, rfl⟩ := hR
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g0
  dsimp only at fP fQ wD s8 ⊢
  wpx [W_224, o11, Vz, s8]
  cfin x228 hℓ rK rfl rfl

theorem vcAll (hP : Pc F Wl V0 g0) (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv V0 g0 ℓ m g V) :
    Wt ℓ F Wl (Nx V0 g0 m) g f V := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨hc, hℓ, rfl, hR, rfl⟩ := h
  · exact vc_0 hP
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact vc_48 hP hR hℓ
    · exact vc_72 hP hR hℓ
    · exact vc_96 hP hR hℓ
    · exact vc_112 hP hR hℓ
    · exact vc_128 hP hR hℓ
    · exact vc_144 hP hR hℓ
    · exact vc_160 hP hR hℓ
    · exact vc_176 hP hR hℓ
    · exact vc_192 hP hR hℓ
    · exact vc_208 hP hR hℓ
    · exact vc_224 hP hR hℓ

/-! ## From the entry to an exit -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The return address apart from a store. -/
theorem rdq_st {W : Addr → Byte} {d a : Addr} {bs : List Byte}
    (h : ∀ i < 8, ∀ j < bs.length, Addr.add a i ≠ Addr.add d j) : rdq(Vst W d bs, a) = rdq(W, a) :=
  congrArg (ofBytesLE 64) (rdv h)

/-- A tail jump at `j` to `T`. -/
theorem tj (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpv_at cpv) {j R T : Nat} {code₂ : List Byte} {Y : State}
    {t : Nat} {V : Addr → Byte} (hj : j < 233) (hd : Dec prof.feat cpv j (FV7z.mk .jmp 64 [.rel R] 5))
    (hinT : CodeIn L (BitVec.ofNat 64 T) code₂) (hT : 0 < code₂.length)
    (ht : cpv_at.add (j + 5) + BitVec.ofNat 64 R = (BitVec.ofNat 64 T).add 0)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hr : Y.cpu.rip = cpv_at.add j)
    (k : ∀ (Y' : State) (t' : Nat), KeptW Wl s₀ Y' → Agree F Y'.proc.mm.mem V → Y'.cpu.rip = BitVec.ofNat 64 T →
      Y'.cpu.gpr = Y.cpu.gpr → GoG prof L o gev gP gE Y' t') :
    GoG prof L o gev gP gE Y t :=
  c.s_jmp_x hK hA hin (lt_len hj) hr hd hinT hT ht fun Y' t' hK' hA' ⟨hr', hg'⟩ =>
    k Y' t' hK' hA' (by rw [hr', addr_add_zero]) hg'

/-- `ConvertPropVariantToShortString (prop, dest)` from its entry: to the return address after `*dest` = 0, the
character of `VT_BOOL` and 0, or "?" (`Rv`), the registers a call keeps as `Str.Back` has them; or a tail jump to a
callee (`Jt`), the registers a call keeps as at the entry. -/
theorem cpv_ok {X : State} {t : Nat} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpv_at cpv)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpv_at) (hP : Pc F Wl V X.cpu.gpr)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsS : ∀ i < 8, ∀ j < 2, Addr.add X.cpu.gpr.rsp i ≠ Addr.add X.cpu.gpr.rsi j)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    {cU cW cI cF : List Byte} (hU : CodeIn L 4500528#64 cU) (hU' : 0 < cU.length)
    (hW : CodeIn L 4500336#64 cW) (hW' : 0 < cW.length) (hI : CodeIn L 4501152#64 cI) (hI' : 0 < cI.length)
    (hF : CodeIn L 4553232#64 cF) (hF' : 0 < cF.length)
    (kr : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → Rv V X.cpu.gpr V' → GoG prof L o gev gP gE Z t')
    (kj : ∀ (T : Addr) (V' : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = T → Kp X.cpu.gpr Y.cpu.gpr → Jt V X.cpu.gpr T Y.cpu.gpr V' → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have r0 : rdq(Vz V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ :=
    (rdq_st fun i hi j hj => hsS i hi j (by simp only [toBytesLE_length] at hj; omega)).trans hra
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv V X.cpu.gpr ℓ m g V') (Ex V X.cpu.gpr)
    (fun ℓ m g f V' h => vcAll hP ℓ m g f V' h) ?_ 2 0 hK hA (by rw [addr_add_zero]; exact hrip)
    (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨hk, hx⟩ Y t' hKY hAY hrY hgY -
  have hkY : Kp X.cpu.gpr Y.cpu.gpr := Kp.of_eq hgY hk
  obtain ⟨rfl, h40, rfl⟩ | ⟨rfl, h72, rfl⟩ | ⟨rfl, h160, rfl⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ |
    ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩ := hx
  · exact ret_back c hin (lt_len (by decide)) (ret_40 _) hKY hAY hrY hkY hl hin₂ h₂ r0
      fun Z t₂ hKZ hAZ hrZ hbZ _ => kr _ Z t₂ hKZ hAZ hrZ hbZ (Or.inl ⟨h40, rfl⟩)
  · have r1 : rdq(Vb V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
      refine (rdq_st fun i hi j hj => hsS i hi j (by simp only [toBytesLE_length] at hj; omega)).trans ?_
      refine (rdq_st fun i hi j hj => ?_).trans r0
      simp only [toBytesLE_length] at hj
      have h := hsS i hi (1 + j) (by omega)
      rw [← addr_add_add'] at h
      exact h
    exact ret_back c hin (lt_len (by decide)) (ret_91 _) hKY hAY hrY hkY hl hin₂ h₂ r1
      fun Z t₂ hKZ hAZ hrZ hbZ _ => kr _ Z t₂ hKZ hAZ hrZ hbZ (Or.inr (Or.inl ⟨h72, rfl⟩))
  · have r2 : rdq(Vs V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ :=
      (rdq_st fun i hi j hj => hsS i hi j (by simp only [toBytesLE_length] at hj; omega)).trans r0
    exact ret_back c hin (lt_len (by decide)) (ret_168 _) hKY hAY hrY hkY hl hin₂ h₂ r2
      fun Z t₂ hKZ hAZ hrZ hbZ _ => kr _ Z t₂ hKZ hAZ hrZ hbZ (Or.inr (Or.inr ⟨h160, rfl⟩))
  · exact tj c hin (by decide) (jmp_64 _) hU hU' tgt_64 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_100 _) hW hW' tgt_100 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_116 _) hW hW' tgt_116 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_131 _) hW hW' tgt_131 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_148 _) hI hI' tgt_148 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_181 _) hI hI' tgt_181 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_198 _) hF hF' tgt_198 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_212 _) hI hI' tgt_212 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)
  · exact tj c hin (by decide) (jmp_228 _) hU hU' tgt_228 hKY hAY hrY fun Y₂ t₂ hK₂ hA₂ hr₂ hg₂ =>
        kj _ _ Y₂ t₂ hK₂ hA₂ hr₂ (Kp.of_eq hg₂ hkY) (by rw [hg₂, hgY]; exact hj)

end FV7z.Cpv
