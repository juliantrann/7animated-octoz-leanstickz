import FV7z.Rdn.Cuts
import FV7z.Lemmas.SpCallKx
import FV7z.Tun.Inv
/-!
# `CDirItems::ReserveDown` (PLAN.md §M, M1)

7-Zip 26.06's `CDirItems::ReserveDown ()` at `0x5c03e0` in `7zzs` (`CPP/7zip/UI/Common/EnumDirItems.cpp`;
`objdump -d`): `CRecordVector::ReserveDown` of the four vectors of the object `a` (`rdi`), at `a`, `a + 16`, `a + 32`,
`a + 48`, each `_items` (8 bytes), `_size` (4 at 8), `_capacity` (4 at 12), elements of 8, 4, 4, 8 bytes (`kv`, the
shift). For each: `_size` = `_capacity`: nothing; else `p` = 0 if `_size` = 0, else `p = new T[_size]` (`0x6029b0`)
and `memcpy (p, _items, _size · sizeof T)` (the PLT entry `0x401070`); `delete [] _items` (`0x6014f0`) unless `_size`
and `_items` are both 0; then `_items` = `p`, `_capacity` = `_size`. The frame: `r12`, `rbp`, `rbx` pushed; the `ret`
at 153.

The callees are hypotheses (`FnK`, with any `T` and `R`: `Cs`), and so is what their contracts give for this code
(`Hy`): a heap invariant `Hi` between the vectors, `H1` after `new`, `H2` after `memcpy` (or for a vector of size 0),
each callee keeping the registers a call keeps and the 32 bytes above its return address (`Kc`). `Hi` does not
depend on the 32 bytes below the return address.

- `Fm`: the frame (the three registers pushed, the return address) and the registers kept; `Ih`, `Fh`, `Nx`: the
  cut points' invariants with a measure, the `ret`, an exit.
- `vc_*`: the verification conditions of the pieces and the calls; `vcAll`, `spC`: all of them.
- `rdn_ok`: from the entry to the return address with `rsp` 8 up, the registers a call keeps, and `Hi`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rdn
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## The calls and the `ret` -/

def pc164 : List Byte := [0xe8, 0x27, 0x25, 0x04, 0x00]
theorem pc164_0 : ∀ feat, Dec feat pc164 0 (FV7z.mk .call 64 [.rel 271655] 5) := by dec_rfl
theorem wc164 : pc164 <+: rdn.drop 164 := by decide +kernel
theorem call_164 (feat : Features) : Dec feat rdn 164 (FV7z.mk .call 64 [.rel 271655] 5) :=
  Dec.shift (j := 164) (k := 0) (pc164_0 feat) wc164 (Nat.zero_le _)

def pc189 : List Byte := [0xe8, 0xce, 0x0b, 0xe4, 0xff]
theorem pc189_0 : ∀ feat, Dec feat pc189 0 (FV7z.mk .call 64 [.rel 18446744073707719630] 5) := by dec_rfl
theorem wc189 : pc189 <+: rdn.drop 189 := by decide +kernel
theorem call_189 (feat : Features) : Dec feat rdn 189 (FV7z.mk .call 64 [.rel 18446744073707719630] 5) :=
  Dec.shift (j := 189) (k := 0) (pc189_0 feat) wc189 (Nat.zero_le _)

def pc197 : List Byte := [0xe8, 0x46, 0x10, 0x04, 0x00]
theorem pc197_0 : ∀ feat, Dec feat pc197 0 (FV7z.mk .call 64 [.rel 266310] 5) := by dec_rfl
theorem wc197 : pc197 <+: rdn.drop 197 := by decide +kernel
theorem call_197 (feat : Features) : Dec feat rdn 197 (FV7z.mk .call 64 [.rel 266310] 5) :=
  Dec.shift (j := 197) (k := 0) (pc197_0 feat) wc197 (Nat.zero_le _)

def pc220 : List Byte := [0xe8, 0xef, 0x24, 0x04, 0x00]
theorem pc220_0 : ∀ feat, Dec feat pc220 0 (FV7z.mk .call 64 [.rel 271599] 5) := by dec_rfl
theorem wc220 : pc220 <+: rdn.drop 220 := by decide +kernel
theorem call_220 (feat : Features) : Dec feat rdn 220 (FV7z.mk .call 64 [.rel 271599] 5) :=
  Dec.shift (j := 220) (k := 0) (pc220_0 feat) wc220 (Nat.zero_le _)

def pc244 : List Byte := [0xe8, 0x97, 0x0b, 0xe4, 0xff]
theorem pc244_0 : ∀ feat, Dec feat pc244 0 (FV7z.mk .call 64 [.rel 18446744073707719575] 5) := by dec_rfl
theorem wc244 : pc244 <+: rdn.drop 244 := by decide +kernel
theorem call_244 (feat : Features) : Dec feat rdn 244 (FV7z.mk .call 64 [.rel 18446744073707719575] 5) :=
  Dec.shift (j := 244) (k := 0) (pc244_0 feat) wc244 (Nat.zero_le _)

def pc252 : List Byte := [0xe8, 0x0f, 0x10, 0x04, 0x00]
theorem pc252_0 : ∀ feat, Dec feat pc252 0 (FV7z.mk .call 64 [.rel 266255] 5) := by dec_rfl
theorem wc252 : pc252 <+: rdn.drop 252 := by decide +kernel
theorem call_252 (feat : Features) : Dec feat rdn 252 (FV7z.mk .call 64 [.rel 266255] 5) :=
  Dec.shift (j := 252) (k := 0) (pc252_0 feat) wc252 (Nat.zero_le _)

def pc276 : List Byte := [0xe8, 0xb7, 0x24, 0x04, 0x00]
theorem pc276_0 : ∀ feat, Dec feat pc276 0 (FV7z.mk .call 64 [.rel 271543] 5) := by dec_rfl
theorem wc276 : pc276 <+: rdn.drop 276 := by decide +kernel
theorem call_276 (feat : Features) : Dec feat rdn 276 (FV7z.mk .call 64 [.rel 271543] 5) :=
  Dec.shift (j := 276) (k := 0) (pc276_0 feat) wc276 (Nat.zero_le _)

def pc301 : List Byte := [0xe8, 0x5e, 0x0b, 0xe4, 0xff]
theorem pc301_0 : ∀ feat, Dec feat pc301 0 (FV7z.mk .call 64 [.rel 18446744073707719518] 5) := by dec_rfl
theorem wc301 : pc301 <+: rdn.drop 301 := by decide +kernel
theorem call_301 (feat : Features) : Dec feat rdn 301 (FV7z.mk .call 64 [.rel 18446744073707719518] 5) :=
  Dec.shift (j := 301) (k := 0) (pc301_0 feat) wc301 (Nat.zero_le _)

def pc309 : List Byte := [0xe8, 0xd6, 0x0f, 0x04, 0x00]
theorem pc309_0 : ∀ feat, Dec feat pc309 0 (FV7z.mk .call 64 [.rel 266198] 5) := by dec_rfl
theorem wc309 : pc309 <+: rdn.drop 309 := by decide +kernel
theorem call_309 (feat : Features) : Dec feat rdn 309 (FV7z.mk .call 64 [.rel 266198] 5) :=
  Dec.shift (j := 309) (k := 0) (pc309_0 feat) wc309 (Nat.zero_le _)

def pc332 : List Byte := [0xe8, 0x7f, 0x24, 0x04, 0x00]
theorem pc332_0 : ∀ feat, Dec feat pc332 0 (FV7z.mk .call 64 [.rel 271487] 5) := by dec_rfl
theorem wc332 : pc332 <+: rdn.drop 332 := by decide +kernel
theorem call_332 (feat : Features) : Dec feat rdn 332 (FV7z.mk .call 64 [.rel 271487] 5) :=
  Dec.shift (j := 332) (k := 0) (pc332_0 feat) wc332 (Nat.zero_le _)

def pc357 : List Byte := [0xe8, 0x26, 0x0b, 0xe4, 0xff]
theorem pc357_0 : ∀ feat, Dec feat pc357 0 (FV7z.mk .call 64 [.rel 18446744073707719462] 5) := by dec_rfl
theorem wc357 : pc357 <+: rdn.drop 357 := by decide +kernel
theorem call_357 (feat : Features) : Dec feat rdn 357 (FV7z.mk .call 64 [.rel 18446744073707719462] 5) :=
  Dec.shift (j := 357) (k := 0) (pc357_0 feat) wc357 (Nat.zero_le _)

def pc365 : List Byte := [0xe8, 0x9e, 0x0f, 0x04, 0x00]
theorem pc365_0 : ∀ feat, Dec feat pc365 0 (FV7z.mk .call 64 [.rel 266142] 5) := by dec_rfl
theorem wc365 : pc365 <+: rdn.drop 365 := by decide +kernel
theorem call_365 (feat : Features) : Dec feat rdn 365 (FV7z.mk .call 64 [.rel 266142] 5) :=
  Dec.shift (j := 365) (k := 0) (pc365_0 feat) wc365 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_153 : pret <+: rdn.drop 153 := by decide +kernel
theorem ret_153 (feat : Features) : Dec feat rdn 153 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 153) (k := 0) (pret_0 feat) w_153 (Nat.zero_le _)

/-! ## The object -/

/-- The `v`-th vector's `_items`. -/
def ia (a : Addr) : Nat → Addr
  | 0 => a
  | 1 => a + 16#64
  | 2 => a + 32#64
  | _ => a + 48#64
/-- Its `_size`. -/
def sa (a : Addr) : Nat → Addr
  | 0 => a + 8#64
  | 1 => a + 24#64
  | 2 => a + 40#64
  | _ => a + 56#64
/-- Its `_capacity`. -/
def ca (a : Addr) : Nat → Addr
  | 0 => a + 12#64
  | 1 => a + 28#64
  | 2 => a + 44#64
  | _ => a + 60#64
/-- The shift of its element size. -/
def kv : Nat → Nat
  | 0 => 3
  | 1 => 2
  | 2 => 2
  | _ => 3
/-- The return addresses of its calls of `new`, `memcpy`, `delete`. -/
def nwr : Nat → Nat
  | 0 => 225
  | 1 => 169
  | 2 => 337
  | _ => 281
def mcr : Nat → Nat
  | 0 => 249
  | 1 => 194
  | 2 => 362
  | _ => 306
def dlr : Nat → Nat
  | 0 => 257
  | 1 => 202
  | 2 => 370
  | _ => 314

abbrev it (a : Addr) (v : Nat) (V : Addr → Byte) : BitVec 64 := ofBytesLE 64 (List.map V (byteAddrs (ia a v) 8))
abbrev sz (a : Addr) (v : Nat) (V : Addr → Byte) : BitVec 32 := ofBytesLE 32 (List.map V (byteAddrs (sa a v) 4))
abbrev cp (a : Addr) (v : Nat) (V : Addr → Byte) : BitVec 32 := ofBytesLE 32 (List.map V (byteAddrs (ca a v) 4))

/-- The bytes after `_items` = `p`, `_capacity` = the low half of `d`. -/
def St (a : Addr) (v : Nat) (V : Addr → Byte) (p d : BitVec 64) : Addr → Byte :=
  Vst (Vst V (ia a v) (toBytesLE p 8)) (ca a v) (toBytesLE (d.setWidth 32) 4)

/-! ## The contract -/

/-- What a callee keeps: `rsp` 8 up (its return address popped), `rbx`, `rbp`, `r12`–`r15`, the 32 bytes above its
return address. -/
def Kc (g g' : Gprs) (V V' : Addr → Byte) : Prop :=
  g'.rsp = g.rsp + 8 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15 ∧ ∀ x : Addr, g.rsp.toNat + 8 ≤ x.toNat → x.toNat < g.rsp.toNat + 40 → V' x = V x

/-- The callees' contracts: `operator new []`, `memcpy`, `operator delete []`. -/
structure Cs where
  Tn : Gprs → (Addr → Byte) → Prop
  Rn : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop
  Tm : Gprs → (Addr → Byte) → Prop
  Rm : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop
  Td : Gprs → (Addr → Byte) → Prop
  Rd : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop

/-- The heap's states: between the vectors (`Hi`), after `new` with the block (`H1 v`), after `memcpy` with the block
and the old `_items` (`H2 v`). -/
structure Gh where
  Hi : (Addr → Byte) → Prop
  H1 : Nat → (Addr → Byte) → BitVec 64 → Prop
  H2 : Nat → (Addr → Byte) → BitVec 64 → BitVec 64 → Prop

/-- The bytes at a callee's entry: its return address stored. -/
abbrev Rt (V : Addr → Byte) (g : Gprs) (r : Nat) : Addr → Byte := Vst V g.rsp (toBytesLE (rdn_at.add r) 8)

/-- The frame and the object: `g₀` the registers at the entry (`rsp` at the return address, `rdi` the object). -/
structure Bd (F : Footprint) (Wl : List Rgn) (g₀ : Gprs) : Prop where
  lo : 32 ≤ g₀.rsp.toNat
  hi : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  /-- The three registers pushed and a callee's return address. -/
  sw : ∀ i < 32, Foot Wl (Addr.add (g₀.rsp - 32#64) i)
  /-- The three registers popped and the return address. -/
  sr : ∀ i < 32, Foot F.data (Addr.add (g₀.rsp - 24#64) i)
  ow : ∀ i < 64, Foot Wl (Addr.add g₀.rdi i)
  orr : ∀ i < 64, Foot F.data (Addr.add g₀.rdi i)
  oh : g₀.rdi.toNat + 64 ≤ 2 ^ 64
  od : g₀.rdi.toNat + 64 + 32 ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat

/-- What the callees' contracts give for this code (`a` = `g₀.rdi` the object). -/
structure Hy (g₀ : Gprs) (G : Gh) (C : Cs) : Prop where
  hf : ∀ V V' : Addr → Byte, G.Hi V →
    (∀ x : Addr, x.toNat + 32 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ x.toNat → V' x = V x) → G.Hi V'
  kn : ∀ g V g' V', C.Rn g V g' V' → Kc g g' V V'
  km : ∀ g V g' V', C.Rm g V g' V' → Kc g g' V V'
  kd : ∀ g V g' V', C.Rd g V g' V' → Kc g g' V V'
  nw : ∀ v < 4, ∀ (g : Gprs) (V : Addr → Byte), g.rsp = g₀.rsp - 8 - 8 - 8 - 8 → G.Hi V →
    sz g₀.rdi v V ≠ cp g₀.rdi v V → sz g₀.rdi v V ≠ 0 → g.rdi = (sz g₀.rdi v V).setWidth 64 <<< kv v →
    C.Tn g (Rt V g (nwr v)) ∧ ∀ g' V', C.Rn g (Rt V g (nwr v)) g' V' → G.H1 v V' g'.rax
  mc : ∀ v < 4, ∀ (g : Gprs) (V : Addr → Byte) (p : BitVec 64), g.rsp = g₀.rsp - 8 - 8 - 8 - 8 → G.H1 v V p →
    g.rdi = p → g.rsi = it g₀.rdi v V → g.rdx = (sz g₀.rdi v V).setWidth 64 <<< kv v →
    C.Tm g (Rt V g (mcr v)) ∧ ∀ g' V', C.Rm g (Rt V g (mcr v)) g' V' → G.H2 v V' p (it g₀.rdi v V)
  dl : ∀ v < 4, ∀ (g : Gprs) (V : Addr → Byte) (p q : BitVec 64), g.rsp = g₀.rsp - 8 - 8 - 8 - 8 →
    G.H2 v V p q → g.rdi = q →
    C.Td g (Rt V g (dlr v)) ∧ ∀ g' V', C.Rd g (Rt V g (dlr v)) g' V' →
      G.Hi (St g₀.rdi v V' p ((sz g₀.rdi v V').setWidth 64))
  /-- `_size` 0, `_items` not null: straight to `delete`. -/
  z : ∀ v < 4, ∀ V : Addr → Byte, G.Hi V → sz g₀.rdi v V = 0 → sz g₀.rdi v V ≠ cp g₀.rdi v V →
    it g₀.rdi v V ≠ 0 → G.H2 v V 0 (it g₀.rdi v V)
  /-- `_size` 0, `_items` null: only the stores. -/
  e : ∀ v < 4, ∀ V : Addr → Byte, G.Hi V → sz g₀.rdi v V = 0 → sz g₀.rdi v V ≠ cp g₀.rdi v V →
    it g₀.rdi v V = 0 → G.Hi (St g₀.rdi v V (it g₀.rdi v V) ((sz g₀.rdi v V).setWidth 64))

/-! ## The invariants -/

/-- The bytes after the three `push`es. -/
abbrev P3 (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- In the body: `rsp` below the three registers pushed, `rbx` the object, `r13`–`r15` kept, the frame and the return
address as after the `push`es. -/
def Fm (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp - 8 - 8 - 8 ∧ g.rbx = g₀.rdi ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧
    ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x

/-- The invariants of the cut points and the calls, with the measure `n`. -/
def Ih (g₀ : Gprs) (V₀ : Addr → Byte) (G : Gh) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  if ℓ = 0 then n = 100 ∧ g = g₀ ∧ V = V₀ ∧ G.Hi V else
  if ℓ = 220 then n = 98 ∧ Fm g₀ V₀ g V ∧ G.Hi V ∧ sz g₀.rdi 0 V ≠ cp g₀.rdi 0 V ∧ sz g₀.rdi 0 V ≠ 0 ∧
    g.rdi = (sz g₀.rdi 0 V).setWidth 64 <<< kv 0 else
  if ℓ = 225 then n = 97 ∧ Fm g₀ V₀ g V ∧ G.H1 0 V g.rax else
  if ℓ = 244 then n = 96 ∧ Fm g₀ V₀ g V ∧ G.H1 0 V g.rbp ∧ g.rdi = g.rbp ∧ g.rsi = g.r12 ∧
    g.r12 = it g₀.rdi 0 V ∧ g.rdx = (sz g₀.rdi 0 V).setWidth 64 <<< kv 0 else
  if ℓ = 249 then n = 95 ∧ Fm g₀ V₀ g V ∧ G.H2 0 V g.rbp g.r12 else
  if ℓ = 252 then n = 94 ∧ Fm g₀ V₀ g V ∧ G.H2 0 V g.rbp g.r12 ∧ g.rdi = g.r12 else
  if ℓ = 257 then n = 93 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 0 V g.rbp ((sz g₀.rdi 0 V).setWidth 64)) else
  if ℓ = 39 then n = 92 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 0 V g.rbp g.rdi) else
  if ℓ = 45 then n = 80 ∧ Fm g₀ V₀ g V ∧ G.Hi V else
  if ℓ = 164 then n = 78 ∧ Fm g₀ V₀ g V ∧ G.Hi V ∧ sz g₀.rdi 1 V ≠ cp g₀.rdi 1 V ∧ sz g₀.rdi 1 V ≠ 0 ∧
    g.rdi = (sz g₀.rdi 1 V).setWidth 64 <<< kv 1 else
  if ℓ = 169 then n = 77 ∧ Fm g₀ V₀ g V ∧ G.H1 1 V g.rax else
  if ℓ = 189 then n = 76 ∧ Fm g₀ V₀ g V ∧ G.H1 1 V g.rbp ∧ g.rdi = g.rbp ∧ g.rsi = g.r12 ∧
    g.r12 = it g₀.rdi 1 V ∧ g.rdx = (sz g₀.rdi 1 V).setWidth 64 <<< kv 1 else
  if ℓ = 194 then n = 75 ∧ Fm g₀ V₀ g V ∧ G.H2 1 V g.rbp g.r12 else
  if ℓ = 197 then n = 74 ∧ Fm g₀ V₀ g V ∧ G.H2 1 V g.rbp g.r12 ∧ g.rdi = g.r12 else
  if ℓ = 202 then n = 73 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 1 V g.rbp ((sz g₀.rdi 1 V).setWidth 64)) else
  if ℓ = 70 then n = 72 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 1 V g.rbp g.rdi) else
  if ℓ = 77 then n = 60 ∧ Fm g₀ V₀ g V ∧ G.Hi V else
  if ℓ = 332 then n = 58 ∧ Fm g₀ V₀ g V ∧ G.Hi V ∧ sz g₀.rdi 2 V ≠ cp g₀.rdi 2 V ∧ sz g₀.rdi 2 V ≠ 0 ∧
    g.rdi = (sz g₀.rdi 2 V).setWidth 64 <<< kv 2 else
  if ℓ = 337 then n = 57 ∧ Fm g₀ V₀ g V ∧ G.H1 2 V g.rax else
  if ℓ = 357 then n = 56 ∧ Fm g₀ V₀ g V ∧ G.H1 2 V g.rbp ∧ g.rdi = g.rbp ∧ g.rsi = g.r12 ∧
    g.r12 = it g₀.rdi 2 V ∧ g.rdx = (sz g₀.rdi 2 V).setWidth 64 <<< kv 2 else
  if ℓ = 362 then n = 55 ∧ Fm g₀ V₀ g V ∧ G.H2 2 V g.rbp g.r12 else
  if ℓ = 365 then n = 54 ∧ Fm g₀ V₀ g V ∧ G.H2 2 V g.rbp g.r12 ∧ g.rdi = g.r12 else
  if ℓ = 370 then n = 53 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 2 V g.rbp ((sz g₀.rdi 2 V).setWidth 64)) else
  if ℓ = 106 then n = 52 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 2 V g.rbp g.rdi) else
  if ℓ = 113 then n = 40 ∧ Fm g₀ V₀ g V ∧ G.Hi V else
  if ℓ = 276 then n = 38 ∧ Fm g₀ V₀ g V ∧ G.Hi V ∧ sz g₀.rdi 3 V ≠ cp g₀.rdi 3 V ∧ sz g₀.rdi 3 V ≠ 0 ∧
    g.rdi = (sz g₀.rdi 3 V).setWidth 64 <<< kv 3 else
  if ℓ = 281 then n = 37 ∧ Fm g₀ V₀ g V ∧ G.H1 3 V g.rax else
  if ℓ = 301 then n = 36 ∧ Fm g₀ V₀ g V ∧ G.H1 3 V g.rbp ∧ g.rdi = g.rbp ∧ g.rsi = g.r12 ∧
    g.r12 = it g₀.rdi 3 V ∧ g.rdx = (sz g₀.rdi 3 V).setWidth 64 <<< kv 3 else
  if ℓ = 306 then n = 35 ∧ Fm g₀ V₀ g V ∧ G.H2 3 V g.rbp g.r12 else
  if ℓ = 309 then n = 34 ∧ Fm g₀ V₀ g V ∧ G.H2 3 V g.rbp g.r12 ∧ g.rdi = g.r12 else
  if ℓ = 314 then n = 33 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 3 V g.rbp ((sz g₀.rdi 3 V).setWidth 64)) else
  if ℓ = 142 then n = 32 ∧ Fm g₀ V₀ g V ∧ G.Hi (St g₀.rdi 3 V g.rbp g.rdi) else
  if ℓ = 149 then n = 10 ∧ Fm g₀ V₀ g V ∧ G.Hi V else
  False

/-- At the `ret`: `rsp` at the return address, the registers a call keeps, the return address, `Hi`. -/
def Fh (g₀ : Gprs) (V₀ : Addr → Byte) (G : Gh) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 153 ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15 ∧ List.map V (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) ∧ G.Hi V

/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (G : Gh) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ Ih g₀ V₀ G j' n' g' V') ∨ Fh g₀ V₀ G j' g' V'

/-- What the code from a cut point needs for `Q` at the next ones; at a call, the callee's contract. -/
def WtC (F : Footprint) (Wl : List Rgn) (C : Cs) (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 164 then CallK Wl rdn_at 169 C.Tn C.Rn else
  if ℓ = 189 then CallK Wl rdn_at 194 C.Tm C.Rm else
  if ℓ = 197 then CallK Wl rdn_at 202 C.Td C.Rd else
  if ℓ = 220 then CallK Wl rdn_at 225 C.Tn C.Rn else
  if ℓ = 244 then CallK Wl rdn_at 249 C.Tm C.Rm else
  if ℓ = 252 then CallK Wl rdn_at 257 C.Td C.Rd else
  if ℓ = 276 then CallK Wl rdn_at 281 C.Tn C.Rn else
  if ℓ = 301 then CallK Wl rdn_at 306 C.Tm C.Rm else
  if ℓ = 309 then CallK Wl rdn_at 314 C.Td C.Rd else
  if ℓ = 332 then CallK Wl rdn_at 337 C.Tn C.Rn else
  if ℓ = 357 then CallK Wl rdn_at 362 C.Tm C.Rm else
  if ℓ = 365 then CallK Wl rdn_at 370 C.Td C.Rd else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat} {G : Gh} {C : Cs}

/-! ## Arithmetic -/

theorem sp8 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem sp16 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem sp24 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem sp32 (s : Addr) (h : 32 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega
theorem sm24 (s : Addr) (h : 32 ≤ s.toNat) : (s - 24#64).toNat = s.toNat - 24 := by bv_omega
theorem sm32 (s : Addr) (h : 32 ≤ s.toNat) : (s - 32#64).toNat = s.toNat - 32 := by bv_omega
theorem sp3 (s : Addr) : s - 8 - 8 - 8 + 8 + 8 + 8 = s := by simp only [BitVec.sub_add_cancel]

theorem oa (a : Addr) (d : Nat) (h : a.toNat + d < 2 ^ 64) : (a + BitVec.ofNat 64 d).toNat = a.toNat + d :=
  toNat_add_of_fits (i := d) (n := d + 1) (Nat.lt_succ_self d) (by omega)

theorem ia_t {a : Addr} (h : a.toNat + 64 ≤ 2 ^ 64) : ∀ v < 4, (ia a v).toNat = a.toNat + 16 * v
  | 0, _ => by simp [ia]
  | 1, _ => by show (a + 16#64).toNat = a.toNat + 16; exact oa a 16 (by omega)
  | 2, _ => by show (a + 32#64).toNat = a.toNat + 32; exact oa a 32 (by omega)
  | 3, _ => by show (a + 48#64).toNat = a.toNat + 48; exact oa a 48 (by omega)
  | _ + 4, hv => absurd hv (by omega)

theorem ca_t {a : Addr} (h : a.toNat + 64 ≤ 2 ^ 64) : ∀ v < 4, (ca a v).toNat = a.toNat + 16 * v + 12
  | 0, _ => by show (a + 12#64).toNat = a.toNat + 12; exact oa a 12 (by omega)
  | 1, _ => by show (a + 28#64).toNat = a.toNat + 28; exact oa a 28 (by omega)
  | 2, _ => by show (a + 44#64).toNat = a.toNat + 44; exact oa a 44 (by omega)
  | 3, _ => by show (a + 60#64).toNat = a.toNat + 60; exact oa a 60 (by omega)
  | _ + 4, hv => absurd hv (by omega)

theorem fsb {R : List Rgn} {b x : Addr} {m k n : Nat} (h : ∀ i < m, Foot R (Addr.add b i))
    (hb : b.toNat + m ≤ 2 ^ 64) (hx : x.toNat = b.toNat + k) (hk : k + n ≤ m) :
    ∀ i < n, Foot R (Addr.add x i) := by
  intro i hi
  have e : Addr.add x i = Addr.add b (k + i) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_of_fits hi (by omega), toNat_add_of_fits (by omega : k + i < m) hb]
    omega
  rw [e]
  exact h _ (by omega)

theorem rdeq {V V' : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → V' a = V a) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ <;> rw [toNat_add_of_fits hj hx] <;> omega

/-! ## The flags -/

theorem ne_dec {w : Nat} {x y : BitVec w} (h : decide (x = y) = false) : x ≠ y := by simpa using h
theorem ne_tst {w : Nat} {x : BitVec w} (h : (!(x &&& x == 0)) = true) : x ≠ 0 := by simpa using h
theorem eq_tst {w : Nat} {x : BitVec w} (h : (!(x &&& x == 0)) = false) : x = 0 := by simpa using h
theorem xz (x : BitVec 64) : (x.setWidth 32 ^^^ x.setWidth 32).setWidth 64 = 0 := by simp
theorem h2z {v : Nat} {V : Addr → Byte} {p q : BitVec 64} (h : G.H2 v V 0 q) (hp : p = 0) : G.H2 v V p q := by
  rw [hp]; exact h

/-! ## The footprint -/

theorem Bd.r (hb : Bd F Wl g₀) {d n : Nat} (hd : d < 64) (h : d + n ≤ 64) :
    ∀ i < n, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 d) i) := by
  have := hb.oh
  exact fsb hb.orr hb.oh (oa _ _ (by omega)) h
theorem Bd.r0 (hb : Bd F Wl g₀) {n : Nat} (h : n ≤ 64) : ∀ i < n, Foot F.data (Addr.add g₀.rdi i) :=
  fun i hi => hb.orr i (by omega)
theorem Bd.w (hb : Bd F Wl g₀) {d n : Nat} (hd : d < 64) (h : d + n ≤ 64) :
    ∀ i < n, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 d) i) := by
  have := hb.oh
  exact fsb hb.ow hb.oh (oa _ _ (by omega)) h
theorem Bd.w0 (hb : Bd F Wl g₀) {n : Nat} (h : n ≤ 64) : ∀ i < n, Foot Wl (Addr.add g₀.rdi i) :=
  fun i hi => hb.ow i (by omega)

theorem Bd.push1 (hb : Bd F Wl g₀) : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 24) hb.sw (by rw [sm32 _ lo]; omega) (by rw [sp8 _ lo, sm32 _ lo]; omega) (by omega)
theorem Bd.push2 (hb : Bd F Wl g₀) : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 16) hb.sw (by rw [sm32 _ lo]; omega) (by rw [sp16 _ lo, sm32 _ lo]; omega) (by omega)
theorem Bd.push3 (hb : Bd F Wl g₀) : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 8) hb.sw (by rw [sm32 _ lo]; omega) (by rw [sp24 _ lo, sm32 _ lo]; omega) (by omega)
theorem Bd.slot (hb : Bd F Wl g₀) : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 0) hb.sw (by rw [sm32 _ lo]; omega) (by rw [sp32 _ lo, sm32 _ lo]; omega) (by omega)
theorem Bd.pop1 (hb : Bd F Wl g₀) : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp - 8 - 8 - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 0) hb.sr (by rw [sm24 _ lo]; omega) (by rw [sp24 _ lo, sm24 _ lo]; omega) (by omega)
theorem Bd.pop2 (hb : Bd F Wl g₀) : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp - 8 - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 8) hb.sr (by rw [sm24 _ lo]; omega) (by rw [sp16 _ lo, sm24 _ lo]; omega) (by omega)
theorem Bd.pop3 (hb : Bd F Wl g₀) : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp - 8) i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 16) hb.sr (by rw [sm24 _ lo]; omega) (by rw [sp8 _ lo, sm24 _ lo]; omega) (by omega)
theorem Bd.ret (hb : Bd F Wl g₀) : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i) := by
  have lo := hb.lo
  have hi := hb.hi
  exact fsb (k := 24) hb.sr (by rw [sm24 _ lo]; omega) (by rw [sm24 _ lo]; omega) (by omega)

/-! ## The frame -/

/-- The three `push`es change only the 24 bytes below the return address. -/
theorem p3_out (hb : Bd F Wl g₀) :
    ∀ x : Addr, x.toNat + 32 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ x.toNat → P3 g₀ V₀ x = V₀ x := by
  intro x hx
  have lo := hb.lo
  have hi := hb.hi
  have e1 := sp8 _ lo
  have e2 := sp16 _ lo
  have e3 := sp24 _ lo
  unfold P3
  rw [Tun.Vst_out _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) x (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega),
    Tun.Vst_out _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) x (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega),
    Tun.Vst_out V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8) x (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega)]

/-- The stores into the object keep the frame. -/
theorem fm_st (hb : Bd F Wl g₀) {v : Nat} (hv : v < 4)
    (hk : ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x)
    (p d : BitVec 64) :
    ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → St g₀.rdi v V p d x = P3 g₀ V₀ x := by
  intro x h1 h2
  have e1 := ia_t hb.oh v hv
  have e2 := ca_t hb.oh v hv
  have hod := hb.od
  have lo := hb.lo
  have hoh := hb.oh
  unfold St
  rw [Tun.Vst_out _ (ca g₀.rdi v) (toBytesLE (d.setWidth 32) 4) x (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega),
    Tun.Vst_out V (ia g₀.rdi v) (toBytesLE p 8) x (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega)]
  exact hk x h1 h2

theorem fr_rbx (hb : Bd F Wl g₀)
    (hk : ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x) :
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8 - 8 - 8) 8)) = g₀.rbx := by
  have lo := hb.lo
  have hi := hb.hi
  have e3 := sp24 _ lo
  rw [rdeq (V := P3 g₀ V₀) (x := g₀.rsp - 8 - 8 - 8) (n := 8) (by omega)
    fun a h1 h2 => hk a (by omega) (by omega)]
  unfold P3
  rw [Tun.rd_Vst_self _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem fr_rbp (hb : Bd F Wl g₀)
    (hk : ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x) :
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8 - 8) 8)) = g₀.rbp := by
  have lo := hb.lo
  have hi := hb.hi
  have e2 := sp16 _ lo
  have e3 := sp24 _ lo
  rw [rdeq (V := P3 g₀ V₀) (x := g₀.rsp - 8 - 8) (n := 8) (by omega)
    fun a h1 h2 => hk a (by omega) (by omega)]
  unfold P3
  rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) (g₀.rsp - 8 - 8) 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst_self _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem fr_r12 (hb : Bd F Wl g₀)
    (hk : ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x) :
    ofBytesLE 64 (List.map V (byteAddrs (g₀.rsp - 8) 8)) = g₀.r12 := by
  have lo := hb.lo
  have hi := hb.hi
  have e1 := sp8 _ lo
  have e2 := sp16 _ lo
  have e3 := sp24 _ lo
  rw [rdeq (V := P3 g₀ V₀) (x := g₀.rsp - 8) (n := 8) (by omega) fun a h1 h2 => hk a (by omega) (by omega)]
  unfold P3
  rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) (g₀.rsp - 8) 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) (g₀.rsp - 8) 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst_self _ (g₀.rsp - 8) (toBytesLE g₀.r12 8) (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem fr_ret (hb : Bd F Wl g₀)
    (hk : ∀ x : Addr, g₀.rsp.toNat - 24 ≤ x.toNat → x.toNat < g₀.rsp.toNat + 8 → V x = P3 g₀ V₀ x) :
    List.map V (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) := by
  have lo := hb.lo
  have hi := hb.hi
  have e1 := sp8 _ lo
  have e2 := sp16 _ lo
  have e3 := sp24 _ lo
  rw [rdeq (V := P3 g₀ V₀) (x := g₀.rsp) (n := 8) (by omega) fun a h1 h2 => hk a (by omega) (by omega)]
  unfold P3
  rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) g₀.rsp 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) g₀.rsp 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8) g₀.rsp 8 (by rw [toBytesLE_length]; omega)
      (by omega) (by rw [toBytesLE_length]; omega)]

/-! ## The calls -/

/-- A call from the body, to the instruction after it: the callee keeps the frame and the registers. -/
theorem vc_call (hb : Bd F Wl g₀) {T : Gprs → (Addr → Byte) → Prop}
    {R : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop} (kR : ∀ g V g' V', R g V g' V' → Kc g g' V V')
    {jn : Nat} {Q : Post} (hF : Fm g₀ V₀ g V)
    (hT : T (g.set 4 (g.rsp - 8)) (Vst V (g.rsp - 8) (toBytesLE (rdn_at.add jn) 8)))
    (hQ : ∀ g' V', R (g.set 4 (g.rsp - 8)) (Vst V (g.rsp - 8) (toBytesLE (rdn_at.add jn) 8)) g' V' →
      Fm g₀ V₀ g' V' → g'.rbp = g.rbp → g'.r12 = g.r12 → ∀ fl, Q jn g' fl V') :
    CallK Wl rdn_at jn T R Q g f V := by
  have lo := hb.lo
  have hi := hb.hi
  have e4 := sp32 _ lo
  obtain ⟨hs, hbx, h13, h14, h15, hk⟩ := hF
  refine ⟨by rw [hs]; exact hb.slot, by rw [hs]; omega, hT, fun g' V' hR fl => ?_⟩
  obtain ⟨hs', hbx', hbp', h12', h13', h14', h15', hk'⟩ := kR _ _ _ _ hR
  refine hQ g' V' hR ⟨?_, hbx'.trans hbx, h13'.trans h13, h14'.trans h14, h15'.trans h15, fun x h1 h2 => ?_⟩
    hbp' h12' fl
  · rw [hs']
    show g.rsp - 8 + 8 = _
    rw [BitVec.sub_add_cancel, hs]
  · have hx1 : (g.rsp - 8).toNat + 8 ≤ x.toNat := by rw [hs]; omega
    have hx2 : x.toNat < (g.rsp - 8).toNat + 40 := by rw [hs]; omega
    rw [hk' x hx1 hx2, Tun.Vst_out V (g.rsp - 8) (toBytesLE (rdn_at.add jn) 8) x
      (by rw [toBytesLE_length, hs]; omega) (Or.inr (by rw [toBytesLE_length]; exact hx1))]
    exact hk x h1 h2

/-! ## The verification conditions -/

theorem vc_220 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 220 n g V) :
    CallK Wl rdn_at 225 C.Tn C.Rn (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hne, hn0, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.nw 0 (by decide) (g.set 4 (g.rsp - 8)) V (by show g.rsp - 8 = _; rw [hF.1]) hH hne hn0 hdi
  exact vc_call hb hy.kn hF hT fun g' V' hR' hF' _ _ _ => Or.inl ⟨_, by decide, rfl, hF', hR g' V' hR'⟩

theorem vc_244 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 244 n g V) :
    CallK Wl rdn_at 249 C.Tm C.Rm (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi, hsi, h12, hdx⟩ := h
  obtain ⟨hT, hR⟩ := hy.mc 0 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp (by show g.rsp - 8 = _; rw [hF.1]) hH hdi
    (hsi.trans h12) hdx
  exact vc_call hb hy.km hF hT fun g' V' hR' hF' hp hq _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp, hq, h12]; exact hR g' V' hR'⟩

theorem vc_252 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 252 n g V) :
    CallK Wl rdn_at 257 C.Td C.Rd (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.dl 0 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp g.r12 (by show g.rsp - 8 = _; rw [hF.1]) hH
    hdi
  exact vc_call hb hy.kd hF hT fun g' V' hR' hF' hp _ _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp]; exact hR g' V' hR'⟩

theorem vc_164 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 164 n g V) :
    CallK Wl rdn_at 169 C.Tn C.Rn (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hne, hn0, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.nw 1 (by decide) (g.set 4 (g.rsp - 8)) V (by show g.rsp - 8 = _; rw [hF.1]) hH hne hn0 hdi
  exact vc_call hb hy.kn hF hT fun g' V' hR' hF' _ _ _ => Or.inl ⟨_, by decide, rfl, hF', hR g' V' hR'⟩

theorem vc_189 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 189 n g V) :
    CallK Wl rdn_at 194 C.Tm C.Rm (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi, hsi, h12, hdx⟩ := h
  obtain ⟨hT, hR⟩ := hy.mc 1 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp (by show g.rsp - 8 = _; rw [hF.1]) hH hdi
    (hsi.trans h12) hdx
  exact vc_call hb hy.km hF hT fun g' V' hR' hF' hp hq _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp, hq, h12]; exact hR g' V' hR'⟩

theorem vc_197 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 197 n g V) :
    CallK Wl rdn_at 202 C.Td C.Rd (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.dl 1 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp g.r12 (by show g.rsp - 8 = _; rw [hF.1]) hH
    hdi
  exact vc_call hb hy.kd hF hT fun g' V' hR' hF' hp _ _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp]; exact hR g' V' hR'⟩

theorem vc_332 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 332 n g V) :
    CallK Wl rdn_at 337 C.Tn C.Rn (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hne, hn0, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.nw 2 (by decide) (g.set 4 (g.rsp - 8)) V (by show g.rsp - 8 = _; rw [hF.1]) hH hne hn0 hdi
  exact vc_call hb hy.kn hF hT fun g' V' hR' hF' _ _ _ => Or.inl ⟨_, by decide, rfl, hF', hR g' V' hR'⟩

theorem vc_357 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 357 n g V) :
    CallK Wl rdn_at 362 C.Tm C.Rm (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi, hsi, h12, hdx⟩ := h
  obtain ⟨hT, hR⟩ := hy.mc 2 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp (by show g.rsp - 8 = _; rw [hF.1]) hH hdi
    (hsi.trans h12) hdx
  exact vc_call hb hy.km hF hT fun g' V' hR' hF' hp hq _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp, hq, h12]; exact hR g' V' hR'⟩

theorem vc_365 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 365 n g V) :
    CallK Wl rdn_at 370 C.Td C.Rd (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.dl 2 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp g.r12 (by show g.rsp - 8 = _; rw [hF.1]) hH
    hdi
  exact vc_call hb hy.kd hF hT fun g' V' hR' hF' hp _ _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp]; exact hR g' V' hR'⟩

theorem vc_276 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 276 n g V) :
    CallK Wl rdn_at 281 C.Tn C.Rn (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hne, hn0, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.nw 3 (by decide) (g.set 4 (g.rsp - 8)) V (by show g.rsp - 8 = _; rw [hF.1]) hH hne hn0 hdi
  exact vc_call hb hy.kn hF hT fun g' V' hR' hF' _ _ _ => Or.inl ⟨_, by decide, rfl, hF', hR g' V' hR'⟩

theorem vc_301 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 301 n g V) :
    CallK Wl rdn_at 306 C.Tm C.Rm (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi, hsi, h12, hdx⟩ := h
  obtain ⟨hT, hR⟩ := hy.mc 3 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp (by show g.rsp - 8 = _; rw [hF.1]) hH hdi
    (hsi.trans h12) hdx
  exact vc_call hb hy.km hF hT fun g' V' hR' hF' hp hq _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp, hq, h12]; exact hR g' V' hR'⟩

theorem vc_309 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 309 n g V) :
    CallK Wl rdn_at 314 C.Td C.Rd (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hF, hH, hdi⟩ := h
  obtain ⟨hT, hR⟩ := hy.dl 3 (by decide) (g.set 4 (g.rsp - 8)) V g.rbp g.r12 (by show g.rsp - 8 = _; rw [hF.1]) hH
    hdi
  exact vc_call hb hy.kd hF hT fun g' V' hR' hF' hp _ _ =>
    Or.inl ⟨_, by decide, rfl, hF', by rw [hp]; exact hR g' V' hR'⟩

/-- The entry: the three `push`es, then vector 0's test, to 45, 220, 249 or 39. -/
theorem vc_0 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 0 n g V) : W_0 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, hg, hV, hH⟩ := h
  subst g V
  have hH0 : G.Hi (P3 g₀ V₀) := hy.hf V₀ _ hH (p3_out hb)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  wpx [W_0, W_19, W_216, W_27, W_400, o0, o1, o18, o2, o25, Op.shl64]
  all_goals repeat' (first
    | exact hb.push1
    | exact hb.push2
    | exact hb.push3
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, hH0, ne_dec ‹_›, ne_tst ‹_›, rfl⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩,
        h2z (hy.z 0 (by decide) _ hH0 (eq_tst ‹_›) (ne_dec ‹_›) (ne_tst ‹_›)) (xz _)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩,
        hy.e 0 (by decide) _ hH0 (eq_tst ‹_›) (ne_dec ‹_›) (eq_tst ‹_›)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, hH0⟩
    | apply And.intro
    | intro _)

/-- Vector 1's test: to the next vector, `new`, `delete`, or the stores. -/
theorem vc_45 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 45 n g V) :
    W_45 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_45, W_53, W_160, W_57, W_416, o4, o1, o14, o5, o25, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, ne_dec ‹_›, ne_tst ‹_›, rfl⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        h2z (hy.z 1 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (ne_tst ‹_›)) (xz _)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        hy.e 1 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (eq_tst ‹_›)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

/-- Vector 2's test: to the next vector, `new`, `delete`, or the stores. -/
theorem vc_77 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 77 n g V) :
    W_77 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_77, W_85, W_328, W_93, W_432, o7, o1, o14, o8, o25, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, ne_dec ‹_›, ne_tst ‹_›, rfl⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        h2z (hy.z 2 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (ne_tst ‹_›)) (xz _)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        hy.e 2 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (eq_tst ‹_›)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

/-- Vector 3's test: to the next vector, `new`, `delete`, or the stores. -/
theorem vc_113 (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (h : Ih g₀ V₀ G 113 n g V) :
    W_113 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_113, W_121, W_272, W_129, W_384, o10, o1, o18, o11, o25, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, ne_dec ‹_›, ne_tst ‹_›, rfl⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        h2z (hy.z 3 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (ne_tst ‹_›)) (xz _)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩,
        hy.e 3 (by decide) _ hH (eq_tst ‹_›) (ne_dec ‹_›) (eq_tst ‹_›)⟩
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_225 (h : Ih g₀ V₀ G 225 n g V) (hb : Bd F Wl g₀) :
    W_225 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_225, o19, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl, rfl, rfl, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_249 (h : Ih g₀ V₀ G 249 n g V) : W_249 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_249, o16]
  all_goals repeat' (first
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_257 (h : Ih g₀ V₀ G 257 n g V) (hb : Bd F Wl g₀) :
    W_257 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_257, o20]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_39 (h : Ih g₀ V₀ G 39 n g V) (hb : Bd F Wl g₀) :
    W_39 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_39, o3]
  all_goals repeat' (first
    | exact hb.w (by decide) (by decide)
    | exact hb.w0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fm_st hb (v := 0) (by decide) hk _ _⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_169 (h : Ih g₀ V₀ G 169 n g V) (hb : Bd F Wl g₀) :
    W_169 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_169, o15, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl, rfl, rfl, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_194 (h : Ih g₀ V₀ G 194 n g V) : W_194 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_194, o16]
  all_goals repeat' (first
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_202 (h : Ih g₀ V₀ G 202 n g V) (hb : Bd F Wl g₀) :
    W_202 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_202, o17]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_70 (h : Ih g₀ V₀ G 70 n g V) (hb : Bd F Wl g₀) :
    W_70 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_70, o6]
  all_goals repeat' (first
    | exact hb.w (by decide) (by decide)
    | exact hb.w0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fm_st hb (v := 1) (by decide) hk _ _⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_337 (h : Ih g₀ V₀ G 337 n g V) (hb : Bd F Wl g₀) :
    W_337 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_337, o23, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl, rfl, rfl, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_362 (h : Ih g₀ V₀ G 362 n g V) : W_362 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_362, o16]
  all_goals repeat' (first
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_370 (h : Ih g₀ V₀ G 370 n g V) (hb : Bd F Wl g₀) :
    W_370 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_370, o24]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_106 (h : Ih g₀ V₀ G 106 n g V) (hb : Bd F Wl g₀) :
    W_106 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_106, o9]
  all_goals repeat' (first
    | exact hb.w (by decide) (by decide)
    | exact hb.w0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fm_st hb (v := 2) (by decide) hk _ _⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_281 (h : Ih g₀ V₀ G 281 n g V) (hb : Bd F Wl g₀) :
    W_281 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_281, o21, Op.shl64]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl, rfl, rfl, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_306 (h : Ih g₀ V₀ G 306 n g V) : W_306 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_306, o16]
  all_goals repeat' (first
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH, rfl⟩
    | apply And.intro
    | intro _)

theorem vc_314 (h : Ih g₀ V₀ G 314 n g V) (hb : Bd F Wl g₀) :
    W_314 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_314, o22]
  all_goals repeat' (first
    | exact hb.r (by decide) (by decide)
    | exact hb.r0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hk⟩, hH⟩
    | apply And.intro
    | intro _)

theorem vc_142 (h : Ih g₀ V₀ G 142 n g V) (hb : Bd F Wl g₀) :
    W_142 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_142, o12]
  all_goals repeat' (first
    | exact hb.w (by decide) (by decide)
    | exact hb.w0 (by decide)
    | exact Or.inl ⟨_, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, fm_st hb (v := 3) (by decide) hk _ _⟩, hH⟩
    | apply And.intro
    | intro _)

/-- The `pop`s, to the `ret`. -/
theorem vc_149 (h : Ih g₀ V₀ G 149 n g V) (hb : Bd F Wl g₀) : W_149 F Wl (Nx g₀ V₀ G n) g f V := by
  obtain ⟨rfl, ⟨hsp, hbx, h13, h14, h15, hk⟩, hH⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only at hsp hbx h13 h14 h15
  subst hsp hbx h13 h14 h15
  wpx [W_149, o13, BitVec.sub_add_cancel]
  all_goals repeat' (first
    | exact hb.pop1
    | exact hb.pop2
    | exact hb.pop3
    | exact Or.inr ⟨rfl, rfl, fr_rbx hb hk, fr_rbp hb hk, fr_r12 hb hk, rfl, rfl, rfl, fr_ret hb hk, hH⟩
    | exact Or.inr ⟨rfl, sp3 _, fr_rbx hb hk, fr_rbp hb hk, fr_r12 hb hk, rfl, rfl, rfl, fr_ret hb hk, hH⟩
    | apply And.intro
    | intro _)

theorem vcAll (hb : Bd F Wl g₀) (hy : Hy g₀ G C) (ℓ : Nat) :
    ∀ n g f V, Ih g₀ V₀ G ℓ n g V → WtC F Wl C ℓ (Nx g₀ V₀ G n) g f V := by
  intro n g f V h
  by_cases h0 : ℓ = 0
  · subst h0; exact vc_0 hb hy h
  by_cases h220 : ℓ = 220
  · subst h220; exact vc_220 hb hy h
  by_cases h225 : ℓ = 225
  · subst h225; exact vc_225 h hb
  by_cases h244 : ℓ = 244
  · subst h244; exact vc_244 hb hy h
  by_cases h249 : ℓ = 249
  · subst h249; exact vc_249 h
  by_cases h252 : ℓ = 252
  · subst h252; exact vc_252 hb hy h
  by_cases h257 : ℓ = 257
  · subst h257; exact vc_257 h hb
  by_cases h39 : ℓ = 39
  · subst h39; exact vc_39 h hb
  by_cases h45 : ℓ = 45
  · subst h45; exact vc_45 hb hy h
  by_cases h164 : ℓ = 164
  · subst h164; exact vc_164 hb hy h
  by_cases h169 : ℓ = 169
  · subst h169; exact vc_169 h hb
  by_cases h189 : ℓ = 189
  · subst h189; exact vc_189 hb hy h
  by_cases h194 : ℓ = 194
  · subst h194; exact vc_194 h
  by_cases h197 : ℓ = 197
  · subst h197; exact vc_197 hb hy h
  by_cases h202 : ℓ = 202
  · subst h202; exact vc_202 h hb
  by_cases h70 : ℓ = 70
  · subst h70; exact vc_70 h hb
  by_cases h77 : ℓ = 77
  · subst h77; exact vc_77 hb hy h
  by_cases h332 : ℓ = 332
  · subst h332; exact vc_332 hb hy h
  by_cases h337 : ℓ = 337
  · subst h337; exact vc_337 h hb
  by_cases h357 : ℓ = 357
  · subst h357; exact vc_357 hb hy h
  by_cases h362 : ℓ = 362
  · subst h362; exact vc_362 h
  by_cases h365 : ℓ = 365
  · subst h365; exact vc_365 hb hy h
  by_cases h370 : ℓ = 370
  · subst h370; exact vc_370 h hb
  by_cases h106 : ℓ = 106
  · subst h106; exact vc_106 h hb
  by_cases h113 : ℓ = 113
  · subst h113; exact vc_113 hb hy h
  by_cases h276 : ℓ = 276
  · subst h276; exact vc_276 hb hy h
  by_cases h281 : ℓ = 281
  · subst h281; exact vc_281 h hb
  by_cases h301 : ℓ = 301
  · subst h301; exact vc_301 hb hy h
  by_cases h306 : ℓ = 306
  · subst h306; exact vc_306 h
  by_cases h309 : ℓ = 309
  · subst h309; exact vc_309 hb hy h
  by_cases h314 : ℓ = 314
  · subst h314; exact vc_314 h hb
  by_cases h142 : ℓ = 142
  · subst h142; exact vc_142 h hb
  by_cases h149 : ℓ = 149
  · subst h149; exact vc_149 h hb
  · simp only [Ih, h0, h220, h225, h244, h249, h252, h257, h39, h45, h164, h169, h189, h194, h197,
      h202, h70, h77, h332, h337, h357, h362, h365, h370, h106, h113, h276, h281, h301,
      h306, h309, h314, h142, h149, ↓reduceIte] at h

/-- The cut points' pieces and the calls in a run with the code and the callees. -/
theorem spC (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rdn_at rdn)
    {eN : Addr} {cN : List Byte} {jN : Nat} (hinN : CodeIn L eN cN) (hjN : jN < cN.length)
    (heN : eN.add jN = 0x6029b0#64) {cM : List Byte} (hinM : CodeIn L 0x401070#64 cM) (hM : 0 < cM.length)
    {cD : List Byte} (hinD : CodeIn L 0x6014f0#64 cD) (hD : 0 < cD.length)
    (fN : FnK prof F Wl L s₀ o 0x6029b0#64 C.Tn C.Rn) (fM : FnK prof F Wl L s₀ o 0x401070#64 C.Tm C.Rm)
    (fD : FnK prof F Wl L s₀ o 0x6014f0#64 C.Td C.Rd) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o rdn_at ℓ (WtC F Wl C ℓ) := by
  unfold WtC
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_164 _) hinN hjN (by rw [heN]; decide) heN fN
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_189 _) hinM hM (by decide) fM
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_197 _) hinD hD (by decide) fD
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_220 _) hinN hjN (by rw [heN]; decide) heN fN
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_244 _) hinM hM (by decide) fM
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_252 _) hinD hD (by decide) fD
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_276 _) hinN hjN (by rw [heN]; decide) heN fN
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_301 _) hinM hM (by decide) fM
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_309 _) hinD hD (by decide) fD
  split
  · subst ℓ
    exact SpAt.callKx c hin (lt_len (by decide)) (call_332 _) hinN hjN (by rw [heN]; decide) heN fN
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_357 _) hinM hM (by decide) fM
  split
  · subst ℓ
    exact SpAt.callK c hin (lt_len (by decide)) (call_365 _) hinD hD (by decide) fD
  exact (spAll prof ℓ).at c hin

variable {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `CDirItems::ReserveDown ()` from its entry, the object in `rdi`, with `operator new []`, `memcpy`,
`operator delete []` as `FnK`s and what their contracts give (`Hy`): to the return address with `rsp` 8 up, `rbx`,
`rbp`, `r12`–`r15` as at the entry, and `Hi`. -/
theorem rdn_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rdn_at rdn)
    {eN : Addr} {cN : List Byte} {jN : Nat} (hinN : CodeIn L eN cN) (hjN : jN < cN.length)
    (heN : eN.add jN = 0x6029b0#64) {cM : List Byte} (hinM : CodeIn L 0x401070#64 cM) (hM : 0 < cM.length)
    {cD : List Byte} (hinD : CodeIn L 0x6014f0#64 cD) (hD : 0 < cD.length)
    (fN : FnK prof F Wl L s₀ o 0x6029b0#64 C.Tn C.Rn) (fM : FnK prof F Wl L s₀ o 0x401070#64 C.Tm C.Rm)
    (fD : FnK prof F Wl L s₀ o 0x6014f0#64 C.Td C.Rd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rdn_at)
    (hb : Bd F Wl X.cpu.gpr) (hy : Hy X.cpu.gpr G C) (hH : G.Hi V)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 (List.map V (byteAddrs X.cpu.gpr.rsp 8)) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → G.Hi V' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cfgAt (spC c hin hinN hjN heN hinM hM hinD hD fN fM fD)
    (fun ℓ n g _ V' => Ih X.cpu.gpr V G ℓ n g V') (fun j g _ V' => Fh X.cpu.gpr V G j g V')
    (fun ℓ n g f V' h => vcAll hb hy ℓ n g f V' h) ?_ 100 0 hK hA (by rw [addr_add_zero]; exact hrip)
    ⟨rfl, rfl, rfl, hH⟩
  intro j g fl V' hF Y t' hKY hAY hrY hg _
  obtain ⟨rfl, hs, hbx, hbp, h12, h13, h14, h15, hV, hH'⟩ := hF
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by rw [hg, hs]; exact hb.ret
  have hra' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hg, hs, hV]; exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_153 _) hl hin₂ h₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hg] at hgZ
  exact k Z t₂ V' hKZ hAZ hrZ (by rw [hgZ]; show g.rsp + 8 = _; rw [hs]) (by rw [hgZ]; exact hbx)
    (by rw [hgZ]; exact hbp) (by rw [hgZ]; exact h12) (by rw [hgZ]; exact h13) (by rw [hgZ]; exact h14)
    (by rw [hgZ]; exact h15) hH'

end FV7z.Rdn

