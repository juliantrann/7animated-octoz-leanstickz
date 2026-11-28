import FV7z.Guv.Cuts
import FV7z.Pvd.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.FnJt
import FV7z.Tun.Inv
import FV7z.Hca.Holds
/-!
# `GetUInt64Value` (PLAN.md §M, M1)

7-Zip 26.06's `GetUInt64Value (archive, index, propID, value)` at `0x5ebcd0` in `7zzs`
(`CPP/7zip/UI/Console/List.cpp`, static), `S` the stack pointer at the entry: `r12`, `rbp`, `rbx` pushed, `rbx` =
`value` (`rcx`, a `CListUInt64Def`: the 8 bytes `Val`, the byte `Def` at `value + 8`), a frame of 32 bytes (`gq S`)
with the stack guard (`fs:0x28`) at `gq S + 24`, `Val` = 0, `Def` = 0, the `PROPVARIANT prop` at `gq S` cleared
(`vt`, the 4 bytes at `gq S`, and the 8 bytes at `gq S + 8`), then `archive->GetProperty (index, propID, &prop)`
(`call qword [rax + 0x30]` at 63 through the vtable, `rcx` = `rbp` = `&prop`). Back at 66: `res` (`eax`) into
`r12d`; when it is 0, `ConvertPropVariantToUInt64 (prop, Val)` inlined: `prop.vt` (the 2 bytes at `rsp`) above
`VT_UI8` (21, the `ja` at 125) or by the jump table at `0x6ea208` (22 entries, `guv_cases`) to the throw stub at
`0x419b70` (`throw 151199`), or to `VT_UI8` (160), `VT_UI4` (184), `VT_UI2` (208), `VT_UI1` (224): `Val` = the 8,
4, 2, 1 bytes at `rsp + 8` zero-extended and `Def` = 1 (173), or `VT_EMPTY` (240): `Def` = 0. Then (73)
`prop.~CPropVariant ()` (`call` at 76 to `Pvd.pvd_at`, `rdi` = `&prop`), the stack guard checked (81), the frame
dropped, `eax` = `r12d`, the registers popped and `ret` (112).

The callees are hypotheses, as in `FV7z/Gbp/Holds.lean`: continuations at their entries (`kf1`, `kf2`), each given
the run from its return to the next piece, and the throw stub one at its entry (`kth`). `P1`, `P2` are what the
callees leave; `GetProperty` leaves the jump table's bytes as they are.

- `gq`: the frame; `Vp`, `Vg`, `VC`: the bytes after the pushes, after the stack guard's store, at the first `call`;
  `gC`: the registers at the first `call`.
- `vtw V a`: the 2 bytes at `a`; `uv`: `Val` by the case; `gV`: the bytes at 73.
- `jt_*`, `tg`, `cs_cls`: the jump table.
- `vc_*`: the verification conditions of the pieces; `guv_mid`: from 66 to 73 or the throw stub.
- `guv_ok`: from the entry, through both callees, to the return address with `eax` = `res`'s low 32 bits and `rbx`,
  `rbp`, `r12`, `rsp` restored (`kr`), or to the throw stub (`kth`).

Not covered: the stack guard failing (`__stack_chk_fail`, 244).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Guv

/-- The `call qword [rax + 0x30]` (`IInArchive::GetProperty`). -/
def pcm : List Byte := [0xff, 0x50, 0x30]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) := by dec_rfl
theorem wm_63 : pcm <+: guv.drop 63 := by decide +kernel
theorem call_63 (feat : Features) : Dec feat guv 63 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) :=
  Dec.shift (j := 63) (k := 0) (pcm_0 feat) wm_63 (Nat.zero_le _)

/-- The `call` to `CPropVariant::~CPropVariant`. -/
def pcall : List Byte := [0xe8, 0x3f, 0xb2, 0xe6, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073707893311] 5) := by dec_rfl
theorem wc_76 : pcall <+: guv.drop 76 := by decide +kernel
theorem call_76 (feat : Features) : Dec feat guv 76 (FV7z.mk .call 64 [.rel 18446744073707893311] 5) :=
  Dec.shift (j := 76) (k := 0) (pcall_0 feat) wc_76 (Nat.zero_le _)
theorem tgt_76 : guv_at.add (76 + 5) + BitVec.ofNat 64 18446744073707893311 = Pvd.pvd_at := by decide

/-- The `ja` to the throw stub. -/
def pja : List Byte := [0x0f, 0x87, 0x1d, 0xde, 0xe2, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073707642397] 6) := by dec_rfl
theorem wj_125 : pja <+: guv.drop 125 := by decide +kernel
theorem ja_125 (feat : Features) : Dec feat guv 125 (FV7z.mk (.jcc 7) 64 [.rel 18446744073707642397] 6) :=
  Dec.shift (j := 125) (k := 0) (pja_0 feat) wj_125 (Nat.zero_le _)
theorem tgt_125 : guv_at.add (125 + 6) + BitVec.ofNat 64 18446744073707642397 = Addr.add (0x419b70#64) 0 := by
  decide

/-- The `notrack jmp rax` of the jump table. -/
theorem jmp_149 (feat : Features) : Dec feat guv 149 (FV7z.mk .jmp 64 [gr 64 0] 3) :=
  Dec.shift (j2_0 feat) wj_149 (by decide)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_112 : pret <+: guv.drop 112 := by decide +kernel
theorem ret_112 (feat : Features) : Dec feat guv 112 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 112) (k := 0) (pret_0 feat) w_112 (Nat.zero_le _)

/-- From 131 to the `jmp` at 149: `movzx eax, word [rsp]`, the table's entry, its target in `rax`. -/
def W_131s : Wpt := fun F Wl Q => wp F Wl o6 (Q 149)
theorem c_131s (prof : Profile) (fb : Addr) : SpF prof guv guv_at fb 131 W_131s :=
  SpF.blkA_then (blk_131 prof) (SpF.skip 149)

/-- The frame: `rsp` after the three pushes and `sub rsp, 0x20`. -/
abbrev gq (S : Addr) : Addr := S - 8 - 8 - 8 - 32#64

/-- The bytes after the pushes of `r12`, `rbp`, `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The bytes after the stack guard `cn` is stored at `gq S + 24`. -/
abbrev Vg (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vp V g) (gq g.rsp + 24#64) (toBytesLE cn 8)

/-- The bytes at the first `call`: `Val` = 0, `Def` = 0, `prop` cleared. -/
abbrev VC (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vg V g cn) g.rcx (toBytesLE 0#64 8)) (g.rcx + 8#64) (toBytesLE 0#8 1)) (gq g.rsp)
    (toBytesLE 0#32 4)) (gq g.rsp + 8#64) (toBytesLE 0#64 8)

/-- The registers at the first `call`: `rax` the vtable `vt`, `rcx` = `rbp` = `rsp` = `&prop`, `rbx` = `value`. -/
abbrev gC (g : Gprs) (vt : BitVec 64) : Gprs :=
  { g with
      rax := vt,
      rcx := gq g.rsp,
      rbx := g.rcx,
      rbp := gq g.rsp,
      rsp := gq g.rsp }

/-- The low 32 bits, zero-extended. -/
abbrev zl (a : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 a)

/-- The 2 bytes at `a`. -/
abbrev vtw (V : Addr → Byte) (a : Addr) : BitVec 16 := ofBytesLE 16 ((byteAddrs a 2).map V)

/-- The `n` bytes of `prop`'s value, at `S + 8`. -/
abbrev pv (V : Addr → Byte) (S : Addr) (n : Nat) : List Byte := (byteAddrs (S + 8#64) n).map V

/-- `Val` by the case `c`: the 8, 4, 2 or 1 bytes of `prop`'s value, zero-extended. -/
def uv (V : Addr → Byte) (S : Addr) (c : Nat) : BitVec 64 :=
  if c = 160 then ofBytesLE 64 (pv V S 8)
  else if c = 184 then (ofBytesLE 32 (pv V S 4)).setWidth 64
  else if c = 208 then ((ofBytesLE 16 (pv V S 2)).setWidth 32).setWidth 64
  else ((ofBytesLE 8 (pv V S 1)).setWidth 32).setWidth 64

theorem uv_160 (V : Addr → Byte) (S : Addr) : uv V S 160 = ofBytesLE 64 ((byteAddrs (S + 8#64) 8).map V) := by
  unfold uv
  rw [if_pos rfl]

theorem uv_184 (V : Addr → Byte) (S : Addr) :
    uv V S 184 = (ofBytesLE 32 ((byteAddrs (S + 8#64) 4).map V)).setWidth 64 := by
  unfold uv
  rw [if_neg (show (184 : Nat) ≠ 160 by decide), if_pos rfl]

theorem uv_208 (V : Addr → Byte) (S : Addr) :
    uv V S 208 = ((ofBytesLE 16 ((byteAddrs (S + 8#64) 2).map V)).setWidth 32).setWidth 64 := by
  unfold uv
  rw [if_neg (show (208 : Nat) ≠ 160 by decide), if_neg (show (208 : Nat) ≠ 184 by decide), if_pos rfl]

theorem uv_224 (V : Addr → Byte) (S : Addr) :
    uv V S 224 = ((ofBytesLE 8 ((byteAddrs (S + 8#64) 1).map V)).setWidth 32).setWidth 64 := by
  unfold uv
  rw [if_neg (show (224 : Nat) ≠ 160 by decide), if_neg (show (224 : Nat) ≠ 184 by decide),
    if_neg (show (224 : Nat) ≠ 208 by decide)]

/-- The bytes at 73: when `GetProperty` answered 0, `Val` = `uv` and `Def` = 1 for the four integer types, `Def` = 0
for `VT_EMPTY`. -/
def gV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  if g.rax.setWidth 32 = 0#32 ∧ guv_cases.getD (vtw V g.rsp).toNat 0 ≠ 240 then
    Vst (Vst V g.rbx (toBytesLE (uv V g.rsp (guv_cases.getD (vtw V g.rsp).toNat 0)) 8)) (g.rbx + 8#64)
      (toBytesLE 1#8 1)
  else if g.rax.setWidth 32 = 0#32 then Vst V (g.rbx + 8#64) (toBytesLE 0#8 1) else V

theorem gV_n {V : Addr → Byte} {g : Gprs} (hz : g.rax.setWidth 32 ≠ 0#32) : gV V g = V := by
  unfold gV
  rw [if_neg (fun h => hz h.1), if_neg hz]

theorem gV_e {V : Addr → Byte} {g : Gprs} (hz : g.rax.setWidth 32 = 0#32)
    (hc : guv_cases.getD (vtw V g.rsp).toNat 0 = 240) : gV V g = Vst V (g.rbx + 8#64) (toBytesLE 0#8 1) := by
  unfold gV
  rw [if_neg (fun h => h.2 hc), if_pos hz]

theorem gV_v {V : Addr → Byte} {g : Gprs} (hz : g.rax.setWidth 32 = 0#32)
    (hc : guv_cases.getD (vtw V g.rsp).toNat 0 ≠ 240) :
    gV V g = Vst (Vst V g.rbx (toBytesLE (uv V g.rsp (guv_cases.getD (vtw V g.rsp).toNat 0)) 8)) (g.rbx + 8#64)
      (toBytesLE 1#8 1) := by
  unfold gV
  rw [if_pos (And.intro hz hc)]

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

theorem g32 (x : Addr) : gq x + 32#64 = x - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- `ja` after `cmp word [m], 21`: taken above `VT_UI8`. -/
theorem c7w (f : Rflags) (m : BitVec 16) :
    (subF f m (BitVec.ofNat 16 21)).cond 7 = decide (21 < m.toNat) := by
  have hy : (BitVec.ofNat 16 21).toNat = 21 := rfl
  have e : (m = BitVec.ofNat 16 21) ↔ m.toNat = 21 := by rw [BitVec.toNat_eq, hy]
  rw [cond_7, subF_cf, subF_zf, hy]
  by_cases h : 21 < m.toNat
  · have h1 : ¬ m.toNat < 21 := by omega
    have h2 : ¬ m = BitVec.ofNat 16 21 := fun h' => by rw [e] at h'; omega
    simp [h, h1, h2]
  · by_cases h3 : m.toNat < 21
    · simp [h, h3]
    · have h2 : m = BitVec.ofNat 16 21 := e.2 (by omega)
      simp [h, h3, h2]

/-! ## The jump table -/

theorem sw_le {v : BitVec 16} (h : v.toNat ≤ 21) : (BitVec.setWidth 32 v).toNat ≤ 21 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
  exact h

theorem jt_addr (w : BitVec 32) (_h : w.toNat ≤ 21) :
    7250440#64 + BitVec.setWidth 64 w * 4#64 = Addr.add 7250440#64 (4 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The table's entries lead to `guv_cases` (offsets from `guv_at`, modulo 2^64: the throw stub below). -/
theorem jt_case : ∀ k < 22, (ofBytesLE 32 ((guv_jt.drop (4 * k)).take 4)).signExtend 64 + 7250440#64 =
    Addr.add guv_at (guv_cases.getD k 0) := by decide +kernel

theorem cs_cls : ∀ k < 22, guv_cases.getD k 0 = 18446744073707642528 ∨ guv_cases.getD k 0 = 240 ∨
    guv_cases.getD k 0 = 224 ∨ guv_cases.getD k 0 = 208 ∨ guv_cases.getD k 0 = 184 ∨
    guv_cases.getD k 0 = 160 := by decide +kernel

theorem tgt_thr : Addr.add guv_at 18446744073707642528 = Addr.add (0x419b70#64) 0 := by decide

theorem jt_foot {F : Footprint} (fT : ∀ i < 88, Foot F.data (Addr.add 7250440#64 i)) (w : BitVec 32)
    (hw : w.toNat ≤ 21) : ∀ i < 4, Foot F.data (Addr.add (7250440#64 + BitVec.setWidth 64 w * 4#64) i) := by
  intro i hi
  rw [jt_addr w hw, addr_add_add']
  exact fT _ (by omega)

/-- The table's target for the tag `v`. -/
theorem tg (V : Addr → Byte) (v : BitVec 16) (hv : v.toNat ≤ 21)
    (hjt : List.map V (byteAddrs 7250440#64 88) = guv_jt) :
    BitVec.signExtend 64 (ofBytesLE 32 (List.map V
      (byteAddrs (7250440#64 + BitVec.setWidth 64 (BitVec.setWidth 32 v) * 4#64) 4))) + 7250440#64 =
      Addr.add guv_at (guv_cases.getD v.toNat 0) := by
  have hw : (BitVec.setWidth 32 v).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
  rw [jt_addr _ (sw_le hv), hw, Hca.sub_rd V _ guv_jt 88 hjt (4 * v.toNat) 4 (by omega)]
  exact jt_case v.toNat (by omega)

/-- The closer of the pieces' conditions. -/
local macro "gcl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- From the entry to the first `call`: the pushes, the stack guard stored, `Val` = `Def` = 0, `prop` cleared,
`rax` the vtable. -/
theorem vc_0 {cn vt : BitVec 64}
    (hcn : rdq(Vp V g, fb + 40#64) = cn) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hvt : rdq(Vg V g cn, g.rdi) = vt) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (gq g.rsp + 24#64) i)) (w5 : ∀ i < 8, Foot Wl (Addr.add g.rcx i))
    (w5b : ∀ i < 1, Foot Wl (Addr.add (g.rcx + 8#64) i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (gq g.rsp) i)) (w7 : ∀ i < 8, Foot Wl (Addr.add (gq g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 63 ∧ g' = gC g vt ∧ V' = VC V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp, Vg, VC, gC, gq] at hcn hvt w1 w2 w3 w4 w5 w5b w6 w7 ⊢
  wpx [W_0, o0, Op.ldf, hcn, hvt, xz, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies,
    implies_true]
  gcl

/-- From 66, `GetProperty`'s answer not 0: to 73. -/
theorem vc_66n (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_66 fb F Wl (fun j' g' _ V' => j' = 73 ∧ g' = { g with r12 := zl g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_66, o1, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  gcl

/-- From 66, the answer 0: `cmp word [rsp], 21`, to the `ja` at 125 (its flags: above `VT_UI8`). -/
theorem vc_66z {Q : Post} (hz : g.rax.setWidth 32 = 0#32) (ft : ∀ i < 2, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, fl.cond 7 = decide (21 < (vtw V g.rsp).toNat) → Q 125 { g with r12 := zl g.rax } fl V) :
    W_66 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw] at hz ft h ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_66, W_120, o1, o5, Op.cmpmi, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | exact h _ (c7w _ _)
    | (rename_i hfl; subst hfl; exact h _ (c7w _ _))
    | with_reducible assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- From 131: the tag `vt` (not above 21) through the table, its target in `rax`, to the `jmp` at 149. -/
theorem vc_131 {Q : Post} (hv : (vtw V g.rsp).toNat ≤ 21)
    (hjt : List.map V (byteAddrs 7250440#64 88) = guv_jt)
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsp i)) (fT : ∀ i < 88, Foot F.data (Addr.add 7250440#64 i))
    (h : ∀ ra fl, ra = Addr.add guv_at (guv_cases.getD (vtw V g.rsp).toNat 0) →
      Q 149 { g with rax := ra, rdx := 7250440#64 } fl V) :
    W_131s F Wl Q g f V := by
  have jT := jt_foot fT _ (sw_le hv)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtw] at hv ft jT h ⊢
  wpx [W_131s, o6, Op.ldsx]
  all_goals repeat' (first
    | exact h _ _ (tg _ _ hv hjt)
    | with_reducible assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- `VT_UI8` (160): `Val` = the 8 bytes at `rsp + 8`, `eax` = 1, to 173. -/
theorem vc_160 (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wb : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_160 fb F Wl (fun j' g' _ V' => j' = 173 ∧ g' = { g with rax := 1#64 } ∧
      V' = Vst V g.rbx (toBytesLE (uv V g.rsp 160) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 wb ⊢
  wpx [W_160, o7, uv_160, eq_self_iff_true, and_true, true_and]
  all_goals repeat' (first
    | exact rfl
    | with_reducible assumption
    | exact fun i hi => f8 i (by omega)
    | exact trivial
    | apply And.intro
    | intro _)

/-- `VT_UI4` (184): `Val` = the 4 bytes at `rsp + 8`, `eax` = 1, to 173. -/
theorem vc_184 (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wb : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_184 fb F Wl (fun j' g' _ V' => j' = 173 ∧ g' = { g with rax := 1#64 } ∧
      V' = Vst V g.rbx (toBytesLE (uv V g.rsp 184) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 wb ⊢
  wpx [W_184, o9, uv_184, eq_self_iff_true, and_true, true_and]
  all_goals repeat' (first
    | exact rfl
    | with_reducible assumption
    | exact fun i hi => f8 i (by omega)
    | exact trivial
    | apply And.intro
    | intro _)

/-- `VT_UI2` (208): `Val` = the 2 bytes at `rsp + 8`, `eax` = 1, to 173. -/
theorem vc_208 (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wb : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_208 fb F Wl (fun j' g' _ V' => j' = 173 ∧ g' = { g with rax := 1#64 } ∧
      V' = Vst V g.rbx (toBytesLE (uv V g.rsp 208) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 wb ⊢
  wpx [W_208, o10, uv_208, eq_self_iff_true, and_true, true_and]
  all_goals repeat' (first
    | exact rfl
    | with_reducible assumption
    | exact fun i hi => f8 i (by omega)
    | exact trivial
    | apply And.intro
    | intro _)

/-- `VT_UI1` (224): `Val` = the byte at `rsp + 8`, `eax` = 1, to 173. -/
theorem vc_224 (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wb : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_224 fb F Wl (fun j' g' _ V' => j' = 173 ∧ g' = { g with rax := 1#64 } ∧
      V' = Vst V g.rbx (toBytesLE (uv V g.rsp 224) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 wb ⊢
  wpx [W_224, o11, uv_224, eq_self_iff_true, and_true, true_and]
  all_goals repeat' (first
    | exact rfl
    | with_reducible assumption
    | exact fun i hi => f8 i (by omega)
    | exact trivial
    | apply And.intro
    | intro _)

/-- `VT_EMPTY` (240): `eax` = 0, to 173. -/
theorem vc_240 : W_240 fb F Wl (fun j' g' _ V' => j' = 173 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_240, o12, xz]
  gcl

/-- 173: `Def` = `al`, to 73. -/
theorem vc_173 (wb8 : ∀ i < 1, Foot Wl (Addr.add (g.rbx + 8#64) i)) :
    W_173 fb F Wl (fun j' g' _ V' => j' = 73 ∧ g' = g ∧
      V' = Vst V (g.rbx + 8#64) (toBytesLE (g.rax.setWidth 8) 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wb8 ⊢
  wpx [W_173, o8]
  gcl

/-- 73: `mov rdi, rbp`, to the `call` at 76. -/
theorem vc_73 : W_73 fb F Wl (fun j' g' _ V' => j' = 76 ∧ g' = { g with rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_73, o2]
  gcl

/-- From 81: the stack guard checked, the frame dropped, `eax` = `r12d`, the pops, to the `ret` at 112. -/
theorem vc_81 {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8) i))
    (h : ∀ fl, Q 112
      { g with
          rax := zl g.r12,
          rbx := rdq(V, g.rsp + 32#64),
          rbp := rdq(V, g.rsp + 32#64 + 8),
          rsp := g.rsp + 32#64 + 8 + 8 + 8,
          r12 := rdq(V, g.rsp + 32#64 + 8 + 8) } fl V) :
    W_81 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 l1 l2 l3 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_81, W_101, o3, o4, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 66 (back from `GetProperty`, `rsp` = `&prop`, `rbx` = `value`) to 73 with the bytes `gV`, `r12` = the
answer's low 32 bits, `rax`, `rdx` some values; or to the throw stub, the bytes as they were. -/
theorem guv_mid {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L guv_at guv)
    {codeT : List Byte} (hinT : CodeIn L (0x419b70#64) codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = guv_at.add 66)
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (fT : ∀ i < 88, Foot F.data (Addr.add 7250440#64 i))
    (hjt : List.map V (byteAddrs 7250440#64 88) = guv_jt)
    (wb : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rbx i))
    (wb8 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rbx + 8#64) i))
    (kth : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = 0x419b70#64 →
      GoG prof L o gev gP gE Y t')
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (gV V X.cpu.gpr) →
      Y.cpu.rip = guv_at.add 73 →
      (∃ ra rd, Y.cpu.gpr = { X.cpu.gpr with rax := ra, rdx := rd, r12 := zl X.cpu.gpr.rax }) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  rcases Classical.em (X.cpu.gpr.rax.setWidth 32 ≠ 0#32) with hz | hz'
  · refine (c_66 prof fb).run c hfs hin _ hK hA hrip (vc_66n hz) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact k Y t₁ hKY (by rw [gV_n hz]; exact hAY) hrY ⟨X.cpu.gpr.rax, X.cpu.gpr.rdx, by rw [hgY]; try rfl⟩
  have hz : X.cpu.gpr.rax.setWidth 32 = 0#32 := Decidable.of_not_not hz'
  -- the answer 0: `cmp word [rsp], 21` and the `ja`
  refine (c_66 prof fb).run c hfs hin (fun j' g' f' V' => j' = 125 ∧
      g' = { X.cpu.gpr with r12 := zl X.cpu.gpr.rax } ∧ f'.cond 7 = decide (21 < (vtw V X.cpu.gpr.rsp).toNat) ∧
      V' = V) hK hA hrip (vc_66z hz ft fun _ h7 => ⟨rfl, rfl, h7, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, h7, hV₁⟩ Y t₁ hKY hAY hrY hgY hfY
  subst V₁
  refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_125 _) hinT (tgt := 0) hT tgt_125 ?_ ?_
  · intro _
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, -⟩
    exact kth Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero])
  intro hc7
  have h7' := hc7
  rw [hfY, h7] at h7'
  have hv : (vtw V X.cpu.gpr.rsp).toNat ≤ 21 := by
    have := of_decide_eq_false h7'
    omega
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have e2 : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hgY]
  -- the table
  refine (c_131s prof fb).run c hfs hin (fun j' g' _ V' => j' = 149 ∧
      (∃ ra, g' = { Y₂.cpu.gpr with rax := ra, rdx := 7250440#64 } ∧
        ra = Addr.add guv_at (guv_cases.getD (vtw V X.cpu.gpr.rsp).toNat 0)) ∧ V' = V) hK₂ hA₂ hr₂
    (vc_131 (by rw [e2]; exact hv) hjt (by rw [e2]; exact ft) fT
      fun ra _ hra => ⟨rfl, ⟨ra, rfl, by rw [hra, e2]⟩, rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, ⟨ra, rfl, hra⟩, hV₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₃
  have hG : ∀ Y₄ : State, Y₄.cpu.gpr = Y₃.cpu.gpr →
      Y₄.cpu.gpr = { X.cpu.gpr with rax := ra, rdx := 7250440#64, r12 := zl X.cpu.gpr.rax } := by
    intro Y₄ h
    rw [h, hg₃, hg₂, hgY]
  -- from 173 with `al` = `b8`: `Def` = `b8`, to 73
  have go173 : ∀ (Y₅ : State) (t₅ : Nat) (U : Addr → Byte) (b : BitVec 64) (b8 : BitVec 8),
      KeptW Wl s₀ Y₅ →
      Agree F Y₅.proc.mm.mem U → Y₅.cpu.rip = guv_at.add 173 →
      Y₅.cpu.gpr = { X.cpu.gpr with rax := b, rdx := 7250440#64, r12 := zl X.cpu.gpr.rax } →
      b.setWidth 8 = b8 → Vst U (X.cpu.gpr.rbx + 8#64) (toBytesLE b8 1) = gV V X.cpu.gpr →
      GoG prof L o gev gP gE Y₅ t₅ := by
    intro Y₅ t₅ U b b8 hK₅ hA₅ hr₅ hg₅ hb hU
    have b5 : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [hg₅]
    have a5 : Y₅.cpu.gpr.rax = b := by rw [hg₅]
    refine (c_173 prof fb).run c hfs hin _ hK₅ hA₅ hr₅ (vc_173 (by rw [b5]; exact wb8)) ?_
    rintro j' g fl V₆ ⟨rfl, rfl, hV₆⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
    subst V₆
    rw [b5, a5, hb, hU] at hA₆
    exact k Y₆ t₆ hK₆ hA₆ hr₆ ⟨b, 7250440#64, by rw [hg₆, hg₅]⟩
  rcases cs_cls (vtw V X.cpu.gpr.rsp).toNat (by omega) with hc | hc | hc | hc | hc | hc
  · -- the other tags: the throw stub
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hinT (tgt := 0) hT
      (by rw [hg₃]; exact hra.trans tgt_thr) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, -⟩
    exact kth Y₄ t₄ hK₄ hA₄ (by rw [hr₄, addr_add_zero])
  · -- `VT_EMPTY`
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hin (tgt := 240) (lt_len (by decide))
      (by rw [hg₃]; exact hra) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have h4 := hG Y₄ hg₄
    refine (c_240 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ vc_240 ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    exact go173 Y₅ t₅ V 0#64 0#8 hK₅ hA₅ hr₅ (by rw [hg₅, h4]) (by decide) (gV_e hz hc).symm
  · -- `VT_UI1`
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hin (tgt := 224) (lt_len (by decide))
      (by rw [hg₃]; exact hra) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have h4 := hG Y₄ hg₄
    have b4 : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [h4]
    have r4 : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [h4]
    refine (c_224 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_224 (by rw [r4]; exact f8) (by rw [b4]; exact wb)) ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    rw [b4, r4] at hA₅
    exact go173 Y₅ t₅ _ 1#64 1#8 hK₅ hA₅ hr₅ (by rw [hg₅, h4]) (by decide)
      (by rw [gV_v (V := V) hz (by rw [hc]; decide), hc])
  · -- `VT_UI2`
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hin (tgt := 208) (lt_len (by decide))
      (by rw [hg₃]; exact hra) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have h4 := hG Y₄ hg₄
    have b4 : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [h4]
    have r4 : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [h4]
    refine (c_208 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_208 (by rw [r4]; exact f8) (by rw [b4]; exact wb)) ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    rw [b4, r4] at hA₅
    exact go173 Y₅ t₅ _ 1#64 1#8 hK₅ hA₅ hr₅ (by rw [hg₅, h4]) (by decide)
      (by rw [gV_v (V := V) hz (by rw [hc]; decide), hc])
  · -- `VT_UI4`
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hin (tgt := 184) (lt_len (by decide))
      (by rw [hg₃]; exact hra) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have h4 := hG Y₄ hg₄
    have b4 : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [h4]
    have r4 : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [h4]
    refine (c_184 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_184 (by rw [r4]; exact f8) (by rw [b4]; exact wb)) ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    rw [b4, r4] at hA₅
    exact go173 Y₅ t₅ _ 1#64 1#8 hK₅ hA₅ hr₅ (by rw [hg₅, h4]) (by decide)
      (by rw [gV_v (V := V) hz (by rw [hc]; decide), hc])
  · -- `VT_UI8`
    rw [hc] at hra
    refine c.s_jmp_rx hK₃ hA₃ hin (lt_len (by decide)) hr₃ (jmp_149 _) hin (tgt := 160) (lt_len (by decide))
      (by rw [hg₃]; exact hra) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have h4 := hG Y₄ hg₄
    have b4 : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [h4]
    have r4 : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [h4]
    refine (c_160 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_160 (by rw [r4]; exact f8) (by rw [b4]; exact wb)) ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    rw [b4, r4] at hA₅
    exact go173 Y₅ t₅ _ 1#64 1#8 hK₅ hA₅ hr₅ (by rw [hg₅, h4]) (by decide)
      (by rw [gV_v (V := V) hz (by rw [hc]; decide), hc])

/-- `GetUInt64Value (archive, index, propID, value)` (`rdi`, `esi`, `edx`, `rcx`) from its entry, the stack guard
`cn` (the 8 bytes at `fs:0x28`), the vtable `vt` (the 8 bytes at `archive`) and `GetProperty`'s entry `eF` (the 8
bytes at `vt + 0x30`) as read. At `eF` the registers are `gC` with `rsp` 8 below the frame and the bytes `VC` with
the return address pushed (`kf1`); if `GetProperty` returns to `guv_at + 66` with `rsp`, `rbp` the frame, `rbx` =
`value` and the jump table's bytes as they are, the run reaches the throw stub with the bytes as `GetProperty` left
them (`kth`), or `~CPropVariant`'s entry with `rdi` = `&prop`, `r12` = the answer's low 32 bits, the bytes `gV` and
the return address `guv_at + 81` pushed (`kf2`); if that returns with `rsp` the frame, `r12` as at its entry, the
stack guard as at `fs:0x28` and the saved registers and the return address as they were, the run reaches the return
address with `eax` = the answer's low 32 bits and `rbx`, `rbp`, `r12`, `rsp` restored (`kr`). -/
theorem guv_ok {fb eF : Addr} {cn vt : BitVec 64} {P1 : State → (Addr → Byte) → Prop}
    {P2 : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L guv_at guv)
    (hinP : CodeIn L Pvd.pvd_at Pvd.pvd)
    {codeT : List Byte} (hinT : CodeIn L (0x419b70#64) codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = guv_at)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 24#64) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (w5b : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rcx + 8#64) i))
    (w6 : ∀ i < 4, Foot Wl (Addr.add (gq X.cpu.gpr.rsp) i))
    (w7 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 8#64) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fT : ∀ i < 88, Foot F.data (Addr.add 7250440#64 i))
    (hcn : rdq(Vp V X.cpu.gpr, fb + 40#64) = cn) (hvt : rdq(Vg V X.cpu.gpr cn, X.cpu.gpr.rdi) = vt)
    (fv : ∀ i < 8, Foot F.data (Addr.add (vt + 48#64) i))
    {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(VC V X.cpu.gpr cn, vt + 48#64) = eF)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VC V X.cpu.gpr cn) (gq X.cpu.gpr.rsp - 8) (toBytesLE (guv_at.add 66) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC X.cpu.gpr vt).set 4 (gq X.cpu.gpr.rsp - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = guv_at.add 66 → Z.cpu.gpr.rsp = gq X.cpu.gpr.rsp → Z.cpu.gpr.rbp = gq X.cpu.gpr.rsp →
        Z.cpu.gpr.rbx = X.cpu.gpr.rcx → List.map V' (byteAddrs 7250440#64 88) = guv_jt → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kth : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), P1 Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V' → Y.cpu.rip = 0x419b70#64 → GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), P1 Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (gV V' Z.cpu.gpr) (gq X.cpu.gpr.rsp - 8) (toBytesLE (guv_at.add 81) 8)) →
      Y.cpu.rip = Pvd.pvd_at →
      (∃ ra rd, Y.cpu.gpr = ({ Z.cpu.gpr with
          rax := ra,
          rdx := rd,
          rdi := Z.cpu.gpr.rbp,
          r12 := zl Z.cpu.gpr.rax }).set 4 (Z.cpu.gpr.rsp - 8)) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = guv_at.add 81 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp → W.cpu.gpr.r12 = zl Z.cpu.gpr.rax →
        rdq(V'', gq X.cpu.gpr.rsp + 24#64) = rdq(V'', fb + 40#64) →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V'', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ →
        P2 Z W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (W : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat),
      P1 Z V' → P2 Z W V'' → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := zl (zl Z.cpu.gpr.rax),
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8,
          r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = guv_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 63 ∧ g' = gC X.cpu.gpr vt ∧
      V' = VC V X.cpu.gpr cn) hK hA hrip' (vc_0 hcn fc hvt fa w1 w2 w3 w4 w5 w5b w6 w7) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = gq X.cpu.gpr.rsp := by rw [hgY]
  have he : eaD Y 0 48 = vt + 48#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 48 = _
    rw [hgY]
    rfl
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_63 _) (by rw [he]; exact fv) hinF hF0
    (by rw [he]; exact htgt) (by rw [hsY]; exact w8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY]; try rfl) ?_
  -- back from `GetProperty`, to 73 or the throw stub
  intro Z V' t'' hKZ hAZ hrZ hzs hzp hzb hjt hP1
  have f0 : ∀ i < 2, Foot F.data (Addr.add Z.cpu.gpr.rsp i) := by
    rw [hzs]
    exact fun i hi => c.hws _ (w6 i (by omega))
  have f8 : ∀ i < 8, Foot F.data (Addr.add (Z.cpu.gpr.rsp + 8#64) i) := by
    rw [hzs]
    exact fun i hi => c.hws _ (w7 i hi)
  refine guv_mid c hfs hin hinT hT hKZ hAZ hrZ f0 f8 fT hjt (by rw [hzb]; exact w5) (by rw [hzb]; exact w5b)
    (fun Y₀ t₀ hK₀ hA₀ hr₀ => kth Z V' Y₀ t₀ hP1 hK₀ hA₀ hr₀) ?_
  rintro U t₃ hKU hAU hrU ⟨ra, rd, hgU⟩
  -- `mov rdi, rbp` and the `call` to `~CPropVariant`
  refine (c_73 prof fb).run c hfs hin (fun j' g' _ V₂ => j' = 76 ∧ g' = { U.cpu.gpr with rdi := U.cpu.gpr.rbp } ∧
      V₂ = gV V' Z.cpu.gpr) hKU hAU hrU vc_73 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U₁ t₄ hKU₁ hAU₁ hrU₁ hgU₁ -
  have hsU₁ : U₁.cpu.gpr.rsp = gq X.cpu.gpr.rsp := by
    rw [hgU₁, hgU]
    exact hzs
  refine c.s_call hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (call_76 _) hinP
    (Pvd.lt_len (j := 0) (by decide)) tgt_76
    (by rw [hsU₁]; exact w8) ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU₁] at hA₃
  refine kf2 Z V' Y₃ t₅ hP1 hK₃ hA₃ hr₃ ⟨ra, rd, by rw [hg₃, hgU₁, hgU]; try rfl⟩ ?_
  -- back from `~CPropVariant`
  intro W V'' t₆ hKW hAW hrW hws hw12 hcw hb1 hb2 hb3 hra hP2
  have f24 : ∀ i < 8, Foot F.data (Addr.add (gq X.cpu.gpr.rsp + 24#64) i) := fun i hi => c.hws _ (w4 i hi)
  have l3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (w3 i hi)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (w2 i hi)
  have l1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (w1 i hi)
  refine (c_81 prof fb).run c hfs hin (fun j' g' _ V₃ => j' = 112 ∧
      g' = { W.cpu.gpr with
          rax := zl (zl Z.cpu.gpr.rax),
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp,
          r12 := X.cpu.gpr.r12 } ∧ V₃ = V'') hKW hAW hrW
    (vc_81 (by rw [hws]; exact hcw) (by rw [hws]; exact f24) fc (by rw [hws, g32]; exact l3)
      (by rw [hws, g32, a3s]; exact l2) (by rw [hws, g32, a3s, a2s]; exact l1)
      fun _ => ⟨rfl, by rw [hw12, hws, g32, a3s, a2s, a1s, hb3, hb2, hb1], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₇ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₄
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_112 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hra) ?_
  rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' W V'' Z' t₈ hP1 hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Guv
