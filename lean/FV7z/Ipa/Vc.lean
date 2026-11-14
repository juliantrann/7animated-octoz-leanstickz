import FV7z.Ipa.Cuts
import FV7z.Hwc.Vc
/-!
# `_dl_init_paths`: the pieces between its `call`s (PLAN.md G3, startup)

glibc 2.31's `_dl_init_paths (llp)` at `0x6a88f0` with `llp` null (no `LD_LIBRARY_PATH`), `rbp = r` its frame:
`_dl_important_hwcaps` gives `ncapstr = n` (8 or 16), `malloc (40)` the array `A` of `rtld_search_dirs.dirs`,
`malloc (160 q)` (`q = (4 n + 79) / 40`: 2 or 3) the 4 elements of `40 q` bytes at `B`; each element's status array
(`4 n` bytes from offset `0x28`) is cleared by `memset`; the names are the system directories of `.rodata`
(lengths at `0x705dc0`, the strings from `0x705de0`, each starting with `/`).

- `vc_0`: the prologue (6 `push`es, `sub rsp, 0x28`, `llp` to `r - 0x50`), the arguments of `_dl_important_hwcaps`
  (`_dl_platform`, `_dl_platformlen`, `&ncapstr`, `&max_capstrlen`), to its `call` (53).
- `vc_58`: the result to `_dl_capstrs` (`0x791ea0`), `rdi = 40` to the `call` of `malloc` (70).
- `vc_75`: `A` to `rtld_search_dirs.dirs` (`0x791e80`), `n` to `r - 0x38`, `rdi = 160 q` to the `call` of `malloc`
  (148).
- `vc_153`: the first element (`/lib/x86_64-linux-gnu/`), `40 q` and `-40 q` to the frame, to the `memset` (267).
- `vc_267`: the arguments of `memset (elem + 0x28, 0, 4 n)` (276); `vc_281`: the last directory or not.
- `vc_293`: the next element (`i + 1`), its name starting with `/` (the `assert`), back to 267.
- `vc_384`: the ends of the lists, `llp` null: `_dl_init_paths` returns (`ret` at 450), the registers popped.

The bytes the pieces keep are stated by address (`toNat`), so that the proofs do not depend on the form of the
addresses the effects compute.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000
set_option Elab.async false

/-- The side conditions of the addresses: sums made `toNat` sums, then `omega`. -/
macro "ipd" : tactic => `(tactic| ((try simp only [FV7z.toBytesLE_length, BitVec.toNat_add, BitVec.toNat_ofNat,
  Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul]) <;> omega))

/-- A load through the stores apart from it, down to the store it reads (or to the memory under them); the side
conditions as goals, so that a failing one stops the `repeat` (a failing discharger of `simp`, like a `by` inside a
`rw`, only logs its error). -/
macro "ipeel" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.rd_Vst _ _ _ _ _ ?_ ?_ ?_]; rotate_left; iterate 3 ipd)))

/-- `ipeel` for the loads at `x` only. -/
macro "ipeelx" x:term : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.rd_Vst _ _ _ $x _ ?_ ?_ ?_]; rotate_left; iterate 3 ipd)))

/-- A byte outside the stores. -/
macro "iout" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 ipd)))

/-- The load of the 8 bytes a store stored. -/
macro "iself" : tactic => `(tactic| (rw [FV7z.Tun.rd_Vst_self _ _ _ (FV7z.toBytesLE_length _ _) (by ipd),
  FV7z.ofBytesLE_toBytesLE (n := 8) rfl]; try rfl))

/-- The goals of a piece: the flags and the conjunctions split, each closed by a hypothesis, `rfl`, or a region. -/
macro "icl" : tactic =>
  `(tactic| (all_goals (repeat' (first | intro (_ : Rflags) | intro (_ : Bool) | intro (_ : _ = _) |
    apply And.intro)); all_goals first | with_reducible assumption | with_reducible rfl | exact True.intro | skip))

/-- `n` bytes from `x` inside a region. -/
theorem rgn {p : Addr → Prop} {lo hi : Nat} (hp : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → p a) {x : Addr}
    {n : Nat} (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) (h3 : x.toNat + n ≤ 2 ^ 64) : ∀ i < n, p (x.add i) :=
  fun i hi' => by
    have e := toNat_add_of_fits hi' h3
    exact hp _ (by rw [e]; omega) (by rw [e]; omega)

/-- A footprint goal of a region, its bounds by `ipd`. -/
macro "ireg" h:term : tactic => `(tactic| (refine rgn $h ?_ ?_ ?_ <;> ipd))

/-! ## The `call`s and the `ret`s -/

def pc53 : List Byte := [0xe8, 0x16, 0x48, 0x00, 0x00]
theorem pc53_0 : ∀ feat, Dec feat pc53 0 (FV7z.mk .call 64 [.rel 18454] 5) := by dec_rfl
theorem w_53 : pc53 <+: ipa.drop 53 := by decide +kernel
theorem call_53 (feat : Features) : Dec feat ipa 53 (FV7z.mk .call 64 [.rel 18454] 5) :=
  Dec.shift (j := 53) (k := 0) (pc53_0 feat) w_53 (Nat.zero_le _)
theorem tgt_53 : ipa_at.add (53 + 5) + BitVec.ofNat 64 18454 = Hwc.hwc_at := by decide

def pc70 : List Byte := [0xe8, 0x25, 0xa8, 0xf8, 0xff]
theorem pc70_0 : ∀ feat, Dec feat pc70 0 (FV7z.mk .call 64 [.rel 18446744073709070373] 5) := by dec_rfl
theorem w_70 : pc70 <+: ipa.drop 70 := by decide +kernel
theorem call_70 (feat : Features) : Dec feat ipa 70 (FV7z.mk .call 64 [.rel 18446744073709070373] 5) :=
  Dec.shift (j := 70) (k := 0) (pc70_0 feat) w_70 (Nat.zero_le _)
theorem tgt_70 : ipa_at.add (70 + 5) + BitVec.ofNat 64 18446744073709070373 = 6500704#64 := by decide

def pc148 : List Byte := [0xe8, 0xd7, 0xa7, 0xf8, 0xff]
theorem pc148_0 : ∀ feat, Dec feat pc148 0 (FV7z.mk .call 64 [.rel 18446744073709070295] 5) := by dec_rfl
theorem w_148 : pc148 <+: ipa.drop 148 := by decide +kernel
theorem call_148 (feat : Features) : Dec feat ipa 148 (FV7z.mk .call 64 [.rel 18446744073709070295] 5) :=
  Dec.shift (j := 148) (k := 0) (pc148_0 feat) w_148 (Nat.zero_le _)
theorem tgt_148 : ipa_at.add (148 + 5) + BitVec.ofNat 64 18446744073709070295 = 6500704#64 := by decide

def pc276 : List Byte := [0xe8, 0x77, 0x86, 0xd5, 0xff]
theorem pc276_0 : ∀ feat, Dec feat pc276 0 (FV7z.mk .call 64 [.rel 18446744073706767991] 5) := by dec_rfl
theorem w_276 : pc276 <+: ipa.drop 276 := by decide +kernel
theorem call_276 (feat : Features) : Dec feat ipa 276 (FV7z.mk .call 64 [.rel 18446744073706767991] 5) :=
  Dec.shift (j := 276) (k := 0) (pc276_0 feat) w_276 (Nat.zero_le _)
theorem tgt_276 : ipa_at.add (276 + 5) + BitVec.ofNat 64 18446744073706767991 = 4198528#64 := by decide

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_450 : pret <+: ipa.drop 450 := by decide +kernel
theorem ret_450 (feat : Features) : Dec feat ipa 450 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 450) (k := 0) (pret_0 feat) w_450 (Nat.zero_le _)
theorem w_1681 : pret <+: Hwc.hwc.drop 1681 := by decide +kernel
/-- The `ret` of `_dl_important_hwcaps`. -/
theorem ret_1681 (feat : Features) : Dec feat Hwc.hwc 1681 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 1681) (k := 0) (pret_0 feat) w_1681 (Nat.zero_le _)

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the prologue: the six `push`es (`rbp`, `r15`, `r14`, `r13`, `r12`, `rbx`) and `llp` at
`rbp - 0x50`. -/
def iV0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8))
    (g.rsp - 8 + 18446744073709551536#64) (toBytesLE g.rdi 8)

/-- The prologue, to the `call` of `_dl_important_hwcaps (_dl_platform, _dl_platformlen, &ncapstr,
&max_capstrlen)`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 88, Foot Wl (Addr.add (g.rsp - 88#64) i)) (hsp : 88 ≤ g.rsp.toNat)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 53 ∧ g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40#64 ∧
      g'.rbp = g.rsp - 8 ∧ g'.rcx = 7937680#64 ∧ g'.rdx = 7937688#64 ∧
      g'.rsi = rdq(iV0 V g, 8029520#64) ∧ g'.rdi = rdq(iV0 V g, 8029512#64) ∧
      g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ V' = iV0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst hsp
  have slot : ∀ a : Addr, (a - (rsp - 88#64)).toNat < 88 → Foot Wl a := fun a ha => by
    have e : Addr.add (rsp - 88#64) (a - (rsp - 88#64)).toNat = a := by simp only [Addr.add]; bv_omega
    exact e ▸ hst _ ha
  wpx [W_0, o0, Op.push, Op.lda]
  all_goals (repeat' apply And.intro)
  all_goals first
    | exact fun i hi => slot _ (by simp only [Addr.add]; bv_omega)
    | exact hf1
    | exact hf2
    | rfl
    | decide
    | skip

/-- After `_dl_important_hwcaps`: its result to `_dl_capstrs`, to the `call` of `malloc (40)`. -/
theorem vc_58 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : ∀ i < 8, Foot Wl (Addr.add 7937696#64 i)) :
    W_58 F Wl (fun j' g' _ V' => j' = 70 ∧ g' = { g with rdi := 40#64 } ∧
      V' = Vst V 7937696#64 (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  hwx [W_58, o1, Op.sta]
  icl

/-- After `malloc (40)` (`A ≠ 0`): `A` to `rtld_search_dirs.dirs`, `n = ncapstr` to `r - 0x38`, `rdi = 160 q`, to
the `call` of `malloc` (148). -/
theorem vc_75 {g : Gprs} {f : Rflags} {V : Addr → Byte} {n q : Nat} (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3)
    (hA : g.rax ≠ 0#64) (hn : rdq(V, 7937688#64) = BitVec.ofNat 64 n)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add 7937664#64 i)) (hf : ∀ i < 8, Foot F.data (Addr.add 7937688#64 i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551560#64) i)) :
    W_75 F Wl (fun j' g' _ V' => j' = 148 ∧
      g'.rdi = BitVec.ofNat 64 (160 * q) ∧ g'.rbx = BitVec.ofNat 64 (5 * q) ∧ g'.r13 = BitVec.ofNat 64 (4 * n) ∧
      g'.r14 = g.rax ∧ g'.rbp = g.rbp ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
      V' = Vst (Vst V 7937664#64 (toBytesLE g.rax 8)) (g.rbp + 18446744073709551560#64)
        (toBytesLE (BitVec.ofNat 64 n) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hA hs2 ⊢
  have hA' : (rax == 0#64) = false := beq_eq_false_iff_ne.2 hA
  have hn' : rdq(Vst V 7937664#64 (toBytesLE rax 8), 7937688#64) = BitVec.ofNat 64 n := by
    rw [Tun.rd_Vst _ _ _ _ _ (by ipd) (by ipd) (by ipd)]
    exact hn
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    hwx [W_75, W_91, o2, o3, Op.sta, Op.lda, Op.mul64, Op.mulp, Op.shr64, Op.shl64, hA', hn',
      BitVec.reduceExtractLsb', Nat.reduceMod, Nat.reduceDiv]
    icl

/-- The bytes `vc_153` stores. -/
def M153 (V : Addr → Byte) (B A r : Addr) (q : Nat) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V A (toBytesLE B 8)) 8029552#64 (toBytesLE B 8))
    (B + 8#64) (toBytesLE 7362447#64 8)) (B + 24#64) (toBytesLE 7364064#64 8))
    (r + 18446744073709551552#64) (toBytesLE (BitVec.ofNat 64 (40 * q)) 8))
    7937672#64 (toBytesLE 0#32 4)) (B + 16#64) (toBytesLE 0#64 8)) (B + 32#64) (toBytesLE 22#64 8))
    (r + 18446744073709551544#64) (toBytesLE (BitVec.ofNat 64 (2 ^ 64 - 40 * q)) 8)

/-- After `malloc (160 q)` (`B ≠ 0`): `B` to `A[0]` and `_dl_all_dirs`, the first element (`/lib/x86_64-linux-gnu/`,
22 bytes), `40 q` and `-40 q` to `r - 0x40`, `r - 0x48`, `n ≠ 0`: to the `memset` of its status array (267). -/
theorem vc_153 {g : Gprs} {f : Rflags} {V : Addr → Byte} {n q : Nat} (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3)
    (hB : g.rax ≠ 0#64) (hbx : g.rbx = BitVec.ofNat 64 (5 * q))
    (hn : rdq(V, g.rbp + 18446744073709551560#64) = BitVec.ofNat 64 n)
    (hr : 7940480 + 88 ≤ g.rbp.toNat) (hr2 : g.rbp.toNat + 16 ≤ 2 ^ 64)
    (hBl : 7940480 ≤ g.rax.toNat) (hBh : g.rax.toNat + 160 * q ≤ g.rbp.toNat - 88)
    (hAl : 7940480 ≤ g.r14.toNat) (hAh : g.r14.toNat + 40 ≤ g.rbp.toNat - 88)
    (h7a : 8029560 ≤ g.rbp.toNat - 88)
    (hWA : ∀ a : Addr, g.r14.toNat ≤ a.toNat → a.toNat < g.r14.toNat + 40 → Foot Wl a)
    (hWB : ∀ a : Addr, g.rax.toNat ≤ a.toNat → a.toNat < g.rax.toNat + 160 * q → Foot Wl a)
    (hWF : ∀ a : Addr, g.rbp.toNat - 80 ≤ a.toNat → a.toNat < g.rbp.toNat + 8 → Foot Wl a ∧ Foot F.data a)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hWb : ∀ a : Addr, 7937664 ≤ a.toNat → a.toNat < 7937720 → Foot Wl a) :
    W_153 F Wl (fun j' g' _ V' => j' = 267 ∧ g'.r15 = g.rax ∧ g'.r14 = g.r14 + 8#64 ∧ g'.r12 = 7364032#64 ∧
      g'.rbx = 7364087#64 ∧ g'.r13 = g.r13 ∧ g'.rbp = g.rbp ∧ g'.rsp = g.rsp ∧
      rdq(V', g.rbp + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q) ∧
      rdq(V', g.rbp + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q) ∧
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨
        g.rbp.toNat - 80 ≤ a.toNat ∧ a.toNat < g.rbp.toNat - 72 ∨ g.rbp.toNat - 56 ≤ a.toNat) → V' a = V a)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hB hbx hn hr hr2 hBl hBh hAl hAh h7a hWA hWB hWF ⊢
  subst hbx
  have hB' : (rax == 0#64) = false := beq_eq_false_iff_ne.2 hB
  have hWFW : ∀ a : Addr, rbp.toNat - 80 ≤ a.toNat → a.toNat < rbp.toNat + 8 → Foot Wl a :=
    fun a h1 h2 => (hWF a h1 h2).1
  have hWFD : ∀ a : Addr, rbp.toNat - 80 ≤ a.toNat → a.toNat < rbp.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hWF a h1 h2).2
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    hwx [W_153, W_168, o4, o5, Op.sta, Op.stia, Op.cmpmi, hB']
    ipeelx (rbp + 18446744073709551560#64)
    hwx [hn]
    icl
  all_goals first
    | (ireg hWA) | (ireg hWB) | (ireg hWFW) | (ireg hWFD) | (ireg hW7a) | (ireg hWb)
    | (ipeel; iself)
    | (intro a ha; iout)
    | skip

/-- The arguments of `memset (r15 + 0x28, 0, r13)`. -/
theorem vc_267 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_267 F Wl (fun j' g' _ V' => j' = 276 ∧ g' = { g with rdx := g.r13, rsi := 0#64, rdi := g.r15 + 40#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  hwx [W_267, o6]
  icl

/-- After the `memset` of element `i`: the last directory (`i = 3`, to 384) or not (to 293). -/
theorem vc_281 {g : Gprs} {f : Rflags} {V : Addr → Byte} {i : Nat} (hi : i ≤ 3)
    (hr : g.r12 = BitVec.ofNat 64 (7364032 + 8 * i)) :
    W_281 F Wl (fun j' g' _ V' => V' = V ∧ g' = { g with rax := 7364056#64 } ∧
      j' = if i = 3 then 384 else 293) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr ⊢
  subst hr
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals
    hwx [W_281, o7]
    icl

/-- The strings of the system directories after the first, `sA i` that of element `i + 1` (`sA 3` past the last). -/
def sA : Nat → Nat
  | 0 => 7364087
  | 1 => 7364114
  | 2 => 7364120
  | _ => 7364130

/-- Their lengths (at `0x705dc8 + 8 i`). -/
def lA : Nat → Nat
  | 0 => 26
  | 1 => 5
  | _ => 9

theorem sA_le (i : Nat) : sA i ≤ 7364130 := by
  unfold sA; split <;> omega

theorem sA_ge (i : Nat) : 7364087 ≤ sA i := by
  unfold sA; split <;> omega

/-- From the `memset` of element `i < 3` (at `r15`) to that of element `i + 1` (at `r15 + 40 q`): the pointers to it
(`A[i + 1]`, the `next` of element `i`), its name (`sA i`, starting with `/`) and length, back to 267. -/
theorem vc_293 {g : Gprs} {f : Rflags} {V : Addr → Byte} {i n q : Nat} (hq : n = 8 ∧ q = 2 ∨ n = 16 ∧ q = 3)
    (hi : i < 3) (hr12 : g.r12 = BitVec.ofNat 64 (7364032 + 8 * i)) (hbx : g.rbx = BitVec.ofNat 64 (sA i))
    (h72 : rdq(V, g.rbp + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q))
    (h64 : rdq(V, g.rbp + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q))
    (h56 : rdq(V, g.rbp + 18446744073709551560#64) = BitVec.ofNat 64 n)
    (hlen : rdq(V, BitVec.ofNat 64 (7364040 + 8 * i)) = BitVec.ofNat 64 (lA i))
    (hsl : ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 (sA i)) 1)) = 47#8)
    (hr : 7940480 + 88 ≤ g.rbp.toNat) (hr2 : g.rbp.toNat + 16 ≤ 2 ^ 64)
    (hBl : 7940480 ≤ g.r15.toNat) (hBh : g.r15.toNat + 40 * q + 40 ≤ g.rbp.toNat - 88)
    (hAl : 7940480 ≤ g.r14.toNat) (hAh : g.r14.toNat + 8 ≤ g.rbp.toNat - 88)
    (hWA : ∀ a : Addr, g.r14.toNat ≤ a.toNat → a.toNat < g.r14.toNat + 8 → Foot Wl a)
    (hWB : ∀ a : Addr, g.r15.toNat ≤ a.toNat → a.toNat < g.r15.toNat + 40 * q + 40 → Foot Wl a)
    (hFD : ∀ a : Addr, g.rbp.toNat - 80 ≤ a.toNat → a.toNat < g.rbp.toNat → Foot F.data a)
    (hFR : ∀ a : Addr, 7364040 ≤ a.toNat → a.toNat < 7364131 → Foot F.data a) :
    W_293 F Wl (fun j' g' _ V' => j' = 267 ∧ g'.r15 = g.r15 + BitVec.ofNat 64 (40 * q) ∧ g'.r14 = g.r14 + 8#64 ∧
      g'.r12 = BitVec.ofNat 64 (7364040 + 8 * i) ∧ g'.rbx = BitVec.ofNat 64 (sA (i + 1)) ∧ g'.r13 = g.r13 ∧
      g'.rbp = g.rbp ∧ g'.rsp = g.rsp ∧
      (∀ a : Addr, (a.toNat < 7940480 ∨ g.rbp.toNat - 88 ≤ a.toNat) → V' a = V a)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr12 hbx h72 h64 h56 hr hr2 hBl hBh hAl hAh hWA hWB hFD ⊢
  have e12 : r12 + 8#64 = BitVec.ofNat 64 (7364040 + 8 * i) := by
    rw [hr12]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hs1 := sA_ge i
  have hs2 := sA_le i
  have hbxn : rbx.toNat = sA i := by rw [hbx]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  rw [← hbx] at hsl
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow] at h72 h64 h56 hBh hWB ⊢
    hwx [W_293, W_362, o8, o9, Op.cmpmi, BitVec.add_zero, h72, h64, e12]
    ipeel
    hwx [hlen, hsl, h56]
    icl
  all_goals first
    | (ireg hWA) | (ireg hWB) | (ireg hFD) | (ireg hFR)
    | (intro a ha; iout)
    | ((rw [hbx]; obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega) <;> rfl)
    | skip

/-- The ends of the lists (`r15` the last element, `r14` the last slot of `A`), `llp` null (`r - 0x50`):
`_dl_init_paths` returns (450), the registers the prologue pushed popped. -/
theorem vc_384 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hllp : rdq(V, g.rbp + 18446744073709551536#64) = 0#64)
    (hr : 7940480 + 88 ≤ g.rbp.toNat) (hr2 : g.rbp.toNat + 16 ≤ 2 ^ 64)
    (hBl : 7940480 ≤ g.r15.toNat) (hBh : g.r15.toNat + 8 ≤ g.rbp.toNat - 88)
    (hAl : 7940480 ≤ g.r14.toNat) (hAh : g.r14.toNat + 8 ≤ g.rbp.toNat - 88) (h7a : 8014928 ≤ g.rbp.toNat - 88)
    (hWA : ∀ a : Addr, g.r14.toNat ≤ a.toNat → a.toNat < g.r14.toNat + 8 → Foot Wl a)
    (hWB : ∀ a : Addr, g.r15.toNat ≤ a.toNat → a.toNat < g.r15.toNat + 8 → Foot Wl a)
    (hW7a : ∀ a : Addr, 8014920 ≤ a.toNat → a.toNat < 8014928 → Foot Wl a)
    (hWb : ∀ a : Addr, 7937712 ≤ a.toNat → a.toNat < 7937720 → Foot Wl a)
    (hFD : ∀ a : Addr, g.rbp.toNat - 80 ≤ a.toNat → a.toNat < g.rbp.toNat + 8 → Foot F.data a) :
    W_384 F Wl (fun j' g' _ V' => j' = 450 ∧ g'.rsp = g.rbp + 8#64 ∧
      g'.rbx = rdq(V, g.rbp + 18446744073709551576#64) ∧ g'.r12 = rdq(V, g.rbp + 18446744073709551584#64) ∧
      g'.r13 = rdq(V, g.rbp + 18446744073709551592#64) ∧ g'.r14 = rdq(V, g.rbp + 18446744073709551600#64) ∧
      g'.r15 = rdq(V, g.rbp + 18446744073709551608#64) ∧ g'.rbp = rdq(V, g.rbp) ∧
      (∀ a : Addr, (a.toNat < 7937712 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ g.rbp.toNat - 88 ≤ a.toNat) →
        V' a = V a)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hllp hr hr2 hBl hBh hAl hAh hWA hWB hFD ⊢
  hwx [W_384, W_416, W_425, o11, o12, o13, Op.cmpmi, Op.stia, hllp]
  ipeel
  icl
  all_goals first
    | (ireg hWA) | (ireg hWB) | (ireg hW7a) | (ireg hWb) | (ireg hFD)
    | (intro a ha; iout)
    | skip

end FV7z.Ipa
