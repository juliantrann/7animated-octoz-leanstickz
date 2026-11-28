import FV7z.Mbu.Cuts
import FV7z.U8u.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `MultiByteToUnicodeString2`: the empty and the UTF-8 paths (PLAN.md §M, M1)

7-Zip 26.06's `MultiByteToUnicodeString2 (dest, src, codePage)` at `0x450a60` in `7zzs`
(`CPP/Common/StringConvert.cpp`), `S` the stack pointer at the entry: `r13`, `r12`, `rbp`, `rbx` pushed, a frame of
40 bytes (`gq S`) with the stack guard (`fs:0x28`) at `gq S + 24`; `rbx` = `dest._chars` (`d`), `dest._len` = 0
(the 4 bytes at `dest + 8`), `n` = `src._len` (the 4 bytes at `src + 8`), `d [0]` = 0 (`dest.Empty ()`). For `n` = 0
(the `je` at 51) to 400. Else `rbp` = `dest`, `r12` = `src`; for `codePage` = `CP_UTF8` (65001, the `je` at 69) or
`g_ForceToUTF8` (the byte at `0x792178`, the `jne` at 85) `ConvertUTF8ToUnicode (src, dest)` (432: `rsi` = `dest`,
`rdi` = `src`, the `call` at 438 to `U8u.u8u_at`), back at 443 to 400. At 400 the stack guard checked, the frame
dropped, the registers popped and `ret` (426).

The callee is a hypothesis, as in `FV7z/Guv/Holds.lean`: a continuation at its entry (`kfu`) given the run from its
return (with the frame `Fr` as it was, and its post `P`).

- `gq`: the frame; `Vp`, `Vg`, `Vd`, `VE`: the bytes after the pushes, the stack guard's store, `dest._len` = 0, `d [0]`
  = 0; `Fr`: the stack guard, the saved registers and the return address in the bytes.
- `vc_*`: the verification conditions of the pieces; `mbu_tail`: from 400 to the return address.
- `mbu_u8`: from the entry, for `n` = 0 (`kr0`) or for `CP_UTF8` or `g_ForceToUTF8` through the callee (`kr1`), to the
  return address with `eax` = 0 and `rbx`, `rbp`, `r12`, `r13`, `rsp` restored.

Not covered yet: the path through `mbstowcs` (106 on), the stack guard failing (`__stack_chk_fail`, 495).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mbu

/-- The `call` to `ConvertUTF8ToUnicode`. -/
def pcu : List Byte := [0xe8, 0xe5, 0x13, 0x00, 0x00]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 5093] 5) := by dec_rfl
theorem wc_438 : pcu <+: mbu.drop 438 := by decide +kernel
theorem call_438 (feat : Features) : Dec feat mbu 438 (FV7z.mk .call 64 [.rel 5093] 5) :=
  Dec.shift (j := 438) (k := 0) (pcu_0 feat) wc_438 (Nat.zero_le _)
theorem tgt_438 : mbu_at.add (438 + 5) + BitVec.ofNat 64 5093 = U8u.u8u_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_426 : pret <+: mbu.drop 426 := by decide +kernel
theorem ret_426 (feat : Features) : Dec feat mbu 426 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 426) (k := 0) (pret_0 feat) w_426 (Nat.zero_le _)

/-- The frame: `rsp` after the four pushes and `sub rsp, 0x28`. -/
abbrev gq (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 40#64

/-- The bytes after the pushes of `r13`, `r12`, `rbp`, `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the stack guard `cn` is stored at `gq S + 24`. -/
abbrev Vg (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vp V g) (gq g.rsp + 24#64) (toBytesLE cn 8)

/-- The bytes after `dest._len` = 0. -/
abbrev Vd (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vg V g cn) (g.rdi + 8#64) (toBytesLE 0#32 4)

/-- The bytes after `d [0]` = 0. -/
abbrev VE (V : Addr → Byte) (g : Gprs) (cn d : BitVec 64) : Addr → Byte :=
  Vst (Vd V g cn) d (toBytesLE 0#32 4)

/-- The frame in the bytes: the stack guard as at `fs:0x28`, the saved registers of `g₀`, the return address `ra`. -/
def Fr (S fb : Addr) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop :=
  rdq(V, gq S + 24#64) = rdq(V, fb + 40#64) ∧ rdq(V, S - 8) = g₀.r13 ∧ rdq(V, S - 8 - 8) = g₀.r12 ∧
    rdq(V, S - 8 - 8 - 8) = g₀.rbp ∧ rdq(V, S - 8 - 8 - 8 - 8) = g₀.rbx ∧ rdq(V, S) = ra

theorem g40 (x : Addr) : gq x + 40#64 = x - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a4s (x : Addr) : x - 8 - 8 - 8 - 8 + 8 = x - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- From the entry: the pushes, the stack guard stored, `rbx` = `d`, `dest._len` = 0, `eax` = `n`, `d [0]` = 0; for
`n` = 0 to 400, else on to 57. -/
theorem vc_0 {Q : Post} {cn d : BitVec 64} {n : BitVec 32}
    (hcn : rdq(Vp V g, fb + 40#64) = cn) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hd : rdq(Vp V g, g.rdi) = d) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hn : rdd(Vd V g cn, g.rsi + 8#64) = n) (fs8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq g.rsp + 24#64) i))
    (wd8 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i)) (wb : ∀ i < 4, Foot Wl (Addr.add d i))
    (hZ : n = 0#32 → ∀ ra fl, Q 400 { g with rax := ra, rbx := d, rsp := gq g.rsp } fl (VE V g cn d))
    (hN : n ≠ 0#32 → ∀ ra fl, W_57 fb F Wl Q { g with rax := ra, rbx := d, rsp := gq g.rsp } fl (VE V g cn d)) :
    W_0 fb F Wl Q g f V := by
  by_cases hz : n = 0#32
  · have e : (n == 0) = true := beq_iff_eq.2 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Vp, Vg, Vd, VE, gq] at hcn hd hn fa fs8 w1 w2 w3 w4 w5 wd8 hZ ⊢
    wpx [W_0, o0, Op.ldf, hcn, hd, hn, e, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true]
    all_goals repeat' (first
      | exact hZ hz _ _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)
  · have e : (n == 0) = false := beq_eq_false_iff_ne.2 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Vp, Vg, Vd, VE, gq] at hcn hd hn fa fs8 w1 w2 w3 w4 w5 wd8 hN ⊢
    wpx [W_0, o0, Op.ldf, hcn, hd, hn, e, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true]
    all_goals repeat' (first
      | exact hN hz _ _
      | with_reducible assumption
      | exact trivial
      | apply And.intro
      | intro _)

/-- 57: `rbp` = `dest`, `r12` = `src`; for `CP_UTF8` or `g_ForceToUTF8` to 432, else on to 91. -/
theorem vc_57 {Q : Post} (fg : ∀ i < 1, Foot F.data (Addr.add 7938424#64 i))
    (hU : ∀ rd fl, (g.rdx.setWidth 32 = 65001#32 ∨ V 7938424#64 ≠ 0#8) →
      Q 432 { g with rdx := rd, rbp := g.rdi, r12 := g.rsi } fl V)
    (hN : ∀ fl, g.rdx.setWidth 32 ≠ 65001#32 → V 7938424#64 = 0#8 →
      W_91 fb F Wl Q { g with rdx := 7938424#64, rbp := g.rdi, r12 := g.rsi } fl V) :
    W_57 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hU hN ⊢
  by_cases hu : BitVec.setWidth 32 rdx = 65001#32
  · have e : decide (BitVec.setWidth 32 rdx = 65001#32) = true := decide_eq_true hu
    wpx [W_57, o1, e, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true]
    all_goals repeat' (first
      | exact hU _ _ (Or.inl hu)
      | exact trivial
      | apply And.intro
      | intro _)
  · have e : decide (BitVec.setWidth 32 rdx = 65001#32) = false := decide_eq_false hu
    by_cases hb : V 7938424#64 = 0#8
    · have eb : decide (V 7938424#64 = 0#8) = true := decide_eq_true hb
      wpx [W_57, W_75, o1, o2, Op.cmpmi, Tun.rd1, e, eb, hb, decide_true, decide_false, Bool.not_true,
        Bool.not_false, Bool.false_eq_true,
        Bool.true_eq_false, false_implies, true_implies, implies_true]
      all_goals repeat' (first
        | exact hN _ hu hb
        | with_reducible assumption
        | exact trivial
        | apply And.intro
        | intro _)
    · have eb : decide (V 7938424#64 = 0#8) = false := decide_eq_false hb
      wpx [W_57, W_75, o1, o2, Op.cmpmi, Tun.rd1, e, eb, hb, decide_true, decide_false, Bool.not_true,
        Bool.not_false, Bool.false_eq_true,
        Bool.true_eq_false, false_implies, true_implies, implies_true]
      all_goals repeat' (first
        | exact hU _ _ (Or.inr hb)
        | with_reducible assumption
        | exact trivial
        | apply And.intro
        | intro _)

/-- 432: `rsi` = `dest`, `rdi` = `src`, to the `call` at 438. -/
theorem vc_432 :
    W_432 fb F Wl (fun j' g' _ V' => j' = 438 ∧ g' = { g with rsi := g.rbp, rdi := g.r12 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_432, o26]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- 443: the `jmp` to 400. -/
theorem vc_443 : W_443 fb F Wl (fun j' g' _ V' => j' = 400 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_443
  exact ⟨rfl, rfl, rfl⟩

/-- From 400: the stack guard checked, the frame dropped, the pops, to the `ret` at 426. -/
theorem vc_400 {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 426
      { g with
          rax := 0#64,
          rbx := rdq(V, g.rsp + 40#64),
          rbp := rdq(V, g.rsp + 40#64 + 8),
          rsp := g.rsp + 40#64 + 8 + 8 + 8 + 8,
          r12 := rdq(V, g.rsp + 40#64 + 8 + 8),
          r13 := rdq(V, g.rsp + 40#64 + 8 + 8 + 8) } fl V) :
    W_400 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 l1 l2 l3 l4 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_400, W_416, o24, o25, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The paths -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 400 with `rsp` the frame of `S` and the frame `Fr` in the bytes: to the return address with `eax` = 0 and the
saved registers of `g₀` restored. -/
theorem mbu_tail {fb S : Addr} {g₀ : Gprs} {W : State} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mbu_at mbu) (hK : KeptW Wl s₀ W) (hA : Agree F W.proc.mm.mem V)
    (hrip : W.cpu.rip = mbu_at.add 400) (hs : W.cpu.gpr.rsp = gq S)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hF : Fr S fb g₀ (e₂.add j₂) V) (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (w4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq S + 24#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := 0#64,
          rbx := g₀.rbx,
          rbp := g₀.rbp,
          rsp := S + 8,
          r12 := g₀.r12,
          r13 := g₀.r13 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE W t := by
  unfold Fr at hF
  obtain ⟨hc, h1, h2, h3, h4, hr⟩ := hF
  have f24 : ∀ i < 8, Foot F.data (Addr.add (gq S + 24#64) i) := fun i hi => c.hws _ (w5 i hi)
  have l4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (w4 i hi)
  have l3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i) := fun i hi => c.hws _ (w3 i hi)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i) := fun i hi => c.hws _ (w2 i hi)
  have l1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i) := fun i hi => c.hws _ (w1 i hi)
  refine (c_400 prof fb).run c hfs hin (fun j' g' _ V' => j' = 426 ∧
      g' = { W.cpu.gpr with
          rax := 0#64,
          rbx := g₀.rbx,
          rbp := g₀.rbp,
          rsp := S,
          r12 := g₀.r12,
          r13 := g₀.r13 } ∧ V' = V) hK hA hrip
    (vc_400 (by rw [hs]; exact hc) (by rw [hs]; exact f24) fc (by rw [hs, g40]; exact l4)
      (by rw [hs, g40, a4s]; exact l3) (by rw [hs, g40, a4s, a3s]; exact l2)
      (by rw [hs, g40, a4s, a3s, a2s]; exact l1)
      fun _ => ⟨rfl, by rw [hs, g40, a4s, a3s, a2s, a1s, h4, h3, h2, h1], rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = S := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_426 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr) ?_
  rintro Z' t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hgU]
  try rfl

/-- `MultiByteToUnicodeString2 (dest, src, codePage)` (`rdi`, `rsi`, `edx`) from its entry, the stack guard `cn`,
`d` = `dest._chars` and `n` = `src._len` as read, for `n` = 0, `codePage` = `CP_UTF8` or `g_ForceToUTF8` not 0. For
`n` = 0 with the frame in the bytes `VE` (`hFE`) the run reaches the return address (`kr0`); else at
`ConvertUTF8ToUnicode`'s entry the registers have `rsi` = `dest`, `rdi` = `src` and the return address
`mbu_at + 443` pushed (`kfu`); if that returns with `rsp` the frame and the frame in the bytes, the run reaches the
return address with `eax` = 0 and `rbx`, `rbp`, `r12`, `r13`, `rsp` restored (`kr1`). -/
theorem mbu_u8 {fb : Addr} {cn d : BitVec 64} {n : BitVec 32} {P : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbu_at mbu)
    (hinU : CodeIn L U8u.u8u_at U8u.u8u)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mbu_at)
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fg : ∀ i < 1, Foot F.data (Addr.add 7938424#64 i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp + 24#64) i))
    (wd8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i)) (wb : ∀ i < 4, Foot Wl (Addr.add d i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (gq X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcn : rdq(Vp V X.cpu.gpr, fb + 40#64) = cn) (hd : rdq(Vp V X.cpu.gpr, X.cpu.gpr.rdi) = d)
    (hn : rdd(Vd V X.cpu.gpr cn, X.cpu.gpr.rsi + 8#64) = n)
    (hp : n = 0#32 ∨ X.cpu.gpr.rdx.setWidth 32 = 65001#32 ∨ VE V X.cpu.gpr cn d 7938424#64 ≠ 0#8)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hFE : n = 0#32 → Fr X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) (VE V X.cpu.gpr cn d))
    (kr0 : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (VE V X.cpu.gpr cn d) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kfu : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VE V X.cpu.gpr cn d) (gq X.cpu.gpr.rsp - 8) (toBytesLE (mbu_at.add 443) 8)) →
      Y.cpu.rip = U8u.u8u_at →
      (∃ ra rd, Y.cpu.gpr = ({ X.cpu.gpr with
          rax := ra,
          rdx := rd,
          rbx := d,
          rsp := gq X.cpu.gpr.rsp,
          rbp := X.cpu.gpr.rdi,
          rsi := X.cpu.gpr.rdi,
          rdi := X.cpu.gpr.rsi,
          r12 := X.cpu.gpr.rsi }).set 4 (gq X.cpu.gpr.rsp - 8)) →
      (∀ (W : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem V'' →
        W.cpu.rip = mbu_at.add 443 → W.cpu.gpr.rsp = gq X.cpu.gpr.rsp →
        Fr X.cpu.gpr.rsp fb X.cpu.gpr (e₂.add j₂) V'' → P W V'' → GoG prof L o gev gP gE W t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (W : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P W V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { W.cpu.gpr with
          rax := 0#64,
          rbx := X.cpu.gpr.rbx,
          rbp := X.cpu.gpr.rbp,
          rsp := X.cpu.gpr.rsp + 8,
          r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = mbu_at.add 0 := by rw [addr_add_zero]; exact hrip
  rcases Classical.em (n = 0#32) with hz | hz
  · -- `n` = 0: to 400
    refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 400 ∧
        (∃ ra, g' = { X.cpu.gpr with rax := ra, rbx := d, rsp := gq X.cpu.gpr.rsp }) ∧
        V' = VE V X.cpu.gpr cn d) hK hA hrip'
      (vc_0 hcn fc hd fa hn fs8 w1 w2 w3 w4 w5 wd8 wb (fun _ ra _ => ⟨rfl, ⟨ra, rfl⟩, rfl⟩)
        (fun h => absurd hz h)) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨ra, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact mbu_tail c hfs hin hKY hAY hrY (by rw [hgY]) hin₂ h₂ (hFE hz) fc w1 w2 w3 w4 w5 hl
      fun Z' t' hKZ hAZ hrZ hgZ => kr0 Z' t' hKZ hAZ hrZ (by rw [hgZ, hgY]; try rfl)
  -- `CP_UTF8` or `g_ForceToUTF8`: to 432
  have hu : X.cpu.gpr.rdx.setWidth 32 = 65001#32 ∨ VE V X.cpu.gpr cn d 7938424#64 ≠ 0#8 := by
    rcases hp with h | h
    · exact absurd h hz
    · exact h
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 432 ∧
      (∃ ra rd, g' = { X.cpu.gpr with
          rax := ra,
          rdx := rd,
          rbx := d,
          rsp := gq X.cpu.gpr.rsp,
          rbp := X.cpu.gpr.rdi,
          r12 := X.cpu.gpr.rsi }) ∧ V' = VE V X.cpu.gpr cn d) hK hA hrip'
    (vc_0 hcn fc hd fa hn fs8 w1 w2 w3 w4 w5 wd8 wb (fun h => absurd h hz)
      fun _ ra _ => vc_57 fg (fun rd _ _ => ⟨rfl, ⟨ra, rd, rfl⟩, rfl⟩)
        fun _ h1 h2 => absurd hu (by
          intro h
          rcases h with h | h
          · exact h1 h
          · exact h h2)) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨ra, rd, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine (c_432 prof fb).run c hfs hin (fun j' g' _ V' => j' = 438 ∧
      g' = { Y.cpu.gpr with rsi := Y.cpu.gpr.rbp, rdi := Y.cpu.gpr.r12 } ∧ V' = VE V X.cpu.gpr cn d)
    hKY hAY hrY vc_432 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₁
  have hs₂ : Y₂.cpu.gpr.rsp = gq X.cpu.gpr.rsp := by rw [hg₂, hgY]
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_438 _) hinU (U8u.lt_len (j := 0) (by decide)) tgt_438
    (by rw [hs₂]; exact w6) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hs₂] at hA₃
  refine kfu Y₃ t₃ hK₃ hA₃ hr₃ ⟨ra, rd, by rw [hg₃, hg₂, hgY]; try rfl⟩ ?_
  -- back from `ConvertUTF8ToUnicode`
  intro W V'' t'' hKW hAW hrW hsW hFW hPW
  refine (c_443 prof fb).run c hfs hin (fun j' g' _ V' => j' = 400 ∧ g' = W.cpu.gpr ∧ V' = V'') hKW hAW hrW
    vc_443 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst V₁
  exact mbu_tail c hfs hin hK₄ hA₄ hr₄ (by rw [hg₄]; exact hsW) hin₂ h₂ hFW fc w1 w2 w3 w4 w5 hl
    fun Z' t' hKZ hAZ hrZ hgZ => kr1 W V'' Z' t' hPW hKZ hAZ hrZ (by rw [hgZ, hg₄]; try rfl)

end FV7z.Mbu
