import FV7z.Npc.Cuts
import FV7z.Mys.Lem
/-!
# `_nl_postload_ctype ()` (PLAN.md §M, M1)

glibc 2.31's `_nl_postload_ctype` at `0x67df40` in `7zzs` (`locale/lc-ctype.c`; `objdump -d`): `Lc` =
`_nl_global_locale.__locales[LC_CTYPE]` (the word at `0x7922c0`); the three table pointers `L->values[…]` (at
`L + 64`, `L + 88`, `L + 72`) plus 128 entries (`ca`, `cb`, `cc`) into `_nl_global_locale.__ctype_b`, `__ctype_toupper`,
`__ctype_tolower` (`0x792328`, `0x792330`, `0x792338`: `V3`); if the thread's locale (`fs:-0x80`) is
`&_nl_global_locale` (`0x7922c0`), the same into the thread's `__libc_tsd_CTYPE_B`, `…_TOUPPER`, `…_TOLOWER`
(`fs:-0x30`, `fs:-0x38`, `fs:-0x40`: `V6`), the `ret` (121); else the `ret` (84). No `call`, no frame.

- `ret_84`, `ret_121`: the instructions outside the blocks.
- `Lc`, `ca`, `cb`, `cc`, `V3`, `Gt`, `V6`, `Vf`: the values, the bytes after the global stores, the test, the bytes
  after the thread's stores, the bytes at the `ret`.
- `vc_0`, `vc_25`, `vc_44`, `vc_78e`, `vc_78n`: the pieces; `npc_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Npc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `ret`s (84, 121). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_84 : pret <+: npc.drop 84 := by decide +kernel
theorem ret_84 (feat : Features) : Dec feat npc 84 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 84) (k := 0) (pret_0 feat) w_84 (Nat.zero_le _)
theorem w_121 : pret <+: npc.drop 121 := by decide +kernel
theorem ret_121 (feat : Features) : Dec feat npc 121 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 121) (k := 0) (pret_0 feat) w_121 (Nat.zero_le _)

/-! ## The values and the bytes -/

/-- `_nl_global_locale.__locales[LC_CTYPE]`. -/
abbrev Lc (V : Addr → Byte) : Addr := rdq(V, 7938752#64)
/-- `__ctype_b`: `L->values[_NL_CTYPE_CLASS]` + 128 entries of 2 bytes. -/
abbrev ca (V : Addr → Byte) : BitVec 64 := rdq(V, Lc V + 64#64) + 256#64
/-- `__ctype_toupper`: `L->values[_NL_CTYPE_TOUPPER]` + 128 entries of 4 bytes. -/
abbrev cb (V : Addr → Byte) : BitVec 64 := rdq(V, Lc V + 88#64) + 512#64
/-- `__ctype_tolower`: `L->values[_NL_CTYPE_TOLOWER]` + 128 entries of 4 bytes. -/
abbrev cc (V : Addr → Byte) : BitVec 64 := rdq(V, Lc V + 72#64) + 512#64

/-- The bytes after the three global stores. -/
abbrev V3 (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V 7938856#64 (toBytesLE (ca V) 8)) 7938864#64 (toBytesLE (cb V) 8)) 7938872#64
    (toBytesLE (cc V) 8)

/-- The thread's locale is the global one. -/
abbrev Gt (fb : Addr) (V : Addr → Byte) : Prop := rdq(V3 V, fb + 18446744073709551488#64) = 7938752#64

/-- The bytes after the thread's three stores too. -/
abbrev V6 (fb : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (V3 V) (fb + 18446744073709551568#64) (toBytesLE (ca V) 8)) (fb + 18446744073709551560#64)
    (toBytesLE (cc V) 8)) (fb + 18446744073709551552#64) (toBytesLE (cb V) 8)

/-- The bytes at the `ret`. -/
def Vf (fb : Addr) (V : Addr → Byte) : Addr → Byte := if Gt fb V then V6 fb V else V3 V

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rdx, [0x7922c0]; mov rdi, -0x80; lea rsi, [0x7922c0]`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add 7938752#64 i))
    (h : ∀ fl, Q 25 { g with rdx := Lc V, rdi := 18446744073709551488#64, rsi := 7938752#64 } fl V) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.lda]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact f0
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- The three loads from `L` (`rdx`), `rcx` = the first + 256. -/
theorem vc_25 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rdx + 64#64) i))
    (f88 : ∀ i < 8, Foot F.data (Addr.add (g.rdx + 88#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (g.rdx + 72#64) i))
    (h : ∀ fl, Q 44
      { g with rax := rdq(V, g.rdx + 88#64), rcx := rdq(V, g.rdx + 64#64) + 256#64,
        rdx := rdq(V, g.rdx + 72#64) } fl V) :
    W_25 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f64 f88 f72 h ⊢
  wpx [W_25, o1]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact f64
    | with_reducible exact f88
    | with_reducible exact f72
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- The three global stores (`rax`, `rdx` + 512 first). -/
theorem vc_44 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w1 : ∀ i < 8, Foot Wl (Addr.add 7938856#64 i)) (w2 : ∀ i < 8, Foot Wl (Addr.add 7938864#64 i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add 7938872#64 i))
    (h : ∀ fl, Q 78 { g with rax := g.rax + 512#64, rdx := g.rdx + 512#64 } fl
      (Vst (Vst (Vst V 7938856#64 (toBytesLE g.rcx 8)) 7938864#64 (toBytesLE (g.rax + 512#64) 8)) 7938872#64
        (toBytesLE (g.rdx + 512#64) 8))) :
    W_44 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_44, o2, Op.sta]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact w1
    | with_reducible exact w2
    | with_reducible exact w3
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- `cmp fs:[rdi], rsi`, equal: the thread's three stores, to the `ret` at 121. -/
theorem vc_78e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + g.rdi) i))
    (he : rdq(V, fb + g.rdi) = g.rsi)
    (w4 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551568#64) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551560#64) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551552#64) i))
    (h : ∀ fl, Q 121
      { g with rsi := 18446744073709551568#64, rcx := 18446744073709551560#64,
        rdx := 18446744073709551552#64 } fl
      (Vst (Vst (Vst V (fb + 18446744073709551568#64) (toBytesLE g.rcx 8)) (fb + 18446744073709551560#64)
        (toBytesLE g.rdx 8)) (fb + 18446744073709551552#64) (toBytesLE g.rax 8))) :
    W_78 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fc he h ⊢
  have d := decide_eq_true he
  wpx [W_78, o3, W_88, o4, Op.cmpmrf, Op.stf, d, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact fc
    | with_reducible exact w4
    | with_reducible exact w5
    | with_reducible exact w6
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- `cmp fs:[rdi], rsi`, not equal: to the `ret` at 84. -/
theorem vc_78n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + g.rdi) i))
    (he : ¬ rdq(V, fb + g.rdi) = g.rsi)
    (h : ∀ fl, Q 84 g fl V) :
    W_78 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fc he h ⊢
  have d := decide_eq_false he
  wpx [W_78, o3, Op.cmpmrf, d, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact fc
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L' : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `_nl_postload_ctype ()` from its entry (`X`'s registers, `fb` the `fs` base): `L`'s three words, the word at
`0x7922c0`, the thread's locale and the return address readable; the three global words and the thread's three
writable. At the return address (`kr`): the bytes `Vf` (`hra`: the return address read from them), the registers a
call keeps (`Str.Back`). -/
theorem npc_ok {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L' s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L' npc_at npc)
    (hin₂ : CodeIn L' e₂ code₂) (h₂ : j₂ < code₂.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = npc_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add 7938752#64 i))
    (f64 : ∀ i < 8, Foot F.data (Addr.add (Lc V + 64#64) i))
    (f88 : ∀ i < 8, Foot F.data (Addr.add (Lc V + 88#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (Lc V + 72#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add 7938856#64 i)) (w2 : ∀ i < 8, Foot Wl (Addr.add 7938864#64 i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add 7938872#64 i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551488#64) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551568#64) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551560#64) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551552#64) i))
    (hra : rdq(Vf fb V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vf fb V) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L' o gev gP gE Z t') :
    GoG prof L' o gev gP gE X t := by
  have hr0 : X.cpu.rip = npc_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 25 ∧ V' = V ∧
      g' = { X.cpu.gpr with rdx := Lc V, rdi := 18446744073709551488#64, rsi := 7938752#64 })
    hK hA hr0 (vc_0 f0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, rfl⟩ U t₁ hKU hAU hrU hgU -
  rw [hV₁] at hAU
  refine (c_25 prof fb).run c hfs hin (fun j' g' _ V' => j' = 44 ∧ V' = V ∧
      g' =
        { X.cpu.gpr with rax := rdq(V, Lc V + 88#64), rcx := ca V, rdx := rdq(V, Lc V + 72#64),
          rdi := 18446744073709551488#64, rsi := 7938752#64 })
    hKU hAU hrU (vc_25 (g := U.cpu.gpr) (by rw [hgU]; exact f64) (by rw [hgU]; exact f88) (by rw [hgU]; exact f72)
      (by rw [hgU]; exact fun _ => ⟨rfl, rfl, rfl⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, hV₂, rfl⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
  rw [hV₂] at hAU₂
  refine (c_44 prof fb).run c hfs hin (fun j' g' _ V' => j' = 78 ∧ V' = V3 V ∧
      g' =
        { X.cpu.gpr with rax := cb V, rcx := ca V, rdx := cc V, rdi := 18446744073709551488#64,
          rsi := 7938752#64 })
    hKU₂ hAU₂ hrU₂ (vc_44 (g := U₂.cpu.gpr) w1 w2 w3 (by rw [hgU₂]; exact fun _ => ⟨rfl, rfl, rfl⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, hV₃, rfl⟩ U₃ t₃ hKU₃ hAU₃ hrU₃ hgU₃ -
  rw [hV₃] at hAU₃
  by_cases he : Gt fb V
  · have hf : Vf fb V = V6 fb V := by rw [Vf, if_pos he]
    refine (c_78 prof fb).run c hfs hin (fun j' g' _ V' => j' = 121 ∧ V' = V6 fb V ∧
        g' =
          { X.cpu.gpr with rax := cb V, rcx := 18446744073709551560#64, rdx := 18446744073709551552#64,
            rdi := 18446744073709551488#64, rsi := 18446744073709551568#64 })
      hKU₃ hAU₃ hrU₃
      (vc_78e (g := U₃.cpu.gpr) (by rw [hgU₃]; exact fc) (by rw [hgU₃]; exact he) (by rw [hgU₃]; exact w4)
        (by rw [hgU₃]; exact w5) (by rw [hgU₃]; exact w6) (by rw [hgU₃]; exact fun _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₄, rfl⟩ U₄ t₄ hKU₄ hAU₄ hrU₄ hgU₄ -
    rw [hV₄, ← hf] at hAU₄
    have hkp : Kp X.cpu.gpr U₄.cpu.gpr := by rw [hgU₄]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ret_back c hin (lt_len (by decide)) (ret_121 _) hKU₄ hAU₄ hrU₄ hkp hl hin₂ h₂ hra
      fun Z t' hK' hA' hr' hb _ => kr Z t' hK' hA' hr' hb
  · have hf : Vf fb V = V3 V := by rw [Vf, if_neg he]
    refine (c_78 prof fb).run c hfs hin (fun j' g' _ V' => j' = 84 ∧ V' = V3 V ∧
        g' =
          { X.cpu.gpr with rax := cb V, rcx := ca V, rdx := cc V, rdi := 18446744073709551488#64,
            rsi := 7938752#64 })
      hKU₃ hAU₃ hrU₃
      (vc_78n (g := U₃.cpu.gpr) (by rw [hgU₃]; exact fc) (by rw [hgU₃]; exact he)
        (by rw [hgU₃]; exact fun _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₄, rfl⟩ U₄ t₄ hKU₄ hAU₄ hrU₄ hgU₄ -
    rw [hV₄, ← hf] at hAU₄
    have hkp : Kp X.cpu.gpr U₄.cpu.gpr := by rw [hgU₄]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ret_back c hin (lt_len (by decide)) (ret_84 _) hKU₄ hAU₄ hrU₄ hkp hl hin₂ h₂ hra
      fun Z t' hK' hA' hr' hb _ => kr Z t' hK' hA' hr' hb

end FV7z.Npc
