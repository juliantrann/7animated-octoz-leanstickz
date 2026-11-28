import FV7z.Sse.Cuts
import FV7z.Gdt.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
/-!
# `CPU_IsSupported_SSE41 ()` (PLAN.md §M, M1)

7-Zip 26.06's `CPU_IsSupported_SSE41 ()` at `0x424390` in `7zzs` (`C/CpuArch.c`), `S` the entry's `rsp`: a frame of
40 bytes with the stack guard (`fs:0x28`) at `S - 16` (as `FV7z/Gdt/Holds.lean`: `Gdt.dV1`), `z7_x86_cpuid (a, 1)`
(`call` at 32 to `0x424290`, `rdi` = the frame, `esi` = 1); back at 37 `eax` = bit 19 of `a[2]` (the 4 bytes at
`S - 32`: `mov eax, [rsp + 8]; shr eax, 19; and eax, 1`), the guard's check (`jne` to the `call __stack_chk_fail`
at 68), `add rsp, 40`, the `ret` (67).

The callee is a hypothesis, as in `FV7z/Lzp/Holds.lean` (`kf`): a continuation at its entry, given the run from its
return (`rsp` as at the `call`, the guard and the return address left as they were, its own post `Pc`) to the
return address (`kr`).

- `sg1`: the registers at the `call`; `sbit`: the answer, from the bytes at the frame `s`.
- `vc_0`, `vc_37`: the pieces from the entry and from 37.
- `sse_ok`: through `z7_x86_cpuid` to the return address, `rax` = `sbit`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sse

/-- `z7_x86_cpuid`. -/
abbrev cpuid_at : Addr := 0x424290

/-- The `call` to `z7_x86_cpuid`. -/
def pcall : List Byte := [0xe8, 0xdb, 0xfe, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709551323] 5) := by dec_rfl
theorem wc_32 : pcall <+: sse.drop 32 := by decide +kernel
theorem call_32 (feat : Features) : Dec feat sse 32 (FV7z.mk .call 64 [.rel 18446744073709551323] 5) :=
  Dec.shift (j := 32) (k := 0) (pcall_0 feat) wc_32 (Nat.zero_le _)
theorem tgt_32 : sse_at.add (32 + 5) + BitVec.ofNat 64 18446744073709551323 = cpuid_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_67 : pret <+: sse.drop 67 := by decide +kernel
theorem ret_67 (feat : Features) : Dec feat sse 67 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 67) (k := 0) (pret_0 feat) w_67 (Nat.zero_le _)

/-! ## The frame -/

/-- The registers at the `call`, the function called with registers `g` and the stack guard `c`: `rdi` the frame,
`esi` 1. -/
def sg1 (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 c ^^^ BitVec.setWidth 32 c)
    rsp := g.rsp - 40#64
    rsi := BitVec.setWidth 64 1#32
    rdi := g.rsp - 40#64 }

/-- The answer: bit 19 of the 4 bytes at `s + 8` (`a[2]`, `ecx` of leaf 1), zero-extended. -/
abbrev sbit (V : Addr → Byte) (s : Addr) : BitVec 64 :=
  BitVec.setWidth 64 ((ofBytesLE 32 (List.map V (byteAddrs (s + 8#64) 4)) >>> 19) &&& 1#32)

theorem t32 {rs : Addr} (h : 48 ≤ rs.toNat) : (rs - 40#64 + 8#64).toNat = rs.toNat - 32 := by
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem s40 (s : Addr) : s - 40#64 + 40#64 = s := BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to the `call`: the stack guard stored in the frame, `esi` 1, `rdi` the frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 32 ∧ g' = sg1 g rdq(V, fb + 40#64) ∧ V' = Gdt.dV1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw
  wpx [W_0, o0, Op.ldf]
  all_goals vc_fin

/-- From after the `call` to the `ret`: `eax` = `sbit`, the stack guard checked, the frame dropped. -/
theorem vc_37 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64))
    (h : ∀ fl, Q 67 { g with rax := sbit V g.rsp, rdx := 0#64, rsp := g.rsp + 40#64 } fl V) :
    W_37 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl4 hl24 hc h
  wpx [W_37, W_63, o1, o2, Op.xormf, hc, BitVec.xor_self]
  all_goals repeat' (first
    | exact h _
    | rfl
    | assumption
    | (intro hh; exact absurd hh (by decide))
    | constructor
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPU_IsSupported_SSE41 ()` from its entry, `z7_x86_cpuid` as a hypothesis (`kf`, the return into
`CPU_IsSupported_SSE41` pushed at `S - 48`): if it returns with `rsp` as at the `call`, the stack guard and the
return address as they were, the run reaches the return address with `rax` = `sbit` of the bytes it left and
`rsp` = `S + 8` (`kr`). -/
theorem sse_ok {fb : Addr} {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L sse_at sse)
    {codeC : List Byte} (hinC : CodeIn L cpuid_at codeC) (hC : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sse_at)
    (h48 : 48 ≤ X.cpu.gpr.rsp.toNat)
    (hfw : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hfd : ∀ i < 48, Foot F.data (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Gdt.dV1 V X.cpu.gpr fb) (X.cpu.gpr.rsp - 48#64) (toBytesLE (sse_at.add 37) 8)) →
      Y.cpu.rip = cpuid_at → Y.cpu.gpr = (sg1 X.cpu.gpr rdq(V, fb + 40#64)).set 4 (X.cpu.gpr.rsp - 48#64) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = sse_at.add 37 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 →
        rdq(V', X.cpu.gpr.rsp - 40#64 + 24#64) = rdq(V', fb + 40#64) →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := sbit V' (X.cpu.gpr.rsp - 40#64), rdx := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have a16 := Gdt.t16 h48
  have a32 := t32 h48
  -- to the `call`
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 32 ∧ g' = sg1 X.cpu.gpr rdq(V, fb + 40#64) ∧ V' = Gdt.dV1 V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcl (Gdt.fr hfw (Gdt.fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hgY]; try rfl
  have hcs : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 48#64 := by rw [hYsp]; exact Gdt.e48 h48
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_32 _) hinC hC tgt_32
    (by rw [hcs]; exact fun i hi => hfw i (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hcs] at hA₂
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hcs, hgY]) ?_
  -- back from `z7_x86_cpuid`, at 37: the answer, the guard's check, the `ret` at 67
  intro Z V' t'' hKZ hAZ hrZ hzs hcan hra hP
  refine (c_37 prof fb).run c hfs hin (fun j' g' _ V'' => j' = 67 ∧
      g' = { Z.cpu.gpr with
        rax := sbit V' (X.cpu.gpr.rsp - 40#64), rdx := 0#64, rsp := X.cpu.gpr.rsp } ∧
      V'' = V') hKZ hAZ hrZ
    (vc_37 (by rw [hzs]; exact Gdt.fr hfd (Gdt.fa h48 (d := 16) (by decide) (by rw [a32]; omega)) (by decide))
      (by rw [hzs]; exact Gdt.fr hfd (Gdt.fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide)) hcl
      (by rw [hzs]; exact hcan) fun _ => ⟨rfl, by rw [hzs, s40], rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_67 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hP hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Sse
