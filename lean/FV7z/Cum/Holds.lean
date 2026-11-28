import FV7z.Cum.Cuts
import FV7z.Umk.Code
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `NWindows::NFile::NDir::C_umask::C_umask ()` (PLAN.md §M, M1)

7-Zip 26.06's `C_umask::C_umask ()` at `0x455720` in `7zzs` (`CPP/Windows/FileDir.h`), `this` in `rdi`:
`mask = umask (0); umask (mask)` with the field set to `~mask & 0777`. `push rbx; mov rbx, rdi; xor edi, edi`, the
`call` at 10 to `umask` (`Umk.umk_at`), then `mov edi, eax; not eax; and eax, 0x1ff; mov [rbx], eax; pop rbx` and the
tail `jmp` at 27 to `umask` again, with the return address of `C_umask ()`'s caller on top of the stack.

`umask` (glibc 2.31's `syscall` 95) is a hypothesis twice over, as the callees of `FV7z/Ucu/Holds.lean`: `ku` is a
continuation at its entry from the `call`, given the run from its return (`rsp` 8 below the entry's, `rbx` = `this`,
the saved `rbx` and the return address as they were: `Sv`) and its own post `Pu`; `kj` is the continuation at its
entry from the tail `jmp`. The store `this->mask` (4 bytes at `this`) needs `this` clear of the 16 bytes from the saved
`rbx` to the return address (`hd`): no hypothesis on the bytes after the store, `kj` is given that the return address
is still there (`rdq(Vm …, rsp) = e₂.add j₂`).

- `msk`: `~eax & 0x1ff` for `eax` what the first `umask` returns.
- `V0`, `gC`: the bytes and the registers at the `call`; `Vm`: the bytes after the store.
- `vc_0`, `vc_15`: the verification conditions of the pieces.
- `cum_ok`: from the entry, through the first `umask`, to the entry of the second.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cum

/-- The `call` to `umask`. -/
def pcu : List Byte := [0xe8, 0x51, 0xfd, 0x20, 0x00]
theorem pcu_0 : ∀ feat, Dec feat pcu 0 (FV7z.mk .call 64 [.rel 2162001] 5) := by dec_rfl
theorem wc_10 : pcu <+: cum.drop 10 := by decide +kernel
theorem call_10 (feat : Features) : Dec feat cum 10 (FV7z.mk .call 64 [.rel 2162001] 5) :=
  Dec.shift (j := 10) (k := 0) (pcu_0 feat) wc_10 (Nat.zero_le _)
theorem tgt_10 : cum_at.add (10 + 5) + BitVec.ofNat 64 2162001 = Umk.umk_at.add 0 := by decide

/-- The tail `jmp` to `umask`. -/
def pjm : List Byte := [0xe9, 0x40, 0xfd, 0x20, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2161984] 5) := by dec_rfl
theorem wj_27 : pjm <+: cum.drop 27 := by decide +kernel
theorem jmp_27 (feat : Features) : Dec feat cum 27 (FV7z.mk .jmp 64 [.rel 2161984] 5) :=
  Dec.shift (j := 27) (k := 0) (pjm_0 feat) wj_27 (Nat.zero_le _)
theorem tgt_27 : cum_at.add (27 + 5) + BitVec.ofNat 64 2161984 = Umk.umk_at.add 0 := by decide

theorem umk_lt : 0 < Umk.umk.length := by rw [Umk.umk_length]; decide

/-- `xor edi, edi`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

/-- `not eax; and eax, 0x1ff` for `rax` = `a`. -/
abbrev msk (a : BitVec 64) : BitVec 32 := ~~~ BitVec.setWidth 32 a &&& 511#32

/-- The bytes at the `call`: `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call`: `rbx` = `this`, `edi` 0, 8 below the entry. -/
abbrev gC (g : Gprs) : Gprs := { g with rbx := g.rdi, rdi := 0#64, rsp := g.rsp - 8 }

/-- The bytes after `mov [rbx], eax` for the registers `g` back from `umask`. -/
abbrev Vm (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V g.rbx (toBytesLE (msk g.rax) 4)

/-- The saved `rbx` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop := rdq(V, x.rsp - 8) = x.rbx ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rbx, rdi; xor edi, edi` to the `call` at 10. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 10 ∧ g' = gC g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 ⊢
  wpx [W_0, o0, V0, gC, xz]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `umask`: `mov edi, eax; not eax; and eax, 0x1ff; mov [rbx], eax; pop rbx` to the `jmp` at 27. -/
theorem vc_15 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 4, Foot Wl (Addr.add g.rbx i)) (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 27
      { g with
          rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax), rax := (msk g.rax).setWidth 64,
          rbx := rdq(Vm V g, g.rsp), rsp := g.rsp + 8 } fl (Vm V g)) :
    W_15 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw hl0 h ⊢
  wpx [W_15, o1, Op.not32]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `C_umask::C_umask ()` (`this` = `rdi`) from its entry. At `umask`'s entry from the `call` the registers are `gC`
with `rsp` 16 below the entry's, the bytes `V0` with the return address pushed (`ku`); back at `cum_at + 15` (`Sv`,
`Pu`), at `umask`'s entry from the tail `jmp` with `this->mask` stored (`Vm`), `edi` the first `umask`'s result, the
entry's `rbx` and `rsp`, and the return address still on top of the stack (`kj`). -/
theorem cum_ok {Pu : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cum_at cum) (hinU : CodeIn L Umk.umk_at Umk.umk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cum_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr}
    (ku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (cum_at.add 15) 8)) →
      Y.cpu.rip = Umk.umk_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = cum_at.add 15 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Sv V₁ X.cpu.gpr e₂ → Pu Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kj : ∀ (Z : State) (V₁ : Addr → Byte) (Y : State) (t' : Nat), Pu Z V₁ → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vm V₁ Z.cpu.gpr) → Y.cpu.rip = Umk.umk_at →
      Y.cpu.gpr = { Z.cpu.gpr with
          rdi := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax), rax := (msk Z.cpu.gpr.rax).setWidth 64,
          rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } →
      rdq(Vm V₁ Z.cpu.gpr, X.cpu.gpr.rsp) = e₂ →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have c16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = cum_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `umask`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 10 ∧ g' = gC X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY] <;> rfl
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_10 _) hinU (tgt := 0) umk_lt tgt_10 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hsY, c16, hgY]
  refine ku Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `umask`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hzb hsv hPu
  have mz : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 4 ≤ y.toNat ∨ y.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs y 8).map (Vm V₁ Z.cpu.gpr) = (byteAddrs y 8).map V₁ :=
    fun y hy h => Tun.rd_Vst V₁ _ (toBytesLE (msk Z.cpu.gpr.rax) 4) y 8 (by rw [toBytesLE_length, hzb]; omega) hy
      (by rw [toBytesLE_length, hzb]; omega)
  have hb1 : rdq(Vm V₁ Z.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [mz (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hsv.1
  have hra' : rdq(Vm V₁ Z.cpu.gpr, X.cpu.gpr.rsp) = e₂ := by
    rw [mz X.cpu.gpr.rsp hp8 (by omega)]; exact hsv.2
  refine (c_15 prof).run c hin (fun j' g' _ V' => j' = 27 ∧
      g' = { Z.cpu.gpr with
          rdi := BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax), rax := (msk Z.cpu.gpr.rax).setWidth 64,
          rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
      V' = Vm V₁ Z.cpu.gpr) hKZ hAZ hrZ
    (vc_15 (by rw [hzb]; exact fw) (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, e8, hb1], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  -- the tail `jmp` to `umask`
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_27 _) hinU (tgt := 0) umk_lt tgt_27 ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  exact kj Z V₁ Y₃ t₅ hPu hzb hK₃ hA₃ (by rw [hr₃, addr_add_zero]) (by rw [hg₃, hgU]) hra'

end FV7z.Cum
