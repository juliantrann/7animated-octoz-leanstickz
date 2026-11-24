import FV7z.Start.SjpCall
/-!
# `__libc_start_main` calls `main` (PLAN.md G3, startup)

`_setjmp` returns 0 to `0x613481` (`lsm` 1089), so glibc 2.31's `__libc_start_main` takes the way of a first return:
it saves the thread's `cleanup_jmp_buf` (`fs:0x300`) and `cleanup` (`fs:0x2f8`) into `unwind_buf.priv` at
`rsp + 0xb8`, makes `fs:0x300` point to `unwind_buf` (`rsp + 0x70`), and calls `main (argc, argv, __environ)`
through `rax` at `0x6134ce` (`lsm` 1166), `main` being the one kept at `rsp + 0x18`. The return is to `0x6134d0`
(`lsm` 1168), where `exit` is called with `main`'s result.

- `MainMem V fb q`: the bytes after the three stores, `q` the stack pointer.
- `vc_1089`: from `0x613481` to the call, `_setjmp` having returned 0.
- `call_1166`: the `call *%rax`.
- `lsb_main`: the run from `0x613481` to `main`'s first instruction.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the stores of `fs:0x300` and `fs:0x2f8` into `unwind_buf.priv` (`q + 0xb8`) and of `unwind_buf`'s
address (`q + 0x70`) into `fs:0x300`, the thread control block at `fb`. -/
def MainMem (V : Addr → Byte) (fb q : Addr) : Addr → Byte :=
  Vst (Vst (Vst V (q + 184#64) (toBytesLE rdq(V, fb + 768#64) 8)) (q + 192#64)
      (toBytesLE rdq(Vst V (q + 184#64) (toBytesLE rdq(V, fb + 768#64) 8), fb + 760#64) 8))
    (fb + 768#64) (toBytesLE (q + 112#64) 8)

/-- From `0x613481` to the call of `main`, `_setjmp` having returned 0: `main` and its arguments `argc`, `argv`,
`__environ`. -/
theorem vc_1089 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ev av mn : BitVec 64} {ac : BitVec 32}
    (h0 : g.rax = 0) (hg0 : ∀ i < 8, Foot F.data ((fb + 768#64).add i))
    (hs0 : ∀ i < 8, Foot Wl ((g.rsp + 184#64).add i)) (hg1 : ∀ i < 8, Foot F.data ((fb + 760#64).add i))
    (hs1 : ∀ i < 8, Foot Wl ((g.rsp + 192#64).add i)) (hgw : ∀ i < 8, Foot Wl ((fb + 768#64).add i))
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i)) (h2 : ∀ i < 4, Foot F.data ((g.rsp + 12#64).add i))
    (h3 : ∀ i < 8, Foot F.data ((g.rsp + 16#64).add i)) (h4 : ∀ i < 8, Foot F.data ((g.rsp + 24#64).add i))
    (he : rdq(MainMem V fb g.rsp, 8013720#64) = ev) (hc : rdd(MainMem V fb g.rsp, g.rsp + 12#64) = ac)
    (ha : rdq(MainMem V fb g.rsp, g.rsp + 16#64) = av) (hm : rdq(MainMem V fb g.rsp, g.rsp + 24#64) = mn) :
    W_1089 fb F Wl (fun j' g' _ V' => j' = 1166 ∧ g' = (((g.set 0 mn).set 2 ev).set 6 av).set 7 (ac.setWidth 64) ∧
      V' = MainMem V fb g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 0 := h0
  dsimp only at hs0 hs1 h2 h3 h4 he hc ha hm
  subst he hc ha hm
  wpx [W_1089, W_1097, o12, o13, Op.test, Op.ldf, Op.st, Op.lea, Op.stf, Op.lda, Op.ld]
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · first | exact absurd h (by decide) | simp_all
  · first
    | exact ⟨hg0, hs0, hg1, hs1, hgw, h1, h2, h3, h4, rfl⟩
    | exact ⟨hg0, hs0, hg1, hs1, hgw, h1, h2, h3, h4, rfl, rfl⟩
    | exact ⟨hg0, hs0, hg1, hs1, hgw, h1, h2, h3, h4, rfl, rfl, rfl⟩
    | exact ⟨hg0, hs0, hg1, hs1, hgw, h1, h2, h3, h4, trivial⟩

/-- The `call *%rax` of `main` in `__libc_start_main`. -/
def pc1166 : List Byte := [0xff, 0xd0]
theorem pc1166_0 : ∀ feat, Dec feat pc1166 0 (FV7z.mk .call 64 [gr 64 0] 2) := by dec_rfl
theorem wc1166 : pc1166 <+: lsm.drop 1166 := by decide +kernel
theorem call_1166 (feat : Features) : Dec feat lsm 1166 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 1166) (k := 0) (pc1166_0 feat) wc1166 (Nat.zero_le _)

/-- A read apart from the three stores of `MainMem`. -/
theorem rd_mm {V : Addr → Byte} {fb q : Addr} (x : Addr) (n : Nat) (hq : (q + 184#64).toNat = q.toNat + 184)
    (hq' : (q + 192#64).toNat = q.toNat + 192) (hf : (fb + 768#64).toNat = fb.toNat + 768)
    (hqn : q.toNat + 200 ≤ 2 ^ 64) (hfn : fb.toNat + 776 ≤ 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : q.toNat + 200 ≤ x.toNat ∨ x.toNat + n ≤ q.toNat + 184)
    (h2 : fb.toNat + 776 ≤ x.toNat ∨ x.toNat + n ≤ fb.toNat + 768) :
    List.map (MainMem V fb q) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have hb : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold MainMem
  rw [rd_ra x n (hb _) (by omega) hx (by omega), rd_ra x n (hb _) (by omega) hx (by omega),
    rd_ra x n (hb _) (by omega) hx (by omega)]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- From `0x613481` to the first instruction of `main` (kept at `rsp + 0x18`, its code `code₂`), `_setjmp` having
returned 0: the bytes are `MainMem` with the return address `0x6134d0` stored below the stack pointer, `rdi`, `rsi`,
`rdx` are `argc`, `argv`, `__environ` (at `rsp + 0xc`, `rsp + 0x10`, `0x7a4798`). -/
theorem lsb_main {fb e₂ : Addr} {code₂ : List Byte} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hl : CodeIn L lsm_at lsm) (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1089) (h0 : X.cpu.gpr.rax = 0)
    (hq : 8 ≤ X.cpu.gpr.rsp.toNat) (hqn : X.cpu.gpr.rsp.toNat + 200 ≤ 2 ^ 64) (hfn : fb.toNat + 776 ≤ 2 ^ 64)
    (hg0 : ∀ i < 8, Foot F.data ((fb + 768#64).add i)) (hg1 : ∀ i < 8, Foot F.data ((fb + 760#64).add i))
    (hgw : ∀ i < 8, Foot Wl ((fb + 768#64).add i))
    (hs0 : ∀ i < 8, Foot Wl ((X.cpu.gpr.rsp + 184#64).add i))
    (hs1 : ∀ i < 8, Foot Wl ((X.cpu.gpr.rsp + 192#64).add i))
    (hra : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (h2 : ∀ i < 4, Foot F.data ((X.cpu.gpr.rsp + 12#64).add i))
    (h3 : ∀ i < 8, Foot F.data ((X.cpu.gpr.rsp + 16#64).add i))
    (h4 : ∀ i < 8, Foot F.data ((X.cpu.gpr.rsp + 24#64).add i))
    (hfq : fb.toNat + 776 ≤ X.cpu.gpr.rsp.toNat + 12 ∨ X.cpu.gpr.rsp.toNat + 32 ≤ fb.toNat + 768)
    (hfe : fb.toNat + 776 ≤ 8013720 ∨ 8013728 ≤ fb.toNat + 768)
    (hqe : X.cpu.gpr.rsp.toNat + 200 ≤ 8013720 ∨ 8013728 ≤ X.cpu.gpr.rsp.toNat + 184)
    (hmn : rdq(V, X.cpu.gpr.rsp + 24#64) = e₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem
        (Vst (MainMem V fb X.cpu.gpr.rsp) (X.cpu.gpr.rsp - 8) (toBytesLE (lsm_at.add 1168) 8)) →
      Z.cpu.rip = e₂ →
      Z.cpu.gpr = (((((X.cpu.gpr.set 0 e₂).set 2 rdq(V, 8013720#64)).set 6 rdq(V, X.cpu.gpr.rsp + 16#64)).set 7
        ((rdd(V, X.cpu.gpr.rsp + 12#64)).setWidth 64)).set 4 (X.cpu.gpr.rsp - 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have t184 : (X.cpu.gpr.rsp + 184#64).toNat = X.cpu.gpr.rsp.toNat + 184 := by bv_omega
  have t192 : (X.cpu.gpr.rsp + 192#64).toNat = X.cpu.gpr.rsp.toNat + 192 := by bv_omega
  have t768 : (fb + 768#64).toNat = fb.toNat + 768 := by bv_omega
  have t12 : (X.cpu.gpr.rsp + 12#64).toNat = X.cpu.gpr.rsp.toNat + 12 := by bv_omega
  have t16 : (X.cpu.gpr.rsp + 16#64).toNat = X.cpu.gpr.rsp.toNat + 16 := by bv_omega
  have t24 : (X.cpu.gpr.rsp + 24#64).toNat = X.cpu.gpr.rsp.toNat + 24 := by bv_omega
  have te : (8013720#64 : Addr).toNat = 8013720 := rfl
  have he : rdq(MainMem V fb X.cpu.gpr.rsp, 8013720#64) = rdq(V, 8013720#64) := by
    rw [rd_mm _ 8 t184 t192 t768 hqn hfn (by rw [te]; omega) (by rw [te]; omega) (by rw [te]; omega)]
  have hc : rdd(MainMem V fb X.cpu.gpr.rsp, X.cpu.gpr.rsp + 12#64) = rdd(V, X.cpu.gpr.rsp + 12#64) := by
    rw [rd_mm _ 4 t184 t192 t768 hqn hfn (by rw [t12]; omega) (by rw [t12]; omega) (by rw [t12]; omega)]
  have ha : rdq(MainMem V fb X.cpu.gpr.rsp, X.cpu.gpr.rsp + 16#64) = rdq(V, X.cpu.gpr.rsp + 16#64) := by
    rw [rd_mm _ 8 t184 t192 t768 hqn hfn (by rw [t16]; omega) (by rw [t16]; omega) (by rw [t16]; omega)]
  have hm : rdq(MainMem V fb X.cpu.gpr.rsp, X.cpu.gpr.rsp + 24#64) = e₂ := by
    rw [rd_mm _ 8 t184 t192 t768 hqn hfn (by rw [t24]; omega) (by rw [t24]; omega) (by rw [t24]; omega)]
    exact hmn
  refine (c_1089 prof fb).run c hfs hl _ hK hA hrip (vc_1089 h0 hg0 hs0 hg1 hs1 hgw h1 h2 h3 h4 he hc ha hm) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hgY]
    rfl
  refine c.s_callr hKY hAY hl (by rw [lsm_length]; decide) hrY (call_1166 _) hin₂ h₂ (by rw [hgY]; rfl)
    (fun i hi => by rw [hYs]; exact hra i hi) ?_
  rintro Z u hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hYs] at hAZ hgZ
  rw [hgY] at hgZ
  exact k Z u hKZ hAZ hrZ hgZ

end FV7z.StartB
