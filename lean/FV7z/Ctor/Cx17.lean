import FV7z.Ctor.Prep
import FV7z.Ctor.BlkRet
import FV7z.Lemmas.SysUm
import FV7z.Lemmas.BlkOps20
/-!
# Constructor 17: the file mode creation mask (PLAN.md §M, constructors)

`csuTg 17` (`0x41c240`, offset 304 of `sti`) is `endbr64; mov rdi, 0x79c7c0; jmp f` with `f` (`cf17`, at
`0x455720`) the function

    push rbx; mov rbx, rdi; xor edi, edi; call umask; mov edi, eax; not eax; and eax, 0x1ff; mov [rbx], eax;
    pop rbx; jmp umask

and `umask` (`umk`, at `0x665480`) `endbr64; mov eax, 95; syscall; ret`: the mask is read by `umask (0)` and set
back by `umask (old)`, and `~old & 0777` stored to the word at `0x79c7c0`.

The mask is not as at the start between the two calls, which `KeptW` does not allow: the run from the first call
on is one of its own (`Seg.s_umask_re`), and `KeptW` from the start comes back after the second
(`Seg.s_umask_back`). The two calls go into the log, so the goal must hold of a log with calls 95 put into it
(`InsOK 95`).

- `runs17`: `csuTg 17` for an invariant `J` that the bytes outside the 16 below `sp - 64` and the word keep.
- `c17_jg`: the same for `Jg`, with the spec `wrSpec c17Wr`.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-! ## The code -/

/-- The function constructor 17 jumps to, `0x455720` to `0x455740` of `7zzs`. -/
def cf17 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x31, 0xff, 0xe8, 0x51, 0xfd, 0x20, 0x00, 0x89,
  0xc7, 0xf7, 0xd0, 0x25, 0xff, 0x01, 0x00, 0x00, 0x89, 0x03, 0x5b, 0xe9, 0x40, 0xfd, 0x20, 0x00]
theorem cf17_pin : Exe.bytesAt V2606.zzs.blob 0x455720 32 = some cf17 := by decide +kernel
abbrev cf17_at : Addr := 0x455720

/-- glibc's `umask`, `0x665480` to `0x66548c` of `7zzs`. -/
def umk : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0x5f, 0x00, 0x00, 0x00, 0x0f, 0x05, 0xc3]
theorem umk_pin : Exe.bytesAt V2606.zzs.blob 0x665480 12 = some umk := by decide +kernel
abbrev umk_at : Addr := 0x665480

theorem f17_0 : ∀ feat, Dec feat cf17 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem f17_4 : ∀ feat, Dec feat cf17 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem f17_5 : ∀ feat, Dec feat cf17 5 (FV7z.mk .mov 64 [gr 64 3, gr 64 7] 3) := by dec_rfl
theorem f17_8 : ∀ feat, Dec feat cf17 8 (FV7z.mk .xor 32 [gr 32 7, gr 32 7] 2) := by dec_rfl
theorem f17_10 : ∀ feat, Dec feat cf17 10 (FV7z.mk .call 64 [.rel 2161969] 5) := by dec_rfl
theorem f17_15 : ∀ feat, Dec feat cf17 15 (FV7z.mk .mov 32 [gr 32 7, gr 32 0] 2) := by dec_rfl
theorem f17_17 : ∀ feat, Dec feat cf17 17 (FV7z.mk .not 32 [gr 32 0] 2) := by dec_rfl
theorem f17_19 : ∀ feat, Dec feat cf17 19 (FV7z.mk .and 32 [gr 32 0, .imm 32 511] 5) := by dec_rfl
theorem f17_24 : ∀ feat, Dec feat cf17 24 (FV7z.mk .mov 32 [.mem (mbd 3 0 32), gr 32 0] 2) := by dec_rfl
theorem f17_26 : ∀ feat, Dec feat cf17 26 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem f17_27 : ∀ feat, Dec feat cf17 27 (FV7z.mk .jmp 64 [.rel 2161984] 5) := by dec_rfl

theorem umk_0 : ∀ feat, Dec feat umk 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem umk_4 : ∀ feat, Dec feat umk 4 (FV7z.mk .mov 32 [gr 32 0, .imm 32 95] 5) := by dec_rfl
theorem umk_9 : ∀ feat, Dec feat umk 9 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem umk_11 : ∀ feat, Dec feat umk 11 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- `csuTg 17`: `endbr64; mov rdi, 0x79c7c0; jmp cf17_at`. -/
def c304 : List Byte :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc7, 0xc0, 0xc7, 0x79, 0x00, 0xe9, 0xd0, 0x94, 0x03, 0x00]
theorem c304_0 : ∀ feat, Dec feat c304 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c304_4 : ∀ feat, Dec feat c304 4 (FV7z.mk .mov 64 [gr 64 7, .imm 64 7980992] 7) := by dec_rfl
theorem c304_11 : ∀ feat, Dec feat c304 11 (FV7z.mk .jmp 64 [.rel 234704] 5) := by dec_rfl
theorem v304 : c304 <+: sti.drop 304 := by decide +kernel
theorem tg17 : csuTg 17 = sti_at.add 304 := by decide +kernel
theorem calls17 : calls 17 = [] := by decide +kernel

theorem s304 (feat : Features) : Dec feat sti 304 (FV7z.mk .endbr64 32 [] 4) :=
  Dec.shift (j := 304) (k := 0) (c304_0 feat) v304 (by decide)
theorem s308 (feat : Features) : Dec feat sti 308 (FV7z.mk .mov 64 [gr 64 7, .imm 64 7980992] 7) :=
  Dec.shift (j := 304) (k := 4) (c304_4 feat) v304 (by decide)
theorem s315 (feat : Features) : Dec feat sti 315 (FV7z.mk .jmp 64 [.rel 234704] 5) :=
  Dec.shift (j := 304) (k := 11) (c304_11 feat) v304 (by decide)

/-- `not eax`. -/
theorem b17 {prof : Profile} : Blk prof cf17 17 19 [Op.not32 0] :=
  Blk.cons (f17_17 _) OpI.not32 (by decide) (.nil 19)

/-! ## Stack offsets and the bytes after the stores -/

theorem n72 {sp : Addr} (h : 80 ≤ sp.toNat) : (sp - 72#64).toNat = sp.toNat - 72 := by bv_omega
theorem n80 {sp : Addr} (h : 80 ≤ sp.toNat) : (sp - 80#64).toNat = sp.toNat - 80 := by bv_omega
theorem m72 (sp : Addr) : sp - 64#64 - 8 = sp - 72#64 := by bv_omega
theorem m80 (sp : Addr) : sp - 72#64 - 8 = sp - 80#64 := by bv_omega
theorem p72 (sp : Addr) : sp - 80#64 + 8 = sp - 72#64 := by bv_omega
theorem p64 (sp : Addr) : sp - 72#64 + 8 = sp - 64#64 := by bv_omega

/-- The mask through `rax`, `eax` and `edi`. -/
theorem um9 (u : BitVec 9) : (((u.setWidth 64).setWidth 32).setWidth 64).setWidth 9 = u := by bv_omega

/-- Eight bytes read where they were stored. -/
theorem rs {V : Addr → Byte} {a : Addr} {v : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst V a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self V a (toBytesLE v 8) (toBytesLE_length v 8) ha]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

variable {V : Addr → Byte} {sp : Addr} {b ra : BitVec 64} {v : BitVec 32}

/-- `rbx` read back at the `pop`. -/
theorem r17 (hS : 7991300 + 1024 ≤ sp.toNat) :
    rdq(Vst (Vst (Vst V (sp - 72#64) (toBytesLE b 8)) (sp - 80#64) (toBytesLE ra 8)) 7980992#64
      (toBytesLE v (32 / 8)), sp - 72#64) = b := by
  have hl := sp.isLt
  have e1 := n72 (sp := sp) (by omega)
  have e2 := n80 (sp := sp) (by omega)
  have e3 : (7980992#64 : Addr).toNat = 7980992 := rfl
  rw [Tun.rd_Vst _ 7980992#64 (toBytesLE v (32 / 8)) (sp - 72#64) 8 (by rw [toBytesLE_length, e3]; omega)
      (by rw [e1]; omega) (by rw [toBytesLE_length, e3, e1]; omega),
    Tun.rd_Vst _ (sp - 80#64) (toBytesLE ra 8) (sp - 72#64) 8 (by rw [toBytesLE_length, e2]; omega)
      (by rw [e1]; omega) (by rw [toBytesLE_length, e2, e1]; omega),
    Tun.rd_Vst_self V (sp - 72#64) (toBytesLE b 8) (toBytesLE_length b 8) (by rw [e1]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The return address slot of `__libc_csu_init` after the stores. -/
theorem q17 (hS : 7991300 + 1024 ≤ sp.toNat) :
    List.map (Vst (Vst (Vst V (sp - 72#64) (toBytesLE b 8)) (sp - 80#64) (toBytesLE ra 8)) 7980992#64
      (toBytesLE v (32 / 8))) (byteAddrs (sp - 64#64) 8) = List.map V (byteAddrs (sp - 64#64) 8) := by
  have hl := sp.isLt
  have e0 := Csu.sp_n (sp := sp) (by omega)
  have e1 := n72 (sp := sp) (by omega)
  have e2 := n80 (sp := sp) (by omega)
  have e3 : (7980992#64 : Addr).toNat = 7980992 := rfl
  rw [Tun.rd_Vst _ 7980992#64 (toBytesLE v (32 / 8)) (sp - 64#64) 8 (by rw [toBytesLE_length, e3]; omega)
      (by rw [e0]; omega) (by rw [toBytesLE_length, e3, e0]; omega),
    Tun.rd_Vst _ (sp - 80#64) (toBytesLE ra 8) (sp - 64#64) 8 (by rw [toBytesLE_length, e2]; omega)
      (by rw [e0]; omega) (by rw [toBytesLE_length, e2, e0]; omega),
    Tun.rd_Vst V (sp - 72#64) (toBytesLE b 8) (sp - 64#64) 8 (by rw [toBytesLE_length, e1]; omega)
      (by rw [e0]; omega) (by rw [toBytesLE_length, e1, e0]; omega)]

/-- A byte apart from the three stores. -/
theorem o17 {a : Addr} (hS : 7991300 + 1024 ≤ sp.toNat) (h1 : ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 64))
    (h2 : ¬ (7980992 ≤ a.toNat ∧ a.toNat < 7980996)) :
    Vst (Vst (Vst V (sp - 72#64) (toBytesLE b 8)) (sp - 80#64) (toBytesLE ra 8)) 7980992#64
      (toBytesLE v (32 / 8)) a = V a := by
  have hl := sp.isLt
  have e1 := n72 (sp := sp) (by omega)
  have e2 := n80 (sp := sp) (by omega)
  have e3 : (7980992#64 : Addr).toNat = 7980992 := rfl
  rw [Tun.Vst_out _ 7980992#64 (toBytesLE v (32 / 8)) a (by rw [toBytesLE_length, e3]; omega)
      (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ (sp - 80#64) (toBytesLE ra 8) a (by rw [toBytesLE_length, e2]; omega)
      (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out V (sp - 72#64) (toBytesLE b 8) a (by rw [toBytesLE_length, e1]; omega)
      (by rw [toBytesLE_length, e1]; omega)]

/-- The registers the run keeps track of: `rsp`, `rbx`, and the others a call keeps as at the entry. -/
abbrev Tr17 (g : Gprs) (s r : BitVec 64) (g' : Gprs) : Prop :=
  g'.rsp = s ∧ g'.rbx = r ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-! ## The run -/

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 17` is a function as `Csu.csu_ok` asks, for a goal that holds of a log with calls 95 put into it and a
start with no `rseq` area: `J 18` holds of the bytes after it (as before but for the 16 bytes below `sp - 64` and
the word at `0x79c7c0`). -/
theorem runs17 {J : Nat → (Addr → Byte) → Prop} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (hU : InsOK 95 gP gE) (hrs : s₀.thread.rseq = none) (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinF : CodeIn L cf17_at cf17) (hinU : CodeIn L umk_at umk)
    (hs72 : ∀ i < 8, Foot Wl (Addr.add (sp - 72#64) i)) (hs80 : ∀ i < 8, Foot Wl (Addr.add (sp - 80#64) i))
    (hgw : ∀ i < 4, Foot Wl (Addr.add 7980992#64 i)) (hS : 7991300 + 1024 ≤ sp.toNat)
    (hJ : ∀ W V', J 17 W → (∀ a : Addr, ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7980992 ≤ a.toNat ∧ a.toNat < 7980996) → V' a = W a) → J 18 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 17 (csuTg 17) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra kk
  have hsl := sp.isLt
  -- the constructor: `mov rdi, 0x79c7c0; jmp cf17_at`
  refine c.s_endbr hK hA hin (sti_lt (by decide)) (hr.trans tg17) (s304 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have k1 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y1.cpu.gpr := by
    rw [hg1]
    exact ⟨hsp, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine c.s_mov_ri64 hK1 hA1 hin (sti_lt (by decide)) hr1 (s308 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have k2 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y2.cpu.gpr := by rw [hg2]; exact k1
  have d2 : Y2.cpu.gpr.rdi = 7980992#64 := by rw [hg2]; rfl
  refine c.s_jmp_x hK2 hA2 hin (sti_lt (by decide)) hr2 (s315 _) hinF (tgt := 0) (by decide) (by decide) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have k3 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y3.cpu.gpr := by rw [hg3]; exact k2
  have d3 : Y3.cpu.gpr.rdi = 7980992#64 := by rw [hg3]; exact d2
  -- `push rbx; mov rbx, rdi; xor edi, edi`
  refine c.s_endbr hK3 hA3 hinF (by decide) hr3 (f17_0 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have k4 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y4.cpu.gpr := by rw [hg4]; exact k3
  have d4 : Y4.cpu.gpr.rdi = 7980992#64 := by rw [hg4]; exact d3
  refine c.s_push hK4 hA4 hinF (by decide) hr4 (f17_4 _) (by rw [k4.1, m72]; exact hs72) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  rw [k4.1, m72, show Y4.cpu.gpr.get (regOf 3) = X.cpu.gpr.rbx from k4.2.1] at hA5
  have k5 : Tr17 X.cpu.gpr (sp - 72#64) X.cpu.gpr.rbx Y5.cpu.gpr := by
    rw [hg5]
    refine ⟨?_, k4.2⟩
    show Y4.cpu.gpr.rsp - 8 = _
    rw [k4.1, m72]
  have d5 : Y5.cpu.gpr.rdi = 7980992#64 := by rw [hg5]; exact d4
  refine c.s_mov_rr64 hK5 hA5 hinF (by decide) hr5 (f17_5 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have k6 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y6.cpu.gpr := by
    rw [hg6]
    exact ⟨k5.1, d5, k5.2.2⟩
  refine c.s_xor_rr32 hK6 hA6 hinF (by decide) hr6 (f17_8 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have k7 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y7.cpu.gpr := by rw [hg7]; exact k6
  -- `call umask`
  refine c.s_call_x hK7 hA7 hinF (by decide) hr7 (f17_10 _) hinU (tgt := 0) (by decide) (by decide)
    (by rw [k7.1, m80]; exact hs80) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  rw [k7.1, m80] at hA8
  have k8 : Tr17 X.cpu.gpr (sp - 80#64) 7980992#64 Y8.cpu.gpr := by
    rw [hg8]
    refine ⟨?_, k7.2⟩
    show Y7.cpu.gpr.rsp - 8 = _
    rw [k7.1, m80]
  refine c.s_endbr hK8 hA8 hinU (by decide) hr8 (umk_0 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have k9 : Tr17 X.cpu.gpr (sp - 80#64) 7980992#64 Y9.cpu.gpr := by rw [hg9]; exact k8
  refine c.s_mov_ri32 hK9 hA9 hinU (by decide) hr9 (umk_4 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have k10 : Tr17 X.cpu.gpr (sp - 80#64) 7980992#64 Y10.cpu.gpr := by rw [hg10]; exact k9
  have ax10 : Y10.cpu.gpr.rax = (BitVec.ofNat 32 95).setWidth 64 := by rw [hg10]; rfl
  -- `umask (0)`: the run goes on from the state after as its own start
  refine c.s_umask_re hrs hK10 hA10 hinU (by decide) hr10 (umk_9 _) (by rw [ax10]; decide)
    fun M t11 hKm c₁ hAm => ?_
  refine c₁.s_ret (KeptW.refl Wl _) hAm hinU (by decide) ?_ (umk_11 _) ?_ hinF (j₂ := 15) (by decide) ?_ ?_
  · show Y10.cpu.rip.add 2 = _
    rw [hr10]
    exact addr_add_add _ _ _
  · intro i hi
    show Foot F.data (Addr.add Y10.cpu.gpr.rsp i)
    rw [k10.1]
    exact c₁.hws _ (hs80 i hi)
  · show rdq(_, Y10.cpu.gpr.rsp) = _
    rw [k10.1]
    exact rs (by rw [n80 (sp := sp) (by omega)]; omega)
  rintro Y11 t11' hK11 hA11 ⟨hr11, hg11⟩
  have k11 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y11.cpu.gpr := by
    rw [hg11]
    refine ⟨?_, k10.2⟩
    show Y10.cpu.gpr.rsp + 8 = _
    rw [k10.1, p72]
  have a11 : Y11.cpu.gpr.rax = s₀.proc.umask.setWidth 64 := by
    rw [hg11]
    show Y10.proc.umask.setWidth 64 = _
    rw [hK10.proc]
  -- `mov edi, eax; not eax; and eax, 0x1ff; mov [rbx], eax`
  refine c₁.s_mov_rr32 hK11 hA11 hinF (by decide) hr11 (f17_15 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have k12 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y12.cpu.gpr := by rw [hg12]; exact k11
  have d12 : Y12.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by
    rw [hg12]
    show (Y11.cpu.gpr.rax.setWidth 32).setWidth 64 = _
    rw [a11]
  refine c₁.s_blk hinF b17 hK12 hA12 hr12 ?_
  intro fl _ Y13 t13 hK13 hA13 hr13 hg13 _
  have k13 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y13.cpu.gpr := by rw [hg13]; exact k12
  have d13 : Y13.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg13]; exact d12
  refine c₁.s_and_ri32 hK13 hA13 hinF (by decide) hr13 (f17_19 _) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, -⟩
  have k14 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y14.cpu.gpr := by rw [hg14]; exact k13
  have d14 : Y14.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg14]; exact d13
  have ea14 : eaD Y14 3 0 = 7980992#64 := by
    show Y14.cpu.gpr.rbx + BitVec.ofNat 64 0 = _
    rw [k14.2.1, BitVec.add_zero]
  refine c₁.s_mov_mr hK14 hA14 hinF (by decide) hr14 (.inl rfl) (f17_24 _) (by rw [ea14]; exact hgw) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  rw [ea14] at hA15
  have k15 : Tr17 X.cpu.gpr (sp - 72#64) 7980992#64 Y15.cpu.gpr := by rw [hg15]; exact k14
  have d15 : Y15.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg15]; exact d14
  -- `pop rbx; jmp umask`
  refine c₁.s_pop hK15 hA15 hinF (by decide) hr15 (f17_26 _) (fun i hi => ?_) ?_
  · rw [k15.1]
    exact c₁.hws _ (hs72 i hi)
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  have k16 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y16.cpu.gpr := by
    rw [hg16]
    refine ⟨?_, ?_, k15.2.2⟩
    · show Y15.cpu.gpr.rsp + 8 = _
      rw [k15.1, p64]
    · show rdq(_, Y15.cpu.gpr.rsp) = _
      rw [k15.1]
      exact r17 hS
  have d16 : Y16.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg16]; exact d15
  refine c₁.s_jmp_x hK16 hA16 hinF (by decide) hr16 (f17_27 _) hinU (tgt := 0) (by decide) (by decide) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
  have k17 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y17.cpu.gpr := by rw [hg17]; exact k16
  have d17 : Y17.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg17]; exact d16
  refine c₁.s_endbr hK17 hA17 hinU (by decide) hr17 (umk_0 _) ?_
  rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
  have k18 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y18.cpu.gpr := by rw [hg18]; exact k17
  have d18 : Y18.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg18]; exact d17
  refine c₁.s_mov_ri32 hK18 hA18 hinU (by decide) hr18 (umk_4 _) ?_
  rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
  have k19 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y19.cpu.gpr := by rw [hg19]; exact k18
  have d19 : Y19.cpu.gpr.rdi = ((s₀.proc.umask.setWidth 64).setWidth 32).setWidth 64 := by rw [hg19]; exact d18
  have ax19 : Y19.cpu.gpr.rax = (BitVec.ofNat 32 95).setWidth 64 := by rw [hg19]; rfl
  -- `umask (old)`: `KeptW` from the start again
  refine c₁.s_umask_back rfl hKm hK19 hA19 hinU (by decide) hr19 (umk_9 _) (by rw [ax19]; decide)
    (by rw [d19]; exact um9 _) ?_
  intro Y20 t20 hK20 hA20 hr20 hg20
  have k20 : Tr17 X.cpu.gpr (sp - 64#64) X.cpu.gpr.rbx Y20.cpu.gpr := by rw [hg20]; exact k19
  -- `ret` to `__libc_csu_init`
  refine c.s_ret hK20 hA20 hinU (by decide) hr20 (umk_11 _) (fun i hi => ?_) hC.code hj₂ ?_ ?_
  · rw [k20.1]
    exact c.hws _ (hC.st i (by omega))
  · rw [k20.1, q17 hS]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have hn10 : Y10.cpu.gpr.rax.toNat = 95 := by rw [ax10]; decide
  have hn19 : Y19.cpu.gpr.rax.toNat = 95 := by rw [ax19]; decide
  refine GoG.ins hU hn19 (GoG.ins hU hn10 (kk Z t' _ hKZ hAZ (hJ V _ hI fun a h1 h2 => o17 hS h1 h2)
    (fun a ha => o17 hS (by omega) (by omega)) (fun a ha => o17 hS (by omega) (by omega)) hrZ ?_))
  rw [hgZ]
  refine ⟨?_, k20.2⟩
  exact congrArg (· + 8) (k20.1.trans hsp.symm)

/-- The word constructor 17 stores. -/
def c17Wr : List (Nat × Nat) := [(7980992, 7980996)]

theorem st17 {s n : Nat} (h : ¬ (s - 1024 ≤ n ∧ n < s + 8)) : ¬ (s - 80 ≤ n ∧ n < s - 64) := by omega

theorem gw17 {a : Addr} (h : ¬ InR c17Wr a.toNat) : ¬ (7980992 ≤ a.toNat ∧ a.toNat < 7980996) := by
  simp only [c17Wr, InR, or_false] at h
  omega

/-- `runs17` for `Jg` and the spec `wrSpec c17Wr`. -/
theorem c17_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {tg : Nat → Addr}
    {a₀ a₁ a₂ : BitVec 64} (hU : InsOK 95 gP gE) (hrs : s₀.thread.rseq = none) (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti) (hinF : CodeIn L cf17_at cf17)
    (hinU : CodeIn L umk_at umk)
    (hs72 : ∀ i < 8, Foot Wl (Addr.add (sp - 72#64) i)) (hs80 : ∀ i < 8, Foot Wl (Addr.add (sp - 80#64) i))
    (hgw : ∀ i < 4, Foot Wl (Addr.add 7980992#64 i)) (hS : 7991300 + 1024 ≤ sp.toNat)
    (hspec : spec 17 = wrSpec c17Wr) (hD : ∀ k, (spec k).Dep)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < 17 → ∀ x ∈ (spec k).wr, ∀ y ∈ c17Wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W V', G 17 W → (∀ a : Addr, ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7980992 ≤ a.toNat ∧ a.toNat < 7980996) → V' a = W a) → G 18 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 17 (csuTg 17) := by
  refine runs17 hU hrs c hC hin hinF hinU hs72 hs80 hgw hS
    fun W V' hJ hv => jg_wrk (by decide) calls17 hS hspec hD (by decide) hB hXw (fun a h1 h2 => ?_)
      (hG W V' · hv) hJ
  exact hv a (st17 h2) (gw17 h1)

end FV7z.Ctor
