import FV7z.Tcg.Holds
import FV7z.Tcg.Sys
import FV7z.TcgC.Cuts
import FV7z.Lemmas.Sse2
import FV7z.Lemmas.BlkOps4
import FV7z.Strlen.Run
/-!
# `__tcgetattr`, the whole function (PLAN.md §M, M1)

`Tcg/Holds.lean`'s pieces with the step of the `syscall` (`Seg.s_tcgets`, `Tcg/Sys.lean`) and the copy after an
answer 0: `k`, the kernel's `struct termios` at `rsp - 56`, is copied to `*termios_p` (`r8`): the 4 flags words
(`movdqa`/`movups`), `c_line` and the 19 bytes of `c_cc` (`movdqu`/`movups` and two stores), the rest of glibc's 32
bytes of `c_cc` cleared, `c_ispeed` and `c_ospeed` the `CBAUD` bits of `c_cflag`. Pieces: the entry to the `syscall`
(`c_0`), the `syscall`, then the two ways from 42 (`c_42`): an error to 143, an answer 0 to the vector loads (75, a
`BlkV`), the stretch 86–134 (`TcgC.c_86`), two `movups` (134, 138), and from 143 the check of the stack guard to the
`ret` (`c_143`, 166). The model's `ioctl (TCGETS)` answers an error or 0, so the way at 42 of an answer not 0 is not
taken.

What `tcg_ok` says of the bytes after an answer 0: they are as before outside the frame and the 60 bytes of
`*termios_p` (their contents are not stated).

- `pva`, `pvs`: the vector instructions (75, 80; 134, 138); `bv_75`: the loads as a `BlkV`.
- `TCs`, `TKeep`: the registers a call keeps; those and `rsp`, `r8`.
- `t_fr_add`, `t_vst_in`, `t_rdq_vst`, `t_rdq_congr`: addresses in a frame, stores apart from a load.
- `vc_42_zero`, `vc_86`: the verification conditions of the way of an answer 0.
- `tcg_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Tcg

/-- The vector loads. -/
def pva : List Byte := [0x66, 0x0f, 0x6f, 0x04, 0x24, 0xf3, 0x0f, 0x6f, 0x4c, 0x24, 0x11]
theorem pva_0 : ∀ feat, Dec feat pva 0 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .mem (mbd 4 0 128)] 5) := by dec_rfl
theorem pva_5 : ∀ feat, Dec feat pva 5 (FV7z.mk (.sse .movdqu) 32 [.xmm 1, .mem (mbd 4 17 128)] 6) := by dec_rfl
theorem w_75 : pva <+: tcg.drop 75 := by decide +kernel
theorem dv_75 (feat : Features) : Dec feat tcg 75 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .mem (mbd 4 0 128)] 5) :=
  Dec.shift (j := 75) (k := 0) (pva_0 feat) w_75 (Nat.zero_le _)
theorem dv_80 (feat : Features) : Dec feat tcg 80 (FV7z.mk (.sse .movdqu) 32 [.xmm 1, .mem (mbd 4 17 128)] 6) :=
  Dec.shift (j := 75) (k := 5) (pva_5 feat) w_75 (by decide)

/-- The vector stores. -/
def pvs : List Byte := [0x41, 0x0f, 0x11, 0x00, 0x41, 0x0f, 0x11, 0x48, 0x11]
theorem pvs_0 : ∀ feat, Dec feat pvs 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 0 128), .xmm 0] 4) := by dec_rfl
theorem pvs_4 : ∀ feat, Dec feat pvs 4 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 17 128), .xmm 1] 5) := by dec_rfl
theorem w_134 : pvs <+: tcg.drop 134 := by decide +kernel
theorem ds_134 (feat : Features) : Dec feat tcg 134 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 0 128), .xmm 0] 4) :=
  Dec.shift (j := 134) (k := 0) (pvs_0 feat) w_134 (Nat.zero_le _)
theorem ds_138 (feat : Features) : Dec feat tcg 138 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 17 128), .xmm 1] 5) :=
  Dec.shift (j := 134) (k := 4) (pvs_4 feat) w_134 (by decide)

/-- `movdqa xmm0, [rsp]; movdqu xmm1, [rsp + 17]`. -/
theorem bv_75 (prof : Profile) : BlkV prof tcg 75 86 [VOp.movdqa_m 0 4 0, VOp.movdqu_m 1 4 17] :=
  .cons (dv_75 _) VOpI.movdqa_m (lt_len (by decide)) <|
  .cons (dv_80 _) VOpI.movdqu_m (lt_len (by decide)) <|
  .nil 86

/-- The registers a call keeps, of `g'` as of `g`. -/
abbrev TCs (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- `TCs`, `rsp` and `r8`. -/
abbrev TKeep (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.r8 = g.r8 ∧ TCs g g'

theorem TCs.trans {g g' g'' : Gprs} (h : TCs g g') (h' : TCs g' g'') : TCs g g'' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h'
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

theorem t_fr_add (a : Addr) (d i : Nat) : Addr.add (a + BitVec.ofNat 64 d) i = Addr.add a (d + i) :=
  addr_add_add' a d i

/-- A store into the 60 bytes from `a` keeps a byte apart from them. -/
theorem t_vst_in {W : Addr → Byte} {a y c : Addr} {bs : List Byte} (hr : a.toNat + 60 ≤ 2 ^ 64)
    (hy : y.toNat < a.toNat ∨ a.toNat + 60 ≤ y.toNat) (hc0 : c.toNat < 60) (hd : c.toNat + bs.length ≤ 60) :
    Vst W (a + c) bs y = W y := by
  have e : (a + c).toNat = a.toNat + c.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  exact Tun.Vst_out W _ bs y (by rw [e]; omega) (by rw [e]; omega)

/-- A load apart from a store. -/
theorem t_rdq_vst {V : Addr → Byte} {a x : Addr} {bs : List Byte} (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst V a bs, x) = rdq(V, x) := by
  rw [Tun.rd_Vst V a bs x 8 ha hx h]

/-- A load of bytes that are the same. -/
theorem t_rdq_congr {V W : Addr → Byte} {x : Addr} (h : ∀ i < 8, W (Addr.add x i) = V (Addr.add x i)) :
    rdq(W, x) = rdq(V, x) := by
  congr 1
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h j hj

variable {F : Footprint} {Wl : List Rgn}

/-- From the `syscall` to the vector loads, the kernel's answer 0: `r9` is 0, the 8 bytes at `r8 + 36` cleared, the
bytes apart from the 60 at `r8` as they were. -/
theorem vc_42_zero {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax = 0)
    (hfr : ∀ d i, d + i < 48 → Foot F.data (Addr.add (g.rsp + BitVec.ofNat 64 d) i))
    (hwt : ∀ d i, d + i < 60 → Foot Wl (Addr.add (g.r8 + BitVec.ofNat 64 d) i)) (hr : g.r8.toNat + 60 ≤ 2 ^ 64) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 75 ∧ TKeep g g' ∧ g'.r9 = 0 ∧
      ∀ y : Addr, y.toNat < g.r8.toNat ∨ g.r8.toNat + 60 ≤ y.toNat → V' y = V y) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hfr hwt hr
  have he' : decide (WrErr rax) = false := decide_eq_false (by rw [hz]; unfold WrErr; decide)
  have hz' : (BitVec.setWidth 32 rax == 0) = true := by rw [hz]; decide
  wpx [W_42, W_176, W_50, W_57, o1, o6, o2, o3, Op.stf, ja_cmp, he', BitVec.and_self, hz', Bool.not_true]
  all_goals repeat' (first
    | rfl
    | (intro i hi; exact hfr _ i (by omega))
    | (intro i hi; exact hwt _ i (by omega))
    | (intro y hy; repeat rw [t_vst_in hr hy (by decide) (by simp)])
    | (subst hz; decide)
    | (intro h; exact absurd h (by decide))
    | constructor
    | intro _)

/-- The stretch 86–134 of the copy: the bytes apart from the 60 at `r8` as they were. -/
theorem vc_86 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfr : ∀ d i, d + i < 48 → Foot F.data (Addr.add (g.rsp + BitVec.ofNat 64 d) i))
    (hwt : ∀ d i, d + i < 60 → Foot Wl (Addr.add (g.r8 + BitVec.ofNat 64 d) i)) (hr : g.r8.toNat + 60 ≤ 2 ^ 64) :
    TcgC.W_86 F Wl (fun j' g' _ V' => j' = 134 ∧ TKeep g g' ∧ g'.r9 = g.r9 ∧
      ∀ y : Addr, y.toNat < g.r8.toNat ∨ g.r8.toNat + 60 ≤ y.toNat → V' y = V y) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfr hwt hr
  wpx [TcgC.W_86, TcgC.o0]
  all_goals repeat' (first
    | rfl
    | (intro i hi; exact hfr _ i (by omega))
    | (intro i hi; exact hwt _ i (by omega))
    | (intro y hy; repeat rw [t_vst_in hr hy (by decide) (by simp)])
    | (intro h; exact absurd h (by decide))
    | constructor
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 4000000 in
/-- `__tcgetattr (fd, termios_p)` from its entry to the return address at `rsp`. The frame (`k` = `rsp - 56`, 56
bytes) is aligned to 16, in what the run may store into (its first 48 bytes) and its data (with the return address);
`termios_p`'s 60 bytes are in what the run may store into, apart from the frame, the return address and the stack
guard at `fs:0x28`, `errno` apart from the frame and the guard. The run goes on with the return address popped, the
registers a call keeps as at the entry, after `ioctl (fd, TCGETS, k)` answered `r` with the bytes `bs`: an error, no
bytes, `eax` -1, `errno` = `-r`, the bytes as at the entry but `errno` and the stack guard in the frame; or 0, the 36
bytes of the kernel's `struct termios`, `rax` 0, the bytes as at the entry outside the frame and `*termios_p`. -/
theorem tcg_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L tcg_at tcg)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tcg_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hk : (X.cpu.gpr.rsp - 56#64).toNat + 64 ≤ 2 ^ 64) (hal : (X.cpu.gpr.rsp - 56#64).toNat % 16 = 0)
    (hkw : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56#64) i))
    (hkr : ∀ i < 64, Foot F.data (Addr.add (X.cpu.gpr.rsp - 56#64) i))
    (htop : (X.cpu.gpr.rsp - 56#64).toNat + 36 ≤ userPtrMax prof.feat)
    (hr : X.cpu.gpr.rsi.toNat + 60 ≤ 2 ^ 64) (htw : ∀ i < 60, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (hrk : X.cpu.gpr.rsi.toNat + 60 ≤ (X.cpu.gpr.rsp - 56#64).toNat ∨
      (X.cpu.gpr.rsp - 56#64).toNat + 64 ≤ X.cpu.gpr.rsi.toNat)
    (hrg : X.cpu.gpr.rsi.toNat + 60 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hgk : (fb + 40#64).toNat + 8 ≤ (X.cpu.gpr.rsp - 56#64).toNat ∨
      (X.cpu.gpr.rsp - 56#64).toNat + 64 ≤ (fb + 40#64).toNat)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ (X.cpu.gpr.rsp - 56#64).toNat ∨
      (X.cpu.gpr.rsp - 56#64).toNat + 64 ≤ (errnoAt fb).toNat)
    (hedc : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (r : BitVec 64) (bs : List Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → TCs X.cpu.gpr Z.cpu.gpr →
      (WrErr r ∧ bs = [] ∧ Z.cpu.gpr.rax = BitVec.setWidth 64 4294967295#32 ∧
          Agree F Z.proc.mm.mem (Vst (tV V X.cpu.gpr fb) (errnoAt fb) (errnoB r))) ∨
        (r = 0 ∧ bs.length = 36 ∧ Z.cpu.gpr.rax = 0 ∧ ∃ W : Addr → Byte, Agree F Z.proc.mm.mem W ∧
          ∀ y : Addr, (y.toNat < (X.cpu.gpr.rsp - 56#64).toNat ∨ (X.cpu.gpr.rsp - 56#64).toNat + 56 ≤ y.toNat) →
            (y.toNat < X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 60 ≤ y.toNat) → W y = V y) →
      GoG prof L o (gev ++ [tcEv (tg1 X.cpu.gpr) r bs]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- the frame
  have e40 : (X.cpu.gpr.rsp - 56#64 + 40#64).toNat = (X.cpu.gpr.rsp - 56#64).toNat + 40 :=
    toNat_add_of_fits (a := X.cpu.gpr.rsp - 56#64) (i := 40) (n := 64) (by decide) hk
  have e56 : (X.cpu.gpr.rsp - 56#64 + 56#64).toNat = (X.cpu.gpr.rsp - 56#64).toNat + 56 :=
    toNat_add_of_fits (a := X.cpu.gpr.rsp - 56#64) (i := 56) (n := 64) (by decide) hk
  have FR : ∀ g : Gprs, g.rsp = X.cpu.gpr.rsp - 56#64 → ∀ d i, d + i < 48 →
      Foot F.data (Addr.add (g.rsp + BitVec.ofNat 64 d) i) := fun g hg d i h => by
    rw [hg, t_fr_add]; exact hkr _ (by omega)
  have FW : ∀ g : Gprs, g.r8 = X.cpu.gpr.rsi → ∀ d i, d + i < 60 →
      Foot Wl (Addr.add (g.r8 + BitVec.ofNat 64 d) i) := fun g hg d i h => by
    rw [hg, t_fr_add]; exact htw _ h
  have FT : ∀ g : Gprs, g.r8 = X.cpu.gpr.rsi → g.r8.toNat + 60 ≤ 2 ^ 64 := fun g hg => by rw [hg]; exact hr
  -- the stack guard in the frame
  have hgd1 : rdq(tV V X.cpu.gpr fb, X.cpu.gpr.rsp - 56#64 + 40#64) = rdq(V, fb + 40#64) := by
    unfold tV
    rw [Tun.rd_Vst_self _ (X.cpu.gpr.rsp - 56#64 + 40#64) _ (toBytesLE_length _ _) (by rw [e40]; omega),
      ofBytesLE_toBytesLE (n := 8) rfl]
  have htv : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 → ((X.cpu.gpr.rsp - 56#64).toNat + 48 ≤ x.toNat ∨
      x.toNat + 8 ≤ (X.cpu.gpr.rsp - 56#64).toNat + 40) → rdq(tV V X.cpu.gpr fb, x) = rdq(V, x) := by
    intro x hx h
    unfold tV
    exact t_rdq_vst (by rw [toBytesLE_length, e40]; omega) hx (by rw [toBytesLE_length, e40]; omega)
  have hgk' : rdq(tV V X.cpu.gpr fb, fb + 40#64) = rdq(V, fb + 40#64) := htv _ hcf (by omega)
  have hgr : rdq(tV V X.cpu.gpr fb, X.cpu.gpr.rsp - 56#64 + 56#64) = rdq(V, X.cpu.gpr.rsp) := by
    rw [htv (X.cpu.gpr.rsp - 56#64 + 56#64) (by rw [e56]; omega) (by rw [e56]; omega), BitVec.sub_add_cancel]
  -- to the `syscall`
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 40 ∧ g' = tg1 X.cpu.gpr ∧ V' = tV V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcl fun i hi => by rw [t_fr_add]; exact hkw _ (by omega)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y1 t1 hK1 hA1 hr1 hg1 -
  -- the `syscall`
  refine c.s_tcgets hK1 hA1 hin (lt_len (by decide)) hr1 (sys_40 _)
    (by rw [hg1]; exact (by decide : (BitVec.setWidth 64 16#32).toNat % 2 ^ 32 = 16))
    (by rw [hg1]; exact (by decide : arg32 (BitVec.setWidth 64 21505#32) = 21505))
    (by rw [hg1]; exact htop) (fun i hi => by rw [hg1]; exact hkw i (by omega)) ?_
  intro r bs hrb Y tY hKY hAY ⟨hrY, hgY⟩
  have hdx : Y1.cpu.gpr.rdx = X.cpu.gpr.rsp - 56#64 := by rw [hg1]; try rfl
  rw [hdx] at hAY
  simp only [sysGpr, hg1] at hgY
  have hax : Y.cpu.gpr.rax = r := by rw [hgY]; try rfl
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := by rw [hgY]; try rfl
  have h8Y : Y.cpu.gpr.r8 = X.cpu.gpr.rsi := by rw [hgY]; try rfl
  have cY : TCs X.cpu.gpr Y.cpu.gpr := by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hg1]
  rcases hrb with ⟨he, rfl⟩ | ⟨rfl, hb⟩
  · -- an error
    simp only [Vst] at hAY
    have heb : (errnoB Y.cpu.gpr.rax).length = 4 := toBytesLE_length _ _
    have hE : (errnoAt fb).toNat + (errnoB Y.cpu.gpr.rax).length ≤ 2 ^ 64 := by rw [heb]; exact hfe
    have hcE : rdq(Vst (tV V X.cpu.gpr fb) (errnoAt fb) (errnoB Y.cpu.gpr.rax), X.cpu.gpr.rsp - 56#64 + 40#64) =
        rdq(Vst (tV V X.cpu.gpr fb) (errnoAt fb) (errnoB Y.cpu.gpr.rax), fb + 40#64) := by
      rw [t_rdq_vst hE (x := X.cpu.gpr.rsp - 56#64 + 40#64) (by rw [e40]; omega) (by rw [heb, e40]; omega),
        t_rdq_vst hE hcf (by rw [heb]; exact hedc), hgd1, hgk']
    have hrE : rdq(Vst (tV V X.cpu.gpr fb) (errnoAt fb) (errnoB Y.cpu.gpr.rax), X.cpu.gpr.rsp - 56#64 + 56#64) =
        e₂.add j₂ := by
      rw [t_rdq_vst hE (x := X.cpu.gpr.rsp - 56#64 + 56#64) (by rw [e56]; omega) (by rw [heb, e56]; omega), hgr]
      exact hra
    refine (c_42 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 143 ∧ g' = tErr Y.cpu.gpr ∧
        V' = Vst (tV V X.cpu.gpr fb) (errnoAt fb) (errnoB Y.cpu.gpr.rax))
      hKY hAY hrY (vc_42_err (by rw [hax]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hs1 : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := by rw [hgZ₁]; exact hsY
    have c1 : TCs X.cpu.gpr Z₁.cpu.gpr := by rw [hgZ₁]; exact cY
    refine (c_143 prof fb).run c hfs hin _ hKZ₁ hAZ₁ hrZ₁
      (vc_143 (g := Z₁.cpu.gpr) (fun i hi => by rw [hs1, t_fr_add]; exact hkr _ (by omega)) hcl
        (by rw [hs1]; exact hcE)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 + 56#64 := by rw [hgZ₂, hs1]; try rfl
    have c2 : TCs X.cpu.gpr Z₂.cpu.gpr := by rw [hgZ₂]; exact c1
    refine c.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_166 _)
      (fun i hi => by rw [hs2, t_fr_add]; exact hkr _ (by omega)) hin₂ h₂ (by rw [hs2]; exact hrE) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    have c3 : TCs X.cpu.gpr Z₃.cpu.gpr := by rw [hgZ₃]; exact c2
    have hsp : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 := by
      rw [hgZ₃]; show Z₂.cpu.gpr.rsp + 8 = _; rw [hs2, BitVec.sub_add_cancel]
    have hx3 : Z₃.cpu.gpr.rax = BitVec.setWidth 64 4294967295#32 := by
      rw [hgZ₃, hgZ₂, hgZ₁]; first | rfl | decide
    rw [hax] at hAZ₃
    exact k r [] Z₃ t₃ hKZ₃ hrZ₃ hsp c3 (Or.inl ⟨he, rfl, hx3, hAZ₃⟩)
  · -- 0: the copy
    have hz : Y.cpu.gpr.rax = 0 := hax
    have hk36 : (X.cpu.gpr.rsp - 56#64).toNat + bs.length ≤ 2 ^ 64 := by rw [hb]; omega
    refine (c_42 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 75 ∧ TKeep Y.cpu.gpr g' ∧ g'.r9 = 0 ∧
        ∀ y : Addr, y.toNat < Y.cpu.gpr.r8.toNat ∨ Y.cpu.gpr.r8.toNat + 60 ≤ y.toNat →
          V' y = Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs y)
      hKY hAY hrY (vc_42_zero hz (FR _ hsY) (FW _ h8Y) (FT _ h8Y)) ?_
    rintro j' g fl V₃ ⟨rfl, hq3, h93, hV3⟩ Y3 t3 hK3 hA3 hr3 rfl -
    have hs3 : Y3.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := hq3.1.trans hsY
    have h83 : Y3.cpu.gpr.r8 = X.cpu.gpr.rsi := hq3.2.1.trans h8Y
    have cs3 : TCs X.cpu.gpr Y3.cpu.gpr := TCs.trans cY hq3.2.2
    -- the vector loads
    refine c.s_blkV hin (bv_75 prof) hK3 hA3 hr3 ?_
    refine wpV_v (fun i hi => FR _ hs3 0 i (by omega)) (fun _ => ?_)
      (wpV_v (fun i hi => FR _ hs3 17 i (by omega)) (fun h => absurd h (by decide)) ?_)
    · show (Addr.add Y3.cpu.gpr.rsp 0).toNat % 16 = 0
      rw [addr_add_zero, hs3]; exact hal
    intro Y4 t4 hK4 hA4 hr4 hg4 _ _
    have hg4' : Y4.cpu.gpr = Y3.cpu.gpr := hg4
    have hs4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := by rw [hg4']; exact hs3
    have h84 : Y4.cpu.gpr.r8 = X.cpu.gpr.rsi := by rw [hg4']; exact h83
    -- 86–134
    refine (TcgC.c_86 prof).run c hin
      (fun j' g' _ V' => j' = 134 ∧ TKeep Y4.cpu.gpr g' ∧ g'.r9 = Y4.cpu.gpr.r9 ∧
        ∀ y : Addr, y.toNat < Y4.cpu.gpr.r8.toNat ∨ Y4.cpu.gpr.r8.toNat + 60 ≤ y.toNat → V' y = V₃ y)
      hK4 hA4 hr4 (vc_86 (FR _ hs4) (FW _ h84) (FT _ h84)) ?_
    rintro j' g fl V₄ ⟨rfl, hq4, h94, hV4⟩ Y5 t5 hK5 hA5 hr5 rfl -
    have hs5 : Y5.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := hq4.1.trans hs4
    have h85 : Y5.cpu.gpr.r8 = X.cpu.gpr.rsi := hq4.2.1.trans h84
    have h95 : Y5.cpu.gpr.r9 = 0 := h94.trans (by rw [hg4']; exact h93)
    have cs5 : TCs X.cpu.gpr Y5.cpu.gpr := TCs.trans (by rw [hg4']; exact cs3) hq4.2.2
    -- the vector stores
    refine c.s_movups_st hK5 hA5 hin (lt_len (by decide)) hr5 (ds_134 _) (fun i hi => FW _ h85 0 i (by omega)) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have h86 : Y6.cpu.gpr.r8 = X.cpu.gpr.rsi := by rw [hg6]; exact h85
    refine c.s_movups_st hK6 hA6 hin (lt_len (by decide)) hr6 (ds_138 _) (fun i hi => FW _ h86 17 i (by omega)) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    have hV7 : ∀ y : Addr, y.toNat < X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 60 ≤ y.toNat →
        Vst (Vst V₄ (eaD Y5 8 0) (toBytesLE (xlo Y5 0) 16)) (eaD Y6 8 17) (toBytesLE (xlo Y6 1) 16) y =
          Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs y := by
      intro y hy
      have e5 : eaD Y5 8 0 = X.cpu.gpr.rsi + BitVec.ofNat 64 0 := by
        show Y5.cpu.gpr.r8 + _ = _; rw [h85]
      have e6 : eaD Y6 8 17 = X.cpu.gpr.rsi + BitVec.ofNat 64 17 := by
        show Y6.cpu.gpr.r8 + _ = _; rw [h86]
      rw [e6, t_vst_in (c := BitVec.ofNat 64 17) (bs := toBytesLE (xlo Y6 1) 16) hr hy (by decide)
          (by rw [toBytesLE_length]; decide),
        e5, t_vst_in (c := BitVec.ofNat 64 0) (bs := toBytesLE (xlo Y5 0) 16) hr hy (by decide)
          (by rw [toBytesLE_length]; decide),
        hV4 y (by rw [hg4', h83]; exact hy), hV3 y (by rw [h8Y]; exact hy)]
    obtain ⟨W7, hA7', hW7⟩ : ∃ W : Addr → Byte, Agree F Y7.proc.mm.mem W ∧
        ∀ y : Addr, y.toNat < X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 60 ≤ y.toNat →
          W y = Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs y := ⟨_, hA7, hV7⟩
    have hg75 : Y7.cpu.gpr = Y5.cpu.gpr := hg7.trans hg6
    have hs7 : Y7.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 := by rw [hg75]; exact hs5
    have h97 : Y7.cpu.gpr.r9 = 0 := by rw [hg75]; exact h95
    have cs7 : TCs X.cpu.gpr Y7.cpu.gpr := by rw [hg75]; exact cs5
    have apT : ∀ d i, d + i < 64 →
        (Addr.add (X.cpu.gpr.rsp - 56#64 + BitVec.ofNat 64 d) i).toNat < X.cpu.gpr.rsi.toNat ∨
          X.cpu.gpr.rsi.toNat + 60 ≤ (Addr.add (X.cpu.gpr.rsp - 56#64 + BitVec.ofNat 64 d) i).toNat :=
      fun d i h => by rw [t_fr_add, toNat_add_of_fits h hk]; omega
    have g1 : rdq(W7, X.cpu.gpr.rsp - 56#64 + 40#64) =
        rdq(Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs, X.cpu.gpr.rsp - 56#64 + 40#64) :=
      t_rdq_congr fun i hi => hW7 _ (apT 40 i (by omega))
    have g2 : rdq(W7, fb + 40#64) = rdq(Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs, fb + 40#64) :=
      t_rdq_congr fun i hi => hW7 _ (by rw [toNat_add_of_fits hi hcf]; omega)
    have g3 : rdq(W7, X.cpu.gpr.rsp - 56#64 + 56#64) =
        rdq(Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs, X.cpu.gpr.rsp - 56#64 + 56#64) :=
      t_rdq_congr fun i hi => hW7 _ (apT 56 i (by omega))
    have hcO : rdq(W7, X.cpu.gpr.rsp - 56#64 + 40#64) = rdq(W7, fb + 40#64) := by
      rw [g1, g2, t_rdq_vst hk36 (x := X.cpu.gpr.rsp - 56#64 + 40#64) (by rw [e40]; omega) (by rw [hb, e40]; omega),
        t_rdq_vst hk36 hcf (by rw [hb]; omega), hgd1, hgk']
    have hrO : rdq(W7, X.cpu.gpr.rsp - 56#64 + 56#64) = e₂.add j₂ := by
      rw [g3, t_rdq_vst hk36 (x := X.cpu.gpr.rsp - 56#64 + 56#64) (by rw [e56]; omega) (by rw [hb, e56]; omega),
        hgr]
      exact hra
    -- the stack guard, the `ret`
    refine (c_143 prof fb).run c hfs hin _ hK7 hA7' hr7
      (vc_143 (g := Y7.cpu.gpr) (fun i hi => by rw [hs7, t_fr_add]; exact hkr _ (by omega)) hcl
        (by rw [hs7]; exact hcO)) ?_
    rintro j' g fl V₈ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 56#64 + 56#64 := by rw [hgZ₂, hs7]; try rfl
    have c2 : TCs X.cpu.gpr Z₂.cpu.gpr := by rw [hgZ₂]; exact cs7
    refine c.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_166 _)
      (fun i hi => by rw [hs2, t_fr_add]; exact hkr _ (by omega)) hin₂ h₂ (by rw [hs2]; exact hrO) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    have c3 : TCs X.cpu.gpr Z₃.cpu.gpr := by rw [hgZ₃]; exact c2
    have hsp : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 := by
      rw [hgZ₃]; show Z₂.cpu.gpr.rsp + 8 = _; rw [hs2, BitVec.sub_add_cancel]
    have hx3 : Z₃.cpu.gpr.rax = 0 := by
      rw [hgZ₃]; show Z₂.cpu.gpr.rax = 0; rw [hgZ₂]
      show BitVec.setWidth 64 (BitVec.setWidth 32 Y7.cpu.gpr.r9) = 0
      rw [h97]; first | rfl | decide
    have hout : ∀ y : Addr, (y.toNat < (X.cpu.gpr.rsp - 56#64).toNat ∨
        (X.cpu.gpr.rsp - 56#64).toNat + 56 ≤ y.toNat) →
        Vst (tV V X.cpu.gpr fb) (X.cpu.gpr.rsp - 56#64) bs y = V y := by
      intro y hy
      have hb8 : (toBytesLE rdq(V, fb + 40#64) 8).length = 8 := toBytesLE_length _ _
      rw [Tun.Vst_out _ _ _ y hk36 (by rw [hb]; omega)]
      unfold tV
      rw [Tun.Vst_out V (X.cpu.gpr.rsp - 56#64 + 40#64) (toBytesLE rdq(V, fb + 40#64) 8) y
        (by rw [hb8, e40]; omega) (by rw [hb8, e40]; omega)]
    exact k 0 bs Z₃ t₃ hKZ₃ hrZ₃ hsp c3
      (Or.inr ⟨rfl, hb, hx3, _, hAZ₃, fun y h1 h2 => (hW7 y h2).trans (hout y h1)⟩)

end FV7z.Tcg
