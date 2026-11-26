import FV7z.Ity.Cuts
import FV7z.Tcg.Ok
import FV7z.Sga.Holds
/-!
# `__isatty` asks `__tcgetattr` and answers 1 or 0 (PLAN.md §M, M1)

glibc 2.31's `__isatty (fd)` at `0x665d20` in `7zzs` (`sysdeps/unix/sysv/linux/isatty.c`): a frame of 88 bytes with
the stack guard (`fs:0x28`) at `rsp - 16`, `__tcgetattr (fd, rsp - 88)` (`Tcg.tcg_ok`), then `eax` = (the answer
is 0). Two pieces of the code (`Ity/Cuts.lean`) around the call: from the entry (0) to the `call` (27), from after it
(32) to the `ret` (60).

- `ig1`, `iV1`: the registers and the bytes at the `call`; `ig2`: the registers at `__tcgetattr`'s entry.
- `rdq_out`: a load of bytes that a run kept.
- `vc_0`, `vc_32`: the verification conditions of the pieces.
- `ity_ok`: from the entry to the return address: `rax` 1 if `__tcgetattr` answered 0, else 0 with `errno` set;
  the bytes outside the frame and `errno` as before.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Ity

/-- The `call __tcgetattr`. -/
def pcall : List Byte := [0xe8, 0x00, 0x05, 0x00, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 1280] 5) := by dec_rfl
theorem w_27 : pcall <+: ity.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat ity 27 (FV7z.mk .call 64 [.rel 1280] 5) :=
  Dec.shift (j := 27) (k := 0) (pcall_0 feat) w_27 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_60 : pret <+: ity.drop 60 := by decide +kernel
theorem ret_60 (feat : Features) : Dec feat ity 60 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 60) (k := 0) (pret_0 feat) w_60 (Nat.zero_le _)

/-! ## The frame -/

theorem t88 {rs : Addr} (h : 152 ≤ rs.toNat) : (rs - 88#64).toNat = rs.toNat - 88 := by
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t96 {rs : Addr} (h : 152 ≤ rs.toNat) : (rs - 96#64).toNat = rs.toNat - 96 := by
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t152 {rs : Addr} (h : 152 ≤ rs.toNat) : (rs - 152#64).toNat = rs.toNat - 152 := by
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t16 {rs : Addr} (h : 152 ≤ rs.toNat) : (rs - 88#64 + 72#64).toNat = rs.toNat - 16 := by
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `__tcgetattr`'s stack guard slot. -/
theorem t112 {rs : Addr} (h : 152 ≤ rs.toNat) : (rs - 152#64 + 40#64).toNat = rs.toNat - 112 := by
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The return address's slot of the call. -/
theorem e96 {rs : Addr} (h : 152 ≤ rs.toNat) : rs - 88#64 - 8 = rs - 96#64 := by
  apply BitVec.eq_of_toNat_eq
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

/-- `__tcgetattr`'s frame. -/
theorem e152 {rs : Addr} (h : 152 ≤ rs.toNat) : rs - 96#64 - 56#64 = rs - 152#64 := by
  apply BitVec.eq_of_toNat_eq
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem e88 {rs : Addr} (h : 152 ≤ rs.toNat) : rs - 96#64 + 8 = rs - 88#64 := by
  apply BitVec.eq_of_toNat_eq
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

/-- An address of the frame's 160 bytes (152 and the return address). -/
theorem fa {rs x : Addr} (h : 152 ≤ rs.toNat) {d : Nat} (hd : d ≤ 160) (hx : x.toNat = rs.toNat - 152 + d)
    (hf : rs.toNat + 8 ≤ 2 ^ 64) : x = Addr.add (rs - 152#64) d := by
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_add_of_fits (i := d) (n := d + 1) (by omega) (by rw [t152 h]; omega), t152 h]

theorem fr {P : Addr → Prop} {rs x : Addr} {m : Nat} (h : ∀ i < m, P (Addr.add (rs - 152#64) i)) {d n : Nat}
    (hx : x = Addr.add (rs - 152#64) d) (hdn : d + n ≤ m) : ∀ i < n, P (Addr.add x i) := fun i hi => by
  rw [hx, addr_add_add']
  exact h (d + i) (by omega)

/-- A load of bytes that are the same. -/
theorem rdq_out {W V : Addr → Byte} {x : Addr} (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ y : Addr, x.toNat ≤ y.toNat → y.toNat < x.toNat + 8 → W y = V y) : rdq(W, x) = rdq(V, x) :=
  Tcg.t_rdq_congr fun i hi =>
    h _ (by rw [toNat_add_of_fits (i := i) (n := 8) hi hx]; omega)
      (by rw [toNat_add_of_fits (i := i) (n := 8) hi hx]; omega)

/-- The registers at the `call`, the function called with registers `g` and the stack guard `c`. -/
def ig1 (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 c ^^^ BitVec.setWidth 32 c)
    rsp := g.rsp - 88#64
    rsi := g.rsp - 88#64 }

/-- The registers at `__tcgetattr`'s entry. -/
def ig2 (g : Gprs) (c : BitVec 64) : Gprs := (ig1 g c).set 4 ((ig1 g c).rsp - 8)

/-- The bytes at the `call`: the stack guard at `rsp - 16`. -/
def iV1 (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst V (g.rsp - 88#64 + 72#64) (toBytesLE rdq(V, fb + 40#64) 8)

/-- A byte apart from the two stores before the call. -/
theorem v2_out {V : Addr → Byte} {g : Gprs} {fb y : Addr} (h : 152 ≤ g.rsp.toNat) (hf : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hy : y.toNat < g.rsp.toNat - 96 ∨ g.rsp.toNat - 88 ≤ y.toNat)
    (hy' : y.toNat < g.rsp.toNat - 16 ∨ g.rsp.toNat - 8 ≤ y.toNat) (ra : Addr) :
    Vst (iV1 V g fb) (g.rsp - 96#64) (toBytesLE ra 8) y = V y := by
  unfold iV1
  rw [Sga.vo (n := 8) (toBytesLE_length _ _) (by rw [t96 h]; omega) (by rw [t96 h]; omega),
    Sga.vo (n := 8) (toBytesLE_length _ _) (by rw [t16 h]; omega) (by rw [t16 h]; omega)]

/-- The stack guard in the frame. -/
theorem v2_can {V : Addr → Byte} {g : Gprs} {fb : Addr} (h : 152 ≤ g.rsp.toNat) (hf : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (ra : Addr) :
    rdq(Vst (iV1 V g fb) (g.rsp - 96#64) (toBytesLE ra 8), g.rsp - 88#64 + 72#64) = rdq(V, fb + 40#64) := by
  unfold iV1
  rw [Tcg.t_rdq_vst (by rw [toBytesLE_length, t96 h]; omega) (by rw [t16 h]; omega)
      (by rw [toBytesLE_length, t96 h, t16 h]; omega),
    Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [t16 h]; omega), ofBytesLE_toBytesLE (n := 8) rfl]

/-- The stack guard's source, apart from the frame. -/
theorem v2_fb {V : Addr → Byte} {g : Gprs} {fb : Addr} (h : 152 ≤ g.rsp.toNat) (hf : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 152 ∨ g.rsp.toNat + 8 ≤ (fb + 40#64).toNat) (ra : Addr) :
    rdq(Vst (iV1 V g fb) (g.rsp - 96#64) (toBytesLE ra 8), fb + 40#64) = rdq(V, fb + 40#64) := by
  unfold iV1
  rw [Tcg.t_rdq_vst (by rw [toBytesLE_length, t96 h]; omega) hcb (by rw [toBytesLE_length, t96 h]; omega),
    Tcg.t_rdq_vst (by rw [toBytesLE_length, t16 h]; omega) hcb (by rw [toBytesLE_length, t16 h]; omega)]

/-- The return address, apart from the frame. -/
theorem v2_rsp {V : Addr → Byte} {g : Gprs} {fb : Addr} (h : 152 ≤ g.rsp.toNat) (hf : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (ra : Addr) : rdq(Vst (iV1 V g fb) (g.rsp - 96#64) (toBytesLE ra 8), g.rsp) = rdq(V, g.rsp) := by
  unfold iV1
  rw [Tcg.t_rdq_vst (by rw [toBytesLE_length, t96 h]; omega) hf (by rw [toBytesLE_length, t96 h]; omega),
    Tcg.t_rdq_vst (by rw [toBytesLE_length, t16 h]; omega) hf (by rw [toBytesLE_length, t16 h]; omega)]

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to the `call`: the stack guard stored in the frame, `rsi` the frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 88#64 + 72#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 27 ∧ g' = ig1 g rdq(V, fb + 40#64) ∧ V' = iV1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw
  wpx [W_0, o0, Op.ldf]
  all_goals vc_fin

/-- From after the `call` to the `ret`: `eax` = (`eax` was 0), the stack guard checked, the frame dropped. -/
theorem vc_32 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (a : BitVec 64)
    (hax : (g.rax = 0 ∧ a = 1#64) ∨ (g.rax = BitVec.setWidth 64 4294967295#32 ∧ a = 0#64))
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hc : rdq(V, g.rsp + 72#64) = rdq(V, fb + 40#64))
    (h : ∀ d fl, Q 60 { g with rax := a, rdx := d, rsp := g.rsp + 88#64 } fl V) :
    W_32 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hl hc h
  rcases hax with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · wpx [W_32, W_53, o1, o2, Op.xormf, Op.setcc, Op.zxr, hc, BitVec.xor_self, ↓reduceIte]
    repeat' (first | exact h _ _ | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _)

/-- The registers a call keeps. -/
abbrev Kp (g h : Gprs) : Prop := Tcg.TCs h g

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__isatty (fd)` from its entry to the return address, the frame's 152 bytes below the stack pointer (88, the
call's return address, `__tcgetattr`'s 56) in what the run may store into, `rsp` 8 modulo 16 as at a call's entry,
the stack guard and `errno` apart from the frame: the run goes on with the return address popped, the registers a
call keeps as at the entry, `rax` 1 if `__tcgetattr` answered 0 and 0 if it failed, the bytes outside the frame and
`errno` as before. -/
theorem ity_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L ity_at ity)
    (hint : CodeIn L Tcg.tcg_at Tcg.tcg) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = ity_at) (h152 : 152 ≤ X.cpu.gpr.rsp.toNat) (hal : X.cpu.gpr.rsp.toNat % 16 = 8)
    (hup : X.cpu.gpr.rsp.toNat + 8 ≤ userPtrMax prof.feat)
    (hfw : ∀ i < 152, Foot Wl (Addr.add (X.cpu.gpr.rsp - 152#64) i))
    (hfd : ∀ i < 160, Foot F.data (Addr.add (X.cpu.gpr.rsp - 152#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 152 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (fb + 40#64).toNat)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 152 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (hedc : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (rc : BitVec 64) (bs : List Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Kp Z.cpu.gpr X.cpu.gpr →
      ((rc = 0 ∧ Z.cpu.gpr.rax = 1#64) ∨ (WrErr rc ∧ Z.cpu.gpr.rax = 0#64)) →
      (∃ W : Addr → Byte, Agree F Z.proc.mm.mem W ∧ ∀ y : Addr,
        (y.toNat < X.cpu.gpr.rsp.toNat - 152 ∨ X.cpu.gpr.rsp.toNat ≤ y.toNat) →
        (y.toNat < (errnoAt fb).toNat ∨ (errnoAt fb).toNat + 4 ≤ y.toNat) → W y = V y) →
      GoG prof L o (gev ++ [tcEv (Tcg.tg1 (ig2 X.cpu.gpr rdq(V, fb + 40#64))) rc bs]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hpm : userPtrMax prof.feat ≤ 2 ^ 64 := by unfold userPtrMax; split <;> decide
  have a88 := t88 h152
  have a96 := t96 h152
  have a152 := t152 h152
  have a16 := t16 h152
  have hf8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by omega
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 27 ∧ g' = ig1 X.cpu.gpr rdq(V, fb + 40#64) ∧ V' = iV1 V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcl (fr hfw (fa h152 (d := 136) (by decide) (by rw [a16]; omega) hf8) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 88#64 := by rw [hgY]; try rfl
  have hcs : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 96#64 := by rw [hYsp]; exact e96 h152
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_27 _) hint (Tcg.lt_len (by decide)) (by decide)
    (by rw [hcs]; exact fr hfw (fa h152 (d := 56) (by decide) (by rw [a96]; omega) hf8) (by decide)) ?_
  rintro Y₂ t₂ hKY₂ hAY₂ ⟨hrY₂, hgY₂⟩
  rw [hcs] at hAY₂
  -- the bytes `__tcgetattr` starts from
  have hY2sp : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 96#64 := by rw [hgY₂]; exact hcs
  have hY2si : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsp - 88#64 := by rw [hgY₂, hgY]; try rfl
  have hY2f : Y₂.cpu.gpr.rsp - 56#64 = X.cpu.gpr.rsp - 152#64 := by rw [hY2sp]; exact e152 h152
  have kY₂ : Tcg.TCs X.cpu.gpr Y₂.cpu.gpr := by rw [hgY₂, hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hev : Tcg.tg1 Y₂.cpu.gpr = Tcg.tg1 (ig2 X.cpu.gpr rdq(V, fb + 40#64)) := by
    rw [hgY₂, hgY]
    try rfl
  have hra₂ : rdq(Vst (iV1 V X.cpu.gpr fb) (X.cpu.gpr.rsp - 96#64) (toBytesLE (ity_at.add (27 + 5)) 8),
      Y₂.cpu.gpr.rsp) = ity_at.add 32 := by
    rw [hY2sp, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [a96]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
  refine Tcg.tcg_ok c hfs hint hKY₂ hAY₂ hrY₂ hcl hcb
    (by rw [hY2f, a152]; omega) (by rw [hY2f, a152]; omega)
    (by rw [hY2f]; exact fun i hi => hfw i (by omega))
    (by rw [hY2f]; exact fun i hi => hfd i (by omega))
    (by rw [hY2f, a152]; omega)
    (by rw [hY2si, a88]; omega)
    (by rw [hY2si]; exact fr hfw (fa h152 (d := 64) (by decide) (by rw [a88]; omega) hf8) (by decide))
    (by rw [hY2si, hY2f, a88, a152]; omega)
    (by rw [hY2si, a88]; omega)
    (by rw [hY2f, a152]; omega)
    fe hfe (by rw [hY2f, a152]; omega) hedc hin (j₂ := 32) (lt_len (by decide)) hra₂ ?_
  intro rc bs Z t₃ hKZ hrZ hZsp' kZ' hcase
  rw [hev]
  have hZsp : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 88#64 := by rw [hZsp', hY2sp]; exact e88 h152
  have kZ : Tcg.TCs X.cpu.gpr Z.cpu.gpr := Tcg.TCs.trans kY₂ kZ'
  -- what `__tcgetattr` left: the bytes `W`, `rax` and what `__isatty` makes of it
  obtain ⟨W, a, hAW, hWo, hax, hres⟩ : ∃ (W : Addr → Byte) (a : BitVec 64), Agree F Z.proc.mm.mem W ∧
      (∀ y : Addr, (y.toNat < X.cpu.gpr.rsp.toNat - 152 ∨ X.cpu.gpr.rsp.toNat - 96 ≤ y.toNat) →
        (y.toNat < X.cpu.gpr.rsp.toNat - 88 ∨ X.cpu.gpr.rsp.toNat - 28 ≤ y.toNat) →
        (y.toNat < (errnoAt fb).toNat ∨ (errnoAt fb).toNat + 4 ≤ y.toNat) →
        W y = Vst (iV1 V X.cpu.gpr fb) (X.cpu.gpr.rsp - 96#64) (toBytesLE (ity_at.add (27 + 5)) 8) y) ∧
      ((Z.cpu.gpr.rax = 0 ∧ a = 1#64) ∨ (Z.cpu.gpr.rax = BitVec.setWidth 64 4294967295#32 ∧ a = 0#64)) ∧
      ((rc = 0 ∧ a = 1#64) ∨ (WrErr rc ∧ a = 0#64)) := by
    rcases hcase with ⟨hw, -, hr, hA'⟩ | ⟨h0, -, hr, W, hA', hW⟩
    · refine ⟨_, 0#64, hA', fun y h1 h2 h3 => ?_, Or.inr ⟨hr, rfl⟩, Or.inr ⟨hw, rfl⟩⟩
      rw [Sga.vo (toBytesLE_length _ _) hfe h3]
      unfold Tcg.tV
      rw [hY2f]
      exact Sga.vo (n := 8) (toBytesLE_length _ _) (by rw [t112 h152]; omega) (by rw [t112 h152]; omega)
    · refine ⟨W, 1#64, hA', fun y h1 h2 _ => hW y ?_ ?_, Or.inl ⟨hr, rfl⟩, Or.inl ⟨h0, rfl⟩⟩
      · rw [hY2f, a152]; omega
      · rw [hY2si, a88]; omega
  -- the stack guard and the return address, as stored
  have c1 : rdq(W, X.cpu.gpr.rsp - 88#64 + 72#64) = rdq(V, fb + 40#64) :=
    (rdq_out (by rw [a16]; omega) fun y h1 h2 => by
      rw [a16] at h1 h2
      exact hWo y (by omega) (by omega) (by omega)).trans (v2_can h152 hf8 _)
  have c2 : rdq(W, fb + 40#64) = rdq(V, fb + 40#64) :=
    (rdq_out hcb fun y h1 h2 => hWo y (by omega) (by omega) (by omega)).trans (v2_fb h152 hf8 hcb hcd _)
  have c3 : rdq(W, X.cpu.gpr.rsp) = rdq(V, X.cpu.gpr.rsp) :=
    (rdq_out hf8 fun y h1 h2 => hWo y (by omega) (by omega) (by omega)).trans (v2_rsp h152 hf8 _)
  have hc : rdq(W, Z.cpu.gpr.rsp + 72#64) = rdq(W, fb + 40#64) := by rw [hZsp, c1, c2]
  refine (c_32 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 60 ∧ ∃ d, g' = { Z.cpu.gpr with rax := a, rdx := d, rsp := Z.cpu.gpr.rsp + 88#64 } ∧
      V' = W) hKZ hAW hrZ
    (vc_32 a hax (by rw [hZsp]; exact fr hfd (fa h152 (d := 136) (by decide) (by rw [a16]; omega) hf8) (by decide))
      hcl hc fun d _ => ⟨rfl, d, rfl, rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, d, rfl, rfl⟩ Z₄ t₅ hKZ₄ hAZ₄ hrZ₄ hgZ₄ -
  have hZ4sp : Z₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hgZ₄]
    show Z.cpu.gpr.rsp + 88#64 = _
    rw [hZsp]
    exact BitVec.sub_add_cancel _ _
  have kZ₄ : Tcg.TCs X.cpu.gpr Z₄.cpu.gpr := by rw [hgZ₄]; exact kZ
  refine c.s_ret hKZ₄ hAZ₄ hin (lt_len (by decide)) hrZ₄ (ret_60 _)
    (by rw [hZ4sp]; exact fr hfd (fa h152 (d := 152) (by decide) (by omega) hf8) (by decide)) hin₂ h₂
    (by rw [hZ4sp]; exact c3.trans hra) ?_
  rintro Z₅ t₆ hKZ₅ hAZ₅ ⟨hrZ₅, hgZ₅⟩
  refine k rc bs Z₅ t₆ hKZ₅ hrZ₅ ?_ (by rw [hgZ₅]; exact kZ₄) ?_ ⟨_, hAZ₅, fun y h1 h2 => ?_⟩
  · rw [hgZ₅]
    show Z₄.cpu.gpr.rsp + 8 = _
    rw [hZ4sp]
  · have ha : Z₅.cpu.gpr.rax = a := by
      rw [hgZ₅, hgZ₄]
      try rfl
    rw [ha]
    exact hres
  · rw [hWo y (by omega) (by omega) h2]
    exact v2_out h152 hf8 (by omega) (by omega) _

end FV7z.Ity
