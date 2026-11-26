import FV7z.Gdt.Cuts
import FV7z.Grl.Holds
import FV7z.Cxa.Holds
import FV7z.Write.Holds
/-!
# `__getdtablesize` returns `RLIMIT_NOFILE`'s soft limit (PLAN.md §M, M1)

glibc 2.31's `__getdtablesize ()` at `0x6664a0` in `7zzs` (`getdtsz.c`): `__getrlimit (RLIMIT_NOFILE, &r)` into a
frame of 40 bytes with the stack guard (`fs:0x28`) at `rsp - 16`, then `r.rlim_cur` (its low 32 bits, `cmovns eax,
[rsp]`) or 256 if the call failed. `__getrlimit` (`Grl.grl_ok`, `prlimit64 (0, 7, 0, &r)`) does not fail: the limit
is the start's (`s₀.proc.signal.rlimits`). Two pieces of the code (`Gdt/Cuts.lean`) around the call: from the entry
(0) to the `call` (32), from after it (37) to the `ret` (68).

- `dg1`, `dV1`: the registers and the bytes at the `call`; `dVf`: the bytes at the `ret`.
- `rd4_rl`: the first 4 bytes of a limit stored (`Rlimit.bytes`) are its soft limit's low half.
- `vc_0`, `vc_37`: the verification conditions of the pieces.
- `gdt_ok`: from the entry to the return address: `rax` = `RLIMIT_NOFILE`'s soft limit's low 32 bits, zero-extended.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Gdt

/-- The `call __getrlimit`. -/
def pcall : List Byte := [0xe8, 0x4b, 0xfe, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709551179] 5) := by dec_rfl
theorem w_32 : pcall <+: gdt.drop 32 := by decide +kernel
theorem call_32 (feat : Features) : Dec feat gdt 32 (FV7z.mk .call 64 [.rel 18446744073709551179] 5) :=
  Dec.shift (j := 32) (k := 0) (pcall_0 feat) w_32 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_68 : pret <+: gdt.drop 68 := by decide +kernel
theorem ret_68 (feat : Features) : Dec feat gdt 68 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 68) (k := 0) (pret_0 feat) w_68 (Nat.zero_le _)

/-! ## The limit's first 4 bytes -/

theorem tb_take4 (x : BitVec 64) : (toBytesLE x 8).take 4 = toBytesLE (x.setWidth 32) 4 := by
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_take, toBytesLE_length] at h₁
  simp only [toBytesLE, List.getElem_take, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp [show 8 * j + i < 32 from by omega]

/-- The first 4 bytes of a limit stored at `a` (`Rlimit.bytes`): its soft limit's low half. -/
theorem rd4_rl (W : Addr → Byte) (a : Addr) (r : Rlimit) (ha : a.toNat + 16 ≤ 2 ^ 64) :
    ofBytesLE 32 ((byteAddrs a 4).map (Vst W a r.bytes)) = r.cur.setWidth 32 := by
  have hs : r.bytes = toBytesLE (r.cur.setWidth 32) 4 ++ ((toBytesLE r.cur 8).drop 4 ++ toBytesLE r.max 8) := by
    unfold Rlimit.bytes
    rw [← tb_take4, ← List.append_assoc, List.take_append_drop]
  have h4 : (Addr.add a 4).toNat = a.toNat + 4 := toNat_add_of_fits (i := 4) (n := 16) (by decide) ha
  have hl : ((toBytesLE r.cur 8).drop 4 ++ toBytesLE r.max 8).length = 12 := by
    simp only [List.length_append, List.length_drop, toBytesLE_length]
  rw [hs, Cxa.Vst_append, toBytesLE_length,
    Tun.rd_Vst _ (Addr.add a 4) _ a 4 (by rw [h4, hl]; omega) (by omega) (Or.inr (by omega)),
    Tun.rd_Vst_self _ a _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (w := 32) (n := 4) rfl]

/-! ## The frame -/

theorem t40 {rs : Addr} (h : 48 ≤ rs.toNat) : (rs - 40#64).toNat = rs.toNat - 40 := by
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t48 {rs : Addr} (h : 48 ≤ rs.toNat) : (rs - 48#64).toNat = rs.toNat - 48 := by
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t16 {rs : Addr} (h : 48 ≤ rs.toNat) : (rs - 40#64 + 24#64).toNat = rs.toNat - 16 := by
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The return address's slot of the call. -/
theorem e48 {rs : Addr} (h : 48 ≤ rs.toNat) : rs - 40#64 - 8 = rs - 48#64 := by
  apply BitVec.eq_of_toNat_eq
  have := rs.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem e40 {rs : Addr} (h : 48 ≤ rs.toNat) : rs - 48#64 + 8 = rs - 40#64 := by
  apply BitVec.eq_of_toNat_eq
  have := rs.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

/-- An address of the frame's 48 bytes. -/
theorem fa {rs x : Addr} (h : 48 ≤ rs.toNat) {d : Nat} (hd : d ≤ 48) (hx : x.toNat = rs.toNat - 48 + d) :
    x = Addr.add (rs - 48#64) d := by
  have := rs.isLt
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_add_of_fits (i := d) (n := d + 1) (by omega) (by rw [t48 h]; omega), t48 h]

theorem fr {P : Addr → Prop} {rs x : Addr} (h : ∀ i < 48, P (Addr.add (rs - 48#64) i)) {d n : Nat}
    (hx : x = Addr.add (rs - 48#64) d) (hdn : d + n ≤ 48) : ∀ i < n, P (Addr.add x i) := fun i hi => by
  rw [hx, addr_add_add']
  exact h (d + i) (by omega)

/-- The registers at the `call`, the function called with registers `g` and the stack guard `c`. -/
def dg1 (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 c ^^^ BitVec.setWidth 32 c)
    rsp := g.rsp - 40#64
    rsi := g.rsp - 40#64
    rdi := BitVec.setWidth 64 7#32 }

/-- The bytes at the `call`: the stack guard at `rsp - 16`. -/
def dV1 (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst V (g.rsp - 40#64 + 24#64) (toBytesLE rdq(V, fb + 40#64) 8)

/-- The bytes at the `ret`: the return address of the call at `rsp - 48`, the limit's 16 bytes `bs` at `rsp - 40`. -/
def dVf (V : Addr → Byte) (g : Gprs) (fb : Addr) (bs : List Byte) : Addr → Byte :=
  Vst (Vst (dV1 V g fb) (g.rsp - 48#64) (toBytesLE (gdt_at.add 37) 8)) (g.rsp - 40#64) bs

/-- The stack guard at the check. -/
theorem can_ok {V : Addr → Byte} {g : Gprs} {fb : Addr} {bs : List Byte} (hb : bs.length = 16)
    (h48 : 48 ≤ g.rsp.toNat) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ (fb + 40#64).toNat) :
    rdq(dVf V g fb bs, g.rsp - 40#64 + 24#64) = rdq(dVf V g fb bs, fb + 40#64) := by
  have := g.rsp.isLt
  have a40 := t40 h48
  have a48 := t48 h48
  have a16 := t16 h48
  unfold dVf dV1
  rw [Tun.rd_Vst _ (g.rsp - 40#64) bs (g.rsp - 40#64 + 24#64) 8 ?a1 ?a2 ?a3,
    Tun.rd_Vst _ (g.rsp - 48#64) _ (g.rsp - 40#64 + 24#64) 8 ?b1 ?b2 ?b3,
    Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) ?c1, ofBytesLE_toBytesLE (n := 8) rfl,
    Tun.rd_Vst _ (g.rsp - 40#64) bs (fb + 40#64) 8 ?d1 hcb ?d3,
    Tun.rd_Vst _ (g.rsp - 48#64) _ (fb + 40#64) 8 ?e1 hcb ?e3,
    Tun.rd_Vst _ (g.rsp - 40#64 + 24#64) _ (fb + 40#64) 8 ?f1 hcb ?f3]
  all_goals (try simp only [hb, toBytesLE_length, a40, a48, a16])
  all_goals omega

/-- The return address, apart from the frame. -/
theorem ra_ok {V : Addr → Byte} {g : Gprs} {fb : Addr} {bs : List Byte} (hb : bs.length = 16)
    (h48 : 48 ≤ g.rsp.toNat) (hsp : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(dVf V g fb bs, g.rsp) = rdq(V, g.rsp) := by
  have := g.rsp.isLt
  have a40 := t40 h48
  have a48 := t48 h48
  have a16 := t16 h48
  unfold dVf dV1
  rw [Tun.rd_Vst _ (g.rsp - 40#64) bs g.rsp 8 ?a1 hsp ?a3, Tun.rd_Vst _ (g.rsp - 48#64) _ g.rsp 8 ?b1 hsp ?b3,
    Tun.rd_Vst _ (g.rsp - 40#64 + 24#64) _ g.rsp 8 ?c1 hsp ?c3]
  all_goals (try simp only [hb, toBytesLE_length, a40, a48, a16])
  all_goals omega

/-- The return address of the call, apart from the limit. -/
theorem rag_ok {V : Addr → Byte} {g : Gprs} {fb : Addr} {bs : List Byte} (hb : bs.length = 16)
    (h48 : 48 ≤ g.rsp.toNat) :
    rdq(dVf V g fb bs, g.rsp - 48#64) = gdt_at.add 37 := by
  have := g.rsp.isLt
  have a40 := t40 h48
  have a48 := t48 h48
  unfold dVf
  rw [Tun.rd_Vst _ (g.rsp - 40#64) bs (g.rsp - 48#64) 8 ?a1 ?a2 ?a3,
    Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) ?c1, ofBytesLE_toBytesLE (n := 8) rfl]
  all_goals (try simp only [hb, toBytesLE_length, a40, a48])
  all_goals omega

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to the `call`: the stack guard stored in the frame, `edi` 7 (`RLIMIT_NOFILE`), `rsi` the
frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 32 ∧ g' = dg1 g rdq(V, fb + 40#64) ∧ V' = dV1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw
  wpx [W_0, o0, Op.ldf]
  all_goals vc_fin

/-- `test eax, eax` after the call that answered 0. -/
theorem msb0 : (!(BitVec.setWidth 32 (0 : BitVec 64) &&& BitVec.setWidth 32 (0 : BitVec 64)).msb) = true := by
  decide

/-- From after the `call` (`eax` 0) to the `ret`: `eax` the 4 bytes at `rsp`, the stack guard checked, the frame
dropped. -/
theorem vc_37 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add g.rsp i)) (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) :
    W_37 fb F Wl (fun j' g' _ V' => j' = 68 ∧
      g' = { g with
        rax := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs g.rsp 4)))
        rdx := 0#64
        rsp := g.rsp + 40#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0 hl4 hl24 hc
  subst h0
  wpx [W_37, W_64, o1, o2, Op.xormf, Op.cmovld32, hc, BitVec.xor_self, msb0, ↓reduceIte]
  all_goals vc_fin

/-- The registers a call keeps. -/
abbrev Kp (g h : Gprs) : Prop :=
  g.rbx = h.rbx ∧ g.rbp = h.rbp ∧ g.r12 = h.r12 ∧ g.r13 = h.r13 ∧ g.r14 = h.r14 ∧ g.r15 = h.r15

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__getdtablesize ()` from its entry to the return address, the frame's 48 bytes (40 and the call's return
address) below the stack pointer in what the run may store into, below the end of the user address space, the stack
guard apart from the frame: the run goes on with the return address popped, the registers a call keeps as at the
entry, `rax` = the start's `RLIMIT_NOFILE` soft limit's low 32 bits, the bytes `dVf` (the frame), after
`prlimit64 (0, RLIMIT_NOFILE, 0, rsp - 40)`. -/
theorem gdt_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L gdt_at gdt)
    (hing : CodeIn L Grl.grl_at Grl.grl) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gdt_at)
    (h48 : 48 ≤ X.cpu.gpr.rsp.toNat) (hup : X.cpu.gpr.rsp.toNat + 8 ≤ userPtrMax prof.feat)
    (hfw : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hfd : ∀ i < 48, Foot F.data (Addr.add (X.cpu.gpr.rsp - 48#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (dVf V X.cpu.gpr fb (s₀.proc.signal.rlimits ⟨7, by decide⟩).bytes) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Kp Z.cpu.gpr X.cpu.gpr →
      Z.cpu.gpr.rax = BitVec.setWidth 64 ((s₀.proc.signal.rlimits ⟨7, by decide⟩).cur.setWidth 32) →
      GoG prof L o (gev ++ [Grl.grlEv (dg1 X.cpu.gpr rdq(V, fb + 40#64)) (s₀.proc.signal.rlimits ⟨7, by decide⟩).bytes])
        gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hpm : userPtrMax prof.feat ≤ 2 ^ 64 := by unfold userPtrMax; split <;> decide
  have a40 := t40 h48
  have a48 := t48 h48
  have a16 := t16 h48
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 32 ∧ g' = dg1 X.cpu.gpr rdq(V, fb + 40#64) ∧ V' = dV1 V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcl (fr hfw (fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hgY]; try rfl
  have hcs : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 48#64 := by rw [hYsp]; exact e48 h48
  have kY : Kp Y.cpu.gpr X.cpu.gpr := by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_32 _) hing (Grl.lt_len (by decide)) (by decide)
    (by rw [hcs]; exact fun i hi => hfw i (by omega)) ?_
  rintro Y₂ t₂ hKY₂ hAY₂ ⟨hrY₂, hgY₂⟩
  rw [hcs] at hAY₂
  have hY2sp : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 48#64 := by rw [hgY₂]; exact hcs
  have hY2si : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsp - 40#64 := by rw [hgY₂, hgY]; try rfl
  have kY₂ : Kp Y₂.cpu.gpr X.cpu.gpr := by rw [hgY₂]; exact kY
  have hev : Grl.grlEv Y₂.cpu.gpr (s₀.proc.signal.rlimits ⟨7, by decide⟩).bytes =
      Grl.grlEv (dg1 X.cpu.gpr rdq(V, fb + 40#64)) (s₀.proc.signal.rlimits ⟨7, by decide⟩).bytes := by
    rw [hgY₂, hgY]
    try rfl
  have hb := Rlimit.bytes_length (s₀.proc.signal.rlimits ⟨7, by decide⟩)
  refine Grl.grl_ok c hing hKY₂ hAY₂ hrY₂ (r := 7) (by decide) (by rw [hgY₂, hgY]; first | rfl | decide)
    (by
      rw [hY2si]
      intro h
      have h1 := congrArg BitVec.toNat h
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [a40] at h1
      omega)
    (by rw [hY2si, a40]; omega)
    (by rw [hY2si]; exact fr hfw (fa h48 (d := 8) (by decide) (by rw [a40]; omega)) (by decide)) ?_
  intro rc r11 Zg t₃ hKZg hAZg hrZg hgZg
  rw [hev]
  rw [hY2si] at hAZg
  have hZgsp : Zg.cpu.gpr.rsp = X.cpu.gpr.rsp - 48#64 := by rw [hgZg]; exact hY2sp
  have kZg : Kp Zg.cpu.gpr X.cpu.gpr := by rw [hgZg]; exact kY₂
  refine c.s_ret hKZg hAZg hing (Grl.lt_len (by decide)) hrZg (Grl.ret_28 _)
    (by rw [hZgsp]; exact fun i hi => hfd i (by omega)) hin (j₂ := 37) (lt_len (by decide))
    (by rw [hZgsp]; exact rag_ok (g := X.cpu.gpr) hb h48) ?_
  rintro Z₃ t₄ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
  have hZ3sp : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by
    rw [hgZ₃]
    show Zg.cpu.gpr.rsp + 8 = _
    rw [hZgsp]
    exact e40 h48
  have kZ₃ : Kp Z₃.cpu.gpr X.cpu.gpr := by rw [hgZ₃]; exact kZg
  have h0 : Z₃.cpu.gpr.rax = 0 := by rw [hgZ₃, hgZg]; try rfl
  refine (c_37 prof fb).run c hfs hin _ hKZ₃ hAZ₃ hrZ₃
    (vc_37 (g := Z₃.cpu.gpr) h0
      (by rw [hZ3sp]; exact fr hfd (fa h48 (d := 8) (by decide) (by rw [a40]; omega)) (by decide))
      (by rw [hZ3sp]; exact fr hfd (fa h48 (d := 32) (by decide) (by rw [a16]; omega)) (by decide)) hcl
      (by rw [hZ3sp]; exact can_ok (g := X.cpu.gpr) hb h48 hcb hcd)) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Z₄ t₅ hKZ₄ hAZ₄ hrZ₄ hgZ₄ -
  have hZ4sp : Z₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hgZ₄]
    show Z₃.cpu.gpr.rsp + 40#64 = _
    rw [hZ3sp]
    exact BitVec.sub_add_cancel _ _
  have kZ₄ : Kp Z₄.cpu.gpr X.cpu.gpr := by rw [hgZ₄]; exact kZ₃
  have hr4 : ofBytesLE 32 (List.map (dVf V X.cpu.gpr fb (s₀.proc.signal.rlimits ⟨7, by decide⟩).bytes)
      (byteAddrs Z₃.cpu.gpr.rsp 4)) = (s₀.proc.signal.rlimits ⟨7, by decide⟩).cur.setWidth 32 := by
    rw [hZ3sp]
    exact rd4_rl _ _ _ (by rw [a40]; omega)
  refine c.s_ret hKZ₄ hAZ₄ hin (lt_len (by decide)) hrZ₄ (ret_68 _) (by rw [hZ4sp]; exact hl) hin₂ h₂
    (by rw [hZ4sp]; exact (ra_ok (g := X.cpu.gpr) hb h48 (by omega)).trans hra) ?_
  rintro Z₅ t₆ hKZ₅ hAZ₅ ⟨hrZ₅, hgZ₅⟩
  refine k Z₅ t₆ hKZ₅ hAZ₅ hrZ₅ ?_ (by rw [hgZ₅]; exact kZ₄) ?_
  · rw [hgZ₅]
    show Z₄.cpu.gpr.rsp + 8 = _
    rw [hZ4sp]
  · rw [hgZ₅, hgZ₄]
    exact congrArg (BitVec.setWidth 64) hr4

end FV7z.Gdt
