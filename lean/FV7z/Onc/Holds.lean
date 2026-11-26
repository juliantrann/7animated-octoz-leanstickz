import FV7z.Onc.Cuts
import FV7z.Lemmas.SysOpen
import FV7z.Write.Holds
/-!
# `__open64_nocancel` opens a file (PLAN.md §M, M1)

glibc 2.31's `__open64_nocancel (path, flags, …)` at `0x666090` in `7zzs`: `openat (AT_FDCWD, path, flags, mode)`
in a frame of 88 bytes with the stack guard (`fs:0x28`) at `rsp - 64`; the third argument (`rdx`) is stored at
`rsp - 40` (the `va_list`'s register save area). The flags are restricted to ones without `O_CREAT`, `O_TRUNC` and
`O_TMPFILE` (`0x400240`): then no mode is taken from the `va_list` (the way at 112 is not one of these runs), and
the model does not stop at a call that may create or truncate a file (`Lemmas/SysOpen.lean`). 7-Zip's reads open
their files so. The kernel's answer `r` is left open: not an error (`Write.WrErr`), it is returned; an error,
`errno` (`fs:-0x48`) is set to `-r` and `eax` to -1. Three pieces of the code (`Onc/Cuts.lean`): from the entry (0)
to the `syscall` (74), from after it (76) to where the two ways meet (84), from there to the `ret` (104).

- `g1`, `oV`: the registers and the bytes at the `syscall`; `oErr`: the registers after the error path.
- `vc_0`, `vc_76_ok`, `vc_76_err`, `vc_84`: the verification conditions of the pieces.
- `can_ok`, `can_err`: the stack guard at `rsp - 64` is the one at `fs:0x28` at the check.
- `onc_ok`: from the entry to the return address, the run going on from the state after the `syscall`, its own start
  (`Seg.s_openat_re`); the registers a call keeps as at the entry (as `Osv.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Onc

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_74 : psys <+: onc.drop 74 := by decide +kernel
theorem sys_74 (feat : Features) : Dec feat onc 74 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 74) (k := 0) (psys_0 feat) w_74 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_104 : pret <+: onc.drop 104 := by decide +kernel
theorem ret_104 (feat : Features) : Dec feat onc 104 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 104) (k := 0) (pret_0 feat) w_104 (Nat.zero_le _)

/-! ## The flags -/

/-- No `O_CREAT`: `test $0x40` finds nothing. -/
theorem nc40 {v : BitVec 64} (hx : arg32 v &&& 0x400240 = 0) : BitVec.setWidth 32 v &&& 64#32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth]
  exact land_sub_zero hx (by decide)

/-- No `O_TMPFILE`: the flags' bits `0x410000` are not all set. -/
theorem nc41 {v : BitVec 64} (hx : arg32 v &&& 0x400240 = 0) :
    ¬ (BitVec.setWidth 32 v &&& 4259840#32 = 4259840#32) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_setWidth] at h2
  have h3 : v.toNat % 2 ^ 32 &&& 0x400000 = 0 := land_sub_zero hx (by decide)
  have h5 := congrArg (· &&& 0x400000) h2
  rw [Nat.and_assoc, show ((4259840#32).toNat &&& 0x400000 : Nat) = 0x400000 by decide, h3] at h5
  exact absurd h5 (by decide)

/-- The flags passed on: `edx` is `esi`. -/
theorem arg32_sw (v : BitVec 64) : arg32 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = arg32 v := by
  unfold arg32
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (a := v.toNat % 2 ^ 32) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
    Nat.mod_mod]

/-! ## The frame -/

theorem fr_toNat {sp : Addr} (h : 88 ≤ sp.toNat) (d : Nat) (hd : d ≤ 88) :
    (sp - 88#64 + BitVec.ofNat 64 d).toNat = sp.toNat - 88 + d := by
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem fr24 {sp : Addr} (h : 88 ≤ sp.toNat) : (sp - 88#64 + 24#64).toNat = sp.toNat - 64 := by
  rw [fr_toNat h 24 (by decide)]
  omega

theorem fr48 {sp : Addr} (h : 88 ≤ sp.toNat) : (sp - 88#64 + 48#64).toNat = sp.toNat - 40 := by
  rw [fr_toNat h 48 (by decide)]
  omega

/-- Bytes of the frame, from the frame's 88 bytes. -/
theorem fr_ft {P : Addr → Prop} {a : Addr} (h : ∀ i < 88, P (Addr.add a i)) {d n : Nat} (hd : d + n ≤ 88) :
    ∀ i < n, P ((a + BitVec.ofNat 64 d).add i) := fun i hi => by
  have e : (a + BitVec.ofNat 64 d).add i = Addr.add a (d + i) := addr_add_add' a d i
  rw [e]
  exact h (d + i) (by omega)

/-- The registers at the `syscall`, the function called with registers `g`. -/
def g1 (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 257#32
    rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)
    rsp := g.rsp - 88#64
    rsi := g.rdi
    rdi := BitVec.setWidth 64 4294967196#32
    r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)
    r9 := g.rdi
    r10 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi &&& 64#32) }

/-- The bytes at the `syscall`: `rdx` at `rsp - 40`, the stack guard at `rsp - 64`. -/
def oV (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst (Vst V (g.rsp - 88#64 + 48#64) (toBytesLE g.rdx 8)) (g.rsp - 88#64 + 24#64)
    (toBytesLE rdq(Vst V (g.rsp - 88#64 + 48#64) (toBytesLE g.rdx 8), fb + 40#64) 8)

/-- The registers after the error path: `rdx` is `-0x48`, `eax` is -1. -/
def oErr (g : Gprs) : Gprs := { g with rax := BitVec.setWidth 64 4294967295#32, rdx := 18446744073709551544#64 }

/-- The event of `openat` from `__open64_nocancel` called with registers `g`, the kernel's answer `r`, the bytes
`bs` from the process. -/
abbrev oncEv (g : Gprs) (r : BitVec 64) (bs : List Byte) : Event :=
  ⟨(g1 g).rax, [(g1 g).rdi, (g1 g).rsi, (g1 g).rdx, (g1 g).r10, (g1 g).r8, (g1 g).r9], r, bs, []⟩

theorem oV_out {V : Addr → Byte} {g : Gprs} {fb x : Addr} (h88 : 88 ≤ g.rsp.toNat)
    (hx : x.toNat < g.rsp.toNat - 88 ∨ g.rsp.toNat ≤ x.toNat) : oV V g fb x = V x := by
  have := g.rsp.isLt
  unfold oV
  rw [Tun.Vst_out _ _ _ x ?a1 ?a2, Tun.Vst_out _ _ _ x ?b1 ?b2]
  all_goals first
    | (rw [toBytesLE_length, fr24 h88]; omega)
    | (rw [toBytesLE_length, fr48 h88]; omega)

theorem oV_rd {V : Addr → Byte} {g : Gprs} {fb x : Addr} {n : Nat} (h88 : 88 ≤ g.rsp.toNat)
    (hx : x.toNat + n ≤ 2 ^ 64) (h : x.toNat + n ≤ g.rsp.toNat - 88 ∨ g.rsp.toNat ≤ x.toNat) :
    List.map (oV V g fb) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have := g.rsp.isLt
  unfold oV
  rw [Tun.rd_Vst _ _ _ x n ?a1 hx ?a2, Tun.rd_Vst _ _ _ x n ?b1 hx ?b2]
  all_goals first
    | (rw [toBytesLE_length, fr24 h88]; omega)
    | (rw [toBytesLE_length, fr48 h88]; omega)

/-- The stack guard at the check, the way without an error. -/
theorem can_ok {V : Addr → Byte} {g : Gprs} {fb : Addr} (h88 : 88 ≤ g.rsp.toNat)
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 88 ∨ g.rsp.toNat ≤ (fb + 40#64).toNat) :
    rdq(oV V g fb, g.rsp - 88#64 + 24#64) = rdq(oV V g fb, fb + 40#64) := by
  have := g.rsp.isLt
  unfold oV
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) ?c1, ofBytesLE_toBytesLE (n := 8) rfl,
    Tun.rd_Vst _ (g.rsp - 88#64 + 24#64) _ (fb + 40#64) 8 ?c2 hcb ?c3]
  all_goals first
    | (rw [toBytesLE_length, fr24 h88]; omega)
    | (rw [fr24 h88]; omega)

/-- The stack guard at the check, the way with an error: `errno` is apart from both places. -/
theorem can_err {V : Addr → Byte} {g : Gprs} {fb : Addr} {eb : List Byte} (heb : eb.length = 4)
    (h88 : 88 ≤ g.rsp.toNat) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 88 ∨ g.rsp.toNat ≤ (fb + 40#64).toNat)
    (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ g.rsp.toNat - 88 ∨ g.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (hec : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat) :
    rdq(Vst (oV V g fb) (errnoAt fb) eb, g.rsp - 88#64 + 24#64) =
      rdq(Vst (oV V g fb) (errnoAt fb) eb, fb + 40#64) := by
  have := g.rsp.isLt
  have h1 : (errnoAt fb).toNat + eb.length ≤ 2 ^ 64 := by rw [heb]; exact hfe
  rw [Tun.rd_Vst _ (errnoAt fb) eb (g.rsp - 88#64 + 24#64) 8 h1 ?d1 ?d2,
    Tun.rd_Vst _ (errnoAt fb) eb (fb + 40#64) 8 h1 hcb ?d3]
  · exact can_ok h88 hcb hcd
  all_goals first
    | (rw [fr24 h88]; omega)
    | (rw [heb, fr24 h88]; omega)
    | (rw [heb]; omega)

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-! ## The pieces -/

/-- From the entry to the `syscall`, flags without `O_CREAT`, `O_TRUNC`, `O_TMPFILE`: `rdx` and the stack guard
stored in the frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hx : arg32 g.rsi &&& 0x400240 = 0)
    (hfw : ∀ i < 88, Foot Wl (Addr.add (g.rsp - 88#64) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 74 ∧ g' = g1 g ∧ V' = oV V g fb) g f V := by
  have h40 := nc40 hx
  have h41 := nc41 hx
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw h40 h41
  wpx [W_0, W_44, W_58, o0, o1, o2, Op.ldf]
  all_goals first
  | exact ⟨fr_ft hfw (d := 48) (by decide), hcl, fr_ft hfw (d := 24) (by decide),
      fun h => absurd h (by rw [h40]; decide), fun _ => ⟨fun h => absurd (of_decide_eq_true h) h41,
      fun _ => ⟨rfl, rfl⟩⟩⟩
  | exact ⟨fr_ft hfw (d := 48) (by decide), hcl, fr_ft hfw (d := 24) (by decide),
      fun h => absurd h (by rw [h40]; decide), fun _ => ⟨fun h => absurd (of_decide_eq_true h) h41, fun _ => rfl⟩⟩
  | exact ⟨fr_ft hfw (d := 48) (by decide), hcl, fr_ft hfw (d := 24) (by decide),
      fun h => absurd h (by rw [h40]; decide), fun _ => ⟨fun h => absurd (of_decide_eq_true h) h41,
      fun _ => ⟨rfl, rfl, rfl⟩⟩⟩

/-- From the `syscall` to where the ways meet, the kernel's answer `rax` not an error. -/
theorem vc_76_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ WrErr g.rax) :
    W_76 fb F Wl (fun j' g' _ V' => j' = 84 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = false := decide_eq_false he
  wpx [W_76, W_152, o3, o6, Op.stf, ja_cmp, he']
  all_goals first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩
  | vc_fin

/-- From the `syscall` to where the ways meet, the kernel's answer `rax` an error: `errno` set, `eax` -1. -/
theorem vc_76_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : WrErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_76 fb F Wl (fun j' g' _ V' => j' = 84 ∧ g' = oErr g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = true := decide_eq_true he
  wpx [W_76, W_152, o3, o6, Op.stf, ja_cmp, he']
  all_goals first
  | exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩
  | exact ⟨fe, rfl⟩
  | exact ⟨⟨fe, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  | exact ⟨fe, rfl, rfl⟩
  | vc_fin

/-- The check of the stack guard, to the `ret`. -/
theorem vc_84 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i)) (hfl : ∀ i < 8, Foot F.data ((fb + 40#64).add i))
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) :
    W_84 fb F Wl (fun j' g' _ V' => j' = 104 ∧ g' = { g with rcx := 0#64, rsp := g.rsp + 88#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc
  wpx [W_84, W_100, o4, o5, Op.xormf, hc, BitVec.xor_self]
  all_goals first
  | exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => rfl⟩
  | exact ⟨hl, hfl, fun _ => rfl⟩
  | exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩
  | exact ⟨hl, hfl⟩
  | vc_fin

/-- The registers a call keeps, after the `ret` (as `Osv.Back`), from the registers at the `syscall`. -/
theorem oBack {gX gY G : Gprs} (hY : gY = g1 gX)
    (hb : G.rbx = gY.rbx ∧ G.rbp = gY.rbp ∧ G.r12 = gY.r12 ∧ G.r13 = gY.r13 ∧ G.r14 = gY.r14 ∧ G.r15 = gY.r15)
    (hs : G.rsp = gX.rsp + 8#64) :
    G.rsp = gX.rsp + 8#64 ∧ G.rbx = gX.rbx ∧ G.rbp = gX.rbp ∧ G.r12 = gX.r12 ∧ G.r13 = gX.r13 ∧ G.r14 = gX.r14 ∧
      G.r15 = gX.r15 := by
  rw [hY] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
  exact ⟨hs, h1, h2, h3, h4, h5, h6⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__open64_nocancel (path, flags, …)` from its entry to the return address, with flags without `O_CREAT`,
`O_TRUNC` and `O_TMPFILE`, a path name of `m` nonzero bytes then a NUL apart from the frame (the word it ends in the
footprint's data), the frame's 88 bytes below the stack pointer in what the run may store into, the stack guard and
`errno` apart from the frame and from each other: the `syscall` `openat (AT_FDCWD, path, flags)` from `Y` (registers
`g1`, bytes `oV`) answers some `r`; the run goes on from the state after it, `S`, its own start, to the return
address with the return address popped, the registers a call keeps as at the entry, and, if `r` is not an error,
`rax` = `r`; if it is, `errno` = `-r` and `rax` = `0xffffffff` (`eax` -1). -/
theorem onc_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L onc_at onc) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = onc_at) (hx : arg32 X.cpu.gpr.rsi &&& 0x400240 = 0)
    (h88 : 88 ≤ X.cpu.gpr.rsp.toNat) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfw : ∀ i < 88, Foot Wl (Addr.add (X.cpu.gpr.rsp - 88#64) i))
    (hfd : ∀ i < 88, Foot F.data (Addr.add (X.cpu.gpr.rsp - 88#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 88 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 88 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (hec : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat)
    {m : Nat} (hm : m < pathMax) (htop : X.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hpl : ∀ i < 8 * (m / 8 + 1), Foot F.data (X.cpu.gpr.rdi.add i))
    (hpd : X.cpu.gpr.rdi.toNat + 8 * (m / 8 + 1) ≤ X.cpu.gpr.rsp.toNat - 88 ∨
      X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hnz : ∀ i < m, V (X.cpu.gpr.rdi.add i) ≠ 0) (hz : V (X.cpu.gpr.rdi.add m) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Y S Z : State) (r : BitVec 64) (bs : List Byte) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (oV V X.cpu.gpr fb) → Y.cpu.gpr = g1 X.cpu.gpr → Y.cpu.rip = onc_at.add 74 →
      S.cpu = (sysSt Y 2 r).cpu → S.proc.mm = Y.proc.mm → Seg prof F Wl L S o → S.thread.rseq = none →
      KeptW Wl S Z →
      Z.cpu.rip = e₂.add j₂ →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (¬ WrErr r → Agree F Z.proc.mm.mem (oV V X.cpu.gpr fb) ∧ Z.cpu.gpr.rax = r) →
      (WrErr r → Agree F Z.proc.mm.mem (Vst (oV V X.cpu.gpr fb) (errnoAt fb) (errnoB r)) ∧
        Z.cpu.gpr.rax = 4294967295#64) →
      GoG prof L o (gev ++ [oncEv X.cpu.gpr r bs]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hup : userPtrMax prof.feat ≤ 2 ^ 64 := by unfold userPtrMax; split <;> decide
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 74 ∧ g' = g1 X.cpu.gpr ∧ V' = oV V X.cpu.gpr fb)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hx hfw hcl) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hrsi : Y.cpu.gpr.rsi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  have hxY : arg32 Y.cpu.gpr.rdx &&& 0x400240 = 0 := by
    rw [hgY]
    show arg32 (BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi)) &&& _ = 0
    rw [arg32_sw]
    exact hx
  have hpv : ∀ i < 8 * (m / 8 + 1), oV V X.cpu.gpr fb (X.cpu.gpr.rdi.add i) = V (X.cpu.gpr.rdi.add i) :=
    fun i hi => oV_out h88 (by
      have e : (X.cpu.gpr.rdi.add i).toNat = X.cpu.gpr.rdi.toNat + i := toNat_add_of_fits hi (by omega)
      rw [e]
      omega)
  refine c.s_openat_re hrs hKY hAY hin (lt_len (by decide)) hrY (sys_74 _) (by rw [hgY]; rfl) hxY hm
    (by rw [hrsi]; exact htop) (by rw [hrsi]; exact hpl)
    (by rw [hrsi]; exact fun i hi => by rw [hpv i (by omega)]; exact hnz i hi)
    (by rw [hrsi, hpv m (by omega)]; exact hz) ?_
  intro M S r bs t₂ hKm hcS hmmS c₁ hrsS hAS
  have hev : (⟨Y.cpu.gpr.rax, syscallArgs Y, r, bs, []⟩ : Event) = oncEv X.cpu.gpr r bs := by
    unfold syscallArgs
    rw [hgY]
  rw [hev]
  have hfs₁ : S.cpu.seg.fsBase = fb :=
    (congrArg (·.seg.fsBase) hcS).trans (by show Y.cpu.seg.fsBase = fb; rw [hKY.seg]; exact hfs)
  have hrS : S.cpu.rip = onc_at.add 76 :=
    (congrArg (·.rip) hcS).trans (by show Y.cpu.rip.add 2 = _; rw [hrY]; exact addr_add_add _ _ _)
  have hgS : S.cpu.gpr = (sysGpr Y 2).set 0 r := (congrArg (·.gpr) hcS).trans rfl
  have hspS : ((sysGpr Y 2).set 0 r).rsp = X.cpu.gpr.rsp - 88#64 := by
    show Y.cpu.gpr.rsp = _
    rw [hgY]
    rfl
  have hY : (Y.withMem M).cpu.gpr = g1 X.cpu.gpr := hgY
  have hAm : Agree F (Y.withMem M).proc.mm.mem (oV V X.cpu.gpr fb) := by rw [← hmmS]; exact hAS
  have kk := fun Z t' => k (Y.withMem M) S Z r bs t' hKm hAm hY hrY hcS hmmS c₁ hrsS
  have hr0 : ((sysGpr Y 2).set 0 r).rax = r := rfl
  have hl24 : ∀ i < 8, Foot F.data (Addr.add (((sysGpr Y 2).set 0 r).rsp + 24#64) i) := fun i hi => by
    have h := fr_ft hfd (d := 24) (n := 8) (by decide) i hi
    rw [← hspS] at h
    exact h
  have hsp8 : ((sysGpr Y 2).set 0 r).rsp + 88#64 = X.cpu.gpr.rsp := by
    rw [hspS]
    exact BitVec.sub_add_cancel _ _
  by_cases he : WrErr r
  · have heb : (errnoB ((sysGpr Y 2).set 0 r).rax).length = 4 := toBytesLE_length _ _
    refine (c_76 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 84 ∧ g' = oErr ((sysGpr Y 2).set 0 r) ∧
        V' = Vst (oV V X.cpu.gpr fb) (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax))
      (KeptW.refl _ _) hAS hrS (by rw [hgS]; exact vc_76_err (by rw [hr0]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₄ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hc : rdq(Vst (oV V X.cpu.gpr fb) (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax),
        (oErr ((sysGpr Y 2).set 0 r)).rsp + 24#64) =
        rdq(Vst (oV V X.cpu.gpr fb) (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax), fb + 40#64) := by
      show rdq(_, ((sysGpr Y 2).set 0 r).rsp + 24#64) = _
      rw [hspS]
      exact can_err heb h88 hcb hcd hfe hed hec
    refine (c_84 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 104 ∧
        g' = { oErr ((sysGpr Y 2).set 0 r) with rcx := 0#64, rsp := (oErr ((sysGpr Y 2).set 0 r)).rsp + 88#64 } ∧
        V' = Vst (oV V X.cpu.gpr fb) (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r).rax))
      hKZ₁ hAZ₁ hrZ₁ (by rw [hgZ₁]; exact vc_84 hl24 hcl hc) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₅ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hspZ : Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ₂]; exact hsp8
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_104 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have h1 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r).rax).length ≤ 2 ^ 64 := by rw [heb]; exact hfe
      have h2 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r).rax).length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [heb]; omega
      rw [hspZ, Tun.rd_Vst (oV V X.cpu.gpr fb) (errnoAt fb) _ X.cpu.gpr.rsp 8 h1 hsp h2,
        oV_rd h88 hsp (Or.inr (Nat.le_refl _))]
      exact hra
    rintro Z₃ t₆ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    rw [hr0] at hAZ₃
    refine kk Z₃ t₆ hKZ₃ hrZ₃ ?_ (fun h => absurd he h) fun _ => ⟨hAZ₃, ?_⟩
    · rw [hgZ₃, hgZ₂]
      exact oBack (gY := Y.cpu.gpr) hgY ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (by
        show ((sysGpr Y 2).set 0 r).rsp + 88#64 + 8 = _
        rw [hsp8]
        try rfl)
    · rw [hgZ₃, hgZ₂]
      try first | rfl | decide
  · refine (c_76 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 84 ∧ g' = (sysGpr Y 2).set 0 r ∧ V' = oV V X.cpu.gpr fb)
      (KeptW.refl _ _) hAS hrS (by rw [hgS]; exact vc_76_ok (by rw [hr0]; exact he)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z₁ t₄ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    subst V₂
    have hc : rdq(oV V X.cpu.gpr fb, ((sysGpr Y 2).set 0 r).rsp + 24#64) = rdq(oV V X.cpu.gpr fb, fb + 40#64) := by
      rw [hspS]
      exact can_ok h88 hcb hcd
    refine (c_84 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 104 ∧
        g' = { (sysGpr Y 2).set 0 r with rcx := 0#64, rsp := ((sysGpr Y 2).set 0 r).rsp + 88#64 } ∧
        V' = oV V X.cpu.gpr fb)
      hKZ₁ hAZ₁ hrZ₁ (by rw [hgZ₁]; exact vc_84 hl24 hcl hc) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Z₂ t₅ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    subst V₃
    have hspZ : Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ₂]; exact hsp8
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_104 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · rw [hspZ, oV_rd h88 hsp (Or.inr (Nat.le_refl _))]
      exact hra
    rintro Z₃ t₆ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    refine kk Z₃ t₆ hKZ₃ hrZ₃ ?_ (fun _ => ⟨hAZ₃, ?_⟩) fun h => absurd h he
    · rw [hgZ₃, hgZ₂]
      exact oBack (gY := Y.cpu.gpr) hgY ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (by
        show ((sysGpr Y 2).set 0 r).rsp + 88#64 + 8 = _
        rw [hsp8]
        try rfl)
    · rw [hgZ₃, hgZ₂]
      try rfl

end FV7z.Onc
