import FV7z.Sga.Cuts
import FV7z.Start.TaskSeg
import FV7z.Osv.Holds
/-!
# `__libc_sigaction` sets a signal's action (PLAN.md G3, startup)

glibc 2.31's `__libc_sigaction (sig, act, oact)` at `0x600ff0` in `7zzs`, called with an action and no place for the
old one (`oact` 0), as `__pthread_initialize_minimal_internal` calls it for its two signals. The function copies the
action to the kernel's layout in its frame of 328 bytes (the handler, the flags with `SA_RESTORER`, the restorer
`0x600fe0`, the mask; the mask's 128 bytes go through `xmm` registers, their values not followed), asks
`rt_sigaction (sig, frame, 0, 8)`, checks the stack guard and returns the kernel's answer.

- `vc_0`, `vc_185`, `vc_198`, `vc_383`: the verification conditions of the four pieces (`Sga/Cuts.lean`); `Fr`: what
  the bytes at the `syscall` have, the stores' bytes that came through `xmm` registers any.
- `ign_false`: an action with a handler does not ignore a signal.
- `sga_ok`: called from a start with `Base`, with the frame's 328 bytes in what the run may store into, the action's
  140 bytes apart from them with a handler other than `SIG_DFL` and `SIG_IGN`, a signal from 1 to 64 other than
  `SIGKILL` and `SIGSTOP`, the stack guard at `fs:0x28` apart from the frame, and a return address in the code, the
  run reaches the return address with `rax` 0, the registers a call keeps as at the entry (`Osv.Back`), the bytes
  outside the frame as they were. The run goes on from the state after the `syscall`, its own start
  (`Seg.b_sigaction`).

The ways with no action, with a place for the old one, and with an error from the kernel are not ones of these runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Sga

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_196 : psys <+: sga.drop 196 := by decide +kernel
theorem sys_196 (feat : Features) : Dec feat sga 196 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 196) (k := 0) (psys_0 feat) w_196 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_412 : pret <+: sga.drop 412 := by decide +kernel
theorem ret_412 (feat : Features) : Dec feat sga 412 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 412) (k := 0) (pret_0 feat) w_412 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-! ## Reads and stores from the stack pointer -/

theorem sk0' (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 0 v =
      Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl

/-- A byte outside a store of `n` bytes. -/
theorem vo {V : Addr → Byte} {a x : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) (h : x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat) : Vst V a bs x = V x :=
  Vst_out V a bs x (hn ▸ ha) (hn ▸ h)

/-- Bytes apart from a store of `n` bytes. -/
theorem vr {V : Addr → Byte} {a x : Addr} {bs : List Byte} {m n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) (hx : x.toNat + m ≤ 2 ^ 64) (h : a.toNat + n ≤ x.toNat ∨ x.toNat + m ≤ a.toNat) :
    List.map (Vst V a bs) (byteAddrs x m) = List.map V (byteAddrs x m) :=
  rd_Vst V a bs x m (hn ▸ ha) hx (hn ▸ h)

/-- The bytes a store stored. -/
theorem vs {V : Addr → Byte} {a : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n) (ha : a.toNat + n ≤ 2 ^ 64) :
    List.map (Vst V a bs) (byteAddrs a n) = bs := rd_Vst_self V a bs hn ha

/-- The length of stored bytes. -/
macro "ln" : tactic => `(tactic| first | exact toBytesLE_length _ _ | assumption)

/-- A byte, or bytes, through a store apart from them. -/
macro "pv" : tactic =>
  `(tactic| first
    | (rw [vo (hn := ?pv1) (ha := ?pv2) (h := ?pv3)]; (case pv1 => ln); (case pv2 => bv_omega); (case pv3 => bv_omega))
    | (rw [vr (hn := ?pv1) (ha := ?pv2) (hx := ?pv3) (h := ?pv4)]; (case pv1 => ln); (case pv2 => bv_omega);
       (case pv3 => bv_omega); (case pv4 => bv_omega)))

/-- Bytes apart from where `V'` is not `V`. -/
theorem rd_out {V V' : Addr → Byte} {lo hi : Nat} (h : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ lo ∨ hi ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_
  rw [toNat_add_of_fits hj hx]
  omega

theorem act_ft {a : Addr} (hal : ∀ i < 140, Foot F.data (Addr.add a i)) {d n : Nat} (h : d + n ≤ 140) :
    ∀ i < n, Foot F.data ((a + BitVec.ofNat 64 d).add i) := fun i hi => by
  have := hal (d + i) (by omega)
  rwa [show Addr.add a (d + i) = (a + BitVec.ofNat 64 d).add i from by simp only [Addr.add]; bv_omega] at this

theorem frm_ft {sp : Addr} (hst : ∀ i < 328, Foot Wl (Addr.add (sp - 328#64) i)) {d n : Nat} (h : d + n ≤ 328) :
    ∀ i < n, Foot Wl ((sp - 328#64 + BitVec.ofNat 64 d).add i) := fun i hi => by
  have := hst (d + i) (by omega)
  rwa [show Addr.add (sp - 328#64) (d + i) = (sp - 328#64 + BitVec.ofNat 64 d).add i from by
    simp only [Addr.add]; bv_omega] at this

/-! ## The pieces -/

/-- The registers at the `syscall`'s stretch, the function called with registers `g`, no old action asked for. -/
abbrev g1 (g : Gprs) : Gprs := { g with rax := 0, rdx := 0, rsp := g.rsp - 328#64, rsi := g.rsp - 328#64, r8 := 0 }

/-- What the bytes `V'` at the `syscall` have of the bytes `V` at the entry, the stack pointer `sp` there, the `fs`
base `fb`: all outside the frame, in the frame the action's handler `h` and the stack guard. -/
structure Fr (V V' : Addr → Byte) (sp fb : Addr) (h : BitVec 64) : Prop where
  out : ∀ a : Addr, ¬ (sp.toNat - 328 ≤ a.toNat ∧ a.toNat < sp.toNat) → V' a = V a
  hnd : rdq(V', sp - 328#64) = h
  can : rdq(V', sp - 16#64) = rdq(V, fb + 40#64)

/-- From the entry to the `syscall`'s stretch, with an action and no place for the old one: the action's copy for
the kernel is in the frame. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {h : BitVec 64}
    (hsp : 328 < g.rsp.toNat) (hst : ∀ i < 328, Foot Wl (Addr.add (g.rsp - 328#64) i))
    (hact : g.rsi ≠ 0) (hold : g.rdx = 0) (ha : g.rsi.toNat + 140 ≤ 2 ^ 64)
    (hal : ∀ i < 140, Foot F.data (Addr.add g.rsi i))
    (hdis : g.rsi.toNat + 140 ≤ g.rsp.toNat - 328 ∨ g.rsp.toNat ≤ g.rsi.toNat)
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hh : rdq(V, g.rsi) = h) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 185 ∧ g' = g1 g ∧ Fr V V' g.rsp fb h) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst hact hold ha hal hdis hh
  subst hold
  have hb : (rsi == 0) = false := by simpa using hact
  have e16 : rsp - 328#64 + 312#64 = rsp - 16#64 := by bv_omega
  wpx [W_0, W_42, W_416, o0, o1, o8, Op.ldf, Op.vl, Op.vs, Op.cdqe, sk0', BitVec.and_self, hb, Bool.false_eq_true,
    false_implies, beq_self_eq_true, ↓reduceIte, e16]
  refine ⟨hfl, fun i hi => e16 ▸ frm_ft hst (d := 312) (by decide) i hi, ?_⟩
  have fa : ∀ d n : Nat, d + n ≤ 140 → ∀ i < n, Foot F.data ((rsi + BitVec.ofNat 64 d).add i) :=
    fun d n h => act_ft hal h
  have fw : ∀ d n : Nat, d + n ≤ 328 → ∀ i < n, Foot Wl ((rsp - 328#64 + BitVec.ofNat 64 d).add i) :=
    fun d n h => frm_ft hst h
  refine ⟨fun i hi => hal i (Nat.lt_trans hi (by decide)), fa 8 16 (by decide), fa 24 16 (by decide),
    fa 40 16 (by decide), fa 56 16 (by decide), fa 72 16 (by decide), fun i hi => hst i (Nat.lt_trans hi (by decide)),
    fa 136 4 (by decide), fa 88 16 (by decide), fw 24 16 (by decide), fun b1 h1 =>
    ⟨fa 104 16 (by decide), fa 120 16 (by decide), fw 40 16 (by decide), fun b2 h2 =>
    ⟨fw 56 16 (by decide), fun b3 h3 => ⟨fw 72 16 (by decide), fun b4 h4 =>
    ⟨fw 8 8 (by decide), fw 88 16 (by decide), fun b5 h5 => ⟨fw 16 8 (by decide), fw 104 16 (by decide), fun b6 h6 =>
    ⟨fw 120 16 (by decide), fun b7 h7 => ⟨fw 136 16 (by decide), fun b8 h8 => ⟨?_, ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · rfl
  refine ⟨fun a ha' => ?_, ?_, ?_⟩
  · repeat pv
  · repeat pv
    rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]
    pv
    exact hh
  · repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The registers at the `syscall`. -/
abbrev g2 (g : Gprs) : Gprs := { g1 g with rax := 13, r10 := 8 }

/-- To the `syscall`: `rt_sigaction`'s number and the size of a set of signals. -/
theorem vc_185 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_185 fb F Wl (fun j' g' _ V' => j' = 196 ∧ g' = { g with rax := 13, r10 := 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_185, o2]
  rfl

/-- From the `syscall`, the kernel's answer 0 and no place for the old action, to the check of the stack guard. -/
theorem vc_198 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) (h8 : g.r8 = 0) :
    W_198 fb F Wl (fun j' g' _ V' => j' = 383 ∧ g' = { g with r9 := 0 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h0 h8
  subst h0 h8
  wpx [W_198, W_210, W_222, o3, o4, o5]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => rfl, fun h => absurd h (by decide)⟩⟩

/-- The check of the stack guard, to the `ret`. -/
theorem vc_383 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h9 : g.r9 = 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 312#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 312#64) = rdq(V, fb + 40#64)) :
    W_383 fb F Wl (fun j' g' _ V' => j' = 412 ∧ g' = { g with rax := 0, rsp := g.rsp + 328#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h9 hl hc
  subst h9
  wpx [W_383, W_402, o6, o7, Op.xormf, hc, BitVec.xor_self]
  exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => rfl⟩

/-- An action whose handler is neither `SIG_DFL` nor `SIG_IGN` does not ignore a signal. -/
theorem ign_false {V : Addr → Byte} {a : Addr} {h : BitVec 64} (n : Nat) (hh : rdq(V, a) = h) (h0 : h ≠ 0)
    (h1 : h ≠ 1) : (actOf ((byteAddrs a 32).map V)).ignores n = false := by
  have e : (((byteAddrs a 32).map V).drop (8 * 0)).take 8 = (byteAddrs a 8).map V := rfl
  simp only [actOf, SigAction.ignores, SigAction.ofBytes, e, hh, h0, h1, ↓reduceIte]

/-- The event of `rt_sigaction` from `__libc_sigaction` called with registers `g`, the kernel's answer 0. -/
abbrev sgaEv (g : Gprs) : Event := ⟨13, [g.rdi, g.rsp - 328#64, 0, 8, 0, g.r9], 0, [], []⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__libc_sigaction (n, act, 0)` with a handler `h` in the action, from a start with `Base`: the run reaches the
return address with `rax`, `r8` and `r9` 0, the kernel's action for `n` set; the run goes on from the state after the
`syscall`, its own start. -/
theorem sga_ok {lim n : Nat} {b fb : Addr} {kst : Kst} {h : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fb kst) (hin : CodeIn L sga_at sga) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sga_at) (hsp : 328 < X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hst : ∀ i < 328, Foot Wl (Addr.add (X.cpu.gpr.rsp - 328#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hsig : argInt X.cpu.gpr.rdi = (n : Int)) (h1 : 1 ≤ n) (h64 : n ≤ 64) (h9 : n ≠ 9) (h19 : n ≠ 19)
    (hact : X.cpu.gpr.rsi ≠ 0) (hold : X.cpu.gpr.rdx = 0) (ha : X.cpu.gpr.rsi.toNat + 140 ≤ 2 ^ 64)
    (hal : ∀ i < 140, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hdis : X.cpu.gpr.rsi.toNat + 140 ≤ X.cpu.gpr.rsp.toNat - 328 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    (hh : rdq(V, X.cpu.gpr.rsi) = h) (hh0 : h ≠ 0) (hh1 : h ≠ 1)
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hfb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 328 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (k : ∀ s₁ V' g' Z t', Seg prof F Wl L s₁ o → Base s₁ lim b fb kst → KeptW Wl s₁ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 328 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → V' a = V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = 0 → g'.r8 = 0 → g'.r9 = 0 → Osv.Back X.cpu.gpr g' →
      GoG prof L o (gev ++ [sgaEv X.cpu.gpr]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to the `syscall`
  refine (c_0 prof fb).run c hB.fsb hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hsp hst hact hold ha hal hdis hfl hh) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine (c_185 prof fb).run c hB.fsb hin _ hK₁ hA₁ hr₁ vc_185 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hg₂' : Y₂.cpu.gpr = g2 X.cpu.gpr := by rw [hg₂, hg₁]
  have e32 : (X.cpu.gpr.rsp - 328#64).toNat = X.cpu.gpr.rsp.toNat - 328 := by bv_omega
  -- `rt_sigaction`
  refine c.b_sigaction hB hK₂ hA₂ hin (lt_len (by decide)) hr₂ (sys_196 _) (by rw [hg₂']; rfl) (by rw [hg₂']; rfl)
    (by rw [hg₂']; show X.cpu.gpr.rsp - 328#64 ≠ 0; bv_omega) (by rw [hg₂']) (by rw [hg₂']; exact hsig) h1 h64 h9 h19
    (by rw [hg₂']; show (X.cpu.gpr.rsp - 328#64).toNat + 32 ≤ _; omega)
    (by rw [hg₂']; exact fun i hi => c.hws _ (hst i (Nat.lt_trans hi (by decide))))
    (by rw [hg₂']; exact ign_false n hF.hnd hh0 hh1) ?_
  intro s₁ t₃ c₁ hB₁ hA₃ hr₃ hg₃ _
  have hev : sysEv Y₂ 0 = sgaEv X.cpu.gpr := by simp only [sysEv, hg₂']
  rw [hev]
  -- to the `ret`
  refine (c_198 prof fb).run c₁ hB₁.fsb hin _ (KeptW.refl _ _) hA₃ hr₃
    (vc_198 (by rw [hg₃]; rfl) (by rw [hg₃]; unfold sysGpr; rw [hg₂']; rfl)) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 328#64 := by rw [hg₄, hg₃]; unfold sysGpr; rw [hg₂']; rfl
  have e16 : X.cpu.gpr.rsp - 328#64 + 312#64 = X.cpu.gpr.rsp - 16#64 := by bv_omega
  refine (c_383 prof fb).run c₁ hB₁.fsb hin _ hK₄ hA₄ hr₄ (vc_383 (by rw [hg₄]) (fun i hi => ?_) hfl ?_) ?_
  · rw [hsp₄]
    exact c.hws _ (frm_ft hst (d := 312) (by decide) i hi)
  · rw [hsp₄, e16, hF.can]
    exact (congrArg (ofBytesLE 64) (rd_out hF.out hfb hfd)).symm
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₅]
    show Y₄.cpu.gpr.rsp + 328#64 = _
    rw [hsp₄]
    bv_omega
  have etop : rdq(V₅, X.cpu.gpr.rsp) = rdq(V, X.cpu.gpr.rsp) := by
    congr 1
    apply List.map_congr_left
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
    refine hF.out _ fun h => ?_
    simp only [Addr.add] at h
    bv_omega
  refine c₁.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_412 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₅]
    exact hl i hi
  · rw [hsp₅, etop]
    exact hra
  rintro Z t₆ hKZ hAZ ⟨hrZ, hgZ⟩
  have keep : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₅.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₅.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₅.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₅.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₅.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₅, hg₄, hg₃]
    unfold sysGpr
    rw [hg₂']
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine k s₁ V₅ _ Z t₆ c₁ hB₁ hKZ hAZ hF.out hrZ hgZ ?_ ?_ ?_ ⟨?_, keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1,
    keep.2.2.2.2.1, keep.2.2.2.2.2⟩
  · rw [hg₅]
    rfl
  · rw [hg₅, hg₄, hg₃]
    unfold sysGpr
    rw [hg₂']
    rfl
  · rw [hg₅, hg₄, hg₃]
    rfl
  · show Y₅.cpu.gpr.rsp + 8 = _
    rw [hsp₅]
    rfl

end FV7z.Sga
