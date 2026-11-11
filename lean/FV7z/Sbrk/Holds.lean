import FV7z.Sbrk.Cuts
import FV7z.Brk.Holds
import FV7z.Tun.Inv
/-!
# The first `__sbrk` of a run grows the break (PLAN.md G3, startup)

glibc 2.31's `__sbrk (n)` at `0x666390` in `7zzs`. With `__curbrk` 0, as the file has it, `__sbrk` calls `__brk (0)`
for the break `b`, then with `n` above 0 and `b + n` not past the end of the address space `__brk (b + n)`, and
returns `b`. Five pieces of the code between the calls (cut points 0, 96, 103, 36, 145; `vc_*`), `Seg.s_call` and
`Seg.s_ret` at the two calls of `__brk`, `Brk.brk_keep` for the first and `Brk.brk_grow` for the second.

- `frame`: the bytes `__sbrk` leaves, outside the new pages, the 32 bytes below the stack pointer and `__curbrk`.
- `sbrk_first`: from a start with `Base`, `__curbrk` 0, `0 < n < 2 ^ 47`, the page of `b + n` above the break's and
  not above the `lim`-th, the kernel not refusing memory, the run reaches the `ret` (159) from a new start with the
  regions `N` of the new pages and `Base` with the break `b + n`. There `rax` is `b`, the registers a call keeps are
  as at the entry (`Saved`), the new pages' bytes are 0, `__curbrk` is `b + n`, and the other bytes are as at the
  entry but for the 32 below the stack pointer.

The ways not taken in these runs: the read of `__libc_multiple_libcs` (`0x7939c0`; not reached when `__curbrk` is
0), `n` 0 or below, the overflow of `b + n`, and `__brk` failing (`ENOMEM`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Sbrk

variable {F : Footprint} {Wl : List Rgn}

/-- `setb al`: the low byte is the flag. -/
theorem setb_al (x : BitVec 64) (c : Bool) :
    BitVec.setWidth 8 (x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.ofBool c)) <<< 0) = BitVec.setWidth 8 (BitVec.ofBool c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem cond_14 (f : Rflags) : f.cond 14 = (f.zf || (f.sf != f.of)) := rfl
theorem rfz_of (f : Rflags) : (rfz f).of = f.of := rfl
theorem arith_of {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).of = of := rfl
theorem addF_cf {w : Nat} (f : Rflags) (x y : BitVec w) : (addF f x y).cf = decide (2 ^ w ≤ x.toNat + y.toNat) := by
  simp [addF, carryAdd]

/-- From the entry, `__curbrk` 0, to the `xor` before the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : ∀ i < 8, Foot F.data (curbrk.add i)) (hst : ∀ i < 16, Foot Wl (Addr.add (g.rsp - 16) i))
    (hsp : 0x7a4c40 + 32 ≤ g.rsp.toNat) (h0 : rdq(V, curbrk) = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = ((g.set 12 0).set 3 g.rdi).set 4 (g.rsp - 8 - 8 - 8) ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hsp' : 0x7a4c40 + 32 ≤ rsp.toNat := hsp
  have hst' : ∀ i < 16, Foot Wl (Addr.add (rsp - 16) i) := hst
  have e : rdq(Vst (Vst V (rsp - 8) (toBytesLE r12 8)) (rsp - 8 - 8) (toBytesLE rbx 8), 8014904#64) = 0 := by
    rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by decide)
        (by simp only [toBytesLE_length]; bv_omega),
      rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by decide)
        (by simp only [toBytesLE_length]; bv_omega)]
    exact h0
  wpx [W_0, W_26, o0, o1, Op.lda]
  simp only [e]
  refine ⟨fun i hi => ?_, fun i hi => ?_, hc, fun _ => rfl, fun h => absurd h (by decide)⟩
  · have h := hst' (8 + i) (by omega)
    have e2 : Addr.add (rsp - 16) (8 + i) = Addr.add (rsp - 8) i := by simp only [Addr.add]; bv_omega
    rw [← e2]
    exact h
  · have h := hst' i (by omega)
    have e2 : rsp - 8 - 8 = rsp - 16 := by bv_omega
    rw [e2]
    exact h

/-- From after the first `call`, `__brk` having returned 0: `r12` is `__curbrk`. -/
theorem vc_103 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : ∀ i < 8, Foot F.data (curbrk.add i))
    (h0 : g.rax = 0) :
    W_103 F Wl (fun j' g' _ V' => j' = 36 ∧ g' = g.set 12 rdq(V, curbrk) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 0 := h0
  wpx [W_103, W_114, o6, Op.lda]
  exact ⟨hc, fun _ => rfl, fun h => absurd h (by decide)⟩

/-- From 36 with an increment above 0 that does not overflow, to the second `call`: `rdi` is the new break. -/
theorem vc_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : 0 < g.rbx.toNat) (h2 : g.rbx.toNat < 2 ^ 47)
    (h3 : g.r12.toNat ≤ 2 ^ 47) :
    W_36 F Wl (fun j' g' _ V' => j' = 140 ∧ (∃ ax, g' = (g.set 0 ax).set 7 (g.r12 + g.rbx)) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' : 0 < rbx.toNat := h1
  have h2' : rbx.toNat < 2 ^ 47 := h2
  have h3' : r12.toNat ≤ 2 ^ 47 := h3
  have hz : (rbx == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    rw [e] at h1'
    exact absurd h1' (by decide)
  have hm : rbx.msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false (by omega)
  have hcf : ∀ fl : Rflags, (addF fl r12 rbx).cf = false := by
    intro fl
    rw [addF_cf]
    exact decide_eq_false (by omega)
  wpx [W_36, W_77, W_41, W_43, W_136, o2, o3, o4, o7, Op.setcc, cond_14, rfz_of, arith_of, hz, hcf, setb_al,
    BitVec.and_self, hm]
  exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h (by decide)⟩⟩

/-- From after the second `call`, `__brk` having returned 0, to the `ret`: the old break in `rax`. -/
theorem vc_145 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 16, Foot F.data (Addr.add (g.rsp + 8) i))
    (h0 : g.rax = 0) :
    W_145 F Wl (fun j' g' _ V' => j' = 159 ∧ g' = (((g.set 4 (g.rsp + 8 + 8 + 8)).set 0 g.r12).set 3
      rdq(V, g.rsp + 8)).set 12 rdq(V, g.rsp + 8 + 8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 0 := h0
  have hl' : ∀ i < 16, Foot F.data (Addr.add (rsp + 8) i) := hl
  wpx [W_145, W_149, o8, o4]
  refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun i hi => hl' i (by omega), fun i hi => ?_, rfl⟩⟩
  have e : Addr.add (rsp + 8#64 + 8) i = Addr.add (rsp + 8) (8 + i) := by simp only [Addr.add]; bv_omega
  rw [e]
  exact hl' (8 + i) (by omega)

theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_96 F Wl (fun j' g' _ V' => j' = 98 ∧ g' = g.set 7 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_96, o5]
  rw [BitVec.xor_self]
  rfl

/-! ## The `call`s and the `ret` -/

def pc98 : List Byte := [0xe8, 0x09, 0xc6, 0x03, 0x00]
def pc140 : List Byte := [0xe8, 0xdf, 0xc5, 0x03, 0x00]
def pret : List Byte := [0xc3]
theorem pc98_0 : ∀ feat, Dec feat pc98 0 (FV7z.mk .call 64 [.rel 247305] 5) := by dec_rfl
theorem pc140_0 : ∀ feat, Dec feat pc140 0 (FV7z.mk .call 64 [.rel 247263] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc98 : pc98 <+: sbk.drop 98 := by decide +kernel
theorem wc140 : pc140 <+: sbk.drop 140 := by decide +kernel
theorem w_159 : pret <+: sbk.drop 159 := by decide +kernel
theorem call_98 (feat : Features) : Dec feat sbk 98 (FV7z.mk .call 64 [.rel 247305] 5) :=
  Dec.shift (j := 98) (k := 0) (pc98_0 feat) wc98 (Nat.zero_le _)
theorem call_140 (feat : Features) : Dec feat sbk 140 (FV7z.mk .call 64 [.rel 247263] 5) :=
  Dec.shift (j := 140) (k := 0) (pc140_0 feat) wc140 (Nat.zero_le _)
theorem ret_159 (feat : Features) : Dec feat sbk 159 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 159) (k := 0) (pret_0 feat) w_159 (Nat.zero_le _)

/-- A byte of the 32 below the stack pointer at the entry. -/
theorem slot {sp a : Addr} (hst : ∀ i < 32, Foot Wl (Addr.add (sp - 32) i)) {k : Nat} (hk : k < 32)
    (ha : a = Addr.add (sp - 32) k) : Foot Wl a := ha ▸ hst k hk

/-- The event of a `brk (a)` from `__sbrk` called in `X`, the kernel's answer `v`. -/
abbrev sbrkEv (X : State) (a v : BitVec 64) : Event :=
  ⟨12, [a, X.cpu.gpr.rsi, X.cpu.gpr.rdx, X.cpu.gpr.r10, X.cpu.gpr.r8, X.cpu.gpr.r9], v, [], []⟩

/-- Side conditions of reads and stores at addresses given from the stack pointer. -/
macro "sd" : tactic =>
  `(tactic| first | (simp only [toBytesLE_length]; done) | (simp only [toBytesLE_length]; bv_omega) | bv_omega | decide)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- The bytes `__sbrk` leaves, outside the new pages, the 32 bytes below the stack pointer and `__curbrk`. -/
theorem frame (V : Addr → Byte) {sp a : Addr} {lo hi : Nat} (x1 x2 x3 x4 x5 x6 : BitVec 64)
    (hsp : 0x7a4c40 + 32 ≤ sp.toNat) (h1 : ¬ (lo ≤ a.toNat ∧ a.toNat < hi))
    (h2 : ¬ (sp.toNat - 32 ≤ a.toNat ∧ a.toNat < sp.toNat)) (h3 : ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40)) :
    Vst (Vz (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8)) (sp - 8 - 8 - 8 - 8)
      (toBytesLE x3 8)) curbrk (toBytesLE x4 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE x5 8)) lo hi) curbrk
      (toBytesLE x6 8) a = V a := by
  rw [Vst_out, Vz_out h1, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals simp only [toBytesLE_length]
  all_goals bv_omega

/-- The bytes `__sbrk` has left where it saved `r12`. -/
theorem rd_x1 (V : Addr → Byte) {sp : Addr} {lo hi : Nat} (x1 x2 x3 x4 x5 x6 : BitVec 64)
    (hsp : 0x7a4c40 + 32 ≤ sp.toNat)
    (hout : ∀ a : Addr, sp.toNat - 32 ≤ a.toNat → a.toNat < sp.toNat → ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    rdq(Vst (Vz (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8))
      (sp - 8 - 8 - 8 - 8) (toBytesLE x3 8)) curbrk (toBytesLE x4 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE x5 8)) lo hi)
      curbrk (toBytesLE x6 8), sp - 8) = x1 := by
  rw [rd_Vst, rd_Vz _ _ _ (sp - 8) 8 (fun i hi => hout _ (by simp only [Addr.add]; bv_omega)
    (by simp only [Addr.add]; bv_omega)), rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self,
    ofBytesLE_toBytesLE (n := 8) rfl]
  all_goals sd

/-- The bytes `__sbrk` has left where it saved `rbx`. -/
theorem rd_x2 (V : Addr → Byte) {sp : Addr} {lo hi : Nat} (x1 x2 x3 x4 x5 x6 : BitVec 64)
    (hsp : 0x7a4c40 + 32 ≤ sp.toNat)
    (hout : ∀ a : Addr, sp.toNat - 32 ≤ a.toNat → a.toNat < sp.toNat → ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    rdq(Vst (Vz (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8))
      (sp - 8 - 8 - 8 - 8) (toBytesLE x3 8)) curbrk (toBytesLE x4 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE x5 8)) lo hi)
      curbrk (toBytesLE x6 8), sp - 8 - 8) = x2 := by
  rw [rd_Vst, rd_Vz _ _ _ (sp - 8 - 8) 8 (fun i hi => hout _ (by simp only [Addr.add]; bv_omega)
    (by simp only [Addr.add]; bv_omega)), rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
  all_goals sd

/-- The return address of the second `call`, in the bytes `__sbrk` has left. -/
theorem rd_x5 (V : Addr → Byte) {sp : Addr} {lo hi : Nat} (x1 x2 x3 x4 x5 x6 : BitVec 64)
    (hsp : 0x7a4c40 + 32 ≤ sp.toNat)
    (hout : ∀ a : Addr, sp.toNat - 32 ≤ a.toNat → a.toNat < sp.toNat → ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    rdq(Vst (Vz (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8))
      (sp - 8 - 8 - 8 - 8) (toBytesLE x3 8)) curbrk (toBytesLE x4 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE x5 8)) lo hi)
      curbrk (toBytesLE x6 8), sp - 8 - 8 - 8 - 8) = x5 := by
  rw [rd_Vst, rd_Vz _ _ _ (sp - 8 - 8 - 8 - 8) 8 (fun i hi => hout _ (by simp only [Addr.add]; bv_omega)
    (by simp only [Addr.add]; bv_omega)), rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
  all_goals sd

/-- The bytes of the new pages after `__sbrk`: 0. -/
theorem zero_new (W : Addr → Byte) {a : Addr} {lo hi : Nat} (x6 : BitVec 64) (h1 : lo ≤ a.toNat) (h2 : a.toNat < hi)
    (h3 : a.toNat < 0x7a4c38 ∨ 0x7a4c38 + 8 ≤ a.toNat) : Vst (Vz W lo hi) curbrk (toBytesLE x6 8) a = 0 := by
  rw [Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; exact h3)]
  exact Vz_in h1 h2

/-- The end of `__sbrk`: from the `ret` of the second `__brk`, which has returned 0, to the `ret`. `q` is the stack
pointer at that `ret` of `__brk`. -/
theorem sbrk_end {G : Footprint} {Wn : List Rgn} {s₁ Y : State} {V₉ : Addr → Byte} {q : Addr}
    (c' : Seg prof G Wn L s₁ o) (hin : CodeIn L sbk_at sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wn s₁ Y) (hA : Agree G Y.proc.mm.mem V₉) (hr : Y.cpu.rip = Brk.brk_at.add 33)
    (hsp : Y.cpu.gpr.rsp = q) (hst : ∀ i < 32, Foot G.data (Addr.add q i)) (hra : rdq(V₉, q) = sbk_at.add 145)
    (hax : Y.cpu.gpr.rax = 0)
    (k : ∀ Z t', KeptW Wn s₁ Z → Agree G Z.proc.mm.mem V₉ → Z.cpu.rip = sbk_at.add 159 →
      Z.cpu.gpr = ((((Y.cpu.gpr.set 4 (q + 8)).set 4 (q + 8 + 8 + 8 + 8)).set 0 Y.cpu.gpr.r12).set 3
        rdq(V₉, q + 8 + 8)).set 12 rdq(V₉, q + 8 + 8 + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine c'.s_ret hK hA hinb (Brk.lt_len (by decide)) hr (Brk.ret_33 _) (fun i hi => ?_) hin (j₂ := 145)
    (lt_len (by decide)) (by rw [hsp]; exact hra) ?_
  · rw [hsp]
    exact hst i (by omega)
  rintro Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀⟩
  rw [hsp] at hg₁₀
  have hax₁₀ : Y₁₀.cpu.gpr.rax = 0 := by rw [hg₁₀]; exact hax
  have hsp₁₀ : Y₁₀.cpu.gpr.rsp = q + 8 := by rw [hg₁₀]; rfl
  refine (c_145 prof).run c' hin _ hK₁₀ hA₁₀ hr₁₀ (vc_145 (fun i hi => ?_) hax₁₀) ?_
  · rw [hsp₁₀]
    have e : Addr.add (q + 8 + 8) i = Addr.add q (16 + i) := by
      simp only [Addr.add]
      bv_omega
    rw [e]
    exact hst _ (by omega)
  rintro j' g fl V₁₁ ⟨rfl, rfl, rfl⟩ Y₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ hg₁₁ -
  refine k Y₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ ?_
  rw [hg₁₁, hg₁₀]
  rfl

set_option maxHeartbeats 1600000 in
/-- The first `__sbrk (n)` of a run from a start with `Base` (`__curbrk` is 0), `n` above 0 and the new break's page
above the break's, the kernel not refusing memory: `__brk (0)` asks for the break `b`, `__brk (b + n)` grows it. At
the `ret` the run has a new start with the regions `N` of the new pages and `Base` with the break `b + n`; `rax` is
`b`, the registers a call keeps are as at the entry, the new pages' bytes are 0, `__curbrk` is `b + n`, and the
bytes else are as they were but for the 32 below the stack pointer. -/
theorem sbrk_first {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L sbk_at sbk) (hinb : CodeIn L Brk.brk_at Brk.brk) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sbk_at) (hcur : ∀ i < 8, Foot Wl (curbrk.add i))
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i)) (hsp : 0x7a4c40 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (hc0 : rdq(V, curbrk) = 0) (hn0 : 0 < X.cpu.gpr.rdi.toNat) (hn : X.cpu.gpr.rdi.toNat < 2 ^ 47)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hgt : pageUp b.toNat / 4096 < pageUp (b + X.cpu.gpr.rdi).toNat / 4096)
    (hlim : pageUp (b + X.cpu.gpr.rdi).toNat / 4096 ≤ lim)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096))
    (k : ∀ g' V₂ s₁ Z t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + X.cpu.gpr.rdi) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V₂ → Z.cpu.rip = sbk_at.add 159 → Z.cpu.gpr = g' →
      g'.rax = b → Saved X.cpu.gpr g' →
      (∀ a : Addr, pageUp b.toNat / 4096 * 4096 ≤ a.toNat →
        a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096 → V₂ a = 0) →
      (∀ a : Addr, ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧
          a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) →
        ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = V a) →
      rdq(V₂, curbrk) = b + X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sbrkEv X 0 b, sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hle := hB.le
  have hcurD : ∀ i < 8, Foot F.data (curbrk.add i) := fun i hi => c.hws _ (hcur i hi)
  obtain ⟨-, -, hbm0, -, -⟩ := c.ready.layout
  -- the bytes below the stack pointer and `__curbrk` are not in the new pages
  have hout : ∀ k < 32, ¬ (pageUp b.toNat / 4096 * 4096 ≤ (Addr.add (X.cpu.gpr.rsp - 32) k).toNat ∧
      (Addr.add (X.cpu.gpr.rsp - 32) k).toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) :=
    fun k hk h => c.foot_below hB (foot_data (c.hws _ (hst k hk))) ⟨h.1, by omega⟩
  have hcbo : ∀ a : Addr, 0x7a4c38 ≤ a.toNat → a.toNat < 0x7a4c40 →
      ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) := by
    intro a h1 h2 h
    have e : curbrk.add (a.toNat - 0x7a4c38) = a := by simp only [Addr.add]; bv_omega
    have h3 := c.foot_below hB (foot_data (hcurD (a.toNat - 0x7a4c38) (by omega)))
    rw [e] at h3
    exact h3 ⟨h.1, by omega⟩
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcurD (fun i hi => slot hst (k := 16 + i) (by omega) (by simp only [Addr.add]; bv_omega)) hsp hc0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine (c_96 prof).run c hin _ hK₁ hA₁ hr₁ vc_96 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hg₂, hg₁]; rfl
  -- `__brk (0)`
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_98 _) hinb (Brk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₂]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsp₂] at hA₃ hg₃
  have hdi₃ : Y₃.cpu.gpr.rdi = 0 := by rw [hg₃, hg₂]; rfl
  have e₃ : Brk.brkEv Y₃ s₀.proc.mm.brk = sbrkEv X 0 b := by
    simp only [Brk.brkEv, sbrkEv, hg₃, hg₂, hg₁, hB.brk]
    rfl
  refine Brk.brk_keep c hinb hK₃ hA₃ hr₃ hcur (by rw [hdi₃]; exact hbm0) (by rw [hB.brk]; omega) ?_
  rw [e₃, hB.brk]
  intro rc r11 Y₄ t₄ hK₄ hA₄ hr₄ hg₄
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 := by rw [hg₄, hg₃]; rfl
  refine c.s_ret hK₄ hA₄ hinb (Brk.lt_len (by decide)) hr₄ (Brk.ret_33 _) (fun i hi => ?_) hin (j₂ := 103)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₄]
    exact c.hws _ (slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega))
  · rw [hsp₄, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  have hax₅ : Y₅.cpu.gpr.rax = 0 := by rw [hg₅, hg₄]; rfl
  refine (c_103 prof).run c hin _ hK₅ hA₅ hr₅ (vc_103 hcurD hax₅) ?_
  rintro j' g fl V₆ ⟨rfl, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  have e₆ : ∀ W : Addr → Byte, rdq(Vst W curbrk (toBytesLE b 8), curbrk) = b := by
    intro W
    rw [rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd
  rw [e₆] at hg₆
  have hbx₆ : Y₆.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]; rfl
  have h12₆ : Y₆.cpu.gpr.r12 = b := by rw [hg₆]; rfl
  refine (c_36 prof).run c hin _ hK₆ hA₆ hr₆
    (vc_36 (by rw [hbx₆]; exact hn0) (by rw [hbx₆]; exact hn) (by rw [h12₆]; omega)) ?_
  rintro j' g fl V₇ ⟨rfl, ⟨ax, rfl⟩, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [h12₆, hbx₆] at hg₇
  have hsp₇ : Y₇.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by
    rw [hg₇, hg₆, hg₅, hsp₄]
    show X.cpu.gpr.rsp - 8 - 8 - 8 - 8 + 8 = _
    bv_omega
  -- `__brk (b + n)`
  refine c.s_call hK₇ hA₇ hin (lt_len (by decide)) hr₇ (call_140 _) hinb (Brk.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₇]
    exact slot hst (k := i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [hsp₇] at hA₈ hg₈
  have hdi₈ : Y₈.cpu.gpr.rdi = b + X.cpu.gpr.rdi := by rw [hg₈, hg₇]; rfl
  have e₈ : Brk.brkEv Y₈ Y₈.cpu.gpr.rdi = sbrkEv X (b + X.cpu.gpr.rdi) (b + X.cpu.gpr.rdi) := by
    simp only [Brk.brkEv, sbrkEv, hg₈, hg₇, hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]
    rfl
  refine Brk.brk_grow c hB hinb hK₈ hA₈ hr₈ hcur hmg (by rw [hdi₈]; exact hgt) (by rw [hdi₈]; exact hlim)
    (by rw [hdi₈]; exact hN) ?_
  rw [e₈, hdi₈, List.append_assoc]
  intro rc' r11' s₁ Y₉ t₉ c' hB' hK₉ hA₉ hr₉ hg₉
  have hout' : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat →
      ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < pageUp (b + X.cpu.gpr.rdi).toNat / 4096 * 4096) := by
    intro a h1 h2
    have e : Addr.add (X.cpu.gpr.rsp - 32) (a.toNat - (X.cpu.gpr.rsp.toNat - 32)) = a := by
      simp only [Addr.add]
      bv_omega
    have h3 := hout (a.toNat - (X.cpu.gpr.rsp.toNat - 32)) (by omega)
    rw [e] at h3
    exact h3
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by bv_omega
  have h12₉ : Y₉.cpu.gpr.r12 = b := by rw [hg₉, hg₈, hg₇]; exact h12₆
  have hkeep : Y₉.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₉.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
      Y₉.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₉.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₉, hg₈, hg₇, hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine sbrk_end c' hin hinb hK₉ hA₉ hr₉ (q := X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (by rw [hg₉, hg₈]; rfl)
    (fun i hi => ?_) (rd_x5 V _ _ _ _ _ _ hsp hout') (by rw [hg₉]; rfl) ?_
  · rw [e32]
    exact c'.hws _ (foot_append_iff.2 (.inr (hst i hi)))
  intro Z t' hKz hAz hrz hgz
  have e1 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8 = X.cpu.gpr.rsp := by bv_omega
  have e2 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 + 8 + 8 = X.cpu.gpr.rsp - 8 - 8 := by bv_omega
  have e3 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 + 8 + 8 + 8 = X.cpu.gpr.rsp - 8 := by bv_omega
  rw [e1, e3, e2, rd_x1 V _ _ _ _ _ _ hsp hout', rd_x2 V _ _ _ _ _ _ hsp hout'] at hgz
  refine k _ _ s₁ Z t' c' hB' hKz hAz hrz hgz h12₉ ⟨rfl, rfl, hkeep.1, rfl, hkeep.2.1, hkeep.2.2.1, hkeep.2.2.2⟩ ?_ ?_
    ?_
  · intro a h1 h2
    refine zero_new _ _ h1 h2 ?_
    by_cases h : 0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40
    · exact absurd ⟨h1, h2⟩ (hcbo a h.1 h.2)
    · omega
  · intro a h1 h2 h3
    exact frame V _ _ _ _ _ _ hsp h1 h2 h3
  · rw [rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals sd

end FV7z.Sbrk
