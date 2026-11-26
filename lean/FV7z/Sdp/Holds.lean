import FV7z.Sdp.Cuts
import FV7z.Startup.StrAt
import FV7z.Tls.Holds
import FV7z.Hwc.Call
/-!
# `__strdup`: `strlen`, `malloc`, then `memcpy` (PLAN.md §M, M1)

glibc 2.31's `__strdup (s)` at `0x635dd0` in `7zzs`: `r12` and `rbp` saved, `strlen (s)` through the PLT
(`Str.LenAt`), `malloc (n + 1)` (`Mal.At`), then the registers given back and a tail jump to `memcpy (p, s, n + 1)`
through the PLT (`Tls.CpyAt`), which returns `p` to the caller. Three pieces of code: from the entry to the call of
`strlen` (0), from its return to the call of `malloc` (19), from its return to the jump (31). `malloc`'s contract
gives a block at `0x792a80` or above, never 0, so the way to the `ret` with 0 (57) is not one of these runs.

- `frV`: the two registers saved below the stack pointer; `sdFr1`, `sdFr2`: the bytes outside the 32 below the
  stack pointer as they were, after one or two return addresses; `sdRbp`, `sdR12`: the saved registers read back.
- `sdp_ok`: called with a string of `n < 1024` bytes that are not 0 and a 0, outside what `malloc` may change
  (below `0x792a80` or above the stack pointer), the run reaches the return address with `rax` the block `p`, the
  string's `n + 1` bytes at `p`, the registers a call keeps kept, and `malloc`'s facts about the bytes.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Sdp

/-! ## The calls and the jump -/

def pc14 : List Byte := [0xe8, 0x25, 0xb3, 0xdc, 0xff]
theorem pc14_0 : ∀ feat, Dec feat pc14 0 (FV7z.mk .call 64 [.rel 18446744073707238181] 5) := by dec_rfl
theorem w_14 : pc14 <+: sdp.drop 14 := by decide +kernel
theorem call_14 (feat : Features) : Dec feat sdp 14 (FV7z.mk .call 64 [.rel 18446744073707238181] 5) :=
  Dec.shift (j := 14) (k := 0) (pc14_0 feat) w_14 (Nat.zero_le _)

def pc26 : List Byte := [0xe8, 0x71, 0xd3, 0xff, 0xff]
theorem pc26_0 : ∀ feat, Dec feat pc26 0 (FV7z.mk .call 64 [.rel 18446744073709540209] 5) := by dec_rfl
theorem w_26 : pc26 <+: sdp.drop 26 := by decide +kernel
theorem call_26 (feat : Features) : Dec feat sdp 26 (FV7z.mk .call 64 [.rel 18446744073709540209] 5) :=
  Dec.shift (j := 26) (k := 0) (pc26_0 feat) w_26 (Nat.zero_le _)

def pj52 : List Byte := [0xe9, 0x67, 0xb2, 0xdc, 0xff]
theorem pj52_0 : ∀ feat, Dec feat pj52 0 (FV7z.mk .jmp 64 [.rel 18446744073707237991] 5) := by dec_rfl
theorem w_52 : pj52 <+: sdp.drop 52 := by decide +kernel
theorem jmp_52 (feat : Features) : Dec feat sdp 52 (FV7z.mk .jmp 64 [.rel 18446744073707237991] 5) :=
  Dec.shift (j := 52) (k := 0) (pj52_0 feat) w_52 (Nat.zero_le _)

/-! ## Offsets from the stack pointer -/

theorem sdE16 (x : BitVec 64) : x - 8 - 8 = x - 16#64 := by bv_omega
theorem sdE24 (x : BitVec 64) : x - 16#64 - 8#64 = x - 24#64 := by bv_omega
theorem sdE32 (x : BitVec 64) : x - 24#64 - 8 = x - 32#64 := by bv_omega
theorem sdA24 (x : BitVec 64) : x - 32#64 + 8 = x - 24#64 := by bv_omega
theorem sdA16 (x : BitVec 64) : x - 24#64 + 8#64 = x - 16#64 := by bv_omega
theorem sdA8 (x : BitVec 64) : x - 24#64 + 16#64 = x - 8#64 := by bv_omega
theorem sdA0 (x : BitVec 64) : x - 24#64 + 24#64 = x := by bv_omega
theorem sdP16 (x : BitVec 64) : x + 8#64 + 8 = x + 16#64 := by bv_omega
theorem sdP24 (x : BitVec 64) : x + 16#64 + 8 = x + 24#64 := by bv_omega
theorem sdT8 {x : BitVec 64} (h : 8 ≤ x.toNat) : (x - 8#64).toNat = x.toNat - 8 := by bv_omega
theorem sdT16 {x : BitVec 64} (h : 16 ≤ x.toNat) : (x - 16#64).toNat = x.toNat - 16 := by bv_omega
theorem sdT32 {x : BitVec 64} (h : 32 ≤ x.toNat) : (x - 32#64).toNat = x.toNat - 32 := by bv_omega
theorem sdN1 {n : Nat} (h : n < 1024) : (BitVec.ofNat 64 n + 1#64).toNat = n + 1 := by bv_omega

/-! ## The frame -/

/-- The two registers saved, called with registers `g`. -/
def frV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8#64) (toBytesLE g.r12 8)) (g.rsp - 16#64) (toBytesLE g.rbp 8)

variable {V : Addr → Byte} {g : Gprs}

theorem sdFr1 {r1 : Addr} (hs : 32 ≤ g.rsp.toNat) {a : Addr}
    (h : ¬ (g.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < g.rsp.toNat)) :
    Vst (frV V g) (g.rsp - 32#64) (toBytesLE r1 8) a = V a := by
  have hl := g.rsp.isLt
  have e8 := sdT8 (x := g.rsp) (by omega)
  have e16 := sdT16 (x := g.rsp) (by omega)
  have e32 := sdT32 (x := g.rsp) hs
  unfold frV
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [toBytesLE_length, e32]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (by rw [toBytesLE_length, e16]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)]

theorem sdFr2 {r1 r2 : Addr} (hs : 32 ≤ g.rsp.toNat) {a : Addr}
    (h : ¬ (g.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < g.rsp.toNat)) :
    Vst (Vst (frV V g) (g.rsp - 32#64) (toBytesLE r1 8)) (g.rsp - 32#64) (toBytesLE r2 8) a = V a := by
  have hl := g.rsp.isLt
  have e32 := sdT32 (x := g.rsp) hs
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [toBytesLE_length, e32]; omega)]
  exact sdFr1 hs h

theorem sdRbp {r1 r2 : Addr} (hs : 32 ≤ g.rsp.toNat) :
    rdq(Vst (Vst (frV V g) (g.rsp - 32#64) (toBytesLE r1 8)) (g.rsp - 32#64) (toBytesLE r2 8), g.rsp - 16#64) =
      g.rbp := by
  have hl := g.rsp.isLt
  have e16 := sdT16 (x := g.rsp) (by omega)
  have e32 := sdT32 (x := g.rsp) hs
  unfold frV
  rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [e16]; omega)
      (by rw [toBytesLE_length, e32, e16]; omega),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [e16]; omega)
      (by rw [toBytesLE_length, e32, e16]; omega),
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e16]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem sdR12 {r1 r2 : Addr} (hs : 32 ≤ g.rsp.toNat) :
    rdq(Vst (Vst (frV V g) (g.rsp - 32#64) (toBytesLE r1 8)) (g.rsp - 32#64) (toBytesLE r2 8), g.rsp - 8#64) =
      g.r12 := by
  have hl := g.rsp.isLt
  have e8 := sdT8 (x := g.rsp) (by omega)
  have e16 := sdT16 (x := g.rsp) (by omega)
  have e32 := sdT32 (x := g.rsp) hs
  unfold frV
  rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [e8]; omega)
      (by rw [toBytesLE_length, e32, e8]; omega),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e32]; omega) (by rw [e8]; omega)
      (by rw [toBytesLE_length, e32, e8]; omega),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e16]; omega) (by rw [e8]; omega)
      (by rw [toBytesLE_length, e16, e8]; omega),
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e8]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- Bytes read where two memories agree. -/
theorem sdRd {V V' : Addr → Byte} {P : Addr → Prop} (h : ∀ a, P a → V' a = V a) {x : Addr} {n : Nat}
    (hP : ∀ i < n, P (Addr.add x i)) : List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  exact h _ (hP i hi)

/-- Eight bytes from `b` in the stack below `s`. -/
theorem sdSlot {Wl : List Rgn} {hi : Nat} {s : Addr} (hstk : ∀ a : Addr, hi ≤ a.toNat → a.toNat < s.toNat → Foot Wl a)
    {b : Addr} (h1 : hi ≤ b.toNat) (h2 : b.toNat + 8 ≤ s.toNat) : ∀ i < 8, Foot Wl (Addr.add b i) := fun i hi' => by
  have hl := s.isLt
  have e := toNat_add_of_fits (a := b) (n := 8) hi' (by omega)
  exact hstk _ (by rw [e]; omega) (by rw [e]; omega)

/-! ## The straight pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- To the call of `strlen`: `r12` and `rbp` saved, the string's address in `rbp`. -/
theorem vc_0 {f : Rflags} (h8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8#64) i))
    (h16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 16#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 14 ∧ g' = { g with rsp := g.rsp - 24#64, rbp := g.rdi } ∧ V' = frV V g)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h8' : ∀ i < 8, Foot Wl (Addr.add (rsp - 8#64) i) := h8
  have h16' : ∀ i < 8, Foot Wl (Addr.add (rsp - 16#64) i) := h16
  wpx [W_0, o0]
  try simp only [sdE16, sdE24]
  all_goals repeat' (first | exact h8' | exact h16' | exact rfl | exact trivial | apply And.intro)

/-- To the call of `malloc`: `n + 1` in `r12` and `rdi`. -/
theorem vc_19 {f : Rflags} :
    W_19 F Wl (fun j' g' _ V' => j' = 26 ∧ g' = { g with r12 := g.rax + 1#64, rdi := g.rax + 1#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_19, o1]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro)

/-- From `malloc`'s return with a block, not 0, to the jump to `memcpy`: the frame given back, the registers
popped, the arguments `(p, s, n + 1)`. -/
theorem vc_31 {f : Rflags} (hz : g.rax ≠ 0) (r16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (r8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_31 F Wl (fun j' g' _ V' => j' = 52 ∧
      g' = { g with
        rsp := g.rsp + 24#64, rdx := g.r12, rsi := g.rbp, rdi := g.rax, rbp := rdq(V, g.rsp + 8#64),
        r12 := rdq(V, g.rsp + 16#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have r16' : ∀ i < 8, Foot F.data (Addr.add (rsp + 8#64) i) := r16
  have r8' : ∀ i < 8, Foot F.data (Addr.add (rsp + 16#64) i) := r8
  have hz' : rax ≠ 0 := hz
  wpx [W_31, W_36, W_57, o2, o3, o4, BitVec.and_self, BitVec.setWidth_eq]
  try simp only [sdP16, sdP24]
  refine ⟨fun hc => absurd (by simpa using hc) hz', fun _ => ?_⟩
  all_goals repeat' (first | exact r16' | exact r8' | exact rfl | exact trivial | apply And.intro)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 1600000 in
/-- `__strdup (s)` for a string of `n < 1024` bytes not 0 and a 0, outside what `malloc` may change: `strlen`,
`malloc` and `memcpy` by their contracts (the PLT's `strlen` at `0x401108`, `malloc` at `0x633160`, the PLT's
`memcpy` at `0x401070`), the run reaches the return address with `rax` the block `p` `malloc` gave, the string's
bytes at `p`, the registers a call keeps as at the entry, the other bytes as `malloc` left them (`V₂`: below
`0x792a80` and above the stack pointer as at the entry), and `malloc`'s heap predicate for what follows. -/
theorem sdp_ok {fb : Addr} {hi k n : Nat} {pl pm pc : List Byte} {Pl Pc : (Addr → Byte) → Prop}
    {Pm : Nat → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hgf : GotF F) (hin : CodeIn L sdp_at sdp)
    (hil : CodeIn L 4198664#64 pl) (hl0 : 0 < pl.length) (hlen : Str.LenAt prof L o 4198664#64 Pl)
    (him : CodeIn L 6500704#64 pm) (hm0 : 0 < pm.length) (hmal : Mal.At prof F Wl L o fb hi 6500704#64 Pm)
    (hic : CodeIn L 4198512#64 pc) (hc0 : 0 < pc.length) (hcpy : Tls.CpyAt prof L o 4198512#64 Pc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sdp_at)
    (hdf : X.cpu.rflags.df = false)
    (hhi : hi + 248 ≤ X.cpu.gpr.rsp.toNat) (hs8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64)
    (hlo : 7940480 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (hstk : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hn : n < 1024) (hfit : X.cpu.gpr.rdi.toNat + n + 1 < 2 ^ 64)
    (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rdi i) ≠ 0) (hz : V (Addr.add X.cpu.gpr.rdi n) = 0)
    (hpg : ∀ x : Addr, X.cpu.gpr.rdi.toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ (X.cpu.gpr.rdi.toNat + n) / 4096 → Foot F.data x)
    (hsd : X.cpu.gpr.rdi.toNat + n + 1 ≤ 7940480 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hPl : ∀ W : Addr → Byte,
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → W a = V a) → Pl W)
    (hPm : ∀ W : Addr → Byte,
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → W a = V a) →
        Pm (k + 1) W)
    (hPc : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pc W)
    (kk : ∀ (Z : State) (t' : Nat) (W : Addr → Byte) (p : Addr) (V₂ : Addr → Byte), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 ≤ p.toNat → p.toNat + (n + 1) ≤ X.cpu.gpr.rsp.toNat - 32 →
      (∀ i < n + 1, W (Addr.add p i) = V (Addr.add X.cpu.gpr.rdi i)) →
      (∀ a : Addr, ¬ (p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + (n + 1)) → W a = V₂ a) →
      (∀ a : Addr, a.toNat < 7940480 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat → V₂ a = V a) →
      (∀ W' : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat - 32 →
        (a.toNat < p.toNat ∨ p.toNat + (n + 1) ≤ a.toNat) → W' a = V₂ a) → Pm k W') →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsl := X.cpu.gpr.rsp.isLt
  have hs32 : 32 ≤ X.cpu.gpr.rsp.toNat := by omega
  have h8 := sdT8 (x := X.cpu.gpr.rsp) (by omega)
  have h16 := sdT16 (x := X.cpu.gpr.rsp) (by omega)
  have h32 := sdT32 (x := X.cpu.gpr.rsp) hs32
  have sout : ∀ i ≤ n, ¬ (X.cpu.gpr.rsp.toNat - 32 ≤ (Addr.add X.cpu.gpr.rdi i).toNat ∧
      (Addr.add X.cpu.gpr.rdi i).toNat < X.cpu.gpr.rsp.toNat) := fun i hi => by
    rw [toNat_add_of_fits (n := n + 1) (by omega) (by omega)]
    omega
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (sdSlot hstk (by rw [h8]; omega) (by rw [h8]; omega))
      (sdSlot hstk (by rw [h16]; omega) (by rw [h16]; omega))) ?_
  rintro j' g₁ fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₁]
  -- the call of `strlen`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_14 _) hil hl0 (by decide) (fun i hi => ?_) ?_
  · rw [hsp₁, sdE32]
    exact sdSlot hstk (by rw [h32]; omega) (by rw [h32]; omega) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, sdE32] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁]; rfl
  refine hlen n c hgf hK₂ hA₂ hr₂ (hPl _ fun a ha => sdFr1 hs32 ha) hin (lt_len (show 19 < 64 by decide)) ?_
    (fun i hi => ?_) (by rw [hdi₂]; omega) (fun i hi => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [hsp₂, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [h32]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₂]
    exact c.hws _ (sdSlot hstk (by rw [h32]; omega) (by rw [h32]; omega) i hi)
  · rw [hdi₂, sdFr1 hs32 (sout i (by omega))]
    exact hnz i hi
  · rw [hdi₂, sdFr1 hs32 (sout n (Nat.le_refl _))]
    exact hz
  · rw [hdi₂] at h1 h2
    exact hpg x h1 h2
  intro Z₁ t₃ hKZ hAZ hrZ hspZ haxZ hbxZ hbpZ h12Z h13Z h14Z h15Z
  have esp : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hspZ, hsp₂]; exact sdA24 _
  -- to the call of `malloc`
  refine (c_19 prof).run c hin _ hKZ hAZ hrZ vc_19 ?_
  rintro j' g₃ fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₃]; exact esp
  refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_26 _) him hm0 (by decide) (fun i hi => ?_) ?_
  · rw [hsp₃, sdE32]
    exact sdSlot hstk (by rw [h32]; omega) (by rw [h32]; omega) i hi
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsp₃, sdE32] at hA₄ hg₄
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by rw [hg₄]; rfl
  have hdi₄ : Y₄.cpu.gpr.rdi = BitVec.ofNat 64 n + 1#64 := by
    rw [hg₄, hg₃]
    show Z₁.cpu.gpr.rax + 1#64 = _
    rw [haxZ]
  have edi : Y₄.cpu.gpr.rdi.toNat = n + 1 := by rw [hdi₄]; exact sdN1 hn
  -- `malloc (n + 1)`
  refine hmal c hK₄ hA₄ hr₄ (hPm _ fun a ha => sdFr2 hs32 ha) (by rw [edi]; omega) hfs (by rw [hsp₄, h32]; omega)
    (by rw [hsp₄, h32]; omega) (fun a h1 h2 => hstk a h1 (by rw [hsp₄, h32] at h2; omega)) hin (j := 31)
    (lt_len (by decide)) ?_ (fun i hi => ?_) ?_
  · rw [hsp₄, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [h32]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₄]
    exact c.hws _ (sdSlot hstk (by rw [h32]; omega) (by rw [h32]; omega) i hi)
  intro Zm t₆ V₅ p hKm hAm hrm hspm haxm hbxm hbpm h12m h13m h14m h15m hlo' hpe hWP hV₅ hPk _ hph _ _ _ _
  rw [edi] at hpe hWP hPk
  rw [hsp₄, h32] at hpe hV₅ hPk
  have hV : ∀ a : Addr, a.toNat < 7940480 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat → V₅ a = V a := fun a ha =>
    (hV₅ a (by omega)).trans (sdFr2 hs32 (by omega))
  have hp0 : p ≠ 0 := fun h => by
    rw [h] at hlo'
    exact absurd hlo' (by decide)
  have espm : Zm.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hspm, hsp₄]; exact sdA24 _
  -- to the jump
  refine (c_31 prof).run c hin _ hKm hAm hrm (vc_31 (by rw [haxm]; exact hp0) (fun i hi => ?_) (fun i hi => ?_)) ?_
  · rw [espm, sdA16]
    exact c.hws _ (sdSlot hstk (by rw [h16]; omega) (by rw [h16]; omega) i hi)
  · rw [espm, sdA8]
    exact c.hws _ (sdSlot hstk (by rw [h8]; omega) (by rw [h8]; omega) i hi)
  rintro j' g₅ fl V₆ ⟨rfl, rfl, rfl⟩ Y₅ t₇ hK₅ hA₅ hr₅ hg₅ -
  refine c.s_jmp_x hK₅ hA₅ hin (lt_len (by decide)) hr₅ (jmp_52 _) hic (tgt := 0) hc0 (by decide) ?_
  rintro Y₆ t₈ hK₆ hA₆ ⟨hr₆, hg₆⟩
  have g6 := hg₆.trans hg₅
  have r_sp : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [g6]
    show Zm.cpu.gpr.rsp + 24#64 = _
    rw [espm]
    exact sdA0 _
  have r_dx : Y₆.cpu.gpr.rdx = BitVec.ofNat 64 n + 1#64 := by
    rw [g6]
    show Zm.cpu.gpr.r12 = _
    rw [h12m, hg₄, hg₃]
    show Z₁.cpu.gpr.rax + 1#64 = _
    rw [haxZ]
  have r_si : Y₆.cpu.gpr.rsi = X.cpu.gpr.rdi := by
    rw [g6]
    show Zm.cpu.gpr.rbp = _
    rw [hbpm, hg₄, hg₃]
    show Z₁.cpu.gpr.rbp = _
    rw [hbpZ, hg₂, hg₁]
    rfl
  have r_di : Y₆.cpu.gpr.rdi = p := by
    rw [g6]
    exact haxm
  have r_bx : Y₆.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [g6]
    show Zm.cpu.gpr.rbx = _
    rw [hbxm, hg₄, hg₃]
    show Z₁.cpu.gpr.rbx = _
    rw [hbxZ, hg₂, hg₁]
    rfl
  have r_13 : Y₆.cpu.gpr.r13 = X.cpu.gpr.r13 := by
    rw [g6]
    show Zm.cpu.gpr.r13 = _
    rw [h13m, hg₄, hg₃]
    show Z₁.cpu.gpr.r13 = _
    rw [h13Z, hg₂, hg₁]
    rfl
  have r_14 : Y₆.cpu.gpr.r14 = X.cpu.gpr.r14 := by
    rw [g6]
    show Zm.cpu.gpr.r14 = _
    rw [h14m, hg₄, hg₃]
    show Z₁.cpu.gpr.r14 = _
    rw [h14Z, hg₂, hg₁]
    rfl
  have r_15 : Y₆.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [g6]
    show Zm.cpu.gpr.r15 = _
    rw [h15m, hg₄, hg₃]
    show Z₁.cpu.gpr.r15 = _
    rw [h15Z, hg₂, hg₁]
    rfl
  have rd5 : ∀ {x : Addr}, X.cpu.gpr.rsp.toNat - 24 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
      rdq(V₅, x) = rdq(Vst (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 32#64)
        (toBytesLE (sdp_at.add (14 + 5)) 8)) (X.cpu.gpr.rsp - 32#64) (toBytesLE (sdp_at.add (26 + 5)) 8), x) :=
    fun {x} h1 h2 => congrArg (ofBytesLE 64) (sdRd (P := fun a => X.cpu.gpr.rsp.toNat - 24 ≤ a.toNat)
      (fun a ha => hV₅ a (.inr (by omega))) fun i hi => by
        rw [toNat_add_of_fits (n := 8) hi h2]
        omega)
  have r_bp : Y₆.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [g6]
    show rdq(V₅, Zm.cpu.gpr.rsp + 8#64) = _
    rw [espm, sdA16, rd5 (by rw [h16]; omega) (by rw [h16]; omega)]
    exact sdRbp hs32
  have r_12 : Y₆.cpu.gpr.r12 = X.cpu.gpr.r12 := by
    rw [g6]
    show rdq(V₅, Zm.cpu.gpr.rsp + 16#64) = _
    rw [espm, sdA8, rd5 (by rw [h8]; omega) (by rw [h8]; omega)]
    exact sdR12 hs32
  have edx : Y₆.cpu.gpr.rdx.toNat = n + 1 := by rw [r_dx]; exact sdN1 hn
  -- `memcpy (p, s, n + 1)`
  refine hcpy c hgf hK₆ hA₆ (by rw [hr₆, addr_add_zero]) (hPc _ fun a ha => hV a (.inl ha)) hin₂ h₂ ?_
    (fun i hi => by rw [r_sp]; exact hl i hi) (fun i hi => ?_) (fun i hi => ?_) (by rw [r_si, edx]; omega)
    (by rw [r_di, edx]; omega) (by rw [r_si, r_di, edx]; omega) (by rw [r_di, r_sp, edx]; omega)
    (hK₆.df.trans (hK.df.symm.trans hdf)) (by rw [r_sp]; omega) ?_
  · rw [r_sp]
    refine (congrArg (ofBytesLE 64) (sdRd (P := fun a => X.cpu.gpr.rsp.toNat ≤ a.toNat)
      (fun a ha => hV a (.inr ha)) fun i hi => ?_)).trans hra
    rw [toNat_add_of_fits (n := 8) hi (by omega)]
    omega
  · rw [edx] at hi
    rw [r_si]
    have e := toNat_add_of_fits (a := X.cpu.gpr.rdi) (n := n + 1) hi (by omega)
    exact hpg _ (by rw [e]; exact Nat.div_le_div_right (by omega)) (by rw [e]; exact Nat.div_le_div_right (by omega))
  · rw [edx] at hi
    rw [r_di]
    have e := toNat_add_of_fits (a := p) (n := n + 1) hi (by omega)
    exact (hWP _ (by rw [e]; omega) (by rw [e]; omega)).1
  intro Z t' V₇ hKZ' hAZ' hrZ' hspZ' haxZ' hbxZ' hbpZ' h12Z' h13Z' h14Z' h15Z' hcp hout
  rw [edx, r_di, r_si] at hcp
  rw [edx, r_di] at hout
  refine kk Z t' V₇ p V₅ hKZ' hAZ' hrZ' (by rw [hspZ', r_sp]) (by rw [haxZ', r_di]) (by rw [hbxZ', r_bx])
    (by rw [hbpZ', r_bp]) (by rw [h12Z', r_12]) (by rw [h13Z', r_13]) (by rw [h14Z', r_14]) (by rw [h15Z', r_15])
    hph hpe (fun i hi => (hcp i hi).trans (hV _ ?_)) hout hV hPk
  rw [toNat_add_of_fits (n := n + 1) hi (by omega)]
  omega

end FV7z.Sdp
