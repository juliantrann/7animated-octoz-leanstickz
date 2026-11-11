import FV7z.Genv.Cuts
import FV7z.Sga.Holds
import FV7z.Startup.StrAt
import FV7z.Memcmp.Words
/-!
# `getenv` returns null when the environment has no such name (PLAN.md G3, startup)

glibc 2.31's `getenv` (`stdlib/getenv.c`) at `0x623070`, 224 bytes, as `_dl_non_dynamic_init` calls it seven times
(`LD_WARN`, `LD_LIBRARY_PATH`, …): for a name of two characters or more, it compares the name's first two characters
with each string's (a 16-bit `cmp`), then the rest with `strncmp`, then looks for `=`.

`strlen` and `strncmp` are reached through the PLT (IFUNC): the proof takes their contracts (`Str.LenAt`,
`Str.NcmpAt`) as hypotheses, as `__libc_setup_tls` takes `memcpy`'s.

- `frV`, `vc_0` … `vc_96`: the six cut blocks.
- `Par`, `InFr`, `Par.Ok`: what the function is given — the name (`n ≥ 2` characters), `__environ` and its `N`
  strings, the pages read, nothing of these in the 64 bytes of the frame, and `nom`: no string begins with the name
  and `=`.
- `Mem`: the bytes while the function runs (the entry's outside the frame, the saved registers in it).
- `Lp`: the registers in the loop. `fin` (the epilogue), `next` (to the next string), `loop` (induction over the
  strings left).
- `getenv_none`: from the entry to the return address, `rax` null, callee-saved registers kept (`Str.Back`), the
  bytes outside the frame those of the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Genv

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the six `push`es. -/
def frV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 16#64) (toBytesLE g.r14 8))
    (g.rsp - 24#64) (toBytesLE g.r13 8)) (g.rsp - 32#64) (toBytesLE g.r12 8)) (g.rsp - 40#64) (toBytesLE g.rbp 8))
    (g.rsp - 48#64) (toBytesLE g.rbx 8)

theorem s16 (x : BitVec 64) : x - 8 - 8 = x - 16#64 := by bv_omega
theorem s24 (x : BitVec 64) : x - 16#64 - 8 = x - 24#64 := by bv_omega
theorem s32 (x : BitVec 64) : x - 24#64 - 8 = x - 32#64 := by bv_omega
theorem s40 (x : BitVec 64) : x - 32#64 - 8 = x - 40#64 := by bv_omega
theorem s48 (x : BitVec 64) : x - 40#64 - 8 = x - 48#64 := by bv_omega
theorem s56 (x : BitVec 64) : x - 48#64 - 8#64 = x - 56#64 := by bv_omega

theorem a16 (x : BitVec 64) : x + 8#64 + 8 = x + 16#64 := by bv_omega
theorem a24 (x : BitVec 64) : x + 16#64 + 8 = x + 24#64 := by bv_omega
theorem a32 (x : BitVec 64) : x + 24#64 + 8 = x + 32#64 := by bv_omega
theorem a40 (x : BitVec 64) : x + 32#64 + 8 = x + 40#64 := by bv_omega
theorem a48 (x : BitVec 64) : x + 40#64 + 8 = x + 48#64 := by bv_omega
theorem a56 (x : BitVec 64) : x + 48#64 + 8 = x + 56#64 := by bv_omega

theorem sw8 (c : Byte) : BitVec.setWidth 8 (BitVec.setWidth 32 c) = c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := c.isLt
  omega

/-- The prologue, for a name of two characters or more and an environment: to the `call` of `strlen`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {envp p0 : BitVec 64} {c0 : Byte}
    (hst : ∀ i < 48, Foot Wl (Addr.add (g.rsp - 48#64) i)) (hsp : 48 ≤ g.rsp.toNat)
    (fe : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i)) (he : rdq(frV V g, 8013720#64) = envp) (he0 : envp ≠ 0)
    (f0 : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 1#64) i))
    (h0 : frV V g g.rdi = c0) (hc0 : c0 ≠ 0) (h1 : frV V g (g.rdi + 1#64) ≠ 0)
    (fp : ∀ i < 8, Foot F.data (Addr.add envp i)) (hp : rdq(frV V g, envp) = p0) :
    W_0 F Wl (fun j' g' _ V' => j' = 120 ∧
      g' = { g with rax := (c0.setWidth 32).setWidth 64, rbx := envp, rsp := g.rsp - 56#64, r12 := p0,
                    r13 := g.rdi } ∧
      V' = frV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold frV at he h0 h1 hp ⊢
  dsimp only at hst hsp he h0 h1 hp f0 f1 ⊢
  have w : ∀ (a : Addr) (k : Nat), k + 8 ≤ 48 → a.toNat = rsp.toNat - 48 + k → ∀ i < 8, Foot Wl (Addr.add a i) := by
    intro a k hk ha i hi
    have := hst (k + i) (by omega)
    rwa [show Addr.add (rsp - 48#64) (k + i) = Addr.add a i by simp only [Addr.add]; bv_omega] at this
  have w1 := w (rsp - 8) 40 (by omega) (by bv_omega)
  have w2 := w (rsp - 16#64) 32 (by omega) (by bv_omega)
  have w3 := w (rsp - 24#64) 24 (by omega) (by bv_omega)
  have w4 := w (rsp - 32#64) 16 (by omega) (by bv_omega)
  have w5 := w (rsp - 40#64) 8 (by omega) (by bv_omega)
  have w6 := w (rsp - 48#64) 0 (by omega) (by bv_omega)
  clear w hst
  wpx [W_0, W_34, W_48, o0, o1, o2, Op.push, Op.lda, Op.ldzx, Op.cmpmi, Op.ld]
  simp only [s16, s24, s32, s40, s48, s56]
  generalize Vst (Vst (Vst (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 16#64) (toBytesLE r14 8))
    (rsp - 24#64) (toBytesLE r13 8)) (rsp - 32#64) (toBytesLE r12 8)) (rsp - 40#64) (toBytesLE rbp 8))
    (rsp - 48#64) (toBytesLE rbx 8) = W at he h0 h1 hp ⊢
  simp only [he, hp, BitVec.and_self, Tun.rd1, h0, sw8]
  exact ⟨w1, w2, w3, w4, w5, w6, fe, fun af => ⟨fun h => absurd (beq_iff_eq.1 h) he0, fun _ => ⟨f0,
    fun h => absurd (beq_iff_eq.1 h) hc0, fun _ => ⟨f1, fp, fun _ => ⟨trivial, trivial⟩,
      fun h => absurd (by simpa using h) h1⟩⟩⟩⟩

/-- After `strlen`: the name's first two characters, its length, and the first string. -/
theorem vc_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f2 : ∀ i < 2, Foot F.data (Addr.add g.r13 i)) :
    W_125 F Wl (fun j' g' _ V' => (j' = 165 ∧ g.r12 ≠ 0 ∨ j' = 96 ∧ g.r12 = 0) ∧
      g' = { g with rbp := (rdw(V, g.r13).setWidth 32).setWidth 64, r13 := g.r13 + 2#64, r14 := g.rax,
                    r15 := g.rax - 2#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f2 ⊢
  have e1 : r13 + 2#64 + 18446744073709551614#64 = r13 := by bv_omega
  have e2 : rax + 18446744073709551614#64 = rax - 2#64 := by bv_omega
  wpx [W_125, W_146, o4, Op.ldzx, Op.lea]
  simp only [e1, e2, BitVec.and_self]
  exact ⟨f2, fun h => ⟨.inl (by simpa using h), trivial⟩, fun h => ⟨.inr (by simpa using h), trivial⟩⟩

/-- A string of the environment: its first two characters are not the name's, or they are (to the `call` of
`strncmp`). -/
theorem vc_165 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f2 : ∀ i < 2, Foot F.data (Addr.add g.r12 i)) :
    W_165 F Wl (fun j' g' _ V' => V' = V ∧ (j' = 152 ∧ g' = g ∧ g.rbp.setWidth 16 ≠ rdw(V, g.r12) ∨
      j' = 183 ∧ g.rbp.setWidth 16 = rdw(V, g.r12) ∧
        g' = { g with rdi := g.r12 + 2#64, rdx := g.r15, rsi := g.r13 })) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f2 ⊢
  wpx [W_165, W_172, o6, o7, Op.cmpm, Op.lea]
  exact ⟨f2, fun h => .inl (by simpa using h), fun h => .inr (by simpa using h)⟩

/-- After `strncmp`: not 0, or the string's next character is not `=`. -/
theorem vc_188 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : g.rax.setWidth 32 ≠ 0#32 ∨
      (∀ i < 1, Foot F.data (Addr.add (g.r12 + g.r14) i)) ∧ V (g.r12 + g.r14) ≠ 61#8) :
    W_188 F Wl (fun j' g' _ V' => j' = 152 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_188, W_192, o8, o9, Op.cmpmi]
  refine ⟨fun _ => trivial, fun h1 => ?_⟩
  rcases h with h | ⟨hf, hv⟩
  · exact absurd (by simpa using h1) h
  · exact ⟨hf, fun _ => trivial, fun h2 => absurd (by simpa [Tun.rd1] using h2) hv⟩

/-- The next string of the environment, `p` its address. -/
theorem vc_152 {g : Gprs} {f : Rflags} {V : Addr → Byte} {p : BitVec 64}
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i)) (hp : rdq(V, g.rbx + 8#64) = p) :
    W_152 F Wl (fun j' g' _ V' => (j' = 165 ∧ p ≠ 0 ∨ j' = 96 ∧ p = 0) ∧
      g' = { g with rbx := g.rbx + 8#64, r12 := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 hp ⊢
  wpx [W_152, o5, Op.ld]
  simp only [hp, BitVec.and_self]
  exact ⟨f8, fun h => ⟨.inr (by simpa using h), trivial⟩, fun h => ⟨.inl (by simpa using h), trivial⟩⟩

/-- The epilogue. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 48, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 113 ∧
      g' = { g with rax := g.r12, rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 16#64),
                    r12 := rdq(V, g.rsp + 24#64), r13 := rdq(V, g.rsp + 32#64), r14 := rdq(V, g.rsp + 40#64),
                    r15 := rdq(V, g.rsp + 48#64), rsp := g.rsp + 56#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  have w : ∀ (a : Addr) (k : Nat), k + 8 ≤ 48 → a.toNat = (rsp.toNat + 8 + k) % 2 ^ 64 →
      ∀ i < 8, Foot F.data (Addr.add a i) := by
    intro a k hk ha i hi
    have := hl (k + i) (by omega)
    rwa [show Addr.add (rsp + 8#64) (k + i) = Addr.add a i by simp only [Addr.add]; bv_omega] at this
  have w1 := w (rsp + 8#64) 0 (by omega) (by bv_omega)
  have w2 := w (rsp + 16#64) 8 (by omega) (by bv_omega)
  have w3 := w (rsp + 24#64) 16 (by omega) (by bv_omega)
  have w4 := w (rsp + 32#64) 24 (by omega) (by bv_omega)
  have w5 := w (rsp + 40#64) 32 (by omega) (by bv_omega)
  have w6 := w (rsp + 48#64) 40 (by omega) (by bv_omega)
  clear w hl
  wpx [W_96, o3, Op.pop]
  simp only [a16, a24, a32, a40, a48, a56]
  exact ⟨w1, w2, w3, w4, w5, w6, trivial⟩

/-! ## The `call`s and the `ret` -/

def pc120 : List Byte := [0xe8, 0x1b, 0xe0, 0xdd, 0xff]
def pc183 : List Byte := [0xe8, 0x1c, 0xdf, 0xdd, 0xff]
def pret : List Byte := [0xc3]
theorem pc120_0 : ∀ feat, Dec feat pc120 0 (FV7z.mk .call 64 [.rel 18446744073707315227] 5) := by dec_rfl
theorem pc183_0 : ∀ feat, Dec feat pc183 0 (FV7z.mk .call 64 [.rel 18446744073707314972] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc120 : pc120 <+: gev.drop 120 := by decide +kernel
theorem wc183 : pc183 <+: gev.drop 183 := by decide +kernel
theorem w_113 : pret <+: gev.drop 113 := by decide +kernel
theorem call_120 (feat : Features) : Dec feat gev 120 (FV7z.mk .call 64 [.rel 18446744073707315227] 5) :=
  Dec.shift (j := 120) (k := 0) (pc120_0 feat) wc120 (Nat.zero_le _)
theorem call_183 (feat : Features) : Dec feat gev 183 (FV7z.mk .call 64 [.rel 18446744073707314972] 5) :=
  Dec.shift (j := 183) (k := 0) (pc183_0 feat) wc183 (Nat.zero_le _)
theorem ret_113 (feat : Features) : Dec feat gev 113 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 113) (k := 0) (pret_0 feat) w_113 (Nat.zero_le _)

/-! ## What the function is given -/

/-- What `getenv` is given: the registers `g` (`rdi` the name) and the bytes `V` at the entry, the name's length
`n`, the environment's array `envp` of `N` strings, their addresses and lengths. -/
structure Par where
  g : Gprs
  V : Addr → Byte
  n : Nat
  envp : Addr
  N : Nat
  ptr : Nat → Addr
  len : Nat → Nat

/-- A byte of the function's frame: the 64 bytes below the stack pointer of the entry. -/
def InFr (P : Par) (a : Addr) : Prop := P.g.rsp.toNat - 64 ≤ a.toNat ∧ a.toNat < P.g.rsp.toNat

/-- What `getenv` needs: 64 bytes of stack; `__environ` (`0x7a4798`) is `envp`, not null; the name has `n ≥ 2`
characters and a 0, its pages read; `envp` has the `N` strings' addresses and a null; each string has `len i`
characters and a 0, its pages and the byte after its first read; none of these is in the frame; and no string begins
with the name and `=`. -/
structure Par.Ok (P : Par) (F : Footprint) (Wl : List Rgn) : Prop where
  hsp : 64 ≤ P.g.rsp.toNat
  stk : ∀ i < 64, Foot Wl (Addr.add (P.g.rsp - 64#64) i)
  ret : ∀ i < 8, Foot F.data (Addr.add P.g.rsp i)
  top : P.g.rsp.toNat + 8 ≤ 2 ^ 64
  fe : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i)
  oe : ∀ i < 8, ¬ InFr P (Addr.add 8013720#64 i)
  he : rdq(P.V, 8013720#64) = P.envp
  he0 : P.envp ≠ 0
  hn : 2 ≤ P.n
  nfit : P.g.rdi.toNat + P.n < 2 ^ 64
  nnz : ∀ k < P.n, P.V (Addr.add P.g.rdi k) ≠ 0
  nz : P.V (Addr.add P.g.rdi P.n) = 0
  npg : ∀ x : Addr, P.g.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (P.g.rdi.toNat + P.n) / 4096 →
    Foot F.data x
  nout : ∀ k ≤ P.n, ¬ InFr P (Addr.add P.g.rdi k)
  efit : P.envp.toNat + 8 * (P.N + 1) ≤ 2 ^ 64
  erd : ∀ k < 8 * (P.N + 1), Foot F.data (Addr.add P.envp k)
  eout : ∀ k < 8 * (P.N + 1), ¬ InFr P (Addr.add P.envp k)
  eptr : ∀ i ≤ P.N, rdq(P.V, Addr.add P.envp (8 * i)) = P.ptr i
  enz : ∀ i < P.N, P.ptr i ≠ 0
  eend : P.ptr P.N = 0
  sfit : ∀ i < P.N, (P.ptr i).toNat + P.len i + 2 ≤ 2 ^ 64
  sz : ∀ i < P.N, P.V (Addr.add (P.ptr i) (P.len i)) = 0
  spg : ∀ i < P.N, ∀ x : Addr, (P.ptr i).toNat / 4096 ≤ x.toNat / 4096 →
    x.toNat / 4096 ≤ ((P.ptr i).toNat + P.len i) / 4096 → Foot F.data x
  s2 : ∀ i < P.N, Foot F.data (Addr.add (P.ptr i) 1)
  sout : ∀ i < P.N, ∀ k ≤ P.len i + 1, ¬ InFr P (Addr.add (P.ptr i) k)
  nom : ∀ i < P.N, (∀ k < P.n, P.V (Addr.add (P.ptr i) k) = P.V (Addr.add P.g.rdi k)) →
    P.V (Addr.add (P.ptr i) P.n) ≠ 61#8

/-- The bytes while the function runs: those of the entry outside the frame, the six saved registers in it. -/
structure Mem (P : Par) (W : Addr → Byte) : Prop where
  out : ∀ a, ¬ InFr P a → W a = P.V a
  s15 : rdq(W, P.g.rsp - 8) = P.g.r15
  s14 : rdq(W, P.g.rsp - 16#64) = P.g.r14
  s13 : rdq(W, P.g.rsp - 24#64) = P.g.r13
  s12 : rdq(W, P.g.rsp - 32#64) = P.g.r12
  sbp : rdq(W, P.g.rsp - 40#64) = P.g.rbp
  sbx : rdq(W, P.g.rsp - 48#64) = P.g.rbx

variable {P : Par} {W : Addr → Byte}

/-- After the `push`es. -/
theorem mem_fr (hsp : 64 ≤ P.g.rsp.toNat) : Mem P (frV P.V P.g) := by
  have hlt := P.g.rsp.isLt
  have q : ∀ v : BitVec 64, ofBytesLE 64 (toBytesLE v 8) = v := fun v => ofBytesLE_toBytesLE (w := 64) (n := 8) rfl v
  unfold frV
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold InFr at ha
    rw [vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega), vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega),
      vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega), vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega),
      vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega), vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega)]
  · rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega), q]
  · rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega), q]
  · rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega), q]
  · rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega), q]
  · rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega), q]
  · rw [vs (toBytesLE_length _ _) (by bv_omega), q]

/-- With the return address of a call. -/
theorem Mem.call (hM : Mem P W) (hsp : 64 ≤ P.g.rsp.toNat) {bs : List Byte} (hl : bs.length = 8) :
    Mem P (Vst W (P.g.rsp - 64#64) bs) := by
  have hlt := P.g.rsp.isLt
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold InFr at ha
    rw [vo hl (by bv_omega) (by bv_omega)]
    exact hM.out a (by unfold InFr; exact ha)
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.s15
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.s14
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.s13
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.s12
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.sbp
  · rw [vr hl (by bv_omega) (by bv_omega) (by bv_omega)]
    exact hM.sbx

/-- Bytes outside the frame are those of the entry. -/
theorem Mem.rd (hM : Mem P W) {x : Addr} {n : Nat} (hx : ∀ i < n, ¬ InFr P (Addr.add x i)) :
    List.map W (byteAddrs x n) = List.map P.V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  exact hM.out _ (hx i hi)

/-- Two words of 16 bits are equal: so are their bytes. -/
theorem w2_inj {V V' : Addr → Byte} {a b : Addr} (h : rdw(V, a) = rdw(V', b)) :
    V (Addr.add a 0) = V' (Addr.add b 0) ∧ V (Addr.add a 1) = V' (Addr.add b 1) := by
  have h' : toBytesLE rdw(V, a) 2 = toBytesLE rdw(V', b) 2 := congrArg (fun v => toBytesLE v 2) h
  rw [Order.toBytesLE_ofBytesLE (by simp [byteAddrs]) (by decide),
    Order.toBytesLE_ofBytesLE (by simp [byteAddrs]) (by decide)] at h'
  have h2 : [V (Addr.add a 0), V (Addr.add a 1)] = [V' (Addr.add b 0), V' (Addr.add b 1)] := h'
  injection h2 with h1 h2
  injection h2 with h2 _
  exact ⟨h1, h2⟩

theorem sw16 (x : BitVec 16) : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

/-- The registers in the loop, at the environment's string `i`. -/
def Lp (P : Par) (i : Nat) (g : Gprs) : Prop :=
  g.rsp = P.g.rsp - 56#64 ∧ g.rbx = Addr.add P.envp (8 * i) ∧ g.r12 = P.ptr i ∧
    g.rbp.setWidth 16 = rdw(P.V, P.g.rdi) ∧ g.r13 = P.g.rdi + 2#64 ∧ g.r14 = BitVec.ofNat 64 P.n ∧
    g.r15 = BitVec.ofNat 64 P.n - 2#64

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {ev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Pm : (Addr → Byte) → Prop}

/-- From the epilogue (96) with `r12` null: the `ret`, `rax` null. -/
theorem fin {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gev_at gev)
    (hO : P.Ok F Wl) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(P.V, P.g.rsp) = e₂.add j₂)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → (∀ a, ¬ InFr P a → W a = P.V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 → Str.Back P.g Z.cpu.gpr → GoG prof L o ev gP gE Z t')
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Mem P W)
    (hrip : X.cpu.rip = gev_at.add 96) (hsp : X.cpu.gpr.rsp = P.g.rsp - 56#64) (h12 : X.cpu.gpr.r12 = 0) :
    GoG prof L o ev gP gE X t := by
  have hlt := P.g.rsp.isLt
  have h64 := hO.hsp
  have htop := hO.top
  refine (c_96 prof).run c hin _ hK hA hrip (vc_96 fun i hi => ?_) ?_
  · rw [hsp]
    have := hO.stk (16 + i) (by omega)
    rw [show Addr.add (P.g.rsp - 64#64) (16 + i) = Addr.add (P.g.rsp - 56#64 + 8#64) i by
      simp only [Addr.add]; bv_omega] at this
    exact c.hws _ this
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hspY : Y.cpu.gpr.rsp = P.g.rsp := by
    rw [hgY]
    show X.cpu.gpr.rsp + 56#64 = _
    rw [hsp]
    bv_omega
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_113 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hspY]
    exact hO.ret i hi
  · rw [hspY, hM.rd fun i hi => ?_]
    · exact hret
    · unfold InFr
      simp only [Addr.add]
      bv_omega
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  have e8 : X.cpu.gpr.rsp + 8#64 = P.g.rsp - 48#64 := by rw [hsp]; bv_omega
  have e16 : X.cpu.gpr.rsp + 16#64 = P.g.rsp - 40#64 := by rw [hsp]; bv_omega
  have e24 : X.cpu.gpr.rsp + 24#64 = P.g.rsp - 32#64 := by rw [hsp]; bv_omega
  have e32 : X.cpu.gpr.rsp + 32#64 = P.g.rsp - 24#64 := by rw [hsp]; bv_omega
  have e40 : X.cpu.gpr.rsp + 40#64 = P.g.rsp - 16#64 := by rw [hsp]; bv_omega
  have e48 : X.cpu.gpr.rsp + 48#64 = P.g.rsp - 8 := by rw [hsp]; bv_omega
  refine k Z t'' V' hKZ hAZ hM.out hrZ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgZ, hgY]
    exact h12
  · rw [hgZ, hspY]
    rfl
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 8#64) = _
    rw [e8, hM.sbx]
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 16#64) = _
    rw [e16, hM.sbp]
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 24#64) = _
    rw [e24, hM.s12]
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 32#64) = _
    rw [e32, hM.s13]
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 40#64) = _
    rw [e40, hM.s14]
  · rw [hgZ, hgY]
    show rdq(V', X.cpu.gpr.rsp + 48#64) = _
    rw [e48, hM.s15]

/-- From 152 at the string `i`: the next string, or the end. -/
theorem next (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gev_at gev) (hO : P.Ok F Wl) {i : Nat}
    (ih : ∀ (X : State) (t : Nat) (W : Addr → Byte), i + 1 < P.N → KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      Mem P W → X.cpu.rip = gev_at.add 165 → Lp P (i + 1) X.cpu.gpr → GoG prof L o ev gP gE X t)
    (kx : ∀ (X : State) (t : Nat) (W : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem W → Mem P W →
      X.cpu.rip = gev_at.add 96 → X.cpu.gpr.rsp = P.g.rsp - 56#64 → X.cpu.gpr.r12 = 0 →
      GoG prof L o ev gP gE X t)
    {X : State} {t : Nat} (hi : i < P.N) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Mem P W)
    (hrip : X.cpu.rip = gev_at.add 152) (hL : Lp P i X.cpu.gpr) : GoG prof L o ev gP gE X t := by
  obtain ⟨hsp, hbx, h12, hbp, h13, h14, h15⟩ := hL
  have hef := hO.efit
  have ea : X.cpu.gpr.rbx + 8#64 = Addr.add P.envp (8 * (i + 1)) := by
    rw [hbx]
    simp only [Addr.add]
    bv_omega
  have eb : ∀ k, Addr.add (Addr.add P.envp (8 * (i + 1))) k = Addr.add P.envp (8 * (i + 1) + k) := fun k => by
    simp only [Addr.add]
    bv_omega
  have hp : rdq(W, X.cpu.gpr.rbx + 8#64) = P.ptr (i + 1) := by
    rw [ea, hM.rd fun k hk => ?_]
    · exact hO.eptr (i + 1) (by omega)
    · rw [eb]
      exact hO.eout _ (by omega)
  refine (c_152 prof).run c hin _ hK hA hrip (vc_152 (fun k hk => ?_) hp) ?_
  · rw [ea, eb]
    exact hO.erd _ (by omega)
  rintro j' g fl V' ⟨hj, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hL' : Lp P (i + 1) Y.cpu.gpr := by
    rw [hgY]
    exact ⟨hsp, ea, rfl, hbp, h13, h14, h15⟩
  rcases hj with ⟨rfl, hne⟩ | ⟨rfl, h0⟩
  · have hlt : i + 1 < P.N := by
      rcases Nat.lt_or_ge (i + 1) P.N with h | h
      · exact h
      · have e : i + 1 = P.N := by omega
        exact absurd (e ▸ hO.eend) hne
    exact ih Y t' V' hlt hKY hAY hM hrY hL'
  · exact kx Y t' V' hKY hAY hM hrY (by rw [hgY]; exact hsp) (by rw [hgY]; exact h0)

set_option maxHeartbeats 1600000 in
/-- The loop over the environment's strings, from 165 at the string `i`: none begins with the name and `=`, so the
epilogue is reached with `r12` null. -/
theorem loop {pc : List Byte} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gev_at gev)
    (hic : CodeIn L 4198472#64 pc) (hc0 : 0 < pc.length) (hcmp : Str.NcmpAt prof L o 4198472#64 Pm)
    (hO : P.Ok F Wl) (hPm : ∀ W, (∀ a, ¬ InFr P a → W a = P.V a) → Pm W)
    (kx : ∀ (X : State) (t : Nat) (W : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem W → Mem P W →
      X.cpu.rip = gev_at.add 96 → X.cpu.gpr.rsp = P.g.rsp - 56#64 → X.cpu.gpr.r12 = 0 →
      GoG prof L o ev gP gE X t) :
    ∀ (d i : Nat), P.N - i = d → i < P.N → ∀ (X : State) (t : Nat) (W : Addr → Byte), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem W → Mem P W → X.cpu.rip = gev_at.add 165 → Lp P i X.cpu.gpr →
      GoG prof L o ev gP gE X t := by
  intro d
  induction d with
  | zero =>
    intro i hd hi
    omega
  | succ d ih =>
    intro i hd hi X t W hK hA hM hrip hL
    have nx : ∀ (X : State) (t : Nat) (W : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem W → Mem P W →
        X.cpu.rip = gev_at.add 152 → Lp P i X.cpu.gpr → GoG prof L o ev gP gE X t :=
      fun X t W hK hA hM hr hL =>
        next c hin hO (fun X t W hlt => ih (i + 1) (by omega) hlt X t W) kx hi hK hA hM hr hL
    obtain ⟨hsp, hbx, h12, hbp, h13, h14, h15⟩ := id hL
    have hsf := hO.sfit i hi
    have hnf := hO.nfit
    have hn2 := hO.hn
    have h64 := hO.hsp
    have hlt := P.g.rsp.isLt
    have f2 : ∀ k < 2, Foot F.data (Addr.add X.cpu.gpr.r12 k) := by
      intro k hk
      rw [h12]
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · rw [addr_add_zero]
        exact hO.spg i hi _ (Nat.le_refl _) (Nat.div_le_div_right (by omega))
      · exact hO.s2 i hi
    refine (c_165 prof).run c hin _ hK hA hrip (vc_165 f2) ?_
    rintro j' g fl V' ⟨rfl, hj⟩ Y t₁ hKY hAY hrY hgY -
    rcases hj with ⟨rfl, rfl, -⟩ | ⟨rfl, heq, rfl⟩
    · exact nx Y t₁ V' hKY hAY hM hrY (by rw [hgY]; exact hL)
    -- the `call` of `strncmp`
    have hspY : Y.cpu.gpr.rsp = P.g.rsp - 56#64 := by rw [hgY]; exact hsp
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_183 _) hic hc0 (by decide) (fun k hk => ?_) ?_
    · rw [hspY, show P.g.rsp - 56#64 - 8 = P.g.rsp - 64#64 by bv_omega]
      exact hO.stk k (by omega)
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hspY, show P.g.rsp - 56#64 - 8 = P.g.rsp - 64#64 by bv_omega] at hA₂ hg₂
    have hM₂ := hM.call h64 (bs := toBytesLE (gev_at.add (183 + 5)) 8) (toBytesLE_length _ _)
    have hdi : Y₂.cpu.gpr.rdi = P.ptr i + 2#64 := by rw [hg₂, hgY]; exact congrArg (· + 2#64) h12
    have hsi : Y₂.cpu.gpr.rsi = P.g.rdi + 2#64 := by rw [hg₂, hgY]; exact h13
    have hdx : Y₂.cpu.gpr.rdx = BitVec.ofNat 64 P.n - 2#64 := by rw [hg₂, hgY]; exact h15
    have hsp₂ : Y₂.cpu.gpr.rsp = P.g.rsp - 64#64 := by rw [hg₂]; rfl
    -- the first two characters are the name's
    have hw : rdw(P.V, P.ptr i) = rdw(P.V, P.g.rdi) := by
      rw [← hbp, heq, h12, hM.rd (n := 2) fun k hk => hO.sout i hi k (by omega)]
    have h01 := w2_inj hw
    have key : ∀ m ≤ P.n - 2, (∀ k < m, P.V (Addr.add (P.ptr i) (2 + k)) = P.V (Addr.add P.g.rdi (2 + k))) →
        ∀ k < 2 + m, P.V (Addr.add (P.ptr i) k) = P.V (Addr.add P.g.rdi k) := by
      intro m hm h k hk
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | h2
      · exact h01.1
      · exact h01.2
      · have := h (k - 2) (by omega)
        rwa [show 2 + (k - 2) = k by omega] at this
    have lenge : ∀ j ≤ P.n, (∀ k < j, P.V (Addr.add (P.ptr i) k) = P.V (Addr.add P.g.rdi k)) → j ≤ P.len i := by
      intro j hj h
      rcases Nat.lt_or_ge (P.len i) j with hl | hge
      · exact absurd (hO.sz i hi) (by rw [h _ hl]; exact hO.nnz _ (by omega))
      · exact hge
    have vW : ∀ k ≤ P.len i + 1, Vst V' (P.g.rsp - 64#64) (toBytesLE (gev_at.add (183 + 5)) 8)
        (Addr.add (P.ptr i) k) = P.V (Addr.add (P.ptr i) k) := fun k hk => hM₂.out _ (hO.sout i hi k hk)
    have vN : ∀ k ≤ P.n, Vst V' (P.g.rsp - 64#64) (toBytesLE (gev_at.add (183 + 5)) 8) (Addr.add P.g.rdi k) =
        P.V (Addr.add P.g.rdi k) := fun k hk => hM₂.out _ (hO.nout k hk)
    -- after `strncmp`: to the next string
    have aft : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
        Agree F Z.proc.mm.mem (Vst V' (P.g.rsp - 64#64) (toBytesLE (gev_at.add (183 + 5)) 8)) →
        Z.cpu.rip = gev_at.add 188 → Lp P i Z.cpu.gpr →
        (Z.cpu.gpr.rax.setWidth 32 ≠ 0#32 ∨ (∀ k < P.n, P.V (Addr.add (P.ptr i) k) = P.V (Addr.add P.g.rdi k))) →
        GoG prof L o ev gP gE Z t' := by
      intro Z t' hKZ hAZ hrZ hLZ hor
      obtain ⟨-, -, h12Z, -, -, h14Z, -⟩ := id hLZ
      have e : Z.cpu.gpr.r12 + Z.cpu.gpr.r14 = Addr.add (P.ptr i) P.n := by rw [h12Z, h14Z]; rfl
      refine (c_188 prof).run c hin _ hKZ hAZ hrZ (vc_188 ?_) ?_
      · rcases hor with h | h
        · exact .inl h
        · have hlen : P.n ≤ P.len i := lenge P.n (Nat.le_refl _) h
          refine .inr ⟨fun k hk => ?_, ?_⟩
          · obtain rfl : k = 0 := by omega
            rw [addr_add_zero, e]
            refine hO.spg i hi _ ?_ ?_
            · rw [toNat_add_of_fits (n := P.len i + 1) (by omega) (by omega)]
              exact Nat.div_le_div_right (by omega)
            · rw [toNat_add_of_fits (n := P.len i + 1) (by omega) (by omega)]
              exact Nat.div_le_div_right (by omega)
          · rw [e, vW _ (by omega)]
            exact hO.nom i hi h
      rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
      exact nx Y₃ t₃ _ hK₃ hA₃ hM₂ hr₃ (by rw [hg₃]; exact hLZ)
    -- `strncmp` with the first `m` characters equal
    have callc : ∀ m ≤ P.n - 2,
        (∀ k < m, P.V (Addr.add (P.ptr i) (2 + k)) = P.V (Addr.add P.g.rdi (2 + k))) →
        (m = P.n - 2 ∨ m < P.n - 2 ∧ P.V (Addr.add (P.ptr i) (2 + m)) ≠ P.V (Addr.add P.g.rdi (2 + m))) →
        GoG prof L o ev gP gE Y₂ t₂ := by
      intro m hm hpre hcase
      have hk2 := key m hm hpre
      have hlen := lenge (2 + m) (by omega) hk2
      have hdxn : Y₂.cpu.gpr.rdx.toNat = P.n - 2 := by rw [hdx]; bv_omega
      have edi : Y₂.cpu.gpr.rdi.toNat = (P.ptr i).toNat + 2 := by rw [hdi]; bv_omega
      have esi : Y₂.cpu.gpr.rsi.toNat = P.g.rdi.toNat + 2 := by rw [hsi]; bv_omega
      have adi : ∀ k, Addr.add Y₂.cpu.gpr.rdi k = Addr.add (P.ptr i) (2 + k) := fun k => by
        rw [hdi]
        simp only [Addr.add]
        bv_omega
      have asi : ∀ k, Addr.add Y₂.cpu.gpr.rsi k = Addr.add P.g.rdi (2 + k) := fun k => by
        rw [hsi]
        simp only [Addr.add]
        bv_omega
      refine hcmp m c hK₂ hA₂ hr₂ (hPm _ hM₂.out) hin (lt_len (show 188 < 224 by decide)) ?_ (fun k hk => ?_)
        (by omega) (by omega) (by omega) (fun k hk => ?_) (fun x k hk hkd hx => ?_) ?_
      · rw [hsp₂, vs (toBytesLE_length _ _) (by bv_omega)]
        exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
      · rw [hsp₂]
        exact c.hws _ (hO.stk k (by omega))
      · rw [adi, asi, vW _ (by omega), vN _ (by omega)]
        exact ⟨hpre k hk, by rw [hpre k hk]; exact hO.nnz _ (by omega)⟩
      · rcases hx with hx | hx
        · rw [edi] at hx
          exact hO.spg i hi x (by rw [hx]; exact Nat.div_le_div_right (by omega))
            (by rw [hx]; exact Nat.div_le_div_right (by omega))
        · rw [esi] at hx
          exact hO.npg x (by rw [hx]; exact Nat.div_le_div_right (by omega))
            (by rw [hx]; exact Nat.div_le_div_right (by omega))
      · intro Z t' hKZ hAZ hrZ hspZ _ _ r3 hbxZ hbpZ h12Z h13Z h14Z h15Z
        have hLZ : Lp P i Z.cpu.gpr := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hspZ, hsp₂]
            bv_omega
          · rw [hbxZ, hg₂, hgY]
            exact hbx
          · rw [h12Z, hg₂, hgY]
            exact h12
          · rw [hbpZ, hg₂, hgY]
            exact hbp
          · rw [h13Z, hg₂, hgY]
            exact h13
          · rw [h14Z, hg₂, hgY]
            exact h14
          · rw [h15Z, hg₂, hgY]
            exact h15
        refine aft Z t' hKZ hAZ hrZ hLZ ?_
        rcases hcase with rfl | ⟨hlt, hne⟩
        · exact .inr fun k hk => hk2 k (by omega)
        · refine .inl (r3 (by rw [hdxn]; omega) ?_)
          rw [adi, asi, vW _ (by omega), vN _ (by omega)]
          exact hne
    rcases Str.first_not (fun k => P.V (Addr.add (P.ptr i) (2 + k)) = P.V (Addr.add P.g.rdi (2 + k))) (P.n - 2)
      with hall | ⟨m, hm, hpre, hdiff⟩
    · exact callc (P.n - 2) (Nat.le_refl _) hall (.inl rfl)
    · exact callc m (Nat.le_of_lt hm) hpre (.inr ⟨hm, hdiff⟩)

set_option maxHeartbeats 1600000 in
/-- `getenv (name)` when no string of the environment begins with the name and `=`: from the entry to the return
address with `rax` null, the callee-saved registers and the bytes outside the frame kept. `strlen` and `strncmp`
(through the PLT) by their contracts. -/
theorem getenv_none {pl pc : List Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {X : State} {t : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gev_at gev)
    (hil : CodeIn L 4198664#64 pl) (hl0 : 0 < pl.length) (hlen : Str.LenAt prof L o 4198664#64 Pm)
    (hic : CodeIn L 4198472#64 pc) (hc0 : 0 < pc.length) (hcmp : Str.NcmpAt prof L o 4198472#64 Pm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem P.V) (hrip : X.cpu.rip = gev_at) (hg : X.cpu.gpr = P.g)
    (hO : P.Ok F Wl) (hPm : ∀ W, (∀ a, ¬ InFr P a → W a = P.V a) → Pm W)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(P.V, P.g.rsp) = e₂.add j₂)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → (∀ a, ¬ InFr P a → W a = P.V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 → Str.Back P.g Z.cpu.gpr → GoG prof L o ev gP gE Z t') :
    GoG prof L o ev gP gE X t := by
  have h64 := hO.hsp
  have hlt := P.g.rsp.isLt
  have hnf := hO.nfit
  have hn2 := hO.hn
  have hM0 : Mem P (frV P.V P.g) := mem_fr h64
  have kx : ∀ (X : State) (t : Nat) (W : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem W → Mem P W →
      X.cpu.rip = gev_at.add 96 → X.cpu.gpr.rsp = P.g.rsp - 56#64 → X.cpu.gpr.r12 = 0 →
      GoG prof L o ev gP gE X t :=
    fun X t W hK hA hM hr hs h12 => fin c hin hO hin₂ h₂ hret k hK hA hM hr hs h12
  have nfoot : ∀ k ≤ P.n, Foot F.data (Addr.add P.g.rdi k) := fun k hk =>
    hO.npg _ (by rw [toNat_add_of_fits (n := P.n + 1) (by omega) (by omega)]; exact Nat.div_le_div_right (by omega))
      (by rw [toNat_add_of_fits (n := P.n + 1) (by omega) (by omega)]; exact Nat.div_le_div_right (by omega))
  have vc := vc_0 (F := F) (Wl := Wl) (g := P.g) (f := X.cpu.rflags) (V := P.V) (envp := P.envp) (p0 := P.ptr 0)
    (c0 := P.V P.g.rdi)
    (fun i hi => by
      have := hO.stk (16 + i) (by omega)
      rwa [show Addr.add (P.g.rsp - 64#64) (16 + i) = Addr.add (P.g.rsp - 48#64) i by
        simp only [Addr.add]; bv_omega] at this)
    (by omega) hO.fe (by rw [hM0.rd hO.oe]; exact hO.he) hO.he0
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact nfoot 0 (by omega))
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero]
      exact nfoot 1 (by omega))
    (by
      have := hM0.out _ (hO.nout 0 (Nat.zero_le _))
      rwa [addr_add_zero] at this)
    (by
      have := hO.nnz 0 (by omega)
      rwa [addr_add_zero] at this)
    (by
      have := hM0.out _ (hO.nout 1 (by omega))
      have e : frV P.V P.g (P.g.rdi + 1#64) = P.V (Addr.add P.g.rdi 1) := this
      rw [e]
      exact hO.nnz 1 (by omega))
    (fun i hi => hO.erd i (by omega))
    (by
      rw [hM0.rd fun i hi => hO.eout i (by omega)]
      have := hO.eptr 0 (Nat.zero_le _)
      rwa [Nat.mul_zero, addr_add_zero] at this)
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (by rw [hg]; exact vc) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  -- the `call` of `strlen`
  have hspY : Y.cpu.gpr.rsp = P.g.rsp - 56#64 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_120 _) hil hl0 (by decide) (fun k hk => ?_) ?_
  · rw [hspY, show P.g.rsp - 56#64 - 8 = P.g.rsp - 64#64 by bv_omega]
    exact hO.stk k (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hspY, show P.g.rsp - 56#64 - 8 = P.g.rsp - 64#64 by bv_omega] at hA₂ hg₂
  have hM₂ := hM0.call h64 (bs := toBytesLE (gev_at.add (120 + 5)) 8) (toBytesLE_length _ _)
  have hdi : Y₂.cpu.gpr.rdi = P.g.rdi := by rw [hg₂, hgY]; rfl
  have hsp₂ : Y₂.cpu.gpr.rsp = P.g.rsp - 64#64 := by rw [hg₂]; rfl
  refine hlen P.n c hK₂ hA₂ hr₂ (hPm _ hM₂.out) hin (lt_len (show 125 < 224 by decide)) ?_ (fun k hk => ?_)
    (by rw [hdi]; exact hnf) (fun k hk => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [hsp₂, vs (toBytesLE_length _ _) (by bv_omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hsp₂]
    exact c.hws _ (hO.stk k (by omega))
  · rw [hdi, hM₂.out _ (hO.nout k (by omega))]
    exact hO.nnz k hk
  · rw [hdi, hM₂.out _ (hO.nout P.n (Nat.le_refl _))]
    exact hO.nz
  · rw [hdi] at h1 h2
    exact hO.npg x h1 h2
  intro Z t' hKZ hAZ hrZ hspZ hax hbxZ hbpZ h12Z h13Z h14Z h15Z
  have e13 : Z.cpu.gpr.r13 = P.g.rdi := by rw [h13Z, hg₂, hgY]; rfl
  have e12 : Z.cpu.gpr.r12 = P.ptr 0 := by rw [h12Z, hg₂, hgY]; rfl
  have ebx : Z.cpu.gpr.rbx = P.envp := by rw [hbxZ, hg₂, hgY]; rfl
  have esp : Z.cpu.gpr.rsp = P.g.rsp - 56#64 := by rw [hspZ, hsp₂]; bv_omega
  refine (c_125 prof).run c hin _ hKZ hAZ hrZ (vc_125 fun i hi => ?_) ?_
  · rw [e13]
    exact nfoot i (by omega)
  rintro j' g fl V₃ ⟨hj, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hL : Lp P 0 Y₃.cpu.gpr := by
    rw [hg₃]
    refine ⟨esp, ?_, e12, ?_, ?_, hax, ?_⟩
    · show Z.cpu.gpr.rbx = _
      rw [ebx]
      exact (addr_add_zero _).symm
    · show BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 rdw(_, Z.cpu.gpr.r13))) = _
      rw [sw16, e13, hM₂.rd (n := 2) fun k hk => hO.nout k (by omega)]
    · show Z.cpu.gpr.r13 + 2#64 = _
      rw [e13]
    · show Z.cpu.gpr.rax - 2#64 = _
      rw [hax]
  rcases hj with ⟨rfl, hne⟩ | ⟨rfl, h0⟩
  · have h0N : 0 < P.N := by
      rcases Nat.eq_zero_or_pos P.N with h | h
      · exact absurd (by rw [← e12] at *; exact hne) (by rw [e12]; have := hO.eend; rw [h] at this; simp [this])
      · exact h
    exact loop c hin hic hc0 hcmp hO hPm kx P.N 0 rfl h0N Y₃ t₃ _ hK₃ hA₃ hM₂ hr₃ hL
  · exact kx Y₃ t₃ _ hK₃ hA₃ hM₂ hr₃ (by rw [hg₃]; exact esp) (by rw [hg₃]; exact h0)

end FV7z.Genv
