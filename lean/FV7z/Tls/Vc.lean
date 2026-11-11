import FV7z.Tls.Cuts
import FV7z.Sbrk.Holds
/-!
# `__libc_setup_tls`: the pieces between the cut points (PLAN.md G3, startup)

glibc 2.31's `__libc_setup_tls` (`csu/libc-tls.c`) at `0x613a10` in `7zzs`, called once by `__libc_start_main`. The
verification conditions of `Tls/Cuts.lean` for the one way the run of `7zzs` takes: the loop over the program
headers finds `PT_TLS` at the sixth (`0x400158`: 40 bytes of initialisation image at `0x777770`, 128 bytes of
memory, alignment 8), the block is `__sbrk (4544)`, the image is copied by `memcpy`, and the thread pointer is set
by `arch_prctl (ARCH_SET_FS)`.

- `In`: what the function reads of the bytes at its entry (`_dl_phdr`, `_dl_phnum`, the main map, the program
  headers, `_dl_tls_static_size`, `__curbrk`).
- `vc_0` … `vc_427`: from a cut point to the next stop (the two `div`s, the `call`s of `__sbrk` and `memcpy`, the
  `syscall`, the three SSE moves, the `ret`), the registers and bytes there given.
- `div_166` … `ret_523`: the instructions at the stops, decoded.

The ways not taken: no `PT_TLS` header, alignment 0 or above 64, `__sbrk` failing (`_startup_fatal`), and
`arch_prctl` failing.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
namespace FV7z.Tls

variable {F : Footprint} {Wl : List Rgn}

def pdiv5 : List Byte := [0x48, 0xf7, 0xf5]
def pdiv6 : List Byte := [0x48, 0xf7, 0xf6]
def pc184 : List Byte := [0xe8, 0xc3, 0x28, 0x05, 0x00]
def pc299 : List Byte := [0xe8, 0x30, 0xd5, 0xde, 0xff]
def psys : List Byte := [0x0f, 0x05]
def pmovq : List Byte := [0xf3, 0x0f, 0x7e, 0x44, 0x24, 0x08]
def pmovhps : List Byte := [0x0f, 0x16, 0x44, 0x24, 0x10]
def pmovups : List Byte := [0x41, 0x0f, 0x11, 0x86, 0x30, 0x04, 0x00, 0x00]
def pret : List Byte := [0xc3]
theorem pdiv5_0 : ∀ feat, Dec feat pdiv5 0 (FV7z.mk .div 64 [gr 64 5] 3) := by dec_rfl
theorem pdiv6_0 : ∀ feat, Dec feat pdiv6 0 (FV7z.mk .div 64 [gr 64 6] 3) := by dec_rfl
theorem pc184_0 : ∀ feat, Dec feat pc184 0 (FV7z.mk .call 64 [.rel 338115] 5) := by dec_rfl
theorem pc299_0 : ∀ feat, Dec feat pc299 0 (FV7z.mk .call 64 [.rel 18446744073707377968] 5) := by dec_rfl
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem pmovq_0 : ∀ feat, Dec feat pmovq 0 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 8 64)] 6) := by dec_rfl
theorem pmovhps_0 : ∀ feat, Dec feat pmovhps 0 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 16 64)] 5) := by
  dec_rfl
theorem pmovups_0 : ∀ feat, Dec feat pmovups 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 14 1072 128), .xmm 0] 8) := by
  dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_166 : pdiv5 <+: tls.drop 166 := by decide +kernel
theorem w_184 : pc184 <+: tls.drop 184 := by decide +kernel
theorem w_245 : pdiv6 <+: tls.drop 245 := by decide +kernel
theorem w_299 : pc299 <+: tls.drop 299 := by decide +kernel
theorem w_341 : psys <+: tls.drop 341 := by decide +kernel
theorem w_375 : pmovq <+: tls.drop 375 := by decide +kernel
theorem w_402 : pmovhps <+: tls.drop 402 := by decide +kernel
theorem w_419 : pmovups <+: tls.drop 419 := by decide +kernel
theorem w_523 : pret <+: tls.drop 523 := by decide +kernel
theorem div_166 (feat : Features) : Dec feat tls 166 (FV7z.mk .div 64 [gr 64 5] 3) :=
  Dec.shift (j := 166) (k := 0) (pdiv5_0 feat) w_166 (Nat.zero_le _)
theorem call_184 (feat : Features) : Dec feat tls 184 (FV7z.mk .call 64 [.rel 338115] 5) :=
  Dec.shift (j := 184) (k := 0) (pc184_0 feat) w_184 (Nat.zero_le _)
theorem div_245 (feat : Features) : Dec feat tls 245 (FV7z.mk .div 64 [gr 64 6] 3) :=
  Dec.shift (j := 245) (k := 0) (pdiv6_0 feat) w_245 (Nat.zero_le _)
theorem call_299 (feat : Features) : Dec feat tls 299 (FV7z.mk .call 64 [.rel 18446744073707377968] 5) :=
  Dec.shift (j := 299) (k := 0) (pc299_0 feat) w_299 (Nat.zero_le _)
theorem sys_341 (feat : Features) : Dec feat tls 341 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 341) (k := 0) (psys_0 feat) w_341 (Nat.zero_le _)
theorem movq_375 (feat : Features) : Dec feat tls 375 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 8 64)] 6) :=
  Dec.shift (j := 375) (k := 0) (pmovq_0 feat) w_375 (Nat.zero_le _)
theorem movhps_402 (feat : Features) :
    Dec feat tls 402 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 16 64)] 5) :=
  Dec.shift (j := 402) (k := 0) (pmovhps_0 feat) w_402 (Nat.zero_le _)
theorem movups_419 (feat : Features) :
    Dec feat tls 419 (FV7z.mk (.sse .movups) 32 [.mem (mbd 14 1072 128), .xmm 0] 8) :=
  Dec.shift (j := 419) (k := 0) (pmovups_0 feat) w_419 (Nat.zero_le _)
theorem ret_523 (feat : Features) : Dec feat tls 523 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 523) (k := 0) (pret_0 feat) w_523 (Nat.zero_le _)


/-- `wpx`, with the arithmetic of numbers done. -/
macro "wpc" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceSub, BitVec.reduceAnd, BitVec.reduceToNat,
    BitVec.reduceSetWidth, BitVec.reduceSignExtend, BitVec.reduceXOr, BitVec.reduceNeg, BitVec.reduceEq,
    BitVec.reduceBEq, Nat.reduceLT, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, false_implies,
    BitVec.xor_self, Op.lda, Op.cmpmi, $ls,*])

/-- What `__libc_setup_tls` reads of the bytes at its entry. -/
structure In (V : Addr → Byte) : Prop where
  phdr : rdq(V, 8029568#64) = 4194368#64
  phnum : rdq(V, 8029592#64) = 8#64
  map : rdq(V, 7943232#64) = 7943392#64
  laddr : rdq(V, 7943392#64) = 0#64
  ssize : rdq(V, 7938736#64) = 2048#64
  cur : rdq(V, 8014904#64) = 0#64
  nt : ∀ i < 5, rdd(V, BitVec.ofNat 64 (4194368 + 56 * i)) ≠ 7#32
  ty : rdd(V, 4194648#64) = 7#32
  vaddr : rdq(V, 4194664#64) = 7829360#64
  filesz : rdq(V, 4194680#64) = 40#64
  memsz : rdq(V, 4194688#64) = 128#64
  align : rdq(V, 4194696#64) = 8#64

/-- Bytes below the stack, read after the six `push`es. -/
theorem rd_p6 (V : Addr → Byte) (sp : Addr) (x1 x2 x3 x4 x5 x6 : BitVec 64) (a : Addr) (n : Nat)
    (hsp : 0x7a9000 + 128 ≤ sp.toNat) (ha : a.toNat + n ≤ 0x7a9000) :
    List.map (Vst (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE x1 8)) (sp - 8 - 8) (toBytesLE x2 8))
      (sp - 8 - 8 - 8) (toBytesLE x3 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE x4 8)) (sp - 8 - 8 - 8 - 8 - 8)
      (toBytesLE x5 8)) (sp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE x6 8)) (byteAddrs a n) =
      List.map V (byteAddrs a n) := by
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hI : In V)
    (hst : ∀ i < 48, Foot Wl (Addr.add (g.rsp - 48) i))
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a)
    (hsp : 0x7a9000 + 128 ≤ g.rsp.toNat) :
    W_0 F Wl (fun j' g' _ V' => j' = 93 ∧
      g' = ((((g.set 4 (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 40)).set 0 4194368#64).set 14 7943392#64).set 1 8#64).set 2
        4194816#64 ∧
      V' = Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
        (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
        (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8))
        g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hsp' : 0x7a9000 + 128 ≤ rsp.toNat := hsp
  have hst' : ∀ i < 48, Foot Wl (Addr.add (rsp - 48) i) := hst
  have e1 := rd_p6 V rsp r15 r14 r13 r12 rbp rbx 8029568#64 8 hsp' (by decide)
  have e2 := rd_p6 V rsp r15 r14 r13 r12 rbp rbx 7943232#64 8 hsp' (by decide)
  have e3 := rd_p6 V rsp r15 r14 r13 r12 rbp rbx 8029592#64 8 hsp' (by decide)
  have sl : ∀ k, k + 8 ≤ 48 → ∀ a : Addr, a = rsp - 48 + BitVec.ofNat 64 k → ∀ i < 8, Foot Wl (Addr.add a i) := by
    intro k hk a ha i hi
    have e : Addr.add a i = Addr.add (rsp - 48) (k + i) := by subst ha; simp only [Addr.add]; bv_omega
    rw [e]
    exact hst' _ (by omega)
  have gl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat + 8 ≤ 0x7a9000 → ∀ i < 8, Foot F.data (Addr.add a i) :=
    fun a h1 h2 i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  wpc [W_0, W_41, W_68, o0, o1, e1, e2, e3, hI.phdr, hI.map, hI.phnum]
  exact ⟨sl 40 (by omega) _ (by bv_omega), sl 32 (by omega) _ (by bv_omega), sl 24 (by omega) _ (by bv_omega),
    sl 16 (by omega) _ (by bv_omega), sl 8 (by omega) _ (by bv_omega), sl 0 (by omega) _ (by bv_omega),
    gl _ (by decide) (by decide), gl _ (by decide) (by decide), gl _ (by decide) (by decide), rfl⟩

/-- A program header that is not `PT_TLS`, not the last: to the next. -/
theorem vc_93n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 4, Foot F.data (Addr.add g.rax i))
    (h7 : rdd(V, g.rax) ≠ 7#32) (hlt : (g.rax + 56#64).toNat < g.rdx.toNat) :
    W_93 F Wl (fun j' g' _ V' => j' = 93 ∧ g' = g.set 0 (g.rax + 56#64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hl' : ∀ i < 4, Foot F.data (Addr.add rax i) := hl
  have h7' : rdd(V, rax) ≠ 7#32 := h7
  have hlt' : (rax + 56#64).toNat < rdx.toNat := hlt
  wpc [W_93, W_80, W_98, o3, o2, h7', hlt']
  exact ⟨hl', rfl⟩

/-- The `PT_TLS` program header: to the `div`. -/
theorem vc_93e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hI : In V) (hax : g.rax = 4194648#64)
    (h14 : g.r14 = 7943392#64)
    (hst : ∀ i < 16, Foot Wl (Addr.add (g.rsp + 8#64) i))
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot F.data a)
    (hhd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x401000 → Foot F.data a) :
    W_93 F Wl (fun j' g' _ V' => j' = 166 ∧
      g' = ((((((((g.set 12 8#64).set 3 128#64).set 5 64#64).set 15 1#64).set 1 40#64).set 8 7829360#64).set 0
        2239#64).set 2 0#64).set 13 7829360#64 ∧
      V' = Vst (Vst V (g.rsp + 16#64) (toBytesLE 128#64 8)) (g.rsp + 8#64) (toBytesLE 40#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 4194648#64 := hax
  obtain rfl : r14 = 7943392#64 := h14
  have hst' : ∀ i < 16, Foot Wl (Addr.add (rsp + 8#64) i) := hst
  have gl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat + 8 ≤ 0x7a9000 → ∀ i < 8, Foot F.data (Addr.add a i) :=
    fun a h1 h2 i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  have hd : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat + 8 ≤ 0x401000 → ∀ i < 8, Foot F.data (Addr.add a i) :=
    fun a h1 h2 i hi => hhd _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  wpc [W_93, W_80, W_98, o3, o4, hI.ty, hI.vaddr, hI.filesz, hI.memsz, hI.align, hI.ssize, hI.laddr]
  refine ⟨fun i hi => hhd _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega),
    hd _ (by decide) (by decide), hd _ (by decide) (by decide), hd _ (by decide) (by decide),
    hd _ (by decide) (by decide), gl _ (by decide) (by decide), gl _ (by decide) (by decide), fun i hi => ?_,
    fun i hi => hst' i (by omega), rfl⟩
  have e : Addr.add (rsp + 16#64) i = Addr.add (rsp + 8#64) (8 + i) := by simp only [Addr.add]; bv_omega
  rw [e]
  exact hst' _ (by omega)

/-- After the first `div`: to the `call` of `__sbrk`. -/
theorem vc_169 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax = 34#64) (hbp : g.rbp = 64#64) :
    W_169 F Wl (fun j' g' _ V' => j' = 184 ∧ g' = ((g.set 0 2176#64).set 7 4544#64).set 3 2176#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 34#64 := hax
  obtain rfl : rbp = 64#64 := hbp
  wpc [W_169, o5, Op.imul64]
  exact fun _ => rfl

/-- After `__sbrk`: to the second `div`. -/
theorem vc_189 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = 64#64) (h12 : g.r12 = 8#64)
    (h15 : g.r15 = 1#64)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h16 : rdq(Vst V 8027904#64 (toBytesLE 62#64 8), g.rsp + 16#64) = 128#64) :
    W_189 F Wl (fun j' g' _ V' => j' = 245 ∧
      g' = ((((g.set 6 8#64).set 1 ((64#64 + g.rax + 18446744073709551615#64) &&& 18446744073709551552#64)).set 0
        135#64).set 2 0#64).set 7 g.rbx ∧
      V' = Vst V 8027904#64 (toBytesLE 62#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rbp = 64#64 := hbp
  obtain rfl : r12 = 8#64 := h12
  obtain rfl : r15 = 1#64 := h15
  have hl' : ∀ i < 8, Foot F.data (Addr.add (rsp + 16#64) i) := hl
  have h16' : rdq(Vst V 8027904#64 (toBytesLE 62#64 8), rsp + 16#64) = 128#64 := h16
  wpc [W_189, W_230, o6, o7, Op.stia, h16']
  exact ⟨fun i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega), hl', rfl⟩

/-- After the second `div`: to the `call` of `memcpy`. -/
theorem vc_248 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax = 16#64) (hsi : g.rsi = 8#64)
    (hdi : g.rdi = 2176#64) (h14 : g.r14 = 7943392#64)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i))
    (h8 : rdq(V, g.rsp + 8#64) = 40#64) :
    W_248 F Wl (fun j' g' _ V' => j' = 299 ∧
      g' = ((((g.set 0 128#64).set 15 128#64).set 7 (2048#64 + g.rcx)).set 2 40#64).set 6 g.r13 ∧
      V' = Vst (Vst (Vst (Vst V (g.rsp + 24#64) (toBytesLE g.rcx 8)) 7944496#64 (toBytesLE 128#64 8)) 8027936#64
        (toBytesLE (2048#64 + g.rcx) 8)) 8027944#64 (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 16#64 := hax
  obtain rfl : rsi = 8#64 := hsi
  obtain rfl : rdi = 2176#64 := hdi
  obtain rfl : r14 = 7943392#64 := h14
  have hl' : ∀ i < 8, Foot F.data (Addr.add (rsp + 8#64) i) := hl
  have hst' : ∀ i < 8, Foot Wl (Addr.add (rsp + 24#64) i) := hst
  have h8' : rdq(V, rsp + 8#64) = 40#64 := h8
  wpc [W_248, W_258, o8, o9, Op.imul64, Op.stia, Op.sta, h8']
  have gl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat + 8 ≤ 0x7a9000 → ∀ i < 8, Foot Wl (Addr.add a i) :=
    fun a h1 h2 i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  exact fun _ => ⟨hl', hst', gl _ (by decide) (by decide), gl _ (by decide) (by decide),
    gl _ (by decide) (by decide), rfl⟩

/-- After `memcpy`: to the `syscall`. `c` is the block's address. -/
theorem vc_304 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c : Addr} (hbx : g.rbx = 2176#64)
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hst : ∀ i < 24, Foot Wl (Addr.add (c + 2176#64) i))
    (h24 : rdq(V, g.rsp + 24#64) = c) :
    W_304 F Wl (fun j' g' _ V' => j' = 341 ∧
      g' = (((g.set 1 c).set 7 4098#64).set 6 (c + 2176#64)).set 0 158#64 ∧
      V' = Vst (Vst (Vst V (c + 2176#64 + 8#64) (toBytesLE 8027920#64 8)) (c + 2176#64) (toBytesLE (c + 2176#64) 8))
        (c + 2176#64 + 16#64) (toBytesLE (c + 2176#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rbx = 2176#64 := hbx
  have hl' : ∀ i < 8, Foot F.data (Addr.add (rsp + 24#64) i) := hl
  have h24' : rdq(V, rsp + 24#64) = c := h24
  wpc [W_304, o10, h24']
  have sl : ∀ k, k + 8 ≤ 24 → ∀ a : Addr, a = c + 2176#64 + BitVec.ofNat 64 k → ∀ i < 8, Foot Wl (Addr.add a i) := by
    intro k hk a ha i hi
    have e : Addr.add a i = Addr.add (c + 2176#64) (k + i) := by subst ha; simp only [Addr.add]; bv_omega
    rw [e]
    exact hst _ (by omega)
  exact ⟨hl', sl 8 (by omega) _ rfl, sl 0 (by omega) _ (by bv_omega), sl 16 (by omega) _ rfl, rfl⟩

/-- After `arch_prctl` has returned 0: to the `movq`. -/
theorem vc_343 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax = 0#64) :
    W_343 F Wl (fun j' g' _ V' => j' = 375 ∧ g' = g.set 0 8008672#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 0#64 := hax
  wpc [W_343, W_368, o11, o12]
  rfl

/-- Between the `movq` and the `movhps`. -/
theorem vc_381 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (h14 : g.r14 = 7943392#64) (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hws : ∀ a, Foot Wl a → Foot F.data a)
    (hs : rdq(V, 7938736#64) = 2048#64)
    (hQ : ∀ fl, Q (g.set 0 2048#64) fl
      (Vst (Vst V 7944480#64 (toBytesLE g.r12 8)) 8027888#64 (toBytesLE g.rax 8))) :
    wp F Wl o13 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : r14 = 7943392#64 := h14
  have gl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat + 8 ≤ 0x7a9000 → ∀ i < 8, Foot Wl (Addr.add a i) :=
    fun a h1 h2 i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  have e : rdq(Vst (Vst V 7944480#64 (toBytesLE r12 8)) 8027888#64 (toBytesLE rax 8), 7938736#64) = 2048#64 := by
    rw [rd_Vst, rd_Vst]
    · exact hs
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  wpc [o13, Op.sta, e]
  exact ⟨gl _ (by decide) (by decide), gl _ (by decide) (by decide),
    fun i hi => hws _ (gl _ (by decide) (by decide) i hi), hQ _⟩

/-- Between the `movhps` and the `movups`. -/
theorem vc_407 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (h14 : g.r14 = 7943392#64) (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hQ : ∀ fl, Q (g.set 0 (g.r15 + g.rax + 63#64)) fl (Vst V 7944456#64 (toBytesLE g.r13 8))) :
    wp F Wl o14 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : r14 = 7943392#64 := h14
  wpc [o14]
  exact ⟨fun i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega), hQ _⟩

/-- After the `movups`: to the `ret`. -/
theorem vc_427 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax = 2239#64) (h14 : g.r14 = 7943392#64)
    (hgl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat < 0x7a9000 → Foot Wl a)
    (hl : ∀ i < 48, Foot F.data (Addr.add (g.rsp + 40#64) i)) (hsp : 0x7a9000 ≤ g.rsp.toNat)
    (hsp' : g.rsp.toNat + 88 ≤ 2 ^ 64) :
    W_427 F Wl (fun j' g' _ V' => j' = 523 ∧
      V' = Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V 8008712#64 (toBytesLE 7943392#64 8)) 8027880#64
        (toBytesLE g.r15 8)) 7944504#64 (toBytesLE 1#64 8)) 8027856#64 (toBytesLE g.rbp 8)) 8008672#64
        (toBytesLE 64#64 8)) 8027864#64 (toBytesLE 1#64 8)) 7938736#64 (toBytesLE 4480#64 8)) 8027872#64
        (toBytesLE 1#64 8) ∧
      g' = (((((((g.set 0 4480#64).set 4 (g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8)).set 3 rdq(V, g.rsp + 40#64)).set 5
        rdq(V, g.rsp + 40#64 + 8)).set 12 rdq(V, g.rsp + 40#64 + 8 + 8)).set 13 rdq(V, g.rsp + 40#64 + 8 + 8 + 8)).set
        14 rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8)).set 15 rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 2239#64 := hax
  obtain rfl : r14 = 7943392#64 := h14
  have hl' : ∀ i < 48, Foot F.data (Addr.add (rsp + 40#64) i) := hl
  have hsp1 : 0x7a9000 ≤ rsp.toNat := hsp
  have hsp2 : rsp.toNat + 88 ≤ 2 ^ 64 := hsp'
  have gl : ∀ a : Addr, 0x777000 ≤ a.toNat → a.toNat + 8 ≤ 0x7a9000 → ∀ i < 8, Foot Wl (Addr.add a i) :=
    fun a h1 h2 i hi => hgl _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  have rd : ∀ x : Addr, 0x7a9000 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
      rdq(Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V 8008712#64 (toBytesLE 7943392#64 8)) 8027880#64
        (toBytesLE r15 8)) 7944504#64 (toBytesLE 1#64 8)) 8027856#64 (toBytesLE rbp 8)) 8008672#64
        (toBytesLE 64#64 8)) 8027864#64 (toBytesLE 1#64 8)) 7938736#64 (toBytesLE 4480#64 8)) 8027872#64
        (toBytesLE 1#64 8), x) = rdq(V, x) := by
    intro x h1 h2
    rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  have sl : ∀ k, k + 8 ≤ 48 → ∀ a : Addr, a = rsp + 40#64 + BitVec.ofNat 64 k → ∀ i < 8,
      Foot F.data (Addr.add a i) := by
    intro k hk a ha i hi
    have e : Addr.add a i = Addr.add (rsp + 40#64) (k + i) := by subst ha; simp only [Addr.add]; bv_omega
    rw [e]
    exact hl' _ (by omega)
  wpc [W_427, o15, Op.sta, Op.stia, rd (rsp + 40#64) (by bv_omega) (by bv_omega),
    rd (rsp + 40#64 + 8) (by bv_omega) (by bv_omega), rd (rsp + 40#64 + 8 + 8) (by bv_omega) (by bv_omega),
    rd (rsp + 40#64 + 8 + 8 + 8) (by bv_omega) (by bv_omega),
    rd (rsp + 40#64 + 8 + 8 + 8 + 8) (by bv_omega) (by bv_omega),
    rd (rsp + 40#64 + 8 + 8 + 8 + 8 + 8) (by bv_omega) (by bv_omega)]
  exact ⟨gl _ (by decide) (by decide), gl _ (by decide) (by decide), gl _ (by decide) (by decide),
    gl _ (by decide) (by decide), gl _ (by decide) (by decide), gl _ (by decide) (by decide),
    gl _ (by decide) (by decide), gl _ (by decide) (by decide), sl 0 (by omega) _ (by bv_omega),
    sl 8 (by omega) _ (by bv_omega), sl 16 (by omega) _ (by bv_omega), sl 24 (by omega) _ (by bv_omega),
    sl 32 (by omega) _ (by bv_omega), sl 40 (by omega) _ (by bv_omega), rfl⟩

end FV7z.Tls
