import FV7z.Pmi.Cuts
import FV7z.Eli.Holds
import FV7z.Cxa.Holds
import FV7z.Lemmas.Xmm3
/-!
# `ptmalloc_init` (PLAN.md G3, malloc)

glibc 2.31's `ptmalloc_init` at `0x632170` in `7zzs` (`malloc/arena.c`), what the first `malloc` runs through
`malloc_hook_ini`: `__malloc_initialized := 0`, `thread_arena := &main_arena` (`fs:-24`), `malloc_init_state
(&main_arena)` (the 127 bins each its own list, the arena's flags 0, `global_max_fast := 128`, `top` the first bin),
twelve `__tunable_get_val (id, &v, callback)` for the `glibc.malloc.*` tunables (ids 25, 8, 2, 19, 1, 12, 18, 22, 24,
21, 14, 6 of `tunable_list`; 25, 2 and 12 of type `INT_32`, the others `SIZE_T`), then `__malloc_initialized := 1`.
With the tunables not set (`Tgv.tgv32_ok`, `Tgv.tgv64_ok`) no callback runs.

- `movq_64`, `punp_73`, `movaps_77`, `call_131` … `call_351`, `ret_387`: the instructions outside the blocks; `vc_*`:
  the verification conditions.
- `Env`: what the code, the frame, the thread's block and the arena's words need; `Wr`: the bytes outside the frame
  the function stores into; `Lp`: the memory in the loop over the bins; `Dat`: after it.
- `bin_step`, `bins_go`: the loop; `tcall`: one call of `__tunable_get_val` and its return, the frame kept.
- `pmi_ok`: called with the twelve tunables not set, the run reaches the return address, the registers a call keeps
  as at the entry (`Osv.Back`), the bytes outside the 32 below the stack pointer and `Wr` as they were, the words
  stored as `Dat` says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Pmi

/-! ## The instructions outside the blocks -/

def pmq : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xc0]
theorem pmq_0 : ∀ feat, Dec feat pmq 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) := by dec_rfl
theorem w_64 : pmq <+: pmi.drop 64 := by decide +kernel
theorem movq_64 (feat : Features) : Dec feat pmi 64 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 0] 5) :=
  Dec.shift (j := 64) (k := 0) (pmq_0 feat) w_64 (Nat.zero_le _)

def ppu : List Byte := [0x66, 0x0f, 0x6c, 0xc0]
theorem ppu_0 : ∀ feat, Dec feat ppu 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem w_73 : ppu <+: pmi.drop 73 := by decide +kernel
theorem punp_73 (feat : Features) : Dec feat pmi 73 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 0] 4) :=
  Dec.shift (j := 73) (k := 0) (ppu_0 feat) w_73 (Nat.zero_le _)

def pma : List Byte := [0x0f, 0x29, 0x00]
theorem pma_0 : ∀ feat, Dec feat pma 0 (FV7z.mk (.sse .movaps) 32 [.mem (mbd 0 0 128), .xmm 0] 3) := by dec_rfl
theorem w_77 : pma <+: pmi.drop 77 := by decide +kernel
theorem movaps_77 (feat : Features) : Dec feat pmi 77 (FV7z.mk (.sse .movaps) 32 [.mem (mbd 0 0 128), .xmm 0] 3) :=
  Dec.shift (j := 77) (k := 0) (pma_0 feat) w_77 (Nat.zero_le _)

def pc0 : List Byte := [0xe8, 0xa8, 0xd1, 0x03, 0x00]
theorem pc0_0 : ∀ feat, Dec feat pc0 0 (FV7z.mk .call 64 [.rel 250280] 5) := by dec_rfl
theorem w_131 : pc0 <+: pmi.drop 131 := by decide +kernel
theorem call_131 (feat : Features) : Dec feat pmi 131 (FV7z.mk .call 64 [.rel 250280] 5) :=
  Dec.shift (j := 131) (k := 0) (pc0_0 feat) w_131 (Nat.zero_le _)

def pc1 : List Byte := [0xe8, 0x94, 0xd1, 0x03, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 250260] 5) := by dec_rfl
theorem w_151 : pc1 <+: pmi.drop 151 := by decide +kernel
theorem call_151 (feat : Features) : Dec feat pmi 151 (FV7z.mk .call 64 [.rel 250260] 5) :=
  Dec.shift (j := 151) (k := 0) (pc1_0 feat) w_151 (Nat.zero_le _)

def pc2 : List Byte := [0xe8, 0x80, 0xd1, 0x03, 0x00]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 250240] 5) := by dec_rfl
theorem w_171 : pc2 <+: pmi.drop 171 := by decide +kernel
theorem call_171 (feat : Features) : Dec feat pmi 171 (FV7z.mk .call 64 [.rel 250240] 5) :=
  Dec.shift (j := 171) (k := 0) (pc2_0 feat) w_171 (Nat.zero_le _)

def pc3 : List Byte := [0xe8, 0x6c, 0xd1, 0x03, 0x00]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 250220] 5) := by dec_rfl
theorem w_191 : pc3 <+: pmi.drop 191 := by decide +kernel
theorem call_191 (feat : Features) : Dec feat pmi 191 (FV7z.mk .call 64 [.rel 250220] 5) :=
  Dec.shift (j := 191) (k := 0) (pc3_0 feat) w_191 (Nat.zero_le _)

def pc4 : List Byte := [0xe8, 0x58, 0xd1, 0x03, 0x00]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 250200] 5) := by dec_rfl
theorem w_211 : pc4 <+: pmi.drop 211 := by decide +kernel
theorem call_211 (feat : Features) : Dec feat pmi 211 (FV7z.mk .call 64 [.rel 250200] 5) :=
  Dec.shift (j := 211) (k := 0) (pc4_0 feat) w_211 (Nat.zero_le _)

def pc5 : List Byte := [0xe8, 0x44, 0xd1, 0x03, 0x00]
theorem pc5_0 : ∀ feat, Dec feat pc5 0 (FV7z.mk .call 64 [.rel 250180] 5) := by dec_rfl
theorem w_231 : pc5 <+: pmi.drop 231 := by decide +kernel
theorem call_231 (feat : Features) : Dec feat pmi 231 (FV7z.mk .call 64 [.rel 250180] 5) :=
  Dec.shift (j := 231) (k := 0) (pc5_0 feat) w_231 (Nat.zero_le _)

def pc6 : List Byte := [0xe8, 0x30, 0xd1, 0x03, 0x00]
theorem pc6_0 : ∀ feat, Dec feat pc6 0 (FV7z.mk .call 64 [.rel 250160] 5) := by dec_rfl
theorem w_251 : pc6 <+: pmi.drop 251 := by decide +kernel
theorem call_251 (feat : Features) : Dec feat pmi 251 (FV7z.mk .call 64 [.rel 250160] 5) :=
  Dec.shift (j := 251) (k := 0) (pc6_0 feat) w_251 (Nat.zero_le _)

def pc7 : List Byte := [0xe8, 0x1c, 0xd1, 0x03, 0x00]
theorem pc7_0 : ∀ feat, Dec feat pc7 0 (FV7z.mk .call 64 [.rel 250140] 5) := by dec_rfl
theorem w_271 : pc7 <+: pmi.drop 271 := by decide +kernel
theorem call_271 (feat : Features) : Dec feat pmi 271 (FV7z.mk .call 64 [.rel 250140] 5) :=
  Dec.shift (j := 271) (k := 0) (pc7_0 feat) w_271 (Nat.zero_le _)

def pc8 : List Byte := [0xe8, 0x08, 0xd1, 0x03, 0x00]
theorem pc8_0 : ∀ feat, Dec feat pc8 0 (FV7z.mk .call 64 [.rel 250120] 5) := by dec_rfl
theorem w_291 : pc8 <+: pmi.drop 291 := by decide +kernel
theorem call_291 (feat : Features) : Dec feat pmi 291 (FV7z.mk .call 64 [.rel 250120] 5) :=
  Dec.shift (j := 291) (k := 0) (pc8_0 feat) w_291 (Nat.zero_le _)

def pc9 : List Byte := [0xe8, 0xf4, 0xd0, 0x03, 0x00]
theorem pc9_0 : ∀ feat, Dec feat pc9 0 (FV7z.mk .call 64 [.rel 250100] 5) := by dec_rfl
theorem w_311 : pc9 <+: pmi.drop 311 := by decide +kernel
theorem call_311 (feat : Features) : Dec feat pmi 311 (FV7z.mk .call 64 [.rel 250100] 5) :=
  Dec.shift (j := 311) (k := 0) (pc9_0 feat) w_311 (Nat.zero_le _)

def pc10 : List Byte := [0xe8, 0xe0, 0xd0, 0x03, 0x00]
theorem pc10_0 : ∀ feat, Dec feat pc10 0 (FV7z.mk .call 64 [.rel 250080] 5) := by dec_rfl
theorem w_331 : pc10 <+: pmi.drop 331 := by decide +kernel
theorem call_331 (feat : Features) : Dec feat pmi 331 (FV7z.mk .call 64 [.rel 250080] 5) :=
  Dec.shift (j := 331) (k := 0) (pc10_0 feat) w_331 (Nat.zero_le _)

def pc11 : List Byte := [0xe8, 0xcc, 0xd0, 0x03, 0x00]
theorem pc11_0 : ∀ feat, Dec feat pc11 0 (FV7z.mk .call 64 [.rel 250060] 5) := by dec_rfl
theorem w_351 : pc11 <+: pmi.drop 351 := by decide +kernel
theorem call_351 (feat : Features) : Dec feat pmi 351 (FV7z.mk .call 64 [.rel 250060] 5) :=
  Dec.shift (j := 351) (k := 0) (pc11_0 feat) w_351 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_387 : pret <+: pmi.drop 387 := by decide +kernel
theorem ret_387 (feat : Features) : Dec feat pmi 387 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 387) (k := 0) (pret_0 feat) w_387 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- To the loop: `rbp` pushed, the stack guard's copy, `__malloc_initialized := 0`, `thread_arena := &main_arena`,
the loop's registers. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hbp : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 16#64 + 8#64) i))
    (hini : ∀ i < 4, Foot Wl (Addr.add 7940484#64 i))
    (htl : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551592#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 64 ∧
      g' = { g with rax := 7940768#64, rcx := 7942800#64, rdx := 7940768#64, rsp := g.rsp - 8 - 16#64 } ∧
      V' = Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 16#64 + 8#64)
        (toBytesLE rdq(Vst V (g.rsp - 8) (toBytesLE g.rbp 8), fb + 40#64) 8)) (7940484#64) (toBytesLE (0#32) 4))
        (fb + 18446744073709551592#64) (toBytesLE (7940672#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp hst
  wpx [W_0, o0, Op.ldf, Op.stf, Op.stia, BitVec.xor_self]
  exact ⟨hbp, hfl, hst, hini, htl, rfl⟩

/-- `add rax, 16`. -/
theorem vc_69 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    wp F Wl o1 (fun g' _ V' => g' = { g with rax := g.rax + 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o1]

/-- The loop's end: not the last bin, again; the last, `global_max_fast := 128`, the arena's flags 0, `top` the
first bin, the arguments `(25, &v, callback)`. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hgm : ∀ i < 8, Foot Wl (Addr.add 8013224#64 i)) (hfg : ∀ i < 4, Foot Wl (Addr.add 7940680#64 i))
    (htp : ∀ i < 8, Foot Wl (Addr.add 7940768#64 i)) :
    W_80 fb F Wl (fun j' g' _ V' => (j' = 64 ∧ g.rax ≠ g.rcx ∧ g' = g ∧ V' = V) ∨
      (j' = 131 ∧ g.rax = g.rcx ∧ g' = { g with rdx := 6484736#64, rbp := g.rsp, rsi := g.rsp, rdi := 25 } ∧
        V' = Vst (Vst (Vst V (8013224#64) (toBytesLE (128#64) 8)) (7940680#64) (toBytesLE (0#32) 4)) (7940768#64)
          (toBytesLE g.rdx 8))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_80, W_85, o2, o3, Op.sta, Op.stia]
  refine ⟨fun h => ?_, fun h => ⟨hgm, hfg, htp, ?_⟩⟩
  · exact .inl (by simpa using h)
  · exact .inr ⟨by simpa using h, rfl⟩

/-- The arguments `(8, &v, callback)`. -/
theorem vc_136 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_136 fb F Wl (fun j' g' _ V' => j' = 151 ∧ g' = { g with rdx := 6480768#64, rsi := g.rbp, rdi := 8 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_136, o4]
  rfl

/-- The arguments `(2, &v, callback)`. -/
theorem vc_156 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_156 fb F Wl (fun j' g' _ V' => j' = 171 ∧ g' = { g with rdx := 6480880#64, rsi := g.rbp, rdi := 2 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_156, o5]
  rfl

/-- The arguments `(19, &v, callback)`. -/
theorem vc_176 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_176 fb F Wl (fun j' g' _ V' => j' = 191 ∧ g' = { g with rdx := 6480800#64, rsi := g.rbp, rdi := 19 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_176, o6]
  rfl

/-- The arguments `(1, &v, callback)`. -/
theorem vc_196 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_196 fb F Wl (fun j' g' _ V' => j' = 211 ∧ g' = { g with rdx := 6480736#64, rsi := g.rbp, rdi := 1 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_196, o7]
  rfl

/-- The arguments `(12, &v, callback)`. -/
theorem vc_216 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_216 fb F Wl (fun j' g' _ V' => j' = 231 ∧ g' = { g with rdx := 6480848#64, rsi := g.rbp, rdi := 12 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_216, o8]
  rfl

/-- The arguments `(18, &v, callback)`. -/
theorem vc_236 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_236 fb F Wl (fun j' g' _ V' => j' = 251 ∧ g' = { g with rdx := 6479840#64, rsi := g.rbp, rdi := 18 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_236, o9]
  rfl

/-- The arguments `(22, &v, callback)`. -/
theorem vc_256 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_256 fb F Wl (fun j' g' _ V' => j' = 271 ∧ g' = { g with rdx := 6479856#64, rsi := g.rbp, rdi := 22 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_256, o10]
  rfl

/-- The arguments `(24, &v, callback)`. -/
theorem vc_276 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_276 fb F Wl (fun j' g' _ V' => j' = 291 ∧ g' = { g with rdx := 6479872#64, rsi := g.rbp, rdi := 24 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_276, o11]
  rfl

/-- The arguments `(21, &v, callback)`. -/
theorem vc_296 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_296 fb F Wl (fun j' g' _ V' => j' = 311 ∧ g' = { g with rdx := 6479936#64, rsi := g.rbp, rdi := 21 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_296, o12]
  rfl

/-- The arguments `(14, &v, callback)`. -/
theorem vc_316 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_316 fb F Wl (fun j' g' _ V' => j' = 331 ∧ g' = { g with rdx := 6479968#64, rsi := g.rbp, rdi := 14 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_316, o13]
  rfl

/-- The arguments `(6, &v, callback)`. -/
theorem vc_336 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_336 fb F Wl (fun j' g' _ V' => j' = 351 ∧ g' = { g with rdx := 6480896#64, rsi := g.rbp, rdi := 6 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_336, o14]
  rfl

/-- `__malloc_initialized := 1`, the check of the stack guard, to the `ret`. -/
theorem vc_356 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hini : ∀ i < 4, Foot Wl (Addr.add 7940484#64 i))
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(Vst V (7940484#64) (toBytesLE (1#32) 4), g.rsp + 8#64) =
      rdq(Vst V (7940484#64) (toBytesLE (1#32) 4), fb + 40#64))
    (hp : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_356 fb F Wl (fun j' g' _ V' => j' = 387 ∧
      g' = { g with rax := 0, rsp := g.rsp + 16#64 + 8,
                    rbp := rdq(Vst V (7940484#64) (toBytesLE (1#32) 4), g.rsp + 16#64) } ∧
      V' = Vst V (7940484#64) (toBytesLE (1#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc hp
  wpx [W_356, W_382, o15, o16, Op.xormf, Op.stia, hc, BitVec.xor_self]
  exact ⟨hini, hl, hfl, fun h => absurd h (by decide), fun _ => ⟨hp, rfl⟩⟩

/-! ## The addresses -/

theorem b24 (S : Addr) : S - 24#64 = S - 32#64 + BitVec.ofNat 64 8 := by bv_omega
theorem tn24 {S : Addr} (h : 32 < S.toNat) : (S - 24#64).toNat = S.toNat - 24 := by bv_omega
theorem ad16 (i : Nat) :
    BitVec.ofNat 64 (7940768 + 16 * i) + 16#64 = BitVec.ofNat 64 (7940768 + 16 * (i + 1)) := by bv_omega
theorem ea16 (i : Nat) :
    BitVec.ofNat 64 (7940768 + 16 * (i + 1)) + BitVec.ofNat 64 0 = BitVec.ofNat 64 (7940784 + 16 * i) := by bv_omega
theorem nx8 (i : Nat) : BitVec.ofNat 64 (7940784 + 16 * i) + 8#64 = BitVec.ofNat 64 (7940792 + 16 * i) := by bv_omega
theorem bn16 (i : Nat) : BitVec.ofNat 64 (7940784 + 16 * i) = 7940784#64 + BitVec.ofNat 64 (16 * i) := by bv_omega
theorem al16 (i : Nat) : (BitVec.ofNat 64 (7940784 + 16 * i)).toNat % 16 = 0 := by bv_omega
theorem eq127 {i : Nat} (hi : i < 127) (h : BitVec.ofNat 64 (7940768 + 16 * (i + 1)) = 7942800#64) :
    i + 1 = 127 := by bv_omega

/-- The 16 bytes of a bin as its two words. -/
theorem st2 (V : Addr → Byte) (i : Nat) (x : BitVec 64) :
    Vst V (BitVec.ofNat 64 (7940784 + 16 * i)) (toBytesLE (x ++ x) 16) =
      Vst (Vst V (BitVec.ofNat 64 (7940784 + 16 * i)) (toBytesLE x 8)) (BitVec.ofNat 64 (7940792 + 16 * i))
        (toBytesLE x 8) := by
  rw [← nx8 i]
  exact Cxa.st16 V _ x x

/-! ## The memory -/

/-- What `ptmalloc_init` needs of the code, of the 32 bytes below the stack pointer `S` at its entry, of the thread's
block at `fb` and of the words it stores into: the frame and the words in what the run may store into, the thread's
block above the data and below the frame. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb S : Addr) : Prop where
  code : CodeIn L pmi_at pmi
  tcode : CodeIn L Tgv.tgv_at Tgv.tgv
  s0 : 32 < S.toNat
  s8 : S.toNat + 8 ≤ 2 ^ 64
  f0 : 8013232 + 24 ≤ fb.toNat
  f1 : fb.toNat + 48 ≤ S.toNat - 32
  st : ∀ i < 32, Foot Wl (Addr.add (S - 32#64) i)
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  fl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  tl : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551592#64) i)
  ini : ∀ i < 4, Foot Wl (Addr.add 7940484#64 i)
  flg : ∀ i < 4, Foot Wl (Addr.add 7940680#64 i)
  top : ∀ i < 8, Foot Wl (Addr.add 7940768#64 i)
  bins : ∀ i < 2032, Foot Wl (Addr.add 7940784#64 i)
  gmf : ∀ i < 8, Foot Wl (Addr.add 8013224#64 i)

/-- The bytes outside its frame `ptmalloc_init` stores into: `__malloc_initialized` (`0x792984`), `main_arena`'s
flags (`0x792a48`), its `top` (`0x792aa0`), its bins (`0x792ab0`, 2032 bytes), `global_max_fast` (`0x7a45a8`),
`thread_arena` (`fs:-24`). -/
def Wr (fb : Addr) (n : Nat) : Prop :=
  (7940484 ≤ n ∧ n < 7940488) ∨ (7940680 ≤ n ∧ n < 7940684) ∨ (7940768 ≤ n ∧ n < 7940776) ∨
    (7940784 ≤ n ∧ n < 7942816) ∨ (8013224 ≤ n ∧ n < 8013232) ∨ (fb.toNat - 24 ≤ n ∧ n < fb.toNat - 16)

/-- In the loop, the first `i` bins done: the bytes outside the frame and `Wr` as at the entry (`V`), the stack
guard's copy and the guard, the saved `rbp`, the return address, `__malloc_initialized` 0, `thread_arena`, the `i`
bins each with its two pointers to itself. -/
structure Lp (fb S rb : Addr) (i : Nat) (V V' : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 32 ≤ a.toNat ∧ a.toNat < S.toNat) → ¬ Wr fb a.toNat → V' a = V a
  can : rdq(V', S - 16#64) = rdq(V, fb + 40#64)
  gd : rdq(V', fb + 40#64) = rdq(V, fb + 40#64)
  bp : rdq(V', S - 8#64) = rb
  ra : rdq(V', S) = rdq(V, S)
  ini : rdd(V', 7940484#64) = 0
  tls : rdq(V', fb + 18446744073709551592#64) = 7940672#64
  bins : ∀ k < i, rdq(V', BitVec.ofNat 64 (7940784 + 16 * k)) = BitVec.ofNat 64 (7940768 + 16 * k) ∧
    rdq(V', BitVec.ofNat 64 (7940792 + 16 * k)) = BitVec.ofNat 64 (7940768 + 16 * k)

/-- After the prologue. -/
theorem lp0 {fb S rb : Addr} {V : Addr → Byte} (hs0 : 32 < S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hf0 : 8013232 + 24 ≤ fb.toNat) (hf1 : fb.toNat + 48 ≤ S.toNat - 32) :
    Lp fb S rb 0 V (Vst (Vst (Vst (Vst V (S - 8#64) (toBytesLE rb 8)) (S - 16#64)
      (toBytesLE rdq(Vst V (S - 8#64) (toBytesLE rb 8), fb + 40#64) 8)) (7940484#64) (toBytesLE (0#32) 4))
      (fb + 18446744073709551592#64) (toBytesLE (7940672#64) 8)) := by
  refine ⟨fun a ha hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [Wr, not_or] at hw
    repeat pv
  · pv
    pv
    rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl]
    pv
  · repeat pv
  · pv
    pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · repeat pv
  · pv
    rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- One more bin. -/
theorem Lp.step {fb S rb : Addr} {i : Nat} {V V' : Addr → Byte} (hs0 : 32 < S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hf0 : 8013232 + 24 ≤ fb.toNat) (hf1 : fb.toNat + 48 ≤ S.toNat - 32) (h : Lp fb S rb i V V') (hi : i < 127) :
    Lp fb S rb (i + 1) V (Vst (Vst V' (BitVec.ofNat 64 (7940784 + 16 * i))
      (toBytesLE (BitVec.ofNat 64 (7940768 + 16 * i)) 8)) (BitVec.ofNat 64 (7940792 + 16 * i))
      (toBytesLE (BitVec.ofNat 64 (7940768 + 16 * i)) 8)) := by
  refine ⟨fun a ha hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · have hw' := hw
    simp only [Wr, not_or] at hw'
    pv
    pv
    exact h.out a ha hw
  · pv
    pv
    exact h.can
  · pv
    pv
    exact h.gd
  · pv
    pv
    exact h.bp
  · pv
    pv
    exact h.ra
  · pv
    pv
    exact h.ini
  · pv
    pv
    exact h.tls
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · refine ⟨?_, ?_⟩
      · pv
        pv
        exact (h.bins k hk').1
      · pv
        pv
        exact (h.bins k hk').2
    · refine ⟨?_, ?_⟩
      · pv
        rw [vs (by ln) (by bv_omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _
      · rw [vs (by ln) (by bv_omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- What `ptmalloc_init` leaves, `__malloc_initialized` being `m`: the bytes outside the frame and `Wr` as at the
entry (`V`), `thread_arena = &main_arena`, the arena's flags 0, its `top` the first bin (`0x792aa0`),
`global_max_fast` 128, the 127 bins each with its two pointers to itself. -/
structure Dat (fb S : Addr) (m : BitVec 32) (V V' : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (S.toNat - 32 ≤ a.toNat ∧ a.toNat < S.toNat) → ¬ Wr fb a.toNat → V' a = V a
  ini : rdd(V', 7940484#64) = m
  tls : rdq(V', fb + 18446744073709551592#64) = 7940672#64
  flg : rdd(V', 7940680#64) = 0
  top : rdq(V', 7940768#64) = 7940768#64
  gmf : rdq(V', 8013224#64) = 128
  bins : ∀ k < 127, rdq(V', BitVec.ofNat 64 (7940784 + 16 * k)) = BitVec.ofNat 64 (7940768 + 16 * k) ∧
    rdq(V', BitVec.ofNat 64 (7940792 + 16 * k)) = BitVec.ofNat 64 (7940768 + 16 * k)

/-- After the loop and the three stores: the words, and the frame as the calls keep it (`Eli.Inv`). -/
theorem Lp.fin {fb S rb : Addr} {V V' Vd : Addr → Byte} (hs0 : 32 < S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hf0 : 8013232 + 24 ≤ fb.toNat) (hf1 : fb.toNat + 48 ≤ S.toNat - 32) (h : Lp fb S rb 127 V V')
    (hd : Vd = Vst (Vst (Vst V' (8013224#64) (toBytesLE (128#64) 8)) (7940680#64) (toBytesLE (0#32) 4))
      (7940768#64) (toBytesLE (7940768#64) 8)) :
    Dat fb S 0 V Vd ∧ Eli.Inv fb S rb Vd Vd ∧ rdq(Vd, S) = rdq(V, S) := by
  subst hd
  refine ⟨⟨fun a ha hw => ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ⟨?_, ?_⟩⟩, ⟨fun _ _ => rfl, ?_, ?_⟩, ?_⟩
  · have hw' := hw
    simp only [Wr, not_or] at hw'
    pv
    pv
    pv
    exact h.out a ha hw
  · pv
    pv
    pv
    exact h.ini
  · pv
    pv
    pv
    exact h.tls
  · pv
    rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · pv
    pv
    rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · pv
    pv
    pv
    exact (h.bins k hk).1
  · pv
    pv
    pv
    exact (h.bins k hk).2
  · repeat pv
    rw [h.can, h.gd]
  · pv
    pv
    pv
    exact h.bp
  · pv
    pv
    pv
    exact h.ra

/-- At the stack guard's check, after `__malloc_initialized := 1`. -/
theorem Dat.fin {fb S rb : Addr} {V Vd V₂ : Addr → Byte} (hs0 : 32 < S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64)
    (hf0 : 8013232 + 24 ≤ fb.toNat) (hf1 : fb.toNat + 48 ≤ S.toNat - 32) (h : Dat fb S 0 V Vd)
    (hI : Eli.Inv fb S rb Vd V₂) (hra : rdq(Vd, S) = rdq(V, S)) :
    Dat fb S 1 V (Vst V₂ (7940484#64) (toBytesLE (1#32) 4)) ∧
      rdq(Vst V₂ (7940484#64) (toBytesLE (1#32) 4), S - 16#64) =
        rdq(Vst V₂ (7940484#64) (toBytesLE (1#32) 4), fb + 40#64) ∧
      rdq(Vst V₂ (7940484#64) (toBytesLE (1#32) 4), S - 8#64) = rb ∧
      rdq(Vst V₂ (7940484#64) (toBytesLE (1#32) 4), S) = rdq(V, S) := by
  refine ⟨⟨fun a ha hw => ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · have hw' := hw
    simp only [Wr, not_or] at hw'
    pv
    exact (hI.out a ha).trans (h.out a ha hw)
  · rw [vs (by ln) (by decide)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans h.tls
  · pv
    exact (congrArg (ofBytesLE 32) (rd_out hI.out (by bv_omega) (by bv_omega))).trans h.flg
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans h.top
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans h.gmf
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans (h.bins k hk).1
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans (h.bins k hk).2
  · repeat pv
    rw [hI.can]
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).symm
  · pv
    exact hI.bp
  · pv
    exact (congrArg (ofBytesLE 64) (rd_out hI.out (by bv_omega) (by bv_omega))).trans hra

/-- A return address pushed and a tunable's 4 bytes stored: the frame as it was. -/
theorem stepd {fb S rb : Addr} {V₀ V : Addr → Byte} (hs : 32 < S.toNat) (h : Eli.Inv fb S rb V₀ V) (x : BitVec 64)
    (w : BitVec 32) : Eli.Inv fb S rb V₀ (Vst (Vst V (S - 32#64) (toBytesLE x 8)) (S - 24#64) (toBytesLE w 4)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · pv
    pv
    exact h.out a ha
  · pv
    pv
    exact h.can
  · pv
    pv
    exact h.bp

/-- A return address pushed and a tunable's 8 bytes stored: the frame as it was. -/
theorem stepq {fb S rb : Addr} {V₀ V : Addr → Byte} (hs : 32 < S.toNat) (h : Eli.Inv fb S rb V₀ V) (x y : BitVec 64) :
    Eli.Inv fb S rb V₀ (Vst (Vst V (S - 32#64) (toBytesLE x 8)) (S - 24#64) (toBytesLE y 8)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · pv
    pv
    exact h.out a ha
  · pv
    pv
    exact h.can
  · pv
    pv
    exact h.bp

/-! ## The loop over the bins -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- Bin `i`, from `movq xmm0, rax` to the loop's end: again (not the last), or past the three stores to the first
`call` (the last). -/
theorem bin_step {fb S rb : Addr} {V₀ V₁ : Addr → Byte} {G : Gprs} {Y : State} {i : Nat} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hE : Env F Wl L fb S) (hi : i < 127) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V₁) (hL : Lp fb S rb i V₀ V₁) (hr : Y.cpu.rip = pmi_at.add 64)
    (hax : Y.cpu.gpr.rax = BitVec.ofNat 64 (7940768 + 16 * i)) (hcx : Y.cpu.gpr.rcx = 7942800#64)
    (hdx : Y.cpu.gpr.rdx = 7940768#64) (hsp : Y.cpu.gpr.rsp = S - 24#64) (hsv : Eli.Sv G Y.cpu.gpr)
    (k₁ : i + 1 < 127 → ∀ V₂ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Lp fb S rb (i + 1) V₀ V₂ →
      Z.cpu.rip = pmi_at.add 64 → Z.cpu.gpr.rax = BitVec.ofNat 64 (7940768 + 16 * (i + 1)) →
      Z.cpu.gpr.rcx = 7942800#64 → Z.cpu.gpr.rdx = 7940768#64 → Z.cpu.gpr.rsp = S - 24#64 → Eli.Sv G Z.cpu.gpr →
      GoG prof L o gev gP gE Z t')
    (k₂ : i + 1 = 127 → ∀ Vd Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem Vd → Dat fb S 0 V₀ Vd →
      Eli.Inv fb S rb Vd Vd → rdq(Vd, S) = rdq(V₀, S) → Z.cpu.rip = pmi_at.add 131 → Z.cpu.gpr.rsp = S - 24#64 →
      Z.cpu.gpr.rbp = S - 24#64 → Z.cpu.gpr.rsi = S - 24#64 →
      BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rdi) = 25 → Eli.Sv G Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') : GoG prof L o gev gP gE Y t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hf0 := hE.f0
  have hf1 := hE.f1
  -- `movq xmm0, rax`
  refine c.s_movq_rx hK hA hE.code (lt_len (by decide)) hr (movq_64 _) ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁, hx₁, -⟩
  have hx₁' : xlo Y₁ 0 = (BitVec.ofNat 64 (7940768 + 16 * i)).setWidth 128 := by
    rw [hx₁]
    show (BitVec.setWidth 64 Y.cpu.gpr.rax).setWidth 128 = _
    rw [BitVec.setWidth_eq, hax]
  -- `add rax, 16`
  refine c.runB hE.code (blk_69 prof) rfl _ hK₁ hA₁ hr₁ vc_69 ?_
  rintro g fl V₂ ⟨rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hv₂
  -- `punpcklqdq xmm0, xmm0`
  refine c.s_punpcklqdq hK₂ hA₂ hE.code (lt_len (by decide)) hr₂ (punp_73 _) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hx₃, -⟩
  have hx₃' : xlo Y₃ 0 = BitVec.ofNat 64 (7940768 + 16 * i) ++ BitVec.ofNat 64 (7940768 + 16 * i) := by
    have h2 : xlo Y₂ 0 = (BitVec.ofNat 64 (7940768 + 16 * i)).setWidth 128 := by
      show (Y₂.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
      rw [hv₂]
      exact hx₁'
    rw [hx₃, h2, Cxa.lane_lo]
  have hg₃' : Y₃.cpu.gpr = { Y.cpu.gpr with rax := Y.cpu.gpr.rax + 16#64 } := by rw [hg₃, hg₂, hg₁]
  have hax₃ : Y₃.cpu.gpr.rax = BitVec.ofNat 64 (7940768 + 16 * (i + 1)) := by
    rw [hg₃']
    show Y.cpu.gpr.rax + 16#64 = _
    rw [hax]
    exact ad16 i
  have hcx₃ : Y₃.cpu.gpr.rcx = 7942800#64 := by rw [hg₃']; exact hcx
  have hdx₃ : Y₃.cpu.gpr.rdx = 7940768#64 := by rw [hg₃']; exact hdx
  have hsp₃ : Y₃.cpu.gpr.rsp = S - 24#64 := by rw [hg₃']; exact hsp
  have hsv₃ : Eli.Sv G Y₃.cpu.gpr := by rw [hg₃']; exact hsv
  -- `movaps [rax], xmm0`
  have ea : eaD Y₃ 0 0 = BitVec.ofNat 64 (7940784 + 16 * i) := by
    show Y₃.cpu.gpr.rax + BitVec.ofNat 64 0 = _
    rw [hax₃]
    exact ea16 i
  refine c.s_movaps_stv hK₃ hA₃ hE.code (lt_len (by decide)) hr₃ (movaps_77 _) (by rw [ea]; exact al16 i)
    (by rw [ea]; exact off_ft hE.bins (16 * i) (bn16 i) (by omega)) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, -⟩
  rw [ea, hx₃', st2] at hA₄
  have hL₄ := hL.step hs0 hs8 hf0 hf1 hi
  -- the loop's end
  refine (c_80 prof fb).run c hfs hE.code _ hK₄ hA₄ hr₄ (vc_80 hE.gmf hE.flg hE.top) ?_
  rintro j' g fl V₅ (⟨rfl, hne, rfl, rfl⟩ | ⟨rfl, heq, rfl, rfl⟩) Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  · rw [hg₄, hax₃, hcx₃] at hne
    have hlt : i + 1 < 127 := by
      rcases Nat.lt_or_ge (i + 1) 127 with h | h
      · exact h
      · have e : i = 126 := by omega
        subst e
        exact absurd rfl hne
    refine k₁ hlt _ Y₅ t₅ hK₅ hA₅ hL₄ hr₅ ?_ ?_ ?_ ?_ ?_
    · rw [hg₅, hg₄]; exact hax₃
    · rw [hg₅, hg₄]; exact hcx₃
    · rw [hg₅, hg₄]; exact hdx₃
    · rw [hg₅, hg₄]; exact hsp₃
    · rw [hg₅, hg₄]; exact hsv₃
  · rw [hg₄, hax₃, hcx₃] at heq
    rw [hg₄, hdx₃] at hA₅
    have e127 := eq127 hi heq
    rw [e127] at hL₄
    obtain ⟨hD, hI, hra⟩ := hL₄.fin hs0 hs8 hf0 hf1 rfl
    refine k₂ e127 _ Y₅ t₅ hK₅ hA₅ hD hI hra hr₅ ?_ ?_ ?_ ?_ ?_
    · rw [hg₅, hg₄]; exact hsp₃
    · rw [hg₅, hg₄]; exact hsp₃
    · rw [hg₅, hg₄]; exact hsp₃
    · rw [hg₅]; rfl
    · rw [hg₅, hg₄]; exact hsv₃

/-- The loop from bin `i`, `n` more after it, to the first `call`. -/
theorem bins_go {fb S rb : Addr} {V₀ : Addr → Byte} {G : Gprs} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hE : Env F Wl L fb S)
    (k : ∀ Vd Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem Vd → Dat fb S 0 V₀ Vd →
      Eli.Inv fb S rb Vd Vd → rdq(Vd, S) = rdq(V₀, S) → Z.cpu.rip = pmi_at.add 131 → Z.cpu.gpr.rsp = S - 24#64 →
      Z.cpu.gpr.rbp = S - 24#64 → Z.cpu.gpr.rsi = S - 24#64 →
      BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rdi) = 25 → Eli.Sv G Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    ∀ (n i : Nat), i + n = 126 → ∀ {Y : State} {t : Nat} {V₁ : Addr → Byte}, KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V₁ → Lp fb S rb i V₀ V₁ → Y.cpu.rip = pmi_at.add 64 →
      Y.cpu.gpr.rax = BitVec.ofNat 64 (7940768 + 16 * i) → Y.cpu.gpr.rcx = 7942800#64 →
      Y.cpu.gpr.rdx = 7940768#64 → Y.cpu.gpr.rsp = S - 24#64 → Eli.Sv G Y.cpu.gpr →
      GoG prof L o gev gP gE Y t := by
  intro n
  induction n with
  | zero =>
    intro i hi Y t V₁ hK hA hL hr hax hcx hdx hsp hsv
    exact bin_step c hfs hE (by omega) hK hA hL hr hax hcx hdx hsp hsv (fun h => absurd h (by omega)) (fun _ => k)
  | succ m ih =>
    intro i hi Y t V₁ hK hA hL hr hax hcx hdx hsp hsv
    exact bin_step c hfs hE (by omega) hK hA hL hr hax hcx hdx hsp hsv
      (fun _ V₂ Z t' hK' hA' hL' hr' hax' hcx' hdx' hsp' hsv' =>
        ih (i + 1) (by omega) hK' hA' hL' hr' hax' hcx' hdx' hsp' hsv')
      (fun h => absurd h (by omega))

/-! ## The calls -/

/-- One call `__tunable_get_val (d, &v, callback)` for a tunable not set, of type `INT_32` or another, from the
`call` at `jc` to the instruction after it: the frame kept. -/
theorem tcall {fb S rb d : Addr} {V₀ V₁ : Addr → Byte} {Y : State} {jc r : Nat} (c : Seg prof F Wl L s₀ o)
    (hE : Env F Wl L fb S) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hI : Eli.Inv fb S rb V₀ V₁)
    (hU : Tgv.Unset F V₀ d ∨ Tgv.UnsetW F V₀ d) (hdl : (Tgv.ent d).toNat + 48 ≤ 7940484) (hjc : jc + 5 < 393)
    (hr : Y.cpu.rip = pmi_at.add jc) (hdec : Dec prof.feat pmi jc (FV7z.mk .call 64 [.rel r] 5))
    (htgt : pmi_at.add (jc + 5) + BitVec.ofNat 64 r = Tgv.tgv_at)
    (hsp : Y.cpu.gpr.rsp = S - 24#64) (hsi : Y.cpu.gpr.rsi = S - 24#64) (hbp : Y.cpu.gpr.rbp = S - 24#64)
    (hdi : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rdi) = d)
    (k : ∀ V₂ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Eli.Inv fb S rb V₀ V₂ →
      Z.cpu.rip = pmi_at.add (jc + 5) → Z.cpu.gpr.rsp = S - 24#64 → Z.cpu.gpr.rbp = S - 24#64 →
      Eli.Sv Y.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') : GoG prof L o gev gP gE Y t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hf0 := hE.f0
  have hf1 := hE.f1
  obtain ⟨n32, n20, n16, n8⟩ := Eli.tn hs0
  have n24 := tn24 hs0
  have n40 := Eli.en (d := d) (by omega)
  refine c.s_call hK hA hE.code (lt_len (by omega)) hr hdec hE.tcode (Tgv.lt_len (by decide)) htgt
    (fun i hi => ?_) ?_
  · rw [hsp, Eli.a_ra]
    exact off_ft hE.st 0 (Eli.b_ra S) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp, Eli.a_ra] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = S - 32#64 := by rw [hg₂]; rfl
  have hsi₂ : Y₂.cpu.gpr.rsi = S - 24#64 := by rw [hg₂]; exact hsi
  have hpush := hI.push hs0 (pmi_at.add (jc + 5))
  rcases hU with hU | hU
  · have hU₁ := hU.out (lo := S.toNat - 32) (hi := S.toNat) (by omega) (by omega) hpush
    refine Tgv.tgv32_ok (d := d) c hE.tcode hK₂ hA₂ hr₂ (by rw [hg₂]; exact hdi) hU₁.ty hU₁.va hU₁.ini hU₁.t0 hU₁.z
      (fun i hi => ?_) (by rw [hsi₂]; omega) (by rw [hsi₂]; omega) (fun i hi => ?_) hE.code (j₂ := jc + 5)
      (lt_len hjc) (by rw [hsp₂]; exact Eli.rd_ra hs0 _) (by rw [hsp₂]; omega) (by rw [hsp₂, hsi₂]; omega) ?_
    · rw [hsi₂]
      exact off_ft hE.st 8 (b24 S) (by decide) i hi
    · rw [hsp₂]
      exact c.hws _ (off_ft hE.st 0 (Eli.b_ra S) (by decide) i hi)
    intro g₃ Z t₃ hK₃ hA₃ hr₃ hg₃ hbk₃
    rw [hsi₂] at hA₃
    refine k _ Z t₃ hK₃ hA₃ (stepd hs0 hI _ _) hr₃ ?_ ?_ ?_
    · rw [hg₃, hbk₃.1, hsp₂]
      exact Eli.a_bk S
    · rw [hg₃, hbk₃.2.2.1, hg₂]
      exact hbp
    · rw [hg₃]
      obtain ⟨-, k1, -, k3, k4, k5, k6⟩ := hbk₃
      rw [hg₂] at k1 k3 k4 k5 k6
      exact ⟨k1, k3, k4, k5, k6⟩
  · have hU₁ := hU.out (lo := S.toNat - 32) (hi := S.toNat) (by omega) (by omega) hpush
    refine Tgv.tgv64_ok (d := d) c hE.tcode hK₂ hA₂ hr₂ (by rw [hg₂]; exact hdi) hU₁.ty hU₁.va hU₁.ini hU₁.tw hU₁.z
      (fun i hi => ?_) (by rw [hsi₂]; omega) (by rw [hsi₂]; omega) (fun i hi => ?_) hE.code (j₂ := jc + 5)
      (lt_len hjc) (by rw [hsp₂]; exact Eli.rd_ra hs0 _) (by rw [hsp₂]; omega) (by rw [hsp₂, hsi₂]; omega) ?_
    · rw [hsi₂]
      exact off_ft hE.st 8 (b24 S) (by decide) i hi
    · rw [hsp₂]
      exact c.hws _ (off_ft hE.st 0 (Eli.b_ra S) (by decide) i hi)
    intro g₃ Z t₃ hK₃ hA₃ hr₃ hg₃ hbk₃
    rw [hsi₂] at hA₃
    refine k _ Z t₃ hK₃ hA₃ (stepq hs0 hI _ _) hr₃ ?_ ?_ ?_
    · rw [hg₃, hbk₃.1, hsp₂]
      exact Eli.a_bk S
    · rw [hg₃, hbk₃.2.2.1, hg₂]
      exact hbp
    · rw [hg₃]
      obtain ⟨-, k1, -, k3, k4, k5, k6⟩ := hbk₃
      rw [hg₂] at k1 k3 k4 k5 k6
      exact ⟨k1, k3, k4, k5, k6⟩

/-! ## The whole -/

/-- The `glibc.malloc.*` tunables of type `INT_32`: `perturb`, `check`, `mmap_threshold`. -/
def t32 : List Addr := [25, 2, 12]

/-- Those of type `SIZE_T`: `mmap_max`, `top_pad`, `arena_max`, `trim_threshold`, `arena_test`, `tcache_max`,
`tcache_count`, `tcache_unsorted_limit`, `mxfast`. -/
def t64 : List Addr := [8, 19, 1, 18, 22, 24, 21, 14, 6]

/-- `ptmalloc_init` with the twelve `glibc.malloc.*` tunables not set: the run reaches the return address, the
registers a call keeps as at the entry, the bytes outside its 32 and `Wr` as they were, the words stored as `Dat`
says, `__malloc_initialized` 1. -/
theorem pmi_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hE : Env F Wl L fb X.cpu.gpr.rsp) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pmi_at) (h32 : ∀ d ∈ t32, Tgv.Unset F V d) (h64 : ∀ d ∈ t64, Tgv.UnsetW F V d)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat fb X.cpu.gpr.rsp 1 V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have hf0 := hE.f0
  have hf1 := hE.f1
  -- the prologue
  refine (c_0 prof fb).run c hfs hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (off_ft hE.st 24 (Eli.b_bp _) (by decide)) hE.fl
      (by rw [Eli.a_can]; exact off_ft hE.st 16 (Eli.b_can _) (by decide)) hE.ini hE.tl) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [Eli.a_can, show X.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 from rfl] at hA₁
  have hL₁ : Lp fb X.cpu.gpr.rsp X.cpu.gpr.rbp 0 V _ := lp0 hs0 hs8 hf0 hf1
  -- the bins
  refine bins_go (G := X.cpu.gpr) c hfs hE ?_ 126 0 rfl hK₁ hA₁ hL₁ hr₁ (by rw [hg₁]) (by rw [hg₁])
    (by rw [hg₁]) (by rw [hg₁]; exact Eli.a_sp _) (by rw [hg₁]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  intro Vd Y0 t0 hK0 hA0 hD hI0 hraD hr0 hsp0 hbp0 hsi0 hdi0 sv0
  have ho : ∀ a : Addr, ¬ (7940484 ≤ a.toNat ∧ a.toNat < 2 ^ 64) → Vd a = V a := fun a ha =>
    hD.out a (by omega) (by unfold Wr; omega)
  have u32 : ∀ d ∈ t32, (Tgv.ent d).toNat + 48 ≤ 7940484 → Tgv.Unset F Vd d ∨ Tgv.UnsetW F Vd d :=
    fun d hd hl => .inl ((h32 d hd).out hl (by decide) ho)
  have u64 : ∀ d ∈ t64, (Tgv.ent d).toNat + 48 ≤ 7940484 → Tgv.Unset F Vd d ∨ Tgv.UnsetW F Vd d :=
    fun d hd hl => .inr ((h64 d hd).out hl (by decide) ho)
  -- `glibc.malloc.perturb`
  refine tcall (d := 25) c hE hK0 hA0 hI0 (u32 25 (by decide) (by decide)) (by decide) (by decide) hr0
    (call_131 _) (by decide) hsp0 hsi0 hbp0 hdi0 ?_
  intro V1 Y1 t1 hK1 hA1 hI1 hr1 hsp1 hbp1 s1
  have sv1 : Eli.Sv X.cpu.gpr Y1.cpu.gpr := sv0.trans s1
  refine (c_136 prof fb).run c hfs hE.code _ hK1 hA1 hr1 vc_136 ?_
  rintro j' g fl V2 ⟨rfl, rfl, rfl⟩ Y2 t2 hK2 hA2 hr2 hg2 -
  have hI2 := hI1
  have hsp2 : Y2.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg2]; exact hsp1
  have hbp2 : Y2.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg2]; exact hbp1
  have hsi2 : Y2.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg2]; exact hbp1
  have hdi2 : BitVec.setWidth 64 (BitVec.setWidth 32 Y2.cpu.gpr.rdi) = 8 := by rw [hg2]; rfl
  have sv2 : Eli.Sv X.cpu.gpr Y2.cpu.gpr := by rw [hg2]; exact sv1
  -- `glibc.malloc.mmap_max`
  refine tcall (d := 8) c hE hK2 hA2 hI2 (u64 8 (by decide) (by decide)) (by decide) (by decide) hr2
    (call_151 _) (by decide) hsp2 hsi2 hbp2 hdi2 ?_
  intro V3 Y3 t3 hK3 hA3 hI3 hr3 hsp3 hbp3 s3
  have sv3 : Eli.Sv X.cpu.gpr Y3.cpu.gpr := sv2.trans s3
  refine (c_156 prof fb).run c hfs hE.code _ hK3 hA3 hr3 vc_156 ?_
  rintro j' g fl V4 ⟨rfl, rfl, rfl⟩ Y4 t4 hK4 hA4 hr4 hg4 -
  have hI4 := hI3
  have hsp4 : Y4.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg4]; exact hsp3
  have hbp4 : Y4.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg4]; exact hbp3
  have hsi4 : Y4.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg4]; exact hbp3
  have hdi4 : BitVec.setWidth 64 (BitVec.setWidth 32 Y4.cpu.gpr.rdi) = 2 := by rw [hg4]; rfl
  have sv4 : Eli.Sv X.cpu.gpr Y4.cpu.gpr := by rw [hg4]; exact sv3
  -- `glibc.malloc.check`
  refine tcall (d := 2) c hE hK4 hA4 hI4 (u32 2 (by decide) (by decide)) (by decide) (by decide) hr4
    (call_171 _) (by decide) hsp4 hsi4 hbp4 hdi4 ?_
  intro V5 Y5 t5 hK5 hA5 hI5 hr5 hsp5 hbp5 s5
  have sv5 : Eli.Sv X.cpu.gpr Y5.cpu.gpr := sv4.trans s5
  refine (c_176 prof fb).run c hfs hE.code _ hK5 hA5 hr5 vc_176 ?_
  rintro j' g fl V6 ⟨rfl, rfl, rfl⟩ Y6 t6 hK6 hA6 hr6 hg6 -
  have hI6 := hI5
  have hsp6 : Y6.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg6]; exact hsp5
  have hbp6 : Y6.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg6]; exact hbp5
  have hsi6 : Y6.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg6]; exact hbp5
  have hdi6 : BitVec.setWidth 64 (BitVec.setWidth 32 Y6.cpu.gpr.rdi) = 19 := by rw [hg6]; rfl
  have sv6 : Eli.Sv X.cpu.gpr Y6.cpu.gpr := by rw [hg6]; exact sv5
  -- `glibc.malloc.top_pad`
  refine tcall (d := 19) c hE hK6 hA6 hI6 (u64 19 (by decide) (by decide)) (by decide) (by decide) hr6
    (call_191 _) (by decide) hsp6 hsi6 hbp6 hdi6 ?_
  intro V7 Y7 t7 hK7 hA7 hI7 hr7 hsp7 hbp7 s7
  have sv7 : Eli.Sv X.cpu.gpr Y7.cpu.gpr := sv6.trans s7
  refine (c_196 prof fb).run c hfs hE.code _ hK7 hA7 hr7 vc_196 ?_
  rintro j' g fl V8 ⟨rfl, rfl, rfl⟩ Y8 t8 hK8 hA8 hr8 hg8 -
  have hI8 := hI7
  have hsp8 : Y8.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg8]; exact hsp7
  have hbp8 : Y8.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg8]; exact hbp7
  have hsi8 : Y8.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg8]; exact hbp7
  have hdi8 : BitVec.setWidth 64 (BitVec.setWidth 32 Y8.cpu.gpr.rdi) = 1 := by rw [hg8]; rfl
  have sv8 : Eli.Sv X.cpu.gpr Y8.cpu.gpr := by rw [hg8]; exact sv7
  -- `glibc.malloc.arena_max`
  refine tcall (d := 1) c hE hK8 hA8 hI8 (u64 1 (by decide) (by decide)) (by decide) (by decide) hr8
    (call_211 _) (by decide) hsp8 hsi8 hbp8 hdi8 ?_
  intro V9 Y9 t9 hK9 hA9 hI9 hr9 hsp9 hbp9 s9
  have sv9 : Eli.Sv X.cpu.gpr Y9.cpu.gpr := sv8.trans s9
  refine (c_216 prof fb).run c hfs hE.code _ hK9 hA9 hr9 vc_216 ?_
  rintro j' g fl V10 ⟨rfl, rfl, rfl⟩ Y10 t10 hK10 hA10 hr10 hg10 -
  have hI10 := hI9
  have hsp10 : Y10.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg10]; exact hsp9
  have hbp10 : Y10.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg10]; exact hbp9
  have hsi10 : Y10.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg10]; exact hbp9
  have hdi10 : BitVec.setWidth 64 (BitVec.setWidth 32 Y10.cpu.gpr.rdi) = 12 := by rw [hg10]; rfl
  have sv10 : Eli.Sv X.cpu.gpr Y10.cpu.gpr := by rw [hg10]; exact sv9
  -- `glibc.malloc.mmap_threshold`
  refine tcall (d := 12) c hE hK10 hA10 hI10 (u32 12 (by decide) (by decide)) (by decide) (by decide) hr10
    (call_231 _) (by decide) hsp10 hsi10 hbp10 hdi10 ?_
  intro V11 Y11 t11 hK11 hA11 hI11 hr11 hsp11 hbp11 s11
  have sv11 : Eli.Sv X.cpu.gpr Y11.cpu.gpr := sv10.trans s11
  refine (c_236 prof fb).run c hfs hE.code _ hK11 hA11 hr11 vc_236 ?_
  rintro j' g fl V12 ⟨rfl, rfl, rfl⟩ Y12 t12 hK12 hA12 hr12 hg12 -
  have hI12 := hI11
  have hsp12 : Y12.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg12]; exact hsp11
  have hbp12 : Y12.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg12]; exact hbp11
  have hsi12 : Y12.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg12]; exact hbp11
  have hdi12 : BitVec.setWidth 64 (BitVec.setWidth 32 Y12.cpu.gpr.rdi) = 18 := by rw [hg12]; rfl
  have sv12 : Eli.Sv X.cpu.gpr Y12.cpu.gpr := by rw [hg12]; exact sv11
  -- `glibc.malloc.trim_threshold`
  refine tcall (d := 18) c hE hK12 hA12 hI12 (u64 18 (by decide) (by decide)) (by decide) (by decide) hr12
    (call_251 _) (by decide) hsp12 hsi12 hbp12 hdi12 ?_
  intro V13 Y13 t13 hK13 hA13 hI13 hr13 hsp13 hbp13 s13
  have sv13 : Eli.Sv X.cpu.gpr Y13.cpu.gpr := sv12.trans s13
  refine (c_256 prof fb).run c hfs hE.code _ hK13 hA13 hr13 vc_256 ?_
  rintro j' g fl V14 ⟨rfl, rfl, rfl⟩ Y14 t14 hK14 hA14 hr14 hg14 -
  have hI14 := hI13
  have hsp14 : Y14.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg14]; exact hsp13
  have hbp14 : Y14.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg14]; exact hbp13
  have hsi14 : Y14.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg14]; exact hbp13
  have hdi14 : BitVec.setWidth 64 (BitVec.setWidth 32 Y14.cpu.gpr.rdi) = 22 := by rw [hg14]; rfl
  have sv14 : Eli.Sv X.cpu.gpr Y14.cpu.gpr := by rw [hg14]; exact sv13
  -- `glibc.malloc.arena_test`
  refine tcall (d := 22) c hE hK14 hA14 hI14 (u64 22 (by decide) (by decide)) (by decide) (by decide) hr14
    (call_271 _) (by decide) hsp14 hsi14 hbp14 hdi14 ?_
  intro V15 Y15 t15 hK15 hA15 hI15 hr15 hsp15 hbp15 s15
  have sv15 : Eli.Sv X.cpu.gpr Y15.cpu.gpr := sv14.trans s15
  refine (c_276 prof fb).run c hfs hE.code _ hK15 hA15 hr15 vc_276 ?_
  rintro j' g fl V16 ⟨rfl, rfl, rfl⟩ Y16 t16 hK16 hA16 hr16 hg16 -
  have hI16 := hI15
  have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg16]; exact hsp15
  have hbp16 : Y16.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg16]; exact hbp15
  have hsi16 : Y16.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg16]; exact hbp15
  have hdi16 : BitVec.setWidth 64 (BitVec.setWidth 32 Y16.cpu.gpr.rdi) = 24 := by rw [hg16]; rfl
  have sv16 : Eli.Sv X.cpu.gpr Y16.cpu.gpr := by rw [hg16]; exact sv15
  -- `glibc.malloc.tcache_max`
  refine tcall (d := 24) c hE hK16 hA16 hI16 (u64 24 (by decide) (by decide)) (by decide) (by decide) hr16
    (call_291 _) (by decide) hsp16 hsi16 hbp16 hdi16 ?_
  intro V17 Y17 t17 hK17 hA17 hI17 hr17 hsp17 hbp17 s17
  have sv17 : Eli.Sv X.cpu.gpr Y17.cpu.gpr := sv16.trans s17
  refine (c_296 prof fb).run c hfs hE.code _ hK17 hA17 hr17 vc_296 ?_
  rintro j' g fl V18 ⟨rfl, rfl, rfl⟩ Y18 t18 hK18 hA18 hr18 hg18 -
  have hI18 := hI17
  have hsp18 : Y18.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg18]; exact hsp17
  have hbp18 : Y18.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg18]; exact hbp17
  have hsi18 : Y18.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg18]; exact hbp17
  have hdi18 : BitVec.setWidth 64 (BitVec.setWidth 32 Y18.cpu.gpr.rdi) = 21 := by rw [hg18]; rfl
  have sv18 : Eli.Sv X.cpu.gpr Y18.cpu.gpr := by rw [hg18]; exact sv17
  -- `glibc.malloc.tcache_count`
  refine tcall (d := 21) c hE hK18 hA18 hI18 (u64 21 (by decide) (by decide)) (by decide) (by decide) hr18
    (call_311 _) (by decide) hsp18 hsi18 hbp18 hdi18 ?_
  intro V19 Y19 t19 hK19 hA19 hI19 hr19 hsp19 hbp19 s19
  have sv19 : Eli.Sv X.cpu.gpr Y19.cpu.gpr := sv18.trans s19
  refine (c_316 prof fb).run c hfs hE.code _ hK19 hA19 hr19 vc_316 ?_
  rintro j' g fl V20 ⟨rfl, rfl, rfl⟩ Y20 t20 hK20 hA20 hr20 hg20 -
  have hI20 := hI19
  have hsp20 : Y20.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg20]; exact hsp19
  have hbp20 : Y20.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg20]; exact hbp19
  have hsi20 : Y20.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg20]; exact hbp19
  have hdi20 : BitVec.setWidth 64 (BitVec.setWidth 32 Y20.cpu.gpr.rdi) = 14 := by rw [hg20]; rfl
  have sv20 : Eli.Sv X.cpu.gpr Y20.cpu.gpr := by rw [hg20]; exact sv19
  -- `glibc.malloc.tcache_unsorted_limit`
  refine tcall (d := 14) c hE hK20 hA20 hI20 (u64 14 (by decide) (by decide)) (by decide) (by decide) hr20
    (call_331 _) (by decide) hsp20 hsi20 hbp20 hdi20 ?_
  intro V21 Y21 t21 hK21 hA21 hI21 hr21 hsp21 hbp21 s21
  have sv21 : Eli.Sv X.cpu.gpr Y21.cpu.gpr := sv20.trans s21
  refine (c_336 prof fb).run c hfs hE.code _ hK21 hA21 hr21 vc_336 ?_
  rintro j' g fl V22 ⟨rfl, rfl, rfl⟩ Y22 t22 hK22 hA22 hr22 hg22 -
  have hI22 := hI21
  have hsp22 : Y22.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg22]; exact hsp21
  have hbp22 : Y22.cpu.gpr.rbp = X.cpu.gpr.rsp - 24#64 := by rw [hg22]; exact hbp21
  have hsi22 : Y22.cpu.gpr.rsi = X.cpu.gpr.rsp - 24#64 := by rw [hg22]; exact hbp21
  have hdi22 : BitVec.setWidth 64 (BitVec.setWidth 32 Y22.cpu.gpr.rdi) = 6 := by rw [hg22]; rfl
  have sv22 : Eli.Sv X.cpu.gpr Y22.cpu.gpr := by rw [hg22]; exact sv21
  -- `glibc.malloc.mxfast`
  refine tcall (d := 6) c hE hK22 hA22 hI22 (u64 6 (by decide) (by decide)) (by decide) (by decide) hr22
    (call_351 _) (by decide) hsp22 hsi22 hbp22 hdi22 ?_
  intro V23 Y23 t23 hK23 hA23 hI23 hr23 hsp23 hbp23 s23
  have sv23 : Eli.Sv X.cpu.gpr Y23.cpu.gpr := sv22.trans s23
  -- `__malloc_initialized := 1`, the stack guard's check, the epilogue
  obtain ⟨hD₁, hcn, hbq, hrq⟩ := hD.fin hs0 hs8 hf0 hf1 hI23 hraD
  refine (c_356 prof fb).run c hfs hE.code _ hK23 hA23 hr23
    (vc_356 hE.ini (fun i hi => ?_) hE.fl ?_ (fun i hi => ?_)) ?_
  · rw [hsp23, Eli.e_can]
    exact c.hws _ (off_ft hE.st 16 (Eli.b_can _) (by decide) i hi)
  · rw [hsp23, Eli.e_can]
    exact hcn
  · rw [hsp23, Eli.e_bp]
    exact c.hws _ (off_ft hE.st 24 (Eli.b_bp _) (by decide) i hi)
  rintro j' g fl Vc ⟨rfl, rfl, rfl⟩ Yc tc hKc hAc hrc hgc -
  have hspc : Yc.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hgc]
    show Y23.cpu.gpr.rsp + 16#64 + 8 = _
    rw [hsp23, Eli.e_bp]
    exact Eli.e_sp _
  have hbpc : Yc.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hgc]
    show rdq(_, Y23.cpu.gpr.rsp + 16#64) = _
    rw [hsp23, Eli.e_bp]
    exact hbq
  have sc : Eli.Sv X.cpu.gpr Yc.cpu.gpr := by rw [hgc]; exact sv23
  refine c.s_ret hKc hAc hE.code (lt_len (by decide)) hrc (ret_387 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hspc]
    exact hE.lr i hi
  · rw [hspc, hrq]
    exact hra
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hD₁ hrZ ?_
  rw [hgZ]
  refine ⟨?_, sc.1, hbpc, sc.2.1, sc.2.2.1, sc.2.2.2.1, sc.2.2.2.2⟩
  show Yc.cpu.gpr.rsp + 8 = _
  rw [hspc]
  rfl

end FV7z.Pmi
