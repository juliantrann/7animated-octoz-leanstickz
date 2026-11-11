import FV7z.Csu.Cuts
import FV7z.Lemmas.CallX
import FV7z.Nef.Holds
/-!
# `__libc_csu_init` calls the initializers in order (PLAN.md G3, startup)

glibc 2.31's `__libc_csu_init (argc, argv, envp)` at `0x613ca0` in `7zzs` (`csu/elf-init.c`), which
`__libc_start_main` calls before `main`: the one entry of `.preinit_array` (`0x777798`), `_init` (`0x401000`), then
the 102 entries of `.init_array` (`0x7777a0` to `0x777ad0`: `frame_dummy` and the static constructors of 7-Zip), each
entry through `call *(%r15,%rbx,8)` with `(argc, argv, envp)`.

The theorem is the function's frame: what the 104 functions do is a hypothesis (`Runs`), in the form the theorems of
this proof have for a function (from its entry, with the return address in the stack, to that address), with an
invariant `I k` of the bytes after `k` of them.

- `callx_64`, `call_91`, `callx_120`, `ret_147`: the instructions outside the blocks.
- `Rg`, `Fr`, `prV`, `pr_fr`: the registers and the stack of the frame.
- `vc_0`, `vc_56`, `vc_68`, `vc_77`, `vc_96`, `vc_112`, `vc_124`, `vc_133`: the verification conditions of the pieces.
- `Env`, `St`: what is around the call, and the bytes the frame reads.
- `Runs`: what the frame asks of a function it calls.
- `enter`: a function's run, from the state its `call` left; `fin`: the frame's end; `lpHead`, `lpAll`: the loop
  over `.init_array`, by the number of entries left.
- `csu_ok`: the run reaches the return address with the registers a call keeps as at the entry and `I 104`.

The counts are the file's: one entry in `.preinit_array` and 102 in `.init_array` (`vc_0`, `vc_96` compute them from
the arrays' bounds in the code).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out sk0')
open FV7z.Raf (Out off_ft rd_out2)
namespace FV7z.Csu

/-- `call *(%r15,%rbx,8)`. -/
def pcx : List Byte := [0x41, 0xff, 0x14, 0xdf]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (FV7z.mk .call 64 [.mem (msi (some 15) 3 8 0 64)] 4) := by dec_rfl
theorem w_64 : pcx <+: csu.drop 64 := by decide +kernel
theorem callx_64 (feat : Features) : Dec feat csu 64 (FV7z.mk .call 64 [.mem (msi (some 15) 3 8 0 64)] 4) :=
  Dec.shift (j := 64) (k := 0) (pcx_0 feat) w_64 (Nat.zero_le _)
theorem w_120 : pcx <+: csu.drop 120 := by decide +kernel
theorem callx_120 (feat : Features) : Dec feat csu 120 (FV7z.mk .call 64 [.mem (msi (some 15) 3 8 0 64)] 4) :=
  Dec.shift (j := 120) (k := 0) (pcx_0 feat) w_120 (Nat.zero_le _)

/-- `call _init`. -/
def pcl : List Byte := [0xe8, 0x00, 0xd3, 0xde, 0xff]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 18446744073707377408] 5) := by dec_rfl
theorem w_91 : pcl <+: csu.drop 91 := by decide +kernel
theorem call_91 (feat : Features) : Dec feat csu 91 (FV7z.mk .call 64 [.rel 18446744073707377408] 5) :=
  Dec.shift (j := 91) (k := 0) (pcl_0 feat) w_91 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_147 : pret <+: csu.drop 147 := by decide +kernel
theorem ret_147 (feat : Features) : Dec feat csu 147 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 147) (k := 0) (pret_0 feat) w_147 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-! ## The frame -/

/-- The registers between the frame's push and its pop: `rbx` the index `i`, `r14` the number `n` of entries, `r15`
the array `q`, and the three arguments. -/
structure Rg (g₀ g : Gprs) (i n q : BitVec 64) : Prop where
  rsp : g.rsp = g₀.rsp - 56#64
  rbx : g.rbx = i
  rbp : g.rbp = (g₀.rdi.setWidth 32).setWidth 64
  r12 : g.r12 = g₀.rsi
  r13 : g.r13 = g₀.rdx
  r14 : g.r14 = n
  r15 : g.r15 = q

/-- The stack after the six pushes. -/
abbrev prV (V : Addr → Byte) (sp : Addr) (b bp r12 r13 r14 r15 : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (sp - 8) (toBytesLE r15 8)) (sp - 8 - 8) (toBytesLE r14 8)) (sp - 8 - 8 - 8)
    (toBytesLE r13 8)) (sp - 8 - 8 - 8 - 8) (toBytesLE r12 8)) (sp - 8 - 8 - 8 - 8 - 8) (toBytesLE bp 8))
    (sp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE b 8)

/-- The saved registers in the stack. -/
structure Fr (V : Addr → Byte) (sp : Addr) (g₀ : Gprs) : Prop where
  r15 : rdq(V, sp - 8#64) = g₀.r15
  r14 : rdq(V, sp - 16#64) = g₀.r14
  r13 : rdq(V, sp - 24#64) = g₀.r13
  r12 : rdq(V, sp - 32#64) = g₀.r12
  rbp : rdq(V, sp - 40#64) = g₀.rbp
  rbx : rdq(V, sp - 48#64) = g₀.rbx

/-- Bytes in a range where `V'` is `V`. -/
theorem rd_in {V V' : Addr → Byte} {lo hi : Nat} (h : ∀ a : Addr, lo ≤ a.toNat ∧ a.toNat < hi → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_
  rw [toNat_add_of_fits hj hx]
  omega

/-- The addresses of the frame. -/
theorem sp_c (sp : Addr) (h : 64 ≤ sp.toNat) :
    (sp - 8#64).toNat = sp.toNat - 8 ∧ (sp - 16#64).toNat = sp.toNat - 16 ∧ (sp - 24#64).toNat = sp.toNat - 24 ∧
    (sp - 32#64).toNat = sp.toNat - 32 ∧ (sp - 40#64).toNat = sp.toNat - 40 ∧ (sp - 48#64).toNat = sp.toNat - 48 ∧
    (sp - 56#64).toNat = sp.toNat - 56 ∧ (sp - 64#64).toNat = sp.toNat - 64 ∧ sp - 56#64 - 8 = sp - 64#64 ∧
    sp - 64#64 + 8#64 = sp - 56#64 ∧ sp - 56#64 + 56#64 = sp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The addresses of the pushes. -/
theorem sp_e (sp : Addr) : sp - 8 - 8 = sp - 16#64 ∧ sp - 16#64 - 8 = sp - 24#64 ∧ sp - 24#64 - 8 = sp - 32#64 ∧
    sp - 32#64 - 8 = sp - 40#64 ∧ sp - 40#64 - 8 = sp - 48#64 ∧ sp - 48#64 - 8#64 = sp - 56#64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The pops' addresses. -/
theorem sp_g (sp : Addr) : sp - 56#64 + 8#64 = sp - 48#64 ∧ sp - 56#64 + 16#64 = sp - 40#64 ∧
    sp - 56#64 + 24#64 = sp - 32#64 ∧ sp - 56#64 + 32#64 = sp - 24#64 ∧ sp - 56#64 + 40#64 = sp - 16#64 ∧
    sp - 56#64 + 48#64 = sp - 8#64 ∧ sp - 56#64 + 56#64 = sp ∧
    sp - 56#64 + 8#64 = sp - 64#64 + BitVec.ofNat 64 16 ∧ sp - 48#64 = sp - 64#64 + BitVec.ofNat 64 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Entry `k` of `.init_array`. -/
theorem ar_i (k : Nat) (hk : k < 102) :
    (BitVec.ofNat 64 (7829408 + 8 * k)).toNat = 7829408 + 8 * k ∧
    7829408#64 + BitVec.ofNat 64 k * 8#64 + 0#64 = BitVec.ofNat 64 (7829408 + 8 * k) ∧
    BitVec.ofNat 64 (7829408 + 8 * k) = 7829400#64 + BitVec.ofNat 64 (8 + 8 * k) := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

/-- The pushes' addresses in the 48 bytes under the stack pointer. -/
theorem sp_f (sp : Addr) : sp - 8 = sp - 48#64 + BitVec.ofNat 64 40 ∧ sp - 8 - 8 = sp - 48#64 + BitVec.ofNat 64 32 ∧
    sp - 8 - 8 - 8 = sp - 48#64 + BitVec.ofNat 64 24 ∧ sp - 8 - 8 - 8 - 8 = sp - 48#64 + BitVec.ofNat 64 16 ∧
    sp - 8 - 8 - 8 - 8 - 8 = sp - 48#64 + BitVec.ofNat 64 8 ∧
    sp - 8 - 8 - 8 - 8 - 8 - 8 = sp - 48#64 + BitVec.ofNat 64 0 ∧
    sp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 = sp - 56#64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem Fr.kept {V V' : Addr → Byte} {sp : Addr} {g₀ : Gprs} (h : Fr V sp g₀) (hs : 64 ≤ sp.toNat)
    (hk : ∀ a : Addr, sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat + 8 → V' a = V a) : Fr V' sp g₀ := by
  obtain ⟨s8, s16, s24, s32, s40, s48, -⟩ := sp_c sp hs
  exact ⟨(congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.r15,
    (congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.r14,
    (congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.r13,
    (congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.r12,
    (congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.rbp,
    (congrArg (ofBytesLE 64) (rd_in hk (by omega) (by omega) (by omega))).trans h.rbx⟩

/-- The pushes: the saved registers, and no byte outside the 48 under the stack pointer. -/
theorem pr_fr (V : Addr → Byte) (sp : Addr) (g₀ : Gprs) (hs : 64 ≤ sp.toNat) :
    Fr (prV V sp g₀.rbx g₀.rbp g₀.r12 g₀.r13 g₀.r14 g₀.r15) sp g₀ ∧
    Out (sp.toNat - 48) sp.toNat V (prV V sp g₀.rbx g₀.rbp g₀.r12 g₀.r13 g₀.r14 g₀.r15) := by
  obtain ⟨s8, s16, s24, s32, s40, s48, -⟩ := sp_c sp hs
  unfold prV
  rw [(sp_e sp).1, (sp_e sp).2.1, (sp_e sp).2.2.1, (sp_e sp).2.2.2.1, (sp_e sp).2.2.2.2.1,
    show sp - 8 = sp - 8#64 from rfl]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun a ha => ?_⟩
  · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vr (by ln) (by omega) (by omega) (by omega), vr (by ln) (by omega) (by omega) (by omega),
      vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vr (by ln) (by omega) (by omega) (by omega), vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega),
      vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega), vo (by ln) (by omega) (by omega)]

/-! ## The pieces -/

/-- From the entry to the first call's arguments: the frame, one entry in `.preinit_array`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hsp : 56 ≤ g.rsp.toNat)
    (hst : ∀ i < 48, Foot Wl (Addr.add (g.rsp - 48#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 56 ∧ Rg g g' 0 1 7829400#64 ∧
      V' = prV V g.rsp g.rbx g.rbp g.r12 g.r13 g.r14 g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst
  obtain ⟨f1, f2, f3, f4, f5, f6, e7⟩ := sp_f rsp
  have z : ((7829408#64 - 7829400#64).sshiftRight 3 == 0) = false := by decide
  wpx [W_0, W_49, o0, o1, Op.sar64]
  refine ⟨off_ft hst 40 f1 (by decide), off_ft hst 32 f2 (by decide), off_ft hst 24 f3 (by decide),
    off_ft hst 16 f4 (by decide), off_ft hst 8 f5 (by decide), off_ft hst 0 f6 (by decide), fun fl hz =>
    ⟨fun h => ?_, fun _ => ?_⟩⟩
  · rw [hz (by decide), z] at h
    exact absurd h (by decide)
  · rw [e7, BitVec.xor_self]
    exact ⟨rfl, rfl, rfl, rfl, rfl, (by decide : (7829408#64 - 7829400#64).sshiftRight 3 = 1), rfl⟩

/-- The arguments of an entry's call. -/
theorem vc_56 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {i n q : BitVec 64} (hg : Rg g₀ g i n q) :
    W_56 F Wl (fun j' g' _ V' => j' = 64 ∧ g'.rdi = (g₀.rdi.setWidth 32).setWidth 64 ∧ g'.rsi = g₀.rsi ∧
      g'.rdx = g₀.rdx ∧ Rg g₀ g' i n q ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  wpx [W_56, o2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After the entry of `.preinit_array`: it was the only one. -/
theorem vc_68 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {q : BitVec 64} (hg : Rg g₀ g 0 1 q) :
    W_68 F Wl (fun j' g' _ V' => j' = 77 ∧ Rg g₀ g' 1 1 q ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  wpx [W_68, o3]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The bounds of `.init_array`. -/
theorem vc_77 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {i n q : BitVec 64} (hg : Rg g₀ g i n q) :
    W_77 F Wl (fun j' g' _ V' => j' = 91 ∧ Rg g₀ g' i 7830224#64 7829408#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  wpx [W_77, o4]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After `_init`: 102 entries in `.init_array`. -/
theorem vc_96 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {i : BitVec 64}
    (hg : Rg g₀ g i 7830224#64 7829408#64) :
    W_96 F Wl (fun j' g' _ V' => j' = 112 ∧ Rg g₀ g' 0 102 7829408#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  have z : ((7830224#64 - 7829408#64).sshiftRight 3 == 0) = false := by decide
  wpx [W_96, W_105, o5, o1, Op.sar64]
  refine fun fl hz => ⟨fun h => ?_, fun _ => ?_⟩
  · rw [hz (by decide), z] at h
    exact absurd h (by decide)
  · rw [BitVec.xor_self]
    exact ⟨rfl, rfl, rfl, rfl, rfl, (by decide : (7830224#64 - 7829408#64).sshiftRight 3 = 102), rfl⟩

/-- The arguments of an entry's call. -/
theorem vc_112 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {i n q : BitVec 64} (hg : Rg g₀ g i n q) :
    W_112 F Wl (fun j' g' _ V' => j' = 120 ∧ g'.rdi = (g₀.rdi.setWidth 32).setWidth 64 ∧ g'.rsi = g₀.rsi ∧
      g'.rdx = g₀.rdx ∧ Rg g₀ g' i n q ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  wpx [W_112, o2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After entry `i` of `.init_array`: the next one, or the end. -/
theorem vc_124 {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} {i : Nat} {q : BitVec 64}
    (hg : Rg g₀ g (BitVec.ofNat 64 i) 102 q) (hi : i < 102) :
    W_124 F Wl (fun j' g' _ V' => (j' = 112 ∧ i + 1 < 102 ∨ j' = 133 ∧ i + 1 = 102) ∧
      Rg g₀ g' (BitVec.ofNat 64 (i + 1)) 102 q ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  have e : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by bv_omega
  wpx [W_124, o3]
  by_cases h102 : i + 1 = 102
  · have hi' : i = 101 := by omega
    subst hi'
    exact ⟨fun h => absurd h (by decide), fun _ => ⟨Or.inr rfl,
      ⟨rfl, (by decide : 101#64 + 1#64 = BitVec.ofNat 64 (101 + 1)), rfl, rfl, rfl, rfl, rfl⟩⟩⟩
  · have ne : ¬ (102 : BitVec 64) = BitVec.ofNat 64 i + 1#64 := by bv_omega
    refine ⟨fun _ => ⟨Or.inl (by omega), ⟨rfl, e, rfl, rfl, rfl, rfl, rfl⟩⟩, fun h => ?_⟩
    rw [decide_eq_false ne] at h
    exact absurd h (by decide)

/-- The frame's end. -/
theorem vc_133 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 48, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_133 F Wl (fun j' g' _ V' => j' = 147 ∧ g'.rsp = g.rsp + 56#64 ∧ g'.rbx = rdq(V, g.rsp + 8#64) ∧
      g'.rbp = rdq(V, g.rsp + 16#64) ∧ g'.r12 = rdq(V, g.rsp + 24#64) ∧ g'.r13 = rdq(V, g.rsp + 32#64) ∧
      g'.r14 = rdq(V, g.rsp + 40#64) ∧ g'.r15 = rdq(V, g.rsp + 48#64) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl
  wpx [W_133, o6]
  refine ⟨off_ft hl 0 (by bv_omega) (by decide), off_ft hl 8 (by bv_omega) (by decide),
    off_ft hl 16 (by bv_omega) (by decide), off_ft hl 24 (by bv_omega) (by decide),
    off_ft hl 32 (by bv_omega) (by decide), off_ft hl 40 (by bv_omega) (by decide), ?_⟩
  rw [show rsp + 8#64 + 8 = rsp + 16#64 from by bv_omega, show rsp + 16#64 + 8 = rsp + 24#64 from by bv_omega,
    show rsp + 24#64 + 8 = rsp + 32#64 from by bv_omega, show rsp + 32#64 + 8 = rsp + 40#64 from by bv_omega,
    show rsp + 40#64 + 8 = rsp + 48#64 from by bv_omega, show rsp + 48#64 + 8 = rsp + 56#64 from by bv_omega]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The calls -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- What is around the call: the code, the stack under `sp`, the two arrays, and the code of the functions `tg`. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (sp : Addr) (tg : Nat → Addr) :
    Prop where
  code : CodeIn L csu_at csu
  st : ∀ i < 64, Foot Wl (Addr.add (sp - 64#64) i)
  s0 : 64 ≤ sp.toNat
  lr : ∀ i < 8, Foot F.data (Addr.add sp i)
  s8 : sp.toNat + 8 ≤ 2 ^ 64
  ar : ∀ i < 824, Foot F.data (Addr.add 7829400#64 i)
  ad : sp.toNat + 8 ≤ 7829400 ∨ 7830224 ≤ sp.toNat - 64
  tcode : ∀ i < 104, ∃ code, CodeIn L (tg i) code ∧ 0 < code.length
  ini : tg 1 = 0x401000#64

/-- The bytes the frame reads: the saved registers, the return address `ra`, the arrays' entries. -/
structure St (V : Addr → Byte) (g₀ : Gprs) (tg : Nat → Addr) (ra : Addr) : Prop where
  fr : Fr V g₀.rsp g₀
  ra : rdq(V, g₀.rsp) = ra
  pre : rdq(V, 7829400#64) = tg 0
  arr : ∀ k < 102, rdq(V, BitVec.ofNat 64 (7829408 + 8 * k)) = tg (k + 2)

theorem St.kept {V V' : Addr → Byte} {g₀ : Gprs} {tg : Nat → Addr} {ra : Addr} (h : St V g₀ tg ra)
    (hs : 64 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hk : ∀ a : Addr, g₀.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat + 8 → V' a = V a)
    (ha : ∀ a : Addr, 7829400 ≤ a.toNat ∧ a.toNat < 7830224 → V' a = V a) : St V' g₀ tg ra :=
  ⟨h.fr.kept hs hk, (congrArg (ofBytesLE 64) (rd_in hk hs8 (by omega) (by omega))).trans h.ra,
    (congrArg (ofBytesLE 64) (rd_in ha (by decide) (by decide) (by decide))).trans h.pre,
    fun k hk' => (congrArg (ofBytesLE 64) (rd_in ha (by rw [(ar_i k hk').1]; omega)
      (by rw [(ar_i k hk').1]; omega) (by rw [(ar_i k hk').1]; omega))).trans (h.arr k hk')⟩

/-- A store under the frame. -/
theorem St.out {V V' : Addr → Byte} {g₀ : Gprs} {tg : Nat → Addr} {ra : Addr} (h : St V g₀ tg ra)
    (hs : 64 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (had : g₀.rsp.toNat + 8 ≤ 7829400 ∨ 7830224 ≤ g₀.rsp.toNat - 64) {lo hi : Nat} (ho : Out lo hi V V')
    (h1 : g₀.rsp.toNat - 64 ≤ lo) (h2 : hi ≤ g₀.rsp.toNat - 56) : St V' g₀ tg ra :=
  h.kept hs hs8 (fun a ha => ho a (by omega)) (fun a ha => ho a (by omega))

/-- What the frame asks of the `i`-th function it calls, at `f`: from its entry with the return address (in
`__libc_csu_init`) in the stack, the arguments `a₀`, `a₁`, `a₂` (not for `_init`, the function 1) and `I i`, the run
goes on to the goal if it does from every state at the return address with `I (i + 1)`, the registers a call keeps,
and the frame's bytes and the arrays as they were. -/
def Runs (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (I : Nat → (Addr → Byte) → Prop) (sp : Addr) (a₀ a₁ a₂ : BitVec 64) (i : Nat) (f : Addr) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte) (j₂ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → I i V →
    X.cpu.rip = f → X.cpu.gpr.rsp = sp - 64#64 →
    (i ≠ 1 → X.cpu.gpr.rdi = a₀ ∧ X.cpu.gpr.rsi = a₁ ∧ X.cpu.gpr.rdx = a₂) →
    j₂ < csu.length → rdq(V, sp - 64#64) = csu_at.add j₂ →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → I (i + 1) V' →
      (∀ a : Addr, sp.toNat - 56 ≤ a.toNat ∧ a.toNat < sp.toNat + 8 → V' a = V a) →
      (∀ a : Addr, 7829400 ≤ a.toNat ∧ a.toNat < 7830224 → V' a = V a) →
      Z.cpu.rip = csu_at.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- From offset `j` with `m` of the functions done and the frame's registers, the run goes on to the goal. -/
def At (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (I : Nat → (Addr → Byte) → Prop) (g₀ : Gprs) (tg : Nat → Addr) (ra : Addr) (j m : Nat) (b n q : BitVec 64) :
    Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → I m V → St V g₀ tg ra →
    Y.cpu.rip = csu_at.add j → Rg g₀ Y.cpu.gpr b n q → GoG prof L o gev gP gE Y t

variable {I : Nat → (Addr → Byte) → Prop} {g₀ : Gprs} {tg : Nat → Addr} {ra : Addr}

/-- A function's run, from the state its `call` left to the state after it. -/
theorem enter {g : Gprs} {i j₂ : Nat} {b n q : BitVec 64} (hE : Env F Wl L g₀.rsp tg)
    (hI : ∀ m V V', I m V → Out (g₀.rsp.toNat - 64) g₀.rsp.toNat V V' → I m V')
    (hfn : Runs prof F Wl L s₀ o gev gP gE I g₀.rsp ((g₀.rdi.setWidth 32).setWidth 64) g₀.rsi g₀.rdx i (tg i))
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem (Vst V (g.rsp - 8) (toBytesLE (csu_at.add j₂) 8))) (hIi : I i V)
    (hS : St V g₀ tg ra) (hr : Y.cpu.rip = tg i) (hg : Y.cpu.gpr = g.set 4 (g.rsp - 8)) (hR : Rg g₀ g b n q)
    (hj : j₂ < csu.length)
    (hargs : i ≠ 1 → g.rdi = (g₀.rdi.setWidth 32).setWidth 64 ∧ g.rsi = g₀.rsi ∧ g.rdx = g₀.rdx)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → I (i + 1) V' →
      St V' g₀ tg ra → Z.cpu.rip = csu_at.add j₂ → Rg g₀ Z.cpu.gpr b n q → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s8, s16, s24, s32, s40, s48, s56, s64, e64, e56, -⟩ := sp_c g₀.rsp hE.s0
  rw [hR.rsp, e64] at hA hg
  have hs0 := hE.s0
  have ho : Out (g₀.rsp.toNat - 64) (g₀.rsp.toNat - 56) V
      (Vst V (g₀.rsp - 64#64) (toBytesLE (csu_at.add j₂) 8)) :=
    (Out.vst (toBytesLE_length _ _) (by omega)).mono (by omega) (by omega)
  have hsp : Y.cpu.gpr.rsp = g₀.rsp - 64#64 := by rw [hg]; rfl
  refine hfn Y t _ j₂ hK hA (hI _ _ _ hIi (ho.mono (Nat.le_refl _) (by omega))) hr hsp (fun h1 => ?_) hj ?_ ?_
  · rw [hg]
    exact hargs h1
  · rw [vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro Z t' V' hKZ hAZ hI' hk1 hk2 hrZ hB
  refine k Z t' V' hKZ hAZ hI' ((hS.out hE.s0 hE.s8 hE.ad ho (Nat.le_refl _) (Nat.le_refl _)).kept hE.s0 hE.s8
    hk1 hk2) hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hB
  rw [hsp] at b1
  rw [hg] at b2 b3 b4 b5 b6 b7
  exact ⟨b1.trans e56, b2.trans hR.rbx, b3.trans hR.rbp, b4.trans hR.r12, b5.trans hR.r13, b6.trans hR.r14,
    b7.trans hR.r15⟩

variable {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- The frame's end and the `ret`. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L g₀.rsp tg) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → I 104 V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') (b n q : BitVec 64) :
    At prof F Wl L s₀ o gev gP gE I g₀ tg (e₂.add j₂) 133 104 b n q := by
  intro Y t V hK hA hIi hS hr hR
  obtain ⟨p8, p16, p24, p32, p40, p48, p56, pf, -⟩ := sp_g g₀.rsp
  refine (c_133 prof).run c hE.code _ hK hA hr (vc_133 (fun i hi => by
    rw [hR.rsp]
    exact c.hws _ (off_ft hE.st 16 pf (by decide) i hi))) ?_
  rintro j' g fl V₁ ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  rw [hR.rsp] at hsp hbx hbp h12 h13 h14 h15
  rw [p56] at hsp
  rw [p8, hS.fr.rbx] at hbx
  rw [p16, hS.fr.rbp] at hbp
  rw [p24, hS.fr.r12] at h12
  rw [p32, hS.fr.r13] at h13
  rw [p40, hS.fr.r14] at h14
  rw [p48, hS.fr.r15] at h15
  refine c.s_ret hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (ret_147 _) (fun i hi => by rw [hsp]; exact hE.lr i hi)
    hin₂ h₂ (by rw [hsp]; exact hS.ra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ Z t' hKZ hAZ hIi hrZ ?_
  rw [hgZ]
  refine ⟨?_, hbx, hbp, h12, h13, h14, h15⟩
  show Y₁.cpu.gpr.rsp + 8 = _
  rw [hsp]
  rfl

/-- Entry `i` of `.init_array`: its call, then the next entry or the end. -/
theorem lpHead {i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L g₀.rsp tg)
    (hI : ∀ m V V', I m V → Out (g₀.rsp.toNat - 64) g₀.rsp.toNat V V' → I m V')
    (hfn : ∀ m < 104, Runs prof F Wl L s₀ o gev gP gE I g₀.rsp ((g₀.rdi.setWidth 32).setWidth 64) g₀.rsi g₀.rdx
      m (tg m))
    (ke : ∀ b n q, At prof F Wl L s₀ o gev gP gE I g₀ tg ra 133 104 b n q) (hi : i < 102)
    (kn : i + 1 < 102 →
      At prof F Wl L s₀ o gev gP gE I g₀ tg ra 112 (i + 1 + 2) (BitVec.ofNat 64 (i + 1)) 102 7829408#64) :
    At prof F Wl L s₀ o gev gP gE I g₀ tg ra 112 (i + 2) (BitVec.ofNat 64 i) 102 7829408#64 := by
  intro Y t V hK hA hIi hS hr hR
  obtain ⟨-, -, -, -, -, -, -, -, e64, -⟩ := sp_c g₀.rsp hE.s0
  refine (c_112 prof).run c hE.code _ hK hA hr (vc_112 hR) ?_
  rintro j' g fl V₁ ⟨rfl, ha0, ha1, ha2, hR₁, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  obtain ⟨code, hc, hcl⟩ := hE.tcode (i + 2) (by omega)
  have hadr : eaS Y₁ (some 15) 3 8 0 = BitVec.ofNat 64 (7829408 + 8 * i) := by
    show Y₁.cpu.gpr.r15 + Y₁.cpu.gpr.rbx * 8#64 + 0#64 = _
    rw [hR₁.r15, hR₁.rbx]
    exact (ar_i i hi).2.1
  refine c.s_callX hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (callx_120 _)
    (fun m hm => by rw [hadr]; exact off_ft hE.ar (8 + 8 * i) (ar_i i hi).2.2 (by omega) m hm) hc hcl
    (by rw [hadr]; exact hS.arr i hi) (fun m hm => by rw [hR₁.rsp, e64]; exact hE.st m (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine enter hE hI (hfn (i + 2) (by omega)) hK₂ hA₂ hIi hS hr₂ hg₂ hR₁ (lt_len (by decide))
    (fun _ => ⟨ha0, ha1, ha2⟩) ?_
  intro Z t' V' hKZ hAZ hI' hS' hrZ hRZ
  refine (c_124 prof).run c hE.code _ hKZ hAZ hrZ (vc_124 hRZ hi) ?_
  rintro j' g fl V₂ ⟨hj, hR₂, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst hg₃
  obtain ⟨rfl, hlt⟩ | ⟨rfl, heq⟩ := hj
  · exact kn hlt Y₃ t₃ _ hK₃ hA₃ ((by omega : i + 2 + 1 = i + 1 + 2) ▸ hI') hS' hr₃ hR₂
  · exact ke _ _ _ Y₃ t₃ _ hK₃ hA₃ ((by omega : i + 2 + 1 = 104) ▸ hI') hS' hr₃ hR₂

/-- The entries of `.init_array` from any one: by the number left. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L g₀.rsp tg)
    (hI : ∀ m V V', I m V → Out (g₀.rsp.toNat - 64) g₀.rsp.toNat V V' → I m V')
    (hfn : ∀ m < 104, Runs prof F Wl L s₀ o gev gP gE I g₀.rsp ((g₀.rdi.setWidth 32).setWidth 64) g₀.rsi g₀.rdx
      m (tg m))
    (ke : ∀ b n q, At prof F Wl L s₀ o gev gP gE I g₀ tg ra 133 104 b n q) :
    ∀ (n i : Nat), i + n = 101 →
      At prof F Wl L s₀ o gev gP gE I g₀ tg ra 112 (i + 2) (BitVec.ofNat 64 i) 102 7829408#64
  | 0, _, h => lpHead c hE hI hfn ke (by omega) fun h' => absurd h' (by omega)
  | n + 1, i, h => lpHead c hE hI hfn ke (by omega) fun _ => lpAll c hE hI hfn ke n (i + 1) (by omega)

/-- `__libc_csu_init (argc, argv, envp)`: if each of the 104 functions `tg` (the entry of `.preinit_array`, `_init`,
the 102 entries of `.init_array`) runs from its entry to its return address as `Runs` says, taking `I m` to
`I (m + 1)`, the run reaches the return address with `I 104` and the registers a call keeps as at the entry. -/
theorem csu_ok (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L X.cpu.gpr.rsp tg) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = csu_at) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hpre : rdq(V, 7829400#64) = tg 0)
    (harr : ∀ k < 102, rdq(V, BitVec.ofNat 64 (7829408 + 8 * k)) = tg (k + 2))
    (hI : ∀ m V V', I m V → Out (X.cpu.gpr.rsp.toNat - 64) X.cpu.gpr.rsp.toNat V V' → I m V') (h0 : I 0 V)
    (hfn : ∀ m < 104, Runs prof F Wl L s₀ o gev gP gE I X.cpu.gpr.rsp
      ((X.cpu.gpr.rdi.setWidth 32).setWidth 64) X.cpu.gpr.rsi X.cpu.gpr.rdx m (tg m))
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → I 104 V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨s8, s16, s24, s32, s40, s48, s56, s64, e64, e56, -⟩ := sp_c X.cpu.gpr.rsp hE.s0
  obtain ⟨hfr, ho⟩ := pr_fr V X.cpu.gpr.rsp X.cpu.gpr hE.s0
  have t0 : (7829400#64).toNat = 7829400 := rfl
  have had := hE.ad
  have hs8 := hE.s8
  have hs0 := hE.s0
  -- the frame
  refine (c_0 prof).run c hE.code _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by omega) (off_ft hE.st 16 (sp_g X.cpu.gpr.rsp).2.2.2.2.2.2.2.2 (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, hR₁, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  have hS₁ : St (prV V X.cpu.gpr.rsp X.cpu.gpr.rbx X.cpu.gpr.rbp X.cpu.gpr.r12 X.cpu.gpr.r13 X.cpu.gpr.r14
      X.cpu.gpr.r15) X.cpu.gpr tg (e₂.add j₂) :=
    ⟨hfr, (congrArg (ofBytesLE 64) (ho.rd hs8 (Or.inr (Nat.le_refl _)))).trans hra,
      (congrArg (ofBytesLE 64) (ho.rd (by decide) (by rw [t0]; omega))).trans hpre,
      fun k hk => (congrArg (ofBytesLE 64) (ho.rd (by rw [(ar_i k hk).1]; omega)
        (by rw [(ar_i k hk).1]; omega))).trans (harr k hk)⟩
  have hI₁ := hI _ _ _ h0 (ho.mono (by omega) (Nat.le_refl _))
  -- the entry of `.preinit_array`
  refine (c_56 prof).run c hE.code _ hK₁ hA₁ hr₁ (vc_56 hR₁) ?_
  rintro j' g fl V₂ ⟨rfl, ha0, ha1, ha2, hR₂, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst hg₂
  obtain ⟨code, hc, hcl⟩ := hE.tcode 0 (by decide)
  have hadr : eaS Y₂ (some 15) 3 8 0 = 7829400#64 := by
    show Y₂.cpu.gpr.r15 + Y₂.cpu.gpr.rbx * 8#64 + 0#64 = _
    rw [hR₂.r15, hR₂.rbx]
    decide
  refine c.s_callX hK₂ hA₂ hE.code (lt_len (by decide)) hr₂ (callx_64 _)
    (fun m hm => by rw [hadr]; exact hE.ar m (by omega)) hc hcl (by rw [hadr]; exact hS₁.pre)
    (fun m hm => by rw [hR₂.rsp, e64]; exact hE.st m (by omega)) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  refine enter hE hI (hfn 0 (by decide)) hK₃ hA₃ hI₁ hS₁ hr₃ hg₃ hR₂ (lt_len (by decide))
    (fun _ => ⟨ha0, ha1, ha2⟩) ?_
  intro Z₁ u₁ V₃ hKZ₁ hAZ₁ hI₃ hS₃ hrZ₁ hRZ₁
  refine (c_68 prof).run c hE.code _ hKZ₁ hAZ₁ hrZ₁ (vc_68 hRZ₁) ?_
  rintro j' g fl V₄ ⟨rfl, hR₄, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst hg₄
  refine (c_77 prof).run c hE.code _ hK₄ hA₄ hr₄ (vc_77 hR₄) ?_
  rintro j' g fl V₅ ⟨rfl, hR₅, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  subst hg₅
  -- `_init`
  obtain ⟨code1, hc1, hcl1⟩ := hE.tcode 1 (by decide)
  refine c.s_call hK₅ hA₅ hE.code (lt_len (by decide)) hr₅ (call_91 _) hc1 hcl1 (by rw [hE.ini]; decide)
    (fun m hm => by rw [hR₅.rsp, e64]; exact hE.st m (by omega)) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  refine enter hE hI (hfn 1 (by decide)) hK₆ hA₆ hI₃ hS₃ hr₆ hg₆ hR₅ (lt_len (by decide))
    (fun h => absurd rfl h) ?_
  intro Z₂ u₂ V₆ hKZ₂ hAZ₂ hI₆ hS₆ hrZ₂ hRZ₂
  -- the entries of `.init_array`
  refine (c_96 prof).run c hE.code _ hKZ₂ hAZ₂ hrZ₂ (vc_96 hRZ₂) ?_
  rintro j' g fl V₇ ⟨rfl, hR₇, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  subst hg₇
  exact lpAll c hE hI hfn (fin c hE hin₂ h₂ k) 101 0 rfl Y₇ t₇ _ hK₇ hA₇ hI₆ hS₆ hr₇ hR₇

end FV7z.Csu
