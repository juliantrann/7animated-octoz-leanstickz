import FV7z.Pim.B
import FV7z.Gts.Holds
import FV7z.Grl.Holds
import FV7z.Lemmas.BlkOps4
/-!
# `__pthread_initialize_minimal_internal`: the static TLS block's size, the conditions

The third stretch of the function at `0x6000b0`, offsets 352 to 545: `_dl_get_tls_static_info`, the alignment (16 at
least) less one in `__static_tls_align_m1`, the size a multiple of it in `__static_tls_size` (`div`), `__getrlimit
(RLIMIT_STACK)`, the default stack's size in the frame.

- `MemC`: the bytes outside the frame after the stretch; the two values the function computes are not described.
- `Kp`: the registers the stretch's pieces keep.
- `rlEv`: the system call's event.
- `vc_352` … `vc_492`: the verification conditions (`pim_c`, the stretch, is in `Pim/C.lean`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes outside the frame after the stretch: `__static_tls_size` (the loader's value, then `tv`),
`__static_tls_align_m1` (`am`). -/
def MemC (G : Addr → Byte) (am tv : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst G (8027712#64) (toBytesLE rdq(G, 7938736#64) 8)) (8027696#64) (toBytesLE am 8))
    (8027712#64) (toBytesLE tv 8)

/-- The registers a piece keeps. -/
structure Kp (g g' : Gprs) : Prop where
  rsp : g'.rsp = g.rsp
  rbx : g'.rbx = g.rbx
  rbp : g'.rbp = g.rbp
  r12 : g'.r12 = g.r12
  r13 : g'.r13 = g.r13
  r14 : g'.r14 = g.r14
  r15 : g'.r15 = g.r15
  r8 : g'.r8 = g.r8
  r9 : g'.r9 = g.r9

theorem Kp.trans {g g' g'' : Gprs} (h : Kp g g') (h' : Kp g' g'') : Kp g g'' :=
  ⟨h'.rsp.trans h.rsp, h'.rbx.trans h.rbx, h'.rbp.trans h.rbp, h'.r12.trans h.r12, h'.r13.trans h.r13,
    h'.r14.trans h.r14, h'.r15.trans h.r15, h'.r8.trans h.r8, h'.r9.trans h.r9⟩

/-- `prlimit64 (0, RLIMIT_STACK, 0, sp - 200)` of `__getrlimit`, the limit's bytes `bs` written. -/
abbrev rlEv (sp : Addr) (r8 r9 : BitVec 64) (bs : List Byte) : Event :=
  ⟨302, [0, BitVec.setWidth 64 3#32, 0, sp - 200#64, r8, r9], 0, [], bs⟩

/-- A choice of registers, register by register. -/
theorem ite_mk (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6
    b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 64) :
    (if c then Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      else Gprs.mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) =
    Gprs.mk (if c then a0 else b0) (if c then a1 else b1) (if c then a2 else b2) (if c then a3 else b3)
      (if c then a4 else b4) (if c then a5 else b5) (if c then a6 else b6) (if c then a7 else b7)
      (if c then a8 else b8) (if c then a9 else b9) (if c then a10 else b10) (if c then a11 else b11)
      (if c then a12 else b12) (if c then a13 else b13) (if c then a14 else b14) (if c then a15 else b15) := by
  split <;> rfl

/-- What holds of both registers' states holds of the one a condition picks (whatever decides the condition). -/
theorem of_ite {c : Prop} {inst : Decidable c} {A B : Gprs} {P : Gprs → Prop} (hA : P A) (hB : P B) :
    P (@ite Gprs c inst A B) := by
  cases inst <;> assumption

/-- The arguments of `_dl_get_tls_static_info`. -/
theorem vc_352 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_352 fb F Wl (fun j' g' _ V' => j' = 364 ∧ g' = { g with rsi := g.rsp + 8#64, rdi := 8027712#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_352, o10]

/-- The alignment, 16 at least. -/
theorem vc_369 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hs : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 8#64) i)) :
    W_369 fb F Wl (fun j' g' _ V' => j' = 403 ∧ ∃ al am : BitVec 64, al ≠ 0 ∧ g' = { g with rax := am, rcx := al } ∧
      (V' = V ∨ V' = Vst V (g.rsp + 8#64) (toBytesLE (16#64) 8))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_369, W_384, o11, o12]
  refine ⟨hl, fun hc => ⟨_, _, fun h0 => ?_, rfl, Or.inl trivial⟩,
    fun _ => ⟨hs, _, _, by decide, rfl, Or.inr trivial⟩⟩
  rw [h0] at hc
  exact absurd hc (by decide)

/-- `__static_tls_align_m1`, the arguments of `__getrlimit`, the size to round. -/
theorem vc_403 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add 8027696#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add 8027712#64 i)) :
    W_403 fb F Wl (fun j' g' _ V' => j' = 434 ∧ ∃ ax : BitVec 64,
      g' = { g with rax := ax, rdx := BitVec.setWidth 64 0#32, rsi := g.rsp + 16#64,
                    rdi := BitVec.setWidth 64 3#32 } ∧
      V' = Vst V (8027696#64) (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_403, o13, Op.sta, Op.lda, BitVec.xor_self]
  exact ⟨h1, h2, _, rfl⟩

/-- `__static_tls_size`. -/
theorem vc_437 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ∀ i < 8, Foot Wl (Addr.add 8027712#64 i)) :
    W_437 fb F Wl (fun j' g' _ V' => j' = 448 ∧ ∃ tv : BitVec 64, g' = { g with rax := tv } ∧
      V' = Vst V (8027712#64) (toBytesLE tv 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_437, o14, Op.sta, Op.imul64]
  intro fl
  exact ⟨h, _, rfl, rfl⟩

/-- The limit of the stack, or 2 MiB. -/
theorem vc_453 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) :
    W_453 fb F Wl (fun j' g' _ V' => j' = 492 ∧ ∃ ax cx dx : BitVec 64,
      g' = { g with rax := ax, rcx := cx, rdx := dx } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_453, W_462, W_473, o15, o16, o17]
  refine ⟨fun _ => ⟨_, _, _, rfl⟩, fun _ => ⟨hl, fun _ => ⟨_, _, _, rfl⟩, fun _ => ?_⟩⟩
  exact of_ite (P := fun G => ∃ ax cx dx, G.set (regOf 1) (G.get (regOf 0)) =
    Gprs.mk ax cx dx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15) ⟨_, _, _, rfl⟩ ⟨_, _, _, rfl⟩

/-- The default stack's size, a multiple of the page's. -/
theorem vc_492 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add 8027712#64 i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 16#64) i)) :
    W_492 fb F Wl (fun j' g' _ V' => j' = 545 ∧ ∃ sz : BitVec 64,
      g' = { g with rax := BitVec.setWidth 64 0#32, rdx := BitVec.setWidth 64 1#32 } ∧
      V' = Vst V (g.rsp + 16#64) (toBytesLE sz 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_492, o18, Op.lda, BitVec.xor_self, ite_mk, ite_self]
  exact ⟨h1, h2, h3, _, rfl⟩

end FV7z.Pim
