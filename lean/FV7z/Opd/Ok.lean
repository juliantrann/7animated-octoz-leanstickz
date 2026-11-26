import FV7z.Opd.Holds
import FV7z.Onc.Holds
import FV7z.Fxs.Holds
import FV7z.Cnc.Holds
import FV7z.Mal.Ok
/-!
# `__opendir` from its entry to its return (PLAN.md §M, M1)

The ways `Opd.Holds` leaves out, and the join at 219 every way meets at:

- `vc_0z` (the empty `name`: `errno` = `ENOENT`, 288), `vc_55n` (the open failing, 312), `vc_80n` (`fstat` failing),
  `vc_80d` (not a directory: `errno` = `ENOTDIR`, 256), `vc_270` (to `__close_nocancel`), `vc_280`, `vc_153z` (the
  first `malloc` failing, 322), `vc_337` (after the second `malloc (0x2030)`), `vc_371` (`errno` restored);
- `Kp`: what every way keeps of the bytes at the entry (from the stack guard's slot `S - 48` up, and the stack guard at
  `fs:0x28`); `opd_join`: from 219 with `Kp`, to the return address, `rax` = `r12`;
- `OMal`: `malloc` as `Mal.AtHW` with a heap invariant indexed by a budget for both calls (`bsz _ + 48`, then
  `0x2030`); `omal_hp` gives it from `Mal.at_hpW` (`Pm k` = `Mal.Hp … (k + m₀)`, kept by the frame and `errno` by
  `hp_mvE`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out rd1)
namespace FV7z.Opd

/-- The `call __close_nocancel` after `fstat` (275). -/
def pcc : List Byte := [0xe8, 0x38, 0x28, 0x00, 0x00]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 10296] 5) := by dec_rfl
theorem wc_275 : pcc <+: opd.drop 275 := by decide +kernel
theorem call_275 (feat : Features) : Dec feat opd 275 (FV7z.mk .call 64 [.rel 10296] 5) :=
  Dec.shift (j := 275) (k := 0) (pcc_0 feat) wc_275 (Nat.zero_le _)

/-- The second `call malloc` (332). -/
def pcm2 : List Byte := [0xe8, 0x3f, 0xfa, 0xfc, 0xff]
theorem pcm2_0 : ∀ feat, Dec feat pcm2 0 (FV7z.mk .call 64 [.rel 18446744073709353535] 5) := by dec_rfl
theorem wc_332 : pcm2 <+: opd.drop 332 := by decide +kernel
theorem call_332 (feat : Features) : Dec feat opd 332 (FV7z.mk .call 64 [.rel 18446744073709353535] 5) :=
  Dec.shift (j := 332) (k := 0) (pcm2_0 feat) wc_332 (Nat.zero_le _)

/-- The `call __close_nocancel` after the second `malloc` (366). -/
def pcc2 : List Byte := [0xe8, 0xdd, 0x27, 0x00, 0x00]
theorem pcc2_0 : ∀ feat, Dec feat pcc2 0 (FV7z.mk .call 64 [.rel 10205] 5) := by dec_rfl
theorem wc_366 : pcc2 <+: opd.drop 366 := by decide +kernel
theorem call_366 (feat : Features) : Dec feat opd 366 (FV7z.mk .call 64 [.rel 10205] 5) :=
  Dec.shift (j := 366) (k := 0) (pcc2_0 feat) wc_366 (Nat.zero_le _)

/-! ## The ways left out -/

/-- `ENOENT`, `ENOTDIR` as `errno`'s bytes. -/
abbrev enoent : List Byte := toBytesLE (2#32) 4
abbrev enotdir : List Byte := toBytesLE (20#32) 4

variable {F : Footprint} {Wl : List Rgn}

local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

/-- `vfin`, and `assumption` at the default transparency (the `fs` stores' addresses `fb + eaG …`). -/
local macro "vfinE" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | assumption | rfl | intro _))

/-- The empty `name`: the pushes, the stack guard stored, `errno` = `ENOENT`, `r12` 0. -/
theorem vc_0z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64}
    (hcn : rdq(P4 V g, fb + 40#64) = cn) (hz : ofBytesLE 8 ((byteAddrs g.rdi 1).map (Vo g cn V)) = 0#8)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aQ g.rsp + 152#64) i))
    (fr : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 219 ∧
      g' = { g with rax := 18446744073709551544#64, rsp := aQ g.rsp, r12 := 0#64 } ∧
      V' = Vst (Vo g cn V) (errnoAt fb) enoent) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vo, P4, aQ] at hcn hz w1 w2 w3 w4 wc fr ⊢
  wpx [W_0, W_288, o0, o13, Op.ldf, Op.cmpmi, Op.stfi, hcn, hz, BitVec.sub_self, xz, decide_true,
    Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfinE

/-- The open failing (`eax` negative): `r12` 0. -/
theorem vc_55n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : (BitVec.setWidth 32 g.rax).msb = true) :
    W_55 fb F Wl (fun j' g' _ V' => j' = 219 ∧
      g' = { g with rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax), r12 := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs ⊢
  wpx [W_55, W_312, o2, o14, BitVec.and_self, hs, xz, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true,
    true_implies]
  all_goals vfin

/-- `fstat` failing (`eax` negative): to 270. -/
theorem vc_80n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : (BitVec.setWidth 32 g.rax).msb = true) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 270 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs ⊢
  wpx [W_80, o4, BitVec.and_self, hs, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- Not a directory: `errno` = `ENOTDIR`, to 270. -/
theorem vc_80d {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : (BitVec.setWidth 32 g.rax).msb = false)
    (hm : ofBytesLE 32 ((byteAddrs (g.rsp + 24#64) 4).map V) &&& 61440#32 ≠ 16384#32)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i)) (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 270 ∧ g' = { g with rax := 18446744073709551544#64 } ∧
      V' = Vst V (errnoAt fb) enotdir) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hm f24 ⊢
  have hm' : decide (ofBytesLE 32 ((byteAddrs (rsp + 24#64) 4).map V) &&& 61440#32 = 16384#32) = false :=
    decide_eq_false hm
  wpx [W_80, W_88, W_256, o4, o5, o11, Op.stfi, BitVec.and_self, hs, hm', decide_false, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfinE

/-- To `__close_nocancel (fd)`: `edi` the descriptor (`ebp`), `r12` 0. -/
theorem vc_270 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_270 fb F Wl (fun j' g' _ V' => j' = 275 ∧
      g' = { g with rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp), r12 := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_270, o12, xz]
  all_goals vfin

theorem vc_280 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_280 fb F Wl (fun j' g' _ V' => j' = 219 ∧ g' = g ∧ V' = V) g f V :=
  ⟨rfl, rfl, rfl⟩

/-- The first `malloc` failing: to `malloc (0x2030)`, `ebx` 0x2000. -/
theorem vc_153z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax = 0#64) :
    W_153 fb F Wl (fun j' g' _ V' => j' = 322 ∧ g' = { g with r12 := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz
  subst hz
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_153, o7, BitVec.and_self, z0, decide_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true,
    true_implies]
  all_goals vfin

theorem vc_322 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_322 fb F Wl (fun j' g' _ V' => j' = 332 ∧ g' = { g with rbx := 8192#64, rdi := 8240#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e1 : BitVec.setWidth 64 8240#32 = 8240#64 := by decide
  have e2 : BitVec.setWidth 64 8192#32 = 8192#64 := by decide
  wpx [W_322, o15, e1, e2]
  all_goals vfin

/-- The second `malloc`'s block not null: to the stores. -/
theorem vc_337 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hnz : g.rax ≠ 0#64) :
    W_337 fb F Wl (fun j' g' _ V' => j' = 165 ∧ g' = { g with r12 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hnz ⊢
  have hnz' : rax ≠ (0 : BitVec 64) := hnz
  have hb0 : (rax == 0) = false := beq_false_of_ne hnz'
  wpx [W_337, o7, BitVec.and_self, hnz, hnz', hb0, decide_false, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- Both `malloc`s failing: `errno` kept in `r13d` (`rbx` its offset), `edi` the descriptor, to `__close_nocancel`. -/
theorem vc_337z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax = 0#64)
    (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_337 fb F Wl (fun j' g' _ V' => j' = 366 ∧
      g' =
        { g with
          rbx := 18446744073709551544#64
          rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp)
          r12 := 0#64
          r13 := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs (errnoAt fb) 4).map V)) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_337, W_349, o7, o16, Op.ldf, BitVec.and_self, z0, decide_true, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfinE

/-- `errno` restored from `r13d` (`rbx` its offset), to 219. -/
theorem vc_371 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hb : g.rbx = 18446744073709551544#64)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_371 fb F Wl (fun j' g' _ V' => j' = 219 ∧ g' = g ∧
      V' = Vst V (errnoAt fb) (toBytesLE (BitVec.setWidth 32 g.r13) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb ⊢
  subst hb
  wpx [W_371, o17, Op.stf]
  all_goals vfinE

/-! ## The join at 219 -/

/-- `errno`'s 4 bytes. -/
abbrev ER (fb a : Addr) : Prop := (errnoAt fb).toNat ≤ a.toNat ∧ a.toNat < (errnoAt fb).toNat + 4

/-- What every way keeps of the bytes `V₀` at the entry (registers `g`, `S` = `g.rsp`): from the stack guard's slot
`S - 48` up, and the stack guard at `fs:0x28`, but `errno`. -/
def Kp (g : Gprs) (fb : Addr) (V₀ W : Addr → Byte) : Prop :=
  ∀ a : Addr,
    g.rsp.toNat - 48 ≤ a.toNat ∨ ((fb + 40#64).toNat ≤ a.toNat ∧ a.toNat < (fb + 40#64).toNat + 8) →
    ¬ ER fb a → W a = V₀ a

theorem q168 (S : Addr) : aQ S + 168#64 = S - 8 - 8 - 8 - 8 := by dsimp only [aQ]; bv_omega
theorem q176 (S : Addr) : aQ S + 176#64 = S - 8 - 8 - 8 := by dsimp only [aQ]; bv_omega
theorem q184 (S : Addr) : aQ S + 184#64 = S - 8 - 8 := by dsimp only [aQ]; bv_omega
theorem q192 (S : Addr) : aQ S + 192#64 = S - 8 := by dsimp only [aQ]; bv_omega
theorem q200 (S : Addr) : aQ S + 200#64 = S := by dsimp only [aQ]; bv_omega
theorem q208 (S : Addr) : aQ S + 208#64 = S + 8#64 := by dsimp only [aQ]; bv_omega

/-- The stack guard's slot and the pushes in `Vo`. -/
theorem Vo_reads (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 208 ≤ g.rsp.toNat) :
    rdq(Vo g cn V, aQ g.rsp + 152#64) = cn ∧ rdq(Vo g cn V, g.rsp - 8 - 8 - 8 - 8) = g.rbx ∧
      rdq(Vo g cn V, g.rsp - 8 - 8 - 8) = g.rbp ∧ rdq(Vo g cn V, g.rsp - 8 - 8) = g.r12 ∧
      rdq(Vo g cn V, g.rsp - 8) = g.r13 := by
  obtain ⟨e1, e2, e3, e4, -, e6, -⟩ := stA g.rsp h
  have hl := g.rsp.isLt
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have c6 : (aQ g.rsp + 152#64).toNat + (toBytesLE cn 8).length ≤ 2 ^ 64 := by rw [l8, e6]; omega
  have c4 : (g.rsp - 8 - 8 - 8 - 8).toNat + (toBytesLE g.rbx 8).length ≤ 2 ^ 64 := by rw [l8, e4]; omega
  have c3 : (g.rsp - 8 - 8 - 8).toNat + (toBytesLE g.rbp 8).length ≤ 2 ^ 64 := by rw [l8, e3]; omega
  have c2 : (g.rsp - 8 - 8).toNat + (toBytesLE g.r12 8).length ≤ 2 ^ 64 := by rw [l8, e2]; omega
  have c1 : (g.rsp - 8).toNat + (toBytesLE g.r13 8).length ≤ 2 ^ 64 := by rw [l8, e1]; omega
  have n4 : (g.rsp - 8 - 8 - 8 - 8).toNat + 8 ≤ 2 ^ 64 := by rw [e4]; omega
  have n3 : (g.rsp - 8 - 8 - 8).toNat + 8 ≤ 2 ^ 64 := by rw [e3]; omega
  have n2 : (g.rsp - 8 - 8).toNat + 8 ≤ 2 ^ 64 := by rw [e2]; omega
  have n1 : (g.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [e1]; omega
  have o4 : (aQ g.rsp + 152#64).toNat + (toBytesLE cn 8).length ≤ (g.rsp - 8 - 8 - 8 - 8).toNat ∨
      (g.rsp - 8 - 8 - 8 - 8).toNat + 8 ≤ (aQ g.rsp + 152#64).toNat := by rw [l8, e6, e4]; omega
  have o3 : (aQ g.rsp + 152#64).toNat + (toBytesLE cn 8).length ≤ (g.rsp - 8 - 8 - 8).toNat ∨
      (g.rsp - 8 - 8 - 8).toNat + 8 ≤ (aQ g.rsp + 152#64).toNat := by rw [l8, e6, e3]; omega
  have o2 : (aQ g.rsp + 152#64).toNat + (toBytesLE cn 8).length ≤ (g.rsp - 8 - 8).toNat ∨
      (g.rsp - 8 - 8).toNat + 8 ≤ (aQ g.rsp + 152#64).toNat := by rw [l8, e6, e2]; omega
  have o1 : (aQ g.rsp + 152#64).toNat + (toBytesLE cn 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (aQ g.rsp + 152#64).toNat := by rw [l8, e6, e1]; omega
  have x43 : (g.rsp - 8 - 8 - 8 - 8).toNat + (toBytesLE g.rbx 8).length ≤ (g.rsp - 8 - 8 - 8).toNat ∨
      (g.rsp - 8 - 8 - 8).toNat + 8 ≤ (g.rsp - 8 - 8 - 8 - 8).toNat := by rw [l8, e4, e3]; omega
  have x42 : (g.rsp - 8 - 8 - 8 - 8).toNat + (toBytesLE g.rbx 8).length ≤ (g.rsp - 8 - 8).toNat ∨
      (g.rsp - 8 - 8).toNat + 8 ≤ (g.rsp - 8 - 8 - 8 - 8).toNat := by rw [l8, e4, e2]; omega
  have x41 : (g.rsp - 8 - 8 - 8 - 8).toNat + (toBytesLE g.rbx 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (g.rsp - 8 - 8 - 8 - 8).toNat := by rw [l8, e4, e1]; omega
  have x32 : (g.rsp - 8 - 8 - 8).toNat + (toBytesLE g.rbp 8).length ≤ (g.rsp - 8 - 8).toNat ∨
      (g.rsp - 8 - 8).toNat + 8 ≤ (g.rsp - 8 - 8 - 8).toNat := by rw [l8, e3, e2]; omega
  have x31 : (g.rsp - 8 - 8 - 8).toNat + (toBytesLE g.rbp 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (g.rsp - 8 - 8 - 8).toNat := by rw [l8, e3, e1]; omega
  have x21 : (g.rsp - 8 - 8).toNat + (toBytesLE g.r12 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (g.rsp - 8 - 8).toNat := by rw [l8, e2, e1]; omega
  have b8 : (64 : Nat) = 8 * 8 := rfl
  dsimp only [Vo, P4]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_Vst_self _ (aQ g.rsp + 152#64) _ (l8 cn) (by rw [e6]; omega), ofBytesLE_toBytesLE b8]
  · rw [rd_Vst _ _ _ _ 8 c6 n4 o4, rd_Vst_self _ (g.rsp - 8 - 8 - 8 - 8) _ (l8 g.rbx) (by rw [e4]; omega),
      ofBytesLE_toBytesLE b8]
  · rw [rd_Vst _ _ _ _ 8 c6 n3 o3, rd_Vst _ _ _ _ 8 c4 n3 x43,
      rd_Vst_self _ (g.rsp - 8 - 8 - 8) _ (l8 g.rbp) (by rw [e3]; omega), ofBytesLE_toBytesLE b8]
  · rw [rd_Vst _ _ _ _ 8 c6 n2 o2, rd_Vst _ _ _ _ 8 c4 n2 x42, rd_Vst _ _ _ _ 8 c3 n2 x32,
      rd_Vst_self _ (g.rsp - 8 - 8) _ (l8 g.r12) (by rw [e2]; omega), ofBytesLE_toBytesLE b8]
  · rw [rd_Vst _ _ _ _ 8 c6 n1 o1, rd_Vst _ _ _ _ 8 c4 n1 x41, rd_Vst _ _ _ _ 8 c3 n1 x31,
      rd_Vst _ _ _ _ 8 c2 n1 x21, rd_Vst_self _ (g.rsp - 8) _ (l8 g.r13) (by rw [e1]; omega),
      ofBytesLE_toBytesLE b8]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {t : Nat} {V : Addr → Byte}

/-- From 219, the bytes `W` keeping (`Kp`) those at the entry (registers `g`, bytes `Vo g cn V`, `cn` the stack guard),
`rsp` the frame (`aQ`): at the return address with `rax` = `r12`, `rsp` 8 above the entry's, `rbx`, `rbp`, `r12`, `r13`
as at the entry. -/
theorem opd_join {fb : Addr} {g : Gprs} {cn : BitVec 64} {Y : State} {W : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = opd_at.add 219)
    (hsp : Y.cpu.gpr.rsp = aQ g.rsp) (h208 : 208 ≤ g.rsp.toNat) (hsb : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hfd : ∀ i < 208, Foot F.data (Addr.add (aQ g.rsp) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ (fb + 40#64).toNat)
    (hed : (errnoAt fb).toNat + 4 ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (hec : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat)
    (hkp : Kp g fb (Vo g cn V) W) (hcn : rdq(V, fb + 40#64) = cn)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, g.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = g.rsp + 8#64 → Z.cpu.gpr.rax = Y.cpu.gpr.r12 → Z.cpu.gpr.rbx = g.rbx →
      Z.cpu.gpr.rbp = g.rbp → Z.cpu.gpr.r12 = g.r12 → Z.cpu.gpr.r13 = g.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := stA g.rsp h208
  obtain ⟨vc, vbx, vbp, v12, v13⟩ := Vo_reads g cn V h208
  have hlt := g.rsp.isLt
  have kr : ∀ (x : Addr), x.toNat ≤ g.rsp.toNat → g.rsp.toNat - 48 ≤ x.toNat →
      rdq(W, x) = rdq(Vo g cn V, x) := fun x h1 h2 =>
    congrArg (ofBytesLE 64) (Sbrk.rd_eq (by omega) fun a b1 b2 =>
      hkp a (Or.inl (by omega)) fun he => by obtain ⟨b3, b4⟩ := he; omega)
  have kc : rdq(W, fb + 40#64) = cn := by
    rw [congrArg (ofBytesLE 64) (Sbrk.rd_eq hcb fun a b1 b2 =>
      hkp a (Or.inr ⟨b1, b2⟩) fun he => by obtain ⟨b3, b4⟩ := he; omega),
      congrArg (ofBytesLE 64) (Vo_rd g cn V h208 hcb hcd)]
    exact hcn
  have hc : rdq(W, Y.cpu.gpr.rsp + 152#64) = rdq(W, fb + 40#64) := by
    rw [hsp, kc, kr (aQ g.rsp + 152#64) (by omega) (by omega)]
    exact vc
  have hra' : rdq(W, Y.cpu.gpr.rsp + 200#64) = e₂.add j₂ := by
    rw [hsp, q200, kr g.rsp (Nat.le_refl _) (by omega),
      congrArg (ofBytesLE 64) (Vo_rd g cn V h208 hsb (Or.inr (Nat.le_refl _)))]
    exact hra
  refine opd_tail c hfs hin hK hA hrip (by rw [hsp]; exact hfd) (by rw [hsp, e5]; omega) hcl hc hin₂ h₂ hra' ?_
  intro Z t' hKZ hAZ hrZ z1 z2 z3 z4 z5 z6 z7 z8
  refine k Z t' hKZ hAZ hrZ (by rw [z1, hsp, q208]) z2 ?_ ?_ ?_ ?_ z7 z8
  · rw [z3, hsp, q168, kr _ (by omega) (by omega)]
    exact vbx
  · rw [z4, hsp, q176, kr _ (by omega) (by omega)]
    exact vbp
  · rw [z5, hsp, q184, kr _ (by omega) (by omega)]
    exact v12
  · rw [z6, hsp, q192, kr _ (by omega) (by omega)]
    exact v13

/-! ## The whole function: what it needs, what it gives -/

theorem nER {fb x : Addr} (he : ¬ ER fb x) : x.toNat < (errnoAt fb).toNat ∨ (errnoAt fb).toNat + 4 ≤ x.toNat := by
  rcases Nat.lt_or_ge x.toNat (errnoAt fb).toNat with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge x.toNat ((errnoAt fb).toNat + 4) with h2 | h2
    · exact absurd ⟨h1, h2⟩ he
    · exact Or.inr h2

/-- What every way keeps of the bytes `V` at the entry until `malloc`: all but the 304 bytes from `S - 296` and
`errno`. -/
def Kq (g : Gprs) (fb : Addr) (V W : Addr → Byte) : Prop :=
  ∀ a : Addr, a.toNat < g.rsp.toNat - 296 ∨ g.rsp.toNat + 8 ≤ a.toNat → ¬ ER fb a → W a = V a

theorem Kp_st {g : Gprs} {fb : Addr} {V₀ W : Addr → Byte} (h : Kp g fb V₀ W) (a : Addr) (bs : List Byte)
    (ha : a.toNat + bs.length ≤ g.rsp.toNat - 48)
    (hc : a.toNat + bs.length ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ a.toNat) :
    Kp g fb V₀ (Vst W a bs) := by
  intro x hx he
  have := g.rsp.isLt
  rw [Vst_out W a bs x (by omega) (by rcases hx with hx | ⟨hx1, hx2⟩ <;> omega)]
  exact h x hx he

theorem Kp_e {g : Gprs} {fb : Addr} {V₀ W : Addr → Byte} (h : Kp g fb V₀ W) (bs : List Byte) (hb : bs.length = 4)
    (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64) : Kp g fb V₀ (Vst W (errnoAt fb) bs) := by
  intro x hx he
  rw [Vst_out W _ bs x (by rw [hb]; exact hfe) (by rw [hb]; exact nER he)]
  exact h x hx he

theorem Kq_st {g : Gprs} {fb : Addr} {V W : Addr → Byte} (h : Kq g fb V W) (a : Addr) (bs : List Byte)
    (h1 : g.rsp.toNat - 296 ≤ a.toNat) (h2 : a.toNat + bs.length ≤ g.rsp.toNat + 8)
    (h3 : g.rsp.toNat + 8 ≤ 2 ^ 64) : Kq g fb V (Vst W a bs) := by
  intro x hx he
  rw [Vst_out W a bs x (by omega) (by omega)]
  exact h x hx he

theorem Kq_e {g : Gprs} {fb : Addr} {V W : Addr → Byte} (h : Kq g fb V W) (bs : List Byte) (hb : bs.length = 4)
    (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64) : Kq g fb V (Vst W (errnoAt fb) bs) := by
  intro x hx he
  rw [Vst_out W _ bs x (by rw [hb]; exact hfe) (by rw [hb]; exact nER he)]
  exact h x hx he

theorem Kq_Vo (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (fb : Addr) (h : 296 ≤ g.rsp.toNat) :
    Kq g fb V (Vo g cn V) :=
  fun x hx _ => Vo_out g cn V (by omega) x (by omega)

/-- A byte apart from the `DIR`'s 44. -/
theorem Vd_out (U : Addr → Byte) (p bp bx : BitVec 64) (hp : p.toNat + 44 ≤ 2 ^ 64) (x : Addr)
    (h : x.toNat < p.toNat ∨ p.toNat + 44 ≤ x.toNat) : Vd U p bp bx x = U x := by
  have e4 : (p + 4#64).toNat = p.toNat + 4 := tAdd p 4 (by omega)
  have e8 : (p + 8#64).toNat = p.toNat + 8 := tAdd p 8 (by omega)
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e24 : (p + 24#64).toNat = p.toNat + 24 := tAdd p 24 (by omega)
  have e32 : (p + 32#64).toNat = p.toNat + 32 := tAdd p 32 (by omega)
  have e40 : (p + 40#64).toNat = p.toNat + 40 := tAdd p 40 (by omega)
  dsimp only [Vd]
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length, e4, e8, e16, e24, e32, e40])
  all_goals omega

theorem Kp_Vd {g : Gprs} {fb : Addr} {V₀ W : Addr → Byte} (h : Kp g fb V₀ W) (p bp bx : BitVec 64)
    (ha : p.toNat + 44 ≤ g.rsp.toNat - 48)
    (hc : p.toNat + 44 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ p.toNat) :
    Kp g fb V₀ (Vd W p bp bx) := by
  intro x hx he
  have := g.rsp.isLt
  rw [Vd_out W p bp bx (by omega) x (by rcases hx with hx | ⟨hx1, hx2⟩ <;> omega)]
  exact h x hx he

/-- What `__opendir` needs of its frame (registers `g` at the entry, `S` = `g.rsp`), the stack guard and `errno`: the
296 bytes below `S` (its frame, a return address, `__open_nocancel`'s 88) in what the run may store into, those and
the return address in the footprint's data, the stack guard and `errno` apart from them and from each other, `errno`
in the footprint's data too (read after `malloc` fails). -/
structure OFr (F : Footprint) (Wl : List Rgn) (g : Gprs) (fb : Addr) : Prop where
  h296 : 296 ≤ g.rsp.toNat
  hsb : g.rsp.toNat + 8 ≤ 2 ^ 64
  hfw : ∀ i < 296, Foot Wl (Addr.add (g.rsp - 296#64) i)
  hfd : ∀ i < 304, Foot F.data (Addr.add (g.rsp - 296#64) i)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  hcd : (fb + 40#64).toNat + 8 ≤ g.rsp.toNat - 296 ∨ g.rsp.toNat + 8 ≤ (fb + 40#64).toNat
  fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)
  fed : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)
  hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64
  hed : (errnoAt fb).toNat + 4 ≤ g.rsp.toNat - 296 ∨ g.rsp.toNat + 8 ≤ (errnoAt fb).toNat
  hec : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat

/-- The events after `fstat`'s: `close`'s; or `malloc`'s (`Pe`); or both `malloc`s', then `close`'s. -/
def OEnd (Pe : List Event → Prop) (e : List Event) : Prop :=
  (∃ G r, e = [clsEv G r]) ∨ Pe e ∨ (∃ e₁ e₂, e = e₁ ++ e₂ ∧ Pe e₁ ∧ Pe e₂) ∨
    (∃ e₁ e₂ G r, e = e₁ ++ (e₂ ++ [clsEv G r]) ∧ Pe e₁ ∧ Pe e₂)

/-- `__opendir`'s events: none (the empty name); `openat`'s; or `openat`'s and `fstat`'s, then `OEnd`. -/
def OpdEv (Pe : List Event → Prop) (ev : List Event) : Prop :=
  ev = [] ∨ (∃ G r bs, ev = [Onc.oncEv G r bs]) ∨
    ∃ G r bs G' r' e, ev = [Onc.oncEv G r bs, fsEv G' r'] ++ e ∧ OEnd Pe e

/-- The events `tr`: `gev`, then `__opendir`'s. -/
def OT (Pe : List Event → Prop) (gev tr : List Event) : Prop := ∃ ev, tr = gev ++ ev ∧ OpdEv Pe ev

/-- What `__opendir` returns (`p`) with the bytes `W` at its end: null, or a `DIR` with its fields stored. -/
def ORes (p : BitVec 64) (W : Addr → Byte) : Prop :=
  p = 0#64 ∨ ∃ (U : Addr → Byte) (bp bx : BitVec 64), W = Vd U p bp bx

/-- The run after `__opendir` (registers `g`, bytes `V` at its entry, events `gev` before it), from its return to
`e₂ + j₂`, perhaps from a new start (`Seg`) after system calls: the registers a call keeps as at the entry, `rsp` 8
above, the bytes from `S` up but `errno`'s as at the entry, the events `OT`, the answer `ORes`. -/
def OpdK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (fb : Addr) (g : Gprs)
    (V : Addr → Byte) (e₂ : Addr) (j₂ : Nat) (gev : List Event) (Pe : List Event → Prop) : Prop :=
  ∀ (S Z : State) (tr : List Event) (W : Addr → Byte) (t' : Nat), Seg prof F Wl L S o → S.cpu.seg.fsBase = fb →
    S.thread.rseq = none → KeptW Wl S Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ →
    Z.cpu.gpr.rsp = g.rsp + 8#64 → Z.cpu.gpr.rbx = g.rbx → Z.cpu.gpr.rbp = g.rbp → Z.cpu.gpr.r12 = g.r12 →
    Z.cpu.gpr.r13 = g.r13 → Z.cpu.gpr.r14 = g.r14 → Z.cpu.gpr.r15 = g.r15 →
    (∀ a : Addr, g.rsp.toNat ≤ a.toNat → ¬ ER fb a → W a = V a) → OT Pe gev tr → ORes Z.cpu.gpr.rax W →
    GoG prof L o tr gP gE Z t'

/-- The registers a call keeps (`G'` as `G`). -/
def Keeps (G G' : Gprs) : Prop :=
  G'.rbx = G.rbx ∧ G'.rbp = G.rbp ∧ G'.r12 = G.r12 ∧ G'.r13 = G.r13 ∧ G'.r14 = G.r14 ∧ G'.r15 = G.r15

theorem Keeps.trans {A B C : Gprs} (h1 : Keeps A B) (h2 : Keeps B C) : Keeps A C :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem set4_rsp (G : Gprs) (v : BitVec 64) : (G.set 4 v).rsp = v := by cases G; rfl

theorem setK (G : Gprs) (x y : BitVec 64) : Keeps G ((G.set 4 x).set 0 y) := by
  unfold Keeps
  cases G
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After a `syscall` stretch's return: `rsp` set, the registers a call keeps as at the `syscall`. -/
theorem sysK (Y : State) (r v : BitVec 64) :
    (((sysGpr Y 2).set 0 r).set 4 v).rsp = v ∧ Keeps Y.cpu.gpr (((sysGpr Y 2).set 0 r).set 4 v) ∧
      ((errG ((sysGpr Y 2).set 0 r)).set 4 v).rsp = v ∧
      Keeps Y.cpu.gpr ((errG ((sysGpr Y 2).set 0 r)).set 4 v) := by
  unfold sysGpr errG Keeps
  generalize Y.cpu.gpr = G
  cases G
  exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- From 219, the bytes keeping those at the entry (`Kp`): to the end (`OpdK`). -/
theorem opd_fin {fb : Addr} {g : Gprs} {Pe : List Event → Prop} {S Y : State} {W : Addr → Byte}
    {tr : List Event} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (fr : OFr F Wl g fb) (hK : KeptW Wl S Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = opd_at.add 219) (hsp : Y.cpu.gpr.rsp = aQ g.rsp) (h14 : Y.cpu.gpr.r14 = g.r14)
    (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, g.rsp) = e₂.add j₂)
    (hT : OT Pe gev tr) (hR : ORes Y.cpu.gpr.r12 W) (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) :
    GoG prof L o tr gP gE Y t := by
  have h296 := fr.h296
  have hlt := g.rsp.isLt
  obtain ⟨-, -, -, -, e5, -⟩ := stA g.rsp (by omega)
  have t296 : (g.rsp - 296#64).toNat = g.rsp.toNat - 296 := tSub _ 296 (by omega)
  refine opd_join c hfs hin hK hA hrip hsp (by omega) fr.hsb
    (frw fr.hfd (fa (d := 96) (by omega) (by rw [e5, t296]; omega)) (by decide)) fr.hcl fr.hcb
    (by rcases fr.hcd with h | h <;> omega) (by rcases fr.hed with h | h <;> omega) fr.hec hkp rfl hin₂ h₂ hra ?_
  intro Z t' hKZ hAZ hrZ z1 z2 z3 z4 z5 z6 z7 z8
  exact K S Z tr W t' c hfs hrs hKZ hAZ hrZ z1 z3 z4 z5 z6 (z7.trans h14) (z8.trans h15)
    (fun a ha he => by rw [hkp a (Or.inl (by omega)) he]; exact Vo_out g _ V (by omega) a (Or.inr ha)) hT
    (by rw [z2]; exact hR)

/-- From a `call __close_nocancel` at `j` (`rsp` the frame): `close (edi)` answers `r`, the run goes on from the
state after it, its own start, at `j + 5` with `rsp` the frame, the registers a call keeps as at `j`, the bytes
keeping `Kp` (`errno` `-r` if `r` is an error). -/
theorem opd_cnc {fb : Addr} {g : Gprs} {V₀ : Addr → Byte} {S Y : State} {W : Addr → Byte} {j rel : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (fr : OFr F Wl g fb) (hK : KeptW Wl S Y)
    (hA : Agree F Y.proc.mm.mem W) (hj : j + 5 < 380) (hrip : Y.cpu.rip = opd_at.add j)
    (hd : Dec prof.feat opd j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : opd_at.add (j + 5) + BitVec.ofNat 64 rel = Cnc.cnc_at) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (hkp : Kp g fb V₀ W)
    (k : ∀ (S' Z : State) (r : BitVec 64) (W' : Addr → Byte) (t' : Nat), Seg prof F Wl L S' o →
      S'.cpu.seg.fsBase = fb → S'.thread.rseq = none → KeptW Wl S' Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = opd_at.add (j + 5) → Kp g fb V₀ W' → Z.cpu.gpr.rsp = aQ g.rsp → Keeps Y.cpu.gpr Z.cpu.gpr →
      GoG prof L o (gev ++ [clsEv (Y.cpu.gpr.set 4 (Y.cpu.gpr.rsp - 8)) r]) gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have h296 := fr.h296
  have hlt := g.rsp.isLt
  obtain ⟨-, -, -, -, -, -, e7, -⟩ := stA g.rsp (by omega)
  have t296 : (g.rsp - 296#64).toNat = g.rsp.toNat - 296 := tSub _ 296 (by omega)
  have hY8 : (Y.cpu.gpr.rsp - 8).toNat = g.rsp.toNat - 208 := by rw [hsp]; exact e7
  have hx : Y.cpu.gpr.rsp - 8 = Addr.add (g.rsp - 296#64) 88 := fa (by omega) (by rw [hY8, t296]; omega)
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd hinC (Cnc.lt_len (j := 0) (by decide)) htgt
    (frw fr.hfw hx (by decide)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hs₂ : Y₂.cpu.gpr.rsp = Y.cpu.gpr.rsp - 8 := by rw [hg₂]; exact set4_rsp _ _
  have hb8 : (64 : Nat) = 8 * 8 := rfl
  refine Cnc.cnc_ok c hfs hrs hinC hK₂ hA₂ hr₂ fr.fe fr.hfe (by rw [hs₂]; exact frw fr.hfd hx (by decide))
    (by rw [hs₂, hY8]; omega) (by rw [hs₂, hY8]; rcases fr.hed with h | h <;> omega) hin (lt_len hj)
    (by rw [hs₂, rd_Vst_self W (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add (j + 5)) 8) (toBytesLE_length _ _)
      (by rw [hY8]; omega), ofBytesLE_toBytesLE hb8]) ?_
  intro Y' S' Z r t' hKY' hAY' hgY' hrY' _ hS' c' hKZ hrZ hok herr
  subst hS'
  have hfs' : (sysSt (closeSt Y') 2 r).cpu.seg.fsBase = fb := by
    show Y'.cpu.seg.fsBase = fb
    rw [hKY'.seg]
    exact hfs
  have hrs' : (sysSt (closeSt Y') 2 r).thread.rseq = none := by
    show Y'.thread.rseq = none
    rw [hKY'.thread]
    exact hrs
  have hkp₁ : Kp g fb V₀ (Vst W (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add (j + 5)) 8)) :=
    Kp_st hkp _ _ (by rw [toBytesLE_length, hY8]; omega)
      (by rw [toBytesLE_length, hY8]; rcases fr.hcd with h | h <;> omega)
  have hKs : Keeps Y.cpu.gpr Y'.cpu.gpr := by rw [hgY', hg₂]; exact setK _ _ _
  obtain ⟨s1, s2, s3, s4⟩ := sysK Y' r (Y₂.cpu.gpr.rsp + 8)
  have hsp' : Y₂.cpu.gpr.rsp + 8 = aQ g.rsp := by rw [hs₂, hsp]; exact BitVec.sub_add_cancel _ _
  rw [hg₂]
  by_cases he : CloseErr r
  · obtain ⟨hAZ, hgZ⟩ := herr he
    exact k _ Z r _ t' c' hfs' hrs' hKZ hAZ hrZ (Kp_e hkp₁ _ (toBytesLE_length _ _) fr.hfe)
      (by rw [hgZ, s3, hsp']) (by rw [hgZ]; exact hKs.trans s4)
  · obtain ⟨hAZ, hgZ⟩ := hok he
    exact k _ Z r _ t' c' hfs' hrs' hKZ hAZ hrZ hkp₁ (by rw [hgZ, s1, hsp']) (by rw [hgZ]; exact hKs.trans s2)

/-- From 270 (`fstat` failing, or not a directory): `__close_nocancel (fd)`, then to the end with null. -/
theorem opd_e270 {fb : Addr} {g : Gprs} {Pe : List Event → Prop} {S Y : State} {W : Addr → Byte}
    {tr : List Event} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (fr : OFr F Wl g fb) (hK : KeptW Wl S Y)
    (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = opd_at.add 270) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (h14 : Y.cpu.gpr.r14 = g.r14) (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, g.rsp) = e₂.add j₂)
    (hT : ∀ G r, OT Pe gev (tr ++ [clsEv G r])) (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) :
    GoG prof L o tr gP gE Y t := by
  refine (c_270 prof fb).run c hfs hin _ hK hA hrip (vc_270 (g := Y.cpu.gpr)) ?_
  rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  refine opd_cnc c hfs hrs hin hinC fr hK₁ hA₁ (by decide) hr₁ (call_275 _) (by decide)
    (by rw [hg₁, hsp]) hkp ?_
  intro S' Z r W' t' c' hfs' hrs' hKZ hAZ hrZ hkp' zs zk
  refine (c_280 prof fb).run c' hfs' hin _ hKZ hAZ hrZ (vc_280 (g := Z.cpu.gpr)) ?_
  rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Z₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₂
  obtain ⟨-, -, z12, -, z14, z15⟩ := zk
  exact opd_fin c' hfs' hrs' hin fr hK₂ hA₂ hr₂ (by rw [hg₂, zs]) (by rw [hg₂, z14, hg₁]; exact h14)
    (by rw [hg₂, z15, hg₁]; exact h15) hkp' hin₂ h₂ hra (hT _ _) (Or.inl (by rw [hg₂, z12, hg₁])) K

/-- From the return of the second `malloc` (337): its block not null, the `DIR`'s fields stored, to the end with the
block; null, `errno` kept over `__close_nocancel (fd)`, to the end with null. -/
theorem opd_r337 {fb : Addr} {g : Gprs} {Pe : List Event → Prop} {S Y : State} {W : Addr → Byte}
    {tr : List Event} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (fr : OFr F Wl g fb) (hK : KeptW Wl S Y)
    (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = opd_at.add 337) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (h14 : Y.cpu.gpr.r14 = g.r14) (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W)
    (hblk : Y.cpu.gpr.rax ≠ 0#64 → (∀ i < 44, Foot Wl (Addr.add Y.cpu.gpr.rax i)) ∧
      Y.cpu.gpr.rax.toNat + 44 ≤ g.rsp.toNat - 48 ∧
      (Y.cpu.gpr.rax.toNat + 44 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ Y.cpu.gpr.rax.toNat))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, g.rsp) = e₂.add j₂)
    (hT : OT Pe gev tr) (hTc : ∀ G r, OT Pe gev (tr ++ [clsEv G r]))
    (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) : GoG prof L o tr gP gE Y t := by
  by_cases hz : Y.cpu.gpr.rax = 0#64
  · refine (c_337 prof fb).run c hfs hin _ hK hA hrip (vc_337z (g := Y.cpu.gpr) hz fr.fed) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    refine opd_cnc c hfs hrs hin hinC fr hK₁ hA₁ (by decide) hr₁ (call_366 _) (by decide)
      (by rw [hg₁, hsp]) hkp ?_
    intro S' Z r W' t' c' hfs' hrs' hKZ hAZ hrZ hkp' zs zk
    obtain ⟨zbx, -, z12, -, z14, z15⟩ := zk
    refine (c_371 prof fb).run c' hfs' hin _ hKZ hAZ hrZ (vc_371 (g := Z.cpu.gpr) (by rw [zbx, hg₁]) fr.fe) ?_
    rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Z₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst V₂
    exact opd_fin c' hfs' hrs' hin fr hK₂ hA₂ hr₂ (by rw [hg₂, zs]) (by rw [hg₂, z14, hg₁]; exact h14)
      (by rw [hg₂, z15, hg₁]; exact h15) (Kp_e hkp' _ (toBytesLE_length _ _) fr.hfe) hin₂ h₂ hra (hTc _ _)
      (Or.inl (by rw [hg₂, z12, hg₁])) K
  · obtain ⟨hdw, hd1, hd2⟩ := hblk hz
    have hlt := g.rsp.isLt
    have a4 : (Y.cpu.gpr.rax + 4#64).toNat = Y.cpu.gpr.rax.toNat + 4 := tAdd _ 4 (by omega)
    have a8 : (Y.cpu.gpr.rax + 8#64).toNat = Y.cpu.gpr.rax.toNat + 8 := tAdd _ 8 (by omega)
    have a16 : (Y.cpu.gpr.rax + 16#64).toNat = Y.cpu.gpr.rax.toNat + 16 := tAdd _ 16 (by omega)
    have a24 : (Y.cpu.gpr.rax + 24#64).toNat = Y.cpu.gpr.rax.toNat + 24 := tAdd _ 24 (by omega)
    have a32 : (Y.cpu.gpr.rax + 32#64).toNat = Y.cpu.gpr.rax.toNat + 32 := tAdd _ 32 (by omega)
    have a40 : (Y.cpu.gpr.rax + 40#64).toNat = Y.cpu.gpr.rax.toNat + 40 := tAdd _ 40 (by omega)
    refine (c_337 prof fb).run c hfs hin _ hK hA hrip (vc_337 (g := Y.cpu.gpr) hz) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    have h12 : Y₁.cpu.gpr.r12 = Y.cpu.gpr.rax := by rw [hg₁]
    have hbp : Y₁.cpu.gpr.rbp = Y.cpu.gpr.rbp := by rw [hg₁]
    have hbx : Y₁.cpu.gpr.rbx = Y.cpu.gpr.rbx := by rw [hg₁]
    refine (c_165 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
      (vc_165 (g := Y₁.cpu.gpr) (by rw [h12]; exact frw hdw (fa (d := 0) (by omega) (by simp)) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 4) (by omega) a4) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 8) (by omega) a8) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 16) (by omega) a16) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 24) (by omega) a24) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 32) (by omega) a32) (by decide))
        (by rw [h12]; exact frw hdw (fa (d := 40) (by omega) a40) (by decide))) ?_
    rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst V₂
    rw [h12, hbp, hbx] at hA₂
    exact opd_fin c hfs hrs hin fr hK₂ hA₂ hr₂ (by rw [hg₂, hg₁, hsp]) (by rw [hg₂, hg₁]; exact h14)
      (by rw [hg₂, hg₁]; exact h15) (Kp_Vd hkp _ _ _ hd1 hd2) hin₂ h₂ hra hT
      (Or.inr ⟨W, Y.cpu.gpr.rbp, Y.cpu.gpr.rbx, by rw [hg₂, h12]⟩) K

/-! ## `malloc`, the open and `fstat`: to the end from the entry -/

theorem Kp_refl (g : Gprs) (fb : Addr) (V₀ : Addr → Byte) : Kp g fb V₀ V₀ := fun _ _ _ => rfl

theorem Kq_refl (g : Gprs) (fb : Addr) (V : Addr → Byte) : Kq g fb V V := fun _ _ _ => rfl

/-- A store in the frame below the stack guard's slot keeps `Kp`. -/
theorem Kp_fs {g : Gprs} {fb : Addr} {V₀ W : Addr → Byte} (fr : OFr F Wl g fb) (h : Kp g fb V₀ W) (a : Addr)
    (bs : List Byte) (h1 : g.rsp.toNat - 296 ≤ a.toNat) (h2 : a.toNat + bs.length ≤ g.rsp.toNat - 48) :
    Kp g fb V₀ (Vst W a bs) :=
  Kp_st h a bs h2 (by have := fr.hcd; omega)

/-- A store in the frame below the stack guard's slot keeps `Kq`. -/
theorem Kq_fs {g : Gprs} {fb : Addr} {V W : Addr → Byte} (fr : OFr F Wl g fb) (h : Kq g fb V W) (a : Addr)
    (bs : List Byte) (h1 : g.rsp.toNat - 296 ≤ a.toNat) (h2 : a.toNat + bs.length ≤ g.rsp.toNat - 48) :
    Kq g fb V (Vst W a bs) :=
  Kq_st h a bs h1 (by omega) fr.hsb

theorem rd_ret (W : Addr → Byte) (a e : Addr) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst W a (toBytesLE e 8), a) = e := by
  rw [rd_Vst_self W a (toBytesLE e 8) (toBytesLE_length _ _) ha, ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]

theorem set4K (G : Gprs) (v : BitVec 64) : Keeps G (G.set 4 v) := by
  unfold Keeps
  cases G
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bsz_le (x : BitVec 64) : 32768 ≤ (bsz x).toNat ∧ (bsz x).toNat ≤ 1048576 := by
  unfold bsz
  split
  · exact ⟨by decide, by decide⟩
  · split
    · exact ⟨by decide, by decide⟩
    · rename_i h1 h2
      exact ⟨by omega, by omega⟩

/-- `errno` (`fs:-0x48`) for a TLS block at or above `0x7a86e8`. -/
theorem tE (fb : Addr) (h : 8029928 ≤ fb.toNat) : (errnoAt fb).toNat = fb.toNat - 72 := by
  show (fb + 18446744073709551544#64).toNat = fb.toNat - 72
  have := fb.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `Mal.Gl` for bytes that agree from `0x792980` up to `E` but for the word `main_arena.top` and `errno` (the tcache
`C` above the TLS words). -/
theorem gl_mvE {F : Footprint} {Wl : List Rgn} {fb C : Addr} {E : Nat} {V W : Addr → Byte} (h : Mal.Gl F Wl fb C V)
    (hf1 : 8029928 ≤ fb.toNat) (hf2 : fb.toNat + 48 ≤ E) (hc1 : fb.toNat + 64 ≤ C.toNat) (hc2 : C.toNat + 128 ≤ E)
    (hE : E < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < E → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → ¬ ER fb a →
      W a = V a) :
    Mal.Gl F Wl fb C W := by
  obtain ⟨f24, -, f40⟩ := Mal.fofs fb (by omega) (by omega)
  have eE := tE fb hf1
  have R : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat ∧ x.toNat + n ≤ E →
      x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat → x.toNat + n ≤ fb.toNat - 72 ∨ fb.toNat - 68 ≤ x.toNat →
      List.map W (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h1 h3 h4 => Sbrk.rd_eq (by omega) fun a a1 a2 =>
      hW a (by omega) (by omega) (by omega) fun he => by obtain ⟨he1, he2⟩ := he; omega
  have Rc : ∀ (x n : Nat), 7940480 ≤ x ∧ x + n ≤ 8013232 → x + n ≤ 7940768 ∨ 7940776 ≤ x →
      List.map W (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
    fun x n h1 h3 => R _ n (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
      (by rw [BitVec.toNat_ofNat]; omega)
  exact
    { h with
      hk := by rw [Rc 7940656 8 (by omega) (by omega)]; exact h.hk
      tc := by rw [R _ 8 (by rw [f40]; omega) (by rw [f40]; omega) (by rw [f40]; omega)]; exact h.tc
      cn := fun i hi => by
        have e : (C + BitVec.ofNat 64 (2 * i)).toNat = C.toNat + 2 * i := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [R _ 2 (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)]
        exact h.cn i hi
      t1 := by rw [R _ 4 (by rw [f24]; omega) (by rw [f24]; omega) (by rw [f24]; omega)]; exact h.t1
      gm := by rw [Rc 8013224 8 (by omega) (by omega)]; exact h.gm
      fc := by rw [Rc 7940680 4 (by omega) (by omega)]; exact h.fc
      fz := fun k hk => by rw [Rc (7940688 + 8 * k) 8 (by omega) (by omega)]; exact h.fz k hk
      bk := fun i i1 i2 => by rw [Rc (7940776 + 16 * i) 8 (by omega) (by omega)]; exact h.bk i i1 i2
      lb := fun i i1 i2 => by rw [Rc (7940768 + 16 * i) 8 (by omega) (by omega)]; exact h.lb i i1 i2
      tb := by rw [Rc 7940592 8 (by omega) (by omega)]; exact h.tb
      un := by rw [Rc 7940792 8 (by omega) (by omega)]; exact h.un
      m0 := by rw [Rc 7942816 4 (by omega) (by omega)]; exact h.m0
      m1 := by rw [Rc 7942820 4 (by omega) (by omega)]; exact h.m1
      m2 := by rw [Rc 7942824 4 (by omega) (by omega)]; exact h.m2
      m3 := by rw [Rc 7942828 4 (by omega) (by omega)]; exact h.m3
      p0 := by rw [Rc 8013220 4 (by omega) (by omega)]; exact h.p0 }

/-- `Mal.Hp` for bytes that agree from `0x792980` to `hi` but for `errno`. -/
theorem hp_mvE {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V W : Addr → Byte}
    (h : Mal.Hp F Wl fb hi m V) (hm : 16 ≤ m)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi → ¬ ER fb a → W a = V a) :
    Mal.Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  have eE := tE fb hf1
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, gl_mvE (E := T.toNat) G hf1 hf2 hc1 hc2 (by omega) fun a a1 a2 _ a4 =>
    hW a a1 (by omega) a4, hf1, hf2, hc1, hc2, hT, hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
  · rw [Sbrk.rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by rw [et] at a1; omega) (by rw [et] at a2; omega) fun he => by
        obtain ⟨he1, he2⟩ := he; rw [et] at a2; omega]
    exact htop
  · rw [Sbrk.rd_eq (V := V) (x := T + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by rw [e8] at a1; omega) (by rw [e8] at a2; omega) fun he => by
        obtain ⟨he1, he2⟩ := he; rw [e8] at a1; omega]
    exact hsz
  · rw [Sbrk.rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by rw [es] at a1; omega) (by rw [es] at a2; omega) fun he => by
        obtain ⟨he1, he2⟩ := he; rw [es] at a2; omega]
    exact hsm

/-- The budget for `__opendir`'s two `malloc`s: `Mal.MalB` of `bsz _ + 48` (at most `0x100030`) and of `0x2030`. -/
abbrev oB : Nat := 8288 + 1048672

/-- `malloc`'s side of `__opendir` (registers `g`, bytes `V` at its entry, the heap's bytes below `hi`): `malloc` as
`Mal.AtHW` (`Mal.at_hpW` gives it), the heap's invariant `Pm` with the budget `oB` of both calls at the entry and kept
by any change of the frame and `errno`, `hi` 424 bytes below `rsp` (216 below `malloc`'s return address), the 224
bytes from there in what the run may store into, the stack guard above `0x792ba8`, and `malloc`'s events none (`Pe`
of `[]`). -/
structure OMal (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle)
    (fb : Addr) (g : Gprs) (V : Addr → Byte) (hi : Nat) (Pm : Nat → (Addr → Byte) → Prop)
    (Pe : List Event → Prop) : Prop where
  mh : Mal.AtHW prof F Wl L o fb hi Mal.mal_at Pm
  hP0 : Pm oB V
  hPS : ∀ k W W', Pm k W → Kq g fb W W' → Pm k W'
  hhi : hi + 424 ≤ g.rsp.toNat
  hsw : ∀ i < 224, Foot Wl (Addr.add (aQ g.rsp - 8 - 216#64) i)
  hfb : 7940776 ≤ (fb + 40#64).toNat
  hPe : Pe []

/-- `OMal` from `Mal.at_hpW`: `Pm k` the heap with a top of at least `k + m₀` bytes (`16 ≤ m₀`), `Pe` no events. -/
theorem omal_hp {fb : Addr} {g : Gprs} {V : Addr → Byte} {hi m₀ : Nat} (hinN : CodeIn L Mnx.mnx_at Mnx.mnx)
    (hinI : CodeIn L Imm.imm_at Imm.imm) (hH : Mal.Hp F Wl fb hi (oB + m₀) V) (hm : 16 ≤ m₀)
    (hhi : hi + 424 ≤ g.rsp.toNat) (hsw : ∀ i < 224, Foot Wl (Addr.add (aQ g.rsp - 8 - 216#64) i)) :
    OMal prof F Wl L o fb g V hi (fun k W => Mal.Hp F Wl fb hi (k + m₀) W) (fun e => e = []) where
  mh := Mal.at_hpW hinN hinI
  hP0 := hH
  hPS := fun k W W' hW hq => hp_mvE hW (by omega) fun a _ a2 he => hq a (.inl (by omega)) he
  hhi := hhi
  hsw := hsw
  hfb := by
    obtain ⟨_, T, _, _, _, hf1, hf2, -, -, -, hTh, hhi', -⟩ := hH
    rw [tAdd fb 40 (by omega)]
    omega
  hPe := rfl

/-- The `name` (`rdi`, `m` bytes not 0, then a 0) for `__open_nocancel`: its 8-byte words in the footprint's data and
below the end of the user address space, apart from the frame. -/
structure ONm (prof : Profile) (F : Footprint) (g : Gprs) (V : Addr → Byte) (m : Nat) : Prop where
  hm : m < pathMax
  htop : g.rdi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat
  hpl : ∀ i < 8 * (m / 8 + 1), Foot F.data (g.rdi.add i)
  hpd : g.rdi.toNat + 8 * (m / 8 + 1) ≤ g.rsp.toNat - 296 ∨ g.rsp.toNat + 8 ≤ g.rdi.toNat
  hnz : ∀ i < m, V (g.rdi.add i) ≠ 0
  hz : V (g.rdi.add m) = 0

theorem OT_f {Pe : List Event → Prop} {gev e : List Event} {G G' : Gprs} {r : BitVec 64} {bs : List Byte}
    {r' : FsOut} (h : OEnd Pe e) : OT Pe gev (gev ++ ([Onc.oncEv G r bs] ++ ([fsEv G' r'] ++ e))) :=
  ⟨[Onc.oncEv G r bs, fsEv G' r'] ++ e, by simp, Or.inr (Or.inr ⟨G, r, bs, G', r', e, rfl, h⟩)⟩

/-- From a `call malloc` at `j` (`rsp` the frame), the bytes keeping the heap's invariant with the budget `k + B`
(`Mal.MalB` of `rdi`): the run goes on from a state after it, its own start, at `j + 5` with `rsp` the frame, the
registers a call keeps as at `j`, the bytes keeping `Kp` and the invariant with the budget `k`, the block (`n` = `rdi`
at `j`) in what the run may store into, below the frame and apart from the stack guard. -/
theorem opd_mal {fb : Addr} {g : Gprs} {V₀ : Addr → Byte} {hi : Nat} {Pm : Nat → (Addr → Byte) → Prop}
    {Pe : List Event → Prop} {S Y : State} {W : Addr → Byte} {j rel k B : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinM : CodeIn L Mal.mal_at Mal.mal) (fr : OFr F Wl g fb)
    (om : OMal prof F Wl L o fb g V hi Pm Pe) (hK : KeptW Wl S Y) (hA : Agree F Y.proc.mm.mem W)
    (hj : j + 5 < 380) (hrip : Y.cpu.rip = opd_at.add j) (hd : Dec prof.feat opd j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : opd_at.add (j + 5) + BitVec.ofNat 64 rel = Mal.mal_at) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (hkp : Kp g fb V₀ W) (hPm : Pm (k + B) W) (hB : Mal.MalB Y.cpu.gpr.rdi B)
    (kc : ∀ (S' Z : State) (ev : List Event) (W' : Addr → Byte) (t' : Nat), Seg prof F Wl L S' o →
      S'.cpu.seg.fsBase = fb → S'.thread.rseq = none → KeptW Wl S' Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = opd_at.add (j + 5) → Pe ev → Pm k W' → Kp g fb V₀ W' → Z.cpu.gpr.rsp = aQ g.rsp →
      Keeps Y.cpu.gpr Z.cpu.gpr →
      (Z.cpu.gpr.rax ≠ 0#64 → (∀ i < Y.cpu.gpr.rdi.toNat, Foot Wl (Addr.add Z.cpu.gpr.rax i)) ∧
        Z.cpu.gpr.rax.toNat + Y.cpu.gpr.rdi.toNat ≤ g.rsp.toNat - 424 ∧
        (Z.cpu.gpr.rax.toNat + Y.cpu.gpr.rdi.toNat ≤ (fb + 40#64).toNat ∨
          (fb + 40#64).toNat + 8 ≤ Z.cpu.gpr.rax.toNat)) →
      GoG prof L o (gev ++ ev) gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have h296 := fr.h296
  have hlt := g.rsp.isLt
  have hhi := om.hhi
  have hfb := om.hfb
  have hcb := fr.hcb
  obtain ⟨-, -, -, -, -, -, e7, -⟩ := stA g.rsp (by omega)
  have t296 : (g.rsp - 296#64).toNat = g.rsp.toNat - 296 := tSub _ 296 (by omega)
  have hY8 : (Y.cpu.gpr.rsp - 8).toNat = g.rsp.toNat - 208 := by rw [hsp]; exact e7
  have hx : Y.cpu.gpr.rsp - 8 = Addr.add (g.rsp - 296#64) 88 := fa (by omega) (by rw [hY8, t296]; omega)
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd hinM (Mal.lt_len (j := 0) (by decide)) htgt
    (frw fr.hfw hx (by decide)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hs₂ : Y₂.cpu.gpr.rsp = Y.cpu.gpr.rsp - 8 := by rw [hg₂]; exact set4_rsp _ _
  have hsY : Y₂.cpu.gpr.rsp = aQ g.rsp - 8 := by rw [hs₂, hsp]
  have hYt : Y₂.cpu.gpr.rsp.toNat = g.rsp.toNat - 208 := by rw [hs₂]; exact hY8
  have hd₂ : Y₂.cpu.gpr.rdi = Y.cpu.gpr.rdi := by rw [hg₂] <;> rfl
  have hKY : Keeps Y.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact set4K _ _
  have hp₁ := Kp_fs fr hkp (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add (j + 5)) 8) (by rw [hY8]; omega)
    (by rw [toBytesLE_length, hY8]; omega)
  have hq : Kq g fb W (Vst W (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add (j + 5)) 8)) :=
    Kq_fs fr (Kq_refl g fb W) _ _ (by rw [hY8]; omega) (by rw [toBytesLE_length, hY8]; omega)
  have h40 : (fb + 40#64).toNat ≤ fb.toNat + 40 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine om.mh c hfs hK₂ hA₂ hr₂ (om.hPS _ _ _ hPm hq) (by rw [hd₂]; exact hB) (by rw [hYt]; omega)
    (by rw [hYt]; omega) (by rw [hsY]; exact om.hsw) hin (lt_len hj)
    (by rw [hs₂]; exact rd_ret W _ _ (by rw [hY8]; omega)) ?_
  intro Z t' V₂ p hKZ hAZ hrZ zsp zax zbx zbp z12 z13 z14 z15 _ hpf hpe hfoot hV hPmW _ _ _
  rw [hd₂] at hpe hfoot
  have hkpZ : Kp g fb V₀ V₂ := fun a ha he => by
    have hva : V₂ a = Vst W (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add (j + 5)) 8) a := by
      refine hV a ?_
      rcases ha with ha | ha
      · exact .inr (.inr ⟨by omega, .inr (by rw [hYt]; omega)⟩)
      · exact .inr (.inl ⟨by omega, by omega⟩)
    rw [hva]
    exact hp₁ a ha he
  have hzs : Z.cpu.gpr.rsp = aQ g.rsp := by
    rw [zsp, hsY]
    exact BitVec.sub_add_cancel _ _
  have hblk : Z.cpu.gpr.rax ≠ 0#64 → (∀ i < Y.cpu.gpr.rdi.toNat, Foot Wl (Addr.add Z.cpu.gpr.rax i)) ∧
      Z.cpu.gpr.rax.toNat + Y.cpu.gpr.rdi.toNat ≤ g.rsp.toNat - 424 ∧
      (Z.cpu.gpr.rax.toNat + Y.cpu.gpr.rdi.toNat ≤ (fb + 40#64).toNat ∨
        (fb + 40#64).toNat + 8 ≤ Z.cpu.gpr.rax.toNat) := fun _ => by
    rw [zax]
    refine ⟨fun i hi' => ?_, by omega, .inr (by omega)⟩
    have e := toNat_add_of_fits (a := p) (i := i) (n := Y.cpu.gpr.rdi.toNat) hi' (by omega)
    exact (hfoot _ (by rw [e]; omega) (by rw [e]; omega)).1
  have h := kc S Z [] V₂ t' c hfs hrs hKZ hAZ hrZ om.hPe (hPmW V₂ fun _ _ _ _ => rfl) hkpZ hzs
    (hKY.trans ⟨zbx, zbp, z12, z13, z14, z15⟩) hblk
  rw [List.append_nil] at h
  exact h

/-- From the return of the first `malloc` (153): its block not null, the `DIR`'s fields stored, to the end with the
block; null, `malloc (0x2030)`, then from its return (`opd_r337`). -/
theorem opd_m1 {fb : Addr} {g : Gprs} {hi : Nat} {Pm : Nat → (Addr → Byte) → Prop} {Pe : List Event → Prop}
    {S Y : State} {W : Addr → Byte} {tr : List Event} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (hinM : CodeIn L Mal.mal_at Mal.mal)
    (fr : OFr F Wl g fb) (om : OMal prof F Wl L o fb g V hi Pm Pe) (hK : KeptW Wl S Y)
    (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = opd_at.add 153) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (h14 : Y.cpu.gpr.r14 = g.r14) (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W)
    (hPm : Pm 8288 W)
    (hblk : Y.cpu.gpr.rax ≠ 0#64 → (∀ i < 44, Foot Wl (Addr.add Y.cpu.gpr.rax i)) ∧
      Y.cpu.gpr.rax.toNat + 44 ≤ g.rsp.toNat - 48 ∧
      (Y.cpu.gpr.rax.toNat + 44 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ Y.cpu.gpr.rax.toNat))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, g.rsp) = e₂.add j₂)
    (hT : OT Pe gev tr) (hT2 : ∀ e, Pe e → OT Pe gev (tr ++ e) ∧ ∀ G r, OT Pe gev (tr ++ e ++ [clsEv G r]))
    (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) : GoG prof L o tr gP gE Y t := by
  have hlt := g.rsp.isLt
  by_cases hz : Y.cpu.gpr.rax = 0#64
  · refine (c_153 prof fb).run c hfs hin _ hK hA hrip (vc_153z (g := Y.cpu.gpr) hz) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    refine (c_322 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_322 (g := Y₁.cpu.gpr)) ?_
    rintro j' g' fl V₂ ⟨rfl, rfl, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst V₂
    have hdi : Y₂.cpu.gpr.rdi = 8240#64 := by rw [hg₂]
    have t8 : (8240#64 : BitVec 64).toNat = 8240 := rfl
    refine opd_mal (k := 0) (B := 8288) c hfs hrs hin hinM fr om hK₂ hA₂ (by decide) hr₂ (call_332 _) (by decide)
      (by rw [hg₂, hg₁, hsp]) hkp hPm (by rw [hdi]; exact ⟨by decide, by decide, by decide⟩) ?_
    intro S' Z ev W' t' c' hfs' hrs' hKZ hAZ hrZ hPe hPm' hkp' zs zk hb
    obtain ⟨-, -, -, -, z14, z15⟩ := zk
    rw [hdi, t8] at hb
    exact opd_r337 c' hfs' hrs' hin hinC fr hKZ hAZ hrZ zs (by rw [z14, hg₂, hg₁] <;> exact h14)
      (by rw [z15, hg₂, hg₁] <;> exact h15) hkp'
      (fun hz' => by obtain ⟨b1, b2, b3⟩ := hb hz'; exact ⟨fun i hi => b1 i (by omega), by omega, by omega⟩)
      hin₂ h₂ hra (hT2 ev hPe).1 (hT2 ev hPe).2 K
  · obtain ⟨hdw, hd1, hd2⟩ := hblk hz
    refine opd_dir c hfs hin hK hA hrip hz hdw (by omega) ?_
    intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁
    exact opd_fin c hfs hrs hin fr hK₁ hA₁ hr₁ (by rw [hg₁, hsp]) (by rw [hg₁] <;> exact h14)
      (by rw [hg₁] <;> exact h15) (Kp_Vd hkp _ _ _ hd1 hd2) hin₂ h₂ hra hT
      (Or.inr ⟨W, Y.cpu.gpr.rbp, Y.cpu.gpr.rbx, by rw [hg₁]⟩) K

/-- From the return of `__fxstat` (80), `rsp` the frame: its answer negative, or not a directory, `__close_nocancel`
and null (`opd_e270`); a directory, `malloc (bsz (st_blksize) + 48)`, then from its return (`opd_m1`). -/
theorem opd_s80 {fb : Addr} {g : Gprs} {hi : Nat} {Pm : Nat → (Addr → Byte) → Prop} {Pe : List Event → Prop}
    {S Y : State} {W : Addr → Byte} {tr : List Event} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (hinM : CodeIn L Mal.mal_at Mal.mal)
    (fr : OFr F Wl g fb) (om : OMal prof F Wl L o fb g V hi Pm Pe) (hK : KeptW Wl S Y)
    (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = opd_at.add 80) (hsp : Y.cpu.gpr.rsp = aQ g.rsp)
    (h14 : Y.cpu.gpr.r14 = g.r14) (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W)
    (hkq : Kq g fb V W) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, g.rsp) = e₂.add j₂) (hTc : ∀ G r, OT Pe gev (tr ++ [clsEv G r]))
    (hT1 : ∀ e, Pe e → OT Pe gev (tr ++ e) ∧
      ∀ e', Pe e' → OT Pe gev (tr ++ e ++ e') ∧ ∀ G r, OT Pe gev (tr ++ e ++ e' ++ [clsEv G r]))
    (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) : GoG prof L o tr gP gE Y t := by
  have h296 := fr.h296
  have hlt := g.rsp.isLt
  have hhi := om.hhi
  obtain ⟨-, -, -, -, e5, -⟩ := stA g.rsp (by omega)
  have t296 : (g.rsp - 296#64).toNat = g.rsp.toNat - 296 := tSub _ 296 (by omega)
  have q24 : Y.cpu.gpr.rsp + 24#64 = Addr.add (g.rsp - 296#64) 120 :=
    fa (by omega) (by rw [hsp, tAdd _ 24 (by rw [e5]; omega), e5, t296]; omega)
  have q56 : Y.cpu.gpr.rsp + 56#64 = Addr.add (g.rsp - 296#64) 152 :=
    fa (by omega) (by rw [hsp, tAdd _ 56 (by rw [e5]; omega), e5, t296]; omega)
  cases hs : (BitVec.setWidth 32 Y.cpu.gpr.rax).msb
  · by_cases hm : ofBytesLE 32 ((byteAddrs (Y.cpu.gpr.rsp + 24#64) 4).map W) &&& 61440#32 = 16384#32
    · refine (c_80 prof fb).run c hfs hin _ hK hA hrip
        (vc_80 hs hm (frw fr.hfd q24 (by decide)) (frw fr.hfd q56 (by decide))) ?_
      rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      subst V₁
      have hdi : Y₁.cpu.gpr.rdi = bsz rdq(W, Y.cpu.gpr.rsp + 56#64) + 48#64 := by rw [hg₁]
      obtain ⟨b1, b2⟩ := bsz_le rdq(W, Y.cpu.gpr.rsp + 56#64)
      have t48 : (bsz rdq(W, Y.cpu.gpr.rsp + 56#64) + 48#64).toNat =
          (bsz rdq(W, Y.cpu.gpr.rsp + 56#64)).toNat + 48 := tAdd _ 48 (by omega)
      refine opd_mal (k := 8288) (B := 1048672) c hfs hrs hin hinM fr om hK₁ hA₁ (by decide) hr₁ (call_148 _)
        (by decide) (by rw [hg₁, hsp]) hkp (om.hPS _ _ _ om.hP0 hkq)
        (by rw [hdi]; unfold Mal.MalB; rw [t48]; exact ⟨by omega, by omega, by omega⟩) ?_
      intro S' Z ev W' t' c' hfs' hrs' hKZ hAZ hrZ hPe hPm' hkp' zs zk hb
      obtain ⟨-, -, -, -, z14, z15⟩ := zk
      rw [hdi, t48] at hb
      exact opd_m1 c' hfs' hrs' hin hinC hinM fr om hKZ hAZ hrZ zs (by rw [z14, hg₁] <;> exact h14)
        (by rw [z15, hg₁] <;> exact h15) hkp' hPm'
        (fun hz => by obtain ⟨d1, d2, d3⟩ := hb hz; exact ⟨fun i hi => d1 i (by omega), by omega, by omega⟩)
        hin₂ h₂ hra (hT1 ev hPe).1 (fun e he => (hT1 ev hPe).2 e he) K
    · refine (c_80 prof fb).run c hfs hin _ hK hA hrip (vc_80d hs hm (frw fr.hfd q24 (by decide)) fr.fe) ?_
      rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      subst V₁
      exact opd_e270 c hfs hrs hin hinC fr hK₁ hA₁ hr₁ (by rw [hg₁, hsp]) (by rw [hg₁] <;> exact h14)
        (by rw [hg₁] <;> exact h15) (Kp_e hkp _ (toBytesLE_length _ _) fr.hfe) hin₂ h₂ hra hTc K
  · refine (c_80 prof fb).run c hfs hin _ hK hA hrip (vc_80n hs) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact opd_e270 c hfs hrs hin hinC fr hK₁ hA₁ hr₁ (by rw [hg₁, hsp]) (by rw [hg₁] <;> exact h14)
      (by rw [hg₁] <;> exact h15) hkp hin₂ h₂ hra hTc K

/-- From the return of `__open_nocancel` (55), `rsp` the frame: its answer (`eax`) negative, null; else
`__fxstat (1, fd, rsp)`, then from its return (`opd_s80`). -/
theorem opd_s55 {fb : Addr} {g : Gprs} {hi : Nat} {Pm : Nat → (Addr → Byte) → Prop} {Pe : List Event → Prop}
    {S Y : State} {W : Addr → Byte} {G0 : Gprs} {r0 : BitVec 64} {bs0 : List Byte} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hrs : S.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinX : CodeIn L Fxs.fxs_at Fxs.fxs) (hinC : CodeIn L Cnc.cnc_at Cnc.cnc)
    (hinM : CodeIn L Mal.mal_at Mal.mal) (fr : OFr F Wl g fb) (om : OMal prof F Wl L o fb g V hi Pm Pe)
    (hup : g.rsp.toNat ≤ userPtrMax prof.feat) (hK : KeptW Wl S Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = opd_at.add 55) (hsp : Y.cpu.gpr.rsp = aQ g.rsp) (h14 : Y.cpu.gpr.r14 = g.r14)
    (h15 : Y.cpu.gpr.r15 = g.r15) (hkp : Kp g fb (Vo g rdq(V, fb + 40#64) V) W) (hkq : Kq g fb V W)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, g.rsp) = e₂.add j₂)
    (K : OpdK prof F Wl L o gP gE fb g V e₂ j₂ gev Pe) :
    GoG prof L o (gev ++ [Onc.oncEv G0 r0 bs0]) gP gE Y t := by
  have h296 := fr.h296
  have hlt := g.rsp.isLt
  obtain ⟨-, -, -, -, e5, -, e7, -⟩ := stA g.rsp (by omega)
  have t296 : (g.rsp - 296#64).toNat = g.rsp.toNat - 296 := tSub _ 296 (by omega)
  have hY8 : (Y.cpu.gpr.rsp - 8).toNat = g.rsp.toNat - 208 := by rw [hsp]; exact e7
  have hx : Y.cpu.gpr.rsp - 8 = Addr.add (g.rsp - 296#64) 88 := fa (by omega) (by rw [hY8, t296]; omega)
  cases hs : (BitVec.setWidth 32 Y.cpu.gpr.rax).msb
  · refine opd_stat c hfs hin hinX hK hA hrip hs (frw fr.hfw hx (by decide)) ?_
    intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁
    have hs₁ : Y₁.cpu.gpr.rsp = Y.cpu.gpr.rsp - 8 := by rw [hg₁]; exact set4_rsp _ _
    have hdx : Y₁.cpu.gpr.rdx = aQ g.rsp := by rw [← hsp, hg₁] <;> rfl
    have hdi1 : Y₁.cpu.gpr.rdi = 1#64 := by rw [hg₁] <;> rfl
    have hr14 : Y₁.cpu.gpr.r14 = g.r14 := by rw [hg₁] <;> exact h14
    have hr15 : Y₁.cpu.gpr.r15 = g.r15 := by rw [hg₁] <;> exact h15
    refine Fxs.fxs_ok c hfs hinX hK₁ hA₁ hr₁ fr.fe fr.hfe (by rw [hs₁]; exact frw fr.hfd hx (by decide))
      (by rw [hs₁, hY8]; omega) (by rw [hs₁, hY8]; rcases fr.hed with h | h <;> omega) (by rw [hdx, e5]; omega)
      (by rw [hdx]; exact frw fr.hfw (fa (d := 96) (by omega) (by rw [e5, t296]; omega)) (by decide))
      (by rw [hdx, hs₁, hY8, e5]; omega) hin (lt_len (j := 80) (by decide))
      (by rw [hs₁]; exact rd_ret _ _ _ (by rw [hY8]; omega)) (fun hv => absurd hv (by rw [hdi1]; decide)) ?_
    intro _ Y' Z r t' hgY' _ hok hKZ hrZ hsucc herr
    have hlen : r.bs.length ≤ 144 := by
      rcases hok with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · rw [h]
        exact Nat.zero_le _
    have hp1 := Kp_fs fr hkp (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 80) 8) (by rw [hY8]; omega)
      (by rw [toBytesLE_length, hY8]; omega)
    have hq1 := Kq_fs fr hkq (Y.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 80) 8) (by rw [hY8]; omega)
      (by rw [toBytesLE_length, hY8]; omega)
    have hp2 := Kp_fs fr hp1 Y₁.cpu.gpr.rdx r.bs (by rw [hdx, e5]; omega) (by rw [hdx, e5]; omega)
    have hq2 := Kq_fs fr hq1 Y₁.cpu.gpr.rdx r.bs (by rw [hdx, e5]; omega) (by rw [hdx, e5]; omega)
    obtain ⟨s1, s2, s3, s4⟩ := sysK Y' r.ret (Y₁.cpu.gpr.rsp + 8)
    have k14 : Y'.cpu.gpr.r14 = g.r14 := by rw [hgY'] <;> exact hr14
    have k15 : Y'.cpu.gpr.r15 = g.r15 := by rw [hgY'] <;> exact hr15
    have hZs : Y₁.cpu.gpr.rsp + 8 = aQ g.rsp := by rw [hs₁, hsp]; exact BitVec.sub_add_cancel _ _
    have hT : ∀ e, OEnd Pe e →
        OT Pe gev (gev ++ [Onc.oncEv G0 r0 bs0] ++ [fsEv (Fxs.fxG Y₁.cpu.gpr) r] ++ e) := fun e h => by
      simp only [List.append_assoc]
      exact OT_f h
    have hTc : ∀ G r', OT Pe gev (gev ++ [Onc.oncEv G0 r0 bs0] ++ [fsEv (Fxs.fxG Y₁.cpu.gpr) r] ++
        [clsEv G r']) := fun G r' => hT _ (Or.inl ⟨G, r', rfl⟩)
    have hT1 : ∀ e, Pe e → OT Pe gev (gev ++ [Onc.oncEv G0 r0 bs0] ++ [fsEv (Fxs.fxG Y₁.cpu.gpr) r] ++ e) ∧
        ∀ e', Pe e' → OT Pe gev (gev ++ [Onc.oncEv G0 r0 bs0] ++ [fsEv (Fxs.fxG Y₁.cpu.gpr) r] ++ e ++ e') ∧
          ∀ G r', OT Pe gev (gev ++ [Onc.oncEv G0 r0 bs0] ++ [fsEv (Fxs.fxG Y₁.cpu.gpr) r] ++ e ++ e' ++
            [clsEv G r']) := fun e he =>
      ⟨hT e (Or.inr (Or.inl he)), fun e' he' =>
        ⟨by
          have h := hT (e ++ e') (Or.inr (Or.inr (Or.inl ⟨e, e', rfl, he, he'⟩)))
          simp only [List.append_assoc] at h ⊢
          exact h,
        fun G r' => by
          have h := hT (e ++ (e' ++ [clsEv G r'])) (Or.inr (Or.inr (Or.inr ⟨e, e', G, r', rfl, he, he'⟩)))
          simp only [List.append_assoc] at h ⊢
          exact h⟩⟩
    by_cases he : CloseErr r.ret
    · obtain ⟨hAZ, hgZ⟩ := herr he
      exact opd_s80 c hfs hrs hin hinC hinM fr om hKZ hAZ hrZ (by rw [hgZ, s3, hZs])
        (by rw [hgZ, ← k14]; exact s4.2.2.2.2.1) (by rw [hgZ, ← k15]; exact s4.2.2.2.2.2)
        (Kp_e hp1 _ (toBytesLE_length _ _) fr.hfe) (Kq_e hq1 _ (toBytesLE_length _ _) fr.hfe) hin₂ h₂ hra
        hTc hT1 K
    · obtain ⟨hAZ, hgZ⟩ := hsucc he
      exact opd_s80 c hfs hrs hin hinC hinM fr om hKZ hAZ hrZ (by rw [hgZ, s1, hZs])
        (by rw [hgZ, ← k14]; exact s2.2.2.2.2.1) (by rw [hgZ, ← k15]; exact s2.2.2.2.2.2) hp2 hq2 hin₂ h₂ hra
        hTc hT1 K
  · refine (c_55 prof fb).run c hfs hin _ hK hA hrip (vc_55n hs) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact opd_fin c hfs hrs hin fr hK₁ hA₁ hr₁ (by rw [hg₁, hsp]) (by rw [hg₁] <;> exact h14)
      (by rw [hg₁] <;> exact h15) hkp hin₂ h₂ hra
      ⟨[Onc.oncEv G0 r0 bs0], rfl, Or.inr (Or.inl ⟨G0, r0, bs0, rfl⟩)⟩ (Or.inl (by rw [hg₁])) K

/-- `__opendir (name)` from its entry to its return: with the frame (`OFr`), `malloc`'s side (`OMal`) and the `name`
(`ONm`, `m` bytes before its 0), the run reaches the return address with `rsp` 8 above, the registers a call keeps as
at the entry, the bytes from `rsp` up but `errno`'s as at the entry, the events `OT` and the answer null or a `DIR`
(`ORes`), perhaps from a new start after the system calls (`OpdK`). -/
theorem opd_ok {fb : Addr} {X : State} {hi : Nat} {Pm : Nat → (Addr → Byte) → Prop} {Pe : List Event → Prop} {m : Nat}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinO : CodeIn L Onc.onc_at Onc.onc) (hinX : CodeIn L Fxs.fxs_at Fxs.fxs)
    (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (hinM : CodeIn L Mal.mal_at Mal.mal) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = opd_at) (fr : OFr F Wl X.cpu.gpr fb)
    (om : OMal prof F Wl L o fb X.cpu.gpr V hi Pm Pe) (nm : ONm prof F X.cpu.gpr V m)
    (hup : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (K : OpdK prof F Wl L o gP gE fb X.cpu.gpr V e₂ j₂ gev Pe) : GoG prof L o gev gP gE X t := by
  have h296 := fr.h296
  have hlt := X.cpu.gpr.rsp.isLt
  have hpd := nm.hpd
  have hum : userPtrMax prof.feat ≤ 2 ^ 64 := by unfold userPtrMax; split <;> decide
  have htop := nm.htop
  obtain ⟨e1, e2, e3, e4, -, e6, e7, e8⟩ := stA X.cpu.gpr.rsp (by omega)
  have t296 : (X.cpu.gpr.rsp - 296#64).toNat = X.cpu.gpr.rsp.toNat - 296 := tSub _ 296 (by omega)
  have hcn : rdq(P4 V X.cpu.gpr, fb + 40#64) = rdq(V, fb + 40#64) :=
    congrArg (ofBytesLE 64) (P4_rd V X.cpu.gpr (by omega) fr.hcb (by have := fr.hcd; omega))
  have hEw : Write.errnoAt fb = errnoAt fb := rfl
  have e0 : X.cpu.gpr.rdi.add (0 : Nat) = X.cpu.gpr.rdi :=
    BitVec.eq_of_toNat_eq (toNat_add_of_fits (n := 1) (by omega) (by omega))
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have hz0 := nm.hz
    rw [e0] at hz0
    refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0z hcn (by rw [Vo_rd X.cpu.gpr _ V (by omega) (by omega) (by omega), rd1]; exact hz0)
        (frw fr.hfw (fa (d := 288) (by omega) (by rw [e1, t296]; omega)) (by decide))
        (frw fr.hfw (fa (d := 280) (by omega) (by rw [e2, t296]; omega)) (by decide))
        (frw fr.hfw (fa (d := 272) (by omega) (by rw [e3, t296]; omega)) (by decide))
        (frw fr.hfw (fa (d := 264) (by omega) (by rw [e4, t296]; omega)) (by decide)) fr.hcl
        (frw fr.hfw (fa (d := 248) (by omega) (by rw [e6, t296]; omega)) (by decide))
        (fun i hi => nm.hpl i (by omega)) fr.fe) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact opd_fin c hfs hrs hin fr hK₁ hA₁ hr₁ (by rw [hg₁]) (by rw [hg₁]) (by rw [hg₁])
      (Kp_e (Kp_refl _ _ _) _ (toBytesLE_length _ _) fr.hfe) hin₂ h₂ hra ⟨[], by simp, Or.inl rfl⟩
      (Or.inl (by rw [hg₁])) K
  · have hne : ofBytesLE 8 ((byteAddrs X.cpu.gpr.rdi 1).map V) ≠ 0#8 := by
      rw [rd1]
      have h := nm.hnz 0 hm0
      rw [e0] at h
      exact h
    refine opd_open c hfs hin hinO hK hA hrip (by omega)
      (frw fr.hfw (fa (d := 88) (by omega) (by rw [e8, t296]; omega)) (by decide)) fr.hcl fr.hcb
      (by have := fr.hcd; omega) (fun i hi => nm.hpl i (by omega)) (by omega) hne ?_
    intro Y t₁ hKY hAY hrY hgY
    have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp - 8 := by rw [hgY]; exact set4_rsp _ _
    have hY8 : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 208 := by rw [hsY]; exact e7
    have hdY : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY] <;> rfl
    have hsiY : Y.cpu.gpr.rsi = 591872#64 := by rw [hgY] <;> rfl
    have y14 : Y.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hgY] <;> rfl
    have y15 : Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgY] <;> rfl
    have q88 : Y.cpu.gpr.rsp - 88#64 = Addr.add (X.cpu.gpr.rsp - 296#64) 0 :=
      fa (by omega) (by rw [tSub _ 88 (by omega), hY8, t296]; omega)
    have qY : Y.cpu.gpr.rsp = Addr.add (X.cpu.gpr.rsp - 296#64) 88 := fa (by omega) (by rw [hY8, t296]; omega)
    have vn : ∀ i ≤ m, Vst (Vo X.cpu.gpr rdq(V, fb + 40#64) V) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (opd_at.add 55) 8) (X.cpu.gpr.rdi.add i) = V (X.cpu.gpr.rdi.add i) := by
      intro i hi
      have e : (X.cpu.gpr.rdi.add i).toNat = X.cpu.gpr.rdi.toNat + i :=
        toNat_add_of_fits (n := 8 * (m / 8 + 1)) (by omega) (by omega)
      rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e7]; omega) (by rw [toBytesLE_length, e7, e]; omega)]
      exact Vo_out X.cpu.gpr _ V (by omega) _ (by rw [e]; omega)
    refine Onc.onc_ok c hfs hrs hinO hKY hAY hrY (by rw [hsiY]; decide) (by rw [hY8]; omega) (by rw [hY8]; omega)
      (frw fr.hfw q88 (by decide)) (frw fr.hfd q88 (by decide)) (frw fr.hfd qY (by decide)) fr.hcl fr.hcb
      (by rw [hY8]; have := fr.hcd; omega) fr.fe fr.hfe (by rw [hY8, hEw]; have := fr.hed; omega) fr.hec nm.hm
      (by rw [hdY]; exact htop) (by rw [hdY]; exact nm.hpl) (by rw [hdY, hY8]; omega)
      (by rw [hdY]; exact fun i hi => by rw [vn i (by omega)]; exact nm.hnz i hi)
      (by rw [hdY, vn m (Nat.le_refl _)]; exact nm.hz) hin (lt_len (j := 55) (by decide))
      (by rw [hsY]; exact rd_ret _ _ _ (by rw [e7]; omega)) ?_
    intro Y' S' Z r bs t' hKY' _ _ _ hcpu _ c' hrs' hKZ hrZ hregs hok herr
    obtain ⟨zsp, -, -, -, -, z14, z15⟩ := hregs
    have hfs' : S'.cpu.seg.fsBase = fb := by
      have h1 : S'.cpu.seg = (sysSt Y' 2 r).cpu.seg := by rw [hcpu]
      rw [h1]
      show Y'.cpu.seg.fsBase = fb
      rw [hKY'.seg]
      exact hfs
    have a88 : (Y.cpu.gpr.rsp - 88#64).toNat = X.cpu.gpr.rsp.toNat - 296 := by
      rw [tSub _ 88 (by omega), hY8]
      omega
    have a48 : (Y.cpu.gpr.rsp - 88#64 + 48#64).toNat = X.cpu.gpr.rsp.toNat - 248 := by
      rw [tAdd _ 48 (by omega), a88]
      omega
    have a24 : (Y.cpu.gpr.rsp - 88#64 + 24#64).toNat = X.cpu.gpr.rsp.toNat - 272 := by
      rw [tAdd _ 24 (by omega), a88]
      omega
    have hp0 := Kp_fs fr (Kp_refl X.cpu.gpr fb (Vo X.cpu.gpr rdq(V, fb + 40#64) V)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (opd_at.add 55) 8) (by rw [e7]; omega) (by rw [toBytesLE_length, e7]; omega)
    have hq0 := Kq_fs fr (Kq_Vo X.cpu.gpr rdq(V, fb + 40#64) V fb (by omega)) (aQ X.cpu.gpr.rsp - 8)
      (toBytesLE (opd_at.add 55) 8) (by rw [e7]; omega) (by rw [toBytesLE_length, e7]; omega)
    have hpO : Kp X.cpu.gpr fb (Vo X.cpu.gpr rdq(V, fb + 40#64) V)
        (Onc.oV (Vst (Vo X.cpu.gpr rdq(V, fb + 40#64) V) (aQ X.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 55) 8))
          Y.cpu.gpr fb) := by
      unfold Onc.oV
      exact Kp_fs fr (Kp_fs fr hp0 _ _ (by rw [a48]; omega) (by rw [toBytesLE_length, a48]; omega)) _ _
        (by rw [a24]; omega) (by rw [toBytesLE_length, a24]; omega)
    have hqO : Kq X.cpu.gpr fb V
        (Onc.oV (Vst (Vo X.cpu.gpr rdq(V, fb + 40#64) V) (aQ X.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 55) 8))
          Y.cpu.gpr fb) := by
      unfold Onc.oV
      exact Kq_fs fr (Kq_fs fr hq0 _ _ (by rw [a48]; omega) (by rw [toBytesLE_length, a48]; omega)) _ _
        (by rw [a24]; omega) (by rw [toBytesLE_length, a24]; omega)
    obtain ⟨W₁, hA₁, hp₁, hq₁⟩ : ∃ W₁, Agree F Z.proc.mm.mem W₁ ∧
        Kp X.cpu.gpr fb (Vo X.cpu.gpr rdq(V, fb + 40#64) V) W₁ ∧ Kq X.cpu.gpr fb V W₁ := by
      by_cases he : Write.WrErr r
      · exact ⟨_, (herr he).1, Kp_e hpO _ (toBytesLE_length _ _) fr.hfe, Kq_e hqO _ (toBytesLE_length _ _) fr.hfe⟩
      · exact ⟨_, (hok he).1, hpO, hqO⟩
    exact opd_s55 c' hfs' hrs' hin hinX hinC hinM fr om hup hKZ hA₁ hrZ
      (by rw [zsp, hsY]; exact BitVec.sub_add_cancel _ _) (by rw [z14, y14]) (by rw [z15, y15]) hp₁ hq₁
      hin₂ h₂ hra K


/-- `opd_ok` with `malloc` from `Mal.at_hpW` (`omal_hp`): the heap `Mal.Hp` with a top of at least `oB + m₀` bytes
below `hi` at the entry, `hi` 424 bytes below `rsp`, `malloc`'s 224 bytes of stack in what the run may store into, and
`malloc`'s events none. -/
theorem opd_okH {fb : Addr} {X : State} {hi m₀ m : Nat} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hrs : s₀.thread.rseq = none)
    (hin : CodeIn L opd_at opd) (hinO : CodeIn L Onc.onc_at Onc.onc) (hinX : CodeIn L Fxs.fxs_at Fxs.fxs)
    (hinC : CodeIn L Cnc.cnc_at Cnc.cnc) (hinM : CodeIn L Mal.mal_at Mal.mal) (hinN : CodeIn L Mnx.mnx_at Mnx.mnx)
    (hinI : CodeIn L Imm.imm_at Imm.imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = opd_at) (fr : OFr F Wl X.cpu.gpr fb) (hH : Mal.Hp F Wl fb hi (oB + m₀) V) (hm : 16 ≤ m₀)
    (hhi : hi + 424 ≤ X.cpu.gpr.rsp.toNat)
    (hsw : ∀ i < 224, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8 - 216#64) i)) (nm : ONm prof F X.cpu.gpr V m)
    (hup : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (K : OpdK prof F Wl L o gP gE fb X.cpu.gpr V e₂ j₂ gev fun e => e = []) : GoG prof L o gev gP gE X t :=
  opd_ok c hfs hrs hin hinO hinX hinC hinM hK hA hrip fr (omal_hp hinN hinI hH hm hhi hsw) nm hup hin₂ h₂ hra K

end FV7z.Opd
