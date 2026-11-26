import FV7z.Opd.Holds
import FV7z.Onc.Holds
import FV7z.Fxs.Holds
import FV7z.Cnc.Holds
/-!
# `__opendir` from its entry to its return (PLAN.md §M, M1)

The ways `Opd.Holds` leaves out, and the join at 219 every way meets at:

- `vc_0z` (the empty `name`: `errno` = `ENOENT`, 288), `vc_55n` (the open failing, 312), `vc_80n` (`fstat` failing),
  `vc_80d` (not a directory: `errno` = `ENOTDIR`, 256), `vc_270` (to `__close_nocancel`), `vc_280`, `vc_153z` (the
  first `malloc` failing, 322), `vc_337` (after the second `malloc (0x2030)`), `vc_371` (`errno` restored);
- `Kp`: what every way keeps of the bytes at the entry (from the stack guard's slot `S - 48` up, and the stack guard at
  `fs:0x28`); `opd_join`: from 219 with `Kp`, to the return address, `rax` = `r12`;
- `MalH`: what `__opendir` takes of `malloc` as a hypothesis (`Mal.AtH` covers at most 1024 bytes; `__opendir` asks
  for at least 32 KiB).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
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
    (exact fe) | (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

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
  all_goals vfin

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
  all_goals vfin

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
      g' = { g with rbx := 18446744073709551544#64, rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp),
        r12 := 0#64, r13 := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs (errnoAt fb) 4).map V)) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_337, W_349, o7, o16, Op.ldf, BitVec.and_self, z0, decide_true, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- `errno` restored from `r13d` (`rbx` its offset), to 219. -/
theorem vc_371 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hb : g.rbx = 18446744073709551544#64)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_371 fb F Wl (fun j' g' _ V' => j' = 219 ∧ g' = g ∧
      V' = Vst V (errnoAt fb) (toBytesLE (BitVec.setWidth 32 g.r13) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb ⊢
  subst hb
  wpx [W_371, o17, Op.stf]
  all_goals vfin

/-! ## The join at 219 -/

/-- What every way keeps of the bytes `V₀` at the entry (registers `g`, `S` = `g.rsp`): from the stack guard's slot
`S - 48` up, and the stack guard at `fs:0x28`. -/
def Kp (g : Gprs) (fb : Addr) (V₀ W : Addr → Byte) : Prop :=
  ∀ a : Addr,
    g.rsp.toNat - 48 ≤ a.toNat ∨ ((fb + 40#64).toNat ≤ a.toNat ∧ a.toNat < (fb + 40#64).toNat + 8) →
    W a = V₀ a

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
  have kr : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 → g.rsp.toNat - 48 ≤ x.toNat →
      rdq(W, x) = rdq(Vo g cn V, x) := fun x h1 h2 =>
    congrArg (ofBytesLE 64) (Sbrk.rd_eq h1 fun a b1 b2 => hkp a (Or.inl (by omega)))
  have kc : rdq(W, fb + 40#64) = cn := by
    rw [congrArg (ofBytesLE 64) (Sbrk.rd_eq hcb fun a b1 b2 => hkp a (Or.inr ⟨b1, b2⟩)),
      congrArg (ofBytesLE 64) (Vo_rd g cn V h208 hcb hcd)]
    exact hcn
  have hc : rdq(W, Y.cpu.gpr.rsp + 152#64) = rdq(W, fb + 40#64) := by
    rw [hsp, kc, kr (aQ g.rsp + 152#64) (by omega) (by omega)]
    exact vc
  have hra' : rdq(W, Y.cpu.gpr.rsp + 200#64) = e₂.add j₂ := by
    rw [hsp, q200, kr g.rsp hsb (by omega), congrArg (ofBytesLE 64) (Vo_rd g cn V h208 hsb (Or.inr (Nat.le_refl _)))]
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

end FV7z.Opd
