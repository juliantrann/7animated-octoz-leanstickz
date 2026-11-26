import FV7z.Sas.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `SysAllocStringLen` (PLAN.md §M, M1)

7-Zip 26.06's `SysAllocStringLen (s, len)` at `0x5a0010` in `7zzs` (`CPP/Common/MyWindows.cpp`): `push r12; push rbp;
push rbx`, `ebx` = `len`; `len` above `0x3ffffffc` (`ja`): 0 (`r8d` cleared, 96, the `ret` at 106). Else `r12d` =
`4 len`, `rbp` = `s`, `malloc (4 len + 8)` (the `call` at 34 to `0x633160`); a null result: 0 as above; else the length
word `[p] = 4 len`, `r8` = `p + 4`; `s` not null: `memcpy (p + 4, s, 4 len)` (the `call` at 65 to the PLT entry
`0x401070`), `r8` = its result; the terminator `[r8 + 4 len] = 0`, `rax` = `r8`, the registers popped, the `ret` at 88.

The callees are hypotheses, as in `FV7z/Vcl/Holds.lean`: continuations at their entries (`km`, `kc`), each given the
run from its return (the frame as it was, the callee's own post `Pm`, `Pc`) to the return address.

- `nn`, `n4`, `gM`, `Vp`: `len` and `4 len` zero-extended, the registers at the `call` of `malloc`, the bytes with the
  three registers pushed. `Va`, `qq`, `gC`: the bytes with the length word stored, the terminator's place, the
  registers at the `call` of `memcpy`.
- `vc_*`: the verification conditions of the pieces.
- `sas_z` (from 96), `sas_t` (from 73), `sas_m` (from the return of `malloc`, 39): to the return address, for a frame
  `r` (the three saved registers and the return address at `r`, `r + 8`, `r + 16`, `r + 24`).
- `sas_ok`: from the entry: `len` too large (`kb`); else through `malloc` (`km`), then a null result (`kz`), `s` null
  (`k0`), or through `memcpy` (`kc`, `k1`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sas

/-- The `call` of `malloc`. -/
def pcm : List Byte := [0xe8, 0x29, 0x31, 0x09, 0x00]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 602409] 5) := by dec_rfl
theorem wc_34 : pcm <+: sas.drop 34 := by decide +kernel
theorem call_34 (feat : Features) : Dec feat sas 34 (FV7z.mk .call 64 [.rel 602409] 5) :=
  Dec.shift (j := 34) (k := 0) (pcm_0 feat) wc_34 (Nat.zero_le _)

/-- The `call` of `memcpy` (its PLT entry). -/
def pcc : List Byte := [0xe8, 0x1a, 0x10, 0xe6, 0xff]
theorem pcc_0 : ∀ feat, Dec feat pcc 0 (FV7z.mk .call 64 [.rel 18446744073707851802] 5) := by dec_rfl
theorem wc_65 : pcc <+: sas.drop 65 := by decide +kernel
theorem call_65 (feat : Features) : Dec feat sas 65 (FV7z.mk .call 64 [.rel 18446744073707851802] 5) :=
  Dec.shift (j := 65) (k := 0) (pcc_0 feat) wc_65 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_88 : pret <+: sas.drop 88 := by decide +kernel
theorem ret_88 (feat : Features) : Dec feat sas 88 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 88) (k := 0) (pret_0 feat) w_88 (Nat.zero_le _)
theorem w_106 : pret <+: sas.drop 106 := by decide +kernel
theorem ret_106 (feat : Features) : Dec feat sas 106 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 106) (k := 0) (pret_0 feat) w_106 (Nat.zero_le _)

/-- The callees: glibc's `malloc` and `memcpy`'s PLT entry (code not proved here). -/
abbrev mal_at : Addr := 0x633160
abbrev cpy_at : Addr := 0x401070

/-! ## Offsets -/

theorem s24 (x : Addr) : x - 8 - 8 - 8 = x - 24 := by bv_omega
theorem s16 (x : Addr) : x - 8 - 8 = x - 16 := by bv_omega
theorem s32 (x : Addr) : x - 24 - 8 = x - 32 := by bv_omega
theorem a16 (x : Addr) : x - 24 + 8 = x - 16 := by bv_omega
theorem a8 (x : Addr) : x - 24 + 16 = x - 8 := by bv_omega
theorem a0 (x : Addr) : x - 24 + 24 = x := by bv_omega
theorem a32 (x : Addr) : x - 24 + 32 = x + 8 := by bv_omega
theorem p16 (x : Addr) : x + 8 + 8 = x + 16 := by bv_omega
theorem p24 (x : Addr) : x + 8 + 8 + 8 = x + 24 := by bv_omega
theorem q32 (x : Addr) : x + 24 + 8 = x + 32 := by bv_omega
theorem m8 (x : Addr) : x - 8 = x - 32 + 24 := by bv_omega
theorem m16 (x : Addr) : x - 8 - 8 = x - 32 + 16 := by bv_omega
theorem m24 (x : Addr) : x - 8 - 8 - 8 = x - 32 + 8 := by bv_omega
theorem u8 (x : Addr) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega
theorem u16 (x : Addr) (h : 16 ≤ x.toNat) : (x - 16).toNat = x.toNat - 16 := by bv_omega
theorem u24 (x : Addr) (h : 24 ≤ x.toNat) : (x - 24).toNat = x.toNat - 24 := by bv_omega

theorem tn_add (x : Addr) (m : Nat) (h : x.toNat + m < 2 ^ 64) : (x + BitVec.ofNat 64 m).toNat = x.toNat + m := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64), Nat.mod_eq_of_lt h]

/-- Bytes `k` to `k + m` of a region of `n`. -/
theorem ft {P : Addr → Prop} {x : Addr} {n : Nat} (h : ∀ i < n, P (Addr.add x i)) (k m : Nat) (hk : k + m ≤ n) :
    ∀ i < m, P (Addr.add (x + BitVec.ofNat 64 k) i) := fun i hi => by
  have e : Addr.add (x + BitVec.ofNat 64 k) i = Addr.add x (k + i) := addr_add_add' x k i
  rw [e]; exact h _ (by omega)

/-- A store of 4 bytes at `q` apart from `x`'s 8 keeps them. -/
theorem rd4 {V : Addr → Byte} {q x : Addr} {bs : List Byte} (hb : bs.length = 4) (hq : q.toNat + 4 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : q.toNat + 4 ≤ x.toNat ∨ x.toNat + 8 ≤ q.toNat) :
    rdq(Vst V q bs, x) = rdq(V, x) := by
  rw [Tun.rd_Vst V q bs x 8 (by rw [hb]; exact hq) hx (by rw [hb]; exact h)]

/-- A store of 4 bytes at `q` apart from the 32 bytes at `r` keeps their four words. -/
theorem fr4 {V : Addr → Byte} {q r : Addr} {bs : List Byte} (hb : bs.length = 4) (hq : q.toNat + 4 ≤ 2 ^ 64)
    (hp : r.toNat + 32 ≤ 2 ^ 64) (hd : q.toNat + 4 ≤ r.toNat ∨ r.toNat + 32 ≤ q.toNat) :
    rdq(Vst V q bs, r) = rdq(V, r) ∧ rdq(Vst V q bs, r + 8) = rdq(V, r + 8) ∧
      rdq(Vst V q bs, r + 16) = rdq(V, r + 16) ∧ rdq(Vst V q bs, r + 24) = rdq(V, r + 24) := by
  have t8 : (r + 8).toNat = r.toNat + 8 := tn_add r 8 (by omega)
  have t16 : (r + 16).toNat = r.toNat + 16 := tn_add r 16 (by omega)
  have t24 : (r + 24).toNat = r.toNat + 24 := tn_add r 24 (by omega)
  exact ⟨rd4 hb hq (by omega) (by omega), rd4 hb hq (by rw [t8]; omega) (by rw [t8]; omega),
    rd4 hb hq (by rw [t16]; omega) (by rw [t16]; omega), rd4 hb hq (by rw [t24]; omega) (by rw [t24]; omega)⟩

/-- `ja` after `cmp ebx, 0x3ffffffc`. -/
theorem cnd (a : BitVec 32) :
    (decide (a.toNat < 1073741820) || decide (a = 1073741820#32)) = decide (a.toNat ≤ 1073741820) := by
  by_cases h : a.toNat < 1073741820
  · have h' : a.toNat ≤ 1073741820 := by omega
    simp [h, h']
  · by_cases h2 : a = 1073741820#32
    · subst h2; decide
    · have h3 : ¬ a.toNat ≤ 1073741820 := fun h3 =>
        h2 (BitVec.eq_of_toNat_eq (show a.toNat = 1073741820 by omega))
      simp [h, h2, h3]

/-! ## The registers and bytes at the pieces' ends -/

/-- `len`, zero-extended (`mov ebx, esi`). -/
abbrev nn (g : Gprs) : BitVec 64 := (gv g 32 6).setWidth 64
/-- `4 len`, zero-extended (`lea r12d, [rbx*4]`). -/
abbrev n4 (g : Gprs) : BitVec 64 :=
  ((optV g none + nn g * BitVec.ofNat 64 4 + BitVec.ofNat 64 0).setWidth 32).setWidth 64
/-- The registers at the `call` of `malloc`: `edi` = `4 len + 8`. -/
abbrev gM (g : Gprs) : Gprs :=
  { g with
    rbx := nn g, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi, r12 := n4 g,
    rdi := ((n4 g + optV g none * BitVec.ofNat 64 1 + BitVec.ofNat 64 8).setWidth 32).setWidth 64 }
/-- The bytes with `r12`, `rbp`, `rbx` pushed. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)
/-- The bytes with the length word `[rax] = r12d` stored. -/
abbrev Va (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V g.rax (toBytesLE (g.r12.setWidth 32) 4)
/-- Where the terminator goes: `p + 4 + 4 len`. -/
abbrev qq (g : Gprs) : Addr := g.rax + 4#64 + g.rbx * 4#64
/-- The registers at the `call` of `memcpy`. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with r8 := g.rax + 4#64, rdi := g.rax + 4#64, rdx := (g.r12.setWidth 32).setWidth 64, rsi := g.rbp }
/-- The bytes with the terminator stored. -/
abbrev Vz (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.r8 + g.rbx * 4#64) (toBytesLE 0#32 4)

/-- The pushed registers read back. -/
theorem vp_rd {V : Addr → Byte} {g : Gprs} (hp : 32 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vp V g, g.rsp - 24) = g.rbx ∧ rdq(Vp V g, g.rsp - 24 + 8) = g.rbp ∧
      rdq(Vp V g, g.rsp - 24 + 16) = g.r12 ∧ rdq(Vp V g, g.rsp - 24 + 24) = rdq(V, g.rsp) := by
  have t8 := u8 g.rsp (by omega)
  have t16 := u16 g.rsp (by omega)
  have t24 := u24 g.rsp (by omega)
  dsimp only [Vp]
  rw [s24, s16, a16, a8, a0]
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length v 8
  have e24 : (g.rsp - 24).toNat + 8 ≤ 2 ^ 64 := by omega
  have e16 : (g.rsp - 16).toNat + 8 ≤ 2 ^ 64 := by omega
  have e8 : (g.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by omega
  have d1 : ∀ v : BitVec 64, (g.rsp - 24).toNat + (toBytesLE v 8).length ≤ 2 ^ 64 := fun v => by rw [l8]; omega
  have d2 : ∀ v : BitVec 64, (g.rsp - 16).toNat + (toBytesLE v 8).length ≤ 2 ^ 64 := fun v => by rw [l8]; omega
  have d3 : ∀ v : BitVec 64, (g.rsp - 8).toNat + (toBytesLE v 8).length ≤ 2 ^ 64 := fun v => by rw [l8]; omega
  have x1 : (g.rsp - 24).toNat + (toBytesLE g.rbx 8).length ≤ (g.rsp - 16).toNat ∨
      (g.rsp - 16).toNat + 8 ≤ (g.rsp - 24).toNat := by rw [l8]; omega
  have x2 : (g.rsp - 24).toNat + (toBytesLE g.rbx 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (g.rsp - 24).toNat := by rw [l8]; omega
  have x3 : (g.rsp - 16).toNat + (toBytesLE g.rbp 8).length ≤ (g.rsp - 8).toNat ∨
      (g.rsp - 8).toNat + 8 ≤ (g.rsp - 16).toNat := by rw [l8]; omega
  have y1 : (g.rsp - 24).toNat + (toBytesLE g.rbx 8).length ≤ g.rsp.toNat ∨
      g.rsp.toNat + 8 ≤ (g.rsp - 24).toNat := by rw [l8]; omega
  have y2 : (g.rsp - 16).toNat + (toBytesLE g.rbp 8).length ≤ g.rsp.toNat ∨
      g.rsp.toNat + 8 ≤ (g.rsp - 16).toNat := by rw [l8]; omega
  have y3 : (g.rsp - 8).toNat + (toBytesLE g.r12 8).length ≤ g.rsp.toNat ∨
      g.rsp.toNat + 8 ≤ (g.rsp - 8).toNat := by rw [l8]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Tun.rd_Vst_self _ (g.rsp - 24) (toBytesLE g.rbx 8) (l8 _) e24, ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [Tun.rd_Vst _ (g.rsp - 24) (toBytesLE g.rbx 8) (g.rsp - 16) 8 (d1 _) e16 x1,
      Tun.rd_Vst_self _ (g.rsp - 16) (toBytesLE g.rbp 8) (l8 _) e16, ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [Tun.rd_Vst _ (g.rsp - 24) (toBytesLE g.rbx 8) (g.rsp - 8) 8 (d1 _) e8 x2,
      Tun.rd_Vst _ (g.rsp - 16) (toBytesLE g.rbp 8) (g.rsp - 8) 8 (d2 _) e8 x3,
      Tun.rd_Vst_self _ (g.rsp - 8) (toBytesLE g.r12 8) (l8 _) e8, ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [Tun.rd_Vst _ (g.rsp - 24) (toBytesLE g.rbx 8) g.rsp 8 (d1 _) hp8 y1,
      Tun.rd_Vst _ (g.rsp - 16) (toBytesLE g.rbp 8) g.rsp 8 (d2 _) hp8 y2,
      Tun.rd_Vst _ (g.rsp - 8) (toBytesLE g.r12 8) g.rsp 8 (d3 _) hp8 y3]

variable {F : Footprint} {Wl : List Rgn}

/-! ## The verification conditions -/

/-- `len` above `0x3ffffffc`: the pushes and `mov ebx, esi`, then the `ja` to 96. -/
theorem vc_b {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hc : (decide ((g.rsi.setWidth 32).toNat < 1073741820) || decide (g.rsi.setWidth 32 = 1073741820#32)) = false) :
    W_0 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = { g with rbx := nn g, rsp := g.rsp - 8 - 8 - 8 } ∧ V' = Vp V g)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 hc ⊢
  wpx [W_0, W_18, o0, o1, nn, Vp, hc, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `len` at most `0x3ffffffc`: the pushes, `mov ebx, esi`, then `lea r12d, [rbx*4]; mov rbp, rdi;
lea edi, [r12 + 8]` to the `call` at 34. -/
theorem vc_s {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hc : (decide ((g.rsi.setWidth 32).toNat < 1073741820) || decide (g.rsi.setWidth 32 = 1073741820#32)) = true) :
    W_0 F Wl (fun j' g' _ V' => j' = 34 ∧ g' = gM g ∧ V' = Vp V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 hc ⊢
  wpx [W_0, W_18, o0, o1, nn, n4, gM, Vp, hc, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 96: `xor r8d, r8d; pop rbx; pop rbp; mov rax, r8; pop r12` to the `ret` at 106. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (l0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 106 ∧
      g' = { g with
        rax := 0#64, rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8), r8 := 0#64, r12 := rdq(V, g.rsp + 8 + 8),
        rsp := g.rsp + 8 + 8 + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l0 l1 l2 ⊢
  wpx [W_96, o7, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- From the return of `malloc`, a null result: `test rax, rax; je` to 96. -/
theorem vc_39z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax = 0) :
    W_39 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_39, W_44, W_56, o2, o3, o4, BitVec.and_self, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- Not null, `s` null: the length word, `lea r8, [rax + 4]`, `test rbp, rbp; je` to 73. -/
theorem vc_4z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax ≠ 0) (hb : g.rbp = 0)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_39 F Wl (fun j' g' _ V' => j' = 73 ∧ g' = { g with r8 := g.rax + 4#64 } ∧ V' = Va V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hb hw ⊢
  subst hb
  wpx [W_39, W_44, W_56, o2, o3, o4, Va, BitVec.and_self, beq_self_eq_true, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    h, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _

/-- Not null, `s` not null: the length word, `lea r8, [rax + 4]`, then `mov rdi, r8; mov edx, r12d; mov rsi, rbp`
to the `call` at 65. -/
theorem vc_4n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rax ≠ 0) (hb : g.rbp ≠ 0)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_39 F Wl (fun j' g' _ V' => j' = 65 ∧ g' = gC g ∧ V' = Va V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hb hw ⊢
  wpx [W_39, W_44, W_56, o2, o3, o4, Va, gC, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, h, hb,
    not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh hb)
    | apply And.intro
    | intro _

/-- From the return of `memcpy`: `mov r8, rax` to 73. -/
theorem vc_70 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_70 F Wl (fun j' g' _ V' => j' = 73 ∧ g' = { g with r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_70, o5]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- From 73: the terminator, `mov rax, r8; pop rbx; pop rbp; pop r12` to the `ret` at 88. -/
theorem vc_73 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 4, Foot Wl (Addr.add (g.r8 + g.rbx * 4#64) i))
    (l0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_73 F Wl (fun j' g' _ V' => j' = 88 ∧
      g' = { g with
        rax := g.r8, rbx := rdq(Vz V g, g.rsp), rbp := rdq(Vz V g, g.rsp + 8), r12 := rdq(Vz V g, g.rsp + 8 + 8),
        rsp := g.rsp + 8 + 8 + 8 } ∧ V' = Vz V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw l0 l1 l2 ⊢
  wpx [W_73, o6, Vz]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The pieces -/

/-- From 96 to the return address, for the frame at `r`: `rax` and `r8` 0, the saved registers popped. -/
theorem sas_z (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sas_at sas) {Z : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hrip : Z.cpu.rip = sas_at.add 96)
    {r rf : Addr} (hr : Z.cpu.gpr.rsp = r) (hrf : r + 32 = rf) (hl : ∀ i < 32, Foot F.data (Addr.add r i))
    {b0 bp b12 : BitVec 64} (hb0 : rdq(V, r) = b0) (hb1 : rdq(V, r + 8) = bp) (hb2 : rdq(V, r + 16) = b12)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, r + 24) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := b0, rbp := bp, r8 := 0#64, r12 := b12, rsp := rf } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  refine (c_96 prof).run c hin (fun j' g' _ V' => j' = 106 ∧
      g' = { Z.cpu.gpr with
        rax := 0#64, rbx := rdq(V, Z.cpu.gpr.rsp), rbp := rdq(V, Z.cpu.gpr.rsp + 8), r8 := 0#64,
        r12 := rdq(V, Z.cpu.gpr.rsp + 8 + 8), rsp := Z.cpu.gpr.rsp + 8 + 8 + 8 } ∧ V' = V) hK hA hrip
    (vc_96 (by rw [hr]; exact fun i hi => hl i (by omega)) (by rw [hr]; exact ft hl 8 8 (by decide))
      (by rw [hr, p16]; exact ft hl 16 8 (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = r + 24 := by rw [hgY, hr]; exact p24 r
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_106 _) (by rw [hsY]; exact ft hl 24 8 (by decide))
    hin₂ h₂ (by rw [hsY]; exact hra) ?_
  rintro Z' t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hsY, hgY, hr, p16, hb0, hb1, hb2, q32, hrf]
  try rfl

/-- From 73 to the return address, for the frame at `r` and the terminator at `q`: `rax` = `r8`, the saved registers
popped. -/
theorem sas_t (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sas_at sas) {Z : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hrip : Z.cpu.rip = sas_at.add 73)
    {r rf q : Addr} (hr : Z.cpu.gpr.rsp = r) (hrf : r + 32 = rf) (hqe : Z.cpu.gpr.r8 + Z.cpu.gpr.rbx * 4#64 = q)
    (hp : r.toNat + 32 ≤ 2 ^ 64) (hl : ∀ i < 32, Foot F.data (Addr.add r i))
    (hw : ∀ i < 4, Foot Wl (Addr.add q i)) (hq : q.toNat + 4 ≤ 2 ^ 64)
    (hd : q.toNat + 4 ≤ r.toNat ∨ r.toNat + 32 ≤ q.toNat)
    {b0 bp b12 : BitVec 64} (hb0 : rdq(V, r) = b0) (hb1 : rdq(V, r + 8) = bp) (hb2 : rdq(V, r + 16) = b12)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, r + 24) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vst V q (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := Z.cpu.gpr.r8, rbx := b0, rbp := bp, r12 := b12, rsp := rf } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  obtain ⟨r0, r1, r2, r3⟩ := fr4 (V := V) (toBytesLE_length 0#32 4) hq hp hd
  refine (c_73 prof).run c hin (fun j' g' _ V' => j' = 88 ∧
      g' = { Z.cpu.gpr with
        rax := Z.cpu.gpr.r8, rbx := rdq(Vz V Z.cpu.gpr, Z.cpu.gpr.rsp), rbp := rdq(Vz V Z.cpu.gpr, Z.cpu.gpr.rsp + 8),
        r12 := rdq(Vz V Z.cpu.gpr, Z.cpu.gpr.rsp + 8 + 8), rsp := Z.cpu.gpr.rsp + 8 + 8 + 8 } ∧
      V' = Vz V Z.cpu.gpr) hK hA hrip
    (vc_73 (by rw [hqe]; exact hw) (by rw [hr]; exact fun i hi => hl i (by omega))
      (by rw [hr]; exact ft hl 8 8 (by decide)) (by rw [hr, p16]; exact ft hl 16 8 (by decide))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hVz : Vz V Z.cpu.gpr = Vst V q (toBytesLE 0#32 4) := by
    show Vst V (Z.cpu.gpr.r8 + Z.cpu.gpr.rbx * 4#64) (toBytesLE 0#32 4) = _
    rw [hqe]
  have hsY : Y.cpu.gpr.rsp = r + 24 := by rw [hgY, hr]; exact p24 r
  rw [hVz] at hAY
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_88 _) (by rw [hsY]; exact ft hl 24 8 (by decide))
    hin₂ h₂ (by rw [hsY, r3]; exact hra) ?_
  rintro Z' t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hsY, hgY, hVz, hr, p16, r0, r1, r2, hb0, hb1, hb2, q32, hrf]
  try rfl

/-- From the return of `malloc` (39) to the return address, for the frame at `r`: a null result (`kz`); else the
length word, then `s` null (`k0`) or through `memcpy` (`kc`, then `k1`). -/
theorem sas_m {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sas_at sas)
    {cC : List Byte} (hinC : CodeIn L cpy_at cC) (hC : 0 < cC.length)
    {Z : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hrip : Z.cpu.rip = sas_at.add 39)
    {r rf : Addr} (hr : Z.cpu.gpr.rsp = r) (hrf : r + 32 = rf) (hp : r.toNat + 32 ≤ 2 ^ 64)
    (hl : ∀ i < 32, Foot F.data (Addr.add r i)) (hs : ∀ i < 8, Foot Wl (Addr.add (r - 8) i))
    {b0 bp b12 : BitVec 64} (hb0 : rdq(V, r) = b0) (hb1 : rdq(V, r + 8) = bp) (hb2 : rdq(V, r + 16) = b12)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, r + 24) = e₂.add j₂)
    (hnz : Z.cpu.gpr.rax ≠ 0 → (∀ i < 4, Foot Wl (Addr.add Z.cpu.gpr.rax i)) ∧
      Z.cpu.gpr.rax.toNat + 4 ≤ 2 ^ 64 ∧
      (Z.cpu.gpr.rax.toNat + 4 ≤ r.toNat ∨ r.toNat + 32 ≤ Z.cpu.gpr.rax.toNat) ∧
      (∀ i < 4, Foot Wl (Addr.add (qq Z.cpu.gpr) i)) ∧ (qq Z.cpu.gpr).toNat + 4 ≤ 2 ^ 64 ∧
      ((qq Z.cpu.gpr).toNat + 4 ≤ r.toNat ∨ r.toNat + 32 ≤ (qq Z.cpu.gpr).toNat))
    (kz : Z.cpu.gpr.rax = 0 → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := b0, rbp := bp, r8 := 0#64, r12 := b12, rsp := rf } →
      GoG prof L o gev gP gE Z' t')
    (k0 : Z.cpu.gpr.rax ≠ 0 → Z.cpu.gpr.rbp = 0 → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Va V Z.cpu.gpr) (qq Z.cpu.gpr) (toBytesLE 0#32 4)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := Z.cpu.gpr.rax + 4#64, rbx := b0, rbp := bp, r8 := Z.cpu.gpr.rax + 4#64, r12 := b12, rsp := rf } →
      GoG prof L o gev gP gE Z' t')
    (kc : Z.cpu.gpr.rax ≠ 0 → Z.cpu.gpr.rbp ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Va V Z.cpu.gpr) (r - 8) (toBytesLE (sas_at.add 70) 8)) → Y.cpu.rip = cpy_at →
      Y.cpu.gpr = (gC Z.cpu.gpr).set 4 (r - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = sas_at.add 70 → Z₂.cpu.gpr.rsp = r → Z₂.cpu.gpr.rbx = Z.cpu.gpr.rbx →
        Z₂.cpu.gpr.rax = Z.cpu.gpr.rax + 4#64 → rdq(V₂, r) = b0 → rdq(V₂, r + 8) = bp →
        rdq(V₂, r + 16) = b12 →
        rdq(V₂, r + 24) = e₂.add j₂ → Pc Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (k1 : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ (qq Z.cpu.gpr) (toBytesLE 0#32 4)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with r8 := Z₂.cpu.gpr.rax, rbx := b0, rbp := bp, r12 := b12, rsp := rf } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  by_cases h0 : Z.cpu.gpr.rax = 0
  · -- a null result
    refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 96 ∧ g' = Z.cpu.gpr ∧ V' = V) hK hA hrip (vc_39z h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact sas_z c hin hKY hAY hrY (hgY ▸ hr) hrf hl hb0 hb1 hb2 hin₂ h₂ hra fun Z' t' hKZ hAZ hrZ hgZ =>
      kz h0 Z' t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  obtain ⟨hw, ha, hda, hwq, hq, hdq⟩ := hnz h0
  obtain ⟨r0, r1, r2, r3⟩ := fr4 (V := V) (toBytesLE_length (Z.cpu.gpr.r12.setWidth 32) 4) ha hp hda
  by_cases hb : Z.cpu.gpr.rbp = 0
  · -- `s` null
    refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 73 ∧ g' = { Z.cpu.gpr with r8 := Z.cpu.gpr.rax + 4#64 } ∧
        V' = Va V Z.cpu.gpr) hK hA hrip (vc_4z h0 hb hw) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact sas_t c hin hKY hAY hrY (by rw [hgY]; exact hr) hrf (by rw [hgY] <;> rfl) hp hl hwq hq hdq
      (r0.trans hb0) (r1.trans hb1) (r2.trans hb2) hin₂ h₂ (r3.trans hra) fun Z' t' hKZ hAZ hrZ hgZ =>
      k0 h0 hb Z' t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  · -- through `memcpy`
    refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 65 ∧ g' = gC Z.cpu.gpr ∧ V' = Va V Z.cpu.gpr) hK hA hrip
      (vc_4n h0 hb hw) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hsY : Y.cpu.gpr.rsp = r := by rw [hgY]; exact hr
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_65 _) hinC hC (by decide) (by rw [hsY]; exact hs) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC Z.cpu.gpr).set 4 (r - 8) := by rw [hg₂, hgY, ← hr]
    refine kc h0 hb Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `memcpy`
    intro Z₂ V₂ t'' hKZ hAZ hrZ hzs hzb hza h0' h1' h2' h3' hPc
    refine (c_70 prof).run c hin (fun j' g' _ V' => j' = 73 ∧ g' = { Z₂.cpu.gpr with r8 := Z₂.cpu.gpr.rax } ∧
        V' = V₂) hKZ hAZ hrZ vc_70 ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
    exact sas_t c hin hKU hAU hrU (by rw [hgU]; exact hzs) hrf
      (by rw [hgU]; show Z₂.cpu.gpr.rax + Z₂.cpu.gpr.rbx * 4#64 = qq Z.cpu.gpr; rw [hza, hzb])
      hp hl hwq hq hdq h0' h1' h2' hin₂ h₂ h3' fun Z' t' hKZ' hAZ' hrZ' hgZ' =>
      k1 Z₂ V₂ Z' t' hPc hKZ' hAZ' hrZ' (by rw [hgZ', hgU] <;> rfl)

/-- `SysAllocStringLen (s, len)` (`s` = `rdi`, `len` = `esi`) from its entry. `len` above `0x3ffffffc`: at the return
address with `rax` and `r8` 0 (`kb`). Else at `malloc`'s entry with the registers `gM` and the bytes `Vp` with the
return address into `SysAllocStringLen` pushed (`km`); if `malloc` returns to `sas_at + 39` with the frame as it was
(`rsp` 24 below the entry's, `rbx` = `len`, `rbp` = `s`, `r12` = `4 len`, the saved registers and the return address in
place) and its post `Pm`, then: a null result: at the return address with `rax` 0 (`kz`); else, given the places of
the length word and the terminator, `s` null: at the return address with `rax` = `p + 4` (`k0`); `s` not null: at
`memcpy`'s entry (`kc`), and from its return, at the return address (`k1`). -/
theorem sas_ok {Pm Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sas_at sas)
    {cM : List Byte} (hinM : CodeIn L mal_at cM) (hM : 0 < cM.length)
    {cC : List Byte} (hinC : CodeIn L cpy_at cC) (hC : 0 < cC.length)
    {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sas_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 32, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kb : 1073741820 < (X.cpu.gpr.rsi.setWidth 32).toNat → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vp V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, r8 := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (km : (X.cpu.gpr.rsi.setWidth 32).toNat ≤ 1073741820 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vp V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (sas_at.add 39) 8)) →
      Y.cpu.rip = mal_at → Y.cpu.gpr = (gM X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = sas_at.add 39 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = nn X.cpu.gpr →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.r12 = n4 X.cpu.gpr →
        rdq(V', X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pm Z V' →
        (Z.cpu.gpr.rax ≠ 0 → (∀ i < 4, Foot Wl (Addr.add Z.cpu.gpr.rax i)) ∧
          Z.cpu.gpr.rax.toNat + 4 ≤ 2 ^ 64 ∧
          (Z.cpu.gpr.rax.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ Z.cpu.gpr.rax.toNat) ∧
          (∀ i < 4, Foot Wl (Addr.add (qq Z.cpu.gpr) i)) ∧ (qq Z.cpu.gpr).toNat + 4 ≤ 2 ^ 64 ∧
          ((qq Z.cpu.gpr).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨
            X.cpu.gpr.rsp.toNat + 8 ≤ (qq Z.cpu.gpr).toNat)) →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z : State) (V' : Addr → Byte), Pm Z V' → Z.cpu.gpr.rax = 0 → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := 0#64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r8 := 0#64, r12 := X.cpu.gpr.r12,
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (k0 : ∀ (Z : State) (V' : Addr → Byte), Pm Z V' → Z.cpu.gpr.rax ≠ 0 → Z.cpu.gpr.rbp = 0 →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Va V' Z.cpu.gpr) (qq Z.cpu.gpr) (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := Z.cpu.gpr.rax + 4#64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r8 := Z.cpu.gpr.rax + 4#64,
        r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kc : ∀ (Z : State) (V' : Addr → Byte), Pm Z V' → Z.cpu.gpr.rax ≠ 0 → Z.cpu.gpr.rbp ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Va V' Z.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (sas_at.add 70) 8)) →
      Y.cpu.rip = cpy_at → Y.cpu.gpr = (gC Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = sas_at.add 70 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.rbx = Z.cpu.gpr.rbx →
        Z₂.cpu.gpr.rax = Z.cpu.gpr.rax + 4#64 → rdq(V₂, X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx →
        rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (k1 : ∀ (Z : State) (V' : Addr → Byte), Pm Z V' →
      ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat),
      Pc Z₂ V₂ → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vst V₂ (qq Z.cpu.gpr) (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        r8 := Z₂.cpu.gpr.rax, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have t24 := u24 X.cpu.gpr.rsp (by omega)
  have hp' : (X.cpu.gpr.rsp - 24).toNat + 32 ≤ 2 ^ 64 := by rw [t24]; omega
  have hrip' : X.cpu.rip = sas_at.add 0 := by rw [addr_add_zero]; exact hrip
  have h1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by rw [m8]; exact ft hs 24 8 (by decide)
  have h2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := by rw [m16]; exact ft hs 16 8 (by decide)
  have h3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := by rw [m24]; exact ft hs 8 8 (by decide)
  by_cases hsm : (X.cpu.gpr.rsi.setWidth 32).toNat ≤ 1073741820
  · -- to the `call` of `malloc`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 34 ∧ g' = gM X.cpu.gpr ∧ V' = Vp V X.cpu.gpr) hK hA hrip'
      (vc_s h1 h2 h3 (by rw [cnd]; exact decide_eq_true hsm)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact s24 _
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_34 _) hinM hM (by decide)
      (by rw [hsY, s32]; exact fun i hi => hs i (by omega)) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, s32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gM X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₂, hsY, s32]
      rw [hgY]
    refine km hsm Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `malloc`
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hz12 h24 h16 h8 h0 hPm hnz
    refine sas_m (Pc := Pc) c hin hinC hC hKZ hAZ hrZ hzs (a32 _) hp' hl
      (by rw [s32]; exact fun i hi => hs i (by omega)) h24 (by rw [a16]; exact h16) (by rw [a8]; exact h8) hin₂ h₂
      (by rw [a0]; exact h0) (fun hn => by
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hnz hn
        rw [t24]; exact ⟨a1, a2, by omega, a4, a5, by omega⟩) (kz Z V' hPm) (k0 Z V' hPm) ?_ (k1 Z V' hPm)
    intro hn hb Y t' hKY' hAY' hrY' hgY' k'
    rw [s32] at hAY' hgY'
    exact kc Z V' hPm hn hb Y t' hKY' hAY' hrY' hgY' fun Z₂ V₂ t₃ hK3 hA3 hr3 hs3 hb3 ha3 e0 e1 e2 e3 hPc =>
      k' Z₂ V₂ t₃ hK3 hA3 hr3 hs3 hb3 ha3 e0 (by rw [a16]; exact e1) (by rw [a8]; exact e2) (by rw [a0]; exact e3)
        hPc
  · -- `len` too large
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 96 ∧
        g' = { X.cpu.gpr with rbx := nn X.cpu.gpr, rsp := X.cpu.gpr.rsp - 8 - 8 - 8 } ∧ V' = Vp V X.cpu.gpr)
      hK hA hrip' (vc_b h1 h2 h3 (by rw [cnd]; exact decide_eq_false hsm)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    obtain ⟨r0, r1, r2, r3⟩ := vp_rd (V := V) hp hp8
    exact sas_z c hin hKY hAY hrY (by rw [hgY]; exact s24 _) (a32 _) hl r0 r1 r2 hin₂ h₂ (r3.trans hra)
      fun Z t' hKZ hAZ hrZ hgZ => kb (by omega) Z t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)

end FV7z.Sas
