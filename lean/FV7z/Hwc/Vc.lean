import FV7z.Hwc.Cuts
import FV7z.Tun.Inv
/-!
# `_dl_important_hwcaps`: the pieces up to the table of capabilities (PLAN.md G3, startup)

glibc 2.31's `_dl_important_hwcaps (platform, platform_len, &ncapstr, &max_capstrlen)` at `0x6ad140`, called by
`_dl_init_paths` with `platform` = `_dl_platform` (not null), `platform_len` = `_dl_platformlen` (still 0: it is set
after), no vDSO (`_dl_sysinfo_map` null), `_dl_hwcap` = `h` (2 or 6: `init_cpu_features`) and the mask
`glibc.cpu.hwcap_mask` not set (6). The capabilities are `x86_64` (bit 1), `avx512_1` (bit 2) if `h = 6`, the
platform and `tls`: `cnt` = 3 or 4.

- `vc_0`: the prologue (6 `push`es, `sub rsp, 0x88`, the arguments to the frame), to the `call` of
  `__tunable_get_val (11, rbp - 0x38, NULL)` (61).
- `vc_66`: the mask and `_dl_hwcap`, `rdx` = 1 (the platform), to the loop that counts the bits (112).
- `vc_112`, `vc_132`: one bit of the loop; `vc_150`: no vDSO, the `alloca` of `16 cnt + 16` bytes, to the stack
  probe (1772).
- `vc_1778`: the table `temp` at `rsp`, to the loop over the bits (1840); `vc_1840c`, `vc_1840s`: a bit clear, set
  (to the `call` of `strlen`, 1890); `vc_1895`: after it, the next bit or the platform (682).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

/-! ## The instructions the pieces stop at -/

def pc61 : List Byte := [0xe8, 0x1e, 0x22, 0xfc, 0xff]
theorem pc61_0 : ∀ feat, Dec feat pc61 0 (FV7z.mk .call 64 [.rel 18446744073709298206] 5) := by dec_rfl
theorem w_61 : pc61 <+: hwc.drop 61 := by decide +kernel
theorem call_61 (feat : Features) : Dec feat hwc 61 (FV7z.mk .call 64 [.rel 18446744073709298206] 5) :=
  Dec.shift (j := 61) (k := 0) (pc61_0 feat) w_61 (Nat.zero_le _)

def pc1890 : List Byte := [0xe8, 0x61, 0x38, 0xd5, 0xff]
theorem pc1890_0 : ∀ feat, Dec feat pc1890 0 (FV7z.mk .call 64 [.rel 18446744073706748001] 5) := by dec_rfl
theorem w_1890 : pc1890 <+: hwc.drop 1890 := by decide +kernel
theorem call_1890 (feat : Features) : Dec feat hwc 1890 (FV7z.mk .call 64 [.rel 18446744073706748001] 5) :=
  Dec.shift (j := 1890) (k := 0) (pc1890_0 feat) w_1890 (Nat.zero_le _)

def por : List Byte := [0x48, 0x83, 0x4c, 0x04, 0xf8, 0x00]
theorem por_0 : ∀ feat, Dec feat por 0 (FV7z.mk .or 64 [.mem (mbi 4 0 18446744073709551608 64), .imm 64 0] 6) := by
  dec_rfl
theorem w_1772 : por <+: hwc.drop 1772 := by decide +kernel
theorem or_1772 (feat : Features) :
    Dec feat hwc 1772 (FV7z.mk .or 64 [.mem (mbi 4 0 18446744073709551608 64), .imm 64 0] 6) :=
  Dec.shift (j := 1772) (k := 0) (por_0 feat) w_1772 (Nat.zero_le _)

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn} {fb : Addr}

/-- The bytes after the prologue: the six `push`es (`rbp`, `r15`, `r14`, `r13`, `r12`, `rbx`) and the arguments
`platform` (`rbp - 0x60`), `platform_len` (`rbp - 0x68`), `&ncapstr` (`rbp - 0x58`), `rbp - 0x38` (`rbp - 0x80`),
`&max_capstrlen` (`rbp - 0x70`). -/
def hV0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8))
    (g.rsp - 8 + 18446744073709551520#64) (toBytesLE g.rdi 8))
    (g.rsp - 8 + 18446744073709551512#64) (toBytesLE g.rsi 8))
    (g.rsp - 8 + 18446744073709551528#64) (toBytesLE g.rdx 8))
    (g.rsp - 8 + 18446744073709551488#64) (toBytesLE (g.rsp - 8 + 18446744073709551560#64) 8))
    (g.rsp - 8 + 18446744073709551504#64) (toBytesLE g.rcx 8)

/-- The prologue, to the `call` of `__tunable_get_val (11, rbp - 0x38, NULL)`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 184, Foot Wl (Addr.add (g.rsp - 184#64) i)) (hsp : 184 ≤ g.rsp.toNat) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 61 ∧ g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 136#64 ∧
      g'.rbp = g.rsp - 8 ∧ g'.r15 = g.rdi ∧ g'.rdi = 11#64 ∧ g'.rsi = g.rsp - 8 + 18446744073709551560#64 ∧
      g'.rdx = 0#64 ∧ V' = hV0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst hsp
  have slot : ∀ (a : Addr) (k : Nat), k < 184 → a = Addr.add (rsp - 184#64) k → Foot Wl a :=
    fun a k hk ha => ha ▸ hst k hk
  wpx [W_0, o0, Op.push, BitVec.xor_self]
  all_goals first
    | exact fun i hi => slot _ (176 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (168 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (160 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (152 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (144 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (136 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (80 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (72 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (88 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (48 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact fun i hi => slot _ (64 + i) (by omega) (by simp only [Addr.add]; bv_omega)
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | skip

/-- After `__tunable_get_val`: the mask `6` at `rbp - 0x38`, `_dl_hwcap` = `h` (2 or 6), the platform not null
(`r15`): to the loop over the bits (112) with `rdx = 1`, `rcx = 0`, `rsi = 1`, `r8 = h`. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} {h : Addr} (hh : h = 2#64 ∨ h = 6#64)
    (hm : rdq(V, g.rbp + 18446744073709551560#64) = 6#64) (hhw : rdq(V, 8014536#64) = h) (hp : g.r15 ≠ 0#64)
    (hfm : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 18446744073709551560#64) i))
    (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551536#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551496#64) i)) :
    W_66 fb F Wl (fun j' g' _ V' => j' = 112 ∧ g' = { g with rax := h, rcx := 0#64, rdx := 1#64, rbx := 6#64,
      rsi := 1#64, r8 := h } ∧
      V' = Vst (Vst V (g.rbp + 18446744073709551536#64) (toBytesLE h 8)) (g.rbp + 18446744073709551496#64)
        (toBytesLE 6#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm hhw hp hfm hfh hs1 hs2
  have hp' : (r15 &&& r15 == 0#64) = false := by rw [BitVec.and_self]; exact beq_eq_false_iff_ne.2 hp
  rcases hh with rfl | rfl
  all_goals
    wpx [W_66, W_105, o1, o2, Op.lda, Op.setcc, hm, hhw, hp', BitVec.xor_self, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, false_implies, true_implies]
    all_goals first | exact hfm | exact hfh | exact hs1 | exact hs2 | skip
    all_goals first | (refine ⟨rfl, ?_, rfl⟩; first | rfl | decide | skip) | decide | skip

/-- One bit `c` of the loop that counts the bits of `r8`: `rdx` and `r12` the count so far plus 1, 2 if bit `c` is
set, plus 0, 1 if not; on to 132. -/
theorem vc_112 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_112 fb F Wl (fun j' g' _ V' => j' = 132 ∧
      g' = (if g.r8.getLsbD (g.rcx.toNat % 64) then { g with rax := g.rdx + 2#64, rdx := g.rdx + 1#64,
        r12 := g.rdx + 2#64 } else { g with r12 := g.rdx + 1#64 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_112, W_122, o3, o4, Op.bt64]
  all_goals intro fl hfl
  all_goals first
    | (cases hb : r8.getLsbD (rcx.toNat % 64) <;> simp_all <;> first | rfl | skip)
    | skip

/-- After bit `c`: `rcx = c + 1`; on to the next bit (112) while bits remain above, else (`cnt = n` in `r12`): no vDSO
(`_dl_sysinfo_map` null), the `alloca` of `16 n + 16` bytes (less than a page), to the stack probe (1772). -/
theorem vc_132 {g : Gprs} {f : Rflags} {V : Addr → Byte} {c n : Nat} (hc : c < 63) (hcx : g.rcx = BitVec.ofNat 64 c)
    (hsi : g.rsi = 1#64) (hr : g.r12 = BitVec.ofNat 64 n) (hn : n = 3 ∨ n = 4) (hsm : rdq(V, 8029424#64) = 0#64)
    (hfs : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) :
    W_132 fb F Wl (fun j' g' _ V' => V' = V ∧ (
      (j' = 112 ∧ g' = { g with rax := 0#64 - 1#64 <<< (c + 1), rcx := BitVec.ofNat 64 (c + 1) } ∧
        (0#64 - 1#64 <<< (c + 1)) &&& g.r8 ≠ 0#64) ∨
      (j' = 1772 ∧ (0#64 - 1#64 <<< (c + 1)) &&& g.r8 = 0#64 ∧
        g' = { g with rax := BitVec.ofNat 64 (16 * n + 16), rcx := BitVec.ofNat 64 (c + 1), rbx := g.rsp,
          rdx := g.rsp, rsp := g.rsp - BitVec.ofNat 64 (16 * n + 16) }))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hcx hsi hr ⊢
  subst hcx hsi hr
  have e1 : BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es : (BitVec.setWidth 8 (BitVec.ofNat 64 (c + 1))).toNat % 64 = c + 1 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  by_cases hz : (0#64 - 1#64 <<< (c + 1)) &&& r8 = 0#64
  · have hz' : ((0#64 - 1#64 <<< (c + 1)) &&& r8 == 0#64) = true := by simp only [hz, beq_self_eq_true]
    rcases hn with rfl | rfl
    all_goals
      wpx [W_132, W_150, W_1955, W_1759, o5, o6, o57, o49, Op.shl64, Op.lda, e1, es, hz', hsm, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, false_implies, true_implies, BitVec.sub_zero]
      all_goals first | exact hfs | exact ⟨rfl, Or.inr ⟨rfl, hz, rfl⟩⟩ | skip
  · have hz' : ((0#64 - 1#64 <<< (c + 1)) &&& r8 == 0#64) = false := by simp only [hz, beq_eq_false_iff_ne]; exact hz
    wpx [W_132, o5, Op.shl64, e1, es, hz', Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies,
      true_implies]
    all_goals first | exact ⟨rfl, Or.inl ⟨rfl, rfl, hz⟩⟩ | skip

/-- After the probe: `temp` at `rsp` (16-aligned), `cnt` to `rbp - 0x78`, the loop over the bits of `h` from bit 0
(1840): `rbx = 0` entries so far, `r8 = 1`, `rdx = temp`. -/
theorem vc_1778 {g : Gprs} {f : Rflags} {V : Addr → Byte} {h : Addr} (hh : h = 2#64 ∨ h = 6#64) (hr8 : g.r8 = h)
    (hal : (g.rsp + 15#64) &&& 18446744073709551600#64 = g.rsp)
    (hs : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551496#64) i)) :
    W_1778 fb F Wl (fun j' g' _ V' => j' = 1840 ∧ g' = { g with rax := 1#64, rcx := 1#64, rdx := g.rsp,
      rbx := 0#64, r13 := 0#64, r14 := h, r15 := 0#64, r8 := 1#64 } ∧
      V' = Vst V (g.rbp + 18446744073709551496#64) (toBytesLE g.r12 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr8 hal hs ⊢
  subst hr8
  rcases hh with rfl | rfl
  all_goals
    wpx [W_1778, W_1798, W_1807, o50, o51, o52, hal, BitVec.xor_self, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, false_implies, true_implies]
    all_goals first | exact hs | exact ⟨rfl, rfl, rfl⟩ | skip

/-- Bit `b` of `r14` clear: on to bit `b + 1` (1840). -/
theorem vc_1840c {g : Gprs} {f : Rflags} {V : Addr → Byte} (hb : g.r14.getLsbD (g.r15.toNat % 64) = false) :
    W_1840 fb F Wl (fun j' g' _ V' => j' = 1840 ∧ g' = { g with r13 := g.rbx <<< 4, r12 := g.rdx + g.rbx <<< 4,
      r15 := g.r15 + 1#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb ⊢
  wpx [W_1840, W_2024, o53, o58, Op.bt64]
  all_goals intro fl hfl
  all_goals simp only [hfl, hb, rfz_cf, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_implies,
    true_implies, and_true, true_and]
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | skip

/-- Bit `b` (1 or 2) of `r14` set: the entry `rbx` of `temp` (`r12 = rdx + 16 rbx`) gets the string
`0x6f3870 + 9 b` (`x86_64`, `avx512_1`); `r8` to `rbp - 0x50`, `rdx` to `rbp - 0x48`; to the `call` of `strlen`
(1890) with `rdi` the string. -/
theorem vc_1840s {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : Nat} (hb1 : b = 1 ∨ b = 2)
    (hr15 : g.r15 = BitVec.ofNat 64 b) (hb : g.r14.getLsbD b = true)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551536#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551544#64) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rdx + g.rbx <<< 4) i)) :
    W_1840 fb F Wl (fun j' g' _ V' => j' = 1890 ∧
      g' = { g with r13 := g.rbx <<< 4, r12 := g.rdx + g.rbx <<< 4, rax := 7288944#64,
        rdi := BitVec.ofNat 64 (7288944 + 9 * b) } ∧
      V' = Vst (Vst (Vst V (g.rbp + 18446744073709551536#64) (toBytesLE g.r8 8))
        (g.rbp + 18446744073709551544#64) (toBytesLE g.rdx 8))
        (g.rdx + g.rbx <<< 4) (toBytesLE (BitVec.ofNat 64 (7288944 + 9 * b)) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr15 hb hs1 hs2 hs3 ⊢
  subst hr15
  rcases hb1 with rfl | rfl
  all_goals
    wpx [W_1840, W_1861, o53, o54, Op.bt64, Op.sxr]
    all_goals try intro fl hfl
    all_goals try simp only [hfl, hb, rfz_cf, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_implies,
      true_implies, and_true, true_and]
    all_goals first | exact hs1 | exact hs2 | exact hs3 | exact ⟨rfl, rfl, rfl⟩ | skip

/-- After `strlen` (`rax` the length): the length to `temp[rbx].len` (`r12 + 8`); `rdx = temp` and `r8` back from
the frame; bit `b` the last (`r14 = 1 << b`): to the platform (682) with `rbx = temp`, `r12 = cnt`; else to bit `b + 1`
(1840), `rbx = r8`, `r8 + 1`, `r14` without bit `b`. -/
theorem vc_1895 {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : Nat} {m T e k : Addr}
    (hc : (m = 2#64 ∧ b = 1) ∨ (m = 6#64 ∧ b = 1) ∨ (m = 4#64 ∧ b = 2))
    (hr15 : g.r15 = BitVec.ofNat 64 b) (hr14 : g.r14 = m)
    (hd : rdq(V, g.rbp + 18446744073709551544#64) = T)
    (he : rdq(Vst V (g.r12 + 8#64) (toBytesLE g.rax 8), g.rbp + 18446744073709551536#64) = e)
    (hk : rdq(Vst V (g.r12 + 8#64) (toBytesLE g.rax 8), g.rbp + 18446744073709551496#64) = k)
    (hs : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 8#64) i)) :
    W_1895 fb F Wl (fun j' g' _ V' => V' = Vst V (g.r12 + 8#64) (toBytesLE g.rax 8) ∧
      ((m = 1#64 <<< b ∧ j' = 682 ∧ g' = { g with rax := T + g.r13 + 16#64, rcx := g.rbx + 2#64, rdx := T,
        rbx := T, rsi := 1#64 <<< b, rdi := m ^^^ 1#64 <<< b, r8 := e, r12 := k,
        r15 := BitVec.ofNat 64 (b + 1) }) ∨
      (m ≠ 1#64 <<< b ∧ j' = 1840 ∧ g' = { g with rax := T + g.r13 + 16#64, rcx := g.rbx + 2#64, rdx := T,
        rbx := e, rsi := 1#64 <<< b, rdi := m ^^^ 1#64 <<< b, r8 := e + 1#64, r14 := m ^^^ 1#64 <<< b,
        r15 := BitVec.ofNat 64 (b + 1) }))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr15 hr14 hd he hk hs ⊢
  subst hr15 hr14
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    wpx [W_1895, W_2066, W_1943, o55, o60, o56, Op.shl64, hd, he, hk, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, false_implies, true_implies]
    all_goals first | exact hs | (refine ⟨rfl, Or.inl ⟨by decide, rfl, ?_⟩⟩; first | rfl | skip) |
      (refine ⟨rfl, Or.inr ⟨by decide, rfl, ?_⟩⟩; first | rfl | skip) | skip

/-- The platform (`rbp - 0x60`, not null) and its length (`rbp - 0x68`) to the entry at `rax`; `rax` the next entry
(`rcx`), `rcx + 1`; to `tls` (716). -/
theorem vc_682 {g : Gprs} {f : Rflags} {V : Addr → Byte} {p l : Addr}
    (hp : rdq(V, g.rbp + 18446744073709551520#64) = p) (hp0 : p ≠ 0#64)
    (hl : rdq(Vst V g.rax (toBytesLE p 8), g.rbp + 18446744073709551512#64) = l)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add g.rax i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i)) :
    W_682 fb F Wl (fun j' g' _ V' => j' = 716 ∧ g' = { g with rax := g.rcx <<< 4 + g.rbx, rcx := g.rcx + 1#64,
      rsi := l } ∧ V' = Vst (Vst V g.rax (toBytesLE p 8)) (g.rax + 8#64) (toBytesLE l 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp hl hs1 hs2 ⊢
  have hp' : (p &&& p == 0#64) = false := by rw [BitVec.and_self]; exact beq_eq_false_iff_ne.2 hp0
  wpx [W_682, W_691, o7, o8, Op.shl64, hp, hp', hl, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    false_implies, true_implies]
  all_goals first | exact hs1 | exact hs2 | exact ⟨rfl, rfl, rfl⟩ | skip

/-- `tls` (`0x7065da`, 3) to the entry at `rax = temp + 32`, the last of `cnt = 3`; the total length of the strings
of the result: `23` (`(6 + 3 + 2) * 2 + 0 + 1`); to 1050 with `rsi = 3`. -/
theorem vc_716_3 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r12 = 3#64) (hc : g.rcx = 3#64)
    (hA : g.rax = g.rbx + 32#64)
    (h0 : rdq(Vst (Vst V (g.rbx + 40#64) (toBytesLE 3#64 8)) (g.rbx + 32#64) (toBytesLE 7366106#64 8),
      g.rbx + 8#64) = 6#64)
    (h2 : rdq(Vst (Vst (Vst (Vst V (g.rbx + 40#64) (toBytesLE 3#64 8)) (g.rbx + 32#64) (toBytesLE 7366106#64 8))
      (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8)) (g.rbp + 18446744073709551464#64) (toBytesLE 48#64 8),
      g.rbx + 40#64) = 3#64)
    (h1 : rdq(Vst (Vst (Vst (Vst (Vst V (g.rbx + 40#64) (toBytesLE 3#64 8)) (g.rbx + 32#64)
      (toBytesLE 7366106#64 8)) (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8))
      (g.rbp + 18446744073709551464#64) (toBytesLE 48#64 8)) (g.rbp + 18446744073709551536#64) (toBytesLE 3#64 8),
      g.rbx + 24#64) = 0#64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 40#64) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 32#64) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551544#64) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551464#64) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551536#64) i)) :
    W_716 fb F Wl (fun j' g' _ V' => j' = 1050 ∧
      g' = { g with rax := 23#64, rcx := 22#64, rdx := g.rbx + 32#64, rsi := 3#64, rdi := 2#64 } ∧
      V' = Vst (Vst (Vst (Vst (Vst V (g.rbx + 40#64) (toBytesLE 3#64 8)) (g.rbx + 32#64) (toBytesLE 7366106#64 8))
        (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8)) (g.rbp + 18446744073709551464#64) (toBytesLE 48#64 8))
        (g.rbp + 18446744073709551536#64) (toBytesLE 3#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hc hA h0 h1 h2 hs1 hs2 hs3 hs4 hs5 ⊢
  subst hr hc hA
  wpx [W_716, W_743, W_761, W_806, W_2286, W_920, W_2244, W_2254, o9, o10, o11, o12, o13, o61, o62, o63, Op.shl64,
    BitVec.add_assoc, h0, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies, true_implies]
  all_goals first | exact hs1 | exact hs2 | exact hs3 | exact hs4 | exact hs5 | exact ⟨rfl, rfl, rfl⟩ | skip

/-- `tls` to the entry at `rax = temp + 48`, the last of `cnt = 4`; the total so far `32`
(`(6 + 3 + 2) * 2 + 8 + 1 + 0 + 1`); to 1010 with `rsi = 3`. -/
theorem vc_716_4 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r12 = 4#64) (hc : g.rcx = 4#64)
    (hA : g.rax = g.rbx + 48#64)
    (h0 : rdq(Vst (Vst V (g.rbx + 56#64) (toBytesLE 3#64 8)) (g.rbx + 48#64) (toBytesLE 7366106#64 8),
      g.rbx + 8#64) = 6#64)
    (h3 : rdq(Vst (Vst (Vst (Vst V (g.rbx + 56#64) (toBytesLE 3#64 8)) (g.rbx + 48#64) (toBytesLE 7366106#64 8))
      (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8)) (g.rbp + 18446744073709551464#64) (toBytesLE 64#64 8),
      g.rbx + 56#64) = 3#64)
    (h1 : rdq(Vst (Vst (Vst (Vst (Vst V (g.rbx + 56#64) (toBytesLE 3#64 8)) (g.rbx + 48#64)
      (toBytesLE 7366106#64 8)) (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8))
      (g.rbp + 18446744073709551464#64) (toBytesLE 64#64 8)) (g.rbp + 18446744073709551536#64) (toBytesLE 3#64 8),
      g.rbx + 24#64) = 8#64)
    (h2 : rdq(Vst (Vst (Vst (Vst (Vst V (g.rbx + 56#64) (toBytesLE 3#64 8)) (g.rbx + 48#64)
      (toBytesLE 7366106#64 8)) (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8))
      (g.rbp + 18446744073709551464#64) (toBytesLE 64#64 8)) (g.rbp + 18446744073709551536#64) (toBytesLE 3#64 8),
      g.rbx + 40#64) = 0#64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 56#64) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 48#64) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551544#64) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551464#64) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551536#64) i)) :
    W_716 fb F Wl (fun j' g' _ V' => j' = 1010 ∧
      g' = { g with rax := 32#64, rcx := 4#64, rdx := g.rbx + 48#64, rsi := 3#64, rdi := 2#64 } ∧
      V' = Vst (Vst (Vst (Vst (Vst V (g.rbx + 56#64) (toBytesLE 3#64 8)) (g.rbx + 48#64) (toBytesLE 7366106#64 8))
        (g.rbp + 18446744073709551544#64) (toBytesLE 6#64 8)) (g.rbp + 18446744073709551464#64) (toBytesLE 64#64 8))
        (g.rbp + 18446744073709551536#64) (toBytesLE 3#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hc hA h0 h1 h2 h3 hs1 hs2 hs3 hs4 hs5 ⊢
  subst hr hc hA
  wpx [W_716, W_743, W_761, W_806, W_2286, W_920, W_947, o9, o10, o11, o12, o13, o14, o63, Op.shl64,
    BitVec.add_assoc, h0, h1, h2, h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies, true_implies]
  all_goals first | exact hs1 | exact hs2 | exact hs3 | exact hs4 | exact hs5 | exact ⟨rfl, rfl, rfl⟩ | skip

/-- `cnt = 4 ≤ 63`, and `total + 128` fits: to 1050 with `rsi = 4`. -/
theorem vc_1010 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r12 = 4#64) (ha : g.rax = 32#64) :
    W_1010 fb F Wl (fun j' g' _ V' => j' = 1050 ∧ g' = { g with rcx := 63#64, rsi := 4#64, rdi := 0#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr ha ⊢
  subst hr ha
  wpx [W_1010, W_1020, o15, o16, Op.shr64, Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies,
    true_implies]
  all_goals try intro fl hfl
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | skip

/-- `total << (cnt - 3)`, `*ncapstr = 1 << cnt` (`rcx` the pointer, from `rbp - 0x58`); to the `call` of `malloc`
(1111) with `rdi = 16 · 2^cnt + total` (151 or 320). -/
theorem vc_1050 {g : Gprs} {f : Rflags} {V : Addr → Byte} {n t : Nat} {N : Addr}
    (hn : (n = 3 ∧ t = 23) ∨ (n = 4 ∧ t = 32)) (hsi : g.rsi = BitVec.ofNat 64 n) (ha : g.rax = BitVec.ofNat 64 t)
    (hN : rdq(Vst (Vst V (g.rbp + 18446744073709551512#64) (toBytesLE g.rdx 8)) (g.rbp + 18446744073709551520#64)
      (toBytesLE (BitVec.ofNat 32 n) 4), g.rbp + 18446744073709551528#64) = N)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551512#64) i))
    (hs2 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 18446744073709551520#64) i))
    (hs3 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 18446744073709551476#64) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add N i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 18446744073709551480#64) i)) :
    W_1050 fb F Wl (fun j' g' _ V' => j' = 1111 ∧
      g' = { g with rax := BitVec.ofNat 64 (t <<< (n - 3)), rcx := N,
        rdi := BitVec.ofNat 64 (16 * 2 ^ n + t <<< (n - 3)), r8 := 1#64, r13 := BitVec.ofNat 64 (16 * 2 ^ n) } ∧
      V' = Vst (Vst (Vst (Vst (Vst V (g.rbp + 18446744073709551512#64) (toBytesLE g.rdx 8))
        (g.rbp + 18446744073709551520#64) (toBytesLE (BitVec.ofNat 32 n) 4))
        (g.rbp + 18446744073709551476#64) (toBytesLE (BitVec.ofNat 32 (2 ^ n)) 4)) N
        (toBytesLE (BitVec.ofNat 64 (2 ^ n)) 8)) (g.rbp + 18446744073709551480#64)
        (toBytesLE (BitVec.ofNat 64 (2 ^ n)) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsi ha hN hs1 hs2 hs3 hs4 hs5 ⊢
  subst hsi ha
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    wpx [W_1050, W_1056, o17, o18, Op.shl64, Op.shl, Op.sxr, hN]
    all_goals first | exact hs1 | exact hs2 | exact hs3 | exact hs4 | exact hs5 | exact ⟨rfl, rfl, rfl⟩ | skip

end FV7z.Hwc
