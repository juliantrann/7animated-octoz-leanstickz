import FV7z.Pcs.Cuts
import FV7z.Stu.Holds
import FV7z.Hca.Holds
import FV7z.Start.Inv
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCall
import FV7z.Lemmas.CmovLd
/-!
# `ParseComplexSize` (PLAN.md §M, M1)

7-Zip 26.06's `ParseComplexSize (const wchar_t *s, UInt64 &result)` at `0x5d38f0` in `7zzs`
(`CPP/7zip/UI/Common/OpenArchive.cpp`; `objdump -d`): `result` = 0, `ConvertStringToUInt64 (s, &end)` (`Stu.stu_ok`)
into a frame of 24 bytes with the stack guard (`fs:0x28`) at `rsp + 8`; no digit (`end` = `s`) is a failure; after
the digits, the end of the string stores the value; one more character (the next one the end) picks a shift by the
jump table at `0x6e8e8c` (`b`, `k`, `m`, `g`, `t`, upper case too), stored when the value does not overflow. The
answer is 0 or 1. Cut points (`Pcs/Cuts.lean`): the entry, 47 (after the call), the cases 112, 176, 184, 200, 224,
248, the shift 122 and the stack guard's check 144; the `call` at 42, the `ret` at 166.

- `fsp`: the frame; `pg1`, `pV1`: the registers and the bytes at the `call`; `pV2`: with its return address.
- `Pe`: what the entry needs; `Fr`: the bytes apart from the call's frame and `result`, those with the pushes.
- `Inv`, `Fin`, `Nx`: the invariant at the cut points after the call, the `ret`, the post of `cfgAt`.
- `pcs_ok`: from the entry to the return address, `rax` 0 or 1, the registers a call keeps (`Ret`), the bytes apart
  from the frame and `result` as before. The value is not followed: the spec is the control flow and the stores.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pcs

/-- The `call ConvertStringToUInt64`. -/
def pcall : List Byte := [0xe8, 0x11, 0xda, 0xe7, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073707969041] 5) := by dec_rfl
theorem w_42 : pcall <+: pcs.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat pcs 42 (FV7z.mk .call 64 [.rel 18446744073707969041] 5) :=
  Dec.shift (j := 42) (k := 0) (pcall_0 feat) w_42 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_166 : pret <+: pcs.drop 166 := by decide +kernel
theorem ret_166 (feat : Features) : Dec feat pcs 166 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 166) (k := 0) (pret_0 feat) w_166 (Nat.zero_le _)

/-! ## The frame -/

/-- The frame: `rsp - 40` at the entry, after the two `push`es and `sub rsp, 24`. -/
def fsp (g : Gprs) : Addr := g.rsp - 8 - 8 - 24#64

/-- The stack guard as the entry reads it, after the `push`es. -/
def cnr (V : Addr → Byte) (g : Gprs) (fb : Addr) : BitVec 64 :=
  rdq(Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8), fb + 40#64)

/-- The registers at the `call`, from `g` at the entry and the stack guard `c`. -/
def pg1 (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 c ^^^ BitVec.setWidth 32 c)
    rbx := g.rdi
    rsp := fsp g
    rbp := g.rsi
    rsi := fsp g }

/-- The bytes with `rbp` and `rbx` pushed and the stack guard at `rsp - 32`. -/
def pVf (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)) (fsp g + 8#64)
    (toBytesLE (cnr V g fb) 8)

/-- The bytes at the `call`: `result` = 0 too. -/
def pV1 (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte := Vst (pVf V g fb) g.rsi (toBytesLE (0#64) 8)

/-- The bytes at `ConvertStringToUInt64`'s entry: the return address at `rsp - 48`. -/
def pV2 (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst (pV1 V g fb) (fsp g - 8) (toBytesLE (Addr.add pcs_at 47) 8)

/-- `m` bytes at `a` within the address space, apart from the 48 below `rsp` and from `result`. -/
abbrev Ap (g : Gprs) (a : Addr) (m : Nat) : Prop :=
  a.toNat + m ≤ 2 ^ 64 ∧ (a.toNat + m ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ a.toNat) ∧
    (a.toNat + m ≤ g.rsi.toNat ∨ g.rsi.toNat + 8 ≤ a.toNat)

/-- A character that may be read. -/
abbrev Cf (F : Footprint) (g : Gprs) (a : Addr) : Prop := Ap g a 4 ∧ ∀ i < 4, Foot F.data (Addr.add a i)

/-- An address apart from the 48 bytes below `rsp` and from `result`. -/
abbrev Oa (g : Gprs) (y : Addr) : Prop :=
  (y.toNat < g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ y.toNat) ∧ (y.toNat < g.rsi.toNat ∨ g.rsi.toNat + 8 ≤ y.toNat)

/-- What the entry needs, `n` digits at `s` (`rdi`): the 48 bytes below `rsp` in what the run may store into, and
the return address with them in the footprint; `result` (`rsi`) 8 bytes that may be stored into, apart from them;
the stack guard and the jump table in the footprint, apart from both; the digits and the character after them (and
the one after that when it is not 0) in the footprint, apart from both. -/
structure Pe (F : Footprint) (Wl : List Rgn) (fb : Addr) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop where
  lo : 48 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  fw : ∀ i < 48, Foot Wl (Addr.add (g.rsp - 48#64) i)
  fd : ∀ i < 56, Foot F.data (Addr.add (g.rsp - 48#64) i)
  wr : ∀ i < 8, Foot Wl (Addr.add g.rsi i)
  rb : g.rsi.toNat + 8 ≤ 2 ^ 64
  rf : g.rsi.toNat + 8 ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat + 8 ≤ g.rsi.toNat
  cl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  cf : Ap g (fb + 40#64) 8
  tab : ∀ i < 76, Foot F.data (Addr.add 7245452#64 i)
  ta : Ap g 7245452#64 76
  jt : List.map V (byteAddrs 7245452#64 76) = pcs_jt
  dg : ∀ k < n, Stu.isD (Stu.ch V g.rdi k) = true
  nd : Stu.isD (Stu.ch V g.rdi n) = false
  ca : ∀ k ≤ n, Cf F g (g.rdi + BitVec.ofNat 64 (4 * k))
  cn : Stu.ch V g.rdi n ≠ 0 → Cf F g (g.rdi + BitVec.ofNat 64 (4 * (n + 1)))

variable {F : Footprint} {Wl : List Rgn} {fb : Addr} {n : Nat} {g : Gprs} {V V' : Addr → Byte}

theorem tS8 (lo : 48 ≤ g.rsp.toNat) : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tS16 (lo : 48 ≤ g.rsp.toNat) : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF (lo : 48 ≤ g.rsp.toNat) : (fsp g).toNat = g.rsp.toNat - 40 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF8 (lo : 48 ≤ g.rsp.toNat) : (fsp g + 8#64).toNat = g.rsp.toNat - 32 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tFm8 (lo : 48 ≤ g.rsp.toNat) : (fsp g - 8).toNat = g.rsp.toNat - 48 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem t48 (lo : 48 ≤ g.rsp.toNat) : (g.rsp - 48#64).toNat = g.rsp.toNat - 48 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The `pop`s' slots. -/
theorem e16 (g : Gprs) : fsp g + 24#64 = g.rsp - 8 - 8 := BitVec.sub_add_cancel _ _
theorem e8 (g : Gprs) : fsp g + 24#64 + 8 = g.rsp - 8 := by rw [e16]; exact BitVec.sub_add_cancel _ _
theorem e3 (g : Gprs) : fsp g + 24#64 + 8 + 8 = g.rsp := by rw [e8]; exact BitVec.sub_add_cancel _ _

/-- An address of the 56 bytes from `rsp - 48`. -/
theorem at48 (hP : Pe F Wl fb n g V) {x : Addr} {d : Nat} (hd : d < 56) (hx : x.toNat = g.rsp.toNat - 48 + d) :
    x = Addr.add (g.rsp - 48#64) d := by
  have lo := hP.lo
  have hi := hP.hi
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_add_of_fits (a := g.rsp - 48#64) (n := 56) hd (by rw [t48 lo]; omega), t48 lo]

theorem fd_at (hP : Pe F Wl fb n g V) {x : Addr} {d m : Nat} (hx : x.toNat = g.rsp.toNat - 48 + d)
    (hdm : d + m ≤ 56) : ∀ i < m, Foot F.data (Addr.add x i) := fun i hi => by
  rw [at48 hP (d := d) (by omega) hx, addr_add_add']
  exact hP.fd (d + i) (by omega)

theorem fw_at (hP : Pe F Wl fb n g V) {x : Addr} {d m : Nat} (hx : x.toNat = g.rsp.toNat - 48 + d)
    (hdm : d + m ≤ 48) : ∀ i < m, Foot Wl (Addr.add x i) := fun i hi => by
  rw [at48 hP (d := d) (by omega) hx, addr_add_add']
  exact hP.fw (d + i) (by omega)

/-! ## The bytes -/

/-- The bytes apart from the frame and `result`, those with the pushes and the stack guard. -/
def Fr (g₀ : Gprs) (V₀ : Addr → Byte) (fb : Addr) (V : Addr → Byte) : Prop :=
  ∀ y : Addr, (y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat - 32 ≤ y.toNat) →
    (y.toNat < g₀.rsi.toNat ∨ g₀.rsi.toNat + 8 ≤ y.toNat) → V y = pVf V₀ g₀ fb y

theorem pVf_out (lo : 48 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64) {y : Addr}
    (h : y.toNat < g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ y.toNat) : pVf V g fb y = V y := by
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tF8 lo
  unfold pVf
  rw [Tun.Vst_out _ (fsp g + 8#64) (toBytesLE (cnr V g fb) 8) y ?a1 ?a2,
    Tun.Vst_out _ (g.rsp - 8 - 8) (toBytesLE g.rbx 8) y ?b1 ?b2,
    Tun.Vst_out V (g.rsp - 8) (toBytesLE g.rbp 8) y ?c1 ?c2]
  all_goals (try simp only [toBytesLE_length, a1, a2, a3])
  all_goals omega

theorem fr_out (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') : ∀ y, Oa g y → V' y = V y := by
  rintro y ⟨h1, h2⟩
  rw [hFr y (by omega) h2]
  exact pVf_out hP.lo hP.hi (by omega)

/-- Bytes apart from the frame and `result`. -/
theorem rd_out {V V' : Addr → Byte} {a : Addr} {m : Nat} (h : ∀ y, Oa g y → V y = V' y) (ha : Ap g a m) :
    List.map V (byteAddrs a m) = List.map V' (byteAddrs a m) := by
  obtain ⟨h1, h2, h3⟩ := ha
  exact Start.rd_congr fun i hi => h _ (by
    have := toNat_add_of_fits (a := a) hi h1
    exact ⟨by omega, by omega⟩)

/-- Bytes from `rsp - 32` up to the return address. -/
theorem rd_fr (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') {a : Addr} (h1 : g.rsp.toNat - 32 ≤ a.toNat)
    (h2 : a.toNat ≤ g.rsp.toNat) : List.map V' (byteAddrs a 8) = List.map (pVf V g fb) (byteAddrs a 8) :=
  Start.rd_congr fun i hi => by
    have hi' := hP.hi
    have e := toNat_add_of_fits (a := a) hi (by omega)
    have := hP.rf
    exact hFr _ (by omega) (by omega)

/-- `result` stored. -/
theorem fr_st (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') (x : BitVec 64) :
    Fr g V fb (Vst V' g.rsi (toBytesLE x 8)) := by
  intro y h1 h2
  rw [Tun.Vst_out V' g.rsi (toBytesLE x 8) y (by rw [toBytesLE_length]; exact hP.rb)
    (by rw [toBytesLE_length]; exact h2)]
  exact hFr y h1 h2

/-- The bytes at `ConvertStringToUInt64`'s entry, apart from its return address and `result`. -/
theorem fr_v2 (hP : Pe F Wl fb n g V) {y : Addr} (h1 : y.toNat < g.rsp.toNat - 48 ∨ g.rsp.toNat - 40 ≤ y.toNat)
    (h2 : y.toNat < g.rsi.toNat ∨ g.rsi.toNat + 8 ≤ y.toNat) : pV2 V g fb y = pVf V g fb y := by
  have lo := hP.lo
  have hi := hP.hi
  have rb := hP.rb
  have a4 := tFm8 lo
  unfold pV2 pV1
  rw [Tun.Vst_out _ (fsp g - 8) (toBytesLE (Addr.add pcs_at 47) 8) y ?a1 ?a2,
    Tun.Vst_out _ g.rsi (toBytesLE (0#64) 8) y ?b1 ?b2]
  all_goals (try simp only [toBytesLE_length, a4])
  all_goals omega

theorem v2_out (hP : Pe F Wl fb n g V) {y : Addr} (h : Oa g y) : pV2 V g fb y = V y := by
  obtain ⟨h1, h2⟩ := h
  rw [fr_v2 hP (by omega) h2]
  exact pVf_out hP.lo hP.hi (by omega)

theorem ch2 (hP : Pe F Wl fb n g V) {k : Nat} (ha : Ap g (g.rdi + BitVec.ofNat 64 (4 * k)) 4) :
    Stu.ch (pV2 V g fb) g.rdi k = Stu.ch V g.rdi k :=
  congrArg (ofBytesLE 32) (rd_out (fun _ hy => v2_out hP hy) ha)

/-- The return address of the call. -/
theorem ra2 (lo : 48 ≤ g.rsp.toNat) : rdq(pV2 V g fb, fsp g - 8) = Addr.add pcs_at 47 := by
  have := g.rsp.isLt
  unfold pV2
  rw [Tun.rd_Vst_self (pV1 V g fb) (fsp g - 8) (toBytesLE (Addr.add pcs_at 47) 8) (toBytesLE_length _ _)
    (by rw [tFm8 lo]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- After `ConvertStringToUInt64`: the bytes, and `end` = `s` or the character after the digits. -/
theorem mem3 (hP : Pe F Wl fb n g V) {g' : Gprs} {V₃ : Addr → Byte} (hsi : g'.rsi = fsp g) (hdi : g'.rdi = g.rdi)
    (hM : Stu.Mem g' (pV2 V g fb) n V₃) :
    Fr g V fb V₃ ∧ (rdq(V₃, fsp g) = g.rdi ∨ rdq(V₃, fsp g) = g.rdi + BitVec.ofNat 64 (4 * n)) := by
  have lo := hP.lo
  have hi := hP.hi
  have a0 := tF lo
  have hne : fsp g ≠ 0 := fun h => by
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h, h0] at a0
    omega
  have fr3 : ∀ bs : List Byte, bs.length = 8 → Fr g V fb (Vst (pV2 V g fb) (fsp g) bs) := by
    intro bs hb y h1 h2
    rw [Tun.Vst_out (pV2 V g fb) (fsp g) bs y (by rw [hb, a0]; omega) (by rw [hb, a0]; omega)]
    exact fr_v2 hP (by omega) h2
  unfold Stu.Mem Stu.M1 at hM
  rw [hsi, hdi] at hM
  rcases hM with (⟨h0, -⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩
  · exact absurd h0 hne
  · refine ⟨fr3 _ (toBytesLE_length _ _), Or.inl ?_⟩
    rw [Tun.rd_Vst_self (pV2 V g fb) (fsp g) (Stu.bp g.rdi) (toBytesLE_length _ _) (by rw [a0]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine ⟨?_, Or.inr ?_⟩
    · intro y h1 h2
      rw [Tun.Vst_out (Vst (pV2 V g fb) (fsp g) (Stu.bp g.rdi)) (fsp g)
        (Stu.bp (g.rdi + BitVec.ofNat 64 (4 * n))) y (by rw [toBytesLE_length, a0]; omega)
        (by rw [toBytesLE_length, a0]; omega)]
      exact fr3 _ (toBytesLE_length _ _) y h1 h2
    · rw [Tun.rd_Vst_self (Vst (pV2 V g fb) (fsp g) (Stu.bp g.rdi)) (fsp g)
        (Stu.bp (g.rdi + BitVec.ofNat 64 (4 * n))) (toBytesLE_length _ _) (by rw [a0]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The stack guard read at the entry. -/
theorem cnr_eq (lo : 48 ≤ g.rsp.toNat) (hc : Ap g (fb + 40#64) 8) : cnr V g fb = rdq(V, fb + 40#64) := by
  have a1 := tS8 lo
  have a2 := tS16 lo
  obtain ⟨c1, c2, -⟩ := hc
  unfold cnr
  rw [Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbx 8) (fb + 40#64) 8 ?a1 c1 ?a3,
    Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.rbp 8) (fb + 40#64) 8 ?b1 c1 ?b3]
  all_goals (try simp only [toBytesLE_length, a1, a2])
  all_goals omega

/-- The stack guard at the check. -/
theorem can_eq (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') : rdq(V', fsp g + 8#64) = rdq(V', fb + 40#64) := by
  have lo := hP.lo
  have hi := hP.hi
  have a3 := tF8 lo
  rw [rd_fr hP hFr (a := fsp g + 8#64) (by omega) (by omega), rd_out (fr_out hP hFr) hP.cf, ← cnr_eq lo hP.cf]
  unfold pVf
  rw [Tun.rd_Vst_self _ (fsp g + 8#64) (toBytesLE (cnr V g fb) 8) (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- What the `pop`s read. -/
theorem pop_rd (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') :
    rdq(V', fsp g + 24#64) = g.rbx ∧ rdq(V', fsp g + 24#64 + 8) = g.rbp := by
  have lo := hP.lo
  have hi := hP.hi
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tF8 lo
  rw [e8, e16, rd_fr hP hFr (a := g.rsp - 8 - 8) (by omega) (by omega),
    rd_fr hP hFr (a := g.rsp - 8) (by omega) (by omega)]
  unfold pVf
  refine ⟨?_, ?_⟩
  · rw [Tun.rd_Vst _ (fsp g + 8#64) (toBytesLE (cnr V g fb) 8) (g.rsp - 8 - 8) 8 ?a1 ?a2 ?a3,
      Tun.rd_Vst_self _ (g.rsp - 8 - 8) (toBytesLE g.rbx 8) (toBytesLE_length _ _) ?a4,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, a2, a3])
    all_goals omega
  · rw [Tun.rd_Vst _ (fsp g + 8#64) (toBytesLE (cnr V g fb) 8) (g.rsp - 8) 8 ?b1 ?b2 ?b3,
      Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbx 8) (g.rsp - 8) 8 ?c1 ?c2 ?c3,
      Tun.rd_Vst_self V (g.rsp - 8) (toBytesLE g.rbp 8) (toBytesLE_length _ _) ?c4,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, a1, a2, a3])
    all_goals omega

/-- The return address. -/
theorem ra_rd (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') :
    List.map V' (byteAddrs g.rsp 8) = List.map V (byteAddrs g.rsp 8) := by
  have lo := hP.lo
  rw [rd_fr hP hFr (a := g.rsp) (by omega) (Nat.le_refl _)]
  exact Start.rd_congr fun i hi => pVf_out hP.lo hP.hi
    (by have := toNat_add_of_fits (a := g.rsp) hi hP.hi; omega)

/-! ## The jump table -/

theorem jt_addr (w : BitVec 32) (_h : w.toNat ≤ 18) :
    7245452#64 + BitVec.setWidth 64 w * 4#64 = Addr.add 7245452#64 (4 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The cases. -/
abbrev Cs (ℓ : Nat) : Prop := ℓ = 112 ∨ ℓ = 176 ∨ ℓ = 184 ∨ ℓ = 200 ∨ ℓ = 224 ∨ ℓ = 248

theorem jt_case : ∀ k < 19, (ofBytesLE 32 ((pcs_jt.drop (4 * k)).take 4)).signExtend 64 + 7245452#64 =
    Addr.add pcs_at (pcs_cases.getD k 0) := by decide +kernel

theorem cs_ok : ∀ k < 19, Cs (pcs_cases.getD k 0) ∧ pcs_cases.getD k 0 < 273 := by decide +kernel

theorem ap_jt (hP : Pe F Wl fb n g V) {k : Nat} (hk : k < 19) : Ap g (Addr.add 7245452#64 (4 * k)) 4 := by
  obtain ⟨a1, a2, a3⟩ := hP.ta
  have e := toNat_add_of_fits (a := 7245452#64) (i := 4 * k) (n := 76) (by omega) (by decide)
  simp only [BitVec.toNat_ofNat] at e a1 a2 a3
  exact ⟨by omega, by omega, by omega⟩

theorem jt_V (hP : Pe F Wl fb n g V) (hFr : Fr g V fb V') :
    ∀ k < 19, List.map V' (byteAddrs (Addr.add 7245452#64 (4 * k)) 4) = (pcs_jt.drop (4 * k)).take 4 :=
  fun k hk => (rd_out (fr_out hP hFr) (ap_jt hP hk)).trans (Hca.sub_rd V _ pcs_jt 76 hP.jt (4 * k) 4 (by omega))

theorem jt_foot (hP : Pe F Wl fb n g V) (w : BitVec 32) (hw : w.toNat ≤ 18) :
    ∀ i < 4, Foot F.data (Addr.add (7245452#64 + BitVec.setWidth 64 w * 4#64) i) := by
  intro i hi
  rw [jt_addr w hw, addr_add_add']
  exact hP.tab (4 * w.toNat + i) (by omega)

/-- The table's target, a case. -/
theorem tg {P : Nat → Prop} (w : BitVec 32) (hw : w.toNat ≤ 18)
    (hrd : ∀ k < 19, List.map V (byteAddrs (Addr.add 7245452#64 (4 * k)) 4) = (pcs_jt.drop (4 * k)).take 4)
    (hq : ∀ ℓ, Cs ℓ → P ℓ) :
    ∃ tgt, tgt < pcs.length ∧ BitVec.signExtend 64 (ofBytesLE 32 (List.map V
      (byteAddrs (7245452#64 + BitVec.setWidth 64 w * 4#64) 4))) + 7245452#64 = Addr.add pcs_at tgt ∧ P tgt := by
  have hk : w.toNat < 19 := by omega
  rw [jt_addr w hw, hrd _ hk]
  obtain ⟨hc, hl⟩ := cs_ok w.toNat hk
  exact ⟨_, lt_len hl, jt_case w.toNat hk, hq _ hc⟩

theorem nz_of {c : BitVec 32} (h : (c &&& c == 0) = false) : c ≠ 0 := by
  intro hc
  rw [hc] at h
  exact absurd h (by decide)

theorem ja_le {w : BitVec 32} (h : (!(decide (w.toNat < 18) || decide (w = 18#32))) = false) : w.toNat ≤ 18 := by
  by_cases h1 : w.toNat < 18
  · omega
  · by_cases h2 : w = 18#32
    · subst h2
      decide
    · simp [h1, h2] at h

theorem sw1 : BitVec.setWidth 64 1#32 = (1 : BitVec 64) := by decide

/-! ## The invariant -/

/-- The registers after the call: `rbx` = `s`, `rbp` = `&result`, `rsp` the frame, `r12`–`r15` as at the entry. -/
abbrev Rk (g₀ g : Gprs) : Prop :=
  g.rbx = g₀.rdi ∧ g.rbp = g₀.rsi ∧ g.rsp = fsp g₀ ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- The invariant at the cut points after the call: 47, `end` = `s` or after the digits; a case; the shift; the
check, `rax` 0 or 1. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (fb : Addr) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  Rk g₀ g ∧ Fr g₀ V₀ fb V ∧
    ((ℓ = 47 ∧ m = 4 ∧ (rdq(V, fsp g₀) = g₀.rdi ∨ rdq(V, fsp g₀) = g₀.rdi + BitVec.ofNat 64 (4 * n))) ∨
      (Cs ℓ ∧ m = 3) ∨ (ℓ = 122 ∧ m = 2) ∨ (ℓ = 144 ∧ m = 1 ∧ (g.rax = 0 ∨ g.rax = 1)))

/-- At the `ret`: the frame dropped, `rbx` and `rbp` popped. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (fb : Addr) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 166 ∧ Fr g₀ V₀ fb V ∧ g.rsp = fsp g₀ + 24#64 + 8 + 8 ∧ g.rbx = rdq(V, fsp g₀ + 24#64) ∧
    g.rbp = rdq(V, fsp g₀ + 24#64 + 8) ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧
    (g.rax = 0 ∨ g.rax = 1)

/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (fb : Addr) (n m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ fb n j m' g V) ∨ Fin g₀ V₀ fb j g V

variable {g₀ : Gprs} {V₀ : Addr → Byte} {m ℓ : Nat} {f : Rflags}

theorem eC (hℓ : Cs ℓ) (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) (hm : 3 < m) : Nx g₀ V₀ fb n m ℓ g f V :=
  Or.inl ⟨3, hm, by unfold Inv; exact ⟨hR, hFr, Or.inr (Or.inl ⟨hℓ, rfl⟩)⟩⟩

theorem e122 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) (hm : 2 < m) : Nx g₀ V₀ fb n m 122 g f V :=
  Or.inl ⟨2, hm, by unfold Inv; exact ⟨hR, hFr, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩⟩

theorem e144 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) (hm : 1 < m) (hax : g.rax = 0 ∨ g.rax = 1) :
    Nx g₀ V₀ fb n m 144 g f V :=
  Or.inl ⟨1, hm, by unfold Inv; exact ⟨hR, hFr, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hax⟩))⟩⟩

theorem e166 (hFr : Fr g₀ V₀ fb V) (hax : g.rax = 0 ∨ g.rax = 1) (hs : g.rsp = fsp g₀ + 24#64 + 8 + 8)
    (hb : g.rbx = rdq(V, fsp g₀ + 24#64)) (hp : g.rbp = rdq(V, fsp g₀ + 24#64 + 8)) (h12 : g.r12 = g₀.r12)
    (h13 : g.r13 = g₀.r13) (h14 : g.r14 = g₀.r14) (h15 : g.r15 = g₀.r15) : Nx g₀ V₀ fb n m 166 g f V :=
  Or.inr (by unfold Fin; exact ⟨rfl, hFr, hs, hb, hp, h12, h13, h14, h15, hax⟩)

/-! ## The cut points -/

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- `Rk` of the registers after the substitution. -/
local macro "rR" : term => `(⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- From the entry to the `call`: the pushes, the stack guard stored in the frame, `result` = 0. -/
theorem vc_0 (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (h3 : ∀ i < 8, Foot Wl (Addr.add (fsp g + 8#64) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add g.rsi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 42 ∧ g' = pg1 g (cnr V g fb) ∧ V' = pV1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [fsp] at h1 h2 h3 h4
  wpx [W_0, o0, Op.ldf, Op.stf, Op.xormf]
  all_goals vc_fin

set_option maxHeartbeats 1000000 in
/-- 47, after the call: no digit, to 176; the end of the string, to 184; one more character and the end, by the
table; else 176 or 144 with `rax` = 0. -/
theorem vc_47 (hP : Pe F Wl fb n g₀ V₀) (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V)
    (hE : rdq(V, fsp g₀) = g₀.rdi ∨ rdq(V, fsp g₀) = g₀.rdi + BitVec.ofNat 64 (4 * n)) :
    W_47 fb F Wl (Nx g₀ V₀ fb n 4) g f V := by
  have lo := hP.lo
  have f0 : ∀ i < 8, Foot F.data (Addr.add (fsp g₀) i) := fd_at hP (d := 8) (by rw [tF lo]; omega) (by decide)
  have f1 : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 (4 * n)) i) := (hP.ca n (Nat.le_refl n)).2
  have hcv : rdd(V, g₀.rdi + BitVec.ofNat 64 (4 * n)) = Stu.ch V₀ g₀.rdi n :=
    congrArg (ofBytesLE 32) (rd_out (fr_out hP hFr) (hP.ca n (Nat.le_refl n)).1)
  have f2 : rdd(V, g₀.rdi + BitVec.ofNat 64 (4 * n)) ≠ 0 →
      ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 (4 * n) + 4#64) i) := fun h => by
    rw [Stu.adv4]
    exact (hP.cn fun h0 => h (hcv.trans h0)).2
  have hjv := jt_V hP hFr
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx -implicitDefEqProofs [W_47, W_56, W_65, W_74, W_94, o1, o2, o3, o4, o5, Op.ldsx]
  generalize ofBytesLE 64 (List.map V (byteAddrs (fsp g₀) 8)) = E at hE ⊢
  refine ⟨f0, fun _ => eC (by decide) rR hFr (by decide), fun h1 => ?_⟩
  obtain rfl : E = g₀.rdi + BitVec.ofNat 64 (4 * n) := hE.resolve_left (of_decide_eq_false h1)
  refine ⟨f1, fun _ => ⟨fun _ => eC (by decide) rR hFr (by decide), fun h2 => ⟨f2 (nz_of h2), fun _ _ =>
    ⟨fun _ => e144 rR hFr (by decide) (Or.inl (lf_xz _)), fun _ => ⟨fun _ => eC (by decide) rR hFr (by decide),
    fun h4 => ⟨jt_foot hP _ (ja_le h4), tg _ (ja_le h4) hjv ?_⟩⟩⟩⟩⟩⟩
  intro ℓ hℓ
  exact eC hℓ rR hFr (by decide)

/-- 112: the shift for `b`, to 122. -/
theorem vc_112 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) : W_112 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_112, o6]
  exact e122 rR hFr (by decide)

theorem vc_200 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) : W_200 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_200, o13]
  exact e122 rR hFr (by decide)

theorem vc_224 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) : W_224 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_224, o14]
  exact e122 rR hFr (by decide)

theorem vc_248 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) : W_248 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_248, o15]
  exact e122 rR hFr (by decide)

/-- 176: `rax` = 0, to the check. -/
theorem vc_176 (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) : W_176 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_176, o11]
  exact fun _ => e144 rR hFr (by decide) (Or.inl (lf_xz _))

/-- 184: the value stored, `rax` = 1, to the check. -/
theorem vc_184 (hP : Pe F Wl fb n g₀ V₀) (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) :
    W_184 fb F Wl (Nx g₀ V₀ fb n 3) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_184, o12]
  exact ⟨hP.wr, e144 rR (fr_st hP hFr _) (by decide) (Or.inr sw1)⟩

/-- 122: an overflow, `rax` = 0; else the value shifted stored, `rax` = 1; to the check. -/
theorem vc_122 (hP : Pe F Wl fb n g₀ V₀) (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) :
    W_122 fb F Wl (Nx g₀ V₀ fb n 2) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_122, W_129, o7, o8, Op.shl64]
  exact fun _ => ⟨fun _ => e144 rR hFr (by decide) (Or.inl (lf_xz _)),
    fun _ _ => ⟨hP.wr, e144 rR (fr_st hP hFr _) (by decide) (Or.inr sw1)⟩⟩

set_option maxHeartbeats 1000000 in
/-- 144: the stack guard checked, the frame dropped, `rbx` and `rbp` popped, to the `ret`. -/
theorem vc_144 (hP : Pe F Wl fb n g₀ V₀) (hR : Rk g₀ g) (hFr : Fr g₀ V₀ fb V) (hax : g.rax = 0 ∨ g.rax = 1) :
    W_144 fb F Wl (Nx g₀ V₀ fb n 1) g f V := by
  have lo := hP.lo
  have hc := can_eq hP hFr
  have f8 : ∀ i < 8, Foot F.data (Addr.add (fsp g₀ + 8#64) i) :=
    fd_at hP (d := 16) (by rw [tF8 lo]; omega) (by decide)
  have f24 : ∀ i < 8, Foot F.data (Addr.add (fsp g₀ + 24#64) i) :=
    fd_at hP (d := 32) (by rw [e16, tS16 lo]; omega) (by decide)
  have f32 : ∀ i < 8, Foot F.data (Addr.add (fsp g₀ + 24#64 + 8) i) :=
    fd_at hP (d := 40) (by rw [e8, tS8 lo]; omega) (by decide)
  have hcl := hP.cl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax
  obtain ⟨hb, hp, hs, h12, h13, h14, h15⟩ := hR
  dsimp only at hb hp hs h12 h13 h14 h15
  subst hb hp hs h12 h13 h14 h15
  wpx [W_144, W_160, o9, o10, Op.xormf, hc, BitVec.xor_self]
  repeat' (first | exact f8 | exact hcl | exact f24 | exact f32 | exact e166 hFr hax rfl rfl rfl rfl rfl rfl rfl |
    (intro h; exact absurd h (by decide)) | apply And.intro | intro _)

theorem vcAll (hP : Pe F Wl fb n g₀ V₀) (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ fb n ℓ m g V) : Wt fb ℓ F Wl (Nx g₀ V₀ fb n m) g f V := by
  obtain ⟨hR, hFr, ⟨rfl, rfl, hE⟩ | ⟨hC, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hax⟩⟩ := h
  · exact vc_47 hP hR hFr hE
  · rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
    · exact vc_112 hR hFr
    · exact vc_176 hR hFr
    · exact vc_184 hP hR hFr
    · exact vc_200 hR hFr
    · exact vc_224 hR hFr
    · exact vc_248 hR hFr
  · exact vc_122 hP hR hFr
  · exact vc_144 hP hR hFr hax

/-- What the return leaves of the registers, from `X` at the entry: `rsp` past the return address, `rbx`, `rbp`
and `r12`–`r15` as at the entry. -/
def Ret (X Z : State) : Prop :=
  Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
    Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
    Z.cpu.gpr.r15 = X.cpu.gpr.r15

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `ParseComplexSize (s, result)` from its entry, with `n` digits at `s` and what `Pe` asks: at the return
address, the return address popped, the registers a call keeps as at the entry (`Ret`), `rax` 0 or 1, the bytes
apart from the 48 below `rsp` and from `result` as before. -/
theorem pcs_ok (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pcs_at pcs)
    (hinS : CodeIn L Stu.stu_at Stu.stu) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pcs_at) (hP : Pe F Wl fb n X.cpu.gpr V)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Ret X Z → (Z.cpu.gpr.rax = 0 ∨ Z.cpu.gpr.rax = 1) →
      (∀ y, Oa X.cpu.gpr y → V' y = V y) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have lo := hP.lo
  have hi := hP.hi
  -- to the call
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 42 ∧ g' = pg1 X.cpu.gpr (cnr V X.cpu.gpr fb) ∧ V' = pV1 V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 (fw_at hP (d := 40) (by rw [tS8 lo]; omega) (by decide))
      (fw_at hP (d := 32) (by rw [tS16 lo]; omega) (by decide)) hP.cl
      (fw_at hP (d := 16) (by rw [tF8 lo]; omega) (by decide)) hP.wr) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hgY]; try rfl
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_42 _) hinS (Stu.lt_len (by decide)) (by decide)
    (by rw [hYsp]; exact fw_at hP (d := 0) (by rw [tFm8 lo]; omega) (by decide)) ?_
  rintro Y₂ t₂ hKY₂ hAY₂ ⟨hrY₂, hgY₂⟩
  rw [hYsp] at hAY₂
  have hA2 : Agree F Y₂.proc.mm.mem (pV2 V X.cpu.gpr fb) := hAY₂
  have hsp2 : Y₂.cpu.gpr.rsp = fsp X.cpu.gpr - 8 := by rw [hgY₂]; exact congrArg (· - 8) hYsp
  have hsi2 : Y₂.cpu.gpr.rsi = fsp X.cpu.gpr := by rw [hgY₂, hgY]; try rfl
  have hdi2 : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY₂, hgY]; try rfl
  -- `ConvertStringToUInt64 (s, &end)`
  refine Stu.stu_ok (n := n) c hinS hKY₂ hA2 hrY₂
    (fun k hk => by rw [hdi2, ch2 hP (hP.ca k (Nat.le_of_lt hk)).1]; exact hP.dg k hk)
    (by rw [hdi2, ch2 hP (hP.ca n (Nat.le_refl n)).1]; exact hP.nd)
    (fun k hk => by rw [hdi2]; exact (hP.ca k hk).2)
    (fun _ => by rw [hsi2]; exact fw_at hP (d := 8) (by rw [tF lo]; omega) (by decide)) ?_
    (by rw [hsp2]; exact fd_at hP (d := 0) (by rw [tFm8 lo]; omega) (by decide))
    (by rw [hsp2, tFm8 lo]; omega)
    (fun _ => by rw [hsi2, hsp2, tF lo, tFm8 lo]; omega) hin (j₂ := 47) (lt_len (by decide))
    (by rw [hsp2]; exact ra2 lo) ?_
  · unfold Stu.Sep
    intro _
    rw [hsi2, hdi2, tF lo]
    refine ⟨by omega, fun k hk => ?_⟩
    obtain ⟨a1, a2, -⟩ := (hP.ca k hk).1
    exact ⟨a1, by omega⟩
  intro V₃ hM Z t₃ hKZ hAZ hrZ hgZ
  obtain ⟨a, c', d, di, x, hgZ⟩ := hgZ
  obtain ⟨hFr3, hE3⟩ := mem3 hP hsi2 hdi2 hM
  have hR3 : Rk X.cpu.gpr Z.cpu.gpr := by
    rw [hgZ, hgY₂, hgY]
    exact ⟨rfl, rfl, by show fsp X.cpu.gpr - 8 + 8 = fsp X.cpu.gpr; exact BitVec.sub_add_cancel _ _,
      rfl, rfl, rfl, rfl⟩
  -- from 47 to the `ret`
  refine cfgAt (fun ℓ => (spAll prof fb ℓ).at c hfs hin) (fun ℓ m g _ V' => Inv X.cpu.gpr V fb n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr V fb j g V') (fun ℓ m g f V' h => vcAll hP ℓ m g f V' h) ?_ 4 47 hKZ hAZ hrZ
    (by show Inv X.cpu.gpr V fb n 47 4 Z.cpu.gpr V₃; unfold Inv; exact ⟨hR3, hFr3, Or.inl ⟨rfl, rfl, hE3⟩⟩)
  rintro j g fl V' hF Y₅ t₅ hKY₅ hAY₅ hrY₅ hgY₅ -
  have hF' : Fin X.cpu.gpr V fb j g V' := hF
  unfold Fin at hF'
  obtain ⟨rfl, hFr', hs, hb, hp, h12, h13, h14, h15, hax⟩ := hF'
  subst hgY₅
  have hsp5 : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hs, e3]
  refine c.s_ret hKY₅ hAY₅ hin (lt_len (by decide)) hrY₅ (ret_166 _)
    (by rw [hsp5]; exact fd_at hP (d := 48) (by omega) (by decide)) hin₂ h₂
    (by rw [hsp5, ra_rd hP hFr']; exact hra) ?_
  rintro Z₅ t₆ hKZ₅ hAZ₅ ⟨hrZ₅, hgZ₅⟩
  have hpr := pop_rd hP hFr'
  refine k V' Z₅ t₆ hKZ₅ hAZ₅ hrZ₅ ?_ (by rw [hgZ₅]; exact hax) (fr_out hP hFr')
  unfold Ret
  rw [hgZ₅]
  exact ⟨by show Y₅.cpu.gpr.rsp + 8 = _; rw [hsp5], by show Y₅.cpu.gpr.rbx = _; rw [hb, hpr.1],
    by show Y₅.cpu.gpr.rbp = _; rw [hp, hpr.2], h12, h13, h14, h15⟩

end FV7z.Pcs
