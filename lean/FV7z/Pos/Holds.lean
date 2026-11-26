import FV7z.Pos.Cuts
import FV7z.Pco.Holds
import FV7z.Osv.Holds
import FV7z.Start.Inv
import FV7z.Lemmas.CallReg
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.SysFutex
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCall
/-!
# `__pthread_once_slow` (PLAN.md §M, M1)

glibc 2.31's `__pthread_once_slow (once_control, init_routine)` at `0x5fee60` in `7zzs` (`nptl/pthread_once.c`;
`objdump -d`): three pushes and a frame of 48 bytes with the stack guard (`fs:0x28`) at `rsp + 40`; the control word
(`rdi`) read. Done (bit 2 set): to the check of the stack guard (49), `rax` = 0, the pops, `ret` (79). Not started
(0): `lock cmpxchg` (89) stores `__fork_generation | 1` (the word at `0x7a7f20`); then `_pthread_cleanup_push`
(`Pcp.pcp_ok`, the buffer the frame's first 32 bytes), the call of `init_routine` (`call *rbx` at 189),
`_pthread_cleanup_pop (&buf, 0)` (`Pco.pco_ok`), the word = 2 (201) and `futex (once_control, FUTEX_WAKE_PRIVATE,
INT_MAX)` (`Seg.s_fwake`, 229); back to the check. Cut points (`Pos/Cuts.lean`): the entry, 45, 49, 94, 168, 191,
201, 231.

- `fsp`, `cnr`, `pVf`, `pg1`: the frame, the stack guard read, the bytes and the registers after the prologue.
- `Pe`: what the entry needs; `Pq`: what the way through the init routine needs too.
- `Ot`: the bytes apart from the frame, the control word and the thread's `cleanup`; `Fk`: the stack guard's slot,
  the pushes and the return address as after the prologue.
- `IniR`: what `init_routine` does, as the caller assumes: from its entry with the return address at 191, it returns
  to 191 with the registers a call keeps (`Osv.Back`), the 80 bytes from its caller's frame and the stack guard kept.
- `pos_done`: the word done; `pos_init`: the word 0 and the init routine as `IniR` says; both to the return address
  with `rax` = 0 and the registers a call keeps (`Osv.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pos

/-! ## The instructions outside the blocks -/

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_79 : pret <+: pos.drop 79 := by decide +kernel
theorem ret_79 (feat : Features) : Dec feat pos 79 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 79) (k := 0) (pret_0 feat) w_79 (Nat.zero_le _)

/-- `lock cmpxchg [rbp], edx`. -/
def pcx : List Byte := [0xf0, 0x0f, 0xb1, 0x55, 0x00]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (lockCmpxchgB32 5 0 2 5) := by dec_rfl
theorem w_89 : pcx <+: pos.drop 89 := by decide +kernel
theorem cx_89 (feat : Features) : Dec feat pos 89 (lockCmpxchgB32 5 0 2 5) :=
  Dec.shift (j := 89) (k := 0) (pcx_0 feat) w_89 (Nat.zero_le _)

/-- The `call _pthread_cleanup_push`. -/
def pcp1 : List Byte := [0xe8, 0xc3, 0x00, 0x00, 0x00]
theorem pcp1_0 : ∀ feat, Dec feat pcp1 0 (FV7z.mk .call 64 [.rel 195] 5) := by dec_rfl
theorem w_184 : pcp1 <+: pos.drop 184 := by decide +kernel
theorem call_184 (feat : Features) : Dec feat pos 184 (FV7z.mk .call 64 [.rel 195] 5) :=
  Dec.shift (j := 184) (k := 0) (pcp1_0 feat) w_184 (Nat.zero_le _)

/-- The `call *rbx`: the init routine. -/
def pcr : List Byte := [0xff, 0xd3]
theorem pcr_0 : ∀ feat, Dec feat pcr 0 (FV7z.mk .call 64 [gr 64 3] 2) := by dec_rfl
theorem w_189 : pcr <+: pos.drop 189 := by decide +kernel
theorem callr_189 (feat : Features) : Dec feat pos 189 (FV7z.mk .call 64 [gr 64 3] 2) :=
  Dec.shift (j := 189) (k := 0) (pcr_0 feat) w_189 (Nat.zero_le _)

/-- The `call _pthread_cleanup_pop`. -/
def pco1 : List Byte := [0xe8, 0xe7, 0x00, 0x00, 0x00]
theorem pco1_0 : ∀ feat, Dec feat pco1 0 (FV7z.mk .call 64 [.rel 231] 5) := by dec_rfl
theorem w_196 : pco1 <+: pos.drop 196 := by decide +kernel
theorem call_196 (feat : Features) : Dec feat pos 196 (FV7z.mk .call 64 [.rel 231] 5) :=
  Dec.shift (j := 196) (k := 0) (pco1_0 feat) w_196 (Nat.zero_le _)

/-- The `syscall`: `futex`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_229 : psys <+: pos.drop 229 := by decide +kernel
theorem sys_229 (feat : Features) : Dec feat pos 229 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 229) (k := 0) (psys_0 feat) w_229 (Nat.zero_le _)

/-! ## The frame -/

/-- The frame: `rsp - 72` at the entry, after the three pushes and `sub rsp, 48`. -/
def fsp (g : Gprs) : Addr := g.rsp - 8 - 8 - 8 - 48#64

/-- The stack guard as the entry reads it, after the pushes. -/
def cnr (V : Addr → Byte) (g : Gprs) (fb : Addr) : BitVec 64 :=
  rdq(Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8), fb + 40#64)

/-- The bytes with `r12`, `rbp` and `rbx` pushed and the stack guard at `rsp - 32`. -/
def pVf (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)) (fsp g + 40#64) (toBytesLE (cnr V g fb) 8)

/-- The registers after the prologue and the read of the control word `w`. -/
def pg1 (g : Gprs) (w : BitVec 32) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 w
    rbx := g.rsi
    rsp := fsp g
    rbp := g.rdi
    r8 := BitVec.setWidth 64 1#32
    r9 := BitVec.setWidth 64 202#32 }

/-- `m` bytes at `a` within the address space, apart from the 80 below `rsp` and the return address, from the
control word and from the thread's `cleanup` (`fs:0x2f8`). -/
abbrev Ap (g : Gprs) (fb a : Addr) (m : Nat) : Prop :=
  a.toNat + m ≤ 2 ^ 64 ∧ (a.toNat + m ≤ g.rsp.toNat - 80 ∨ g.rsp.toNat + 8 ≤ a.toNat) ∧
    (a.toNat + m ≤ g.rdi.toNat ∨ g.rdi.toNat + 4 ≤ a.toNat) ∧
    (a.toNat + m ≤ (fb + 760#64).toNat ∨ (fb + 760#64).toNat + 8 ≤ a.toNat)

/-- An address apart from the frame, the control word and the thread's `cleanup`. -/
abbrev Oa (g : Gprs) (fb y : Addr) : Prop :=
  (y.toNat < g.rsp.toNat - 80 ∨ g.rsp.toNat + 8 ≤ y.toNat) ∧ (y.toNat < g.rdi.toNat ∨ g.rdi.toNat + 4 ≤ y.toNat) ∧
    (y.toNat < (fb + 760#64).toNat ∨ (fb + 760#64).toNat + 8 ≤ y.toNat)

/-- `V'` as `V` apart from the frame, the control word and the thread's `cleanup`. -/
def Ot (g : Gprs) (fb : Addr) (V V' : Addr → Byte) : Prop := ∀ y, Oa g fb y → V' y = V y

/-- The stack guard's slot, the pushes and the return address as after the prologue from `V₀`. -/
def Fk (V₀ : Addr → Byte) (g : Gprs) (fb : Addr) (V : Addr → Byte) : Prop :=
  ∀ y : Addr, g.rsp.toNat - 32 ≤ y.toNat → y.toNat < g.rsp.toNat + 8 → V y = pVf V₀ g fb y

/-- What the entry needs: the 80 bytes below `rsp` in what the run may store into, the return address with them in
the footprint; the stack guard in the footprint, apart from them; the control word (`rdi`) in both, apart from
them. -/
structure Pe (F : Footprint) (Wl : List Rgn) (fb : Addr) (g : Gprs) : Prop where
  lo : 80 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  fw : ∀ i < 80, Foot Wl (Addr.add (g.rsp - 80#64) i)
  fd : ∀ i < 88, Foot F.data (Addr.add (g.rsp - 80#64) i)
  cl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  ca : Ap g fb (fb + 40#64) 8
  ww : ∀ i < 4, Foot Wl (Addr.add g.rdi i)
  wd : ∀ i < 4, Foot F.data (Addr.add g.rdi i)
  wb : g.rdi.toNat + 4 ≤ 2 ^ 64
  wf : g.rdi.toNat + 4 ≤ g.rsp.toNat - 80 ∨ g.rsp.toNat + 8 ≤ g.rdi.toNat

/-- What the way through the init routine needs too: the control word aligned, `__fork_generation` in the
footprint, the thread's `cleanup` in both, apart from the frame. -/
structure Pq (F : Footprint) (Wl : List Rgn) (fb : Addr) (g : Gprs) : Prop where
  al : g.rdi.toNat % 4 = 0
  gn : ∀ i < 4, Foot F.data (Addr.add 8027680#64 i)
  tr : ∀ i < 8, Foot F.data ((fb + 760#64).add i)
  tw : ∀ i < 8, Foot Wl ((fb + 760#64).add i)
  tb : (fb + 760#64).toNat + 8 ≤ 2 ^ 64
  tf : (fb + 760#64).toNat + 8 ≤ g.rsp.toNat - 80 ∨ g.rsp.toNat + 8 ≤ (fb + 760#64).toNat

variable {F : Footprint} {Wl : List Rgn} {fb : Addr} {g g₀ : Gprs} {V V₀ W W' : Addr → Byte} {f : Rflags}

theorem tS8 (lo : 80 ≤ g.rsp.toNat) : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tS16 (lo : 80 ≤ g.rsp.toNat) : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tS24 (lo : 80 ≤ g.rsp.toNat) : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF (lo : 80 ≤ g.rsp.toNat) : (fsp g).toNat = g.rsp.toNat - 72 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF8 (lo : 80 ≤ g.rsp.toNat) : (fsp g + 8#64).toNat = g.rsp.toNat - 64 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF24 (lo : 80 ≤ g.rsp.toNat) : (fsp g + 24#64).toNat = g.rsp.toNat - 48 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tF40 (lo : 80 ≤ g.rsp.toNat) : (fsp g + 40#64).toNat = g.rsp.toNat - 32 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem tFm8 (lo : 80 ≤ g.rsp.toNat) : (fsp g - 8).toNat = g.rsp.toNat - 80 := by
  have := g.rsp.isLt
  simp only [fsp, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

theorem t80 (lo : 80 ≤ g.rsp.toNat) : (g.rsp - 80#64).toNat = g.rsp.toNat - 80 := by
  have := g.rsp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The `pop`s' slots. -/
theorem e24' (g : Gprs) : fsp g + 48#64 = g.rsp - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem e16' (g : Gprs) : fsp g + 48#64 + 8 = g.rsp - 8 - 8 := by rw [e24']; exact BitVec.sub_add_cancel _ _
theorem e8' (g : Gprs) : fsp g + 48#64 + 8 + 8 = g.rsp - 8 := by rw [e16']; exact BitVec.sub_add_cancel _ _
theorem e0' (g : Gprs) : fsp g + 48#64 + 8 + 8 + 8 = g.rsp := by rw [e8']; exact BitVec.sub_add_cancel _ _

/-- An address of the 88 bytes from `rsp - 80`. -/
theorem at80 (hP : Pe F Wl fb g) {x : Addr} {d : Nat} (hd : d < 88) (hx : x.toNat = g.rsp.toNat - 80 + d) :
    x = Addr.add (g.rsp - 80#64) d := by
  have lo := hP.lo
  have hi := hP.hi
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_add_of_fits (a := g.rsp - 80#64) (n := 88) hd (by rw [t80 lo]; omega), t80 lo]

theorem fd_at (hP : Pe F Wl fb g) {x : Addr} {d m : Nat} (hx : x.toNat = g.rsp.toNat - 80 + d)
    (hdm : d + m ≤ 88) : ∀ i < m, Foot F.data (Addr.add x i) := fun i hi => by
  rw [at80 hP (d := d) (by omega) hx, addr_add_add']
  exact hP.fd (d + i) (by omega)

theorem fw_at (hP : Pe F Wl fb g) {x : Addr} {d m : Nat} (hx : x.toNat = g.rsp.toNat - 80 + d)
    (hdm : d + m ≤ 80) : ∀ i < m, Foot Wl (Addr.add x i) := fun i hi => by
  rw [at80 hP (d := d) (by omega) hx, addr_add_add']
  exact hP.fw (d + i) (by omega)

/-! ## The bytes -/

theorem pVf_out (lo : 80 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64) {y : Addr}
    (h : y.toNat < g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ y.toNat) : pVf V g fb y = V y := by
  have := g.rsp.isLt
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tS24 lo
  have a4 := tF40 lo
  unfold pVf
  rw [Tun.Vst_out _ (fsp g + 40#64) (toBytesLE (cnr V g fb) 8) y ?a1 ?a2,
    Tun.Vst_out _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) y ?b1 ?b2,
    Tun.Vst_out _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) y ?c1 ?c2,
    Tun.Vst_out V (g.rsp - 8) (toBytesLE g.r12 8) y ?d1 ?d2]
  all_goals (try simp only [toBytesLE_length, a1, a2, a3, a4])
  all_goals omega

/-- Bytes apart from the pushes and the stack guard's slot. -/
theorem rd_pvf (lo : 80 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64) {a : Addr} {m : Nat}
    (h : a.toNat + m ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ a.toNat) (ha : a.toNat + m ≤ 2 ^ 64) :
    List.map (pVf V g fb) (byteAddrs a m) = List.map V (byteAddrs a m) :=
  Start.rd_congr fun i hi' => pVf_out lo hi (by have := toNat_add_of_fits (a := a) hi' ha; omega)

/-- The control word after the prologue. -/
theorem rdi_pvf (hP : Pe F Wl fb g) : rdd(pVf V g fb, g.rdi) = rdd(V, g.rdi) :=
  congrArg (ofBytesLE 32) (rd_pvf hP.lo hP.hi (by have := hP.wf; omega) hP.wb)

/-- The stack guard after the prologue. -/
theorem cv_pvf (hP : Pe F Wl fb g) : rdq(pVf V g fb, fb + 40#64) = rdq(V, fb + 40#64) :=
  congrArg (ofBytesLE 64) (rd_pvf hP.lo hP.hi (by have := hP.ca.2.1; omega) hP.ca.1)

/-- The stack guard read at the entry. -/
theorem cnr_eq (lo : 80 ≤ g.rsp.toNat) (hc : Ap g fb (fb + 40#64) 8) : cnr V g fb = rdq(V, fb + 40#64) := by
  have := g.rsp.isLt
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tS24 lo
  obtain ⟨c1, c2, -, -⟩ := hc
  unfold cnr
  rw [Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (fb + 40#64) 8 ?a1 c1 ?a3,
    Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) (fb + 40#64) 8 ?b1 c1 ?b3,
    Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.r12 8) (fb + 40#64) 8 ?c1 c1 ?c3]
  all_goals (try simp only [toBytesLE_length, a1, a2, a3])
  all_goals omega

/-- Bytes from `rsp - 32` up to the return address. -/
theorem rd_fk (hP : Pe F Wl fb g) (hF : Fk V₀ g fb V) {a : Addr} (h1 : g.rsp.toNat - 32 ≤ a.toNat)
    (h2 : a.toNat ≤ g.rsp.toNat) : List.map V (byteAddrs a 8) = List.map (pVf V₀ g fb) (byteAddrs a 8) :=
  Start.rd_congr fun i hi => by
    have hi' := hP.hi
    have e := toNat_add_of_fits (a := a) hi (by omega)
    exact hF _ (by omega) (by omega)

/-- What the `pop`s read. -/
theorem pop_rd (hP : Pe F Wl fb g) (hF : Fk V₀ g fb V) :
    rdq(V, fsp g + 48#64) = g.rbx ∧ rdq(V, fsp g + 48#64 + 8) = g.rbp ∧ rdq(V, fsp g + 48#64 + 8 + 8) = g.r12 := by
  have lo := hP.lo
  have hi := hP.hi
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tS24 lo
  have a4 := tF40 lo
  rw [e8', e16', e24', rd_fk hP hF (a := g.rsp - 8 - 8 - 8) (by omega) (by omega),
    rd_fk hP hF (a := g.rsp - 8 - 8) (by omega) (by omega), rd_fk hP hF (a := g.rsp - 8) (by omega) (by omega)]
  unfold pVf
  refine ⟨?_, ?_, ?_⟩
  · rw [Tun.rd_Vst _ (fsp g + 40#64) (toBytesLE (cnr V₀ g fb) 8) (g.rsp - 8 - 8 - 8) 8 ?a1 ?a2 ?a3,
      Tun.rd_Vst_self _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (toBytesLE_length _ _) ?a4,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, a3, a4])
    all_goals omega
  · rw [Tun.rd_Vst _ (fsp g + 40#64) (toBytesLE (cnr V₀ g fb) 8) (g.rsp - 8 - 8) 8 ?b1 ?b2 ?b3,
      Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (g.rsp - 8 - 8) 8 ?c1 ?c2 ?c3,
      Tun.rd_Vst_self _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) (toBytesLE_length _ _) ?c4,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, a2, a3, a4])
    all_goals omega
  · rw [Tun.rd_Vst _ (fsp g + 40#64) (toBytesLE (cnr V₀ g fb) 8) (g.rsp - 8) 8 ?d1 ?d2 ?d3,
      Tun.rd_Vst _ (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8) (g.rsp - 8) 8 ?e1 ?e2 ?e3,
      Tun.rd_Vst _ (g.rsp - 8 - 8) (toBytesLE g.rbp 8) (g.rsp - 8) 8 ?f1 ?f2 ?f3,
      Tun.rd_Vst_self _ (g.rsp - 8) (toBytesLE g.r12 8) (toBytesLE_length _ _) ?f4,
      ofBytesLE_toBytesLE (n := 8) rfl]
    all_goals (try simp only [toBytesLE_length, a1, a2, a3, a4])
    all_goals omega

/-! ## Stores apart from the stack guard's slot and the pushes (`Fk`), and from what `Ot` keeps -/

theorem fk_refl : Fk V g fb (pVf V g fb) := fun _ _ _ => rfl

theorem fk_st (h : Fk V₀ g fb W) {a : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) (hs : a.toNat + n ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat + 8 ≤ a.toNat) :
    Fk V₀ g fb (Vst W a bs) := fun y h1 h2 => by
  rw [Tun.Vst_out W a bs y (by rw [hn]; exact ha) (by rw [hn]; omega)]
  exact h y h1 h2

/-- The four stores of `_pthread_cleanup_push` into the frame's buffer and the thread's `cleanup`. -/
theorem fk_v4 {G : Gprs} (hP : Pe F Wl fb g) (hQ : Pq F Wl fb g) (hdi : G.rdi = fsp g) (h : Fk V₀ g fb W) :
    Fk V₀ g fb (Pcp.V4 fb G W) := by
  have lo := hP.lo
  have hi := hP.hi
  have a0 := tF lo
  have a8 := tF8 lo
  have a24 := tF24 lo
  have tf := hQ.tf
  exact fk_st (fk_st (fk_st (fk_st h (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega))
    (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega))
    (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega)) (toBytesLE_length _ _) hQ.tb (by omega)

/-- The 80 bytes from the frame kept. -/
theorem fk_fr (hP : Pe F Wl fb g) (hF : Fk V₀ g fb W)
    (hfr : ∀ i < 80, W' (Addr.add (fsp g) i) = W (Addr.add (fsp g) i)) : Fk V₀ g fb W' := by
  intro y h1 h2
  have lo := hP.lo
  have hi := hP.hi
  have a0 := tF lo
  have e : Addr.add (fsp g) (y.toNat - (g.rsp.toNat - 72)) = y := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_of_fits (a := fsp g) (i := y.toNat - (g.rsp.toNat - 72)) (n := 80) (by omega) (by omega), a0]
    omega
  have := hfr (y.toNat - (g.rsp.toNat - 72)) (by omega)
  rw [e] at this
  rw [this]
  exact hF y h1 h2

theorem ot_refl : Ot g fb V V := fun _ _ => rfl

theorem ot_st (h : Ot g fb V W) {a : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 2 ^ 64) (hin : ∀ y : Addr, a.toNat ≤ y.toNat → y.toNat < a.toNat + n → ¬ Oa g fb y) :
    Ot g fb V (Vst W a bs) := by
  intro y hy
  rcases Nat.lt_or_ge y.toNat a.toNat with h1 | h1
  · rw [Tun.Vst_out W a bs y (by rw [hn]; exact ha) (Or.inl h1)]
    exact h y hy
  · rcases Nat.lt_or_ge y.toNat (a.toNat + n) with h2 | h2
    · exact absurd hy (hin y h1 h2)
    · rw [Tun.Vst_out W a bs y (by rw [hn]; exact ha) (Or.inr (by rw [hn]; exact h2))]
      exact h y hy

/-- A store into the frame. -/
theorem ot_fr (h : Ot g fb V W) (lo : 80 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64) {a : Addr}
    {bs : List Byte} {n : Nat} (hn : bs.length = n) (h1 : g.rsp.toNat - 80 ≤ a.toNat)
    (h2 : a.toNat + n ≤ g.rsp.toNat + 8) : Ot g fb V (Vst W a bs) :=
  ot_st h hn (by omega) fun y hy1 hy2 ho => by
    obtain ⟨o1, -, -⟩ := ho
    omega

/-- A store into the control word. -/
theorem ot_di (h : Ot g fb V W) {bs : List Byte} (hn : bs.length = 4) (wb : g.rdi.toNat + 4 ≤ 2 ^ 64) :
    Ot g fb V (Vst W g.rdi bs) :=
  ot_st h hn wb fun y hy1 hy2 ho => by
    obtain ⟨-, o2, -⟩ := ho
    omega

/-- A store into the thread's `cleanup`. -/
theorem ot_t (h : Ot g fb V W) {bs : List Byte} (hn : bs.length = 8) (tb : (fb + 760#64).toNat + 8 ≤ 2 ^ 64) :
    Ot g fb V (Vst W (fb + 760#64) bs) :=
  ot_st h hn tb fun y hy1 hy2 ho => by
    obtain ⟨-, -, o3⟩ := ho
    omega

theorem ot_pvf (lo : 80 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64) : Ot g fb V (pVf V g fb) :=
  fun y ho => pVf_out lo hi (by obtain ⟨o1, -, -⟩ := ho; omega)

theorem ot_v4 {G : Gprs} (lo : 80 ≤ g.rsp.toNat) (hi : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (tb : (fb + 760#64).toNat + 8 ≤ 2 ^ 64) (hdi : G.rdi = fsp g) (h : Ot g fb V W) :
    Ot g fb V (Pcp.V4 fb G W) := by
  have a0 := tF lo
  have a8 := tF8 lo
  have a24 := tF24 lo
  exact ot_t (ot_fr (ot_fr (ot_fr h lo hi (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega))
    lo hi (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega))
    lo hi (toBytesLE_length _ _) (by rw [hdi]; omega) (by rw [hdi]; omega)) (toBytesLE_length _ _) tb

/-- The stack guard, apart from what `Ot` lets change. -/
theorem cv_ot (ca : Ap g fb (fb + 40#64) 8) (h : Ot g fb V V') : rdq(V', fb + 40#64) = rdq(V, fb + 40#64) :=
  congrArg (ofBytesLE 64) (Start.rd_congr fun i hi => h _ (by
    obtain ⟨c1, c2, c3, c4⟩ := ca
    have := toNat_add_of_fits (a := fb + 40#64) hi c1
    exact ⟨by omega, by omega, by omega⟩))

/-! ## Register facts -/

theorem sw8 (w : BitVec 32) : BitVec.setWidth 8 (BitVec.setWidth 64 w) = BitVec.setWidth 8 w :=
  BitVec.setWidth_setWidth_of_le w (by decide)

theorem sw32 (w : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 w) = w :=
  (BitVec.setWidth_setWidth_of_le w (by decide)).trans (BitVec.setWidth_eq w)

/-- `xor esi, esi`. -/
theorem sx0 (x : BitVec 64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x)) = 0#32 := by
  rw [BitVec.xor_self]
  decide

/-- `or edx, 1`: not 0. -/
theorem or1_ne (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 (x ||| 1#32)) ≠ 0#32 := by
  rw [sw32]
  intro h
  have h1 : (x ||| 1#32).getLsbD 0 = (0#32).getLsbD 0 := congrArg (fun v : BitVec 32 => v.getLsbD 0) h
  rw [BitVec.getLsbD_or] at h1
  have h2 : (1#32).getLsbD 0 = true := by decide
  rw [h2, Bool.or_true] at h1
  exact absurd h1 (by decide)

/-- The registers the init routine's caller keeps: `rbx` the routine, `rbp` the control word, `r13`–`r15`. -/
abbrev Pk (g₀ g : Gprs) : Prop :=
  g.rbx = g₀.rsi ∧ g.rbp = g₀.rdi ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- `rsp` and `r13`–`r15` kept. -/
abbrev Kp (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-! ## The cut points -/

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to 45: the pushes, the frame, the stack guard stored, the control word read. -/
theorem vc_0 (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (fsp g + 40#64) i)) (h5 : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 45 ∧ g' = pg1 g rdd(pVf V g fb, g.rdi) ∧ V' = pVf V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [fsp] at h1 h2 h3 h4 h5
  wpx [W_0, W_42, o0, o1, Op.ldf]
  all_goals vc_fin

/-- 45, the word done (bit 2 set): to 49. -/
theorem vc_45d (hb : (BitVec.setWidth 8 g.rax &&& 2#8 == 0) = false) :
    W_45 fb F Wl (fun j' g' _ V' => j' = 49 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb
  wpx [W_45, hb]
  all_goals vc_fin

/-- 45, the word not done: `__fork_generation | 1` into `edx`, to the `lock cmpxchg` at 89. -/
theorem vc_45i (hb : (BitVec.setWidth 8 g.rax &&& 2#8 == 0) = true)
    (hg : ∀ i < 4, Foot F.data (Addr.add 8027680#64 i)) :
    W_45 fb F Wl (fun j' g' _ V' => j' = 89 ∧
      (∃ x : BitVec 32, g' = { g with rdx := BitVec.setWidth 64 (x ||| 1#32) }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb
  wpx [W_45, W_80, o2, o5, Op.lda, hb]
  all_goals repeat' (first | rfl | assumption | exact ⟨_, rfl⟩ | (intro h; exact absurd h (by decide)) |
    constructor | intro _)

/-- 94, after the `lock cmpxchg` stored: to 168. -/
theorem vc_94 (hz : f.zf = true) (hax : BitVec.setWidth 32 g.rax = 0#32) (hdx : BitVec.setWidth 32 g.rdx ≠ 0#32) :
    W_94 fb F Wl (fun j' g' _ V' => j' = 168 ∧ g' = g ∧ V' = V) g f V := by
  have hq : decide (BitVec.setWidth 32 g.rdx = BitVec.setWidth 32 g.rax) = false :=
    decide_eq_false fun h => hdx (h.trans hax)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq
  wpx [W_94, W_96, o6, hz, hq]
  all_goals vc_fin

/-- 168: the arguments of `_pthread_cleanup_push (&buf, clear_once_control, once_control)`, to its call. -/
theorem vc_168 : W_168 fb F Wl (fun j' g' _ V' => j' = 184 ∧
    g' = { g with rdx := g.rbp, rsi := 6287216#64, rdi := g.rsp, r12 := g.rsp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_168, o9]
  all_goals vc_fin

/-- 191: the arguments of `_pthread_cleanup_pop (&buf, 0)`, to its call. -/
theorem vc_191 : W_191 fb F Wl (fun j' g' _ V' => j' = 196 ∧ g' = { g with
    rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi ^^^ BitVec.setWidth 32 g.rsi), rdi := g.r12 } ∧ V' = V)
    g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_191, o10]
  all_goals vc_fin

/-- 201: the word = 2, the arguments of `futex (once_control, FUTEX_WAKE_PRIVATE, INT_MAX)`, to the `syscall`. -/
theorem vc_201 {a : Addr} (hp : g.rbp = a) (hw : ∀ i < 4, Foot Wl (Addr.add a i)) :
    W_201 fb F Wl (fun j' g' _ V' => j' = 229 ∧ g' = { g with
      rax := BitVec.setWidth 64 202#32, rdx := BitVec.setWidth 64 2147483647#32,
      rsi := BitVec.setWidth 64 129#32, rdi := a,
      r10 := BitVec.setWidth 64 (BitVec.setWidth 32 g.r10 ^^^ BitVec.setWidth 32 g.r10) } ∧
      V' = Vst V a (toBytesLE (2#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp
  subst hp
  wpx [W_201, o11]
  all_goals vc_fin

/-- 231, after the wake: 0, `-EINVAL` or `-EFAULT`, each to 49. -/
theorem vc_231 {feat : Features} {a : Addr} (hr : g.rax = fwR feat a) :
    W_231 fb F Wl (fun j' g' _ V' => j' = 49 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr
  rcases fwR_cases feat a with h | h | h <;> rw [h] at hr <;> subst hr <;>
    wpx [W_231, W_243, W_251, o12, o13] <;> vc_fin

set_option maxHeartbeats 1000000 in
/-- 49: the stack guard checked, the frame dropped, `rax` = 0, the pops, to the `ret`. -/
theorem vc_49 (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8) i))
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8) i)) :
    W_49 fb F Wl (fun j' g' _ V' => j' = 79 ∧ g' = { g with
      rax := 0, rbx := rdq(V, g.rsp + 48#64), rsp := g.rsp + 48#64 + 8 + 8 + 8,
      rbp := rdq(V, g.rsp + 48#64 + 8), r12 := rdq(V, g.rsp + 48#64 + 8 + 8) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f48 f56 f64
  wpx [W_49, W_69, o3, o4, Op.xormf, hc, BitVec.xor_self]
  all_goals vc_fin

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- From 49 with the frame of `g₀` and the bytes as `Fk` says: the stack guard checked, the pops, the `ret`, to the
return address with `rax` = 0 and the registers a call keeps. -/
theorem tl49 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pos_at pos)
    (hP : Pe F Wl fb g₀) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hr : X.cpu.rip = pos_at.add 49)
    (hsp : X.cpu.gpr.rsp = fsp g₀) (h13 : X.cpu.gpr.r13 = g₀.r13) (h14 : X.cpu.gpr.r14 = g₀.r14)
    (h15 : X.cpu.gpr.r15 = g₀.r15) (hF : Fk V₀ g₀ fb V) (hcv : rdq(V, fb + 40#64) = rdq(V₀, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₀, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = 0 → Osv.Back g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have lo := hP.lo
  have hi := hP.hi
  have a1 := tS8 lo
  have a2 := tS16 lo
  have a3 := tS24 lo
  have a40 := tF40 lo
  have hc : rdq(V, X.cpu.gpr.rsp + 40#64) = rdq(V, fb + 40#64) := by
    rw [hsp, rd_fk hP hF (a := fsp g₀ + 40#64) (by omega) (by omega), hcv, ← cnr_eq lo hP.ca]
    unfold pVf
    rw [Tun.rd_Vst_self _ (fsp g₀ + 40#64) (toBytesLE (cnr V₀ g₀ fb) 8) (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 40#64) i) := by
    rw [hsp]; exact fd_at hP (d := 48) (by omega) (by decide)
  have f48 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 48#64) i) := by
    rw [hsp, e24']; exact fd_at hP (d := 56) (by omega) (by decide)
  have f56 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 48#64 + 8) i) := by
    rw [hsp, e16']; exact fd_at hP (d := 64) (by omega) (by decide)
  have f64 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 48#64 + 8 + 8) i) := by
    rw [hsp, e8']; exact fd_at hP (d := 72) (by omega) (by decide)
  refine (c_49 prof fb).run c hfs hin _ hK hA hr (vc_49 hc f40 hP.cl f48 f56 f64) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hspY : Y.cpu.gpr.rsp = g₀.rsp := by
    rw [hgY]
    show X.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 = _
    rw [hsp, e0']
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_79 _)
    (by rw [hspY]; exact fd_at hP (d := 80) (by omega) (by decide)) hin₂ h₂
    (by rw [hspY, rd_fk hP hF (a := g₀.rsp) (by omega) (Nat.le_refl _), rd_pvf lo hi (Or.inr (Nat.le_refl _)) hi]
        exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  obtain ⟨p1, p2, p3⟩ := pop_rd hP hF
  have hsZ : Z.cpu.gpr.rsp = Y.cpu.gpr.rsp + 8 := by rw [hgZ]; try rfl
  refine k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY]; try rfl) ⟨by rw [hsZ, hspY]; try rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgZ, hgY]
    show rdq(V, X.cpu.gpr.rsp + 48#64) = _
    rw [hsp]
    exact p1
  · rw [hgZ, hgY]
    show rdq(V, X.cpu.gpr.rsp + 48#64 + 8) = _
    rw [hsp]
    exact p2
  · rw [hgZ, hgY]
    show rdq(V, X.cpu.gpr.rsp + 48#64 + 8 + 8) = _
    rw [hsp]
    exact p3
  · rw [hgZ, hgY]; exact h13
  · rw [hgZ, hgY]; exact h14
  · rw [hgZ, hgY]; exact h15

/-- `__pthread_once_slow (once_control, init_routine)` with the word done (bit 2 set): to the return address with
`rax` = 0, the registers a call keeps (`Osv.Back`), the bytes apart from the frame as before. -/
theorem pos_done (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pos_at pos)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pos_at) (hP : Pe F Wl fb X.cpu.gpr)
    (hb : (BitVec.setWidth 8 rdd(V, X.cpu.gpr.rdi) &&& 2#8 == 0) = false)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Ot X.cpu.gpr fb V V' → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 → Osv.Back X.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have lo := hP.lo
  have hi := hP.hi
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (fw_at hP (d := 72) (by have := tS8 lo; omega) (by decide))
      (fw_at hP (d := 64) (by have := tS16 lo; omega) (by decide))
      (fw_at hP (d := 56) (by have := tS24 lo; omega) (by decide)) hP.cl
      (fw_at hP (d := 48) (by have := tF40 lo; omega) (by decide)) hP.wd) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₀ t₀ hK₀ hA₀ hr₀ hg₀ -
  have hax0 : Y₀.cpu.gpr.rax = BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi) := by
    rw [hg₀]
    show BitVec.setWidth 64 rdd(pVf V X.cpu.gpr fb, X.cpu.gpr.rdi) = _
    rw [rdi_pvf hP]
  have hb' : (BitVec.setWidth 8 Y₀.cpu.gpr.rax &&& 2#8 == 0) = false := by rw [hax0, sw8]; exact hb
  refine (c_45 prof fb).run c hfs hin _ hK₀ hA₀ hr₀ (vc_45d hb') ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp1 : Y₁.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₁, hg₀]; try rfl
  have pk1 : Pk X.cpu.gpr Y₁.cpu.gpr := by rw [hg₁, hg₀]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine tl49 c hfs hin hP hK₁ hA₁ hr₁ hsp1 pk1.2.2.1 pk1.2.2.2.1 pk1.2.2.2.2 fk_refl (cv_pvf hP) hin₂ h₂ hra ?_
  intro Z t' hKZ hAZ hrZ hax hbk
  exact k _ Z t' hKZ hAZ (ot_pvf lo hi) hrZ hax hbk

/-- What the caller assumes of `init_routine` (at `fn`, called with the frame `fr`): from its entry with the
precondition `I` of the bytes and the return address at 191, it returns there with `J` of the bytes, the registers a
call keeps (`Osv.Back`), the caller's 80 bytes from `fr` and the stack guard as they were, after events `evs`. -/
def IniR (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (I J : (Addr → Byte) → Prop)
    (fb fr fn : Addr) : Prop :=
  ∀ (gev : List Event) (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → I V →
    X.cpu.rip = fn → X.cpu.gpr.rsp = fr - 8 → rdq(V, fr - 8) = pos_at.add 191 →
    (∀ (evs : List Event) (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      J V' → (∀ i < 80, V' (Addr.add fr i) = V (Addr.add fr i)) →
      (∀ i < 8, V' (Addr.add (fb + 40#64) i) = V (Addr.add (fb + 40#64) i)) → Z.cpu.rip = pos_at.add 191 →
      Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o (gev ++ evs) gP gE Z t') →
    GoG prof L o gev gP gE X t

set_option maxHeartbeats 1000000 in
/-- `__pthread_once_slow (once_control, init_routine)` with the word 0 and `init_routine` as `IniR` says: the word
set to 1 (with the fork generation), the cleanup buffer pushed, the routine, the buffer popped, the word = 2, the
wake; to the return address with `rax` = 0 and the registers a call keeps (`Osv.Back`). The bytes: `J` of them
after the routine, kept apart from the frame, the word and the thread's `cleanup`; the word 2. -/
theorem pos_init (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pos_at pos)
    (hinP : CodeIn L Pcp.pcp_at Pcp.pcp) (hinO : CodeIn L Pco.pco_at Pco.pco) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pos_at) (hP : Pe F Wl fb X.cpu.gpr)
    (hQ : Pq F Wl fb X.cpu.gpr) (hw0 : rdd(V, X.cpu.gpr.rdi) = 0#32)
    {codeI : List Byte} (hinI : CodeIn L X.cpu.gpr.rsi codeI) (hI0 : 0 < codeI.length)
    {I J : (Addr → Byte) → Prop} (hI : ∀ V', Ot X.cpu.gpr fb V V' → I V')
    (hJo : ∀ W W', J W → Ot X.cpu.gpr fb W W' → J W')
    (hfn : IniR prof F Wl L s₀ o gP gE I J fb (fsp X.cpu.gpr) X.cpu.gpr.rsi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (evs : List Event) (gw : Gprs) (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → J V' → rdd(V', X.cpu.gpr.rdi) = 2#32 → gw.rax = BitVec.setWidth 64 202#32 →
      gw.rdi = X.cpu.gpr.rdi → gw.rsi = BitVec.setWidth 64 129#32 →
      gw.rdx = BitVec.setWidth 64 2147483647#32 → gw.r10 = 0 → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = 0 →
      Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o ((gev ++ evs) ++ [fwEv prof.feat gw]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have lo := hP.lo
  have hi := hP.hi
  have aF := tF lo
  have aM := tFm8 lo
  have wf := hP.wf
  have tf := hQ.tf
  -- the prologue and the read of the word
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (fw_at hP (d := 72) (by have := tS8 lo; omega) (by decide))
      (fw_at hP (d := 64) (by have := tS16 lo; omega) (by decide))
      (fw_at hP (d := 56) (by have := tS24 lo; omega) (by decide)) hP.cl
      (fw_at hP (d := 48) (by have := tF40 lo; omega) (by decide)) hP.wd) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₀ t₀ hK₀ hA₀ hr₀ hg₀ -
  have hw1 : rdd(pVf V X.cpu.gpr fb, X.cpu.gpr.rdi) = 0#32 := (rdi_pvf hP).trans hw0
  have hax0 : Y₀.cpu.gpr.rax = BitVec.setWidth 64 0#32 := by
    rw [hg₀]
    show BitVec.setWidth 64 rdd(pVf V X.cpu.gpr fb, X.cpu.gpr.rdi) = _
    rw [hw1]
  have hsp0 : Y₀.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₀]; try rfl
  have pk0 : Pk X.cpu.gpr Y₀.cpu.gpr := by rw [hg₀]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- 45: not done
  refine (c_45 prof fb).run c hfs hin _ hK₀ hA₀ hr₀ (vc_45i (by rw [hax0]; decide) hQ.gn) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨x, rfl⟩, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hax1 : Y₁.cpu.gpr.rax = BitVec.setWidth 64 0#32 := by rw [hg₁]; exact hax0
  have hsp1 : Y₁.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₁]; exact hsp0
  have pk1 : Pk X.cpu.gpr Y₁.cpu.gpr := by rw [hg₁]; exact pk0
  have e0 : eaD Y₁ 5 0 = X.cpu.gpr.rdi := by
    show Y₁.cpu.gpr.rbp + 0 = _
    rw [BitVec.add_zero]
    exact pk1.2.1
  -- 89: `lock cmpxchg [rbp], edx`, the word 0
  refine c.s_lock_cmpxchg_bd32 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (cx_89 _)
    (by rw [e0]; have := hQ.al; omega) (by rw [e0]; exact hP.ww)
    (by
      rw [e0, hw1]
      show (0#32) = BitVec.setWidth 32 Y₁.cpu.gpr.rax
      rw [hax1]
      try decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hz₂⟩
  rw [e0] at hA₂
  -- 94: stored, to 168
  refine (c_94 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
    (vc_94 hz₂ (by rw [hg₂, hax1]; try decide) (by rw [hg₂, hg₁]; exact or1_ne x)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hsp3 : Y₃.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₃, hg₂]; exact hsp1
  have pk3 : Pk X.cpu.gpr Y₃.cpu.gpr := by rw [hg₃, hg₂]; exact pk1
  -- 168
  refine (c_168 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ vc_168 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hsp4 : Y₄.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₄]; exact hsp3
  have pk4 : Pk X.cpu.gpr Y₄.cpu.gpr := by rw [hg₄]; exact pk3
  have hq4 : Y₄.cpu.gpr.r12 = fsp X.cpu.gpr := by rw [hg₄]; exact hsp3
  -- 184: `call _pthread_cleanup_push`
  refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_184 _) hinP (Pcp.lt_len (by decide)) (by decide)
    (by rw [hsp4]; exact fw_at hP (d := 0) (by omega) (by decide)) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [hsp4] at hA₅
  obtain ⟨M2, hA₅', hO2, hF2, hra2⟩ : ∃ M, Agree F Y₅.proc.mm.mem M ∧ Ot X.cpu.gpr fb V M ∧
      Fk V X.cpu.gpr fb M ∧ rdq(M, fsp X.cpu.gpr - 8) = pos_at.add 189 :=
    ⟨_, hA₅, ot_fr (ot_di (ot_pvf lo hi) (toBytesLE_length _ _) hP.wb) lo hi (toBytesLE_length _ _) (by omega)
        (by omega),
      fk_st (fk_st fk_refl (toBytesLE_length _ _) hP.wb (by omega)) (toBytesLE_length _ _) (by omega)
        (Or.inl (by omega)),
      by
        rw [Tun.rd_Vst_self _ (fsp X.cpu.gpr - 8) (toBytesLE (pos_at.add (184 + 5)) 8) (toBytesLE_length _ _)
          (by omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _⟩
  have hsp5 : Y₅.cpu.gpr.rsp = fsp X.cpu.gpr - 8 := by rw [hg₅]; exact congrArg (· - 8) hsp4
  have hdi5 : Y₅.cpu.gpr.rdi = fsp X.cpu.gpr := by rw [hg₅, hg₄]; exact hsp3
  have pk5 : Pk X.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact pk4
  have hq5 : Y₅.cpu.gpr.r12 = fsp X.cpu.gpr := by rw [hg₅]; exact hq4
  -- `_pthread_cleanup_push (&buf, clear_once_control, once_control)`
  refine Pcp.pcp_ok c hfs hinP hK₅ hA₅' hr₅ (by rw [hdi5]; exact fw_at hP (d := 8) (by omega) (by decide))
    hQ.tr hQ.tw (by rw [hdi5]; omega) (by rw [hdi5, hsp5]; omega) hQ.tb (by rw [hsp5]; omega)
    (by rw [hsp5]; exact fd_at hP (d := 0) (by omega) (by decide)) (by rw [hsp5]; omega) hin (j₂ := 189)
    (lt_len (by decide)) (by rw [hsp5]; exact hra2) ?_
  intro Z₆ t₆ hK₆ hA₆ hr₆ hg₆
  have hsp6 : Z₆.cpu.gpr.rsp = fsp X.cpu.gpr := by
    rw [hg₆]
    show Y₅.cpu.gpr.rsp + 8 = _
    rw [hsp5]
    exact BitVec.sub_add_cancel _ _
  have pk6 : Pk X.cpu.gpr Z₆.cpu.gpr := by rw [hg₆]; exact pk5
  have hq6 : Z₆.cpu.gpr.r12 = fsp X.cpu.gpr := by rw [hg₆]; exact hq5
  -- 189: `call *rbx`, the init routine
  refine c.s_callr hK₆ hA₆ hin (lt_len (by decide)) hr₆ (callr_189 _) hinI hI0 pk6.1
    (by rw [hsp6]; exact fw_at hP (d := 0) (by omega) (by decide)) ?_
  rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
  rw [hsp6] at hA₇
  obtain ⟨M4, hA₇', hO4, hF4, hra4⟩ : ∃ M, Agree F Y₇.proc.mm.mem M ∧ Ot X.cpu.gpr fb V M ∧
      Fk V X.cpu.gpr fb M ∧ rdq(M, fsp X.cpu.gpr - 8) = pos_at.add 191 :=
    ⟨_, hA₇, ot_fr (ot_v4 lo hi hQ.tb hdi5 hO2) lo hi (toBytesLE_length _ _) (by omega) (by omega),
      fk_st (fk_v4 hP hQ hdi5 hF2) (toBytesLE_length _ _) (by omega) (Or.inl (by omega)),
      by
        rw [Tun.rd_Vst_self _ (fsp X.cpu.gpr - 8) (toBytesLE (pos_at.add (189 + 2)) 8) (toBytesLE_length _ _)
          (by omega)]
        exact ofBytesLE_toBytesLE (n := 8) rfl _⟩
  have hsp7 : Y₇.cpu.gpr.rsp = fsp X.cpu.gpr - 8 := by rw [hg₇]; exact congrArg (· - 8) hsp6
  have pk7 : Pk X.cpu.gpr Y₇.cpu.gpr := by rw [hg₇]; exact pk6
  have hq7 : Y₇.cpu.gpr.r12 = fsp X.cpu.gpr := by rw [hg₇]; exact hq6
  refine hfn gev Y₇ t₇ M4 hK₇ hA₇' (hI M4 hO4) hr₇ hsp7 hra4 ?_
  intro evs Z₈ t₈ V₅ hK₈ hA₈ hJ₈ hfr₈ hcn₈ hr₈ hb₈
  have hF5 : Fk V X.cpu.gpr fb V₅ := fk_fr hP hF4 hfr₈
  have hc5 : rdq(V₅, fb + 40#64) = rdq(V, fb + 40#64) :=
    (congrArg (ofBytesLE 64) (Start.rd_congr hcn₈)).trans (cv_ot hP.ca hO4)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb₈
  have hsp8 : Z₈.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [b1, hsp7]; exact BitVec.sub_add_cancel _ _
  have pk8 : Pk X.cpu.gpr Z₈.cpu.gpr :=
    ⟨b2.trans pk7.1, b3.trans pk7.2.1, b5.trans pk7.2.2.1, b6.trans pk7.2.2.2.1, b7.trans pk7.2.2.2.2⟩
  have hq8 : Z₈.cpu.gpr.r12 = fsp X.cpu.gpr := b4.trans hq7
  -- 191
  refine (c_191 prof fb).run c hfs hin _ hK₈ hA₈ hr₈ vc_191 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  have hsp9 : Y₉.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₉]; exact hsp8
  have pk9 : Pk X.cpu.gpr Y₉.cpu.gpr := by rw [hg₉]; exact pk8
  -- 196: `call _pthread_cleanup_pop`
  refine c.s_call hK₉ hA₉ hin (lt_len (by decide)) hr₉ (call_196 _) hinO (Pco.lt_len (by decide)) (by decide)
    (by rw [hsp9]; exact fw_at hP (d := 0) (by omega) (by decide)) ?_
  rintro Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀⟩
  rw [hsp9] at hA₁₀
  have hsp10 : Y₁₀.cpu.gpr.rsp = fsp X.cpu.gpr - 8 := by rw [hg₁₀]; exact congrArg (· - 8) hsp9
  have hdi10 : Y₁₀.cpu.gpr.rdi = fsp X.cpu.gpr := by rw [hg₁₀, hg₉]; exact hq8
  have hz10 : BitVec.setWidth 32 Y₁₀.cpu.gpr.rsi = 0#32 := by rw [hg₁₀, hg₉]; exact sx0 Z₈.cpu.gpr.rsi
  have pk10 : Pk X.cpu.gpr Y₁₀.cpu.gpr := by rw [hg₁₀]; exact pk9
  -- `_pthread_cleanup_pop (&buf, 0)`
  refine Pco.pco_ok c hfs hinO hK₁₀ hA₁₀ hr₁₀ (by rw [hdi10]; exact fd_at hP (d := 8) (by omega) (by decide))
    hQ.tw hQ.tb (by rw [hsp10]; omega) (by rw [hsp10]; exact fd_at hP (d := 0) (by omega) (by decide))
    (by rw [hsp10]; omega) hin (j₂ := 201) (lt_len (by decide))
    (by
      rw [hsp10, Tun.rd_Vst_self _ (fsp X.cpu.gpr - 8) (toBytesLE (pos_at.add (196 + 5)) 8) (toBytesLE_length _ _)
        (by omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _)
    (fun h => absurd hz10 h) ?_ (fun h => absurd hz10 h)
  intro _ Z₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ hg₁₁
  have hsp11 : Z₁₁.cpu.gpr.rsp = fsp X.cpu.gpr := by
    rw [hg₁₁]
    show Y₁₀.cpu.gpr.rsp + 8 = _
    rw [hsp10]
    exact BitVec.sub_add_cancel _ _
  have pk11 : Pk X.cpu.gpr Z₁₁.cpu.gpr := by rw [hg₁₁]; exact pk10
  -- 201: the word = 2
  refine (c_201 prof fb).run c hfs hin _ hK₁₁ hA₁₁ hr₁₁ (vc_201 pk11.2.1 hP.ww) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁₂ t₁₂ hK₁₂ hA₁₂ hr₁₂ hg₁₂ -
  have hsp12 : Y₁₂.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₁₂]; exact hsp11
  have pk12 : Pk X.cpu.gpr Y₁₂.cpu.gpr := by rw [hg₁₂]; exact pk11
  have hax12 : Y₁₂.cpu.gpr.rax = BitVec.setWidth 64 202#32 := by rw [hg₁₂]; try rfl
  have hdi12 : Y₁₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₁₂]; try rfl
  have hsi12 : Y₁₂.cpu.gpr.rsi = BitVec.setWidth 64 129#32 := by rw [hg₁₂]; try rfl
  have hdx12 : Y₁₂.cpu.gpr.rdx = BitVec.setWidth 64 2147483647#32 := by rw [hg₁₂]; try rfl
  have hr10 : Y₁₂.cpu.gpr.r10 = 0 := by rw [hg₁₂]; exact lf_xz _
  -- 229: `futex (once_control, FUTEX_WAKE_PRIVATE, INT_MAX)`
  refine c.s_fwake hK₁₂ hA₁₂ hin (lt_len (by decide)) hr₁₂ (sys_229 _) (by rw [hax12]; decide)
    (by rw [hsi12]; decide) ?_
  rintro Y₁₃ t₁₃ hK₁₃ hA₁₃ ⟨hr₁₃, hg₁₃⟩
  have hsp13 : Y₁₃.cpu.gpr.rsp = fsp X.cpu.gpr := by rw [hg₁₃]; exact hsp12
  have pk13 : Pk X.cpu.gpr Y₁₃.cpu.gpr := by rw [hg₁₃]; exact pk12
  -- 231: to 49
  refine (c_231 prof fb).run c hfs hin _ hK₁₃ hA₁₃ hr₁₃
    (vc_231 (feat := prof.feat) (a := Y₁₂.cpu.gpr.rdi) (by rw [hg₁₃]; try rfl)) ?_
  rintro j' g fl V₁ ⟨rfl, hkp, rfl⟩ Y₁₄ t₁₄ hK₁₄ hA₁₄ hr₁₄ rfl -
  obtain ⟨M8, hA8, hO8, hF8, hd8⟩ : ∃ M, Agree F Y₁₄.proc.mm.mem M ∧ Ot X.cpu.gpr fb V₅ M ∧
      Fk V X.cpu.gpr fb M ∧ rdd(M, X.cpu.gpr.rdi) = 2#32 :=
    ⟨_, hA₁₄,
      ot_di (ot_t (ot_fr ot_refl lo hi (toBytesLE_length _ _) (by omega) (by omega)) (toBytesLE_length _ _) hQ.tb)
        (toBytesLE_length _ _) hP.wb,
      fk_st (fk_st (fk_st hF5 (toBytesLE_length _ _) (by omega) (Or.inl (by omega))) (toBytesLE_length _ _) hQ.tb
        (by omega)) (toBytesLE_length _ _) hP.wb (by omega),
      by
        rw [Tun.rd_Vst_self _ X.cpu.gpr.rdi (toBytesLE (2#32) 4) (toBytesLE_length _ _) hP.wb]
        exact ofBytesLE_toBytesLE (n := 4) rfl _⟩
  -- 49: the check, the pops, the `ret`
  refine tl49 c hfs hin hP hK₁₄ hA8 hr₁₄ (hkp.1.trans hsp13) (hkp.2.1.trans pk13.2.2.1)
    (hkp.2.2.1.trans pk13.2.2.2.1) (hkp.2.2.2.trans pk13.2.2.2.2) hF8 ((cv_ot hP.ca hO8).trans hc5) hin₂ h₂ hra ?_
  intro Z t' hKZ hAZ hrZ hax hbk
  exact k evs Y₁₂.cpu.gpr M8 Z t' hKZ hAZ (hJo V₅ M8 hJ₈ hO8) hd8 hax12 hdi12 hsi12 hdx12 hr10 hrZ hax hbk

end FV7z.Pos
