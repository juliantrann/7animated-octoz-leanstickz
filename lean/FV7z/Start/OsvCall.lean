import FV7z.Start.Guard
import FV7z.Osv.Holds
import FV7z.Lemmas.Signed
/-!
# `__libc_start_main` reads the kernel's version (PLAN.md G3, startup)

glibc 2.31's `__libc_start_main` from the call of `_dl_discover_osversion` at `0x61363e` to `0x6133f0`: the version
is stored in `_dl_osversion` (`0x7a8520`), 0 before; a version below 3.2.0 (`__LINUX_KERNEL_VERSION`, `0x30200`) or
a negative number is `__libc_fatal ("FATAL: kernel too old\n")`.

The kernel's answer to `uname` is any `struct new_utsname` of the stream, so that this run does not go to
`__libc_fatal` is from an assumption on the stream: every answer has `KernelNew` (`Spec/OsVersion.lean`), as the
release of a Linux since 3.2 has.

- `OsvMem V g u`: the bytes after, from the registers `g` at the call and the kernel's answer `u`; `OsvMem_out`,
  `OsvMem_ver`.
- `vc_1539`, `vc_1561`, `vc_1567`: the verification conditions of the three pieces after the call.
- `lsb_osv`: the run from `0x61363e` to `0x6133f0`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.StartB

/-! ## The `call` -/

def pc1534 : List Byte := [0xe8, 0x0d, 0xe7, 0x05, 0x00]
theorem pc1534_0 : ∀ feat, Dec feat pc1534 0 (FV7z.mk .call 64 [.rel 386829] 5) := by dec_rfl
set_option maxRecDepth 100000 in
theorem wc1534 : pc1534 <+: lsm.drop 1534 := by decide +kernel
theorem call_1534 (feat : Features) : Dec feat lsm 1534 (FV7z.mk .call 64 [.rel 386829] 5) :=
  Dec.shift (j := 1534) (k := 0) (pc1534_0 feat) wc1534 (Nat.zero_le _)

/-! ## The bytes after -/

/-- The registers `_dl_discover_osversion` is called with, from those at the `call`. -/
abbrev callG (g : Gprs) : Gprs := g.set 4 (g.rsp - 8)

/-- The bytes after the stretch, from the registers `g` at the `call` and the kernel's answer `u`: the return
address, what `_dl_discover_osversion` leaves, `_dl_osversion`. -/
def OsvMem (V : Addr → Byte) (g : Gprs) (u : List Byte) : Addr → Byte :=
  Vst (Osv.frameV (Vst V (g.rsp - 8) (toBytesLE (lsm_at.add (1534 + 5)) 8)) (callG g) u) 8029472#64
    (toBytesLE (osVersion u) 4)

variable {V : Addr → Byte} {g : Gprs} {u : List Byte}

/-- A byte of `OsvMem`'s frame's memory outside the 504 bytes below the stack pointer. -/
theorem frame_out (hsp : 504 ≤ g.rsp.toNat) (hu : u.length = 390) {a : Addr}
    (h : ¬ (g.rsp.toNat ≤ a.toNat + 504 ∧ a.toNat < g.rsp.toNat)) :
    Osv.frameV (Vst V (g.rsp - 8) (toBytesLE (lsm_at.add (1534 + 5)) 8)) (callG g) u a = V a := by
  have h8 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bv_omega
  have e0 : Vst V (g.rsp - 8) (toBytesLE (lsm_at.add (1534 + 5)) 8) a = V a :=
    Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)
  have key : 496 ≤ (g.rsp - 8).toNat ∧ ¬ ((g.rsp - 8).toNat - 496 ≤ a.toNat ∧ a.toNat < (g.rsp - 8).toNat) := by
    refine ⟨by omega, fun ⟨h1, h2⟩ => h ⟨?_, ?_⟩⟩ <;> omega
  rw [Osv.frameV_out (g := callG g) key.1 hu key.2, e0]

/-- A byte outside the 504 bytes below the stack pointer and outside `_dl_osversion`. -/
theorem OsvMem_out (hsp : 504 ≤ g.rsp.toNat) (hu : u.length = 390) {a : Addr}
    (h : ¬ (g.rsp.toNat ≤ a.toNat + 504 ∧ a.toNat < g.rsp.toNat))
    (hv : ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476)) : OsvMem V g u a = V a := by
  unfold OsvMem
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length]; bv_omega), frame_out hsp hu h]

/-- `_dl_osversion` after. -/
theorem OsvMem_ver : rdd(OsvMem V g u, 8029472#64) = osVersion u := by
  unfold OsvMem
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by decide)]
  exact ofBytesLE_toBytesLE (n := 4) rfl _

/-! ## The pieces after the call -/

variable {F : Footprint} {Wl : List Rgn}

/-- The version is not negative, `_dl_osversion` is 0. -/
theorem vc_1539 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ver : BitVec 32}
    (hax : g.rax = BitVec.setWidth 64 ver) (hpos : ver.msb = false)
    (hr : ∀ i < 4, Foot F.data (Addr.add 8029472#64 i)) (h0 : rdd(V, 8029472#64) = 0) :
    W_1539 fb F Wl (fun j' g' _ V' => j' = 1561 ∧ g' = g.set 2 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = _ := hax
  wpx [W_1539, W_1547, W_1833, W_1841, o15, o16, o19, Op.lda]
  rw [h0, BitVec.and_self, hpos]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨hr, fun h => absurd h (by decide), fun _ => rfl⟩⟩

/-- The store of `_dl_osversion`. -/
theorem vc_1561 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ver : BitVec 32}
    (hax : g.rax = BitVec.setWidth 64 ver) (hw : ∀ i < 4, Foot Wl (Addr.add 8029472#64 i)) :
    W_1561 fb F Wl (fun j' g' _ V' => j' = 1567 ∧ g' = g ∧ V' = Vst V 8029472#64 (toBytesLE ver 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = _ := hax
  wpx [W_1561, o17, Op.sta]
  exact hw

/-- The version is above 3.1.255. -/
theorem vc_1567 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ver : BitVec 32}
    (hax : g.rax = BitVec.setWidth 64 ver) (hnew : 0x301ff < ver.toInt) :
    W_1567 fb F Wl (fun j' g' _ V' => j' = 944 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = _ := hax
  wpx [W_1567, o18]
  rw [subF_g32, show (197119#32).toInt = 197119 from by decide, decide_eq_true hnew]
  exact ⟨fun _ => trivial, fun h => absurd h (by decide)⟩

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

/-- From the call of `_dl_discover_osversion` (`0x61363e`) to `0x6133f0`, in a run whose kernel answers `uname`
with a release since 3.2: the answer `u` is in the frame below the stack pointer, its version in `_dl_osversion`;
the registers a call keeps are as they were. -/
theorem lsb_osv {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hl : CodeIn L lsm_at lsm)
    (hio : CodeIn L Osv.osv_at Osv.osv) (hiu : CodeIn L Uname.unm_at Uname.unm) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1534) (hsp : 504 ≤ X.cpu.gpr.rsp.toNat)
    (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hst : ∀ i < 504, Foot Wl (Addr.add (X.cpu.gpr.rsp - 504#64) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add 8029472#64 i))
    (hvar : X.cpu.gpr.rsp.toNat ≤ 8029472 ∨ 8029476 + 504 ≤ X.cpu.gpr.rsp.toNat) (h0 : rdd(V, 8029472#64) = 0)
    (hun : ∀ t, KernelNew (o t .uname).val)
    (k : ∀ u Y t', UtsnameOk u → KernelNew u → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (OsvMem V X.cpu.gpr u) →
      Y.cpu.rip = lsm_at.add 944 → Saved X.cpu.gpr Y.cpu.gpr →
      GoG prof L o (gev ++ [Osv.osvEv (callG X.cpu.gpr) u]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have t504 : (X.cpu.gpr.rsp - 504#64).toNat = X.cpu.gpr.rsp.toNat - 504 := by bv_omega
  -- the call
  refine c.s_call hK hA hl (lt_len (by decide)) hrip (call_1534 _) hio (Osv.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · have e : Addr.add (X.cpu.gpr.rsp - 8) i = Addr.add (X.cpu.gpr.rsp - 504#64) (496 + i) := by
      simp only [Addr.add]
      bv_omega
    rw [e]
    exact hst _ (by omega)
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₁]; rfl
  have e496 : X.cpu.gpr.rsp - 8 - 496#64 = X.cpu.gpr.rsp - 504#64 := by bv_omega
  refine Osv.osv_ok c hio hiu hK₁ hA₁ hr₁ (by rw [hsp₁]; bv_omega) (by rw [hsp₁]; bv_omega) (fun i hi => ?_)
    (fun i hi => ?_) hl (j₂ := 1539) (lt_len (by decide)) ?_ hun ?_
  · rw [hsp₁, e496]
    exact hst i (by omega)
  · have e : Addr.add (X.cpu.gpr.rsp - 8) i = Addr.add (X.cpu.gpr.rsp - 504#64) (496 + i) := by
      simp only [Addr.add]
      bv_omega
    rw [hsp₁, e]
    exact c.hws _ (hst _ (by omega))
  · rw [hsp₁, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro u g' Z t₂ hu hnew hKZ hAZ hrZ hgZ hax hback
  subst hgZ
  rw [hg₁] at hAZ hback ⊢
  have hpos : (osVersion u).msb = false := by
    have h : 0x301ff < (osVersion u).toInt := hnew
    rw [BitVec.msb_eq_toInt]
    exact decide_eq_false (by omega)
  -- `_dl_osversion` is 0 still
  have h0' : rdd(Osv.frameV (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lsm_at.add (1534 + 5)) 8)) (callG X.cpu.gpr) u,
      8029472#64) = 0 := by
    rw [← h0]
    refine congrArg _ (rd_congr fun i hi => frame_out hsp hu.1 fun h => ?_)
    have e := tg hi (b := 8029472) (by decide)
    omega
  refine (c_1539 prof fb).run c hfs hl _ hKZ hAZ hrZ
    (vc_1539 (ver := osVersion u) hax hpos (fun i hi => c.hws _ (hw i hi)) h0') ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₃ hK₂ hA₂ hr₂ hg₂ -
  refine (c_1561 prof fb).run c hfs hl _ hK₂ hA₂ hr₂ (vc_1561 (ver := osVersion u) (by rw [hg₂]; exact hax) hw) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  refine (c_1567 prof fb).run c hfs hl _ hK₃ hA₃ hr₃
    (vc_1567 (ver := osVersion u) (by rw [hg₃, hg₂]; exact hax) hnew) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₅ hK₄ hA₄ hr₄ hg₄ -
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hback
  have e8 : X.cpu.gpr.rsp - 8 + 8#64 = X.cpu.gpr.rsp := by bv_omega
  refine k u Y₄ t₅ hu hnew hK₄ hA₄ hr₄ ?_
  rw [hg₄, hg₃, hg₂]
  exact ⟨b1.trans e8, b2, b3, b4, b5, b6, b7⟩

end FV7z.StartB
