import FV7z.Osv.Vc
import FV7z.Uname.Holds
import FV7z.CpuFeat.Inv
/-!
# `_dl_discover_osversion` returns the kernel's version (PLAN.md G3, startup)

glibc 2.31's `_dl_discover_osversion ()` at `0x671d50` in `7zzs`: `__uname (&uts)`, then the number of
`uts.release` (`osVersion`, `Spec/OsVersion.lean`). The prologue (cut point 0), `Seg.s_call` and `Seg.s_ret` around
`Uname.uname_ok`, the code after the call (25), the loop (`Vc.lean`, by `Seg.cfg`), and the `ret`.

- `frameV`: the bytes the function leaves: the three registers it saves, the return address of its call, the
  kernel's answer; `frameV_*`: what is read there.
- `par`, `par_ok`, `par_rel`: the loop's parameters from a call, and the release they have is the answer's.
- `osv_ok`: called with 496 bytes below the stack pointer in what the run may store into, below the end of the user
  address space, and a return address in the code, the run reaches the return address with `eax` the version of
  the kernel's answer `u` (a `struct new_utsname`, with what all the stream's answers to `uname` have, `P`), the
  registers a call keeps as at the entry (`Back`), the bytes outside the 496 as they were.

The way taken when `__uname` fails (the release is read from `/proc/sys/kernel/osrelease`) is not one of these runs:
`uname` with a buffer the process may write does not fail.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.CpuFeat (Vst_at)
namespace FV7z.Osv

/-! ## The `call` and the `ret`s -/

def pc20 : List Byte := [0xe8, 0x77, 0x2c, 0xff, 0xff]
def pret : List Byte := [0xc3]
theorem pc20_0 : ∀ feat, Dec feat pc20 0 (FV7z.mk .call 64 [.rel 18446744073709497463] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc20 : pc20 <+: osv.drop 20 := by decide +kernel
theorem w_138 : pret <+: osv.drop 138 := by decide +kernel
theorem w_169 : pret <+: osv.drop 169 := by decide +kernel
theorem call_20 (feat : Features) : Dec feat osv 20 (FV7z.mk .call 64 [.rel 18446744073709497463] 5) :=
  Dec.shift (j := 20) (k := 0) (pc20_0 feat) wc20 (Nat.zero_le _)
theorem ret_138 (feat : Features) : Dec feat osv 138 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 138) (k := 0) (pret_0 feat) w_138 (Nat.zero_le _)
theorem ret_169 (feat : Features) : Dec feat osv 169 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 169) (k := 0) (pret_0 feat) w_169 (Nat.zero_le _)

/-! ## The frame -/

/-- The bytes the function leaves, called with registers `g` in memory `V`, the kernel's answer `u`. -/
def frameV (V : Addr → Byte) (g : Gprs) (u : List Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8#64) (toBytesLE g.r12 8)) (g.rsp - 16#64) (toBytesLE g.rbp 8)) (g.rsp - 24#64)
    (toBytesLE g.rbx 8)) (g.rsp - 496#64) (toBytesLE (osv_at.add 25) 8)) (g.rsp - 424#64) u

variable {V : Addr → Byte} {g : Gprs} {u : List Byte}

/-- Side conditions of reads and stores at addresses given from the stack pointer. -/
macro "sd" : tactic =>
  `(tactic| first | (simp only [toBytesLE_length]; done) | (simp only [toBytesLE_length]; bv_omega) | bv_omega | decide)

theorem frameV_out (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) {a : Addr}
    (h : ¬ (g.rsp.toNat - 496 ≤ a.toNat ∧ a.toNat < g.rsp.toNat)) : frameV V g u a = V a := by
  unfold frameV
  rw [Vst_out _ _ _ _ (by rw [hu]; bv_omega) (by rw [hu]; bv_omega), Vst_out _ _ _ _ (by sd) (by sd),
    Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd), Vst_out _ _ _ _ (by sd) (by sd)]

/-- The return address of the call of `__uname`. -/
theorem frameV_ra (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) :
    rdq(frameV V g u, g.rsp - 496#64) = osv_at.add 25 := by
  unfold frameV
  rw [rd_Vst _ _ _ _ _ (by rw [hu]; bv_omega) (by sd) (by rw [hu]; bv_omega), rd_Vst_self _ _ _ (by sd) (by sd)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem frameV_rbx (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) : rdq(frameV V g u, g.rsp - 24#64) = g.rbx := by
  unfold frameV
  rw [rd_Vst _ _ _ _ _ (by rw [hu]; bv_omega) (by sd) (by rw [hu]; bv_omega),
    rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst_self _ _ _ (by sd) (by sd)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem frameV_rbp (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) : rdq(frameV V g u, g.rsp - 16#64) = g.rbp := by
  unfold frameV
  rw [rd_Vst _ _ _ _ _ (by rw [hu]; bv_omega) (by sd) (by rw [hu]; bv_omega),
    rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
    rd_Vst_self _ _ _ (by sd) (by sd)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem frameV_r12 (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) : rdq(frameV V g u, g.rsp - 8#64) = g.r12 := by
  unfold frameV
  rw [rd_Vst _ _ _ _ _ (by rw [hu]; bv_omega) (by sd) (by rw [hu]; bv_omega),
    rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
    rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd), rd_Vst_self _ _ _ (by sd) (by sd)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- The word at the stack pointer, the return address. -/
theorem frameV_top (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) : rdq(frameV V g u, g.rsp) = rdq(V, g.rsp) := by
  congr 1
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  refine frameV_out hsp hu fun h => ?_
  simp only [Addr.add] at h
  bv_omega

/-- The release's characters. -/
theorem frameV_ch (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) {i : Nat} (hi : i < 65) :
    frameV V g u (Addr.add (g.rsp - 294#64) i) = u[130 + i]'(by omega) := by
  have e : Addr.add (g.rsp - 294#64) i = Addr.add (g.rsp - 424#64) (130 + i) := by
    simp only [Addr.add]
    bv_omega
  rw [e]
  exact Vst_at u _ _ (by omega) (by rw [hu]; bv_omega)

/-! ## The loop's parameters -/

/-- The loop's parameters: the release is 294 bytes below the stack pointer of the call. -/
def par (V : Addr → Byte) (g g₅ : Gprs) (u : List Byte) : Par := ⟨g.rsp - 294#64, g₅, frameV V g u⟩

variable {F : Footprint} {Wl : List Rgn} {g₅ : Gprs}

theorem par_ok (hsp : 496 ≤ g.rsp.toNat) (hu : UtsnameOk u) (h5 : g₅.rsp = g.rsp - 488#64)
    (hrd : ∀ i < 496, Foot F.data (Addr.add (g.rsp - 496#64) i)) : (par V g g₅ u).Ok F := by
  refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · show (g.rsp - 294#64).toNat + 65 ≤ 2 ^ 64
    bv_omega
  · have e : Addr.add (g.rsp - 294#64) i = Addr.add (g.rsp - 496#64) (202 + i) := by
      simp only [Addr.add]
      bv_omega
    show Foot F.data (Addr.add (g.rsp - 294#64) i)
    rw [e]
    exact hrd _ (by omega)
  · show frameV V g u (Addr.add (g.rsp - 294#64) 64) = 0
    rw [frameV_ch hsp hu.1 (by decide)]
    have h := hu.2 2 (by decide)
    have hl : 65 * 2 + 64 < u.length := by rw [hu.1]; decide
    rw [List.getElem?_eq_getElem hl] at h
    exact Option.some.inj h
  · have e : Addr.add (g₅.rsp + 464#64) i = Addr.add (g.rsp - 496#64) (472 + i) := by
      rw [h5]
      simp only [Addr.add]
      bv_omega
    show Foot F.data (Addr.add (g₅.rsp + 464#64) i)
    rw [e]
    exact hrd _ (by omega)

/-- The loop's release is the answer's. -/
theorem par_rel (hsp : 496 ≤ g.rsp.toNat) (hu : u.length = 390) : (par V g g₅ u).rel = release u := by
  apply List.ext_getElem
  · simp only [Par.rel, release, List.length_map, List.length_range, List.length_take, List.length_drop, hu]
    decide
  · intro i h1 h2
    have hi : i < 65 := by simpa [Par.rel] using h1
    simp only [Par.rel, List.getElem_map, List.getElem_range, release, List.getElem_take, List.getElem_drop]
    exact frameV_ch hsp hu hi

/-! ## The straight pieces -/

theorem e16 (x : BitVec 64) : x - 8 - 8 = x - 16#64 := by bv_omega
theorem e24 (x : BitVec 64) : x - 16#64 - 8 = x - 24#64 := by bv_omega
theorem e488 (x : BitVec 64) : x - 24#64 - 464#64 = x - 488#64 := by bv_omega
theorem e424 (x : BitVec 64) : x - 488#64 + 64#64 = x - 424#64 := by bv_omega
theorem e496 (x : BitVec 64) : x - 488#64 - 8 = x - 496#64 := by bv_omega

/-- A byte of the 496 below the stack pointer. -/
theorem slot {sp a : Addr} (hst : ∀ i < 496, Foot Wl (Addr.add (sp - 496#64) i)) {k : Nat} (hk : k < 496)
    (ha : a = Addr.add (sp - 496#64) k) : Foot Wl a := ha ▸ hst k hk

/-- The prologue: three registers saved, the frame, the buffer's address. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hst : ∀ i < 496, Foot Wl (Addr.add (g.rsp - 496#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 20 ∧ g' = (g.set 4 (g.rsp - 488#64)).set 7 (g.rsp - 424#64) ∧
      V' = Vst (Vst (Vst V (g.rsp - 8#64) (toBytesLE g.r12 8)) (g.rsp - 16#64) (toBytesLE g.rbp 8)) (g.rsp - 24#64)
        (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hst' : ∀ i < 496, Foot Wl (Addr.add (rsp - 496#64) i) := hst
  wpx [W_0, o0]
  simp only [e16, e24, e488, e424]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · exact slot hst' (k := 488 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  · exact slot hst' (k := 480 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  · exact slot hst' (k := 472 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  · exact ⟨rfl, rfl⟩

/-- After `__uname` returns 0: the release's address, no number read yet. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) :
    W_25 F Wl (fun j' g' _ V' => j' = 46 ∧ g' = (g.set 7 (g.rsp + 194#64)).set 8 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = 0 := h0
  wpx [W_25, W_41, o1, o2]
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  simp only [BitVec.xor_self]
  rfl

/-! ## The function -/

/-- The event of the call: `uname` with the buffer 424 bytes below the stack pointer, answered `u`. -/
abbrev osvEv (g : Gprs) (u : List Byte) : Event := ⟨63, [g.rsp - 424#64, g.rsi, g.rdx, g.r10, g.r8, g.r9], 0, [], u⟩

/-- The registers a function keeps, after its `ret`. -/
def Back (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp + 8#64 ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `_dl_discover_osversion ()` returns the version of the kernel's answer. -/
theorem osv_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L osv_at osv) (hinu : CodeIn L Uname.unm_at Uname.unm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = osv_at)
    (hsp : 496 ≤ X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hst : ∀ i < 496, Foot Wl (Addr.add (X.cpu.gpr.rsp - 496#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) {P : List Byte → Prop} (hP : ∀ t, P (o t .uname).val)
    (k : ∀ u g' Z t', UtsnameOk u → P u → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (frameV V X.cpu.gpr u) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → g'.rax = BitVec.setWidth 64 (osVersion u) → Back X.cpu.gpr g' →
      GoG prof L o (gev ++ [osvEv X.cpu.gpr u]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hst) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 488#64 := by rw [hg₁]; rfl
  -- `__uname (&uts)`
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_20 _) hinu (Uname.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁, e496]
    exact hst i (Nat.lt_trans hi (by decide))
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, e496] at hA₂ hg₂
  have hdi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rsp - 424#64 := by rw [hg₂, hg₁]; rfl
  refine Uname.uname_ok c hinu hK₂ hA₂ hr₂ (by rw [hdi₂]; bv_omega) (fun i hi => ?_) hP ?_
  · rw [hdi₂]
    exact slot hst (k := 72 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  intro u rc r11 Y₃ t₃ hu hPu hK₃ hA₃ hr₃ hg₃
  have eEv : Uname.unEv Y₂.cpu.gpr u = osvEv X.cpu.gpr u := by rw [hg₂, hg₁]; rfl
  rw [eEv]
  rw [hdi₂] at hA₃
  have hA₃' : Agree F Y₃.proc.mm.mem (frameV V X.cpu.gpr u) := hA₃
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 496#64 := by rw [hg₃, hg₂]; rfl
  refine c.s_ret hK₃ hA₃' hinu (Uname.lt_len (by decide)) hr₃ (Uname.ret_19 _) (fun i hi => ?_) hin (j₂ := 25)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₃]
    exact c.hws _ (hst i (Nat.lt_trans hi (by decide)))
  · rw [hsp₃]
    exact frameV_ra hsp hu.1
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  have hax₄ : Y₄.cpu.gpr.rax = 0 := by rw [hg₄, hg₃]; rfl
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 488#64 := by
    rw [hg₄, hsp₃]
    show X.cpu.gpr.rsp - 496#64 + 8 = _
    bv_omega
  -- the code after the call
  refine (c_25 prof).run c hin _ hK₄ hA₄ hr₄ (vc_25 hax₄) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 488#64 := by rw [hg₅, ← hsp₄]; rfl
  -- the loop
  have hP : (par V X.cpu.gpr Y₅.cpu.gpr u).Ok F := par_ok hsp hu hsp₅ (fun i hi => c.hws _ (hst i hi))
  have hrel : (par V X.cpu.gpr Y₅.cpu.gpr u).rel = release u := par_rel hsp hu.1
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ W => Inv (par V X.cpu.gpr Y₅.cpu.gpr u) ℓ n g W)
    (fun j' g' _ V' => Fin (par V X.cpu.gpr Y₅.cpu.gpr u) j' g' V') (fun ℓ n g f W h => vcAll hP ℓ n g f W h) ?_
    (3 * 66) 46 hK₅ hA₅ hr₅
    ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, 0, 2, 0, Nat.zero_le _, Nat.le_refl _, rfl, ?_, ?_, ?_, rfl⟩⟩
  · -- the `ret`
    rintro j' g fl V' ⟨hj, rfl, hax, hrsp, hbx, hbp, h12, h13, h14, h15⟩ Y t' hKY hAY hrY hgY -
    subst hgY
    obtain ⟨hlt, hd⟩ : j' < osv.length ∧ Dec prof.feat osv j' (FV7z.mk .ret 64 [] 1) := by
      rcases hj with rfl | rfl
      · exact ⟨lt_len (by decide), ret_138 _⟩
      · exact ⟨lt_len (by decide), ret_169 _⟩
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      rw [hrsp]
      show Y₅.cpu.gpr.rsp + 488#64 = _
      rw [hsp₅]
      bv_omega
    have e24' : Y₅.cpu.gpr.rsp + 464#64 = X.cpu.gpr.rsp - 24#64 := by rw [hsp₅]; bv_omega
    have e16' : Y₅.cpu.gpr.rsp + 472#64 = X.cpu.gpr.rsp - 16#64 := by rw [hsp₅]; bv_omega
    have e8' : Y₅.cpu.gpr.rsp + 480#64 = X.cpu.gpr.rsp - 8#64 := by rw [hsp₅]; bv_omega
    have keep : ∀ r : Gprs → BitVec 64, (∀ (h : Gprs) v, r (h.set 0 v) = r h) → (∀ (h : Gprs) v, r (h.set 1 v) = r h) →
        (∀ (h : Gprs) v, r (h.set 4 v) = r h) → (∀ (h : Gprs) v, r (h.set 7 v) = r h) →
        (∀ (h : Gprs) v, r (h.set 8 v) = r h) → (∀ (h : Gprs) v, r (h.set 11 v) = r h) →
        r Y₅.cpu.gpr = r X.cpu.gpr := by
      intro r h0 h1 h4 h7 h8 h11
      rw [hg₅, hg₄, hg₃, hg₂, hg₁, h8, h7, h4, h11, h1, h0, h4, h7, h4]
    refine c.s_ret hKY hAY hin hlt hrY hd (fun i hi => ?_) hin₂ h₂ ?_ ?_
    · rw [hspY]
      exact hl i hi
    · rw [hspY]
      show rdq(frameV V X.cpu.gpr u, X.cpu.gpr.rsp) = _
      rw [frameV_top hsp hu.1]
      exact hra
    rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
    refine k u _ Z t'' hu hPu hKZ hAZ hrZ hgZ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Y.cpu.gpr.rax = _
      rw [hax]
      show BitVec.setWidth 64 (osParts 3 0 (par V X.cpu.gpr Y₅.cpu.gpr u).rel) = _
      rw [hrel]
      rfl
    · show Y.cpu.gpr.rsp + 8#64 = _
      rw [hspY]
    · show Y.cpu.gpr.rbx = _
      rw [hbx]
      show rdq(frameV V X.cpu.gpr u, Y₅.cpu.gpr.rsp + 464#64) = _
      rw [e24', frameV_rbx hsp hu.1]
    · show Y.cpu.gpr.rbp = _
      rw [hbp]
      show rdq(frameV V X.cpu.gpr u, Y₅.cpu.gpr.rsp + 472#64) = _
      rw [e16', frameV_rbp hsp hu.1]
    · show Y.cpu.gpr.r12 = _
      rw [h12]
      show rdq(frameV V X.cpu.gpr u, Y₅.cpu.gpr.rsp + 480#64) = _
      rw [e8', frameV_r12 hsp hu.1]
    · show Y.cpu.gpr.r13 = _
      rw [h13]
      exact keep (·.r13) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl)
    · show Y.cpu.gpr.r14 = _
      rw [h14]
      exact keep (·.r14) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl)
    · show Y.cpu.gpr.r15 = _
      rw [h15]
      exact keep (·.r15) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl)
  · rw [addr_add_zero, hg₅]
    show Y₄.cpu.gpr.rsp + 194#64 = X.cpu.gpr.rsp - 294#64
    rw [hsp₄]
    bv_omega
  · rw [hg₅]
    show Y₄.cpu.gpr.rax = _
    rw [hax₄]
    rfl
  · rw [hg₅]
    rfl

end FV7z.Osv
