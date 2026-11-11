import FV7z.Dpr.Cuts
import FV7z.Mpr.Holds
import FV7z.Sga.Holds
/-!
# `_dl_protect_relro` makes the RELRO segment read-only (PLAN.md G3, startup)

glibc 2.31's `_dl_protect_relro (l)` at `0x6ab6a0` in `7zzs`, called by `_dl_non_dynamic_init` with the main map
(`_dl_main_map`, `0x7934e0`): the pages from `l_addr + l_relro_addr` rounded down to `l_addr + l_relro_addr +
l_relro_size` rounded down (`_dl_pagesize`, `0x7933d8`) get `PROT_READ` by `__mprotect`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
namespace FV7z.Dpr

/-- The registers at the call of `__mprotect`: the range's address and length, `PROT_READ`. -/
def dprG (g : Gprs) : Gprs :=
  { g with rax := 110592#64, rdx := 1#64, rbx := 7943392#64, rsp := g.rsp - 8, rsi := 110592#64, rdi := 7827456#64 }

variable {F : Footprint} {Wl : List Rgn}

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi = 7943392#64)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hsp : 0x7a9000 + 8 ≤ g.rsp.toNat)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add 7943392#64 i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add 7944520#64 i)) (f4 : ∀ i < 8, Foot F.data (Addr.add 7944528#64 i))
    (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hra : rdq(V, 7944520#64) = 7829360#64) (hrs : rdq(V, 7944528#64) = 108688#64) :
    W_0 F Wl (fun j' g' _ V' => j' = 67 ∧ g' = dprG g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hdi' : rdi = 7943392#64 := hdi
  subst hdi'
  have hlt := rsp.isLt
  dsimp only at hst hsp
  have r2 : rdq(Vst V (rsp - 8) (toBytesLE rbx 8), 7944520#64) = 7829360#64 := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega)]
    exact hra
  have r3 : rdq(Vst V (rsp - 8) (toBytesLE rbx 8), 7943392#64) = 0#64 := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega)]
    exact hla
  have r4 : rdq(Vst V (rsp - 8) (toBytesLE rbx 8), 7944528#64) = 108688#64 := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by decide) (by bv_omega)]
    exact hrs
  have a1 : 7943392#64 + 1128#64 = 7944520#64 := by decide
  have a2 : 7943392#64 + 1136#64 = 7944528#64 := by decide
  wpx [W_0, W_56, o0, o2, Op.lda, Op.push, Op.ld, Op.addm]
  rw [a1, a2, r2, r3, r4, hps]
  exact ⟨f1, hst, f3, f2, f4, fun _ => rfl, fun h => absurd h (by decide)⟩

/-- After `__mprotect` returned 0: to the `pop`. -/
theorem vc_72 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) :
    W_72 F Wl (fun j' g' _ V' => j' = 49 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h0' : rax = 0 := h0
  subst h0'
  wpx [W_72, o3]
  decide

/-- The `pop` of `rbx`. -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_49 F Wl (fun j' g' _ V' => j' = 50 ∧ g' = { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl
  wpx [W_49, o1, Op.pop]
  exact hl

/-- The `call` of `__mprotect`. -/
def pc67 : List Byte := [0xe8, 0x18, 0xaf, 0xfb, 0xff]
theorem pc67_0 : ∀ feat, Dec feat pc67 0 (FV7z.mk .call 64 [.rel 18446744073709268760] 5) := by dec_rfl
theorem wc67 : pc67 <+: dpr.drop 67 := by decide +kernel
theorem call_67 (feat : Features) : Dec feat dpr 67 (FV7z.mk .call 64 [.rel 18446744073709268760] 5) :=
  Dec.shift (j := 67) (k := 0) (pc67_0 feat) wc67 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_50 : pret <+: dpr.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat dpr 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)

/-- The bytes after: the saved `rbx` and the return address of the call of `__mprotect` below the stack pointer. -/
def DprMem (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) (g.rsp - 16#64) (toBytesLE (dpr_at.add 72) 8)

/-- The event: `mprotect (0x777000, 0x1b000, PROT_READ)`, answered 0. -/
abbrev dprEv (g : Gprs) : Event := ⟨10, [7827456#64, 110592#64, 1#64, g.r10, g.r8, g.r9], 0, [], []⟩

/-- The registers after `__mprotect` returned to `_dl_protect_relro`. -/
def dprM (g : Gprs) (rc r11 : BitVec 64) : Gprs :=
  { g with rax := 0#64, rcx := rc, rdx := 1#64, rbx := 7943392#64, rsp := g.rsp - 8, rsi := 110592#64,
           rdi := 7827456#64, r11 := r11 }

/-- The registers at the return: `rcx` and `r11` the kernel's. -/
def dprR (g : Gprs) (rc r11 : BitVec 64) : Gprs :=
  { g with rax := 0#64, rcx := rc, rdx := 1#64, rsp := g.rsp + 8, rsi := 110592#64, rdi := 7827456#64, r11 := r11 }

theorem gpr_mid (g : Gprs) (rc r11 : BitVec 64) :
    (((((dprG g).set 4 (g.rsp - 16#64)).set 0 0).set 1 rc).set 11 r11).set 4 (g.rsp - 8) = dprM g rc r11 := by
  cases g
  rfl

theorem gpr_end (g : Gprs) (rc r11 : BitVec 64) :
    ({ dprM g rc r11 with rbx := g.rbx, rsp := g.rsp } : Gprs).set 4 (g.rsp + 8) = dprR g rc r11 := by
  cases g
  rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `_dl_protect_relro (&_dl_main_map)` from its entry to its return address, from a start with `Base`, the map's
RELRO range `0x777770` and `0x1a890` bytes, pages of 4096 bytes, the 27 pages from `0x777000` mapped and none special,
the kernel not refusing: the run goes on from a new start with the footprint `G`, which does not write into those
pages, and `Base` as before. -/
theorem dpr_ok {lim : Nat} {b fsb : Addr} {ks : Kst} {G : Footprint} {Wl' : List Rgn} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L dpr_at dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dpr_at) (hdi : X.cpu.gpr.rdi = 7943392#64)
    (hst : ∀ i < 16, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16#64) i)) (hsp : 0x7a9000 + 16 ≤ X.cpu.gpr.rsp.toNat)
    (hsn : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add 7943392#64 i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add 7944520#64 i)) (f4 : ∀ i < 8, Foot F.data (Addr.add 7944528#64 i))
    (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hra : rdq(V, 7944520#64) = 7829360#64) (hrs : rdq(V, 7944528#64) = 108688#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < 27, ∃ m, s₀.proc.mm.mem.mapAt (0x777 + i) = some m ∧ m.special = false)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (X.cpu.gpr.rsp - 16#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ rc r11 s₁ Z t', Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem (DprMem V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = dprR X.cpu.gpr rc r11 →
      GoG prof L o (gev ++ [dprEv X.cpu.gpr]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 16#64) (8 + i) = Addr.add (X.cpu.gpr.rsp - 8) i by
      simp only [Addr.add]; bv_omega] at this
  have l1 : ∀ i < 8, Foot G.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => by
    have := hlG (8 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 16#64) (8 + i) = Addr.add (X.cpu.gpr.rsp - 8) i by
      simp only [Addr.add]; bv_omega] at this
  have l2 : ∀ i < 8, Foot G.data (Addr.add X.cpu.gpr.rsp i) := fun i hi => by
    have := hlG (16 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 16#64) (16 + i) = Addr.add X.cpu.gpr.rsp i by
      simp only [Addr.add]; bv_omega] at this
  have e1 : (dprG X.cpu.gpr).rsp - 8 = X.cpu.gpr.rsp - 16#64 := by
    show X.cpu.gpr.rsp - 8 - 8 = _
    bv_omega
  have e2 : X.cpu.gpr.rsp - 16#64 + 8 = X.cpu.gpr.rsp - 8 := by bv_omega
  have p1 : pageUp (110592#64).toNat / 4096 = 27 := by decide
  have p2 : (7827456#64).toNat / 4096 = 0x777 := by decide
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hdi w1 (by omega) f1 f2 f3 f4 hps hla hra hrs) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_67 _) him (by decide) (by decide) (fun i hi => ?_) ?_
  · rw [hg₁, e1]
    exact hst i (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁, e1] at hA₂ hg₂
  have d1 : Y₂.cpu.gpr.rdi = 7827456#64 := by rw [hg₂]; rfl
  have d2 : Y₂.cpu.gpr.rsi = 110592#64 := by rw [hg₂]; rfl
  have d3 : Y₂.cpu.gpr.rdx = 1#64 := by rw [hg₂]; rfl
  have hev : Mpr.mpEv Y₂.cpu.gpr = dprEv X.cpu.gpr := by rw [hg₂]; rfl
  refine Mpr.mprotect_ro c hB him hK₂ hA₂ hr₂ (by rw [d3]; rfl) (by rw [d1]; rfl) (by rw [d2]; decide)
    (by rw [d1, d2]; decide) hmg (by rw [d1, d2, p1, p2]; exact hmap) hGo hGc hfit
    (by rw [d1, d2, p1, p2]; exact hGw) hGr (by rw [d1, d2, p1, p2]; exact hcode) hww ?_
  rw [hev]
  intro rc r11 s₁ Z t₃ c' hB' hKZ hAZ hrZ hgZ
  have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 16#64 := by rw [hgZ, hg₂]; rfl
  refine c'.s_ret hKZ hAZ him (Mpr.lt_len (by decide)) hrZ (Mpr.ret_19 _)
    (fun i hi => by rw [hspZ]; exact hlG i (by omega)) hin (j₂ := 72) (by decide) ?_ ?_
  · rw [hspZ, vs (toBytesLE_length _ _) (by bv_omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  rintro Z₂ t₄ hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
  rw [hspZ, hgZ, hg₂, e2, gpr_mid] at hgZ₂
  refine (c_72 prof).run c' hin _ hKZ₂ hAZ₂ hrZ₂ (vc_72 (by rw [hgZ₂]; rfl)) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₃ t₅ hKZ₃ hAZ₃ hrZ₃ hgZ₃ -
  have hspZ₃ : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgZ₃, hgZ₂]; rfl
  refine (c_49 prof).run c' hin _ hKZ₃ hAZ₃ hrZ₃ (vc_49 (by rw [hspZ₃]; exact l1)) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Z₄ t₆ hKZ₄ hAZ₄ hrZ₄ hgZ₄ -
  have hrb : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16#64)
      (toBytesLE (dpr_at.add 72) 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
      vs (toBytesLE_length _ _) (by bv_omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  have e3 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := by bv_omega
  rw [hspZ₃, hrb, e3, hgZ₃, hgZ₂] at hgZ₄
  have hspZ₄ : Z₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ₄]
  refine c'.s_ret hKZ₄ hAZ₄ hin (lt_len (by decide)) hrZ₄ (ret_50 _) (fun i hi => by rw [hspZ₄]; exact l2 i hi)
    hin₂ h₂ ?_ ?_
  · rw [hspZ₄, vr (toBytesLE_length _ _) (by bv_omega) hsn (by bv_omega),
      vr (toBytesLE_length _ _) (by bv_omega) hsn (by bv_omega)]
    exact hret
  rintro Z₅ t₇ hKZ₅ hAZ₅ ⟨hrZ₅, hgZ₅⟩
  refine k rc r11 s₁ Z₅ t₇ c' hB' hKZ₅ hAZ₅ hrZ₅ ?_
  rw [hgZ₅, hspZ₄, hgZ₄]
  exact gpr_end _ _ _

end FV7z.Dpr
