import FV7z.Ims.Cuts
import FV7z.Sga.Holds
import FV7z.Startup.StrAt
/-!
# `__init_misc` (PLAN.md G3, startup)

glibc 2.31's `__init_misc (argc, argv, envp)` (`misc/init-misc.c`) at `0x668da0`, called by `__libc_init_first`:
with `argv` and `argv[0]` not null, `program_invocation_name` (`0x793340`) is `argv[0]` and
`program_invocation_short_name` (`0x793338`) the address after its last `/` (`strrchr`, through the PLT at
`0x401050`: its contract `Str.RchrAt` is a hypothesis), `argv[0]` itself if it has none.

- `frV`, `vc_0`, `vc_39`, `vc_67`: the cut blocks (prologue, the two stores, epilogue).
- `InFr`, `cV`, `imV`, `Short`: the frame's bytes, the bytes at the call and at the end, what the short name is.
- `init_misc_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ims

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes after the two `push`es. -/
def frV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 16#64) (toBytesLE g.rbx 8)

/-- The prologue, `argv` and `argv[0]` not null: to the `call` of `strrchr`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {a0 : BitVec 64}
    (hst : ∀ i < 16, Foot Wl (Addr.add (g.rsp - 16#64) i)) (hsp : 16 ≤ g.rsp.toNat) (hsi : g.rsi ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) (ha : rdq(frV V g, g.rsi) = a0) (ha0 : a0 ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 34 ∧
      g' = { g with rbx := g.rsi, rsp := g.rsp - 24#64, rbp := a0, rdi := a0, rsi := 47#64 } ∧
      V' = frV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold frV at ha ⊢
  dsimp only at hst hsp ha fa hsi ⊢
  have w1 : ∀ i < 8, Foot Wl (Addr.add (rsp - 8) i) := fun i hi => by
    have := hst (8 + i) (by omega)
    rwa [show Addr.add (rsp - 16#64) (8 + i) = Addr.add (rsp - 8) i by simp only [Addr.add]; bv_omega] at this
  have w2 : ∀ i < 8, Foot Wl (Addr.add (rsp - 16#64) i) := fun i hi => hst i (by omega)
  have e16 : rsp - 8 - 8 = rsp - 16#64 := by bv_omega
  have e24 : rsp - 16#64 - 8#64 = rsp - 24#64 := by bv_omega
  wpx [W_0, W_9, W_26, o0, o1, o2, Op.push, Op.ld]
  simp only [e16, e24]
  generalize Vst (Vst V (rsp - 8) (toBytesLE rbp 8)) (rsp - 16#64) (toBytesLE rbx 8) = W at ha ⊢
  simp only [ha, BitVec.and_self]
  exact ⟨fun h => absurd (beq_iff_eq.1 h) hsi, fun _ => ⟨w1, w2, fa, fun h => absurd (beq_iff_eq.1 h) ha0,
    fun _ => ⟨rfl, trivial⟩⟩⟩

/-- After `strrchr`: the two stores. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} {a0 s : BitVec 64}
    (hw : ∀ i < 16, Foot Wl (Addr.add 7942968#64 i)) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (hs : s = if g.rax = 0 then g.rbp else g.rax + 1#64)
    (ha : rdq(Vst V 7942968#64 (toBytesLE s 8), g.rbx) = a0) :
    W_39 F Wl (fun j' g' _ V' => j' = 67 ∧ g' = { g with rax := a0, rdx := g.rax + 1#64, rbp := s } ∧
      V' = Vst (Vst V 7942968#64 (toBytesLE s 8)) 7942976#64 (toBytesLE a0 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa hs ha ⊢
  have w1 : ∀ i < 8, Foot Wl (Addr.add 7942968#64 i) := fun i hi => hw i (by omega)
  have w2 : ∀ i < 8, Foot Wl (Addr.add 7942976#64 i) := fun i hi => by
    have := hw (8 + i) (by omega)
    rwa [show Addr.add 7942968#64 (8 + i) = Addr.add 7942976#64 i by simp only [Addr.add]; bv_omega] at this
  wpx [W_39, o3, Op.lea, Op.cmov64, Op.sta, Op.ld]
  by_cases h : rax = 0
  · subst h
    simp only [↓reduceIte] at hs
    subst hs
    simp [ha]
    exact ⟨w1, fa, w2⟩
  · simp only [h, ↓reduceIte] at hs
    subst hs
    have h' : ¬ rax = 0#64 := h
    simp [h', ha]
    exact ⟨w1, fa, w2⟩

/-- The epilogue. -/
theorem vc_67 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 16, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_67 F Wl (fun j' g' _ V' => j' = 73 ∧
      g' = { g with rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 16#64), rsp := g.rsp + 24#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  have w1 : ∀ i < 8, Foot F.data (Addr.add (rsp + 8#64) i) := fun i hi => hl i (by omega)
  have w2 : ∀ i < 8, Foot F.data (Addr.add (rsp + 16#64) i) := fun i hi => by
    have := hl (8 + i) (by omega)
    rwa [show Addr.add (rsp + 8#64) (8 + i) = Addr.add (rsp + 16#64) i by simp only [Addr.add]; bv_omega] at this
  have e16 : rsp + 8#64 + 8 = rsp + 16#64 := by bv_omega
  have e24 : rsp + 16#64 + 8 = rsp + 24#64 := by bv_omega
  wpx [W_67, o4, Op.pop]
  rw [e16, e24]
  exact ⟨w1, w2, rfl⟩

/-! ## The `call` and the `ret` -/

def pc34 : List Byte := [0xe8, 0x89, 0x82, 0xd9, 0xff]
def pret : List Byte := [0xc3]
theorem pc34_0 : ∀ feat, Dec feat pc34 0 (FV7z.mk .call 64 [.rel 18446744073707029129] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc34 : pc34 <+: ims.drop 34 := by decide +kernel
theorem w_73 : pret <+: ims.drop 73 := by decide +kernel
theorem call_34 (feat : Features) : Dec feat ims 34 (FV7z.mk .call 64 [.rel 18446744073707029129] 5) :=
  Dec.shift (j := 34) (k := 0) (pc34_0 feat) wc34 (Nat.zero_le _)
theorem ret_73 (feat : Features) : Dec feat ims 73 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 73) (k := 0) (pret_0 feat) w_73 (Nat.zero_le _)

/-! ## The bytes -/

/-- A byte of the function's frame: the 32 bytes below the stack pointer of the entry. -/
def InFr (g : Gprs) (a : Addr) : Prop := g.rsp.toNat - 32 ≤ a.toNat ∧ a.toNat < g.rsp.toNat

/-- The bytes at `strrchr`'s first instruction: the two `push`es and the return address. -/
def cV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (frV V g) (g.rsp - 32#64) (toBytesLE (ims_at.add 39) 8)

/-- The bytes `__init_misc` leaves: `program_invocation_short_name` (`0x793338`) is `s`, `program_invocation_name`
(`0x793340`) is `a0`. -/
def imV (V : Addr → Byte) (g : Gprs) (a0 s : Addr) : Addr → Byte :=
  Vst (Vst (cV V g) 7942968#64 (toBytesLE s 8)) 7942976#64 (toBytesLE a0 8)

/-- `s` is the address after the last `/` of the string of `n` characters at `a`, `a` if it has none. -/
def Short (V : Addr → Byte) (a : Addr) (n : Nat) (s : Addr) : Prop :=
  (∀ k < n, V (Addr.add a k) ≠ 47#8) ∧ s = a ∨
    ∃ m < n, V (Addr.add a m) = 47#8 ∧ (∀ k, m < k → k < n → V (Addr.add a k) ≠ 47#8) ∧ s = Addr.add a (m + 1)

theorem fr_rd {V : Addr → Byte} {g : Gprs} {x : Addr} {m : Nat} (hx : x.toNat + m ≤ 2 ^ 64) (hsp : 16 ≤ g.rsp.toNat)
    (h : g.rsp.toNat ≤ x.toNat ∨ x.toNat + m ≤ g.rsp.toNat - 16) :
    List.map (frV V g) (byteAddrs x m) = List.map V (byteAddrs x m) := by
  have := g.rsp.isLt
  unfold frV
  rw [vr (toBytesLE_length _ _) (by bv_omega) hx (by bv_omega),
    vr (toBytesLE_length _ _) (by bv_omega) hx (by bv_omega)]

theorem cV_out {V : Addr → Byte} {g : Gprs} (hsp : 32 ≤ g.rsp.toNat) {a : Addr} (ha : ¬ InFr g a) :
    cV V g a = V a := by
  have := g.rsp.isLt
  unfold InFr at ha
  unfold cV frV
  rw [vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega), vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega),
    vo (toBytesLE_length _ _) (by bv_omega) (by bv_omega)]

theorem cV_rd {V : Addr → Byte} {g : Gprs} {x : Addr} {m : Nat} (hx : x.toNat + m ≤ 2 ^ 64) (hsp : 32 ≤ g.rsp.toNat)
    (h : g.rsp.toNat ≤ x.toNat ∨ x.toNat + m ≤ g.rsp.toNat - 32) :
    List.map (cV V g) (byteAddrs x m) = List.map V (byteAddrs x m) := by
  have := g.rsp.isLt
  unfold cV
  rw [vr (toBytesLE_length _ _) (by bv_omega) hx (by bv_omega), fr_rd hx (by omega) (by omega)]

theorem cV_rbx {V : Addr → Byte} {g : Gprs} (hsp : 32 ≤ g.rsp.toNat) : rdq(cV V g, g.rsp - 16#64) = g.rbx := by
  have := g.rsp.isLt
  unfold cV frV
  rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega), vs (toBytesLE_length _ _) (by bv_omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem cV_rbp {V : Addr → Byte} {g : Gprs} (hsp : 32 ≤ g.rsp.toNat) : rdq(cV V g, g.rsp - 8) = g.rbp := by
  have := g.rsp.isLt
  unfold cV frV
  rw [vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega),
    vr (toBytesLE_length _ _) (by bv_omega) (by bv_omega) (by bv_omega), vs (toBytesLE_length _ _) (by bv_omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- Bytes apart from the two variables. -/
theorem gl_rd {W : Addr → Byte} {a s x : Addr} {m : Nat} (hx : x.toNat + m ≤ 2 ^ 64)
    (h : 7942984 ≤ x.toNat ∨ x.toNat + m ≤ 7942968) :
    List.map (Vst (Vst W 7942968#64 (toBytesLE s 8)) 7942976#64 (toBytesLE a 8)) (byteAddrs x m) =
      List.map W (byteAddrs x m) := by
  rw [vr (toBytesLE_length _ _) (by decide) hx (by bv_omega), vr (toBytesLE_length _ _) (by decide) hx (by bv_omega)]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {ev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Pm : (Addr → Byte) → Prop}

set_option maxHeartbeats 1600000 in
/-- `__init_misc (argc, argv, envp)` with `argv[0]` a string of `n` characters: from the entry to the return address,
the two variables stored (`imV`, `Short`), the registers a function keeps kept. `strrchr` (through the PLT) by its
contract. -/
theorem init_misc_ok {pr : List Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {X : State} {t : Nat}
    {V : Addr → Byte} {a0 : Addr} {n : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ims_at ims)
    (hir : CodeIn L 4198480#64 pr) (hr0 : 0 < pr.length) (hrchr : Str.RchrAt prof L o 4198480#64 Pm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ims_at)
    (hsp : 32 ≤ X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i))
    (hrf : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hsi : X.cpu.gpr.rsi ≠ 0) (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (ha : rdq(V, X.cpu.gpr.rsi) = a0) (ha0 : a0 ≠ 0) (hafit : X.cpu.gpr.rsi.toNat + 8 ≤ 2 ^ 64)
    (haout : X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32)
    (hag : 7942984 ≤ X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 8 ≤ 7942968)
    (hgl : ∀ i < 16, Foot Wl (Addr.add 7942968#64 i))
    (hgs : 7942984 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ 7942968)
    (nfit : a0.toNat + n < 2 ^ 64) (nnz : ∀ k < n, V (Addr.add a0 k) ≠ 0) (nz : V (Addr.add a0 n) = 0)
    (npg : ∀ x : Addr, a0.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (a0.toNat + n) / 4096 → Foot F.data x)
    (nout : ∀ k ≤ n, ¬ InFr X.cpu.gpr (Addr.add a0 k))
    (hPm : ∀ W, (∀ a, ¬ InFr X.cpu.gpr a → W a = V a) → Pm W)
    (k : ∀ Z t' s, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (imV V X.cpu.gpr a0 s) → Short V a0 n s →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o ev gP gE Z t') :
    GoG prof L o ev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (a0 := a0) (fun i hi => ?_) (by omega) hsi fa ?_ ha0) ?_
  · have := hst (16 + i) (by omega)
    rwa [show Addr.add (X.cpu.gpr.rsp - 32#64) (16 + i) = Addr.add (X.cpu.gpr.rsp - 16#64) i by
      simp only [Addr.add]; bv_omega] at this
  · rw [fr_rd hafit (by omega) (by omega)]
    exact ha
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  -- the `call` of `strrchr`
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_34 _) hir hr0 (by decide) (fun i hi => ?_) ?_
  · rw [hspY, show X.cpu.gpr.rsp - 24#64 - 8 = X.cpu.gpr.rsp - 32#64 by bv_omega]
    exact hst i (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hspY, show X.cpu.gpr.rsp - 24#64 - 8 = X.cpu.gpr.rsp - 32#64 by bv_omega] at hA₂ hg₂
  have hA₂' : Agree F Y₂.proc.mm.mem (cV V X.cpu.gpr) := hA₂
  have hdi : Y₂.cpu.gpr.rdi = a0 := by rw [hg₂, hgY]; rfl
  have hc : Y₂.cpu.gpr.rsi.setWidth 8 = 47#8 := by rw [hg₂, hgY]; rfl
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by rw [hg₂]; rfl
  have vS : ∀ k ≤ n, cV V X.cpu.gpr (Addr.add a0 k) = V (Addr.add a0 k) := fun k hk => cV_out hsp (nout k hk)
  refine hrchr n c hK₂ hA₂' hr₂ (hPm _ fun a ha => cV_out hsp ha) hin (lt_len (show 39 < 81 by decide)) ?_
    (fun i hi => ?_) (by rw [hdi]; exact nfit) (fun i hi => ?_) ?_ (by rw [hc]; decide) (fun x h1 h2 => ?_) ?_
  · rw [hsp₂]
    unfold cV
    rw [vs (toBytesLE_length _ _) (by bv_omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hsp₂]
    exact c.hws _ (hst i (by omega))
  · rw [hdi, vS i (by omega)]
    exact nnz i hi
  · rw [hdi, vS n (Nat.le_refl _)]
    exact nz
  · rw [hdi] at h1 h2
    exact npg x h1 h2
  intro Z t' hKZ hAZ hrZ hspZ r0 r1 hbxZ hbpZ h12Z h13Z h14Z h15Z
  rw [hdi, hc] at r0 r1
  have ebx : Z.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hbxZ, hg₂, hgY]; rfl
  have ebp : Z.cpu.gpr.rbp = a0 := by rw [hbpZ, hg₂, hgY]; rfl
  have esp : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hspZ, hsp₂]; bv_omega
  -- the short name
  have hS : Short V a0 n (if Z.cpu.gpr.rax = 0 then Z.cpu.gpr.rbp else Z.cpu.gpr.rax + 1#64) := by
    rcases Str.last_with (fun k => V (Addr.add a0 k) = 47#8) n with hno | ⟨m, hm, hp, hl⟩
    · have e0 := r0 fun k hk => by rw [vS k (by omega)]; exact hno k hk
      rw [e0, ebp]
      exact .inl ⟨hno, rfl⟩
    · have e1 := r1 m hm (by rw [vS m (by omega)]; exact hp)
        (fun k h1 h2 => by rw [vS k (by omega)]; exact hl k h1 h2)
      have hne : Z.cpu.gpr.rax ≠ 0 := by
        rw [e1]
        intro h
        have h' := congrArg BitVec.toNat h
        rw [toNat_add_of_fits (n := n) hm (by omega)] at h'
        have : a0.toNat ≠ 0 := fun h0 => ha0 (BitVec.eq_of_toNat_eq h0)
        simp at h'
        omega
      simp only [hne, ↓reduceIte]
      rw [e1]
      refine .inr ⟨m, hm, hp, hl, ?_⟩
      simp only [Addr.add]
      bv_omega
  obtain ⟨s, hs⟩ : ∃ s, s = if Z.cpu.gpr.rax = 0 then Z.cpu.gpr.rbp else Z.cpu.gpr.rax + 1#64 := ⟨_, rfl⟩
  rw [← hs] at hS
  refine (c_39 prof).run c hin _ hKZ hAZ hrZ (vc_39 (a0 := a0) (s := s) hgl (fun i hi => ?_) hs ?_) ?_
  · rw [ebx]
    exact fa i hi
  · rw [ebx, vr (toBytesLE_length _ _) (by decide) hafit (by bv_omega), cV_rd hafit hsp (by omega)]
    exact ha
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hA₃' : Agree F Y₃.proc.mm.mem (imV V X.cpu.gpr a0 s) := hA₃
  have esp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₃]; exact esp
  -- the epilogue
  refine (c_67 prof).run c hin _ hK₃ hA₃' hr₃ (vc_67 fun i hi => ?_) ?_
  · rw [esp₃]
    have := hst (16 + i) (by omega)
    rw [show Addr.add (X.cpu.gpr.rsp - 32#64) (16 + i) = Addr.add (X.cpu.gpr.rsp - 24#64 + 8#64) i by
      simp only [Addr.add]; bv_omega] at this
    exact c.hws _ this
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have esp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₄]
    show Y₃.cpu.gpr.rsp + 24#64 = _
    rw [esp₃]
    bv_omega
  refine c.s_ret hK₄ hA₄ hin (lt_len (by decide)) hr₄ (ret_73 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [esp₄]
    exact hrf i hi
  · rw [esp₄]
    unfold imV
    rw [gl_rd (by omega) (by omega), cV_rd (by omega) hsp (.inl (Nat.le_refl _))]
    exact hret
  rintro Z₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  refine k Z₅ t₅ s hK₅ hA₅ hS hr₅ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg₅, esp₄]
    rfl
  · rw [hg₅, hg₄]
    show rdq(imV V X.cpu.gpr a0 s, Y₃.cpu.gpr.rsp + 8#64) = _
    rw [esp₃, show X.cpu.gpr.rsp - 24#64 + 8#64 = X.cpu.gpr.rsp - 16#64 by bv_omega]
    unfold imV
    rw [gl_rd (by bv_omega) (by bv_omega), cV_rbx hsp]
  · rw [hg₅, hg₄]
    show rdq(imV V X.cpu.gpr a0 s, Y₃.cpu.gpr.rsp + 16#64) = _
    rw [esp₃, show X.cpu.gpr.rsp - 24#64 + 16#64 = X.cpu.gpr.rsp - 8 by bv_omega]
    unfold imV
    rw [gl_rd (by bv_omega) (by bv_omega), cV_rbp hsp]
  · rw [hg₅, hg₄, hg₃]
    show Z.cpu.gpr.r12 = _
    rw [h12Z, hg₂, hgY]
    rfl
  · rw [hg₅, hg₄, hg₃]
    show Z.cpu.gpr.r13 = _
    rw [h13Z, hg₂, hgY]
    rfl
  · rw [hg₅, hg₄, hg₃]
    show Z.cpu.gpr.r14 = _
    rw [h14Z, hg₂, hgY]
    rfl
  · rw [hg₅, hg₄, hg₃]
    show Z.cpu.gpr.r15 = _
    rw [h15Z, hg₂, hgY]
    rfl

end FV7z.Ims
