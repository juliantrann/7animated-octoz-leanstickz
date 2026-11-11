import FV7z.Dbg.Cuts
import FV7z.Spec.DebugInit
import FV7z.Tun.Inv
/-!
# `_dl_debug_initialize` keeps its contract (PLAN.md G3, startup)

Three cut points: the entry, where `rax` is `&_r_debug` (36), and where the stores after `r_version`'s begin (54),
`rdi` then `ldbase` or the old `r_ldbase`. With the namespace 0 the way through `_dl_ns` (16) is not taken. The run
ends at one of two `ret`s: 92 after the stores (`F92`: `_r_debug` is `W`), 96 with nothing stored (`F96`). `dbgRun`:
by `Seg.cfg` the run reaches a `ret` with the registers as at the call, and the contract's `Post` holds of the bytes
there. `dbg_holds`: every call of the code at its place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Dbg FV7z.DebugInit
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Dbg

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_92 : pret <+: dbg.drop 92 := by decide +kernel
theorem w_96 : pret <+: dbg.drop 96 := by decide +kernel
theorem ret_92 (feat : Features) : Dec feat dbg 92 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 92) (k := 0) (pret_0 feat) w_92 (Nat.zero_le _)
theorem ret_96 (feat : Features) : Dec feat dbg 96 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 96) (k := 0) (pret_0 feat) w_96 (Nat.zero_le _)

/-- The registers a call keeps are as at the call. -/
def R (s : State) (g : Gprs) : Prop :=
  g.rsp = s.cpu.gpr.rsp ∧ g.rbx = s.cpu.gpr.rbx ∧ g.rbp = s.cpu.gpr.rbp ∧ g.r12 = s.cpu.gpr.r12 ∧
    g.r13 = s.cpu.gpr.r13 ∧ g.r14 = s.cpu.gpr.r14 ∧ g.r15 = s.cpu.gpr.r15

/-- The bytes at the call. -/
abbrev V0 (s : State) : Addr → Byte := s.proc.mm.mem.readByte

/-- `r_ldbase` after an initialization. -/
def lb (s : State) : BitVec 64 := if s.cpu.gpr.rdi = 0 then rdq(V0 s, 0x7a84e0#64) else s.cpu.gpr.rdi

/-- `_r_debug` after the stores: `b1` at the version, `b2` at `r_ldbase`, `b3` at `r_brk`, `b4` at `r_map`. -/
def W (U : Addr → Byte) (b1 b2 b3 b4 : List Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst U 0x7a84c0#64 b1) 0x7a84e0#64 b2) 0x7a84d0#64 b3) 0x7a84c8#64 b4

/-- The fields of `_r_debug` after the stores. -/
theorem W_rd (U : Addr → Byte) (b1 b2 b3 b4 : List Byte) (h1 : b1.length = 4) (h2 : b2.length = 8)
    (h3 : b3.length = 8) (h4 : b4.length = 8) :
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84c0#64 4) = b1 ∧
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84c4#64 4) = List.map U (byteAddrs 0x7a84c4#64 4) ∧
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84c8#64 8) = b4 ∧
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84d0#64 8) = b3 ∧
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84d8#64 8) = List.map U (byteAddrs 0x7a84d8#64 8) ∧
    List.map (W U b1 b2 b3 b4) (byteAddrs 0x7a84e0#64 8) = b2 := by
  unfold W
  have p : ∀ (V : Addr → Byte) (a n : Nat) (bs : List Byte) (x m : Nat), bs.length = n → a + n < 2 ^ 64 →
      x + m < 2 ^ 64 → (a + n ≤ x ∨ x + m ≤ a) →
      List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs (BitVec.ofNat 64 x) m) =
        List.map V (byteAddrs (BitVec.ofNat 64 x) m) := by
    intro V a n bs x m hl ha hx h
    subst hl
    exact rd_Vst V _ bs _ m (by bv_omega) (by bv_omega) (by bv_omega)
  have q : ∀ (V : Addr → Byte) (a n : Nat) (bs : List Byte), bs.length = n → a + n < 2 ^ 64 →
      List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs (BitVec.ofNat 64 a) n) = bs :=
    fun V a n bs hl ha => rd_Vst_self V _ bs hl (by bv_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p _ 0x7a84c8 8 b4 0x7a84c0 4 h4 (by decide) (by decide) (by decide),
      p _ 0x7a84d0 8 b3 0x7a84c0 4 h3 (by decide) (by decide) (by decide),
      p _ 0x7a84e0 8 b2 0x7a84c0 4 h2 (by decide) (by decide) (by decide), q _ 0x7a84c0 4 b1 h1 (by decide)]
  · rw [p _ 0x7a84c8 8 b4 0x7a84c4 4 h4 (by decide) (by decide) (by decide),
      p _ 0x7a84d0 8 b3 0x7a84c4 4 h3 (by decide) (by decide) (by decide),
      p _ 0x7a84e0 8 b2 0x7a84c4 4 h2 (by decide) (by decide) (by decide),
      p _ 0x7a84c0 4 b1 0x7a84c4 4 h1 (by decide) (by decide) (by decide)]
  · rw [q _ 0x7a84c8 8 b4 h4 (by decide)]
  · rw [p _ 0x7a84c8 8 b4 0x7a84d0 8 h4 (by decide) (by decide) (by decide), q _ 0x7a84d0 8 b3 h3 (by decide)]
  · rw [p _ 0x7a84c8 8 b4 0x7a84d8 8 h4 (by decide) (by decide) (by decide),
      p _ 0x7a84d0 8 b3 0x7a84d8 8 h3 (by decide) (by decide) (by decide),
      p _ 0x7a84e0 8 b2 0x7a84d8 8 h2 (by decide) (by decide) (by decide),
      p _ 0x7a84c0 4 b1 0x7a84d8 8 h1 (by decide) (by decide) (by decide)]
  · rw [p _ 0x7a84c8 8 b4 0x7a84e0 8 h4 (by decide) (by decide) (by decide),
      p _ 0x7a84d0 8 b3 0x7a84e0 8 h3 (by decide) (by decide) (by decide), q _ 0x7a84e0 8 b2 h2 (by decide)]

/-- At the entry: the namespace is 0. -/
def I0 (s : State) (g : Gprs) (V : Addr → Byte) : Prop :=
  R s g ∧ g.rsi = 0 ∧ g.rdi = s.cpu.gpr.rdi ∧ V = V0 s

/-- At 36: `rax` is `&_r_debug`. -/
def I36 (s : State) (g : Gprs) (V : Addr → Byte) : Prop := I0 s g V ∧ g.rax = 0x7a84c0#64

/-- At 54: the version is stored, `rdi` is the base to store. -/
def I54 (s : State) (g : Gprs) (V : Addr → Byte) : Prop :=
  R s g ∧ g.rsi = 0 ∧ g.rax = 0x7a84c0#64 ∧ g.rdi = lb s ∧ V = Vst (V0 s) 0x7a84c0#64 (toBytesLE (1 : BitVec 32) 4) ∧
    (rdq(V0 s, 0x7a84c8#64) = 0 ∨ s.cpu.gpr.rdi ≠ 0)

/-- The invariant at each cut point, with the number of cut points still to come. -/
def Inv (s : State) (ℓ : Nat) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 2 ∧ I0 s g V) ∨ (ℓ = 36 ∧ n = 1 ∧ I36 s g V) ∨ (ℓ = 54 ∧ n = 0 ∧ I54 s g V)

/-- At the `ret` after the stores. -/
def F92 (s : State) (g : Gprs) (V : Addr → Byte) : Prop :=
  R s g ∧ g.rax = 0x7a84c0#64 ∧ (rdq(V0 s, 0x7a84c8#64) = 0 ∨ s.cpu.gpr.rdi ≠ 0) ∧
    V = W (V0 s) (toBytesLE (1 : BitVec 32) 4) (toBytesLE (lb s) 8) (toBytesLE 0x66e490#64 8)
      (toBytesLE rdq(V0 s, 0x793440#64) 8)

/-- At the `ret` with nothing to do. -/
def F96 (s : State) (g : Gprs) (V : Addr → Byte) : Prop :=
  R s g ∧ g.rax = 0x7a84c0#64 ∧ rdq(V0 s, 0x7a84c8#64) ≠ 0 ∧ s.cpu.gpr.rdi = 0 ∧ V = V0 s

/-- At a `ret`. -/
def Fin (s : State) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop := (j = 92 ∧ F92 s g V) ∨ (j = 96 ∧ F96 s g V)

variable {s : State} {F : Footprint} {Wl : List Rgn}

/-- What may be read and written: `_r_debug`, and the map of namespace 0 read. -/
structure Env (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  dbg : ∀ y : Addr, 0x7a84c0 ≤ y.toNat → y.toNat < 0x7a84c0 + 40 → Foot Wl y
  map : ∀ y : Addr, 0x793440 ≤ y.toNat → y.toNat < 0x793440 + 8 → Foot F.data y

/-- Bytes of `_r_debug`. -/
theorem Env.ft (hE : Env F Wl) {b n : Nat} (h1 : 0x7a84c0 ≤ b) (h2 : b + n ≤ 0x7a84c0 + 40) :
    ∀ i, i < n → Foot Wl (Addr.add (BitVec.ofNat 64 b) i) := by
  intro i hi
  have e : (Addr.add (BitVec.ofNat 64 b) i).toNat = b + i := by simp only [Addr.add]; bv_omega
  exact hE.dbg _ (by omega) (by omega)

theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : I0 s g V) :
    W_0 F Wl (fun j' g' _ V' => (∃ m', m' < 2 ∧ Inv s j' m' g' V') ∨ Fin s j' g' V') g f V := by
  obtain ⟨hR, hsi, hdi, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rsi = 0 := hsi
  wpx [W_0, W_16, o0, o1, Op.shl64]
  exact ⟨fun _ => Or.inl ⟨1, by decide, Or.inr (Or.inl ⟨rfl, rfl, ⟨hR, rfl, hdi, rfl⟩, rfl⟩)⟩,
    fun h => absurd h (by decide)⟩

theorem vc_36 (hE : Env F Wl) {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : I36 s g V) :
    W_36 F Wl (fun j' g' _ V' => (∃ m', m' < 1 ∧ Inv s j' m' g' V') ∨ Fin s j' g' V') g f V := by
  obtain ⟨⟨hR, hsi, hdi, rfl⟩, hax⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rsi = 0 := hsi
  obtain rfl : rax = 0x7a84c0#64 := hax
  obtain rfl : rdi = s.cpu.gpr.rdi := hdi
  wpx [W_36, W_104, W_115, W_43, W_48, o2, o3, o4, o6, o7, Op.cmpmi, Op.lda]
  simp only [BitVec.reduceAdd]
  refine ⟨fun i hi => hE.ws _ (hE.ft (by decide) (by decide) i hi), fun hz => ?_, fun hz => ?_⟩
  · have hz' : rdq(V0 s, 0x7a84c8#64) = 0 := of_decide_eq_true hz
    refine ⟨hE.ft (by decide) (by decide), fun hd => ?_, fun hd => ?_⟩
    · have hd' : s.cpu.gpr.rdi ≠ 0 := by simpa using hd
      exact Or.inl ⟨0, by decide, Or.inr (Or.inr ⟨rfl, rfl, hR, rfl, rfl, by simp only [lb, hd', ↓reduceIte],
        rfl, Or.inl hz'⟩)⟩
    · have hd' : s.cpu.gpr.rdi = 0 := by simpa using hd
      refine ⟨fun i hi => hE.ws _ (hE.ft (by decide) (by decide) i hi), ?_⟩
      refine Or.inl ⟨0, by decide, Or.inr (Or.inr ⟨rfl, rfl, hR, rfl, rfl, ?_, rfl, Or.inl hz'⟩)⟩
      show rdq(Vst (V0 s) 0x7a84c0#64 (toBytesLE (1 : BitVec 32) 4), 0x7a84e0#64) = lb s
      rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
        (by simp only [toBytesLE_length]; decide)]
      simp only [lb, hd', ↓reduceIte]
  · have hz' : rdq(V0 s, 0x7a84c8#64) ≠ 0 := of_decide_eq_false hz
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · have hd' : s.cpu.gpr.rdi = 0 := by simpa using hd
      exact Or.inr (Or.inr ⟨rfl, hR, rfl, hz', hd', rfl⟩)
    · have hd' : s.cpu.gpr.rdi ≠ 0 := by simpa using hd
      exact ⟨hE.ft (by decide) (by decide), Or.inl ⟨0, by decide, Or.inr (Or.inr ⟨rfl, rfl, hR, rfl, rfl,
        by simp only [lb, hd', ↓reduceIte], rfl, Or.inr hd'⟩)⟩⟩

theorem vc_54 (hE : Env F Wl) {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : I54 s g V) :
    W_54 F Wl (fun j' g' _ V' => (∃ m', m' < 0 ∧ Inv s j' m' g' V') ∨ Fin s j' g' V') g f V := by
  obtain ⟨hR, hsi, hax, hdi, rfl, hc⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rsi = 0 := hsi
  obtain rfl : rax = 0x7a84c0#64 := hax
  obtain rfl : rdi = lb s := hdi
  wpx [W_54, o5, Op.shl64]
  have e0 : (0x793440#64 + (0 : BitVec 64) <<< 4) = 0x793440#64 := by decide
  simp only [BitVec.reduceAdd, e0]
  have e1 : rdq(Vst (Vst (V0 s) 0x7a84c0#64 (toBytesLE (1 : BitVec 32) 4)) 0x7a84e0#64 (toBytesLE (lb s) 8),
      0x793440#64) = rdq(V0 s, 0x793440#64) := by
    rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
        (by simp only [toBytesLE_length]; decide),
      rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
        (by simp only [toBytesLE_length]; decide)]
  refine ⟨hE.ft (by decide) (by decide), fun _ => ⟨fun i hi => ?_, hE.ft (by decide) (by decide),
    hE.ft (by decide) (by decide), Or.inr (Or.inl ⟨rfl, hR, rfl, hc, ?_⟩)⟩⟩
  · have e : (Addr.add 0x793440#64 i).toNat = 0x793440 + i := by simp only [Addr.add]; bv_omega
    exact hE.map _ (by omega) (by omega)
  · unfold W
    rw [e1]

theorem vcAll (hE : Env F Wl) (ℓ : Nat) :
    ∀ n g f V, Inv s ℓ n g V → Wt ℓ F Wl (fun j' g' _ V' => (∃ m', m' < n ∧ Inv s j' m' g' V') ∨ Fin s j' g' V')
      g f V := by
  rintro n g f V (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩)
  · exact vc_0 h
  · exact vc_36 hE h
  · exact vc_54 hE h

variable {prof : Profile} {L : List (Addr × List Byte)} {ra : Addr} {o : Oracle}

/-- A call runs to its return, as the contract says. -/
theorem dbgRun (c : Call prof 0 (fun _ => [rDebug]) reads Pre DebugInit.Post dbg_at L s ra o)
    (hin : CodeIn L dbg_at dbg) (t : Nat) :
    Go prof 0 (fun _ => [rDebug]) reads Pre DebugInit.Post L s ra o s t := by
  have hE : Env (fp 0 (fun _ => [rDebug]) reads Pre DebugInit.Post L s) (ws 0 (fun _ => [rDebug]) s) :=
    ⟨c.toSeg.hws, fun y h1 h2 => ⟨rDebug, by simp [ws], h1, h2⟩,
      fun y h1 h2 => ⟨rLoaded, by simp [Footprint.data, Contract.footprint, fn, reads], h1, h2⟩⟩
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => Inv s ℓ n g V)
    (fun j' g' _ V' => Fin s j' g' V') (fun ℓ n g f V h => vcAll hE ℓ n g f V h) ?_ 2 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    (Or.inl ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, c.call.pre.ns, rfl, rfl⟩)
  rintro j' g fl V' (⟨rfl, ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩, hax, hc, rfl⟩ |
    ⟨rfl, ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩, hax, hnz, hdi, rfl⟩) Y t' hKY hAY hrY rfl rfl
  · refine c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_92 _) fun M hM => ?_
    have hAM := c.agreeK hKY hAY hM
    have rd : ∀ (b n : Nat), 0x7a84c0 ≤ b → b + n ≤ 0x7a84c0 + 40 → readBytes M (BitVec.ofNat 64 b) n =
        List.map _ (byteAddrs (BitVec.ofNat 64 b) n) :=
      fun b n h1 h2 => hAM.read fun i hi => hE.ws _ (hE.ft h1 h2 i hi)
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := W_rd (V0 s) (toBytesLE (1 : BitVec 32) 4) (toBytesLE (lb s) 8)
      (toBytesLE 0x66e490#64 8) (toBytesLE rdq(V0 s, 0x793440#64) 8) (by simp only [toBytesLE_length])
      (by simp only [toBytesLE_length]) (by simp only [toBytesLE_length]) (by simp only [toBytesLE_length])
    refine ⟨hax, fun h1 h2 => hc.elim (fun h => absurd h h1) (fun h => absurd h2 h), fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (congrArg (ofBytesLE 32) ((rd 0x7a84c0 4 (by decide) (by decide)).trans w1)).trans
        (ofBytesLE_toBytesLE (n := 4) rfl _)
    · exact (rd 0x7a84c4 4 (by decide) (by decide)).trans w2
    · exact (congrArg (ofBytesLE 64) ((rd 0x7a84c8 8 (by decide) (by decide)).trans w3)).trans
        (ofBytesLE_toBytesLE (n := 8) rfl _)
    · exact (congrArg (ofBytesLE 64) ((rd 0x7a84d0 8 (by decide) (by decide)).trans w4)).trans
        (ofBytesLE_toBytesLE (n := 8) rfl _)
    · exact (rd 0x7a84d8 8 (by decide) (by decide)).trans w5
    · exact (congrArg (ofBytesLE 64) ((rd 0x7a84e0 8 (by decide) (by decide)).trans w6)).trans
        (ofBytesLE_toBytesLE (n := 8) rfl _)
  · refine c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_96 _) fun M hM => ?_
    have hAM := c.agreeK hKY hAY hM
    exact ⟨hax, fun _ _ => hAM.read fun i hi => hE.ws _ (hE.ft (b := 0x7a84c0) (by decide) (by decide) i hi),
      fun h => h.elim (fun h => absurd h hnz) (fun h => absurd hdi h)⟩

/-- `_dl_debug_initialize`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem dbg_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L dbg_at dbg) :
    ImplementsCall prof dbg_at L DebugInit.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof dbg_at L (fn 0 (fun _ => [rDebug]) reads Pre DebugInit.Post) s₀ ra := hcall
  have hp : Pre s₀ := hcall'.pre
  have hfr : (frame s₀ 0).Fits :=
    hcall'.foot.fits _ (List.mem_append_left _ (by simp [Footprint.data, Contract.footprint, fn]))
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    dbgRun (Call.of hcall' ho (by
      rintro i hi ⟨r, hr, hm⟩
      refine hp.frameApart _ (.head _) r hr _ ?_ hm
      simp only [frame, Rgn.Mem, Rgn.Fits] at hfr ⊢
      have := toNat_add_of_fits (a := s₀.cpu.gpr.rsp) hi (by bv_omega)
      bv_omega)) hin t

end FV7z.Dbg
