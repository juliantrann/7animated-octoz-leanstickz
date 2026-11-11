import FV7z.Sjs.Cuts
import FV7z.Spec.SigjmpSave
import FV7z.Tun.Inv
import FV7z.Lemmas.Apart
/-!
# `__sigjmp_save` keeps its contract, without a mask to save (PLAN.md G3, startup)

One cut point, the entry. With `savemask` 0 the way to `__sigprocmask` (24) is not taken, and the run ends at the
`ret` (18): `rbx` is back from the frame, `rax` is 0 and `env->__mask_was_saved` is 0 (`Fin`). `sjsRun`: by `Seg.cfg`
the run reaches the `ret` with the registers as at the call, and the contract's `Post` holds of the bytes there.
`sjs_holds`: every call of the code at its place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Sjs FV7z.SigjmpSave
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Sjs

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_18 : pret <+: sjs.drop 18 := by decide +kernel
theorem ret_18 (feat : Features) : Dec feat sjs 18 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 18) (k := 0) (pret_0 feat) w_18 (Nat.zero_le _)

/-- The registers a call keeps are as at the call. -/
def R (s : State) (g : Gprs) : Prop :=
  g.rsp = s.cpu.gpr.rsp ∧ g.rbx = s.cpu.gpr.rbx ∧ g.rbp = s.cpu.gpr.rbp ∧ g.r12 = s.cpu.gpr.r12 ∧
    g.r13 = s.cpu.gpr.r13 ∧ g.r14 = s.cpu.gpr.r14 ∧ g.r15 = s.cpu.gpr.r15

/-- The bytes at the call. -/
abbrev V0 (s : State) : Addr → Byte := s.proc.mm.mem.readByte

/-- At the entry. -/
def I0 (s : State) (g : Gprs) (V : Addr → Byte) : Prop :=
  R s g ∧ g.rsi = s.cpu.gpr.rsi ∧ g.rdi = s.cpu.gpr.rdi ∧ V = V0 s

/-- The invariant at the cut point. -/
def Inv (s : State) (ℓ : Nat) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop := ℓ = 0 ∧ n = 0 ∧ I0 s g V

/-- At the `ret`. -/
def Fin (s : State) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 18 ∧ R s g ∧ g.rax = 0 ∧
    V = Vst (Vst (V0 s) (s.cpu.gpr.rsp - 8#64) (toBytesLE s.cpu.gpr.rbx 8)) (s.cpu.gpr.rdi + 0x40#64)
      (toBytesLE (0 : BitVec 32) 4)

variable {s : State} {F : Footprint} {Wl : List Rgn}

/-- What may be written: the frame and `env->__mask_was_saved`, apart. -/
structure Env (s : State) (F : Footprint) (Wl : List Rgn) : Prop where
  ws : ∀ y, Foot Wl y → Foot F.data y
  fr : ∀ i : Nat, i < 8 → Foot Wl (Addr.add (s.cpu.gpr.rsp - 8#64) i)
  sv : ∀ i : Nat, i < 4 → Foot Wl (Addr.add (s.cpu.gpr.rdi + 0x40#64) i)
  lo : 8 ≤ s.cpu.gpr.rsp.toNat
  fit : (s.cpu.gpr.rdi + 0x40#64).toNat + 4 ≤ 2 ^ 64
  ap : (s.cpu.gpr.rdi + 0x40#64).toNat + 4 ≤ s.cpu.gpr.rsp.toNat - 8 ∨
    s.cpu.gpr.rsp.toNat ≤ (s.cpu.gpr.rdi + 0x40#64).toNat
  ns : s.cpu.gpr.rsi.setWidth 32 = 0#32

theorem vc_0 (hE : Env s F Wl) {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : I0 s g V) :
    W_0 F Wl (fun j' g' _ V' => (∃ m', m' < 0 ∧ Inv s j' m' g' V') ∨ Fin s j' g' V') g f V := by
  obtain ⟨hR, hsi, hdi, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := hR
  obtain rfl : rsi = s.cpu.gpr.rsi := hsi
  obtain rfl : rdi = s.cpu.gpr.rdi := hdi
  obtain rfl : rsp = s.cpu.gpr.rsp := hsp
  obtain rfl : rbx = s.cpu.gpr.rbx := hbx
  wpx [W_0, W_12, o0, o1]
  rw [hE.ns]
  have e8 : (s.cpu.gpr.rsp - 8#64).toNat = s.cpu.gpr.rsp.toNat - 8 := by have := hE.lo; bv_omega
  refine ⟨hE.fr, fun h => absurd h (by decide), fun _ => ⟨hE.sv, fun i hi => hE.ws _ (hE.fr i hi),
    Or.inr ⟨rfl, ⟨by show s.cpu.gpr.rsp - 8#64 + 8#64 = _; bv_omega, ?_, hbp, h12, h13, h14, h15⟩, ?_, rfl⟩⟩⟩
  · show rdq(Vst (Vst (V0 s) (s.cpu.gpr.rsp - 8#64) (toBytesLE s.cpu.gpr.rbx 8)) (s.cpu.gpr.rdi + 0x40#64)
      (toBytesLE (0 : BitVec 32) 4), s.cpu.gpr.rsp - 8#64) = s.cpu.gpr.rbx
    have := hE.lo
    have := hE.fit
    have := hE.ap
    rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; omega) (by omega)
        (by simp only [toBytesLE_length]; omega),
      rd_Vst_self _ _ _ (by simp only [toBytesLE_length]) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · show BitVec.setWidth 64 (BitVec.setWidth 32 rax ^^^ BitVec.setWidth 32 rax) = 0
    rw [BitVec.xor_self]
    rfl

theorem vcAll (hE : Env s F Wl) (ℓ : Nat) :
    ∀ n g f V, Inv s ℓ n g V → Wt ℓ F Wl (fun j' g' _ V' => (∃ m', m' < n ∧ Inv s j' m' g' V') ∨ Fin s j' g' V')
      g f V := by
  rintro n g f V ⟨rfl, rfl, h⟩
  exact vc_0 hE h

variable {prof : Profile} {L : List (Addr × List Byte)} {ra : Addr} {o : Oracle}

/-- A call runs to its return, as the contract says. -/
theorem sjsRun (c : Call prof 8 (fun s => [rSaved s]) (fun _ => []) Pre SigjmpSave.Post sjs_at L s ra o)
    (hin : CodeIn L sjs_at sjs) (t : Nat) :
    Go prof 8 (fun s => [rSaved s]) (fun _ => []) Pre SigjmpSave.Post L s ra o s t := by
  have hp : Pre s := c.call.pre
  have hfit : ∀ r, r ∈ (fp 8 (fun s => [rSaved s]) (fun _ => []) Pre SigjmpSave.Post L s).data → r.Fits :=
    fun r hr => c.foot.fits r (List.mem_append_left _ hr)
  have hfr := hfit (frame s 8) (by simp [Footprint.data, Contract.footprint, fn])
  have hsv := hfit (rSaved s) (by simp [Footprint.data, Contract.footprint, fn])
  have d := ends_of_disjoint (hp.frameApart _ (.head _) (rSaved s) (.head _)) (by simp [frame]) (by simp [rSaved])
  simp only [frame, rSaved, Rgn.Fits] at hfr hsv d
  have e8 : (s.cpu.gpr.rsp - 8#64).toNat = s.cpu.gpr.rsp.toNat - 8 ∧ 8 ≤ s.cpu.gpr.rsp.toNat := by bv_omega
  have hE : Env s (fp 8 (fun s => [rSaved s]) (fun _ => []) Pre SigjmpSave.Post L s)
      (ws 8 (fun s => [rSaved s]) s) := by
    refine ⟨c.toSeg.hws, fun i hi => ⟨below s 8, by simp [ws], ?_⟩, fun i hi => ⟨rSaved s, by simp [ws], ?_⟩,
      e8.2, hsv, by omega, hp.nomask⟩
    · have := toNat_add_of_fits (a := s.cpu.gpr.rsp - 8#64) (n := 8) hi (by omega)
      simp only [below, Rgn.Mem]
      omega
    · have := toNat_add_of_fits (a := s.cpu.gpr.rdi + 0x40#64) (n := 4) hi (by omega)
      simp only [rSaved, Rgn.Mem]
      omega
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => Inv s ℓ n g V)
    (fun j' g' _ V' => Fin s j' g' V') (fun ℓ n g f V h => vcAll hE ℓ n g f V h) ?_ 0 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩, hax, rfl⟩ Y t' hKY hAY hrY rfl rfl
  refine c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_18 _) fun M hM => ?_
  have hAM := c.agreeK hKY hAY hM
  refine ⟨hax, ?_⟩
  show ofBytesLE 32 (readBytes M (s.cpu.gpr.rdi + 0x40#64) 4) = 0
  rw [hAM.read fun i hi => hE.ws _ (hE.sv i hi), rd_Vst_self _ _ _ (by simp only [toBytesLE_length]) hsv]
  exact ofBytesLE_toBytesLE (n := 4) rfl _

/-- `__sigjmp_save`, at its place in `7zzs`, on every processor: every call without a mask to save returns as its
contract says. -/
theorem sjs_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L sjs_at sjs) :
    ImplementsCall prof sjs_at L SigjmpSave.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof sjs_at L (fn 8 (fun s => [rSaved s]) (fun _ => []) Pre SigjmpSave.Post) s₀ ra := hcall
  have hp : Pre s₀ := hcall'.pre
  have hfr : (frame s₀ 8).Fits :=
    hcall'.foot.fits _ (List.mem_append_left _ (by simp [Footprint.data, Contract.footprint, fn]))
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    sjsRun (Call.of hcall' ho (by
      rintro i hi ⟨r, hr, hm⟩
      refine hp.frameApart _ (.head _) r hr _ ?_ hm
      simp only [frame, Rgn.Mem, Rgn.Fits] at hfr ⊢
      have := toNat_add_of_fits (a := s₀.cpu.gpr.rsp) hi (by bv_omega)
      bv_omega)) hin t

end FV7z.Sjs
