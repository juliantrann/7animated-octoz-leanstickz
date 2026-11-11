import FV7z.Auxv.Vc
import FV7z.Auxv.Ret
import FV7z.Spec.AuxInit
import FV7z.Lemmas.Apart
/-!
# `_dl_aux_init` keeps its contract (PLAN.md G3, startup)

`ctx`: the call's context, from the state at the call and the contract's parameter (the vector's entries `X`). From
the contract's precondition and footprint (`FV7z/Spec/AuxInit.lean`): `ctx_ok`, `ctx_env`. `auxRun`: by `Seg.cfg` over
the 31 cut points (`spAll`, `vcAll`) the run reaches the `ret` with `Ret`: the callee-saved registers as at the call,
`_dl_auxv` the vector's address, and the variables as the entries set them. `aux_holds`: every call of the code at its
place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Auxv FV7z.AuxInit
namespace FV7z.Auxv

/-! ## The vector as a list -/

theorem getD_mem {X : List (BitVec 64 × BitVec 64)} {i : Nat} (hi : i < X.length) : X.getD i (0, 0) ∈ X := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_get {X : List (BitVec 64 × BitVec 64)} {i : Nat} (hi : i < X.length) : X.getD i (0, 0) = X[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- 4 bytes of the table read whole. -/
theorem sub_read (V : Addr → Byte) (a : Addr) (l : List Byte) (h : List.map V (byteAddrs a 124) = l) (k : Nat)
    (hk : k < 31) : List.map V (byteAddrs (Addr.add a (4 * k)) 4) = (l.drop (4 * k)).take 4 := by
  subst h
  apply List.ext_getElem
  · simp [byteAddrs]; omega
  · intro i h1 h2
    have hi : i < 4 := by simpa [byteAddrs] using h1
    simp [byteAddrs, addr_add_add]

/-- The call's context, from the state at the call. -/
def ctx (X : List (BitVec 64 × BitVec 64)) (s : State) : Ctx where
  sp := s.cpu.gpr.rsp - 104#64
  rbx := s.cpu.gpr.rbx
  rbp := s.cpu.gpr.rbp
  r12 := s.cpu.gpr.r12
  r13 := s.cpu.gpr.r13
  r14 := s.cpu.gpr.r14
  r15 := s.cpu.gpr.r15
  av := s.cpu.gpr.rdi
  N := X.length
  ty i := (X.getD i (0, 0)).1
  val i := (X.getD i (0, 0)).2
  sn := X.findIdx (fun e => e.1 == 23)
  vs n := (X.take n).foldl step (vars s.proc.mm.mem)
  V0 := s.proc.mm.mem.readByte

variable {X : List (BitVec 64 × BitVec 64)} {s : State}

theorem jt_eq : jumpTable = aux_jt := by decide

theorem ctx_ok (hp : Pre X s) (hfr : (frame s 104).Fits) (hfit : (rVec X s).Fits) : (ctx X s).Ok := by
  have offR : ∀ r ∈ reads X s, 0 < r.len → Off (ctx X s) r.base.toNat r.len := by
    intro r hr h0
    have d := ends_of_disjoint (hp.apart _ (.head _) r hr) (by simp [frame]) h0
    simp only [frame] at d
    simp only [Off, ctx]
    omega
  have offG : ∀ r ∈ globals, 0 < r.len → Off (ctx X s) r.base.toNat r.len := by
    intro r hr h0
    have d := ends_of_disjoint (hp.frameApart _ (.head _) r hr) (by simp [frame]) h0
    simp only [frame] at d
    simp only [Off, ctx]
    omega
  obtain ⟨e, he, h23⟩ := hp.secure
  have hsn : X.findIdx (fun e => e.1 == 23) < X.length :=
    List.findIdx_lt_length_of_exists ⟨e, he, by simp [h23]⟩
  exact {
    hsp := hfr
    hfit := hfit
    aAv := offR _ (.head _) (by show 0 < 16 * X.length + 8; omega)
    xAv := by
      have d := ends_of_disjoint (hp.apart ⟨0x7a8540, 8⟩ (.tail _ (.head _)) (rVec X s) (.head _)) (by decide)
        (by show 0 < 16 * X.length + 8; omega)
      simp only [rVec] at d
      show s.cpu.gpr.rdi.toNat + (16 * X.length + 8) ≤ 0x7a8540 ∨ 0x7a8548 ≤ s.cpu.gpr.rdi.toNat
      have e : (0x7a8540 : Addr).toNat = 0x7a8540 := by decide
      rw [e] at d
      omega
    hty := fun n hn => (hp.types n hn).trans (by rw [← getD_get hn]; rfl)
    hval := fun n hn => (hp.values n hn).trans (by rw [← getD_get hn]; rfl)
    hnz := fun n hn => hp.nonNull _ (getD_mem hn)
    hend := hp.vecEnd
    hsn := hsn
    hsec := by
      have := List.findIdx_getElem (w := hsn)
      show (X.getD (X.findIdx (fun e => e.1 == 23)) (0, 0)).1 = 23
      rw [getD_get hsn]
      simpa using this
    aJt := offR _ (.tail _ (.head _)) (by decide)
    hjt := fun k hk => by
      exact congrArg (ofBytesLE 32) (sub_read s.proc.mm.mem.readByte 0x6f3660#64 _ (hp.table.trans jt_eq) k hk)
    hvs := fun n hn => by
      show ((X.take (n + 1)).foldl step (vars s.proc.mm.mem)) =
        step ((X.take n).foldl step (vars s.proc.mm.mem)) ((X.getD n (0, 0)).1, (X.getD n (0, 0)).2)
      rw [List.take_succ_eq_append_getElem hn, List.foldl_append, getD_get hn]; rfl
    hgl := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    oAx := offG ⟨0x7a8540, 8⟩ (by simp [globals]) (by decide)
    oPs := offG ⟨0x7933d8, 8⟩ (by simp [globals]) (by decide)
    oCk := offG ⟨0x7a85c0, 4⟩ (by simp [globals]) (by decide)
    oPh := offG ⟨0x7a8580, 8⟩ (by simp [globals]) (by decide)
    oPn := offG ⟨0x7a8598, 8⟩ (by simp [globals]) (by decide)
    oPl := offG ⟨0x7a8548, 8⟩ (by simp [globals]) (by decide)
    oHw := offG ⟨0x7a4ac8, 8⟩ (by simp [globals]) (by decide)
    oH2 := offG ⟨0x7a4ac0, 8⟩ (by simp [globals]) (by decide)
    oSy := offG ⟨0x7a8508, 8⟩ (by simp [globals]) (by decide)
    oFp := offG ⟨0x7933cc, 2⟩ (by simp [globals]) (by decide)
    oSe := offG ⟨0x791ce0, 4⟩ (by simp [globals]) (by decide)
    oDe := offG ⟨0x7a85c4, 4⟩ (by simp [globals]) (by decide)
    oRa := offG ⟨0x791ca0, 8⟩ (by simp [globals]) (by decide) }

variable {prof : Profile} {L : List (Addr × List Byte)} {ra e : Addr} {o : Oracle}

set_option linter.unusedVariables false in
theorem ctx_env (c : Call prof 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) e L s ra o) (hK : (ctx X s).Ok) :
    Env (ctx X s) (fp 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) L s) (ws 104 (fun _ => globals) s) := by
  have rd : ∀ r ∈ reads X s, ∀ y, r.Mem y →
      Foot (fp 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) L s).data y :=
    fun r hr y hy => ⟨r, by simp [Footprint.data, Contract.footprint, fn, hr], hy⟩
  exact ⟨c.hws, fun y a1 a2 => ⟨below s 104, .head _, ⟨a1, a2⟩⟩, fun r hr y hy => ⟨r, .tail _ hr, hy⟩,
    fun y a1 a2 => rd _ (.tail _ (.head _)) y ⟨a1, a2⟩, fun y a1 a2 => rd _ (.head _) y ⟨a1, a2⟩⟩

/-- The variables in memory that agrees with `V` on the footprint. -/
theorem vars_of {F : Footprint} {Wl : List Rgn} {K : Ctx} (hE : Env K F Wl) {M : Memory} {V : Addr → Byte}
    (hA : Agree F M V) {w : Vars} (hG : Gl V w) (hax : rdq(V, 0x7a8540#64) = K.av) :
    word M 0x7a8540 = K.av ∧ vars M = w := by
  have rd : ∀ (a n : Nat), (⟨BitVec.ofNat 64 a, n⟩ : Rgn) ∈ globals → a + n ≤ 2 ^ 64 →
      readBytes M (BitVec.ofNat 64 a) n = List.map V (byteAddrs (BitVec.ofNat 64 a) n) :=
    fun a n hm hn => hA.read fun i hi => hE.ws _ (hE.wg a n hm hn i hi)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := hG
  refine ⟨(congrArg (ofBytesLE 64) (rd 0x7a8540 8 (by simp [globals]) (by decide))).trans hax, ?_⟩
  have e1 := (congrArg (ofBytesLE 64) (rd 0x7933d8 8 (by simp [globals]) (by decide))).trans g1
  have e2 := (congrArg (ofBytesLE 32) (rd 0x7a85c0 4 (by simp [globals]) (by decide))).trans g2
  have e3 := (congrArg (ofBytesLE 64) (rd 0x7a8580 8 (by simp [globals]) (by decide))).trans g3
  have e4 := (congrArg (ofBytesLE 64) (rd 0x7a8598 8 (by simp [globals]) (by decide))).trans g4
  have e5 := (congrArg (ofBytesLE 64) (rd 0x7a8548 8 (by simp [globals]) (by decide))).trans g5
  have e6 := (congrArg (ofBytesLE 64) (rd 0x7a4ac8 8 (by simp [globals]) (by decide))).trans g6
  have e7 := (congrArg (ofBytesLE 64) (rd 0x7a4ac0 8 (by simp [globals]) (by decide))).trans g7
  have e8 := (congrArg (ofBytesLE 64) (rd 0x7a8508 8 (by simp [globals]) (by decide))).trans g8
  have e9 := (congrArg (ofBytesLE 16) (rd 0x7933cc 2 (by simp [globals]) (by decide))).trans g9
  have e10 := (congrArg (ofBytesLE 32) (rd 0x791ce0 4 (by simp [globals]) (by decide))).trans g10
  have e11 := (congrArg (ofBytesLE 32) (rd 0x7a85c4 4 (by simp [globals]) (by decide))).trans g11
  have e12 := (congrArg (ofBytesLE 64) (rd 0x791ca0 8 (by simp [globals]) (by decide))).trans g12
  show Vars.mk _ _ _ _ _ _ _ _ _ _ _ _ = w
  obtain ⟨⟩ := w
  exact congr (congr (congr (congr (congr (congr (congr (congr (congr (congr (congr (congrArg Vars.mk e1) e2) e3) e4) e5)
    e6) e7) e8) e9) e10) e11) e12

/-- A call runs to its return, as the contract says. -/
theorem auxRun (c : Call prof 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) aux_at L s ra o)
    (hin : CodeIn L aux_at aux) (t : Nat) :
    Go prof 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) L s ra o s t := by
  have hp : Pre X s := c.call.pre
  have hfit : ∀ r, r ∈ (fp 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X) L s).data → r.Fits :=
    fun r hr => c.foot.fits r (List.mem_append_left _ hr)
  have hfr := hfit (frame s 104) (by simp [Footprint.data, Contract.footprint, fn])
  have hK := ctx_ok hp hfr (hfit (rVec X s) (by simp [Footprint.data, Contract.footprint, fn, reads]))
  have hE := ctx_env c hK
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => InvT (ctx X s) ℓ n g V)
    (fun j' g' _ V' => j' = 493 ∧ Ret (ctx X s) g' V') (fun ℓ n g f V h => vcAll hK hE ℓ n g f V h) ?_ _ 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨by show s.cpu.gpr.rsp = s.cpu.gpr.rsp - 104#64 + 104#64; bv_omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15, hG, hax, -⟩ Y t' hKY hAY hrY rfl rfl
  refine c.ret hKY ⟨hbx, hsp.trans ?_, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_493 _)
    fun M hM => ?_
  · show s.cpu.gpr.rsp - 104#64 + 104#64 = s.cpu.gpr.rsp
    bv_omega
  · obtain ⟨p1, p2⟩ := vars_of hE (c.agreeK hKY hAY hM) hG hax
    refine ⟨p1, p2.trans ?_⟩
    show (X.take X.length).foldl step (vars s.proc.mm.mem) = X.foldl step (vars s.proc.mm.mem)
    rw [List.take_length]

/-- `_dl_aux_init`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem aux_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L aux_at aux)
    (X : List (BitVec 64 × BitVec 64)) : ImplementsCall prof aux_at L (AuxInit.contract X) := by
  intro s₀ ra hcall
  have hcall' : CallOf prof aux_at L (fn 104 (fun _ => globals) (reads X) (Pre X) (AuxInit.Post X)) s₀ ra := hcall
  have hp : Pre X s₀ := hcall'.pre
  have hfr : (frame s₀ 104).Fits :=
    hcall'.foot.fits _ (List.mem_append_left _ (by simp [Footprint.data, Contract.footprint, fn]))
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    auxRun (Call.of hcall' ho (by
      rintro i hi ⟨r, hr, hm⟩
      refine hp.frameApart _ (.head _) r hr _ ?_ hm
      simp only [frame, Rgn.Mem, Rgn.Fits] at hfr ⊢
      have := toNat_add_of_fits (a := s₀.cpu.gpr.rsp) hi (by bv_omega)
      bv_omega)) hin t

end FV7z.Auxv
