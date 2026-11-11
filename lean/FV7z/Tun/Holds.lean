import FV7z.Tun.Vc
import FV7z.Tun.Ret
import FV7z.Spec.Tunables
import FV7z.Lemmas.Apart
/-!
# `__tunables_init` keeps its contract (PLAN.md G3, startup)

`ctx`: the call's context, from the state at the call and the contract's parameters (the environment `E`, the
aliases `A`). From the contract's precondition and footprint (`FV7z/Spec/Tunables.lean`): `ctx_ok`, `ctx_env`.
`tinRun`: by `Seg.cfg` over the 13 cut points (`spAll`, `vcAll`) the run reaches the `ret` with `Ret`, the
callee-saved registers as at the call. `tin_holds`: every call of the code at its place in `7zzs`, on every processor,
returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Tun
namespace FV7z.Tun

/-! ## Strings as lists -/

/-- The `k`-th byte of a string with its 0. -/
def sz (l : List Byte) (k : Nat) : Byte := (l ++ [0]).getD k 0

theorem sz_len (l : List Byte) : sz l l.length = 0 := by simp [sz]

theorem sz_lt {l : List Byte} {k : Nat} (h : k < l.length) : sz l k = l[k] := by
  simp [sz, List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getElem?_eq_getElem h]

theorem sz_append_lt {l x : List Byte} {k : Nat} (h : k < l.length) : sz (l ++ x) k = sz l k := by
  rw [sz_lt h, sz_lt (by simp; omega), List.getElem_append_left h]

theorem sz_append_len (l : List Byte) (b : Byte) : sz (l ++ [b]) l.length = b := by
  rw [sz_lt (by simp)]; simp

/-- The `k`-th of `n` bytes read. -/
theorem readBytes_at {m : Memory} {a : Addr} {n k : Nat} {l : List Byte} (h : readBytes m a n = l) (hk : k < n) :
    m.readByte (a.add k) = l.getD k 0 := by
  subst h
  simp [readBytes, byteAddrs, List.getD_eq_getElem?_getD, hk]

/-- A byte of a C string. -/
theorem cstr_at {m : Memory} {p : Addr} {bs : List Byte} (h : Tunables.CStr m p bs) {k : Nat} (hk : k ≤ bs.length) :
    m.readByte (p.add k) = sz bs k :=
  readBytes_at h.2 (by omega)

/-- A string without a 0 whose bytes are the first of another's is a prefix of it. -/
theorem prefix_of_sz {p l : List Byte} (hp : 0 ∉ p) (h : ∀ k, k < p.length → sz l k = sz p k) : p <+: l := by
  have hle : p.length ≤ l.length := by
    rcases Nat.lt_or_ge l.length p.length with hlt | hge
    · have := h l.length hlt
      rw [sz_len, sz_lt hlt] at this
      exact absurd (this ▸ List.getElem_mem hlt) hp
    · exact hge
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    have := h k h1
    rw [sz_lt h1, sz_lt (by omega)] at this
    simp [this]

/-! ## The context -/

/-- A bound of the strings' lengths. -/
def lmaxOf (E : List (Addr × List Byte)) : Nat := E.foldr (fun e n => max e.2.length n) 0

theorem le_lmaxOf {E : List (Addr × List Byte)} {e : Addr × List Byte} (h : e ∈ E) : e.2.length ≤ lmaxOf E := by
  induction E with
  | nil => cases h
  | cons x xs ih =>
    simp only [lmaxOf, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The length of the alias at `p`. -/
def alenOf (A : List (Addr × List Byte)) (p : Addr) : Nat :=
  ((A.find? (fun a => a.1 == p)).map (·.2.length)).getD 0

theorem alenOf_mem {A : List (Addr × List Byte)} {p : Addr} (h : ∃ a ∈ A, a.1 = p) :
    ∃ a ∈ A, a.1 = p ∧ alenOf A p = a.2.length := by
  obtain ⟨a0, h0, e0⟩ := h
  cases hf : A.find? (fun a => a.1 == p) with
  | none => exact absurd e0 (by simpa using List.find?_eq_none.1 hf a0 h0)
  | some a => exact ⟨a, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, by simp [alenOf, hf]⟩

theorem getD_mem {E : List (Addr × List Byte)} {i : Nat} (hi : i < E.length) : E.getD i (0, []) ∈ E := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_get {E : List (Addr × List Byte)} {i : Nat} (hi : i < E.length) : E.getD i (0, []) = E[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The call's context, from the state at the call. -/
def ctx (A E : List (Addr × List Byte)) (s : State) : Ctx where
  sp := s.cpu.gpr.rsp - 104#64
  rbx := s.cpu.gpr.rbx
  rbp := s.cpu.gpr.rbp
  r12 := s.cpu.gpr.r12
  r13 := s.cpu.gpr.r13
  r14 := s.cpu.gpr.r14
  r15 := s.cpu.gpr.r15
  envp := s.cpu.gpr.rdi
  N := E.length
  ptr i := (E.getD i (0, [])).1
  ez i := sz (E.getD i (0, [])).2
  len i := (E.getD i (0, [])).2.length
  lmax := lmaxOf E
  aq t := Tunables.aliasPtr s.proc.mm.mem t
  az t k := s.proc.mm.mem.readByte ((Tunables.aliasPtr s.proc.mm.mem t).add k)
  alen t := alenOf A (Tunables.aliasPtr s.proc.mm.mem t)
  B := 26 * (lmaxOf E + 10) + 30 + lmaxOf E
  C := lmaxOf E + 10
  V0 := s.proc.mm.mem.readByte

variable {A E : List (Addr × List Byte)} {s : State}

theorem mem_reads_env {e : Addr × List Byte} (h : e ∈ E) : Tunables.rStr e ∈ Tunables.reads A E s := by
  simp only [Tunables.reads, List.mem_cons, List.mem_append, List.mem_map]
  exact .inr (.inr (.inr (.inr (.inl ⟨e, h, rfl⟩))))

theorem mem_reads_al {a : Addr × List Byte} (h : a ∈ A) : Tunables.rStr a ∈ Tunables.reads A E s := by
  simp only [Tunables.reads, List.mem_cons, List.mem_append, List.mem_map]
  exact .inr (.inr (.inr (.inr (.inr ⟨a, h, rfl⟩))))

theorem gz_sz : ∀ k, k < 15 → sz (Tunables.glibcTunables ++ [0x3d]) k = if k < 14 then gz k else 61 := by decide
theorem gz_rd : ∀ k, k < 15 → (Tunables.glibcTunables ++ [0]).getD k 0 = gz k := by decide

theorem ctx_ok (hp : Tunables.Pre A E s) (hfr : (frame s 104).Fits) (hfit : ∀ r ∈ Tunables.reads A E s, r.Fits) :
    (ctx A E s).Ok := by
  have off : ∀ r ∈ Tunables.reads A E s, 0 < r.len → Off (ctx A E s) r.base.toNat r.len := by
    intro r hr h0
    have d := ends_of_disjoint (hp.apart _ (.head _) r hr) (by simp [frame]) h0
    simp only [frame] at d
    simp only [Off, ctx]
    omega
  have al : ∀ t, t < 26 → (ctx A E s).aq t ≠ 0 → ∃ a ∈ A, a.1 = Tunables.aliasPtr s.proc.mm.mem t ∧
      alenOf A (Tunables.aliasPtr s.proc.mm.mem t) = a.2.length :=
    fun t ht hq => alenOf_mem ((hp.alias t ht).resolve_left hq)
  exact {
    hsp := hfr
    hC := rfl
    hB := rfl
    hsec := (congrArg (ofBytesLE 32) hp.secure).trans (by decide)
    aSec := off _ (.head _) (by decide)
    hG := fun k hk => (readBytes_at hp.name hk).trans (gz_rd k hk)
    aG := off _ (.tail _ (.head _)) (by decide)
    hfit := hfit _ (.tail _ (.tail _ (.tail _ (.head _))))
    aEnv := off _ (.tail _ (.tail _ (.tail _ (.head _)))) (by show 0 < 8 * (E.length + 1); omega)
    henv := fun i hi => (hp.envp i hi).trans (by rw [← getD_get hi]; rfl)
    hend := hp.envEnd
    hnz := fun i hi => hp.nonNull _ (getD_mem hi)
    sfit := fun i hi => by
      have := hfit _ (mem_reads_env (A := A) (s := s) (getD_mem hi))
      simp only [Rgn.Fits, Tunables.rStr] at this
      simp only [ctx]; omega
    aStr := fun i hi => by
      have := off _ (mem_reads_env (A := A) (s := s) (getD_mem hi)) (Nat.succ_pos _)
      simp only [Off, Tunables.rStr] at this ⊢
      simp only [ctx] at this ⊢; omega
    hstr := fun i hi k hk => cstr_at (hp.strings _ (getD_mem hi)) hk
    hz := fun i hi => sz_len _
    hlen := fun i hi => le_lmaxOf (getD_mem hi)
    aList := off _ (.tail _ (.tail _ (.head _))) (by decide)
    hal := fun t ht => rfl
    afit := fun t ht hq => by
      obtain ⟨a, ha, e1, e2⟩ := al t ht hq
      have := hfit _ (mem_reads_al (E := E) (s := s) ha)
      simp only [Rgn.Fits, Tunables.rStr] at this
      show (Tunables.aliasPtr s.proc.mm.mem t).toNat + alenOf A (Tunables.aliasPtr s.proc.mm.mem t) + 1 ≤ 2 ^ 64
      rw [e2, ← e1]; omega
    aAl := fun t ht hq => by
      obtain ⟨a, ha, e1, e2⟩ := al t ht hq
      have := off _ (mem_reads_al (E := E) (s := s) ha) (Nat.succ_pos _)
      simp only [Off, Tunables.rStr] at this
      show (ctx A E s).sp.toNat + 104 ≤ (Tunables.aliasPtr s.proc.mm.mem t).toNat ∨
        (Tunables.aliasPtr s.proc.mm.mem t).toNat + (alenOf A (Tunables.aliasPtr s.proc.mm.mem t) + 1) ≤
          (ctx A E s).sp.toNat
      rw [e2, ← e1]; exact this
    hastr := fun t ht hq k hk => rfl
    haz := fun t ht hq => by
      obtain ⟨a, ha, e1, e2⟩ := al t ht hq
      show s.proc.mm.mem.readByte ((Tunables.aliasPtr s.proc.mm.mem t).add
        (alenOf A (Tunables.aliasPtr s.proc.mm.mem t))) = 0
      rw [e2, ← e1, cstr_at (hp.aliases a ha) (Nat.le_refl _)]
      exact sz_len _
    hanz := fun t ht hq k hk => by
      obtain ⟨a, ha, e1, e2⟩ := al t ht hq
      have hk' : k < a.2.length := by rw [← e2]; exact hk
      show s.proc.mm.mem.readByte ((Tunables.aliasPtr s.proc.mm.mem t).add k) ≠ 0
      rw [← e1, cstr_at (hp.aliases a ha) (Nat.le_of_lt hk'), sz_lt hk']
      exact fun h => (hp.aliases a ha).1 (h ▸ List.getElem_mem hk')
    noG := fun i hi h h61 => by
      refine hp.noTunables _ (getD_mem hi) (prefix_of_sz (by decide) fun k hk => ?_)
      have hk' : k < 15 := hk
      rw [gz_sz k hk']
      split
      · next h14 => exact h k h14
      · next h14 => obtain rfl : k = 14 := by omega
                    exact h61
    noA := fun i hi t ht hq h h61 => by
      obtain ⟨a, ha, e1, e2⟩ := al t ht hq
      refine hp.noAlias a ha _ (getD_mem hi) (prefix_of_sz ?_ fun k hk => ?_)
      · have := (hp.aliases a ha).1
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨this, by decide⟩
      · have hk' : k < a.2.length + 1 := by simpa using hk
        rcases Nat.lt_or_ge k a.2.length with hlt | hge
        · have := h k (by show k < alenOf A (Tunables.aliasPtr s.proc.mm.mem t); rw [e2]; exact hlt)
          rw [sz_append_lt hlt, ← cstr_at (hp.aliases a ha) (Nat.le_of_lt hlt), e1]
          exact this
        · obtain rfl : k = a.2.length := by omega
          rw [sz_append_len]
          have h61' : (ctx A E s).ez i (alenOf A (Tunables.aliasPtr s.proc.mm.mem t)) = 61 := h61
          rw [e2] at h61'
          exact h61' }

variable {prof : Profile} {L : List (Addr × List Byte)} {ra e : Addr} {o : Oracle}

set_option linter.unusedVariables false in
theorem ctx_env (c : Call prof 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) e L s ra o) (hK : (ctx A E s).Ok) :
    Env (ctx A E s) (fp 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) L s) (ws 104 (fun _ => []) s) := by
  have hp : Tunables.Pre A E s := c.call.pre
  have rd : ∀ r ∈ Tunables.reads A E s, ∀ y, r.Mem y → Foot (fp 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) L s).data y :=
    fun r hr y hy => ⟨r, by simp [Footprint.data, Contract.footprint, fn, hr], hy⟩
  refine ⟨c.hws, fun y a1 a2 => ⟨below s 104, .head _, ⟨a1, a2⟩⟩, fun y a1 a2 => rd _ (.head _) y ⟨a1, a2⟩,
    fun y a1 a2 => rd _ (.tail _ (.head _)) y ⟨a1, a2⟩, fun y a1 a2 => rd _ (.tail _ (.tail _ (.head _))) y ⟨a1, a2⟩,
    fun y a1 a2 => rd _ (.tail _ (.tail _ (.tail _ (.head _)))) y ⟨a1, a2⟩,
    fun i hi y a1 a2 => rd _ (mem_reads_env (getD_mem hi)) y ⟨a1, Nat.add_assoc _ _ _ ▸ a2⟩, fun t ht hq y a1 a2 => ?_⟩
  obtain ⟨a, ha, e1, e2⟩ := alenOf_mem ((hp.alias t ht).resolve_left hq)
  have a1' : (Tunables.aliasPtr s.proc.mm.mem t).toNat ≤ y.toNat := a1
  have a2' : y.toNat < (Tunables.aliasPtr s.proc.mm.mem t).toNat + alenOf A (Tunables.aliasPtr s.proc.mm.mem t) + 1 :=
    a2
  rw [e2, ← e1] at a2'
  rw [← e1] at a1'
  exact rd _ (mem_reads_al ha) y ⟨a1', Nat.add_assoc _ _ _ ▸ a2'⟩

/-- A call runs to its return, as the contract says. -/
theorem tinRun (c : Call prof 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) tin_at L s ra o) (hin : CodeIn L tin_at tin) (t : Nat) :
    Go prof 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) L s ra o s t := by
  have hp : Tunables.Pre A E s := c.call.pre
  have hfit : ∀ r, r ∈ (fp 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True) L s).data → r.Fits := fun r hr => c.foot.fits r (List.mem_append_left _ hr)
  have hfr := hfit (frame s 104) (by simp [Footprint.data, Contract.footprint, fn])
  have hK := ctx_ok hp hfr fun r hr => hfit r (by simp [Footprint.data, Contract.footprint, fn, hr])
  have hE := ctx_env c hK
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => InvT (ctx A E s) ℓ n g V)
    (fun j' g' _ V' => j' = 344 ∧ Ret (ctx A E s) g' V') (fun ℓ n g f V h => vcAll hK hE ℓ n g f V h) ?_ _ 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨by show s.cpu.gpr.rsp = s.cpu.gpr.rsp - 104#64 + 104#64; bv_omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15, -⟩ Y t' hKY hAY hrY rfl rfl
  refine c.ret hKY ⟨hbx, hsp.trans ?_, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_344 _)
    fun M hM => trivial
  show s.cpu.gpr.rsp - 104#64 + 104#64 = s.cpu.gpr.rsp
  bv_omega

/-- `__tunables_init`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem tin_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L tin_at tin)
    (A E : List (Addr × List Byte)) : ImplementsCall prof tin_at L (Tunables.contract A E) := by
  intro s₀ ra hcall
  have hcall' : CallOf prof tin_at L (fn 104 (fun _ => []) (Tunables.reads A E) (Tunables.Pre A E) (fun _ _ => True)) s₀ ra := hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    tinRun (Call.of hcall' ho (by rintro i hi ⟨r, hr, _⟩; cases hr)) hin t

end FV7z.Tun
