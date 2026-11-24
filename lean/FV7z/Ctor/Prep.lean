import FV7z.Ctor.Impl
import FV7z.Ctor.StSpec
/-!
# A constructor that is a function writing globals, with its own proof (PLAN.md §M, constructors)

The functions `csuTg 5`, `7`, `9`, `92` jump to (`Prepare/K.lean`) write a few globals (`Wc`), read the stack canary
and maybe constant tables (`Rc`), and use a stack frame below the return address. For `Jg`, their spec is
`wrSpec (wrOf Wc)`; the frame lies in the stack's window `[sp - 1024, sp + 8)` that `Jc` leaves free.

- `wrOf`, `inR_wrOf`, `Lo`: the intervals of a list of regions; regions that end at or below a bound.
- `Jc_stk`, `jg_wrk`: `Jc_st`, `jg_wr` for a constructor that also stores into the stack's window.
- `prepK_ws`, `prepK_sub`: at a call with `rsp = D`, what the function may store, and the part of `fnK`'s
  `CallOf` about the footprint (also for a call from the middle of a constructor, `Mix.lean`).
- `prepK_core`: a function at `e` with `ImplementsCall` of `fnK k (fun _ => Wc) (canary :: Rc)` is one as
  `Csu.csu_ok` asks, for an invariant its postcondition takes from `m` to `m + 1`; `prepK_runs`: for `Jg` with the
  spec `wrSpec (wrOf Wc)`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The intervals of the regions `rs`. -/
def wrOf (rs : List Rgn) : List (Nat × Nat) := rs.map fun r => (r.base.toNat, r.base.toNat + r.len)

theorem inR_wrOf {r : Rgn} {y : Addr} (hm : r.Mem y) : ∀ {rs : List Rgn}, r ∈ rs → InR (wrOf rs) y.toNat
  | [], h => by simp at h
  | q :: qs, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact Or.inl hm
    · exact Or.inr (inR_wrOf hm h')

theorem foot_wrOf {rs : List Rgn} {y : Addr} (h : Foot rs y) : InR (wrOf rs) y.toNat := by
  obtain ⟨r, hr, hm⟩ := h
  exact inR_wrOf hm hr

/-- The regions `rs` end at or below `b`. -/
def Lo (b : Nat) (rs : List Rgn) : Prop := ∀ r ∈ rs, r.base.toNat + r.len ≤ b

theorem Lo.foot {b : Nat} {rs : List Rgn} (h : Lo b rs) {y : Addr} (hy : Foot rs y) : y.toNat < b := by
  obtain ⟨r, hr, h1, h2⟩ := hy
  have := h r hr
  omega

theorem lo_wrOf {b : Nat} {rs : List Rgn} (h : ∀ x ∈ wrOf rs, x.2 ≤ b) : Lo b rs := fun r hr =>
  h _ (List.mem_map.2 ⟨r, hr, rfl⟩)

/-- The frame of `k` bytes below the slot at `sp - 64`. -/
theorem fr_toNat {sp : Addr} {k : Nat} (hk : k + 64 ≤ 1024) (hs : 1024 ≤ sp.toNat) :
    (sp - 64#64 - BitVec.ofNat 64 k).toNat = sp.toNat - 64 - k := by
  have hb := sp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A constructor that calls no registrar, stores to its `wr` (apart from the tables and from the `wr` of the
constructors before it) and into the stack's window, keeps `Jc` when its `post` holds after. -/
theorem Jc_stk {V W W' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} (hm : 3 ≤ m) (hc : calls m = [])
    (hS : 7991300 + 1024 ≤ sp) (hD : ∀ k, (spec k).Dep) (hT : ∀ x ∈ (spec m).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hX : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ (spec m).wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hJ : Jc V sp spec m W)
    (hW : ∀ a : Addr, ¬ InR (spec m).wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → W' a = W a)
    (hp : (spec m).post W') : Jc V sp spec (m + 1) W' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact hR.far_t fun a ha => hW a (fun hw => InR_sep hw hT ha)
      (by have := InR_lt (b := 7991300) (by decide) ha; omega)
  · rw [hW a (h4 m hm (by omega)) h1]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · exact hD k W W' (fun a ha => hW a (InR_sep ha (hX k hk hlt)) (by have := InR_lt (hB k) ha; omega))
        (hP k hk hlt)
    · obtain rfl : k = m := by omega
      exact hp

/-- `Jg` from `m` to `m + 1` for `spec m = wrSpec wr`, when the constructor keeps the bytes outside `wr` and the
stack's window, and `wr` is apart from the tables and the stores before. -/
theorem jg_wrk {V W W' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {wr : List (Nat × Nat)} (hm : 3 ≤ m) (hc : calls m = []) (hS : 7991300 + 1024 ≤ sp)
    (hspec : spec m = wrSpec wr) (hD : ∀ k, (spec k).Dep) (hT : ∀ x ∈ wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hout : ∀ a : Addr, ¬ InR wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → W' a = W a)
    (hG : G m W → G (m + 1) W') (hJ : Jg V sp spec G m W) : Jg V sp spec G (m + 1) W' := by
  obtain ⟨hJc, hG'⟩ := hJ
  refine ⟨Jc_stk hm hc hS hD ?_ hB (fun k hk hkm => ?_) hJc (fun a ha => hout a ?_) ?_, hG hG'⟩
  · rw [hspec]
    exact hT
  · rw [hspec]
    exact hXw k hk hkm
  · rw [hspec] at ha
    exact ha
  · rw [hspec]
    trivial

/-- The canary's region. -/
abbrev canary (s : State) : Rgn := ⟨Addr.add s.cpu.seg.fsBase 40, 8⟩

theorem lo_canary {b : Nat} {s : State} (h : (Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ b) : Lo b [canary s] :=
  fun r hr => by
    rw [List.mem_singleton] at hr
    subst hr
    exact h

/-- `D - k` for `k ≤ D`. -/
theorem subk_toNat {D : Addr} {k : Nat} (hk : k ≤ D.toNat) : (D - BitVec.ofNat 64 k).toNat = D.toNat - k := by
  have hb := D.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- What the function may store into at a call with `rsp = D`: the `k` bytes below `D`, or `Wc`. -/
theorem prepK_ws {D : Addr} {k : Nat} {Wc : List Rgn} {Y : State} (hsp : Y.cpu.gpr.rsp = D) (hk : k ≤ D.toNat)
    {y : Addr} (hy : Foot (ws k (fun _ => Wc) Y) y) : (D.toNat - k ≤ y.toNat ∧ y.toNat < D.toNat) ∨ Foot Wc y := by
  obtain ⟨r, hr, hm⟩ := hy
  rcases List.mem_cons.1 hr with rfl | hr
  · simp only [below, Rgn.Mem] at hm
    rw [hsp, subk_toNat hk] at hm
    exact .inl (by omega)
  · exact .inr ⟨r, hr, hm⟩

/-- A call, with `rsp = D`, of a function with the contract `fnK` writing the globals `Wc` (below the window) and
reading the canary and `Rc`, its frame of `k` bytes below `D` in the stack's window (in `Wl`, `hstk`): the contract's
footprint is a part of the run's, what it may store lies in `Wl`, and its frame is apart from what it names. -/
theorem prepK_sub {sp D : Addr} {k : Nat} {Wc Rc : List Rgn} {pre : State → Prop} {post : State → State → Prop}
    (c : Seg prof F Wl L s₀ o) (hk : sp.toNat - 1024 + k ≤ D.toNat) (hD : D.toNat + 64 ≤ sp.toNat)
    (hstk : ∀ y : Addr, sp.toNat - 1024 ≤ y.toNat → y.toNat < sp.toNat - 56 → Foot Wl y)
    (hWl : ∀ y, Foot Wc y → Foot Wl y) (hRl : Lo (sp.toNat - 1024) (canary s₀ :: Rc))
    (hRF : ∀ y, Foot (canary s₀ :: Rc) y → Foot F.writes y ∨ Foot F.reads y) (hWlo : Lo (sp.toNat - 1024) Wc)
    {Y : State} (hK : KeptW Wl s₀ Y) (hsp : Y.cpu.gpr.rsp = D) :
    Sub F ((fnK k (fun _ => Wc) (fun s => canary s :: Rc) pre post).footprint L Y) ∧
      (∀ y, Foot (ws k (fun _ => Wc) Y) y → Foot Wl y) ∧ Apart [frame Y k] (Wc ++ (canary Y :: Rc)) := by
  have hsb := sp.isLt
  have hkD : k ≤ D.toNat := by omega
  have e := subk_toNat hkD
  have hfr : ∀ y, (frame Y k).Mem y → D.toNat - k ≤ y.toNat ∧ y.toNat < D.toNat + 8 := fun y hy => by
    simp only [frame, Rgn.Mem] at hy
    rw [hsp, e] at hy
    omega
  have hRY : canary Y :: Rc = canary s₀ :: Rc := by unfold canary; rw [hK.seg]
  refine ⟨⟨fun r hr => ?_, fun y ⟨r, hr, hm⟩ => ?_, fun y ⟨r, hr, hm⟩ => ?_, c.code.symm ▸ rfl, rfl, c.own⟩,
    fun y hy => ?_, fun r hr q hq a ha hb => ?_⟩
  · change r ∈ (frame Y k :: Wc) ++ ([] ++ (canary Y :: Rc)) at hr
    rw [List.nil_append, hRY] at hr
    unfold Rgn.Fits
    rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · simp only [frame]
        rw [hsp, e]
        omega
      · have := hWlo r hr
        omega
    · have := hRl r hr
      omega
  · change r ∈ frame Y k :: Wc at hr
    rcases List.mem_cons.1 hr with rfl | hr
    · have := hfr y hm
      exact c.hww y (hstk y (by omega) (by omega))
    · exact c.hww y (hWl y ⟨r, hr, hm⟩)
  · change r ∈ [] ++ (canary Y :: Rc) at hr
    rw [List.nil_append, hRY] at hr
    exact hRF y ⟨r, hr, hm⟩
  · rcases prepK_ws hsp hkD hy with h | h
    · exact hstk y (by omega) (by omega)
    · exact hWl y h
  · rw [List.mem_singleton] at hr
    subst hr
    have h1 := hfr a ha
    change q ∈ Wc ++ (canary Y :: Rc) at hq
    rw [hRY, List.mem_append] at hq
    rcases hq with hq | hq
    · have := hWlo.foot ⟨q, hq, hb⟩
      omega
    · have := hRl.foot ⟨q, hq, hb⟩
      omega

/-- A function at `e` with its own proof (`ImplementsCall` of `fnK`), writing the globals `Wc` (below the window and
apart from the arrays) and reading the canary and `Rc`, is a function as `Csu.csu_ok` asks: its frame of `k` bytes lies
in the stack's window and in `Wl` (`hstk`), `Wc` in `Wl`, what it reads below the window and in the footprint, and its
precondition holds at the frame's call (`hpre`). `J` goes from `m` to `m + 1` by the postcondition and the bytes it
keeps (`hJ`). -/
theorem prepK_core {J : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m : Nat} {e : Addr} {k : Nat} {Wc Rc : List Rgn}
    {pre : State → Prop} {post : State → State → Prop}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (himp : ImplementsCall prof e L (fnK k (fun _ => Wc) (fun s => canary s :: Rc) pre post))
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) (hal : (sp - 64#64 + 8).toNat % 16 = 0)
    (hk : k + 64 ≤ 1024) (hS : 7991300 + 1024 ≤ sp.toNat)
    (hstk : ∀ y : Addr, sp.toNat - 1024 ≤ y.toNat → y.toNat < sp.toNat - 56 → Foot Wl y)
    (hWl : ∀ y, Foot Wc y → Foot Wl y) (hRl : Lo (sp.toNat - 1024) (canary s₀ :: Rc))
    (hRF : ∀ y, Foot (canary s₀ :: Rc) y → Foot F.writes y ∨ Foot F.reads y)
    (hpre : ∀ Y : State, Y.cpu.seg = s₀.cpu.seg → Y.cpu.gpr.rsp = sp - 64#64 → pre Y)
    (hWlo : Lo (sp.toNat - 1024) Wc) (hA : ∀ x ∈ wrOf Wc, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1)
    (hJ : ∀ (Y Z : State) (W W' : Addr → Byte), post Y Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot Wc y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → J m W → J (m + 1) W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m e := by
  have n := Csu.sp_n (show 64 ≤ sp.toNat by omega)
  have hws : ∀ (Y : State) (y : Addr), Y.cpu.gpr.rsp = sp - 64#64 → Foot (ws k (fun _ => Wc) Y) y →
      (sp.toNat - 64 - k ≤ y.toNat ∧ y.toNat < sp.toNat - 64) ∨ (Foot Wc y ∧ y.toNat < sp.toNat - 1024) :=
    fun Y y hsp hy => by
      rcases prepK_ws hsp (by rw [n]; omega) hy with h | h
      · rw [n] at h
        exact .inl (by omega)
      · exact .inr ⟨h, hWlo.foot h⟩
  refine implK_runs c hC himp hdf hx87 hal (fun Y U hK _ _ _ hsp _ => ?_)
    (fun Y Z U U' hsp hI hpost hU' hAZ => ?_)
  · obtain ⟨hsub, hwl, hap⟩ := prepK_sub (pre := pre) (post := post) c (by rw [n]; omega)
      (by rw [n]; omega) hstk hWl hRl hRF hWlo hK hsp
    refine ⟨hsub, hwl, hpre Y hK.seg hsp, hap, fun y hy => ?_⟩
    rcases hws Y y hsp hy with h | h
    · exact ⟨by omega, by omega⟩
    · have := InR_apart hA (foot_wrOf h.1)
      exact ⟨by omega, by omega⟩
  · refine hJ Y Z U U' hpost (fun y hw hy' => hU' y fun hy => ?_) hAZ hI
    rcases hws Y y hsp hy with h | h
    · exact hw ⟨by omega, by omega⟩
    · exact hy' h.1

/-- `prepK_core` for `Jg` with the spec `wrSpec (wrOf Wc)`: `G` goes from `m` to `m + 1` by the postcondition
(`hG`). -/
theorem prepK_runs {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m : Nat} {e : Addr} {k : Nat} {Wc Rc : List Rgn}
    {pre : State → Prop} {post : State → State → Prop}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (himp : ImplementsCall prof e L (fnK k (fun _ => Wc) (fun s => canary s :: Rc) pre post))
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) (hal : (sp - 64#64 + 8).toNat % 16 = 0)
    (hk : k + 64 ≤ 1024) (hS : 7991300 + 1024 ≤ sp.toNat)
    (hstk : ∀ y : Addr, sp.toNat - 1024 ≤ y.toNat → y.toNat < sp.toNat - 56 → Foot Wl y)
    (hWl : ∀ y, Foot Wc y → Foot Wl y) (hRl : Lo (sp.toNat - 1024) (canary s₀ :: Rc))
    (hRF : ∀ y, Foot (canary s₀ :: Rc) y → Foot F.writes y ∨ Foot F.reads y)
    (hpre : ∀ Y : State, Y.cpu.seg = s₀.cpu.seg → Y.cpu.gpr.rsp = sp - 64#64 → pre Y)
    (hm3 : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec (wrOf Wc)) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ x ∈ wrOf Wc, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hA : ∀ x ∈ wrOf Wc, x.2 ≤ 7829400 ∨ 7830224 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wrOf Wc, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ (Y Z : State) (W W' : Addr → Byte), post Y Z →
      (∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot Wc y → W' y = W y) →
      Agree F Z.proc.mm.mem W' → G m W → G (m + 1) W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m e :=
  prepK_core c hC himp hdf hx87 hal hk hS hstk hWl hRl hRF hpre
    (lo_wrOf (by have h := hB m; rw [hspec] at h; exact h)) hA
    fun Y Z U U' hpost hU' hAZ hI => jg_wrk hm3 hc hS hspec hD hT hB hXw
      (fun a ha hw => hU' a hw fun hy => ha (foot_wrOf hy)) (hG Y Z U U' hpost hU' hAZ) hI

end FV7z.Ctor
