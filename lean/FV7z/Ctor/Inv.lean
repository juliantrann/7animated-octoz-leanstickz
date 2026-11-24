import FV7z.Ctor.ChainRegs
import FV7z.Ctor.Chains
import FV7z.Start.CtorRet
/-!
# The invariant of the 101 constructors (PLAN.md §M, constructors)

`AtCtor` asks for an invariant `J` of the constructors `csuTg 3` to `csuTg 103`. Here `Jc V sp spec`, for the
bytes `V` at `0x61344a`, the stack pointer `sp` of `__libc_csu_init` and a table `spec` of what each constructor
stores apart from the registrars' tables and the stack (`CSpec`: the intervals `wr`, and `post`, what it leaves
there, reading only `wr`):

- the registrars' tables hold `regsAt m`, the lists the registrar calls `calls k` of the constructors before `m`
  add, in order (`RegsIn`);
- a byte away from the stack's `[sp - 1024, sp + 8)`, from the first three functions' stores (`Pre`), from the
  tables and from the `wr` of the constructors before `m` is `V`'s;
- the `post` of each constructor before `m` holds.

- `Jc_out`: `__libc_csu_init`'s own stores to its frame keep `Jc`.
- `Jc_three`: `frame_dummy`'s stores (`Rfi.Dat`) on bytes `Near` `V` give `Jc … 3`, the counts of the tables 0
  in `V`.
- `Jc_end`: at `104`, the words `AtCtor` asks to keep are `V`'s.
- `Jc_chain`: a constructor that only calls registrars (`ChainOut` of its `calls`, with room) keeps `Jc`.
- `Jc_st`: a constructor that calls no registrar and stores only to its `wr`, apart from the tables (`tabs`) and
  from the `wr` before it, keeps `Jc` when its `post` holds after.

The tables are exactly `tabs` (`reg_tab`): `ChainOut.out_t` and `RegsIn.far_t` say so for the calls and the
tables; constructors store to globals between them (`0x79ed50`, …).
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- `n` lies in one of the intervals `[lo, hi)`. -/
def InR : List (Nat × Nat) → Nat → Prop
  | [], _ => False
  | (lo, hi) :: rs, n => lo ≤ n ∧ n < hi ∨ InR rs n

theorem InR_lt {b n : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ x ∈ rs, x.2 ≤ b) → InR rs n → n < b
  | [], _, h => h.elim
  | (lo, hi) :: rs, hb, h => by
    have h0 := hb (lo, hi) (by simp)
    dsimp only at h0
    rcases h with h | h
    · omega
    · exact InR_lt (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h

theorem InR_apart {lo hi n : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ x ∈ rs, x.2 ≤ lo ∨ hi ≤ x.1) → InR rs n →
    n < lo ∨ hi ≤ n
  | [], _, h => h.elim
  | (a, b) :: rs, hb, h => by
    have h0 := hb (a, b) (by simp)
    dsimp only at h0
    rcases h with h | h
    · omega
    · exact InR_apart (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h

/-- `n` is in none of `bs` when it is in `as` and `as`, `bs` are apart. -/
theorem InR_sep {n : Nat} {as : List (Nat × Nat)} (ha : InR as n) :
    ∀ {bs : List (Nat × Nat)}, (∀ x ∈ as, ∀ y ∈ bs, x.2 ≤ y.1 ∨ y.2 ≤ x.1) → ¬ InR bs n
  | [], _, h => h
  | (lo, hi) :: bs, hb, h => by
    rcases h with h | h
    · have := InR_apart (fun x hx => hb x hx (lo, hi) (by simp)) ha
      omega
    · exact InR_sep ha (fun x hx y hy => hb x hx y (List.mem_cons_of_mem _ hy)) h

/-- The registrars' tables with their counts, `[regTab r, regCnt r + 4)` for `r = 0, 1, 2`. -/
def tabs : List (Nat × Nat) := [(7990720, 7991300), (7981312, 7981828), (7981024, 7981284)]

theorem reg_tab {n : Nat} : ∀ r, (regTab r).toNat ≤ n → n < (regCnt r).toNat + 4 → InR tabs n
  | 0, h1, h2 => by
    have e : (regTab 0).toNat = 7990720 ∧ (regCnt 0).toNat = 7991296 := ⟨rfl, rfl⟩
    simp only [tabs, InR]
    omega
  | 1, h1, h2 => by
    have e : (regTab 1).toNat = 7981312 ∧ (regCnt 1).toNat = 7981824 := ⟨rfl, rfl⟩
    simp only [tabs, InR]
    omega
  | k + 2, h1, h2 => by
    have e : (regTab (k + 2)).toNat = 7981024 ∧ (regCnt (k + 2)).toNat = 7981280 := ⟨rfl, rfl⟩
    simp only [tabs, InR]
    omega

theorem not_tab {n : Nat} (r : Nat) (h : ¬ InR tabs n) : n < (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ n := by
  rcases Nat.lt_or_ge n (regTab r).toNat with h1 | h1
  · exact .inl h1
  rcases Nat.lt_or_ge n ((regCnt r).toNat + 4) with h2 | h2
  · exact absurd (reg_tab r h1 h2) h
  exact .inr h2

/-- What a constructor stores apart from the registrars' tables and the stack (the intervals `wr`), and what it
leaves there. -/
structure CSpec where
  wr : List (Nat × Nat)
  post : (Addr → Byte) → Prop

/-- `post` reads only the bytes of `wr`. -/
def CSpec.Dep (c : CSpec) : Prop :=
  ∀ W W' : Addr → Byte, (∀ a : Addr, InR c.wr a.toNat → W' a = W a) → c.post W → c.post W'

/-- The constructors `m` that store elsewhere first and then end with `jmp R` to the registrar `r` with `rdi = A`:
`(m, r, A)`. -/
def tails : List (Nat × Nat × Nat) := [(37, 0, 7840512), (55, 0, 7851136), (61, 0, 7852416)]

/-- The constructors `m` whose registrar calls come with a call of a `*Prepare` function (`Mix.lean`): `(m, calls)`.
`csuTg 67` calls `RegisterArc`, `RegisterHasher`, then jumps to `z7_Black2sp_Prepare`; `csuTg 77` calls
`z7_SwapBytesPrepare`, then `RegisterCodec` twice. -/
def mixes : List (Nat × List (Nat × Nat)) := [(67, [(0, 7853824), (2, 7853792)]), (77, [(1, 7856128), (1, 7856168)])]

/-- The registrar calls of the constructor `m`: its call of `leas`, its calls of `chains`, its call of `tails`, its
calls of `mixes`, none for the others yet. -/
def calls (m : Nat) : List (Nat × Nat) :=
  match leas.find? (fun x => x.1 == m) with
  | some (_, _, r, A) => [(r, A)]
  | none =>
    match chains.find? (fun x => x.1 == m) with
    | some (_, _, cs) => cs
    | none =>
      match tails.find? (fun x => x.1 == m) with
      | some (_, r, A) => [(r, A)]
      | none =>
        match mixes.find? (fun x => x.1 == m) with
        | some (_, cs) => cs
        | none => []

/-- The lists of the registrars' tables before the constructor `m`. -/
def regsAt (m : Nat) : Nat → List (BitVec 64) :=
  ((List.range m).drop 3).foldl (fun R k => updAll R (calls k)) fun _ => []

theorem regsAt_three : regsAt 3 = fun _ => [] := rfl

theorem regsAt_succ {m : Nat} (h : 3 ≤ m) : regsAt (m + 1) = updAll (regsAt m) (calls m) := by
  unfold regsAt
  rw [List.range_succ, List.drop_append_of_le_length (by rw [List.length_range]; exact h), List.foldl_append]
  rfl

theorem calls_lea : ∀ x ∈ leas, calls x.1 = [(x.2.2.1, x.2.2.2)] := by decide +kernel

theorem calls_chain : ∀ x ∈ chains, calls x.1 = x.2.2 := by decide +kernel

theorem calls_tail : ∀ x ∈ tails, calls x.1 = [(x.2.1, x.2.2)] := by decide +kernel

theorem calls_mix : ∀ x ∈ mixes, calls x.1 = x.2 := by decide +kernel

/-- `Fits` as a test. -/
def fitsB : (Nat → List (BitVec 64)) → List (Nat × Nat) → Bool
  | _, [] => true
  | R, (r, A) :: cs => decide (r < 3) && decide ((R r).length < regMax r) && fitsB (upd R r (BitVec.ofNat 64 A)) cs

theorem fits_of : ∀ {R : Nat → List (BitVec 64)} {cs : List (Nat × Nat)}, fitsB R cs = true → Fits R cs
  | _, [], _ => trivial
  | R, (r, A) :: cs, h => by
    simp only [fitsB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, fits_of h.2⟩

/-- Each constructor's registrar calls have room. -/
theorem fits_all : ∀ m < 104, fitsB (regsAt m) (calls m) = true := by decide +kernel

/-- The stores of the first three functions of `__libc_csu_init` apart from the stack: `elision_init`'s word, and
`frame_dummy`'s object and words (`Rfi.Wr`). -/
def Pre (n : Nat) : Prop :=
  7938696 ≤ n ∧ n < 7938700 ∨ 7947808 ≤ n ∧ n < 7947856 ∨ 8008608 ≤ n ∧ n < 8008612 ∨ 8008616 ≤ n ∧ n < 8008624 ∨
    8008648 ≤ n ∧ n < 8008652 ∨ 8008664 ≤ n ∧ n < 8008672

theorem pre_of_wr {n : Nat} (h : Rfi.Wr 7947808#64 n) : Pre n := by
  have e : (7947808#64 : Addr).toNat = 7947808 := rfl
  unfold Rfi.Wr at h
  rw [e] at h
  unfold Pre
  omega

/-- The invariant of the constructors, for the bytes `V` at `0x61344a`, `__libc_csu_init`'s `sp` and the
constructors' stores `spec`. -/
def Jc (V : Addr → Byte) (sp : Nat) (spec : Nat → CSpec) (m : Nat) (W : Addr → Byte) : Prop :=
  RegsIn (regsAt m) W ∧
  (∀ a : Addr, ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → ¬ Pre a.toNat →
    ¬ (7981024 ≤ a.toNat ∧ a.toNat < 7991300) → (∀ k, 3 ≤ k → k < m → ¬ InR (spec k).wr a.toNat) → W a = V a) ∧
  ∀ k, 3 ≤ k → k < m → (spec k).post W

variable {V W W' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec}

/-- The registrars' count words lie in `[7981024, 7991300)`. -/
theorem cnt_in (r : Nat) : 7981024 ≤ (regCnt r).toNat ∧ (regCnt r).toNat + 4 ≤ 7991300 := by
  obtain ⟨-, -, ap⟩ := reg_lay r
  have := reg_in r
  omega

/-- `__libc_csu_init`'s stores to its frame keep `Jc`. -/
theorem Jc_out (hS : 7991300 + 1024 ≤ sp) (hD : ∀ k, (spec k).Dep) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hJ : Jc V sp spec m W) (ho : Raf.Out (sp - 64) sp W W') : Jc V sp spec m W' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  refine ⟨hR.far fun a h4 h5 => ho a (by omega), fun a h1 h2 h3 h4 => (ho a (by omega)).trans (hK a h1 h2 h3 h4),
    fun k hk hkm => hD k W W' (fun a ha => ho a ?_) (hP k hk hkm)⟩
  have := InR_lt (hB k) ha
  omega

/-- `frame_dummy`'s stores on bytes `Near` `V`, the counts of the registrars' tables 0 in `V`, give `Jc` at `3`. -/
theorem Jc_three (hS : 8008672 + 1024 ≤ sp) (hz : ∀ r < 3, rdd(V, regCnt r) = 0)
    (hN : Near (sp - 1024) (sp + 8) V W) (hd : Rfi.Dat (sp - 64 - 72) (sp - 64) 7947808#64 7388000#64 W W') :
    Jc V sp spec 3 W' := by
  have e : ∀ a : Addr, ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → ¬ Pre a.toNat → W' a = V a := fun a h1 h2 =>
    (hd.out a (by omega) fun hw => h2 (pre_of_wr hw)).trans (hN a h1 fun h => h2 (by unfold Pre; omega))
  refine ⟨?_, fun a h1 h2 _ _ => e a h1 h2, fun k hk hkm => absurd hkm (by omega)⟩
  rw [regsAt_three]
  intro r hr
  have hc := cnt_in r
  have c4 := (reg_lay r).c4
  have h : rdd(W', regCnt r) = rdd(V, regCnt r) := rdd_eq c4 fun a h4 h5 => e a (by omega) (by unfold Pre; omega)
  refine ⟨by rw [h, hz r hr]; rfl, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

/-- At `104`, the words above the stack's `[sp - 1024, sp + 8)` that `AtCtor` asks to keep, and `__environ`, are
`V`'s. -/
theorem Jc_end (hS : 8013728 + 1024 ≤ sp) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hE : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1) (hJ : Jc V sp spec 104 W) (a : Addr)
    (ha : sp + 20 ≤ a.toNat ∧ a.toNat < sp + 40 ∨ 8013720 ≤ a.toNat ∧ a.toNat < 8013728) : W a = V a := by
  refine hJ.2.1 a (by omega) (by unfold Pre; omega) (by omega) fun k _ _ hw => ?_
  rcases ha with ha | ha
  · have := InR_lt (hB k) hw
    omega
  · have := InR_apart (hE k) hw
    omega

/-- Bytes apart from `tabs` and the pushed return addresses are as before the calls. -/
theorem ChainOut.out_t {S : Addr} (hS : 16 ≤ S.toNat) {a : Addr} (ha1 : ¬ InR tabs a.toNat)
    (ha2 : a.toNat < S.toNat - 16 ∨ S.toNat - 8 ≤ a.toNat) :
    ∀ (cs : List (Nat × Nat)) (V V' : Addr → Byte), ChainOut S cs V V' → V' a = V a
  | [], V, V', h => by rw [show V' = V from h]
  | [(r, A)], V, V', h =>
    RegOut.out (show RegOut (regCnt r) (regTab r) (regMax r) _ V V' from h) (reg_lay r) (not_tab r ha1)
  | (r, A) :: c :: cs, V, V', h => by
    obtain ⟨ra, V₁, h1, h2⟩ := h
    have e := sub16 S hS
    have hs : (S - 8 - 8).toNat + (toBytesLE ra 8).length ≤ 2 ^ 64 := by
      rw [e, toBytesLE_length]
      have := S.isLt
      omega
    rw [ChainOut.out_t hS ha1 ha2 (c :: cs) V₁ V' h2, RegOut.out h1 (reg_lay r) (not_tab r ha1),
      Tun.Vst_out V _ _ a hs (by rw [e, toBytesLE_length]; omega)]

/-- The tables are as before when the bytes of `tabs` are. -/
theorem RegsIn.far_t {R : Nat → List (BitVec 64)} {V V' : Addr → Byte} (h : RegsIn R V)
    (hV : ∀ a : Addr, InR tabs a.toNat → V' a = V a) : RegsIn R V' := by
  intro r hr
  obtain ⟨hc, hle, he⟩ := h r hr
  obtain ⟨c4, t8, ap⟩ := reg_lay r
  have hx := reg_max r
  refine ⟨?_, hle, fun i hi' => ?_⟩
  · rw [rdd_eq c4 fun a h4 h5 => hV a (reg_tab r (by omega) (by omega))]
    exact hc
  · have ht := ent_toNat r i (by omega)
    rw [rdq_eq (by omega) fun a h4 h5 => hV a (reg_tab r (by omega) (by omega))]
    exact he i hi'

/-- A constructor that only calls registrars, its `calls` with room, `ChainOut` from `S = sp - 64`, and stores
nothing else, keeps `Jc`. -/
theorem Jc_chain {S : Addr} {cs : List (Nat × Nat)} (hm : 3 ≤ m) (hSn : S.toNat + 64 = sp)
    (hS : 7991300 + 1024 ≤ sp) (hc : calls m = cs) (hF : Fits (regsAt m) cs) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hs : ∀ W, (spec m).post W) (hJ : Jc V sp spec m W) (hO : ChainOut S cs W W') :
    Jc V sp spec (m + 1) W' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact RegsIn.chain (by omega) cs _ W W' hR hF hO
  · rw [ChainOut.out (by omega) (by omega) (by omega) cs W W' hO]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · refine hD k W W' (fun a ha => ?_) (hP k hk hlt)
      have h1 := InR_lt (hB k) ha
      exact ChainOut.out_t (by omega) (InR_sep ha (hT k)) (by omega) cs W W' hO
    · obtain rfl : k = m := by omega
      exact hs W'

/-- A constructor that calls no registrar and stores only to its `wr` (apart from the tables and from the `wr` of
the constructors before it) keeps `Jc` when its `post` holds after. -/
theorem Jc_st {V W W' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} (hm : 3 ≤ m) (hc : calls m = [])
    (hD : ∀ k, (spec k).Dep) (hT : ∀ x ∈ (spec m).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hX : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ (spec m).wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hJ : Jc V sp spec m W) (hW : ∀ a : Addr, ¬ InR (spec m).wr a.toNat → W' a = W a) (hp : (spec m).post W') :
    Jc V sp spec (m + 1) W' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact hR.far_t fun a ha => hW a fun hw => InR_sep hw hT ha
  · rw [hW a (h4 m hm (by omega))]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · exact hD k W W' (fun a ha => hW a (InR_sep ha (hX k hk hlt))) (hP k hk hlt)
    · obtain rfl : k = m := by omega
      exact hp

end FV7z.Ctor
