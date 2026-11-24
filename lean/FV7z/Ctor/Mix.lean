import FV7z.Ctor.Prep
/-!
# Constructors that call registrars and a function with its own proof (PLAN.md §M, constructors)

`csuTg 67` is `endbr64; sub rsp, 8; lea rdi, [rip + d₁]; call R₁; lea rdi, [rip + d₂]; call R₂; add rsp, 8; jmp f`
and `csuTg 77` is `endbr64; sub rsp, 8; call f; lea rdi, [rip + d₁]; call R₁; lea rdi, [rip + d₂]; add rsp, 8;
jmp R₁`, with `f` a `*Prepare` function (`Prepare/K.lean`); their `calls` are in `mixes`.

- `CallOut S cs V V'`: the bytes after the registrar calls `cs`, each a `call` with its return address at `S - 16`
  (`ChainOut`'s last call is a `jmp`); `CallOut.out_t`, `RegsIn.calls`.
- `Jc_callsK`, `jg_callsK`: `Jc`, `Jg` from `m` to `m + 1` for the calls (`CallOut`) and then the function's stores.
- `CallsMid prof p cs q`: those calls from offset `p` of `sti` to `q`; `calls_mid`: the run through them.
- `add_jmp`: `add rsp, 8; jmp f`.
- `Mid J P m`: `J`, but at `m` the bytes `P` takes those of `J m` to; `runs_pre`: `Csu.Runs` at a constructor's entry
  from a stretch that reaches `e` with the frame's `rsp` and `Csu.Runs` at `e` for `Mid`.
- `callsK_runs`: `Csu.Runs` for a constructor shaped as `csuTg 67`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- The bytes after the registrar calls `cs` of a constructor entered with `rsp = S`, each a `call` with its return
address pushed at `S - 16`. -/
def CallOut (S : Addr) : List (Nat × Nat) → (Addr → Byte) → (Addr → Byte) → Prop
  | [], V, V' => V' = V
  | (r, A) :: cs, V, V' => ∃ (ra : Addr) (V₁ : Addr → Byte),
      RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) (Vst V (S - 8 - 8) (toBytesLE ra 8)) V₁ ∧
      CallOut S cs V₁ V'

/-- The tables lie in `[7981024, 7991300)`. -/
theorem tabs_in {n : Nat} (h : InR tabs n) : 7981024 ≤ n ∧ n < 7991300 := by
  have h1 := InR_apart (lo := 0) (hi := 7981024) (by decide) h
  have h2 := InR_lt (b := 7991300) (by decide) h
  omega

/-- Bytes apart from `tabs` and the pushed return addresses are as before the calls. -/
theorem CallOut.out_t {S : Addr} (hS : 16 ≤ S.toNat) {a : Addr} (ha1 : ¬ InR tabs a.toNat)
    (ha2 : a.toNat < S.toNat - 16 ∨ S.toNat - 8 ≤ a.toNat) :
    ∀ (cs : List (Nat × Nat)) (V V' : Addr → Byte), CallOut S cs V V' → V' a = V a
  | [], V, V', h => by rw [show V' = V from h]
  | (r, A) :: cs, V, V', h => by
    obtain ⟨ra, V₁, h1, h2⟩ := h
    have e := sub16 S hS
    have hs : (S - 8 - 8).toNat + (toBytesLE ra 8).length ≤ 2 ^ 64 := by
      rw [e, toBytesLE_length]
      have := S.isLt
      omega
    rw [CallOut.out_t hS ha1 ha2 cs V₁ V' h2, RegOut.out h1 (reg_lay r) (not_tab r ha1),
      Tun.Vst_out V _ _ a hs (by rw [e, toBytesLE_length]; omega)]

/-- After the calls `cs` with room, the tables hold `updAll R cs`. -/
theorem RegsIn.calls {S : Addr} (hS : 7991300 + 16 ≤ S.toNat) :
    ∀ (cs : List (Nat × Nat)) (R : Nat → List (BitVec 64)) (V V' : Addr → Byte), RegsIn R V → Fits R cs →
      CallOut S cs V V' → RegsIn (updAll R cs) V'
  | [], R, V, V', h, _, hO => by
    rw [show V' = V from hO]
    exact h
  | (r, A) :: cs, R, V, V', h, hF, hO => by
    obtain ⟨hr, hn, hF'⟩ := hF
    obtain ⟨ra, V₁, h1, h2⟩ := hO
    have e := sub16 S (by omega)
    have hs : (S - 8 - 8).toNat + (toBytesLE ra 8).length ≤ 2 ^ 64 := by
      rw [e, toBytesLE_length]
      have := S.isLt
      omega
    have h0 : RegsIn R (Vst V (S - 8 - 8) (toBytesLE ra 8)) :=
      h.far fun a h4 h5 => Tun.Vst_out V _ _ a hs (by rw [e]; omega)
    exact RegsIn.calls hS cs _ V₁ V' (h0.push hr hn h1) hF' h2

/-- A constructor whose registrar calls (its `calls`, with room, `CallOut` from `S = sp - 64`) come before stores
only to its `wr` (apart from the tables and from the `wr` of the constructors before it) and into the stack's window
keeps `Jc` when its `post` holds after. -/
theorem Jc_callsK {V W U U' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} {S : Addr} {cs : List (Nat × Nat)}
    (hm : 3 ≤ m) (hSn : S.toNat + 64 = sp) (hS : 7991300 + 1024 ≤ sp) (hc : calls m = cs)
    (hF : Fits (regsAt m) cs) (hD : ∀ k, (spec k).Dep) (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hX : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ (spec m).wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hJ : Jc V sp spec m W) (hO : CallOut S cs W U)
    (hW : ∀ a : Addr, ¬ InR (spec m).wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → U' a = U a)
    (hp : (spec m).post U') : Jc V sp spec (m + 1) U' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  have hO' : ∀ a : Addr, ¬ InR tabs a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → U a = W a :=
    fun a h1 h2 => CallOut.out_t (by omega) h1 (by omega) cs W U hO
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact (RegsIn.calls (by omega) cs _ W U hR hF hO).far_t fun a ha => hW a (fun hw => InR_sep hw (hT m) ha)
      (by have := tabs_in ha; omega)
  · have ht : ¬ InR tabs a.toNat := fun ht => h3 (tabs_in ht)
    rw [hW a (h4 m hm (by omega)) h1, hO' a ht h1]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · refine hD k W U' (fun a ha => ?_) (hP k hk hlt)
      have hb := InR_lt (hB k) ha
      rw [hW a (InR_sep ha (hX k hk hlt)) (by omega), hO' a (InR_sep ha (hT k)) (by omega)]
    · obtain rfl : k = m := by omega
      exact hp

/-- `Jg` from `m` to `m + 1` for `spec m = wrSpec wr`, when the constructor makes its registrar calls and then keeps
the bytes outside `wr` and the stack's window. -/
theorem jg_callsK {V W U U' : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {S : Addr} {cs wr : List (Nat × Nat)} (hm : 3 ≤ m) (hSn : S.toNat + 64 = sp) (hS : 7991300 + 1024 ≤ sp)
    (hc : calls m = cs) (hF : Fits (regsAt m) cs) (hspec : spec m = wrSpec wr) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1) (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1) (hO : CallOut S cs W U)
    (hout : ∀ a : Addr, ¬ InR wr a.toNat → ¬ (sp - 1024 ≤ a.toNat ∧ a.toNat < sp + 8) → U' a = U a)
    (hG : G m W → G (m + 1) U') (hJ : Jg V sp spec G m W) : Jg V sp spec G (m + 1) U' := by
  obtain ⟨hJc, hG'⟩ := hJ
  refine ⟨Jc_callsK hm hSn hS hc hF hD hT hB (fun k hk hkm => ?_) hJc hO (fun a ha => hout a ?_) ?_, hG hG'⟩
  · rw [hspec]
    exact hXw k hk hkm
  · rw [hspec] at ha
    exact ha
  · rw [hspec]
    trivial

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- The calls `cs` from offset `p` of `sti` to `q`: a `lea rdi; call R` for each. -/
def CallsMid (prof : Profile) : Nat → List (Nat × Nat) → Nat → Prop
  | p, [], q => p = q
  | p, (r, A) :: cs, q => ∃ rel, BlkA prof sti sti_at p (p + 7) [Op.mov 64 7 (.i A)] ∧
      Dec prof.feat sti (p + 7) (FV7z.mk .call 64 [.rel rel] 5) ∧ p + 7 + 5 < sti.length ∧
      sti_at.add (p + 7 + 5) + BitVec.ofNat 64 rel = regAt r ∧ CallsMid prof (p + 7 + 5) cs q

theorem CallsMid.nil {p : Nat} : CallsMid prof p [] p := rfl

theorem CallsMid.mid {p q r A rel : Nat} {cs : List (Nat × Nat)}
    (hb : BlkA prof sti sti_at p (p + 7) [Op.mov 64 7 (.i A)])
    (hd : Dec prof.feat sti (p + 7) (FV7z.mk .call 64 [.rel rel] 5)) (hj : p + 7 + 5 < sti.length)
    (htgt : sti_at.add (p + 7 + 5) + BitVec.ofNat 64 rel = regAt r) (h : CallsMid prof (p + 7 + 5) cs q) :
    CallsMid prof p ((r, A) :: cs) q := by
  unfold CallsMid
  exact ⟨rel, hb, hd, hj, htgt, h⟩

/-- From the first `lea` of the calls `cs` at offset `p`, `rsp = S - 8`, to `q`: the bytes `CallOut`, `rsp` as
before, the registers a call keeps. -/
theorem calls_mid (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) {S : Addr}
    (hst : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i)) (hhi : 7991300 + 16 ≤ S.toNat) {q : Nat} :
    ∀ (cs : List (Nat × Nat)) (p : Nat) (X : State) (t : Nat) (V : Addr → Byte), CallsMid prof p cs q →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = sti_at.add p → X.cpu.gpr.rsp = S - 8 →
    (∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → CallOut S cs V V' → Z.cpu.rip = sti_at.add q →
      Z.cpu.gpr.rsp = S - 8 → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t
  | [], p, X, t, V, hC, hK, hA, hrip, hsp, k => by
    have hpq : p = q := hC
    rw [hpq] at hrip
    exact k V X t hK hA rfl hrip hsp ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | (r, A) :: cs, p, X, t, V, hC, hK, hA, hrip, hsp, k => by
    obtain ⟨rel, hb, hd, hj, htgt, hC'⟩ := hC
    have := reg_in r
    have e8 : (S - 8).toNat = S.toNat - 8 := sub8 S (by omega)
    have h8 : 8 ≤ X.cpu.gpr.rsp.toNat := by rw [hsp, e8]; omega
    have hap : X.cpu.gpr.rsp.toNat ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 := by
      rw [hsp, e8]
      omega
    have hst' : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by rw [hsp]; exact hst
    refine lea_call hb hd hj htgt c hin (hR r) (hinR r) hK hA hrip hst' h8 hap
      fun V₁ Y t₁ hKY hAY hO hrY hkY => ?_
    rw [hsp] at hO
    obtain ⟨k1, k2⟩ := hkY
    have hsY : Y.cpu.gpr.rsp = S - 8 := k1.trans hsp
    exact calls_mid c hin hR hinR hst hhi cs (p + 7 + 5) Y t₁ V₁ hC' hKY hAY hrY hsY
      fun V' Z t' hKZ hAZ hO' hrZ hsZ hcZ =>
        k V' Z t' hKZ hAZ ⟨_, V₁, hO, hO'⟩ hrZ hsZ (Cs.trans (k2 : Cs X.cpu.gpr Y.cpu.gpr) hcZ)

/-- `add rsp, 8; jmp f` at offset `q` of `sti`: at `f`, `rsp` past the 8 bytes, the registers a call keeps. -/
theorem add_jmp {q rel : Nat} {e : Addr} {code : List Byte}
    (hb : BlkA prof sti sti_at q (q + 4) [Op.add 64 4 (.i 8)])
    (hd : Dec prof.feat sti (q + 4) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : q + 4 < sti.length)
    (htgt : sti_at.add (q + 4 + 5) + BitVec.ofNat 64 rel = e.add 0)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti) (hinE : CodeIn L e code) (h0 : 0 < code.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add q)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (Sp.blkA hb).run c hin (fun j' g' _ V' => j' = q + 4 ∧
    g' = wr X.cpu.gpr 4 (addR (gv X.cpu.gpr 64 4) (BitVec.ofNat 64 8)) ∧ V = V') hK hA hrip ?_ ?_
  · intro fl _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 := by rw [hgY]; exact rsp_add8 _
  have hcs : Cs X.cpu.gpr Y.cpu.gpr := by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine c.s_jmp_x hKY hAY hin hj hrY hd hinE h0 htgt ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ (by rw [hrZ, addr_add_zero]) (by rw [hgZ]; exact hsp) ?_
  rw [hgZ]
  exact hcs

/-- `J`, but at `m` the bytes that `P` takes those of `J m` to. -/
def Mid (J : Nat → (Addr → Byte) → Prop) (P : (Addr → Byte) → (Addr → Byte) → Prop) (m : Nat) :
    Nat → (Addr → Byte) → Prop :=
  fun i U => (i = m ∧ ∃ W, J m W ∧ P W U) ∨ (i ≠ m ∧ J i U)

/-- A constructor at `f` that goes on to `e` with the frame's `rsp`, the bytes `P` of those before (keeping the slot
of the return address, the frame's bytes and the arrays) and the registers a call keeps, is a function as
`Csu.csu_ok` asks when the code at `e` is one for `Mid J P m`, whatever its arguments. -/
theorem runs_pre {J : Nat → (Addr → Byte) → Prop} {P : (Addr → Byte) → (Addr → Byte) → Prop}
    {sp : Addr} {a₀ a₁ a₂ : BitVec 64} {m : Nat} {f e : Addr}
    (hgo : ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = f →
      X.cpu.gpr.rsp = sp - 64#64 →
      (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → P V V' →
        Z.cpu.rip = e → Z.cpu.gpr.rsp = sp - 64#64 → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') →
      GoG prof L o gev gP gE X t)
    (hP : ∀ V V', P V V' → ∀ a : Addr, (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → V' a = V a)
    (hs : 64 ≤ sp.toNat) (hs8 : sp.toNat + 8 ≤ 2 ^ 64)
    (hE : ∀ b₀ b₁ b₂ : BitVec 64, Csu.Runs prof F Wl L s₀ o gev gP gE (Mid J P m) sp b₀ b₁ b₂ m e) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m f := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  have n := Csu.sp_n hs
  refine hgo X t V hK hA hr hsp fun Z t' V' hKZ hAZ hPV hrZ hsZ hcZ => ?_
  have hra' : rdq(V', sp - 64#64) = csu_at.add j₂ :=
    (rdq_eq (V := V) (V' := V') (by rw [n]; omega) fun a h1 h2 =>
      hP V V' hPV a (.inl ⟨by rw [n] at h1; omega, by rw [n] at h2; omega⟩)).trans hra
  refine hE Z.cpu.gpr.rdi Z.cpu.gpr.rsi Z.cpu.gpr.rdx Z t' V' j₂ hKZ hAZ (Or.inl ⟨rfl, V, hI, hPV⟩) hrZ hsZ
    (fun _ => ⟨rfl, rfl, rfl⟩) hj₂ hra' fun W t'' V'' hKW hAW hI' h1 h2 hrW hb => ?_
  have hJ : J (m + 1) V'' := by
    rcases hI' with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  refine k W t'' V'' hKW hAW hJ (fun a ha => ?_) (fun a ha => ?_) hrW ?_
  · rw [h1 a ha]
    exact hP V V' hPV a (.inl ⟨by omega, ha.2⟩)
  · rw [h2 a ha]
    exact hP V V' hPV a (.inr ha)
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
    obtain ⟨c2, c3, c4, c5, c6, c7⟩ := hcZ
    exact ⟨by rw [b1, hsZ, hsp], b2.trans c2, b3.trans c3, b4.trans c4, b5.trans c5, b6.trans c6, b7.trans c7⟩

/-- A constructor `endbr64; sub rsp, 8`, then the registrar calls `cs` (each `lea rdi; call R`), then `add rsp, 8;
jmp e`, the `m`-th function `__libc_csu_init` calls, is a function as `Csu.csu_ok` asks when the code at `e` is one
for `Mid J (CallOut (sp - 64) cs) m`, whatever its arguments. -/
theorem callsK_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j q rel : Nat} {cs : List (Nat × Nat)} {e : Addr} {code : List Byte}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (htg : csuTg m = sti_at.add j) (hpro : BlkA prof sti sti_at j (j + 8) [Op.nop, Op.sub 64 4 (.i 8)])
    (hcs : CallsMid prof (j + 8) cs q) (hb : BlkA prof sti sti_at q (q + 4) [Op.add 64 4 (.i 8)])
    (hd : Dec prof.feat sti (q + 4) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : q + 4 < sti.length)
    (htgt : sti_at.add (q + 4 + 5) + BitVec.ofNat 64 rel = e.add 0) (hinE : CodeIn L e code)
    (h0 : 0 < code.length)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r))
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8 - 8) i)) (hhi : 7991300 + 80 ≤ sp.toNat)
    (hE : ∀ b₀ b₁ b₂ : BitVec 64,
      Csu.Runs prof F Wl L s₀ o gev gP gE (Mid J (CallOut (sp - 64#64) cs) m) sp b₀ b₁ b₂ m e) :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  refine runs_pre (P := CallOut (sp - 64#64) cs) (fun X t V hK hA hr hsp k => ?_) (fun V V' hO a ha => ?_) hs0 hs8
    hE
  · refine pro hpro c hin hK hA (hr.trans htg) fun Y t₀ hKY hAY hrY hsY hcY => ?_
    rw [hsp] at hsY
    refine calls_mid c hin hR hinR hst (by rw [n]; omega) cs (j + 8) Y t₀ V hcs hKY hAY hrY hsY
      fun V' Z t' hKZ hAZ hO hrZ hsZ hcZ => ?_
    refine add_jmp hb hd hj htgt c hin hinE h0 hKZ hAZ hrZ fun Z' t'' hKZ' hAZ' hrZ' hsZ' hcZ' => ?_
    refine k Z' t'' V' hKZ' hAZ' hO hrZ' ?_ (Cs.trans hcY (Cs.trans hcZ hcZ'))
    rw [hsZ', hsZ]
    exact BitVec.sub_add_cancel _ _
  · have hn : ¬ InR tabs a.toNat := fun ht => by
      have := tabs_in ht
      omega
    exact CallOut.out_t (by rw [n]; omega) hn (by rw [n]; omega) cs V V' hO

end FV7z.Ctor
