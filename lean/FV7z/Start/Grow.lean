import FV7z.Start.FootOk
/-!
# New anonymous pages: what a footprint and the layout keep (PLAN.md G3, startup)

`brk` that grows the break, and `mmap` of anonymous memory, leave the address space `Memory.mapAnon`: `n` pages from
page `P`, free before, now mapped to new zero pages. A run that makes such a call goes on from the state the call
leaves, seen as a new start (`Fn.Seg` at that state), with the new pages among what it may store into.

- `free_page`, `mapAnon_old`, `mapAnon_new`, `mapAnon_cases`, `mapAnon_back_old`, `mapAnon_back_new`: the page map
  and the backings of `Memory.mapAnon` over free pages.
- `mapAnon_check`, `mapAnon_readByte`, `mapAnon_readByte_new`: an access check and a byte of a page mapped before are
  as before; a byte of a new page is 0.
- `footOk_grow`: a footprint that was `Footprint.Ok`, owning nothing, with regions `N` in the new pages added to
  what it writes, is `Footprint.Ok` after, for a thread without an `rseq` area and with key 0 allowed.
- `ready_grow`: the state after is `Ready`.
- `agree_grow`: the bytes of the footprint after are those before, and zeros in `N`.
-/
namespace FV7z.Start
open ZellicX86

variable {m : Memory} {P n : Nat} {prot : Prot}

/-- A page among free ones is not mapped. -/
theorem free_page (hf : m.free P n = true) {p : PageNum} (h1 : P ≤ p.toNat) (h2 : p.toNat < P + n) :
    m.map p = none := by
  simp only [Memory.free, List.all_eq_true, List.mem_range] at hf
  have h := hf (p.toNat - P) (by omega)
  have e : P + (p.toNat - P) = p.toNat := by omega
  have e' : BitVec.ofNat 52 p.toNat = p := BitVec.eq_of_toNat_eq (by simp)
  rw [e] at h
  simpa [Memory.mapAt, p.isLt, e'] using h

theorem mapAnon_old (hf : m.free P n = true) {p : PageNum} {mp : Mapping} (h : m.map p = some mp) :
    (m.mapAnon P n prot).map p = some mp := by
  have hn : inPages P n p = false := by
    rw [← Bool.not_eq_true]
    intro hin
    simp only [inPages, decide_eq_true_eq] at hin
    rw [free_page hf hin.1 hin.2] at h
    cases h
  simp only [Memory.mapAnon, hn, Bool.false_eq_true, ↓reduceIte, h]

theorem mapAnon_new {p : PageNum} (h1 : P ≤ p.toNat) (h2 : p.toNat < P + n) :
    (m.mapAnon P n prot).map p =
      some ⟨prot, m.fresh + (p.toNat - P), 0, false, none, m.fresh, ⟨true, true, true⟩, false⟩ := by
  have hin : inPages P n p = true := by simp [inPages, h1, h2]
  simp only [Memory.mapAnon, hin, ↓reduceIte]

/-- A page mapped after is one mapped before, with its mapping, or a new one. -/
theorem mapAnon_cases (hf : m.free P n = true) {p : PageNum} {mp : Mapping}
    (h : (m.mapAnon P n prot).map p = some mp) :
    m.map p = some mp ∨ (m.map p = none ∧ P ≤ p.toNat ∧ p.toNat < P + n ∧
      mp = ⟨prot, m.fresh + (p.toNat - P), 0, false, none, m.fresh, ⟨true, true, true⟩, false⟩) := by
  by_cases hin : P ≤ p.toNat ∧ p.toNat < P + n
  · rw [mapAnon_new hin.1 hin.2] at h
    cases h
    exact .inr ⟨free_page hf hin.1 hin.2, hin.1, hin.2, rfl⟩
  · have hn : inPages P n p = false := by simp [inPages, hin]
    simp only [Memory.mapAnon, hn, Bool.false_eq_true, ↓reduceIte] at h
    exact .inl h

theorem mapAnon_back_old {i : Nat} (h : i < m.fresh) : (m.mapAnon P n prot).backings i = m.backings i := by
  have : ¬ (m.fresh ≤ i ∧ i < m.fresh + n) := by omega
  simp only [Memory.mapAnon, this, ↓reduceIte]

theorem mapAnon_back_new {k : Nat} (h : k < n) : (m.mapAnon P n prot).backings (m.fresh + k) = .priv zeroFrame := by
  have : m.fresh ≤ m.fresh + k ∧ m.fresh + k < m.fresh + n := by omega
  simp only [Memory.mapAnon, this, and_self, ↓reduceIte]

/-- The access check of a byte whose page was mapped before. -/
theorem mapAnon_check (hf : m.free P n = true) (hfr : ∀ p mp, m.map p = some mp → mp.backing < m.fresh)
    {feat : Features} {pkru : BitVec 32} {acc : Access} {x : Addr} (hx : m.map (pageOf x) ≠ none) :
    (m.mapAnon P n prot).check feat pkru acc x = m.check feat pkru acc x := by
  rcases hm : m.map (pageOf x) with _ | mp
  · exact absurd hm hx
  · have hb := mapAnon_back_old (P := P) (n := n) (prot := prot) (hfr _ _ hm)
    have hfiles : (m.mapAnon P n prot).files = m.files := rfl
    simp only [Memory.check, mapAnon_old hf hm, hm, hb, hfiles]

/-- A byte whose page was mapped before. -/
theorem mapAnon_readByte (hf : m.free P n = true) (hfr : ∀ p mp, m.map p = some mp → mp.backing < m.fresh)
    {x : Addr} (hx : m.map (pageOf x) ≠ none) : (m.mapAnon P n prot).readByte x = m.readByte x := by
  rcases hm : m.map (pageOf x) with _ | mp
  · exact absurd hm hx
  · have hb := mapAnon_back_old (P := P) (n := n) (prot := prot) (hfr _ _ hm)
    have hfiles : (m.mapAnon P n prot).files = m.files := rfl
    simp only [Memory.readByte, mapAnon_old hf hm, hm, hb, hfiles]

/-- A byte of a new page is 0. -/
theorem mapAnon_readByte_new {x : Addr} (h1 : P ≤ (pageOf x).toNat) (h2 : (pageOf x).toNat < P + n) :
    (m.mapAnon P n prot).readByte x = 0 := by
  simp only [Memory.readByte, mapAnon_new h1 h2, mapAnon_back_new (show (pageOf x).toNat - P < n by omega)]
  rfl

/-- The page of an address of a region in the pages `[P, P + n)`. -/
theorem in_page {r : Rgn} (hr : r.In (P * 4096) ((P + n) * 4096)) {a : Addr} (ha : r.Mem a) :
    P ≤ (pageOf a).toNat ∧ (pageOf a).toNat < P + n := by
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨h3, h4⟩ := ha
  rw [pageOf_toNat]
  omega

/-- A footprint that owns nothing, with regions `N` of new pages added to what it writes. -/
abbrev withNew (F : Footprint) (N : List Rgn) : Footprint := ⟨N ++ F.writes, [], F.reads, F.code⟩

theorem withNew_foot {F : Footprint} {N : List Rgn} (hown : F.own = []) {a : Addr}
    (h : Foot ((withNew F N).data ++ (withNew F N).codeRgns) a) : Foot N a ∨ Foot (F.data ++ F.codeRgns) a := by
  simp only [Footprint.data, Footprint.codeRgns, hown, List.append_nil] at h ⊢
  rcases foot_append_iff.1 h with h | h
  · rcases foot_append_iff.1 h with h | h
    · rcases foot_append_iff.1 h with h | h
      · exact .inl h
      · exact .inr (foot_append_iff.2 (.inl (foot_append_iff.2 (.inl h))))
    · exact .inr (foot_append_iff.2 (.inl (foot_append_iff.2 (.inr h))))
  · exact .inr (foot_append_iff.2 (.inr h))

/-- Every byte of a footprint that owns nothing is in a mapped page. -/
theorem foot_mapped {feat : Features} {X : State} {F : Footprint} (hok : F.Ok feat X) (hown : F.own = []) {a : Addr}
    (h : Foot (F.data ++ F.codeRgns) a) : X.proc.mm.mem.map (pageOf a) ≠ none := by
  simp only [Footprint.data, hown, List.append_nil] at h
  rcases foot_append_iff.1 h with h | ⟨r, hr, hm⟩
  · rcases foot_append_iff.1 h with ⟨r, hr, hm⟩ | ⟨r, hr, hm⟩
    · exact map_ne_none_of_check (hok.writable r hr a hm).2
    · exact map_ne_none_of_check (hok.readable r hr a hm).2
  · simp only [Footprint.codeRgns, List.mem_map] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact map_ne_none_of_check ((hok.code c hc).1 a hm).2

/-- `Footprint.Ok` after `n` pages from `P`, free before, are mapped anew: of the footprint with regions `N` in
those pages added to what it writes. -/
theorem footOk_grow {feat : Features} {X Y : State} {F : Footprint} {N : List Rgn}
    (hok : F.Ok feat X) (hl : LayoutOk feat X) (hfree : X.proc.mm.mem.free P n = true)
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.mapAnon P n ⟨true, true, false⟩)
    (hpk : Y.cpu.pkru = X.cpu.pkru) (hp0 : X.cpu.pkru &&& 3 = 0)
    (hrs : X.thread.rseq = none) (hrs' : Y.thread.rseq = none) (hown : F.own = [])
    (hN : ∀ r ∈ N, r.In (P * 4096) ((P + n) * 4096)) (htop : (P + n) * 4096 ≤ 2 ^ 47) :
    (withNew F N).Ok feat Y := by
  have hfr := hl.2.1
  have hmp : ∀ a, Foot (F.data ++ F.codeRgns) a → X.proc.mm.mem.map (pageOf a) ≠ none :=
    fun a ha => foot_mapped hok hown ha
  have hnp : ∀ a, Foot N a → P ≤ (pageOf a).toNat ∧ (pageOf a).toNat < P + n := by
    rintro a ⟨r, hr, hm⟩
    exact in_page (hN r hr) hm
  -- the mapping of a new byte, and of a byte of the footprint before
  have hnew : ∀ a, Foot N a → ∀ mp, Y.proc.mm.mem.map (pageOf a) = some mp →
      mp.backing = X.proc.mm.mem.fresh + ((pageOf a).toNat - P) ∧ mp.pkey = 0 ∧ mp.prot.write = true ∧
        Y.proc.mm.mem.backings mp.backing = .priv zeroFrame := by
    intro a ha mp hm
    obtain ⟨h1, h2⟩ := hnp a ha
    rw [hmem, mapAnon_new h1 h2] at hm
    cases hm
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [hmem]
    exact mapAnon_back_new (by omega)
  have hold : ∀ a, Foot (F.data ++ F.codeRgns) a → ∀ mp, Y.proc.mm.mem.map (pageOf a) = some mp →
      X.proc.mm.mem.map (pageOf a) = some mp ∧ mp.backing < X.proc.mm.mem.fresh ∧
        Y.proc.mm.mem.backings mp.backing = X.proc.mm.mem.backings mp.backing := by
    intro a ha mp hm
    rcases hx : X.proc.mm.mem.map (pageOf a) with _ | m0
    · exact absurd hx (hmp a ha)
    · rw [hmem, mapAnon_old hfree hx] at hm
      cases hm
      refine ⟨rfl, hfr _ _ hx, ?_⟩
      rw [hmem]
      exact mapAnon_back_old (hfr _ _ hx)
  have hchk : ∀ a, Foot (F.data ++ F.codeRgns) a → ∀ acc,
      Y.proc.mm.mem.check feat Y.cpu.pkru acc a = X.proc.mm.mem.check feat X.cpu.pkru acc a := by
    intro a ha acc
    rw [hmem, hpk]
    exact mapAnon_check hfree hfr (hmp a ha)
  have hdata : ∀ r, r ∈ F.writes ∨ r ∈ F.reads → ∀ a, r.Mem a → Foot (F.data ++ F.codeRgns) a := by
    intro r hr a hm
    refine foot_append_iff.2 (.inl ⟨r, ?_, hm⟩)
    simp only [Footprint.data, hown, List.append_nil, List.mem_append]
    exact hr
  have hcode : ∀ c ∈ F.code, ∀ a, Rgn.Mem ⟨c.1, c.2.length⟩ a → Foot (F.data ++ F.codeRgns) a := by
    intro c hc a hm
    exact foot_append_iff.2 (.inr ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, hm⟩)
  have hrsY : rseqArea Y = [] := by simp only [rseqArea, hrs']
  have hrsX : rseqArea X = [] := by simp only [rseqArea, hrs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fits
    intro r hr
    have hr' : r ∈ N ∨ r ∈ F.data ++ F.codeRgns := by
      simp only [Footprint.data, Footprint.codeRgns, hown, List.append_nil, List.mem_append] at hr ⊢
      rcases hr with ((hr | hr) | hr) | hr
      · exact .inl hr
      · exact .inr (.inl (.inl hr))
      · exact .inr (.inl (.inr hr))
      · exact .inr (.inr hr)
    rcases hr' with hr' | hr'
    · exact Nat.le_trans (hN r hr').2 (Nat.le_trans htop (by decide))
    · exact hok.fits r hr'
  · -- writable
    intro r hr a hm
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨h1, h2⟩ := hnp a ⟨r, hr, hm⟩
      have hlt : a.toNat < 2 ^ 47 := Nat.lt_of_lt_of_le hm.2 (Nat.le_trans (hN r hr).2 htop)
      have hY := mapAnon_new (m := X.proc.mm.mem) (prot := ⟨true, true, false⟩) h1 h2
      rw [← hmem] at hY
      obtain ⟨-, hk, hw, hb⟩ := hnew a ⟨r, hr, hm⟩ _ hY
      rw [← hpk] at hp0
      exact ⟨canonical_low hlt _, (check_priv (feat := feat) hY hk hb hp0).2 hw⟩
    · rw [hchk a (hdata r (.inl hr) a hm)]
      exact hok.writable r hr a hm
  · -- readable
    intro r hr a hm
    rw [hchk a (hdata r (.inr hr) a hm)]
    exact hok.readable r hr a hm
  · -- code
    intro c hc
    obtain ⟨hacc, hb⟩ := hok.code c hc
    refine ⟨fun a hm => ?_, ?_⟩
    · rw [hchk a (hcode c hc a hm)]
      exact hacc a hm
    · have e : readBytes Y.proc.mm.mem c.1 c.2.length = readBytes X.proc.mm.mem c.1 c.2.length := by
        unfold readBytes
        apply List.map_congr_left
        intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
        have hfit : Rgn.Fits ⟨c.1, c.2.length⟩ :=
          hok.fits _ (List.mem_append_right _ (List.mem_map.2 ⟨c, hc, rfl⟩))
        rw [hmem]
        exact mapAnon_readByte hfree hfr (hmp _ (hcode c hc _ (mem_add_of_fits hi hfit)))
      unfold Bytes at hb ⊢
      rw [e]
      exact hb
  · -- notKernel
    intro a ha mp hm
    rcases withNew_foot hown ha with ha | ha
    · rw [(hnew a ha mp hm).2.2.2]
      exact ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩
    · obtain ⟨hx, -, hb⟩ := hold a ha mp hm
      rw [hb]
      exact hok.notKernel a ha mp hx
  · -- noAlias
    intro a b ha hb hne ma mb hma hmb
    rw [hrsY, List.append_nil] at ha hb
    have hne' : (pageOf a).toNat ≠ (pageOf b).toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
    rcases withNew_foot hown ha with ha | ha <;> rcases withNew_foot hown hb with hb | hb
    · obtain ⟨ea, -, -, pa⟩ := hnew a ha ma hma
      obtain ⟨eb, -, -, -⟩ := hnew b hb mb hmb
      obtain ⟨a1, a2⟩ := hnp a ha
      obtain ⟨b1, b2⟩ := hnp b hb
      refine ⟨by omega, fun fp e => ?_⟩
      rw [pa] at e
      cases e
    · obtain ⟨ea, -, -, pa⟩ := hnew a ha ma hma
      obtain ⟨-, lb, -⟩ := hold b hb mb hmb
      refine ⟨by omega, fun fp e => ?_⟩
      rw [pa] at e
      cases e
    · obtain ⟨-, la, -⟩ := hold a ha ma hma
      obtain ⟨eb, -, -, pb⟩ := hnew b hb mb hmb
      refine ⟨by omega, fun fp _ => ?_⟩
      rw [pb]
      exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
    · obtain ⟨xa, -, ba⟩ := hold a ha ma hma
      obtain ⟨xb, -, bb⟩ := hold b hb mb hmb
      rw [ba, bb]
      exact hok.noAlias a b (by rw [hrsX, List.append_nil]; exact ha) (by rw [hrsX, List.append_nil]; exact hb) hne
        ma mb xa xb
  · -- notShared
    intro a ha mp hm fp
    simp only [List.append_nil] at ha
    rcases foot_append_iff.1 ha with ha | ⟨r, hr, hrm⟩
    · rw [(hnew a ha mp hm).2.2.2]
      intro e
      cases e
    · have ha' := hdata r (.inl hr) a hrm
      obtain ⟨hx, -, hb⟩ := hold a ha' mp hm
      rw [hb]
      exact hok.notShared a ⟨r, List.mem_append_left _ hr, hrm⟩ mp hx fp
  · -- notFixed
    rintro a ⟨r, hr, -⟩
    cases hr
  · -- codeApart
    intro r hr q hq a hra hqa
    have hq' : Foot (F.data ++ F.codeRgns) a := foot_append_iff.2 (.inr ⟨q, hq, hqa⟩)
    have hr' : r ∈ N ∨ r ∈ F.data := by
      simp only [Footprint.data, hown, List.append_nil, List.mem_append] at hr ⊢
      rcases hr with (hr | hr) | hr
      · exact .inl hr
      · exact .inr (.inl hr)
      · exact .inr (.inr hr)
    rcases hr' with hr' | hr'
    · obtain ⟨h1, h2⟩ := hnp a ⟨r, hr', hra⟩
      exact hmp a hq' (free_page hfree h1 h2)
    · exact hok.codeApart r hr' q hq a hra hqa
  · -- rseqApart
    intro r hr
    rw [hrsY] at hr
    cases hr

/-- `Ready` after `n` pages from `P`, free before and below the end of the user address space, are mapped anew, the
break at or above its lowest value, for a thread without an `rseq` area. -/
theorem ready_grow {feat : Features} {X Y : State} (hR : Ready feat X)
    (hfree : X.proc.mm.mem.free P n = true)
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.mapAnon P n prot)
    (hbm : Y.proc.mm.brkMin = X.proc.mm.brkMin) (hbk : X.proc.mm.brkMin.toNat ≤ Y.proc.mm.brk.toNat)
    (htf : Y.cpu.rflags.tf = false) (hac : Y.cpu.rflags.ac = false) (hth : Y.thread = X.thread)
    (hrs : X.thread.rseq = none) (htop : (P + n) * 4096 ≤ taskSize feat) : Ready feat Y := by
  obtain ⟨⟨-, -, h3, h4⟩, -, l1, l2, l3, -, l5, l6⟩ := hR
  refine ⟨⟨htf, hac, by rw [hth]; exact h3, by rw [hth]; exact h4⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RseqQuiet, hth, hrs]
  · intro g hg
    rw [hmem] at hg ⊢
    rcases hx : X.proc.mm.mem.map g with _ | m0
    · exact absurd hx (l1 g hg)
    · rw [mapAnon_old hfree hx]
      exact fun e => (by cases e)
  · intro p mp hp
    rw [hmem] at hp ⊢
    show mp.backing < X.proc.mm.mem.fresh + n
    rcases mapAnon_cases hfree hp with hx | ⟨-, h1, h2, rfl⟩
    · exact Nat.lt_of_lt_of_le (l2 p mp hx) (Nat.le_add_right _ _)
    · show X.proc.mm.mem.fresh + (p.toNat - P) < X.proc.mm.mem.fresh + n
      omega
  · rw [hbm]
    exact l3
  · rw [hbm]
    exact hbk
  · intro p mp hp
    rw [hmem] at hp
    rcases mapAnon_cases hfree hp with hx | ⟨-, -, -, rfl⟩
    · exact l5 p mp hx
    · rfl
  · intro p mp hp
    rw [hmem] at hp
    rcases mapAnon_cases hfree hp with hx | ⟨-, h1, h2, rfl⟩
    · exact l6 p mp hx
    · left
      exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) htop

/-- The footprint's bytes after: those before, and zeros in `N`. -/
theorem agree_grow {feat : Features} {X Y : State} {F : Footprint} {N : List Rgn} {V V' : Addr → Byte}
    (hok : F.Ok feat X) (hl : LayoutOk feat X) (hfree : X.proc.mm.mem.free P n = true)
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.mapAnon P n prot) (hown : F.own = [])
    (hN : ∀ r ∈ N, r.In (P * 4096) ((P + n) * 4096)) (hA : Agree F X.proc.mm.mem V)
    (h0 : ∀ a, Foot N a → V' a = 0) (hV : ∀ a, Foot F.data a → ¬ Foot N a → V' a = V a) :
    Agree (withNew F N) Y.proc.mm.mem V' := by
  intro a ha
  rw [hmem]
  by_cases hn : Foot N a
  · obtain ⟨r, hr, hm⟩ := hn
    obtain ⟨h1, h2⟩ := in_page (hN r hr) hm
    rw [mapAnon_readByte_new h1 h2, h0 a ⟨r, hr, hm⟩]
  · have ha' : Foot F.data a := by
      simp only [Footprint.data, hown, List.append_nil] at ha ⊢
      rcases foot_append_iff.1 ha with ha | ha
      · rcases foot_append_iff.1 ha with ha | ha
        · exact absurd ha hn
        · exact foot_append_iff.2 (.inl ha)
      · exact foot_append_iff.2 (.inr ha)
    rw [mapAnon_readByte hfree hl.2.1 (foot_mapped hok hown (foot_data ha')), hA a ha', hV a ha' hn]

end FV7z.Start
