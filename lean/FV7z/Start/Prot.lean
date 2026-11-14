import FV7z.Start.Base
import FV7z.Lemmas.SysProt
/-!
# `mprotect (a, n, PROT_READ)`, a step of a run (PLAN.md G3, startup)

`Lemmas/SysProt.lean`'s system call as a step of a run that `Fn.Seg` describes. The call changes the layout: the pages
of the range become read-only (glibc's startup protects its RELRO segment so, `_dl_protect_relro`). The run then goes
on from the state after as a new start, with a footprint `G` that no longer writes into those pages.

- `protMem`: memory with the mapped pages among the `n` from `P` given protection `prot`, in new areas.
- `prot_out`, `prot_some`, `prot_cases`, `prot_none`: its page map; `prot_readByte`: its bytes are those before.
- `prot_check_out`: the access check of a byte outside the pages; `prot_check_read`: a byte that could be read or
  written before can be read after, if `prot` allows reading.
- `footOk_prot`, `ready_prot`, `agree_prot`: `Footprint.Ok` of a footprint `G` whose bytes are bytes of `F`, those it
  writes outside the pages, the code outside the pages; `Ready`; the footprint's bytes.
- `Seg.s_mprotect_ro`: the step, to `Fn.Seg` of `G`; `Seg.b_mprotect_ro`: from a `Base` to a `Base`.
-/
namespace FV7z.Start
open ZellicX86

variable {m : Memory} {P n : Nat} {prot : Prot}

/-- `m` with the mapped pages among the `n` from `P` given protection `prot`, in new areas (`mprotect`). -/
abbrev protMem (m : Memory) (P n : Nat) (prot : Prot) : Memory := (m.protect P n prot).renumber P n

theorem prot_out {p : PageNum} (h : inPages P n p = false) : (protMem m P n prot).map p = m.map p := by
  simp only [Memory.renumber, Memory.protect, h, Bool.false_eq_true, ↓reduceIte]

/-- A page mapped before is mapped after, to the same backing with the same key; as it was outside the pages, with
protection `prot` inside. -/
theorem prot_some {p : PageNum} {m0 : Mapping} (hm : m.map p = some m0) :
    ∃ mp, (protMem m P n prot).map p = some mp ∧ mp.backing = m0.backing ∧ mp.pkey = m0.pkey ∧
      mp.special = m0.special ∧ mp.maxProt = m0.maxProt ∧ (inPages P n p = false → mp = m0) ∧
      (inPages P n p = true → mp.prot = prot) := by
  by_cases hi : inPages P n p = true
  · have e : ∃ ar, (protMem m P n prot).map p = some { m0 with prot := prot, area := ar } :=
      ⟨_, by simp only [Memory.renumber, Memory.protect, hi, ↓reduceIte, hm, Option.map_some]; rfl⟩
    obtain ⟨ar, e⟩ := e
    exact ⟨_, e, rfl, rfl, rfl, rfl, fun h => (by rw [hi] at h; cases h), fun _ => rfl⟩
  · have hi' : inPages P n p = false := by simpa using hi
    exact ⟨m0, by rw [prot_out hi', hm], rfl, rfl, rfl, rfl, fun _ => rfl, fun e => absurd e hi⟩

theorem prot_none {p : PageNum} (hm : m.map p = none) : (protMem m P n prot).map p = none := by
  by_cases hi : inPages P n p = true
  · simp only [Memory.renumber, Memory.protect, hi, ↓reduceIte, hm, Option.map_none]
  · have hi' : inPages P n p = false := by simpa using hi
    rw [prot_out hi', hm]

/-- `mprotect` keeps `Relro`: the pages stay mapped, their mappings as special as before. -/
theorem Relro.prot (hr : Relro m) : Relro (protMem m P n prot) := by
  intro i hi
  obtain ⟨mp, h1, h2⟩ := hr i hi
  have hl : 0x777 + i < 2 ^ 52 := by omega
  unfold Memory.mapAt at h1 ⊢
  rw [if_pos hl] at h1 ⊢
  obtain ⟨mp', e, -, -, hs, -⟩ := prot_some (P := P) (n := n) (prot := prot) h1
  exact ⟨mp', e, hs.trans h2⟩

/-- A page mapped after was mapped before. -/
theorem prot_cases {p : PageNum} {mp : Mapping} (h : (protMem m P n prot).map p = some mp) :
    ∃ m0, m.map p = some m0 ∧ mp.backing = m0.backing ∧ mp.pkey = m0.pkey ∧ mp.special = m0.special ∧
      mp.maxProt = m0.maxProt ∧ (inPages P n p = false → mp = m0) ∧ (inPages P n p = true → mp.prot = prot) := by
  rcases hm : m.map p with _ | m0
  · rw [prot_none hm] at h
    cases h
  · obtain ⟨mp', e, h1, h2, h3, h4, h5, h6⟩ := prot_some (P := P) (n := n) (prot := prot) hm
    rw [e] at h
    cases h
    exact ⟨m0, rfl, h1, h2, h3, h4, h5, h6⟩

theorem prot_readByte (x : Addr) : (protMem m P n prot).readByte x = m.readByte x := by
  have hb : (protMem m P n prot).backings = m.backings := rfl
  have hf : (protMem m P n prot).files = m.files := rfl
  rcases hm : m.map (pageOf x) with _ | m0
  · simp only [Memory.readByte, prot_none hm, hm]
  · obtain ⟨mp, e, h1, -⟩ := prot_some (P := P) (n := n) (prot := prot) hm
    simp only [Memory.readByte, e, hm, hb, hf, h1]

theorem prot_check_out {feat : Features} {pkru : BitVec 32} {acc : Access} {x : Addr}
    (h : inPages P n (pageOf x) = false) : (protMem m P n prot).check feat pkru acc x = m.check feat pkru acc x := by
  have hb : (protMem m P n prot).backings = m.backings := rfl
  have hf : (protMem m P n prot).files = m.files := rfl
  simp only [Memory.check, prot_out h, hb, hf]

/-- The check of a mapping's permissions and key for reading, from that of a mapping with the same key that allowed
reading or writing, and either the same protection or one that allows reading. -/
theorem rest_read {feat : Features} {pkru : BitVec 32} {acc : Access} {m0 mp : Mapping}
    (hacc : acc = .read ∨ acc = .write) (hk : mp.pkey = m0.pkey) (hp : mp.prot = m0.prot ∨ mp.prot.read = true)
    (hc : Memory.check.rest feat pkru acc m0 = none) : Memory.check.rest feat pkru .read mp = none := by
  unfold Memory.check.rest at hc ⊢
  rw [hk]
  by_cases c1 : (feat.pku && pkeyDenies pkru m0.pkey acc) = true
  · simp only [c1, ↓reduceIte] at hc
    cases hc
  · simp only [c1] at hc
    by_cases c2 : (!m0.allows feat acc) = true
    · simp only [c2, ↓reduceIte] at hc
      cases hc
    · have c2' : m0.allows feat acc = true := by simpa using c2
      have d1 : ¬ ((feat.pku && pkeyDenies pkru m0.pkey .read) = true) := by
        intro h
        apply c1
        rcases hacc with rfl | rfl
        · exact h
        · simp only [pkeyDenies, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
          exact ⟨h.1, .inl h.2⟩
      have d2 : mp.allows feat .read = true := by
        rcases hp with hp | hp
        · rcases hacc with rfl | rfl
          · simp only [Mapping.allows, hp] at c2' ⊢
            exact c2'
          · simp only [Mapping.allows] at c2'
            simp only [Mapping.allows, hp, c2', Bool.or_true, Bool.true_or]
        · simp only [Mapping.allows, hp, Bool.true_or]
      simp only [d1, d2, ↓reduceIte, Bool.not_true, Bool.false_eq_true]

/-- A byte that could be read or written before can be read after, if `prot` allows reading. -/
theorem prot_check_read {feat : Features} {pkru : BitVec 32} {acc : Access} {x : Addr} (hr : prot.read = true)
    (hacc : acc = .read ∨ acc = .write) (hc : m.check feat pkru acc x = none) :
    (protMem m P n prot).check feat pkru .read x = none := by
  have hb : (protMem m P n prot).backings = m.backings := rfl
  have hf : (protMem m P n prot).files = m.files := rfl
  rcases hm : m.map (pageOf x) with _ | m0
  · exact absurd hm (map_ne_none_of_check hc)
  · obtain ⟨mp, e, h1, h2, -, -, h5, h6⟩ := prot_some (P := P) (n := n) (prot := prot) hm
    rw [check_eq, hm] at hc
    rw [check_eq, e]
    simp only [hb, hf, h1]
    by_cases hbl : blocked m.files (m.backings m0.backing) = true
    · simp only [hbl, ↓reduceIte] at hc
      cases hc
    · simp only [hbl, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      refine rest_read hacc h2 ?_ hc
      by_cases hi : inPages P n (pageOf x) = true
      · exact .inr ((h6 hi).symm ▸ hr)
      · exact .inl (by rw [h5 (by simpa using hi)])

/-- `Footprint.Ok` after the `n` pages from `P` are made read-only: of a footprint `G` whose bytes are bytes of `F`,
those it writes outside the pages, with `F`'s code, which is outside the pages. -/
theorem footOk_prot {feat : Features} {X Y : State} {F G : Footprint} (hok : F.Ok feat X)
    (hmem : Y.proc.mm.mem = protMem X.proc.mm.mem P n ⟨true, false, false⟩) (hpk : Y.cpu.pkru = X.cpu.pkru)
    (hrs : X.thread.rseq = none) (hrs' : Y.thread.rseq = none) (hown : F.own = []) (hGo : G.own = [])
    (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages P n (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages P n (pageOf a) = false) : G.Ok feat Y := by
  have hcr : G.codeRgns = F.codeRgns := by simp only [Footprint.codeRgns, hGc]
  have hsub : ∀ a, Foot G.data a → Foot F.data a := by
    intro a ha
    simp only [Footprint.data, hGo, hown, List.append_nil] at ha ⊢
    rcases foot_append_iff.1 ha with ⟨r, hr, hm⟩ | ⟨r, hr, hm⟩
    · exact foot_append_iff.2 (.inl (hGw r hr a hm).1)
    · exact foot_append_iff.2 (hGr r hr a hm)
  have hsub' : ∀ a, Foot (G.data ++ G.codeRgns) a → Foot (F.data ++ F.codeRgns) a := by
    intro a ha
    rw [hcr] at ha
    rcases foot_append_iff.1 ha with ha | ha
    · exact foot_append_iff.2 (.inl (hsub a ha))
    · exact foot_append_iff.2 (.inr ha)
  have hbk : ∀ a mp, Y.proc.mm.mem.map (pageOf a) = some mp → ∃ m0, X.proc.mm.mem.map (pageOf a) = some m0 ∧
      Y.proc.mm.mem.backings mp.backing = X.proc.mm.mem.backings m0.backing ∧ mp.backing = m0.backing := by
    intro a mp hm
    rw [hmem] at hm ⊢
    obtain ⟨m0, h0, h1, -⟩ := prot_cases hm
    exact ⟨m0, h0, by rw [h1]; rfl, h1⟩
  have hrsY : rseqArea Y = [] := by simp only [rseqArea, hrs']
  have hrsX : rseqArea X = [] := by simp only [rseqArea, hrs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fits
    intro r hr
    rw [hcr] at hr
    rcases List.mem_append.1 hr with hr | hr
    · refine hfit r ?_
      simpa only [Footprint.data, hGo, List.append_nil] using hr
    · exact hok.fits r (List.mem_append_right _ hr)
  · -- writable
    intro r hr a hm
    obtain ⟨⟨q, hq, hqm⟩, hout⟩ := hGw r hr a hm
    rw [hmem, hpk, prot_check_out hout]
    exact hok.writable q hq a hqm
  · -- readable
    intro r hr a hm
    rw [hmem, hpk]
    rcases hGr r hr a hm with ⟨q, hq, hqm⟩ | ⟨q, hq, hqm⟩
    · obtain ⟨h1, h2⟩ := hok.writable q hq a hqm
      exact ⟨h1, prot_check_read rfl (.inr rfl) h2⟩
    · obtain ⟨h1, h2⟩ := hok.readable q hq a hqm
      exact ⟨h1, prot_check_read rfl (.inl rfl) h2⟩
  · -- code
    intro c hc
    rw [hGc] at hc
    obtain ⟨hacc, hb⟩ := hok.code c hc
    refine ⟨fun a hm => ?_, ?_⟩
    · rw [hmem, hpk, prot_check_out (hcode a ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, hm⟩)]
      exact hacc a hm
    · have e : readBytes Y.proc.mm.mem c.1 c.2.length = readBytes X.proc.mm.mem c.1 c.2.length := by
        unfold readBytes
        apply List.map_congr_left
        intro x _
        rw [hmem]
        exact prot_readByte x
      unfold Bytes at hb ⊢
      rw [e]
      exact hb
  · -- notKernel
    intro a ha mp hm
    obtain ⟨m0, h0, hb, -⟩ := hbk a mp hm
    rw [hb]
    exact hok.notKernel a (hsub' a ha) m0 h0
  · -- noAlias
    intro a b ha hb hne ma mb hma hmb
    rw [hrsY, List.append_nil] at ha hb
    obtain ⟨a0, ha0, hba, ea⟩ := hbk a ma hma
    obtain ⟨b0, hb0, hbb, eb⟩ := hbk b mb hmb
    rw [hba, hbb, ea, eb]
    exact hok.noAlias a b (by rw [hrsX, List.append_nil]; exact hsub' a ha)
      (by rw [hrsX, List.append_nil]; exact hsub' b hb) hne a0 b0 ha0 hb0
  · -- notShared
    intro a ha mp hm fp
    simp only [hGo, List.append_nil] at ha
    obtain ⟨r, hr, hrm⟩ := ha
    obtain ⟨⟨q, hq, hqm⟩, -⟩ := hGw r hr a hrm
    obtain ⟨m0, h0, hb, -⟩ := hbk a mp hm
    rw [hb]
    exact hok.notShared a ⟨q, List.mem_append_left _ hq, hqm⟩ m0 h0 fp
  · -- notFixed
    rintro a ⟨r, hr, -⟩
    rw [hGo] at hr
    cases hr
  · -- codeApart
    intro r hr q hq a hra hqa
    rw [hcr] at hq
    obtain ⟨r', hr', hm'⟩ := hsub a ⟨r, hr, hra⟩
    exact hok.codeApart r' hr' q hq a hm' hqa
  · -- rseqApart
    intro r hr
    rw [hrsY] at hr
    cases hr

/-- `Ready` after the pages are protected, for a thread without an `rseq` area. -/
theorem ready_prot {feat : Features} {X Y : State} (hR : Ready feat X)
    (hmem : Y.proc.mm.mem = protMem X.proc.mm.mem P n prot) (hbm : Y.proc.mm.brkMin = X.proc.mm.brkMin)
    (hbk : Y.proc.mm.brk = X.proc.mm.brk) (htf : Y.cpu.rflags.tf = false) (hac : Y.cpu.rflags.ac = false)
    (hth : Y.thread = X.thread) (hrs : X.thread.rseq = none) : Ready feat Y := by
  obtain ⟨⟨-, -, h3, h4⟩, -, l1, l2, l3, l4, l5, l6⟩ := hR
  refine ⟨⟨htf, hac, by rw [hth]; exact h3, by rw [hth]; exact h4⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RseqQuiet, hth, hrs]
  · intro g hg
    rw [hmem] at hg ⊢
    rcases hx : X.proc.mm.mem.map g with _ | m0
    · exact absurd hx (l1 g hg)
    · obtain ⟨mp, e, -⟩ := prot_some (P := P) (n := n) (prot := prot) hx
      rw [e]
      exact fun e => (by cases e)
  · intro p mp hp
    rw [hmem] at hp ⊢
    obtain ⟨m0, h0, h1, -⟩ := prot_cases hp
    show mp.backing < X.proc.mm.mem.fresh + n
    rw [h1]
    exact Nat.lt_of_lt_of_le (l2 p m0 h0) (Nat.le_add_right _ _)
  · rw [hbm]
    exact l3
  · rw [hbm, hbk]
    exact l4
  · intro p mp hp
    rw [hmem] at hp
    obtain ⟨m0, h0, -, -, -, h4, -⟩ := prot_cases hp
    rw [h4]
    exact l5 p m0 h0
  · intro p mp hp
    rw [hmem] at hp
    obtain ⟨m0, h0, -, -, h3, -⟩ := prot_cases hp
    rw [h3]
    exact l6 p m0 h0

/-- The footprint's bytes after are those before. -/
theorem agree_prot {X Y : State} {F G : Footprint} {V : Addr → Byte}
    (hmem : Y.proc.mm.mem = protMem X.proc.mm.mem P n prot) (hsub : ∀ a, Foot G.data a → Foot F.data a)
    (hA : Agree F X.proc.mm.mem V) : Agree G Y.proc.mm.mem V := by
  intro a ha
  rw [hmem, prot_readByte, hA a (hsub a ha)]

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte} {lim : Nat} {b fsb : Addr} {k : Kst}

/-- `syscall` for `mprotect (rdi, rsi, PROT_READ)` of mapped pages, none special, the kernel not refusing: the pages
are read-only, `rax` is 0. The run goes on from the state after, `Y`, as a new start, with a footprint `G` whose
bytes are bytes of `F`, those it writes outside the pages; `X'` is the state the call was made in. -/
theorem s_mprotect_ro (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 10)
    (hprot : X.cpu.gpr.rdx.toNat = 1) (hal : X.cpu.gpr.rdi.toNat % 4096 = 0) (hlen : 0 < X.cpu.gpr.rsi.toNat)
    (hwrap : X.cpu.gpr.rdi.toNat + pageUp X.cpu.gpr.rsi.toNat < 2 ^ 64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < pageUp X.cpu.gpr.rsi.toNat / 4096, ∃ m,
      X.proc.mm.mem.mapAt (X.cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false)
    (hrs : s₀.thread.rseq = none) {G : Footprint} {Wl' : List Rgn} (hGo : G.own = []) (hGc : G.code = F.code)
    (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a →
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (k' : ∀ X' Y t', KeptW Wl s₀ X' → X'.cpu = X.cpu →
      Y = sysSt (roSt X' (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096)) len 0 →
      Seg prof G Wl' L Y o → Agree G Y.proc.mm.mem V → GoG prof L o (gev ++ [sysEv X 0]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
  have hRX := c.ready.keptW c.foot c.hws hK'
  have hmapM : M.map = X.proc.mm.mem.map := hM.map
  have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
  have hmap' : ∀ i < pageUp (X.withMem M).cpu.gpr.rsi.toNat / 4096, ∃ m,
      (X.withMem M).proc.mm.mem.mapAt ((X.withMem M).cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false ∧
        m.maxProt.read = true := by
    intro i hi
    obtain ⟨m, hm, hs⟩ := hmap i hi
    have hm' : M.mapAt (X.cpu.gpr.rdi.toNat / 4096 + i) = some m := by
      simp only [Memory.mapAt, hmapM] at hm ⊢
      exact hm
    refine ⟨m, hm', hs, ?_⟩
    unfold Memory.mapAt at hm'
    split at hm'
    · exact hRX.layout.2.2.2.2.1 _ m hm'
    · cases hm'
  have hsub : ∀ a, Foot G.data a → Foot F.data a := by
    intro a ha
    simp only [Footprint.data, hGo, c.own, List.append_nil] at ha ⊢
    rcases foot_append_iff.1 ha with ⟨r, hr, hm⟩ | ⟨r, hr, hm⟩
    · exact foot_append_iff.2 (.inl (hGw r hr a hm).1)
    · exact foot_append_iff.2 (hGr r hr a hm)
  refine ⟨_, _, _, syscall_mprotect_ro (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hprot hal hlen hwrap
    (hmg _ _) hmap', k' (X.withMem M) _ _ hK' rfl rfl ?_ ?_⟩
  · exact
      { foot := footOk_prot hokX rfl rfl hrsX hrsX c.own hGo hGc hfit hGw hGr hcode
        ready := ready_prot hRX rfl rfl rfl htf hac rfl hrsX
        env := c.env
        code := hGc.trans c.code
        own := hGo
        hww := hww }
  · exact agree_prot rfl hsub (c.agreeK hK hA hM)

/-- `Seg.s_mprotect_ro` from a start with `Base`: the run goes on from the state after, its own start, with `Base`
as before. -/
theorem b_mprotect_ro (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 10)
    (hprot : X.cpu.gpr.rdx.toNat = 1) (hal : X.cpu.gpr.rdi.toNat % 4096 = 0) (hlen : 0 < X.cpu.gpr.rsi.toNat)
    (hwrap : X.cpu.gpr.rdi.toNat + pageUp X.cpu.gpr.rsi.toNat < 2 ^ 64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < pageUp X.cpu.gpr.rsi.toNat / 4096, ∃ m,
      X.proc.mm.mem.mapAt (X.cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false)
    {G : Footprint} {Wl' : List Rgn} (hGo : G.own = []) (hGc : G.code = F.code)
    (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a →
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (k' : ∀ s₁ t', Seg prof G Wl' L s₁ o → Base s₁ lim b fsb k → Agree G s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 0 →
      GoG prof L o (gev ++ [sysEv X 0]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.s_mprotect_ro hK hA hin hj hrip hd hnr hprot hal hlen hwrap hmg hmap hB.rseq hGo hGc hfit hGw hGr hcode
    hww ?_
  rintro X' Y t' hK' hcpu rfl c' hA'
  refine k' _ t' c' ⟨?_, ?_, ?_, ?_, hB.le, hB.top, ?_, ?_, ?_, ?_, ?_, ?_⟩ hA' ?_ ?_
  · show X'.thread.rseq = none
    rw [hK'.thread]
    exact hB.rseq
  · show X'.cpu.pkru &&& 3 = 0
    rw [hK'.pkru]
    exact hB.pkru
  · show X'.proc.mm.brk = b
    rw [hK'.brk]
    exact hB.brk
  · show X'.cpu.seg.fsBase = fsb
    rw [hK'.seg]
    exact hB.fsb
  · intro p h1 h2
    refine prot_none ?_
    rw [hK'.mem_map]
    exact hB.free p h1 h2
  · show X'.thread.tid = k.tid
    rw [hK'.thread]
    exact hB.tid
  · show X'.thread.pending = []
    rw [hK'.thread]
    exact hB.tpend
  · show X'.proc.signal.pending = []
    rw [hK'.proc]
    exact hB.ppend
  · show X'.cpu.rflags.df = false
    rw [hK'.df]
    exact hB.df
  · show Relro (protMem X'.proc.mm.mem _ _ _)
    exact Relro.prot (Relro.of_map hK'.mem_map hB.relro)
  · show X'.cpu.rip.add len = _
    rw [hcpu, hrip, addr_add_add]
  · show ((X'.cpu.gpr.set 1 (X'.cpu.rip.add len)).set 11 ({ X'.cpu.rflags with rf := false } : Rflags).toBits).set 0
      0 = _
    rw [hcpu]

end FV7z.Fn.Seg
