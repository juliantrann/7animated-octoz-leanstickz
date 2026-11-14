import FV7z.Start.SysSeg
import FV7z.Start.Break
import FV7z.Start.Quiet
/-!
# What a run's start keeps through `brk` and `arch_prctl` (PLAN.md G3, startup)

After a system call that changes the process the run goes on from the state the call leaves as a new start
(`Start/SysSeg.lean`). `Base s lim b fsb k` is what the calls to come need of a start `s`, and what each of them
leaves of the next: no `rseq` area, the default protection key open, the break `b`, the `fs` base `fsb`, the pages
from the break's up to the `lim`-th unmapped, below the end of the user address space, the thread's id `k.tid`, and no
signal waiting (`Start/Quiet.lean`).

- `free_of_map`: pages not mapped are free.
- `mapAnon_out`: `Memory.mapAnon` leaves the pages outside its range as they are.
- `Vz`: bytes with zeros in a range of addresses, those of new pages; `rd_Vz`: bytes read outside the range.
- `Saved`: the registers a call keeps.
- `Seg.foot_below`: the footprint of a run from a start with `Base` has no byte in the pages from the break's to the
  `lim`-th.
- `Seg.b_brk_grow`: `Seg.s_brk_grow` from a `Base`, to a `Base` with the new break: the run goes on from the state
  after the call, which is its own start, with zeros in the new pages.
- `Seg.b_set_fs`: `Seg.s_set_fs` likewise, to a `Base` with the new `fs` base.
- `Base.of_room`: a state with room above its break (`BreakRoom`), no `rseq` area and the default key open has
  `Base`; `launch_base`: `7zzs` at its first instruction has it, with `2 ^ 41` bytes above the break.
-/
namespace FV7z.Start
open ZellicX86

/-- What a run relies on of the kernel's record of its thread: the thread's id. -/
structure Kst where
  tid : Nat

/-- What the system calls to come need of a run's start `s`. -/
structure Base (s : State) (lim : Nat) (b fsb : Addr) (k : Kst) : Prop where
  rseq : s.thread.rseq = none
  pkru : s.cpu.pkru &&& 3 = 0
  brk : s.proc.mm.brk = b
  fsb : s.cpu.seg.fsBase = fsb
  le : pageUp b.toNat / 4096 ≤ lim
  top : 4096 * lim ≤ 2 ^ 47 - 4096
  free : ∀ p : PageNum, pageUp b.toNat / 4096 ≤ p.toNat → p.toNat ≤ lim → s.proc.mm.mem.map p = none
  tid : s.thread.tid = k.tid
  tpend : s.thread.pending = []
  ppend : s.proc.signal.pending = []
  df : s.cpu.rflags.df = false
  relro : Relro s.proc.mm.mem

theorem free_of_map {m : Memory} {P n : Nat} (h : ∀ p : PageNum, P ≤ p.toNat → p.toNat < P + n → m.map p = none) :
    m.free P n = true := by
  simp only [Memory.free, List.all_eq_true, List.mem_range]
  intro j hj
  unfold Memory.mapAt
  split
  · rename_i hlt
    have e : (BitVec.ofNat 52 (P + j)).toNat = P + j := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [h _ (by omega) (by omega)]
    rfl
  · rfl

theorem mapAnon_out {m : Memory} {P n : Nat} {prot : Prot} {p : PageNum} (h : ¬ (P ≤ p.toNat ∧ p.toNat < P + n)) :
    (m.mapAnon P n prot).map p = m.map p := by
  have hn : inPages P n p = false := by simp [inPages, h]
  simp only [Memory.mapAnon, hn, Bool.false_eq_true, ↓reduceIte]

/-- `Relro` of memory with the page map of memory with `Relro`. -/
theorem Relro.of_map {m m' : Memory} (h : m'.map = m.map) (hr : Relro m) : Relro m' := by
  intro i hi
  obtain ⟨mp, h1, h2⟩ := hr i hi
  refine ⟨mp, ?_, h2⟩
  unfold Memory.mapAt at h1 ⊢
  rw [h]
  exact h1

/-- New anonymous pages over unmapped ones keep `Relro`. -/
theorem Relro.grow {m : Memory} {P n : Nat} {prot : Prot} (hr : Relro m)
    (hf : ∀ p : PageNum, P ≤ p.toNat → p.toNat < P + n → m.map p = none) : Relro (m.mapAnon P n prot) := by
  intro i hi
  obtain ⟨mp, h1, h2⟩ := hr i hi
  refine ⟨mp, ?_, h2⟩
  have hl : 0x777 + i < 2 ^ 52 := by omega
  unfold Memory.mapAt at h1 ⊢
  rw [if_pos hl] at h1 ⊢
  rw [mapAnon_out ?_]
  · exact h1
  · rintro ⟨q1, q2⟩
    rw [hf _ q1 q2] at h1
    cases h1

/-- `V` with zeros at the addresses from `lo` up to `hi`: the bytes after new pages are mapped there. -/
def Vz (V : Addr → Byte) (lo hi : Nat) : Addr → Byte := fun a => if lo ≤ a.toNat ∧ a.toNat < hi then 0 else V a

theorem Vz_in {V : Addr → Byte} {lo hi : Nat} {a : Addr} (h1 : lo ≤ a.toNat) (h2 : a.toNat < hi) :
    Vz V lo hi a = 0 := by
  simp only [Vz, h1, h2, and_self, ↓reduceIte]

theorem Vz_out {V : Addr → Byte} {lo hi : Nat} {a : Addr} (h : ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    Vz V lo hi a = V a := by
  simp only [Vz, h, ↓reduceIte]

/-- Bytes read outside the range. -/
theorem rd_Vz (V : Addr → Byte) (lo hi : Nat) (x : Addr) (n : Nat)
    (h : ∀ i < n, ¬ (lo ≤ (x.add i).toNat ∧ (x.add i).toNat < hi)) :
    List.map (Vz V lo hi) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact Vz_out (h j hj)

/-- The registers a call keeps (System V): `g` has those of `g₀`. -/
def Saved (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- The break is below the end of the user address space. -/
theorem Base.brk_lt {s : State} {lim : Nat} {b fsb : Addr} {k : Kst} (h : Base s lim b fsb k) :
    b.toNat ≤ 2 ^ 47 - 4096 := by
  have h1 := h.le
  have h2 := h.top
  unfold pageUp at h1
  omega

/-- A state with room above its break has `Base`, up to the page of the break and the room. -/
theorem Base.of_room {s : State} {n : Nat} (hr : s.thread.rseq = none) (hp : s.cpu.pkru &&& 3 = 0)
    (h : BreakRoom s n) (hq : s.thread.pending = [] ∧ s.proc.signal.pending = []) (hdf : s.cpu.rflags.df = false)
    (hrel : Relro s.proc.mm.mem) :
    Base s (pageUp (s.proc.mm.brk.toNat + n) / 4096) s.proc.mm.brk s.cpu.seg.fsBase ⟨s.thread.tid⟩ := by
  obtain ⟨h1, h2⟩ := h
  simp only [stackTopMax] at h1
  refine ⟨hr, hp, rfl, rfl, ?_, ?_, fun p q1 q2 => free_page h2 q1 ?_, rfl, hq.1, hq.2, hdf, hrel⟩
  · simp only [pageUp]
    omega
  · omega
  · simp only [pageUp] at q2 ⊢
    omega

/-- `7zzs` at its first instruction, on a kernel `LinuxBoot.Modest`, started with no signal waiting: `Base`, with
`2 ^ 41` bytes above the break. -/
theorem launch_base {l : Launch} {m : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args m) (hM : l.prof.linux.Modest)
    (hq : l.args.threadPending = [] ∧ l.args.signal.pending = []) :
    Base l.s₀ (pageUp (l.s₀.proc.mm.brk.toNat + 2 ^ 41) / 4096) l.s₀.proc.mm.brk l.s₀.cpu.seg.fsBase
      ⟨l.s₀.thread.tid⟩ :=
  Base.of_room (launch_misc h).2.1 (launch_misc h).1 (launch_breakRoom h hroom hM (Nat.le_refl _))
    (launch_quiet h hq.1 hq.2) (by obtain ⟨_, _, _, _, _, _, _, _, hdf⟩ := launch_regs h; exact hdf)
    (launch_relro h)

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte} {lim : Nat} {b fsb : Addr} {k : Kst}

/-- The footprint of a run from a start with `Base` has no byte in the pages from the break's to the `lim`-th. -/
theorem foot_below (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) {a : Addr}
    (h : Foot (F.data ++ F.codeRgns) a) :
    ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧ a.toNat < (lim + 1) * 4096) := by
  rintro ⟨h1, h2⟩
  refine foot_mapped c.foot c.own h (hB.free _ ?_ ?_)
  · rw [pageOf_toNat]
    omega
  · rw [pageOf_toNat]
    omega

/-- `syscall` for `brk (rdi)` that grows the break of a start with `Base`, the kernel not refusing memory: the run
goes on from the state after, its own start, with the regions `N` of the new pages among what it may store into,
the new pages' bytes 0, and `Base` with the new break. -/
theorem b_brk_grow (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 12)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hgt : pageUp b.toNat / 4096 < pageUp X.cpu.gpr.rdi.toNat / 4096)
    (hlim : pageUp X.cpu.gpr.rdi.toNat / 4096 ≤ lim)
    {N : List Rgn} (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096))
    (k' : ∀ s₁ t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim X.cpu.gpr.rdi fsb k →
      Agree (withNew F N) s₁.proc.mm.mem
        (Vz V (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096)) →
      s₁.cpu.rip = e'.add (j + len) →
      s₁.cpu.gpr = (sysGpr X len).set 0 X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sysEv X X.cpu.gpr.rdi]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  have hbk : X.proc.mm.brk = b := hK.brk.trans hB.brk
  obtain ⟨-, -, -, hlo, -⟩ := c.ready.layout
  have hlo' : X.proc.mm.brkMin.toNat ≤ b.toNat := by rw [hK.brkMin, ← hB.brk]; exact hlo
  have hlow : X.proc.mm.brkMin.toNat ≤ X.cpu.gpr.rdi.toNat := by
    have h := hgt
    unfold pageUp at h
    omega
  have htop := hB.top
  have h0 : ∀ a, Foot N a → Vz V (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096) a = 0 := by
    rintro a ⟨r, hr, h3, h4⟩
    obtain ⟨h1, h2⟩ := hN r hr
    exact Vz_in (by omega) (by omega)
  have hV : ∀ a, Foot F.data a → ¬ Foot N a →
      Vz V (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096) a = V a :=
    fun a ha _ => Vz_out fun h => c.foot_below hB (foot_data ha) ⟨h.1, by omega⟩
  subst hbk
  refine c.s_brk_grow hK hA hin hj hrip hd hnr hmg hlow hgt (by omega) ?_ hB.rseq hB.pkru hN h0 hV ?_
  · rw [free_congr hK.mem_map]
    exact free_of_map fun p h1 h2 => hB.free p h1 (by omega)
  · rintro X' Y t' hK' hcpu rfl c' hA'
    refine k' _ t' c' ⟨?_, ?_, rfl, ?_, hlim, hB.top, ?_, ?_, ?_, ?_, ?_, ?_⟩ hA' ?_ ?_
    · show X'.thread.rseq = none
      rw [hK'.thread]
      exact hB.rseq
    · show X'.cpu.pkru &&& 3 = 0
      rw [hK'.pkru]
      exact hB.pkru
    · show X'.cpu.seg.fsBase = fsb
      rw [hK'.seg]
      exact hB.fsb
    · intro p h1 h2
      show (X'.proc.mm.mem.mapAnon _ _ _).map p = none
      rw [mapAnon_out (by rw [hK'.brk, hK.brk.symm]; omega), hK'.mem_map]
      exact hB.free p (by omega) h2
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
    · show Relro (X'.proc.mm.mem.mapAnon _ _ _)
      have e : X'.proc.mm.brk = X.proc.mm.brk := hK'.brk.trans hK.brk.symm
      refine Relro.grow (Relro.of_map hK'.mem_map hB.relro) fun p h1 h2 => ?_
      rw [e] at h1 h2
      rw [hK'.mem_map]
      exact hB.free p h1 (by omega)
    · show X'.cpu.rip.add len = _
      rw [hcpu, hrip, addr_add_add]
    · show ((X'.cpu.gpr.set 1 (X'.cpu.rip.add len)).set 11 ({ X'.cpu.rflags with rf := false } : Rflags).toBits).set 0
        X.cpu.gpr.rdi = _
      rw [hcpu]

/-- `syscall` for `arch_prctl (ARCH_SET_FS, rsi)` from a start with `Base`: the run goes on from the state after,
its own start, with `Base` of the new `fs` base. -/
theorem b_set_fs (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 158)
    (hopt : arg32 X.cpu.gpr.rdi = 0x1002) (ha : X.cpu.gpr.rsi.toNat < 2 ^ 47 - 4096)
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim b X.cpu.gpr.rsi k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 0 →
      GoG prof L o (gev ++ [sysEv X 0]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.s_set_fs hK hA hin hj hrip hd hnr hopt ha hB.rseq ?_
  rintro X' Y t' hK' hcpu rfl c' hA'
  refine k' _ t' c' ⟨?_, ?_, ?_, rfl, hB.le, hB.top, ?_, ?_, ?_, ?_, ?_, ?_⟩ hA' ?_ ?_
  · show X'.thread.rseq = none
    rw [hK'.thread]
    exact hB.rseq
  · show X'.cpu.pkru &&& 3 = 0
    rw [hK'.pkru]
    exact hB.pkru
  · show X'.proc.mm.brk = b
    rw [hK'.brk]
    exact hB.brk
  · intro p h1 h2
    show X'.proc.mm.mem.map p = none
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
  · show Relro X'.proc.mm.mem
    exact Relro.of_map hK'.mem_map hB.relro
  · show X'.cpu.rip.add len = _
    rw [hcpu, hrip, addr_add_add]
  · show ((X'.cpu.gpr.set 1 (X'.cpu.rip.add len)).set 11 ({ X'.cpu.rflags with rf := false } : Rflags).toBits).set 0
      0 = _
    rw [hcpu]

end FV7z.Fn.Seg
