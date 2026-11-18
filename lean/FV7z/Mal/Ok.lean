import FV7z.Mal.Heap
import FV7z.Hwc.Vc
/-!
# `malloc` after the first call as a contract that holds (PLAN.md G3, `malloc`)

`Mal.At` (in `Hwc.Call`) asks of a `call` of `malloc` more than one can prove: it is for every footprint, so the
frame `malloc` stores to and the top it splits need not be in it, and its `Pm` is kept by every call, so no bound on
the top can be in it. `AtH` is the form that holds:

- `AtH prof F Wl L o fb hi e Pm`: for the footprint `F`, `Wl` and the TLS block `fb` of the run, the stack from
  `hi + 216` below `rsp` (224 bytes of it in `Wl`), `Pm (k + 1)` at the call: the return with `p` in `rax`,
  `[p, p + n)` below `hi`, the bytes outside the heap's words and the frame as at the call, and `Pm k` for every byte
  map that agrees with the one at the return from `0x792980` to `hi` but for `[p, p + n)`.
- `Hp.mv`: `Hp` (a top of at least 16 bytes) for bytes that agree from `0x792980` to `hi`.
- `at_hp`: `AtH` of `malloc` (`0x633160`) with `Pm k = Hp … (1072 k + 16)` (`mal_hp`; the 16 keep the top's
  size word below `hi`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Mal

/-- What a `call` of `malloc` at `e` does after the first call, for the footprint `F`, `Wl` and the TLS block `fb`:
see the module doc. -/
def AtH (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle) (fb : Addr)
    (hi : Nat) (e : Addr) (Pm : Nat → (Addr → Byte) → Prop) : Prop :=
  ∀ {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte} {j k : Nat},
    Seg prof F Wl L s₀ o → s₀.cpu.seg.fsBase = fb → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e →
    Pm (k + 1) V → X.cpu.gpr.rdi.toNat ≤ 1024 → hi + 216 ≤ X.cpu.gpr.rsp.toNat →
    X.cpu.gpr.rsp.toNat + 40 < 2 ^ 64 → (∀ i < 224, Foot Wl (Addr.add (X.cpu.gpr.rsp - 216#64) i)) →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ Z t' (V₂ : Addr → Byte) (p : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = p →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      8032256 + 16 ≤ p.toNat → p.toNat + X.cpu.gpr.rdi.toNat ≤ hi →
      (∀ a : Addr, p.toNat ≤ a.toNat → a.toNat < p.toNat + X.cpu.gpr.rdi.toNat → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 208 < X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) → V₂ a = V a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < p.toNat ∨ p.toNat + X.cpu.gpr.rdi.toNat ≤ a.toNat) → W a = V₂ a) → Pm k W) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- `Hp` for bytes that agree from `0x792980` to `hi`. -/
theorem Hp.mv {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m : Nat} {V W : Addr → Byte}
    (h : Hp F Wl fb hi m V) (hm : 16 ≤ m) (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi → W a = V a) :
    Hp F Wl fb hi m W := by
  obtain ⟨C, T, szw, sm, G, hf1, hf2, hc1, hc2, hT, hTh, hhi, htop, hsz, hsm, hle, hge, hTF⟩ := h
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have et : (7940768#64 : Addr).toNat = 7940768 := rfl
  have es : (7942856#64 : Addr).toNat = 7942856 := rfl
  refine ⟨C, T, szw, sm, G.mv (E := T.toNat) hf1 hf2 hc1 hc2 (by omega) fun a a1 a2 _ => hW a a1 (by omega),
    hf1, hf2, hc1, hc2, hT, hTh, hhi, ?_, ?_, ?_, hle, hge, hTF⟩
  · rw [rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a a1 a2 =>
      hW a (by rw [et] at a1; omega) (by rw [et] at a2; omega)]
    exact htop
  · rw [rd_eq (V := V) (x := T + 8#64) (n := 8) (by rw [e8]; omega) fun a a1 a2 =>
      hW a (by rw [e8] at a1; omega) (by rw [e8] at a2; omega)]
    exact hsz
  · rw [rd_eq (V := V) (x := 7942856#64) (n := 8) (by rw [es]; omega) fun a a1 a2 =>
      hW a (by rw [es] at a1; omega) (by rw [es] at a2; omega)]
    exact hsm

/-- `malloc` after the first call: `AtH` with `Pm k` the heap with a top of at least `1072 k + 16` bytes. -/
theorem at_hp {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {o : Oracle}
    {fb : Addr} {hi : Nat} (hin : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm) :
    AtH prof F Wl L o fb hi mnx_at fun k W => Hp F Wl fb hi (1072 * k + 16) W := by
  intro s₀ gev gP gE X t V e' code j k c hfs hK hA hrip hH hn hhi hR hsw hin₂ hj hra kc
  have e : 1072 * (k + 1) + 16 = 1072 * k + 16 + 1072 := by omega
  rw [e] at hH
  exact mal_hp c hfs hin hinI hK hA hrip hH hn hhi hR hsw hin₂ hj hra kc

/-- The bytes of `Kn` are kept by `malloc` (`AtH`'s frame: below the chunk, apart from `main_arena.top`). -/
theorem kn_kept {V V₂ : Addr → Byte} {p : Addr} (hp : 8032256 + 16 ≤ p.toNat)
    (h : ∀ a : Addr, a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat → V₂ a = V a) :
    ∀ a : Addr, Kn a → V₂ a = V a := fun a ha => by
  have := ha.lt
  exact h a (.inr ⟨by omega, by omega⟩)

end FV7z.Mal
