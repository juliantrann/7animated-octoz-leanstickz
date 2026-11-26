import FV7z.Mnx.PopNext
/-!
# The tcache's entries apart (PLAN.md G3, `malloc`, `free`)

`TcSep fb C bins`: each entry a 16-byte block (`next`, `key`) inside memory, apart from the tcache `C` and from the
bytes `GlB` reads (`Ifr.Gr`), two entries the same or apart, at most 7 in a bin (`mp_.tcache_count`). It gives the
side conditions of `tcache_get` (`dis`, `hG`, `eC` of `pop_inv`) and of `tcache_put` (`Ifr.Alloc`), and it is kept by
both.

- `TcSep.he`, `TcSep.eC`, `TcSep.dis`, `TcSep.hG`, `TcSep.hlen`: `pop_inv`'s side conditions for the head `e`.
- `TcSep.pop`: kept by `bpop`.
- `TcSep.alloc`: `Ifr.Alloc C bins p` when `p + 16`'s block is apart from every entry.
- `TcSep.put`: kept by `bput` with such an entry, its bin below 7.
- `mal_pop_sep`: `mal_pop_next` with `TcSep` before and after.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Mal (GlB TcSt bput)
namespace FV7z.Mnx

/-- The tcache's entries apart (see the module docstring). -/
structure TcSep (fb C : Addr) (bins : Nat → List Addr) : Prop where
  hc : C.toNat + 640 ≤ 2 ^ 64
  gc : ∀ a : Addr, Ifr.Gr fb a → a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat
  ln : ∀ i < 64, (bins i).length ≤ 7
  en : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 16 ≤ 2 ^ 64 ∧ (x.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat) ∧
    ∀ a : Addr, Ifr.Gr fb a → a.toNat < x.toNat ∨ x.toNat + 16 ≤ a.toNat
  ap : ∀ i < 64, ∀ x ∈ bins i, ∀ j < 64, ∀ y ∈ bins j,
    x = y ∨ x.toNat + 16 ≤ y.toNat ∨ y.toNat + 16 ≤ x.toNat

theorem mem_of_hd {l : List Addr} {e : Addr} (h : l.head? = some e) : e ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons.2 (.inl rfl)

theorem mem_bpop {bins : Nat → List Addr} {i j : Nat} {x : Addr} (hx : x ∈ bpop bins i j) : x ∈ bins j := by
  by_cases h : j = i
  · subst h
    simp only [bpop, ↓reduceIte] at hx
    exact List.mem_of_mem_tail hx
  · simp only [bpop, h, ↓reduceIte] at hx
    exact hx

theorem mem_bput {bins : Nat → List Addr} {i j : Nat} {q x : Addr} (hx : x ∈ bput bins i q j) :
    x = q ∨ x ∈ bins j := by
  by_cases h : j = i
  · subst h
    simp only [bput, ↓reduceIte, List.mem_cons] at hx
    exact hx
  · simp only [bput, h, ↓reduceIte] at hx
    exact .inr hx

namespace TcSep
variable {fb C e : Addr} {bins : Nat → List Addr} {i : Nat}

theorem he (s : TcSep fb C bins) (hk : i < 64) (hb : (bins i).head? = some e) : e.toNat + 16 ≤ 2 ^ 64 :=
  (s.en i hk e (mem_of_hd hb)).1

theorem eC (s : TcSep fb C bins) (hk : i < 64) (hb : (bins i).head? = some e) :
    e.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat + 8 := by
  have := (s.en i hk e (mem_of_hd hb)).2.1
  omega

theorem dis (s : TcSep fb C bins) (hk : i < 64) (hb : (bins i).head? = some e) :
    ∀ j < 64, ∀ x ∈ bins j, x.toNat + 8 ≤ 2 ^ 64 ∧ (x.toNat + 8 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) ∧
      (x.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat) := fun j hj x hx => by
  obtain ⟨x1, x2, -⟩ := s.en j hj x hx
  rcases s.ap j hj x hx i hk e (mem_of_hd hb) with rfl | h | h
  · omega
  · omega
  · omega

theorem hG (s : TcSep fb C bins) (hk : i < 64) (hb : (bins i).head? = some e) :
    ∀ a : Addr, Ifr.Gr fb a → (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) ∧
      (a.toNat < e.toNat + 8 ∨ e.toNat + 16 ≤ a.toNat) := fun a ha => by
  have h1 := s.gc a ha
  have h2 := (s.en i hk e (mem_of_hd hb)).2.2 a ha
  omega

theorem hlen (s : TcSep fb C bins) (hk : i < 64) : (bins i).length < 65536 := by
  have := s.ln i hk
  omega

theorem pop (s : TcSep fb C bins) : TcSep fb C (bpop bins i) where
  hc := s.hc
  gc := s.gc
  ln := fun j hj => by
    have := s.ln j hj
    by_cases h : j = i
    · subst h
      simp only [bpop, ↓reduceIte, List.length_tail]
      omega
    · simp only [bpop, h, ↓reduceIte]
      exact this
  en := fun j hj x hx => s.en j hj x (mem_bpop hx)
  ap := fun j hj x hx j' hj' y hy => s.ap j hj x (mem_bpop hx) j' hj' y (mem_bpop hy)

/-- `free`'s `Ifr.Alloc` when the block of `p + 16` (the chunk's user bytes) is apart from every entry. -/
theorem alloc (s : TcSep fb C bins) {p : Addr}
    (hf : ∀ j < 64, ∀ y ∈ bins j, p.toNat + 32 ≤ y.toNat ∨ y.toNat + 16 ≤ p.toNat + 16) :
    Ifr.Alloc C bins p := by
  intro j hj y hy
  obtain ⟨y1, y2, -⟩ := s.en j hj y hy
  have := hf j hj y hy
  omega

/-- Kept by `bput` with an entry `q` apart from the others and from the tcache and `GlB`'s bytes, its bin below 7. -/
theorem put (s : TcSep fb C bins) {q : Addr} (hl : (bins i).length < 7) (hq : q.toNat + 16 ≤ 2 ^ 64)
    (qC : q.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ q.toNat)
    (qG : ∀ a : Addr, Ifr.Gr fb a → a.toNat < q.toNat ∨ q.toNat + 16 ≤ a.toNat)
    (hf : ∀ j < 64, ∀ y ∈ bins j, q.toNat + 16 ≤ y.toNat ∨ y.toNat + 16 ≤ q.toNat) :
    TcSep fb C (bput bins i q) where
  hc := s.hc
  gc := s.gc
  ln := fun j hj => by
    by_cases h : j = i
    · subst h
      simp only [bput, ↓reduceIte, List.length_cons]
      omega
    · simp only [bput, h, ↓reduceIte]
      exact s.ln j hj
  en := fun j hj x hx => by
    rcases mem_bput hx with rfl | hx
    · exact ⟨hq, qC, qG⟩
    · exact s.en j hj x hx
  ap := fun j hj x hx j' hj' y hy => by
    rcases mem_bput hx with rfl | hx' <;> rcases mem_bput hy with rfl | hy'
    · exact .inl rfl
    · have := hf j' hj' y hy'
      omega
    · have := hf j hj x hx'
      omega
    · exact s.ap j hj x hx' j' hj' y hy'

end TcSep

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `mal_pop_next` with `TcSep` for the side conditions: the entries below the frame `S`, `TcSep` kept. -/
theorem mal_pop_sep {fb S C n nb ix e : Addr} {bins : Nat → List Addr} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mnx_at mnx) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hcls : Im5.ClsN n nb) (hix : (nb + 18446744073709551599#64) >>> 4 = ix)
    (hk : ix.toNat < 64) (hrip : X.cpu.rip = mnx_at) (hdi : X.cpu.gpr.rdi = n)
    (hrsp : X.cpu.gpr.rsp = S + 216#64) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (f0 : 40 ≤ fb.toNat) (hf24 : fb.toNat + 28 ≤ S.toNat)
    (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (hs : TcSep fb C bins) (hb : (bins ix.toNat).head? = some e)
    (hC : C ≠ 0#64) (hCS : C.toNat + 640 ≤ S.toNat) (hD : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 16 ≤ S.toNat)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add e i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (e + 8#64) i))
    (hsw : ∀ i < 24, Foot Wl (Addr.add (S + 192#64) i))
    (hsd : ∀ i < 32, Foot F.data (Addr.add (S + 192#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 216#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      GlB F Wl fb C W → TcSt W C (bpop bins ix.toNat) → TcSep fb C (bpop bins ix.toNat) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = e → Z.cpu.gpr.rsp = S + 224#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  mal_pop_next c hfs hin hK hA hcls hix hk hrip hdi hrsp hS hlo f0 hf24 hg ht hb (hs.hlen hk) hC hCS
    (hD _ hk e (mem_of_hd hb)) (hs.eC hk hb) (hs.dis hk hb) (fun i hi x hx => by have := hD i hi x hx; omega)
    (hs.hG hk hb) hfb f2 f3 w1 w2 w3 hsw hsd hin₂ h₂ hra
    fun Z t' W hK' hA' g1 g2 => k Z t' W hK' hA' g1 g2 hs.pop

end FV7z.Mnx
