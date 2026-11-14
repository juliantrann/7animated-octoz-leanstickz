import FV7z.Ndi.Env
import FV7z.Start.Grow
import FV7z.Sbrk.Next
/-!
# `Cx` on other bytes and a grown footprint (PLAN.md G3, startup)

`_dl_get_origin` (with its `malloc`) runs between `ndi_a` and `ndi_b`: it writes the stack below `sp`, the heap, the
words of `malloc` (`main_arena`, `mp_`, `global_max_fast`, `__curbrk`, the TLS words) and gives a new root whose
footprint has the heap's pages `N` added (`withNew F N`, `N ++ Wl`). What `Cx` reads is elsewhere:

- `Same sp V V'`: the bytes agree from `sp` on (the environment), below the data segment (the image's names), on the
  page of the GOT and at `__environ`.
- `Ev.Ok.mvg`, `NmOk.mvg`, `Cx.mvg`: the environment, the names and `Cx` on bytes `Same` as theirs, with a footprint
  and writes that have `F`'s and `Wl`'s; `*.mv`: with `withNew F N` and `N ++ Wl`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Ndi

theorem fwn {F : Footprint} {N : List Rgn} (hown : F.own = []) {a : Addr} (h : Foot F.data a) :
    Foot (withNew F N).data a := by
  simp only [Footprint.data, hown, List.append_nil] at h ⊢
  rcases foot_append_iff.1 h with h | h
  · exact foot_append_iff.2 (.inl (foot_append_iff.2 (.inr h)))
  · exact foot_append_iff.2 (.inr h)

theorem addk (p : Addr) (k : Nat) (hk : k < 2 ^ 64) :
    p.toNat ≤ (Addr.add p k).toNat ∨ (Addr.add p k).toNat < k := by
  have := p.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem addn {p : Addr} {k : Nat} (h : p.toNat + k < 2 ^ 64) : (Addr.add p k).toNat = p.toNat + k := by
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Reads at a constant address agree where the bytes do. -/
theorem rd_of {V V' : Addr → Byte} {x n : Nat} (hx : x + n < 2 ^ 64)
    (h : ∀ a : Addr, x ≤ a.toNat → a.toNat < x + n → V' a = V a) :
    List.map V' (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
  Sbrk.rd_eq (by rw [BitVec.toNat_ofNat]; omega) fun a h1 h2 => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1 h2
    exact h a h1 h2

/-- The bytes `V'` agree with `V` where `Cx` reads: from `sp` on, below the data segment (`0x777000`, the image's
names), the page of the GOT (`[0x792000, 0x792980)`), at `__environ` (`0x7a4798`). -/
def Same (sp : Addr) (V V' : Addr → Byte) : Prop :=
  ∀ x : Addr, sp.toNat ≤ x.toNat ∨ x.toNat < 7827456 ∨ (7938048 ≤ x.toNat ∧ x.toNat < 7940480) ∨
    (8013720 ≤ x.toNat ∧ x.toNat < 8013728) → V' x = V x

theorem Ev.Ok.mvg {E : Ev} {V V' : Addr → Byte} {F F' : Footprint} {sp : Addr} (h : E.Ok V F sp)
    (hF : ∀ a, Foot F.data a → Foot F'.data a) (hs : Same sp V V') : E.Ok V' F' sp := by
  have R : ∀ x : Addr, (sp.toNat ≤ x.toNat ∨ (8013720 ≤ x.toNat ∧ x.toNat + 8 ≤ 8013728)) →
      x.toNat + 8 ≤ 2 ^ 64 → rdq(V', x) = rdq(V, x) := fun x h1 h2 => by
    rw [Sbrk.rd_eq (V' := V') (V := V) (x := x) (n := 8) h2 fun a ha1 ha2 => hs a (by omega)]
  have hehi := h.ehi
  have hefit := h.efit
  refine
    { he := by rw [R (8013720#64) (.inr ⟨by decide, by decide⟩) (by decide)]; exact h.he
      he0 := h.he0
      ehi := h.ehi
      efit := h.efit
      erd := fun k hk => hF _ (h.erd k hk)
      eptr := fun i hi => by
        have e : (Addr.add E.envp (8 * i)).toNat = E.envp.toNat + 8 * i := addn (by omega)
        rw [R (Addr.add E.envp (8 * i)) (.inl (by rw [e]; omega)) (by rw [e]; omega)]
        exact h.eptr i hi
      enz := h.enz
      eend := h.eend
      shi := h.shi
      sfit := h.sfit
      sz := fun i hi => by
        have := h.sfit i hi
        have := h.shi i hi
        have e : (Addr.add (E.ptr i) (E.len i)).toNat = (E.ptr i).toNat + E.len i := addn (by omega)
        rw [hs (Addr.add (E.ptr i) (E.len i)) (.inl (by rw [e]; omega))]
        exact h.sz i hi
      spg := fun i hi x h1 h2 => hF _ (h.spg i hi x h1 h2)
      s2 := fun i hi => hF _ (h.s2 i hi) }

theorem Ev.Ok.mv {E : Ev} {V V' : Addr → Byte} {F : Footprint} {N : List Rgn} {sp : Addr} (h : E.Ok V F sp)
    (hown : F.own = []) (hs : Same sp V V') : E.Ok V' (withNew F N) sp :=
  h.mvg (fun _ => fwn hown) hs

theorem NmOk.mvg {E : Ev} {V V' : Addr → Byte} {F F' : Footprint} {sp a : Addr} {n : Nat}
    (h : NmOk E V F a n) (hE : E.Ok V F sp) (hF : ∀ a, Foot F.data a → Foot F'.data a) (hs : Same sp V V') :
    NmOk E V' F' a n := by
  have hlo := h.lo
  have qa : ∀ k ≤ n, V' (Addr.add a k) = V (Addr.add a k) := fun k hk =>
    hs _ (.inr (.inl (by rw [addn (p := a) (k := k) (by omega)]; omega)))
  have qp : ∀ i < E.N, ∀ k ≤ n, V' (Addr.add (E.ptr i) k) = V (Addr.add (E.ptr i) k) := fun i hi k hk => by
    have := hE.shi i hi
    rcases addk (E.ptr i) k (by omega) with h' | h'
    · exact hs _ (.inl (by omega))
    · exact hs _ (.inr (.inl (by omega)))
  exact
    { hn := h.hn
      lo := h.lo
      nnz := fun k hk => by rw [qa k (Nat.le_of_lt hk)]; exact h.nnz k hk
      nz := by rw [qa n (Nat.le_refl n)]; exact h.nz
      npg := fun x h1 h2 => hF _ (h.npg x h1 h2)
      nom := fun i hi hk => by
        rw [qp i hi n (Nat.le_refl n)]
        exact h.nom i hi fun k hk' => by rw [← qp i hi k (Nat.le_of_lt hk'), ← qa k (Nat.le_of_lt hk')]; exact hk k hk' }

theorem NmOk.mv {E : Ev} {V V' : Addr → Byte} {F : Footprint} {N : List Rgn} {sp a : Addr} {n : Nat}
    (h : NmOk E V F a n) (hE : E.Ok V F sp) (hown : F.own = []) (hs : Same sp V V') :
    NmOk E V' (withNew F N) a n :=
  h.mvg hE (fun _ => fwn hown) hs

/-- `Cx` on bytes `Same` as its own, a footprint `F'` with `F`'s data and writes `Wl'` with `Wl`'s. -/
theorem Cx.mvg {prof : Profile} {F F' : Footprint} {Wl Wl' : List Rgn} {L : List (Addr × List Byte)} {o : Oracle}
    {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V V' : Addr → Byte} {sp : Addr}
    (cx : Cx prof F Wl L o pl pc Pm E V sp) (hF : ∀ a, Foot F.data a → Foot F'.data a)
    (hW : ∀ a, Foot Wl a → Foot Wl' a) (hs : Same sp V V') : Cx prof F' Wl' L o pl pc Pm E V' sp :=
  { hin := cx.hin
    hig := cx.hig
    hil := cx.hil
    hl0 := cx.hl0
    hlen := cx.hlen
    hic := cx.hic
    hc0 := cx.hc0
    hcmp := cx.hcmp
    hPm := fun W hW' => cx.hPm W fun x h1 h2 => (hW' x h1 h2).trans (hs x (.inr (.inr (.inl ⟨h1, h2⟩))))
    hE := cx.hE.mvg hF hs
    n1 := cx.n1.mvg cx.hE hF hs
    n2 := cx.n2.mvg cx.hE hF hs
    n3 := cx.n3.mvg cx.hE hF hs
    n4 := cx.n4.mvg cx.hE hF hs
    n5 := cx.n5.mvg cx.hE hF hs
    n6 := cx.n6.mvg cx.hE hF hs
    n7 := cx.n7.mvg cx.hE hF hs
    h72 := cx.h72
    hstk := fun i hi => hW _ (cx.hstk i hi)
    hr := fun x h1 h2 => hF _ (cx.hr x h1 h2)
    hw := fun x h1 h2 => hW _ (cx.hw x h1 h2) }

/-- `Cx` on bytes `Same` as its own, the footprint grown by new pages `N`. -/
theorem Cx.mv {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {o : Oracle}
    {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V V' : Addr → Byte} {sp : Addr} {N : List Rgn}
    (cx : Cx prof F Wl L o pl pc Pm E V sp) (hown : F.own = []) (hs : Same sp V V') :
    Cx prof (withNew F N) (N ++ Wl) L o pl pc Pm E V' sp :=
  cx.mvg (fun _ => fwn hown) (fun _ h => foot_append_iff.2 (.inr h)) hs

end FV7z.Ndi
