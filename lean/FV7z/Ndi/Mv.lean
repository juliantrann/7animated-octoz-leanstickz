import FV7z.Ndi.Env
import FV7z.Start.Grow
import FV7z.Sbrk.Next
/-!
# `Cx` on other bytes and a grown footprint (PLAN.md G3, startup)

`_dl_get_origin` (with its `malloc`) runs between `ndi_a` and `ndi_b`: it writes the stack below `sp`, the heap, the
words of `malloc` (`main_arena`, `mp_`, `global_max_fast`, `__curbrk`, the TLS words) and gives a new root whose
footprint has the heap's pages `N` added (`withNew F N`, `N ++ Wl`). What `Cx` reads is elsewhere:

- `Same sp V V'`: the bytes agree from `sp` on (the environment), below `0x792980` (the image's names, the GOT) and
  at `__environ`.
- `Ev.Ok.mv`, `NmOk.mv`, `Cx.mv`: the environment, the names and `Cx` on bytes `Same` as theirs, with `withNew F N`
  and `N ++ Wl`.
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

/-- The bytes `V'` agree with `V` where `Cx` reads: from `sp` on, below `0x792980`, at `__environ` (`0x7a4798`). -/
def Same (sp : Addr) (V V' : Addr → Byte) : Prop :=
  ∀ x : Addr, sp.toNat ≤ x.toNat ∨ x.toNat < 7940480 ∨ (8013720 ≤ x.toNat ∧ x.toNat < 8013728) → V' x = V x

theorem Ev.Ok.mv {E : Ev} {V V' : Addr → Byte} {F : Footprint} {N : List Rgn} {sp : Addr} (h : E.Ok V F sp)
    (hown : F.own = []) (hs : Same sp V V') : E.Ok V' (withNew F N) sp := by
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
      erd := fun k hk => fwn hown (h.erd k hk)
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
      spg := fun i hi x h1 h2 => fwn hown (h.spg i hi x h1 h2)
      s2 := fun i hi => fwn hown (h.s2 i hi) }

theorem NmOk.mv {E : Ev} {V V' : Addr → Byte} {F : Footprint} {N : List Rgn} {sp a : Addr} {n : Nat}
    (h : NmOk E V F a n) (hE : E.Ok V F sp) (hown : F.own = []) (hs : Same sp V V') :
    NmOk E V' (withNew F N) a n := by
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
      nnz := fun k hk => by rw [qa k hk.le]; exact h.nnz k hk
      nz := by rw [qa n le_rfl]; exact h.nz
      npg := fun x h1 h2 => fwn hown (h.npg x h1 h2)
      nom := fun i hi hk => by
        rw [qp i hi n le_rfl]
        exact h.nom i hi fun k hk' => by rw [← qp i hi k hk'.le, ← qa k hk'.le]; exact hk k hk' }

/-- `Cx` on bytes `Same` as its own, the footprint grown by new pages `N`. -/
theorem Cx.mv {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {o : Oracle}
    {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V V' : Addr → Byte} {sp : Addr} {N : List Rgn}
    (cx : Cx prof F Wl L o pl pc Pm E V sp) (hown : F.own = []) (hs : Same sp V V') :
    Cx prof (withNew F N) (N ++ Wl) L o pl pc Pm E V' sp :=
  { hin := cx.hin
    hig := cx.hig
    hil := cx.hil
    hl0 := cx.hl0
    hlen := cx.hlen
    hic := cx.hic
    hc0 := cx.hc0
    hcmp := cx.hcmp
    hPm := fun W hW => cx.hPm W fun x h1 h2 => (hW x h1 h2).trans (hs x (.inr (.inl h2)))
    hE := cx.hE.mv hown hs
    n1 := cx.n1.mv cx.hE hown hs
    n2 := cx.n2.mv cx.hE hown hs
    n3 := cx.n3.mv cx.hE hown hs
    n4 := cx.n4.mv cx.hE hown hs
    n5 := cx.n5.mv cx.hE hown hs
    n6 := cx.n6.mv cx.hE hown hs
    n7 := cx.n7.mv cx.hE hown hs
    h72 := cx.h72
    hstk := fun i hi => foot_append_iff.2 (.inr (cx.hstk i hi))
    hr := fun x h1 h2 => fwn hown (cx.hr x h1 h2)
    hw := fun x h1 h2 => foot_append_iff.2 (.inr (cx.hw x h1 h2)) }

end FV7z.Ndi
