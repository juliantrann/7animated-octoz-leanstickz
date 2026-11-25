import FV7z.Ctor.Cx102
import FV7z.Ctor.Prep
import FV7z.C103.Holds
/-!
# Constructor 103: glibc's `init_cacheinfo` (PLAN.md §M, constructors)

`csuTg 103` (`0x41cef0`) is `init_cacheinfo` itself; `C103.c103_fnK` is its contract. Here it is a constructor as
`Csu.csu_ok` asks: its frame and the frames of `handle_intel` and `intel_check_word` lie in the 192 bytes below
`__libc_csu_init`'s return address slot, and it stores only there and to the `__x86_*` words (`C103.Gw`).

- `c103_runs`: `csuTg 103` for an invariant `J` that the bytes outside those two keep.
- `c103_jg`: the same for `Jg`, with the spec `wrSpec c103Wr`.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Hca (hca hca_at hca_jt)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem e256 (sp : Addr) : sp - 64#64 - 192#64 = sp - 256#64 := by bv_omega

/-- `csuTg 103` is a function as `Csu.csu_ok` asks, on processors whose leaves 4 and `0xB` end (H-CPU-cache): `J m`
gives the two jump tables, and `J (m + 1)` holds of the bytes after it (as before but for the 192 bytes below
`sp - 64` and the `__x86_*` words). -/
theorem c103_runs {J : Nat → (Addr → Byte) → Prop} {sp fb : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m : Nat} (hCe : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinH : CodeIn L hca_at hca) (hfs : s₀.cpu.seg.fsBase = fb)
    (htg : csuTg m = C103.c103_at)
    (hst : ∀ i < 192, Foot Wl (Addr.add (sp - 256#64) i)) (hld : ∀ i < 200, Foot F.data (Addr.add (sp - 256#64) i))
    (hS : 8029492 ≤ sp.toNat - 64)
    (hcn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcnf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcna : (fb + 40#64).toNat + 8 + 192 ≤ sp.toNat - 64 ∨ sp.toNat - 64 ≤ (fb + 40#64).toNat)
    (hcpu : ∀ x : Addr, 8014560 ≤ x.toNat → x.toNat < 8014728 → Foot F.data x)
    (htab : ∀ x : Addr, 7282688 ≤ x.toNat → x.toNat < 7283552 → Foot F.data x)
    (hgw : ∀ x : Addr, C103.Gw x → Foot Wl x ∧ Foot F.data x)
    (htb : ∀ W, J m W → List.map W (byteAddrs 0x6f2000#64 36) = hca_jt ∧
      List.map W (byteAddrs 7282852#64 156) = C103.c103_jt)
    (hJ : ∀ W V', J m W →
      (∀ a : Addr, ¬ (sp.toNat - 256 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → ¬ C103.Gw a → V' a = W a) →
      J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra kk
  have hs0 := hC.s0
  have hsl := sp.isLt
  have n64 := Csu.sp_n hs0
  have hT : C103.Te F Wl L fb X.cpu.gpr V :=
    ⟨by rw [hsp, e256]; exact hst, by rw [hsp, e256]; exact hld, by rw [hsp, n64]; omega,
      by rw [hsp, n64]; omega, hcn, hcnf, by rw [hsp, n64]; exact hcna, hcpu, htab, hgw, (htb V hI).1,
      (htb V hI).2, ⟨_, _, j₂, hC.code, hj₂, by rw [hsp]; exact hra⟩⟩
  refine (C103.c103_fnK hCe c hfs hin hinH).run hK hA (hr.trans htg) hT fun Y t' V' hKY hAY hrY hR => ?_
  obtain ⟨hs, hb, hp, h12, h13, h14, h15, hKd⟩ := hR
  unfold C103.Kd at hKd
  rw [hsp, n64] at hKd
  refine kk Y t' V' hKY hAY (hJ V V' hI fun a h1 h2 => hKd a (by omega) h2) (fun a ha => hKd a (by omega) ?_)
    (fun a ha => hKd a (by omega) ?_) (hrY.trans (by rw [hsp]; exact hra)) ⟨hs, hb, hp, h12, h13, h14, h15⟩
  · unfold C103.Gw
    omega
  · unfold C103.Gw
    omega

/-- The `__x86_*` words `init_cacheinfo` stores. -/
def c103Wr : List (Nat × Nat) := [(7942880, 7942944), (8029224, 8029236)]

theorem st_out {s n : Nat} (h : ¬ (s - 1024 ≤ n ∧ n < s + 8)) : ¬ (s - 256 ≤ n ∧ n < s - 64) := by omega

theorem gw_out {a : Addr} (h : ¬ InR c103Wr a.toNat) : ¬ C103.Gw a := by
  simp only [c103Wr, InR, or_false] at h
  unfold C103.Gw
  omega

/-- `c103_runs` for `Jg` and the spec `wrSpec c103Wr`. -/
theorem c103_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp fb : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m : Nat} (hCe : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti) (hinH : CodeIn L hca_at hca)
    (hfs : s₀.cpu.seg.fsBase = fb) (htg : csuTg m = C103.c103_at)
    (hst : ∀ i < 192, Foot Wl (Addr.add (sp - 256#64) i)) (hld : ∀ i < 200, Foot F.data (Addr.add (sp - 256#64) i))
    (hS : 8029492 ≤ sp.toNat - 64)
    (hcn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcnf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcna : (fb + 40#64).toNat + 8 + 192 ≤ sp.toNat - 64 ∨ sp.toNat - 64 ≤ (fb + 40#64).toNat)
    (hcpu : ∀ x : Addr, 8014560 ≤ x.toNat → x.toNat < 8014728 → Foot F.data x)
    (htab : ∀ x : Addr, 7282688 ≤ x.toNat → x.toNat < 7283552 → Foot F.data x)
    (hgw : ∀ x : Addr, C103.Gw x → Foot Wl x ∧ Foot F.data x)
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = wrSpec c103Wr) (hD : ∀ k, (spec k).Dep)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 1024)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ c103Wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (htb : ∀ W, G m W → List.map W (byteAddrs 0x6f2000#64 36) = hca_jt ∧
      List.map W (byteAddrs 7282852#64 156) = C103.c103_jt)
    (hG : ∀ W V', G m W →
      (∀ a : Addr, ¬ (sp.toNat - 256 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → ¬ C103.Gw a → V' a = W a) →
      G (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ m (csuTg m) := by
  refine c103_runs hCe c hC hin hinH hfs htg hst hld hS hcn hcnf hcna hcpu htab hgw (fun W hJ => htb W hJ.2)
    fun W V' hJ hv => jg_wrk hm hc (by omega) hspec hD (by decide) hB hXw (fun a h1 h2 => ?_)
      (hG W V' · hv) hJ
  exact hv a (st_out h2) (gw_out h1)

end FV7z.Ctor
