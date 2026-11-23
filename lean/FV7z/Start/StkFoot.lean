import FV7z.Start.GFoot
/-!
# The stack footprint conditions of `lif_ok` (PLAN.md G3, startup)

`Ndi.lif_ok` asks that the stack words its functions use, relative to its `sp` (`rsp` at `0x613434` less 160), are
stored into (`Wl`, `Wl'`) or data (`F`, `G`): `hpw`, `hst`, `hsm`, `hFs`, `hlG`, `hl`, `hst₂`, `hl₂`. All lie in
`[sp - 4552, sp + 160)`, so in the stack region `[lo, top)` of `zzsFoot` when that holds them.

- `wl_stk`, `lf_stk`, `gw_stk`, `gd_stk`: `n` bytes of the stack region, for each footprint.
- `lif_stk`: the eight conditions.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

variable {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {x : Addr} {n : Nat}

theorem wl_stk (htop : top ≤ 2 ^ 47) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ top) :
    ∀ i < n, Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (Addr.add x i) := fun i hi => by
  have t : (Addr.add x i).toNat = x.toNat + i := toNat_add_of_fits hi (by omega)
  exact foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega)))

theorem lf_stk (htop : top ≤ 2 ^ 47) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ top) :
    ∀ i < n, Foot (withNew (zzsFoot lo top L) [⟨B, 8192⟩]).data (Addr.add x i) := fun i hi =>
  foot_writes (wl_stk (B := B) htop h1 h2 i hi)

theorem gw_stk (htop : top ≤ 2 ^ 47) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ top) :
    ∀ i < n, Foot (lifG lo top B L).writes (Addr.add x i) := fun i hi => by
  have t : (Addr.add x i).toNat = x.toNat + i := toNat_add_of_fits hi (by omega)
  exact gw_stack htop (by omega) (by omega)

theorem gd_stk (htop : top ≤ 2 ^ 47) (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ top) :
    ∀ i < n, Foot (lifG lo top B L).data (Addr.add x i) := fun i hi =>
  foot_writes (gw_stk htop h1 h2 i hi)

/-- The stack conditions of `lif_ok` for the footprints of `launch_to_ptr` and `lifG`, when the stack region holds
`[sp - 4552, sp + 160)`. -/
theorem lif_stk {sp : Addr} (htop : top ≤ 2 ^ 47) (hlo : lo + 4552 ≤ sp.toNat) (hhi : sp.toNat + 160 ≤ top) :
    (∀ i < 40, Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (Addr.add (sp + 80#64) i)) ∧
    (∀ i < 4136, Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) (Addr.add (sp - 8#64 - 4136#64) i)) ∧
    (∀ i < 408, Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)
      (Addr.add (sp - 8#64 - 4136#64 - 240#64 - 168) i)) ∧
    (∀ a : Addr, sp.toNat - 408 ≤ a.toNat → a.toNat < sp.toNat →
      Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) a ∧
      Foot (withNew (zzsFoot lo top L) [⟨B, 8192⟩]).data a) ∧
    (∀ i < 24, Foot (lifG lo top B L).data (Addr.add (sp - 24#64) i)) ∧
    (∀ i < 48, Foot (lifG lo top B L).data (Addr.add (sp + 80#64) i)) ∧
    (∀ i < 40, Foot (lifG lo top B L).writes (Addr.add (sp + 128#64 - 40#64) i)) ∧
    (∀ i < 32, Foot (lifG lo top B L).data (Addr.add (sp + 128#64) i)) := by
  have t1 : (sp + 80#64).toNat = sp.toNat + 80 := by bv_omega
  have t2 : (sp - 8#64 - 4136#64).toNat = sp.toNat - 4144 := by bv_omega
  have t3 : (sp - 8#64 - 4136#64 - 240#64 - 168).toNat = sp.toNat - 4552 := by bv_omega
  have t4 : (sp - 24#64).toNat = sp.toNat - 24 := by bv_omega
  have t5 : (sp + 128#64 - 40#64).toNat = sp.toNat + 88 := by bv_omega
  have t6 : (sp + 128#64).toNat = sp.toNat + 128 := by bv_omega
  refine ⟨wl_stk htop (by rw [t1]; omega) (by rw [t1]; omega), wl_stk htop (by rw [t2]; omega) (by rw [t2]; omega),
    wl_stk htop (by rw [t3]; omega) (by rw [t3]; omega), fun a h1 h2 => ?_,
    gd_stk htop (by rw [t4]; omega) (by rw [t4]; omega), gd_stk htop (by rw [t1]; omega) (by rw [t1]; omega),
    gw_stk htop (by rw [t5]; omega) (by rw [t5]; omega), gd_stk htop (by rw [t6]; omega) (by rw [t6]; omega)⟩
  have w : Foot ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes) a :=
    foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega)))
  exact ⟨w, foot_writes (F := withNew (zzsFoot lo top L) [⟨B, 8192⟩]) w⟩

end FV7z.Start
