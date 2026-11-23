import FV7z.Start.MCxEnt
/-!
# The footprint after `_dl_protect_relro` (PLAN.md G3, startup)

`_dl_non_dynamic_init` ends with `mprotect (0x777000, 0x1b000, PROT_READ)`: the 27 pages `0x777`–`0x791` become
read-only. `Ndi.lif_ok` goes on with a footprint `G` (and `Wl'`, what it may store into) that writes nothing there.
`lifG` is the footprint of `launch_to_ptr` with those pages moved to what is read, and the break's pages and the
first `MORECORE`'s (`brkN`) added to what is written.

- `lifG`: the footprint.
- `lifG_ok`: `hGo`, `hGc`, `hfit`, `hGw`, `hGr`, `hcode`, `hww` of `lif_ok`, for `Wl' = (lifG …).writes`.
- `gd_stack`, `gd_var`, `gd_brk`, `gd_relro`, `gw_stack`, `gw_var`, `gw_brk`: a byte of each kind is data of `G`
  or stored into.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- The footprint after `_dl_protect_relro`: the stack `[lo, top)`, the variables from `0x792000`, the break's
two pages and the first `MORECORE`'s written; the headers, `.rodata` and the read-only pages `0x777`–`0x791` read. -/
def lifG (lo top : Nat) (B : Addr) (L : List (Addr × List Byte)) : Footprint :=
  ⟨[⟨BitVec.ofNat 64 lo, top - lo⟩, ⟨0x792000#64, 0x17000⟩, ⟨B, 8192⟩, ⟨B + 8192#64, 0x21000⟩], [],
    [⟨0x400000#64, 0x1000⟩, ⟨0x6d8000#64, 0x9e000⟩, ⟨0x777000#64, 0x1b000⟩], L⟩

variable {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {y : Addr}

/-- Reduces the bounds of a region given by a constructor to numbers. -/
macro "rgn_red" : tactic =>
  `(tactic| ((try dsimp only at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *)))

theorem not_relro (h : 0x792000 ≤ y.toNat) : inPages 0x777 27 (pageOf y) = false := by
  simp only [inPages, pageOf_toNat, decide_eq_false_iff_not]
  omega

theorem not_relro' (h : y.toNat < 0x777000) : inPages 0x777 27 (pageOf y) = false := by
  simp only [inPages, pageOf_toNat, decide_eq_false_iff_not]
  omega

/-- The conditions `lif_ok` puts on `G` and `Wl'`, for `lifG` and the footprint of `launch_to_ptr`. -/
theorem lifG_ok (hlo : 0x7a9000 ≤ lo) (hlt : lo ≤ top) (htop : top ≤ 2 ^ 47) (hbl : 0x7a9000 ≤ B.toNat)
    (hbt : B.toNat + 0x23000 ≤ 2 ^ 47) (hL : ∀ p ∈ L, p.1.toNat + p.2.length ≤ 0x6d8000) :
    let F := withNew (zzsFoot lo top L) [⟨B, 8192⟩]
    let G := lifG lo top B L
    G.own = [] ∧ G.code = F.code ∧ (∀ r ∈ G.writes ++ G.reads, r.Fits) ∧
    (∀ r ∈ G.writes, ∀ a, r.Mem a → Foot (brkN B ++ F.writes) a ∧ inPages 0x777 27 (pageOf a) = false) ∧
    (∀ r ∈ G.reads, ∀ a, r.Mem a → Foot (brkN B ++ F.writes) a ∨ Foot F.reads a) ∧
    (∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false) ∧
    (∀ y, Foot G.writes y → ∃ q ∈ G.writes, q.Mem y) := by
  intro F G
  have tl : (BitVec.ofNat 64 lo).toNat = lo := by rw [BitVec.toNat_ofNat]; omega
  have t8 : (B + 8192#64).toNat = B.toNat + 8192 := by bv_omega
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, fun _ h => h⟩
  · intro r hr
    simp only [G, lifG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Rgn.Fits] <;> rgn_red <;> omega
  · intro r hr a ha
    simp only [G, lifG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> obtain ⟨h1, h2⟩ := ha <;> rgn_red
    · exact ⟨foot_append_iff.2 (.inr (foot_append_iff.2 (.inr (zzsFoot_stack htop (by omega) (by omega))))),
        not_relro (by omega)⟩
    · exact ⟨foot_append_iff.2 (.inr (lw_var (by omega) (by omega))), not_relro (by omega)⟩
    · exact ⟨foot_append_iff.2 (.inr (lw_brk h1 h2)), not_relro (by omega)⟩
    · exact ⟨foot_append_iff.2 (.inl (foot_one (by rw [t8]; omega) (by rw [t8]; omega))), not_relro (by omega)⟩
  · intro r hr a ha
    simp only [G, lifG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> obtain ⟨h1, h2⟩ := ha <;> rgn_red
    · exact .inr (zzsFoot_hdr (lo := lo) (top := top) (L := L) (by omega) (by omega))
    · exact .inr ⟨⟨0x6d8000#64, 0x9e000⟩, List.mem_cons_of_mem _ List.mem_cons_self,
        show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩
    · exact .inl (foot_append_iff.2 (.inr (lw_var (by omega) (by omega))))
  · intro a ha
    obtain ⟨r, hr, h1, h2⟩ := ha
    simp only [F, Footprint.codeRgns, withNew, zzsFoot, List.mem_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    have := hL p hp
    rgn_red
    exact not_relro' (by omega)

theorem gw_stack (htop : top ≤ 2 ^ 47) (h1 : lo ≤ y.toNat) (h2 : y.toNat < top) : Foot (lifG lo top B L).writes y :=
  ⟨_, List.mem_cons_self, show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩

theorem gd_stack (htop : top ≤ 2 ^ 47) (h1 : lo ≤ y.toNat) (h2 : y.toNat < top) : Foot (lifG lo top B L).data y :=
  foot_writes (gw_stack htop h1 h2)

theorem gw_var (h1 : 0x792000 ≤ y.toNat) (h2 : y.toNat < 0x7a9000) : Foot (lifG lo top B L).writes y :=
  ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩

theorem gd_var (h1 : 0x792000 ≤ y.toNat) (h2 : y.toNat < 0x7a9000) : Foot (lifG lo top B L).data y :=
  foot_writes (gw_var h1 h2)

theorem gw_brk (h1 : B.toNat ≤ y.toNat) (h2 : y.toNat < B.toNat + 8192) : Foot (lifG lo top B L).writes y :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), show _ ∧ _ from ⟨h1, h2⟩⟩

theorem gd_brk (h1 : B.toNat ≤ y.toNat) (h2 : y.toNat < B.toNat + 8192) : Foot (lifG lo top B L).data y :=
  foot_writes (gw_brk h1 h2)

theorem gd_relro (h1 : 0x777000 ≤ y.toNat) (h2 : y.toNat < 0x792000) : Foot (lifG lo top B L).data y :=
  foot_reads ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩

end FV7z.Start
