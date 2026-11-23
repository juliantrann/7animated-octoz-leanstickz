import FV7z.Start.ToTls
/-!
# The footprint at `__libc_init_first` (PLAN.md G3, startup)

`launch_to_ptr` hands on, at the call of `__libc_init_first`, the run's footprint `withNew (zzsFoot lo top L) N`
(`N` the break's pages) and what it may store into, `N ++ (zzsFoot lo top L).writes`. `Ndi.lif_ok` asks for many
runs of bytes at fixed addresses in them: the variables (`0x777000`–`0x7a9000`, written), `.rodata` and the headers
(read).

- `lf_var`, `lw_var`, `lf_ro`, `lf_hdr`: a byte of each kind.
- `lf_varN`, `lw_varN`, `lf_roN`, `lf_hdrN`: `n` bytes from a fixed address, as `lif_ok` states them.
-/
namespace FV7z.Start
open ZellicX86 FV7z.Fn

variable {lo top : Nat} {L : List (Addr × List Byte)} {N : List Rgn} {y : Addr}

theorem lf_var (h1 : 0x777000 ≤ y.toNat) (h2 : y.toNat < 0x7a9000) : Foot (withNew (zzsFoot lo top L) N).data y :=
  zzs_new (foot_writes (zzsFoot_var h1 h2))

theorem lw_var (h1 : 0x777000 ≤ y.toNat) (h2 : y.toNat < 0x7a9000) : Foot (N ++ (zzsFoot lo top L).writes) y :=
  foot_append_iff.2 (.inr (zzsFoot_var h1 h2))

theorem lf_ro (h1 : 0x6d8000 ≤ y.toNat) (h2 : y.toNat < 0x776000) : Foot (withNew (zzsFoot lo top L) N).data y :=
  zzs_new (foot_reads (zzsFoot_ro h1 h2))

theorem lf_hdr (h1 : 0x400000 ≤ y.toNat) (h2 : y.toNat < 0x401000) : Foot (withNew (zzsFoot lo top L) N).data y :=
  zzs_new (foot_reads (zzsFoot_hdr h1 h2))

theorem lf_varN {x n : Nat} (h1 : 0x777000 ≤ x) (h2 : x + n ≤ 0x7a9000) :
    ∀ i < n, Foot (withNew (zzsFoot lo top L) N).data (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have t := tg (b := x) hi (by omega)
  exact lf_var (by omega) (by omega)

theorem lw_varN {x n : Nat} (h1 : 0x777000 ≤ x) (h2 : x + n ≤ 0x7a9000) :
    ∀ i < n, Foot (N ++ (zzsFoot lo top L).writes) (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have t := tg (b := x) hi (by omega)
  exact lw_var (by omega) (by omega)

theorem lf_roN {x n : Nat} (h1 : 0x6d8000 ≤ x) (h2 : x + n ≤ 0x776000) :
    ∀ i < n, Foot (withNew (zzsFoot lo top L) N).data (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have t := tg (b := x) hi (by omega)
  exact lf_ro (by omega) (by omega)

theorem lf_hdrN {x n : Nat} (h1 : 0x400000 ≤ x) (h2 : x + n ≤ 0x401000) :
    ∀ i < n, Foot (withNew (zzsFoot lo top L) N).data (Addr.add (BitVec.ofNat 64 x) i) := fun i hi => by
  have t := tg (b := x) hi (by omega)
  exact lf_hdr (by omega) (by omega)

/-- The runs of fixed bytes `lif_ok` asks to be data of its footprint `F`, and those it asks to be stored into
(`Wl`), for the footprint of `launch_to_ptr`. -/
theorem lif_foot :
    let F := withNew (zzsFoot lo top L) N
    let Wl := N ++ (zzsFoot lo top L).writes
    (∀ i < 2, Foot F.data (Addr.add 7945344#64 i)) ∧ (∀ i < 2, Foot F.data (Addr.add 7943116#64 i)) ∧
    (∀ i < 4, Foot Wl (Addr.add 7944640#64 i)) ∧ (∀ i < 4, Foot Wl (Addr.add 8029640#64 i)) ∧
    (∀ i < 8, Foot Wl (Addr.add 8029648#64 i)) ∧ (∀ i < 8, Foot Wl (Addr.add 8013720#64 i)) ∧
    (∀ i < 16, Foot F.data (Addr.add 7366691#64 i)) ∧ (∀ i < 8, Foot F.data (Addr.add 8029440#64 i)) ∧
    (∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x) ∧
    (∀ i < 3, Foot F.data ((7366106#64).add i)) ∧
    (∀ i < 8, Foot F.data (Addr.add 8014536#64 i)) ∧ (∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) ∧
    (∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) ∧ (∀ i < 8, Foot F.data (Addr.add 8029512#64 i)) ∧
    (∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x) ∧
    (∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x) ∧
    (∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a) ∧
    (∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x) ∧
    (∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x) ∧
    (∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) :=
  ⟨lf_varN (by omega) (by omega), lf_varN (by omega) (by omega), lw_varN (by omega) (by omega),
    lw_varN (by omega) (by omega), lw_varN (by omega) (by omega), lw_varN (by omega) (by omega),
    lf_roN (by omega) (by omega), lf_varN (by omega) (by omega), fun _ h1 h2 => lf_ro (by omega) (by omega),
    fun _ hi => lf_ro (by first | bv_omega | (simp only [BitVec.add_eq]; bv_omega))
      (by first | bv_omega | (simp only [BitVec.add_eq]; bv_omega)),
    lf_varN (by omega) (by omega), lf_varN (by omega) (by omega),
    lf_varN (by omega) (by omega), lf_varN (by omega) (by omega), fun _ h1 h2 => lw_var (by omega) (by omega),
    fun _ h1 h2 => lf_var (by omega) (by omega), fun _ h1 h2 => lw_var (by omega) (by omega),
    fun _ h1 h2 => lw_var (by omega) (by omega), fun _ h1 h2 => lf_ro (by omega) (by omega),
    fun _ h1 h2 => lf_hdr (by omega) (by omega)⟩

end FV7z.Start
