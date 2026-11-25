import FV7z.Ctor.Cx103
import FV7z.Ctor.Cx17
import FV7z.Ctor.St96
import FV7z.Ctor.St97
import FV7z.C3.Holds
import FV7z.C15.Holds
import FV7z.C37.Holds
import FV7z.C55.Holds
import FV7z.C61.Holds
import FV7z.C70.Holds
import FV7z.C75.Holds
import FV7z.C78.Holds
import FV7z.C82.Holds
import FV7z.C87.Holds
import FV7z.Mal.HeapS
/-!
# The invariant `G` of the constructors not `Done` (PLAN.md §M, assembly of `at_ctor`)

One `G` for `at_ctor`: what the constructors from 3 to 103 read of the global state, and how each one changes it.

- `nOf n₀ m`: the places of the exit list `initial` (`0x7a3ba0`, `xl`) taken before constructor `m`, `n₀` at the
  start; `__cxa_atexit` is called twice by 90, 95 and 99, once by 94, 98, 100 and 101.
- `kOf k m`: the top's budget before constructor `m`: 98 takes `operator new (4)` (1072), 102 `malloc (72704)`
  (72752).
- `Tb103 W`: the two jump tables `init_cacheinfo` reads (`handle_amd`'s, its own).
- `Gn F Wl fb hi n K W`: `Tb103`, `CxPre` with `n` places, `Hp` with the budget `K`; `Gs F Wl fb hi n₀ k m W`: `Gn`
  with `nOf n₀ m` and `kOf k m`.
- `GRd hi a`: the bytes `Gn` reads (with the `fs` block inside `[0x7a86c0, hi)` by `Hp`); `Gn.kept`, `Gs.kept`: for
  bytes that agree on them; `Gs.of`, `Gs.step`: `Gs` from `Gn` with its counts, from `Gs` with the same counts.
- `g3`, …: the step of `G` each constructor's theorem asks for (`hG`), for the constructors that leave what `Gs`
  reads.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Mal
open FV7z.Hca (hca_jt)
open FV7z.Sbrk (rd_eq)

/-- The places of the exit list taken before constructor `m`, `n₀` at the start. -/
def nOf (n₀ m : Nat) : Nat :=
  if m ≤ 90 then n₀ else if m ≤ 94 then n₀ + 2 else if m ≤ 95 then n₀ + 3 else if m ≤ 98 then n₀ + 5
  else if m ≤ 99 then n₀ + 6 else if m ≤ 100 then n₀ + 8 else if m ≤ 101 then n₀ + 9 else n₀ + 10

theorem nOf_le (n₀ m : Nat) : nOf n₀ m ≤ n₀ + 10 := by
  unfold nOf
  repeat' split
  all_goals omega

/-- The top's budget before constructor `m`, `k` after the last `malloc`. -/
def kOf (k m : Nat) : Nat := if m ≤ 98 then k + 73824 else if m ≤ 102 then k + 72752 else k

theorem kOf_ge (k m : Nat) : k ≤ kOf k m := by
  unfold kOf
  repeat' split
  all_goals omega

/-- `__exit_funcs`'s first list, `initial`. -/
abbrev xl : Addr := 8010400#64

/-- The jump tables `init_cacheinfo` reads: `handle_amd`'s at `0x6f2000` and its own. -/
structure Tb103 (W : Addr → Byte) : Prop where
  amd : List.map W (byteAddrs 0x6f2000#64 36) = hca_jt
  own : List.map W (byteAddrs 7282852#64 156) = C103.c103_jt

/-- The tables, the exit list with `n` places taken, the heap with the budget `K`. -/
def Gn (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi n K : Nat) (W : Addr → Byte) : Prop :=
  Tb103 W ∧ CxPre fb xl n W ∧ Hp F Wl fb hi K W

/-- The invariant `G` before constructor `m`. -/
def Gs (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi n₀ k m : Nat) (W : Addr → Byte) : Prop :=
  Gn F Wl fb hi (nOf n₀ m) (kOf k m) W

/-- The bytes `Gs` reads: the tables, `__exit_funcs`, `main_arena` below the `__x86_*` words, the flag and the list
`initial`, `global_max_fast`, the lock with its counter, and from `0x7a86c0` (the TLS block, the tcache) up to `hi`. -/
def GRd (hi a : Nat) : Prop :=
  7282688 ≤ a ∧ a < 7283008 ∨ 7938992 ≤ a ∧ a < 7939000 ∨ 7940480 ≤ a ∧ a < 7942880 ∨
    8010388 ≤ a ∧ a < 8011440 ∨ 8013220 ≤ a ∧ a < 8013232 ∨ 8029184 ≤ a ∧ a < 8029200 ∨ 8029888 ≤ a ∧ a < hi

variable {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi n₀ k : Nat}

/-- `Gn` for bytes that agree on `GRd`. -/
theorem Gn.kept {n K : Nat} {W W' : Addr → Byte} (h : Gn F Wl fb hi n K W) (hn : n < 32) (hK : 16 ≤ K)
    (hW : ∀ a : Addr, GRd hi a.toNat → W' a = W a) : Gn F Wl fb hi n K W' := by
  obtain ⟨⟨t1, t2⟩, hc, hp⟩ := h
  obtain ⟨f1, f2, f3⟩ := hp.bnd hK
  have e1 : (0x6f2000#64 : Addr).toNat = 7282688 := rfl
  have e2 : (7282852#64 : Addr).toNat = 7282852 := rfl
  have el : xl.toNat = 8010400 := rfl
  refine ⟨⟨?_, ?_⟩, hc.kept hn (by omega) (by decide) fun a ha => hW a ?_, hp.mvS hK fun a ha => hW a ?_⟩
  · rw [rd_eq (by rw [e1]; omega) fun a h1 h2 => hW a (by rw [e1] at h1 h2; unfold GRd; omega)]
    exact t1
  · rw [rd_eq (by rw [e2]; omega) fun a h1 h2 => hW a (by rw [e2] at h1 h2; unfold GRd; omega)]
    exact t2
  · unfold CxR at ha
    rw [el] at ha
    unfold GRd
    omega
  · unfold GlS at ha
    unfold GRd
    omega

/-- The `fs` block and `hi` above the tables and globals `Gn` reads. -/
theorem Gn.bnd {n K : Nat} {W : Addr → Byte} (h : Gn F Wl fb hi n K W) (hK : 16 ≤ K) :
    8029928 ≤ fb.toNat ∧ fb.toNat + 64 ≤ hi ∧ hi < 2 ^ 64 :=
  h.2.2.bnd hK

/-- `Gs` for bytes that agree on `GRd`. -/
theorem Gs.kept {m : Nat} {W W' : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) (hn : n₀ + 10 < 32) (hk : 16 ≤ k)
    (hW : ∀ a : Addr, GRd hi a.toNat → W' a = W a) : Gs F Wl fb hi n₀ k m W' :=
  Gn.kept h (Nat.lt_of_le_of_lt (nOf_le n₀ m) hn) (Nat.le_trans hk (kOf_ge k m)) hW

theorem Gs.bnd {m : Nat} {W : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) (hk : 16 ≤ k) :
    8029928 ≤ fb.toNat ∧ fb.toNat + 64 ≤ hi ∧ hi < 2 ^ 64 :=
  Gn.bnd h (Nat.le_trans hk (kOf_ge k m))

/-- `Gs` before `m` from `Gn` with its counts. -/
theorem Gs.of {m n K : Nat} {W : Addr → Byte} (e : nOf n₀ m = n ∧ kOf k m = K) (h : Gn F Wl fb hi n K W) :
    Gs F Wl fb hi n₀ k m W := by
  unfold Gs
  rw [e.1, e.2]
  exact h

/-- `Gs` before `m'` from `Gs` before `m` when the counts are the same. -/
theorem Gs.step {m m' : Nat} {W : Addr → Byte} (e : nOf n₀ m' = nOf n₀ m ∧ kOf k m' = kOf k m)
    (h : Gs F Wl fb hi n₀ k m W) : Gs F Wl fb hi n₀ k m' W :=
  Gs.of e h

/-- `Gs` after stores to an interval apart from what it reads. -/
theorem Gs.out {m m' lo up : Nat} {W W' : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) (hn : n₀ + 10 < 32)
    (hk : 16 ≤ k) (e : nOf n₀ m' = nOf n₀ m ∧ kOf k m' = kOf k m) (hd : ∀ a, GRd hi a → a < lo ∨ up ≤ a)
    (ho : Raf.Out lo up W W') : Gs F Wl fb hi n₀ k m' W' :=
  Gs.step e (h.kept hn hk fun a ha => ho a (by have := hd _ ha; omega))

/-- A registrar's stores leave what `Gs` reads. -/
theorem reg_gs {r : Nat} {A : BitVec 64} {W W' : Addr → Byte}
    (h : RegOut (regCnt r) (regTab r) (regMax r) A W W') {a : Addr} (ha : GRd hi a.toNat) : W' a = W a :=
  RegOut.out h (reg_lay r) (not_tab r (by unfold GRd at ha; simp only [tabs, InR, or_false]; omega))

section steps
variable (hn : n₀ + 10 < 32) (hk : 16 ≤ k)
include hn hk

theorem g3 : ∀ W W', Gs F Wl fb hi n₀ k 3 W → C3.Out W W' → Gs F Wl fb hi n₀ k 4 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g15 : ∀ W W', Gs F Wl fb hi n₀ k 15 W → C15.Out W W' → Gs F Wl fb hi n₀ k 16 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g70 : ∀ W W', Gs F Wl fb hi n₀ k 70 W → C70.Out W W' → Gs F Wl fb hi n₀ k 71 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g75 : ∀ W W', Gs F Wl fb hi n₀ k 75 W → C75.Out W W' → Gs F Wl fb hi n₀ k 76 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g78 : ∀ W W', Gs F Wl fb hi n₀ k 78 W → C78.Out W W' → Gs F Wl fb hi n₀ k 79 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g87 : ∀ W W', Gs F Wl fb hi n₀ k 87 W → C87.Out W W' → Gs F Wl fb hi n₀ k 88 W' :=
  fun _ _ h ho => h.out hn hk ⟨by simp [nOf], by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega) ho

theorem g37 : ∀ W W' W'', Gs F Wl fb hi n₀ k 37 W → C37.Out W W' →
    RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7840512) W' W'' → Gs F Wl fb hi n₀ k 38 W'' :=
  fun _ _ _ h ho hr => Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha => by
    rw [reg_gs hr ha]
    exact ho a (by unfold GRd at ha; omega))

theorem g55 : ∀ W W' W'', Gs F Wl fb hi n₀ k 55 W → C55.Out W W' →
    RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7851136) W' W'' → Gs F Wl fb hi n₀ k 56 W'' :=
  fun _ _ _ h ho hr => Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha => by
    rw [reg_gs hr ha]
    exact ho a (by unfold GRd at ha; omega))

theorem g61 : ∀ W W'', Gs F Wl fb hi n₀ k 61 W →
    RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7852416) (C61.st61 W) W'' →
    Gs F Wl fb hi n₀ k 62 W'' :=
  fun _ _ h hr => Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha => by
    rw [reg_gs hr ha]
    exact C61.st61_out _ a (by unfold GRd at ha; omega))

theorem g96 : ∀ W, Gs F Wl fb hi n₀ k 96 W → Gs F Wl fb hi n₀ k 97 (st96 W) :=
  fun _ h => Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha =>
    st96_out _ a (by unfold GRd at ha; omega))

theorem g97 : ∀ W, Gs F Wl fb hi n₀ k 97 W → Gs F Wl fb hi n₀ k 98 (st97 W) :=
  fun _ h => Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha =>
    st97_out _ a (by unfold GRd at ha; omega))

theorem g82 {sp : Addr} (hsp : hi + 1024 ≤ sp.toNat) :
    ∀ W W', Gs F Wl fb hi n₀ k 82 W → C82.Out sp W W' → Gs F Wl fb hi n₀ k 83 W' :=
  fun _ _ h ho => have := h.bnd hk; Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha =>
    ho a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega))

theorem g17 {sp : Addr} (hsp : hi + 1024 ≤ sp.toNat) :
    ∀ W V', Gs F Wl fb hi n₀ k 17 W → (∀ a : Addr, ¬ (sp.toNat - 80 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7980992 ≤ a.toNat ∧ a.toNat < 7980996) → V' a = W a) → Gs F Wl fb hi n₀ k 18 V' :=
  fun _ _ h ho => have := h.bnd hk; Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha =>
    ho a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega))

theorem g103 {sp : Addr} (hsp : hi + 1024 ≤ sp.toNat) :
    ∀ W V', Gs F Wl fb hi n₀ k 103 W → (∀ a : Addr, ¬ (sp.toNat - 256 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ C103.Gw a → V' a = W a) → Gs F Wl fb hi n₀ k 104 V' :=
  fun _ _ h ho => have := h.bnd hk; Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha =>
    ho a (by unfold GRd at ha; omega) (by unfold C103.Gw; unfold GRd at ha; omega))

end steps

/-- The tables `init_cacheinfo` reads, from `Gs`. -/
theorem tb103 {m : Nat} {W : Addr → Byte} (h : Gs F Wl fb hi n₀ k m W) :
    List.map W (byteAddrs 0x6f2000#64 36) = hca_jt ∧ List.map W (byteAddrs 7282852#64 156) = C103.c103_jt :=
  ⟨h.1.amd, h.1.own⟩

end FV7z.Ctor
