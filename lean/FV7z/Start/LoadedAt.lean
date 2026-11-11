import FV7z.Start.Access
import FV7z.Start.Loaded
/-!
# Zellic's `SegmentsLoaded` for `7zzs` at its first instruction (PLAN.md G3, startup)

- `launch_loaded : Launch.Of zzs.blob.bytes zzs.blob.size l → SegmentsLoaded l.prof.feat l.s₀ zzs.blob.bytes zzsPhdrs`:
  the state `execve` starts `7zzs` in has its loadable segments as the model's interface for a C library's startup
  says (`Spec/Process.lean`): the file's bytes at each segment's address (`launch_bytes`), readable
  (`launch_access`), and `.bss` zeros (`launch_zero`) that can be written.
-/
namespace FV7z.Start
open ZellicX86

theorem add_ofNat (v i : Nat) : Addr.add (BitVec.ofNat 64 v) i = BitVec.ofNat 64 (v + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bytes_map {s : State} {a n : Nat} {g : Nat → Byte}
    (h : ∀ i < n, s.proc.mm.mem.readByte (BitVec.ofNat 64 (a + i)) = g i) :
    Bytes s (BitVec.ofNat 64 a) ((List.range n).map g) := by
  simp only [Bytes, readBytes, byteAddrs, List.length_map, List.length_range, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_apply, add_ofNat]
  exact h i hi

theorem bytes_zero {s : State} {a n : Nat} (h : ∀ i < n, s.proc.mm.mem.readByte (BitVec.ofNat 64 (a + i)) = 0) :
    Bytes s (BitVec.ofNat 64 a) (List.replicate n 0) := by
  simp only [Bytes, readBytes, byteAddrs, List.length_replicate, List.map_map]
  rw [List.eq_replicate_iff]
  refine ⟨by simp only [List.length_map, List.length_range], ?_⟩
  intro b hb
  simp only [List.mem_map, List.mem_range, Function.comp_apply] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  rw [add_ofNat]
  exact h i hi

theorem launch_loaded {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    SegmentsLoaded l.prof.feat l.s₀ V2606.zzs.blob.bytes zzsPhdrs := by
  intro p hp hty
  have hp' : p ∈ [ph0, ph1, ph2, ph3] := by
    rw [zzs_phdrs] at hp
    simp only [zzsPh, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp [ph0, ph1, ph2, ph3]; done) | (exact absurd hty (by decide))
  refine ⟨bytes_map fun i hi => launch_bytes h hp' hi, ?_, ?_⟩
  · intro _ a ha
    simp only [Rgn.Mem, BitVec.toNat_ofNat] at ha
    obtain ⟨c0, c1, c2, c3⟩ := launch_access h a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    have f0 : ph0.vaddr = 0x400000 ∧ ph0.filesz = 0x530 := ⟨rfl, rfl⟩
    have f1 : ph1.vaddr = 0x401000 ∧ ph1.filesz = 0x2d667d := ⟨rfl, rfl⟩
    have f2 : ph2.vaddr = 0x6d8000 ∧ ph2.filesz = 0x9dbe9 := ⟨rfl, rfl⟩
    have f3 : ph3.vaddr = 0x777770 ∧ ph3.filesz = 0x1ce60 := ⟨rfl, rfl⟩
    rcases hp' with rfl | rfl | rfl | rfl
    · rw [f0.1, f0.2] at ha
      exact ⟨canonical_low (by omega) _, c0 (by omega) (by omega)⟩
    · rw [f1.1, f1.2] at ha
      exact ⟨canonical_low (by omega) _, (c1 (by omega) (by omega)).2⟩
    · rw [f2.1, f2.2] at ha
      exact ⟨canonical_low (by omega) _, c2 (by omega) (by omega)⟩
    · rw [f3.1, f3.2] at ha
      exact ⟨canonical_low (by omega) _, (c3 (by omega) (by omega)).1⟩
  · intro hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    have f3 : ph3.vaddr + ph3.filesz = 0x7945d0 ∧ ph3.memsz - ph3.filesz = 0x140f0 := ⟨rfl, rfl⟩
    rcases hp' with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · refine ⟨bytes_zero fun i hi => launch_zero h (by omega) (by omega), ?_⟩
      intro a ha
      simp only [Rgn.Mem, BitVec.toNat_ofNat] at ha
      rw [f3.1, f3.2] at ha
      exact ⟨canonical_low (by omega) _, ((launch_access h a).2.2.2 (by omega) (by omega)).2⟩

end FV7z.Start
