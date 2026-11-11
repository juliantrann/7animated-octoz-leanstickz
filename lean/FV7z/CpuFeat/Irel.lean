import FV7z.CpuFeat.IcfI
import FV7z.Glibc.ResolversHolds
import FV7z.Lemmas.CallM
/-!
# `apply_irel`: the IFUNC resolvers' answers into the GOT (PLAN.md G2, "Dispatch theo CPUID")

glibc 2.31's `apply_irel` (`csu/libc-start.c`, `ARCH_SETUP_IREL`), inlined in `__libc_start_main` of `7zzs` 26.06
at `0x613278`, right after `init_cpu_features`: for each `Elf64_Rela` of `.rela.plt` (`[0x400248, 0x400530)`, 31
entries of 24 bytes, all `R_X86_64_IRELATIVE`), `*r_offset = ((Elf64_Addr (*) (void)) r_addend) ()`:

```
613278  mov rbx, 0x400248          0
61327f  jmp 61328b                 7
613281  call [rbx + 0x10]          9
613284  add rbx, 0x18             12
613288  mov [r14], rax            16
61328b  cmp rbx, 0x400530         19
613292  jae 6133bb                26
613298  cmp dword [rbx + 8], 0x25 32
61329c  mov r14, [rbx]            36
61329f  je 613281                 39
6132a1  lea rdi, …; call __libc_fatal   (another type of relocation: not reached, the table is the file's)
```

The table's bytes are the file's (`rela_pin`); each entry's addend is a resolver of `Glibc.V2606.resolvers`
(`ent_res`), whose theorem (`V2606.resolvers_holdK`) says it returns a variant the processor has, given `CpuOk`,
and keeps the memory; the slots are apart from one another, from the table and from `_dl_x86_cpu_features`. So at
`0x6133bb` the GOT is `Glibc.V2606.GotOk`: every call through the PLT goes to code the processor can run.
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

set_option linter.deprecated false

/-- `.rela.plt`: 31 `Elf64_Rela`. -/
def rela : List Byte := [0x08, 0x21, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x5c, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x21, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x60, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0xd6, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x12, 0x6a, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0x52, 0x66, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x12, 0x6a, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x73, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x69, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0xd1, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x74, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x6b, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb0, 0x69, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa8, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0xd1, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x78, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x73, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd0, 0x60, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x88, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x5d, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x73, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x78, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x6b, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x74, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x68, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x30, 0x6d, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x73, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x58, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0x6c, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x6c, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x61, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x61, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x38, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x5c, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x30, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x69, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x28, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb0, 0x5d, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x8c, 0x69, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x20, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x6a, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem rela_pin : Exe.bytesAt V2606.zzs.blob 0x400248 744 = some rela := by decide +kernel

/-- Entry `i`: its GOT slot and its resolver. -/
def ent (i : Nat) : Nat × Nat := V2606.irel.getD i (0, 0)

/-- A table of `Elf64_Rela` as words: `r_offset`, the type (the low half of `r_info`), `r_addend` of each entry. -/
def words : List Byte → List (BitVec 64 × BitVec 32 × BitVec 64)
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: b0 :: b1 :: b2 :: b3 :: _ :: _ :: _ :: _ ::
    c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: l =>
    (ofBytesLE 64 [a0, a1, a2, a3, a4, a5, a6, a7], ofBytesLE 32 [b0, b1, b2, b3],
      ofBytesLE 64 [c0, c1, c2, c3, c4, c5, c6, c7]) :: words l
  | _ => []

/-- Entry `i` of a table, read at its byte offsets. -/
theorem words_get : ∀ (l : List Byte) (i : Nat), i < (words l).length →
    ofBytesLE 64 ((List.range 8).map fun k => l.getD (24 * i + k) 0) = ((words l).getD i (0, 0, 0)).1 ∧
    ofBytesLE 32 ((List.range 4).map fun k => l.getD (24 * i + 8 + k) 0) = ((words l).getD i (0, 0, 0)).2.1 ∧
    ofBytesLE 64 ((List.range 8).map fun k => l.getD (24 * i + 16 + k) 0) = ((words l).getD i (0, 0, 0)).2.2
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
    _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, 0, _ => ⟨rfl, rfl, rfl⟩
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
    c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: l, i + 1, h => by
    have ih := words_get l i (by simpa [words] using h)
    have e : ∀ m, (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
        c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: l).getD (24 * (i + 1) + m) 0 = l.getD (24 * i + m) 0 := by
      intro m
      rw [show 24 * (i + 1) + m = (24 * i + m) + 24 by omega]; rfl
    have e8 : ∀ m, (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
        c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: l).getD (24 * (i + 1) + 8 + m) 0 =
        l.getD (24 * i + 8 + m) 0 := by
      intro m
      rw [show 24 * (i + 1) + 8 + m = (24 * i + 8 + m) + 24 by omega]; rfl
    have e16 : ∀ m, (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
        c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: l).getD (24 * (i + 1) + 16 + m) 0 =
        l.getD (24 * i + 16 + m) 0 := by
      intro m
      rw [show 24 * (i + 1) + 16 + m = (24 * i + 16 + m) + 24 by omega]; rfl
    simp only [e, e8, e16]
    exact ih
  | [], _, h => by simp [words] at h

/-- The table in one pass (one comparison of 31 triples; by entry and byte offset the kernel needs over 2.5 GB). -/
theorem rela_words : words rela = V2606.irel.map fun p => (BitVec.ofNat 64 p.1, 37#32, BitVec.ofNat 64 p.2) := by
  decide +kernel

theorem irel_get : ∀ i < 31, ((V2606.irel.map fun p => (BitVec.ofNat 64 p.1, 37#32, BitVec.ofNat 64 p.2)).getD i
    (0, 0, 0)) = (BitVec.ofNat 64 (ent i).1, 37#32, BitVec.ofNat 64 (ent i).2) := by decide +kernel

/-- The table's words: `r_offset`, the type (`R_X86_64_IRELATIVE`, 37) of `r_info`, `r_addend`. -/
theorem rela_ent : ∀ i < 31,
    ofBytesLE 64 ((List.range 8).map fun k => rela.getD (24 * i + k) 0) = BitVec.ofNat 64 (ent i).1 ∧
    ofBytesLE 32 ((List.range 4).map fun k => rela.getD (24 * i + 8 + k) 0) = BitVec.ofNat 32 37 ∧
    ofBytesLE 64 ((List.range 8).map fun k => rela.getD (24 * i + 16 + k) 0) = BitVec.ofNat 64 (ent i).2 := by
  intro i hi
  have h := words_get rela i (by rw [rela_words]; exact hi)
  rw [rela_words, irel_get i hi] at h
  exact h

theorem ent_slot : ∀ i < 31, (ent i).1 = 0x792108 - 8 * i := by decide +kernel

theorem ent_res : ∀ i < 31, ∃ r ∈ V2606.resolvers, r.1 = (ent i).2 := by decide +kernel

theorem irel_ent : ∀ p ∈ V2606.irel, ∃ k < 31, p = ent k := by decide +kernel

theorem res_nodup : (V2606.resolvers.map (·.1)).Nodup := by decide +kernel

theorem eq_of_nodup_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l →
    f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, hn, x, y, hx, hy, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hx with ex | hx' <;> rcases List.mem_cons.1 hy with ey | hy'
    · rw [ex, ey]
    · exact absurd (List.mem_map.2 ⟨y, hy', by rw [← h, ex]⟩) hn.1
    · exact absurd (List.mem_map.2 ⟨x, hx', by rw [h, ey]⟩) hn.1
    · exact eq_of_nodup_map f hn.2 hx' hy' h

theorem tab_toNat : (0x400248 : Addr).toNat = 0x400248 := rfl
theorem got_toNat : (0x792018 : Addr).toNat = 0x792018 := rfl

theorem slot_toNat {k : Nat} (hk : k < 31) : (BitVec.ofNat 64 (ent k).1).toNat = 0x792108 - 8 * k := by
  rw [BitVec.toNat_ofNat, ent_slot k hk]; omega

/-- What the run may store into: the slot of the return address of the calls it makes, and the GOT's slots. -/
def irelW (q : Addr) : List Rgn := [⟨q, 8⟩, ⟨0x792018, 0xf8⟩]

/-- The setting of the run: `rsp` is `q + 8`. -/
structure RE (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (q : Addr) : Prop where
  code : CodeIn L 0x613278 irl
  codex : ∃ cx, CodeIn L 0x6133bb cx ∧ 0 < cx.length
  codes : ∀ r ∈ V2606.resolvers, ∀ rc, Exe.bytesAt V2606.zzs.blob r.1 r.2.1 = some rc →
    CodeIn L (BitVec.ofNat 64 r.1) rc
  w : ∀ y, Foot (irelW q) y → Foot Wl y
  tab : ∀ j < 744, Foot F.data ((0x400248 : Addr).add j)
  cpu : ∀ y, Rgn.Mem cpuRgn y → Foot F.data y
  fit : q.toNat + 8 ≤ 2 ^ 64
  apart : 0x7a4b48 ≤ q.toNat ∨ q.toNat + 8 ≤ 0x400248
  al : (q.toNat + 8) % 16 = 0

/-- The footprint's bytes: `CInv`; the slots of the first `i` entries, each a variant of its resolver's the
processor has; off what the run may store into, as at the start. -/
structure RV (prof : Profile) (q : Addr) (V₀ V : Addr → Byte) (i : Nat) : Prop where
  inv : CInv prof V
  got : ∀ k < i, ∀ r ∈ V2606.resolvers, r.1 = (ent k).2 →
    Glibc.Returns prof r.2.2 (ofBytesLE 64 ((byteAddrs (BitVec.ofNat 64 (ent k).1) 8).map V))
  off : ∀ y, ¬ Foot (irelW q) y → V y = V₀ y

/-- `rsp`, `rbp`, `r12`, `r13` and `r15` as in `g` (the run uses `rbx` and `r14`). -/
structure TKi (g g' : Gprs) : Prop where
  sp : g'.rsp = g.rsp
  rbp : g'.rbp = g.rbp
  r12 : g'.r12 = g.r12
  r13 : g'.r13 = g.r13
  r15 : g'.r15 = g.r15

theorem vst_ne {bs : List Byte} {V : Addr → Byte} {g x : Addr} (hf : g.toNat + bs.length ≤ 2 ^ 64)
    (h : x.toNat < g.toNat ∨ g.toNat + bs.length ≤ x.toNat) : Vst V g bs x = V x :=
  Vst_apart bs V g x fun j hj he => by
    have := congrArg BitVec.toNat he
    rw [toNat_add_of_fits hj hf] at this; omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {q : Addr} {V₀ V : Addr → Byte} {i : Nat}

/-- A store into the return address's slot, or into the GOT below the slots of the first `i` entries. -/
theorem RV.st (h : RV prof q V₀ V i) {g : Addr} {bs : List Byte} (hf : g.toNat + bs.length ≤ 2 ^ 64)
    (hw : (q.toNat ≤ g.toNat ∧ g.toNat + bs.length ≤ q.toNat + 8) ∨
      (0x792018 ≤ g.toNat ∧ g.toNat + bs.length ≤ 0x792110 - 8 * i))
    (hq : 0x7a4b48 ≤ q.toNat ∨ q.toNat + 8 ≤ 0x400248) (hi : i ≤ 31) : RV prof q V₀ (Vst V g bs) i := by
  refine ⟨h.inv.st_apart _ _ hf fun a ha => ?_, fun k hk r hr he => ?_, fun y hy => ?_⟩
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have hs := slot_toNat (k := k) (by omega)
    have e : (byteAddrs (BitVec.ofNat 64 (ent k).1) 8).map (Vst V g bs) =
        (byteAddrs (BitVec.ofNat 64 (ent k).1) 8).map V := by
      apply List.map_congr_left
      intro x hx
      obtain ⟨m, hm, rfl⟩ := mem_byteAddrs.1 hx
      refine vst_ne hf ?_
      rw [toNat_add_of_fits hm (by rw [hs]; omega), hs]; omega
    rw [e]; exact h.got k hk r hr he
  · rw [vst_ne hf]
    · exact h.off y hy
    · refine Classical.byContradiction fun hc => hy ?_
      rcases hw with hw | hw
      · exact ⟨⟨q, 8⟩, by simp [irelW], by simp only [Rgn.Mem]; omega⟩
      · exact ⟨⟨0x792018, 0xf8⟩, by simp [irelW], by simp only [Rgn.Mem, got_toNat]; omega⟩

/-- The store of entry `i`'s slot. -/
theorem RV.stSlot (h : RV prof q V₀ V i) (hi : i < 31) (hq : 0x7a4b48 ≤ q.toNat ∨ q.toNat + 8 ≤ 0x400248)
    {v : BitVec 64} (hv : ∀ r ∈ V2606.resolvers, r.1 = (ent i).2 → Glibc.Returns prof r.2.2 v) :
    RV prof q V₀ (Vst V (BitVec.ofNat 64 (ent i).1) (toBytesLE v 8)) (i + 1) := by
  have hs := slot_toNat hi
  have h1 := h.st (g := BitVec.ofNat 64 (ent i).1) (bs := toBytesLE v 8) (by rw [toBytesLE_length, hs]; omega)
    (Or.inr ⟨by rw [hs]; omega, by rw [toBytesLE_length, hs]; omega⟩) hq (by omega)
  refine ⟨h1.inv, fun k hk r hr he => ?_, h1.off⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · exact h1.got k hk r hr he
  · have := Vst_self (toBytesLE v 8) V (BitVec.ofNat 64 (ent k).1) (by rw [toBytesLE_length, hs]; omega)
    rw [toBytesLE_length] at this
    rw [this, ofBytesLE_toBytesLE (n := 8) rfl]
    exact hv r hr he

/-- The return address's slot is the run's to store into. -/
theorem RE.fr (hE : RE F Wl L q) {m : Nat} (hm : m < 8) : Foot Wl (q.add m) :=
  hE.w _ ⟨⟨q, 8⟩, by simp [irelW], mem_add_of_fits hm hE.fit⟩

/-- The GOT's slots are the run's to store into. -/
theorem RE.gotw (hE : RE F Wl L q) {k : Nat} (hk : k < 31) {m : Nat} (hm : m < 8) :
    Foot Wl (Addr.add (BitVec.ofNat 64 (ent k).1) m) := by
  have hs := slot_toNat hk
  have e := toNat_add_of_fits (a := BitVec.ofNat 64 (ent k).1) hm (by rw [hs]; omega)
  refine hE.w _ ⟨⟨0x792018, 0xf8⟩, by simp [irelW], ?_⟩
  simp only [Rgn.Mem, got_toNat]
  omega

/-- The table's bytes, which the run does not store into. -/
theorem RV.tab (hE : RE F Wl L q) (h0 : ∀ j < 744, V₀ ((0x400248 : Addr).add j) = rela.getD j 0)
    (hV : RV prof q V₀ V i) {j : Nat} (hj : j < 744) : V ((0x400248 : Addr).add j) = rela.getD j 0 := by
  have hn : ¬ Foot (irelW q) ((0x400248 : Addr).add j) := by
    rintro ⟨r, hr, hm⟩
    have ha := hE.apart
    have e := toNat_add_of_fits (a := (0x400248 : Addr)) hj (by decide)
    rw [tab_toNat] at e
    simp only [irelW, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Rgn.Mem, e] at hm; omega
    · simp only [Rgn.Mem, e, got_toNat] at hm; omega
  rw [hV.off _ hn]; exact h0 j hj

/-- A word of the table. -/
theorem tabW {V : Addr → Byte} (h : ∀ j < 744, V ((0x400248 : Addr).add j) = rela.getD j 0) {m n : Nat}
    (hm : m + n ≤ 744) :
    (byteAddrs ((0x400248 : Addr).add m) n).map V = (List.range n).map fun k => rela.getD (m + k) 0 := by
  simp only [byteAddrs, List.map_map]
  apply List.map_congr_left
  intro k hk
  have := List.mem_range.1 hk
  simp only [Function.comp, addr_add_add]
  exact h _ (by omega)

/-- The rest of the run, from `0x6133bb`. -/
abbrev RK (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (q : Addr) (g₀ : Gprs) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → RV prof q V₀ V 31 →
    Y.cpu.rip = 0x6133bb → TKi g₀ Y.cpu.gpr → GoG prof L o gev gP gE Y t

/-- From the loop's test (`19`) with `rbx` at entry `i`, the run goes on to the goal. -/
def AtH (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (q : Addr) (g₀ : Gprs) (i : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → RV prof q V₀ V i →
    X.cpu.rip = (0x613278 : Addr).add 19 → X.cpu.gpr.rbx = (0x400248 : Addr).add (24 * i) → TKi g₀ X.cpu.gpr →
    GoG prof L o gev gP gE X t

variable {g₀ : Gprs}

/-- The test, and for an entry `i` its resolver's call and its slot's store, back to the test with `i + 1`. -/
theorem irHead (c : Seg prof F Wl L s₀ o) (hE : RE F Wl L q) (hpc : prof.Consistent) (hch : Chain prof)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (h0 : ∀ j < 744, V₀ ((0x400248 : Addr).add j) = rela.getD j 0) (hsp0 : g₀.rsp = q.add 8)
    (k : RK prof F Wl L s₀ o gev gP gE V₀ q g₀) (hi : i ≤ 31)
    (kn : i < 31 → AtH prof F Wl L s₀ o gev gP gE V₀ q g₀ (i + 1)) :
    AtH prof F Wl L s₀ o gev gP gE V₀ q g₀ i := by
  intro X t V hK hA hV hr hbx hT
  have hl : irl.length = 53 := irl_length
  obtain ⟨cx, hcx, hcxl⟩ := hE.codex
  refine c.s_cmp_ri64 hK hA hE.code (by omega) hr (irl_19 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hf1⟩
  have hb : (rv X 64 3).toNat = 0x400248 + 24 * i := by
    simp only [rv, get_regOf_3, hbx, BitVec.setWidth_eq]
    rw [toNat_add_of_fits (n := 745) (by omega) (by decide), tab_toNat]
  have e3 : ∀ g : Rflags, g.cond 3 = !g.cf := fun _ => rfl
  have hcf : Y1.cpu.rflags.cond 3 = !decide (0x400248 + 24 * i < 0x400530) := by
    rw [hf1, e3, subF_cf, hb]; rfl
  refine c.s_jcc_x hK1 hA1 hE.code (by omega) hr1 (irl_26 _) hcx hcxl (tgt := 0) (by decide) (fun hcc => ?_)
    fun hcc => ?_
  · -- past the last entry
    rw [hcf] at hcc
    have hi31 : i = 31 := by simp at hcc; omega
    subst hi31
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact k Y t' V hKY hAY hV (by rw [hrY, addr_add_zero]) (by rw [hgY, hg1]; exact hT)
  rw [hcf] at hcc
  have hi' : i < 31 := by simp at hcc; omega
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hbx2 : Y2.cpu.gpr.rbx = (0x400248 : Addr).add (24 * i) := by rw [hg2, hg1]; exact hbx
  have hea : ∀ (Y : State) (d : Nat), Y.cpu.gpr.rbx = (0x400248 : Addr).add (24 * i) →
      eaD Y 3 d = (0x400248 : Addr).add (24 * i + d) := fun Y d h => by
    simp only [eaD, get_regOf_3, h]; exact add_addn _ _ _
  have htab : ∀ j < 744, V ((0x400248 : Addr).add j) = rela.getD j 0 := fun j hj => hV.tab hE h0 hj
  -- the relocation's type
  refine c.s_cmp_m32i_f hK2 hA2 hE.code (by omega) hr2 (irl_32 _)
    (fun m hm => by rw [hea Y2 8 hbx2, addr_add_add]; exact hE.tab _ (by omega)) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hf3⟩
  have hty : Y3.cpu.rflags.zf = true := by
    rw [hf3, subF_zf, hea Y2 8 hbx2, tabW htab (by omega), (rela_ent i hi').2.1]
    exact decide_eq_true rfl
  have hbx3 : Y3.cpu.gpr.rbx = (0x400248 : Addr).add (24 * i) := by rw [hg3]; exact hbx2
  -- the slot's address
  refine c.s_mov_rm_f hK3 hA3 hE.code (by omega) hr3 (Or.inr rfl) (irl_36 _)
    (fun m hm => by rw [hea Y3 0 hbx3, addr_add_add]; exact hE.tab _ (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hf4⟩
  have h14 : Y4.cpu.gpr.r14 = BitVec.ofNat 64 (ent i).1 := by
    rw [hg4]
    show (ofBytesLE 64 ((byteAddrs (eaD Y3 3 0) 8).map V)).setWidth 64 = _
    rw [BitVec.setWidth_eq, hea Y3 0 hbx3, Nat.add_zero, tabW htab (by omega)]
    exact (rela_ent i hi').1
  refine c.s_jcc hK4 hA4 hE.code (by omega) hr4 (irl_39 _) (tgt := 9) (by decide) (by omega) (fun _ => ?_)
    (fun hcc => absurd hcc (by rw [hf4, cond4]; show ¬ Y3.cpu.rflags.zf = false; rw [hty]; decide))
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hbx5 : Y5.cpu.gpr.rbx = (0x400248 : Addr).add (24 * i) := by rw [hg5, hg4]; exact hbx3
  have h14' : Y5.cpu.gpr.r14 = BitVec.ofNat 64 (ent i).1 := by rw [hg5]; exact h14
  have hT5 : TKi g₀ Y5.cpu.gpr := by
    rw [hg5, hg4, hg3, hg2, hg1]; exact ⟨hT.sp, hT.rbp, hT.r12, hT.r13, hT.r15⟩
  have hsp5 : Y5.cpu.gpr.rsp = q.add 8 := hT5.sp.trans hsp0
  -- the resolver
  obtain ⟨r, hrm, hre⟩ := ent_res i hi'
  obtain ⟨rc, hpin, hrl, hholds⟩ := V2606.resolvers_holdK r hrm
  have hcr := hE.codes r hrm rc hpin
  have e8 : Y5.cpu.gpr.rsp - 8 = q := by rw [hsp5, sub8]
  refine c.s_callM hK5 hA5 hE.code (by omega) hr5 (irl_9 _)
    (fun m hm => by rw [hea Y5 16 hbx5, addr_add_add]; exact hE.tab _ (by omega)) hcr hrl
    (by rw [hea Y5 16 hbx5, tabW htab (by omega), (rela_ent i hi').2.2, hre])
    (fun m hm => by rw [e8]; exact hE.fr hm) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  rw [e8] at hA6
  have hs6 : Y6.cpu.gpr.rsp = q := by rw [hg6]; exact e8
  have hfit := hE.fit
  have hV6 : RV prof q V₀ (Vst V q (toBytesLE ((0x613278 : Addr).add (9 + 3)) 8)) i :=
    hV.st (by rw [toBytesLE_length]; exact hfit) (Or.inl ⟨Nat.le_refl _, by rw [toBytesLE_length]; omega⟩)
      hE.apart hi
  have hcpu6 : CpuOk prof Y6.proc.mm.mem :=
    hV6.inv.mem fun j hj => hA6 _ (hE.cpu _ (mem_add_of_fits hj (by decide)))
  have hno : ∀ y, ¬ Foot (ws 0 (fun _ => []) Y6) y := by
    rintro y ⟨r', hr', hm⟩
    rcases List.mem_singleton.1 hr' with rfl
    simp only [below, Rgn.Mem] at hm; omega
  refine c.enterK (k := 0) (W := fun _ => []) (R := fun _ => [cpuRgn]) (pre := fun s => CpuOk prof s.proc.mm.mem)
    (post := fun _ Z => Glibc.Returns prof r.2.2 Z.cpu.gpr.rax) (ra := (0x613278 : Addr).add (9 + 3))
    hK6 hA6 hr6 (fun m hm => by rw [hs6]; exact hE.fr hm) ?_ (fnK_of_leafK (hholds L prof hpc hch hcr)) hdf hx87
    (by cases prof.feat.la57 <;> decide) ?_ ?_ (fun y hy => absurd hy (hno y)) hcpu6 ?_
  · rw [hs6]
    have := Vst_self (toBytesLE ((0x613278 : Addr).add (9 + 3)) 8) V q (by rw [toBytesLE_length]; exact hfit)
    rw [toBytesLE_length] at this
    rw [this]; exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [hs6]
    show (q + BitVec.ofNat 64 8).toNat % 16 = 0
    have := hE.al
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  · refine ⟨fun r' hr' => ?_, ?_, ?_, c.code.symm ▸ rfl, rfl, c.own⟩
    · simp [Contract.footprint, fnK, fn] at hr'
      rcases hr' with rfl | rfl
      · simp only [Rgn.Fits, frame, hs6, BitVec.sub_zero]; omega
      · simp [Rgn.Fits, cpuRgn]
    · rintro y ⟨r', hr', hm⟩
      simp [Contract.footprint, fnK, fn] at hr'
      subst hr'
      simp only [frame, hs6, Rgn.Mem, BitVec.sub_zero] at hm
      obtain ⟨r'', hr'', hm''⟩ := c.hww y (hE.w _ ⟨⟨q, 8⟩, by simp [irelW], by simp only [Rgn.Mem]; omega⟩)
      exact ⟨r'', hr'', hm''⟩
    · rintro y ⟨r', hr', hm⟩
      simp [Contract.footprint, fnK, fn] at hr'
      subst hr'
      have := hE.cpu y hm
      unfold Footprint.data at this
      rw [c.own, List.append_nil] at this
      exact foot_append_iff.1 this
  intro Z t' hKZ hmem hret hpost
  have hAZ : Agree F Z.proc.mm.mem (Vst V q (toBytesLE ((0x613278 : Addr).add (9 + 3)) 8)) :=
    fun y hy => hmem y hy (hno y)
  have hTZ := TK.ret (show Y6.cpu.gpr = Y5.cpu.gpr.set 4 (Y5.cpu.gpr.rsp - 8) from hg6) hret
  refine c.s_add_ri64 hKZ hAZ hE.code (by omega) hret.1 (irl_12 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have h14_7 : eaD Y7 14 0 = BitVec.ofNat 64 (ent i).1 := by
    simp only [eaD, hg7]
    show Z.cpu.gpr.r14 + BitVec.ofNat 64 0 = _
    rw [BitVec.add_zero, hTZ.r14, h14']
  refine c.s_mov_mr hK7 hA7 hE.code (by omega) hr7 (Or.inr rfl) (irl_16 _)
    (fun m hm => by rw [h14_7]; exact hE.gotw hi' (by omega)) ?_
  rw [h14_7]
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hax : rv Y7 64 0 = Z.cpu.gpr.rax := by simp only [rv, hg7, BitVec.setWidth_eq]; rfl
  have hV8 := hV6.stSlot hi' hE.apart (v := rv Y7 64 0) fun r' hr' he' => by
    obtain rfl := eq_of_nodup_map (·.1) res_nodup hr' hrm (he'.trans hre.symm)
    rw [hax]; exact hpost
  have e24 : 24 * (i + 1) = 24 * i + 24 := by omega
  refine kn hi' Y8 t8 _ hK8 hA8 hV8 hr8 ?_ ?_
  · rw [hg8, hg7, e24]
    show Z.cpu.gpr.rbx + BitVec.ofNat 64 24 = _
    rw [hTZ.rbx, hbx5]; exact add_addn _ _ _
  · rw [hg8, hg7]
    exact ⟨hTZ.sp.trans hT5.sp, hTZ.rbp.trans hT5.rbp, hTZ.r12.trans hT5.r12, hTZ.r13.trans hT5.r13,
      hTZ.r15.trans hT5.r15⟩

/-- The test with `rbx` at any entry: by the number of entries left. -/
theorem irAll (c : Seg prof F Wl L s₀ o) (hE : RE F Wl L q) (hpc : prof.Consistent) (hch : Chain prof)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (h0 : ∀ j < 744, V₀ ((0x400248 : Addr).add j) = rela.getD j 0) (hsp0 : g₀.rsp = q.add 8)
    (k : RK prof F Wl L s₀ o gev gP gE V₀ q g₀) :
    ∀ (n i : Nat), i + n = 31 → AtH prof F Wl L s₀ o gev gP gE V₀ q g₀ i
  | 0, _, h => irHead c hE hpc hch hdf hx87 h0 hsp0 k (by omega) fun hi => absurd hi (by omega)
  | n + 1, i, h => irHead c hE hpc hch hdf hx87 h0 hsp0 k (by omega) fun _ =>
      irAll c hE hpc hch hdf hx87 h0 hsp0 k n (i + 1) (by omega)

/-- glibc's `apply_irel`, inlined in `__libc_start_main`, from `0x613278` (where `init_cpu_features` ends:
`initCpuFeatures`) to `0x6133bb`, on every processor the profile allows: no system call; at `0x6133bb` the GOT is
`GotOk` (each of the 31 slots a variant the processor has), `CpuOk` still, `rsp`, `rbp`, `r12`, `r13`, `r15` as they
were, and the footprint's bytes off the return address's slot and the GOT as at the start. -/
theorem applyIrel (c : Seg prof F Wl L s₀ o) (hE : RE F Wl L q) (hpc : prof.Consistent) (hch : Chain prof)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) {X : State} {t : Nat} (hK : KeptW Wl s₀ X)
    (hcpu : CpuOk prof X.proc.mm.mem)
    (htab : ∀ j < 744, X.proc.mm.mem.readByte ((0x400248 : Addr).add j) = rela.getD j 0)
    (hr : X.cpu.rip = 0x613278) (hsp : X.cpu.gpr.rsp = q.add 8)
    (post : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem →
      V2606.GotOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot (irelW q) y → Y.proc.mm.mem.readByte y = X.proc.mm.mem.readByte y) →
      Y.cpu.rip = 0x6133bb → TKi X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl : irl.length = 53 := irl_length
  have hA : Agree F X.proc.mm.mem fun a => X.proc.mm.mem.readByte a := fun _ _ => rfl
  have hV0 : RV prof q (fun a => X.proc.mm.mem.readByte a) (fun a => X.proc.mm.mem.readByte a) 0 :=
    ⟨CInv.of_cpuOk hcpu, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl⟩
  have k : RK prof F Wl L s₀ o gev gP gE (fun a => X.proc.mm.mem.readByte a) q X.cpu.gpr :=
    fun Y t' V hKY hAY hVY hrY hTY => post Y t' hKY
      (hVY.inv.mem fun j hj => hAY _ (hE.cpu _ (mem_add_of_fits hj (by decide))))
      (fun p hp r hrm he => by
        obtain ⟨m, hm, rfl⟩ := irel_ent p hp
        rw [hAY.read fun n hn => c.hws _ (hE.gotw hm hn)]
        exact hVY.got m hm r hrm he)
      (fun y hy hn => (hAY y hy).trans (hVY.off y hn)) hrY hTY
  refine c.s_mov_ri64 hK hA hE.code (by omega) (by rw [hr, addr_add_zero]) (irl_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jmp hK1 hA1 hE.code (by omega) hr1 (irl_7 _) (tgt := 19) (by decide) (by omega) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact irAll c hE hpc hch hdf hx87 htab hsp k 31 0 rfl Y2 t2 _ hK2 hA2 hV0 hr2
    (by rw [hg2, hg1, Nat.mul_zero, addr_add_zero]; rfl) (by rw [hg2, hg1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- `init_cpu_features` then `apply_irel`: from `0x613113` to `0x6133bb`, for every vendor and every answer of `cpuid`
the profile allows, one system call (`arch_prctl (ARCH_CET_STATUS, …)`), and then `CpuOk` and `GotOk`: the words
of `_dl_x86_cpu_features` say only what the processor has, and each IFUNC's GOT slot holds a variant the processor
can run. `rsp`, `rbp`, `r12`, `r13` and `r15` are as they were, and off what the run may store into the footprint's
bytes are as at the start. -/
theorem initCpuFeatures_applyIrel (c : Seg prof F Wl L s₀ o) (hE : IE F Wl L V₀ q) (hJ : JT F Wl V₀)
    (hR : RE F Wl L q)
    (hT : ∀ j < 744, ¬ Foot Wl ((0x400248 : Addr).add j) ∧ V₀ ((0x400248 : Addr).add j) = rela.getD j 0)
    (hpc : prof.Consistent) (hch : Chain prof) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V₀) (hok : CInv prof V₀)
    (hr : X.cpu.rip = 0x613113) (hsp : X.cpu.gpr.rsp = q.add 8)
    (post : ∀ (g : Gprs) (Y : State) (t' : Nat), g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
      KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem → V2606.GotOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot Wl y → Y.proc.mm.mem.readByte y = V₀ y) →
      Y.cpu.rip = 0x6133bb → TKi X.cpu.gpr Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  initCpuFeatures c hE hJ hpc hdf hx87 hK hA hok hr hsp fun g _ _ hax hdi hKY hcpu hoff hrY hTY =>
    applyIrel c hR hpc hch hdf hx87 hKY hcpu
      (fun j hj => (hoff _ (hR.tab j hj) (hT j hj).1).trans (hT j hj).2) hrY (hTY.sp.trans hsp)
      fun Z t'' hKZ hcpuZ hgot hoffZ hrZ hTZ => post g Z t'' hax hdi hKZ hcpuZ hgot
        (fun y hy hn => (hoffZ y hy fun h => hn (hR.w y h)).trans (hoff y hy hn)) hrZ
        ⟨hTZ.sp.trans hTY.sp, hTZ.rbp.trans hTY.rbp, hTZ.r12.trans hTY.r12, hTZ.r13.trans hTY.r13,
          hTZ.r15.trans hTY.r15⟩

end FV7z.CpuFeat
