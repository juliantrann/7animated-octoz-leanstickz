import FV7z.Start.FootOk
import FV7z.Start.LchOf
import FV7z.Start.Cpu
/-!
# The run of `7zzs` from its first instruction, in the terms of the proofs about it (PLAN.md G3, startup)

The proofs about the startup code are about a run and what it may read and store into (`Fn.Seg prof F Wl L s₀ o`,
`Start.Env K F Wl`). Here both are had from the launch, for one footprint.

- `zzsFoot lo top L`: written, the stack from `lo` to its end `top` and the pages of `.data` and `.bss`; read, the
  pages of the headers and of `.rodata`; owned, nothing; the code, `L`.
- `zzsFoot_ok`: it is memory a function can use (`Footprint.Ok`) at the first instruction, for `lo` in the stack's
  mapping and `L` the file's bytes in the text segment's pages.
- `launch_segOf`: `Fn.Seg` of the launch's state, with all that is written as what a run may store into.
- `StackAt.envOf`: `Start.Env` of `ctxOf`: the frame of `__libc_start_main`, the variables, the tables, the
  environment's array, the auxiliary vector and the environment's strings are in the footprint.
-/
namespace FV7z.Start
open ZellicX86 FV7z.Fn
open FV7z.AuxInit (globals)

/-- The footprint of `7zzs` from its first instruction. -/
def zzsFoot (lo top : Nat) (L : List (Addr × List Byte)) : Footprint :=
  ⟨[⟨BitVec.ofNat 64 lo, top - lo⟩, ⟨0x777000#64, 0x32000⟩], [],
    [⟨0x400000#64, 0x1000⟩, ⟨0x6d8000#64, 0x9e000⟩], L⟩

variable {lo top : Nat} {L : List (Addr × List Byte)} {y : Addr}

theorem zzsFoot_stack (ht : top ≤ 2 ^ 47) (h1 : lo ≤ y.toNat) (h2 : y.toNat < top) :
    Foot (zzsFoot lo top L).writes y := by
  refine ⟨⟨BitVec.ofNat 64 lo, top - lo⟩, List.mem_cons_self, ?_⟩
  show (BitVec.ofNat 64 lo).toNat ≤ y.toNat ∧ y.toNat < (BitVec.ofNat 64 lo).toNat + (top - lo)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem zzsFoot_var (h1 : 0x777000 ≤ y.toNat) (h2 : y.toNat < 0x7a9000) : Foot (zzsFoot lo top L).writes y := by
  refine ⟨⟨0x777000#64, 0x32000⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  show 0x777000 ≤ y.toNat ∧ y.toNat < 0x777000 + 0x32000
  omega

theorem zzsFoot_hdr (h1 : 0x400000 ≤ y.toNat) (h2 : y.toNat < 0x401000) : Foot (zzsFoot lo top L).reads y := by
  refine ⟨⟨0x400000#64, 0x1000⟩, List.mem_cons_self, ?_⟩
  show 0x400000 ≤ y.toNat ∧ y.toNat < 0x400000 + 0x1000
  omega

theorem zzsFoot_ro (h1 : 0x6d8000 ≤ y.toNat) (h2 : y.toNat < 0x776000) : Foot (zzsFoot lo top L).reads y := by
  refine ⟨⟨0x6d8000#64, 0x9e000⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  show 0x6d8000 ≤ y.toNat ∧ y.toNat < 0x6d8000 + 0x9e000
  omega

theorem foot_writes {F : Footprint} (h : Foot F.writes y) : Foot F.data y :=
  foot_append_iff.2 (.inl (foot_append_iff.2 (.inl h)))

theorem foot_reads {F : Footprint} (h : Foot F.reads y) : Foot F.data y := foot_append_iff.2 (.inr h)

/-- At the first instruction of `7zzs`, `zzsFoot` is memory a function can use. -/
theorem zzsFoot_ok {l : Launch} {hdr : ElfHeader} {c : ExecChoice}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hst : StackAt l.prof l.s₀ l.args hdr zzsPhdrs c) (hlo : (stackLayout l.args l.prof.linux c).start ≤ lo)
    (hlt : lo ≤ c.stackTop) (h7 : 0x7a9000 ≤ lo)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) :
    (zzsFoot lo c.stackTop L).Ok l.prof.feat l.s₀ := by
  have htop := hst.top.2
  have elo : (BitVec.ofNat 64 lo).toNat = lo := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine launch_footOk h hst rfl ?_ ?_ hL ?_
  · intro r hr
    simp only [zzsFoot, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · left
      show _ ≤ (BitVec.ofNat 64 lo).toNat ∧ (BitVec.ofNat 64 lo).toNat + (c.stackTop - lo) ≤ c.stackTop
      rw [elo]
      omega
    · exact .inr ⟨by decide, by decide⟩
  · intro r hr
    simp only [zzsFoot, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl ⟨by decide, by decide⟩)
    · exact .inr (.inl ⟨by decide, by decide⟩)
  · intro r hr q hq a hra hqa
    simp only [Footprint.codeRgns, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨b, eb, h1, h2, -⟩ := hL p hp
    have e : (BitVec.ofNat 64 b).toNat = b := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [Rgn.Mem, eb, e] at hqa
    simp only [Footprint.data, zzsFoot, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [Rgn.Mem, elo] at hra
      omega
    · have : 0x777000 ≤ a.toNat := hra.1
      omega
    · have : a.toNat < 0x400000 + 0x1000 := hra.2
      omega
    · have : 0x6d8000 ≤ a.toNat := hra.1
      omega

/-- The run of `7zzs` from its first instruction, for a run that may store into all `zzsFoot` writes. -/
theorem launch_segOf {l : Launch} {hdr : ElfHeader} {c : ExecChoice} {n : Nat} {o : Oracle}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n)
    (hst : StackAt l.prof l.s₀ l.args hdr zzsPhdrs c) (hlo : (stackLayout l.args l.prof.linux c).start ≤ lo)
    (hlt : lo ≤ c.stackTop) (h7 : 0x7a9000 ≤ lo)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (ho : Undisturbed o) :
    Seg l.prof (zzsFoot lo c.stackTop L) (zzsFoot lo c.stackTop L).writes L l.s₀ o :=
  ⟨zzsFoot_ok h hst hlo hlt h7 hL, launch_ready h hroom, ho, rfl, rfl, fun _ hy => hy⟩

/-- The variables `__libc_start_main` and `_dl_aux_init` set are in `.data` and `.bss`. -/
theorem dg_bd : ∀ r ∈ d3 ++ globals, 0x777000 ≤ r.base.toNat ∧ r.base.toNat + r.len ≤ 0x7a9000 := by decide

/-- What the startup reads and stores into is in `zzsFoot`, for `lo` at least 400 bytes below the first `rsp`. -/
theorem StackAt.envOf {prof : Profile} {s : State} {a : ExecArgs} {c : ExecChoice}
    (h : StackAt prof s a (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c)
    (hlo : lo + 400 ≤ (stackLayout a prof.linux c).sp) :
    Env (ctxOf prof s a c) (zzsFoot lo c.stackTop L) (zzsFoot lo c.stackTop L).writes := by
  obtain ⟨r1, r2, r3⟩ := runs_apart (prof := prof) (hdr := ElfHeader.read V2606.zzs.blob.bytes) (phs := zzsPhdrs)
    h.top.1 h.align h.limits
  rw [wordBytes_length, stackWords_length, auxv_length] at r1
  simp only [List.length_append] at r2
  have htop := h.top.2
  have hac : 22 ≤ auxCount prof.linux := by
    unfold auxCount
    split <;> omega
  have hrsp : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf prof s a c).bp.toNat = (stackLayout a prof.linux c).sp - 400 := by
    show (s.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  have henv : (ctxOf prof s a c).envp.toNat = (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) := by
    show (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have eN : (ctxOf prof s a c).N = a.envp.length := rfl
  have eM : (ctxOf prof s a c).M = auxCount prof.linux - 1 := rfl
  have e1 : (ctxOf prof s a c).aq = aqI := rfl
  have e3 : (ctxOf prof s a c).alen = alenI := by simp only [ctxOf]
  exact {
    ws := fun y hy => foot_writes hy
    stk := fun y h1 h2 => zzsFoot_stack htop (by omega) (by omega)
    arg := fun y h1 h2 => foot_writes (zzsFoot_stack htop (by omega) (by omega))
    gl := by
      intro r hr y hy
      have b := dg_bd r hr
      exact zzsFoot_var (Nat.le_trans b.1 hy.1) (Nat.lt_of_lt_of_le hy.2 b.2)
    tab := fun y h1 h2 => foot_reads (zzsFoot_ro (by omega) (by omega))
    nm := fun y h1 h2 => foot_reads (zzsFoot_ro (by omega) (by omega))
    lst := fun y h1 h2 => foot_writes (zzsFoot_var (by omega) (by omega))
    env := by
      intro y h1 h2
      rw [henv] at h1 h2
      rw [eN, eM] at h2
      exact foot_writes (zzsFoot_stack htop (by omega) (by omega))
    str := by
      intro i hi y h1 h2
      rw [eN] at hi
      obtain ⟨b1, b2⟩ := h.env_in hi
      have ep : ((ctxOf prof s a c).ptr i).toNat =
          (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 := by
        show (BitVec.ofNat 64 _).toNat = _
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have el : (ctxOf prof s a c).len i = (a.envp.getD i []).length := rfl
      rw [ep] at h1 h2
      rw [el] at h2
      exact foot_writes (zzsFoot_stack htop (by omega) (by omega))
    al := by
      intro t ht hne y h1 h2
      rw [e1] at hne h1 h2
      rw [e3] at h2
      have b := al_bd t ht hne
      exact foot_reads (zzsFoot_ro (by omega) (by omega)) }

end FV7z.Start
