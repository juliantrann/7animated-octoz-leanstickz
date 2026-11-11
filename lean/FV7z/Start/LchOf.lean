import FV7z.Start.Lch
/-!
# What the launch gives of `__libc_start_main`'s start, from Zellic's `execve` (PLAN.md G3, startup)

- `varsOf`, `gl_varsOf`: `_dl_aux_init`'s variables as the bytes hold them.
- `ctxOf`: the context (`Ctx`) of `__libc_start_main`'s start in a state `execve` starts 7zzs in: the stack 400 bytes
  below `rsp`, `argc` and `argv` at `rsp`, the environment's array after them, the auxiliary vector `execve` wrote,
  the environment's strings, and the bytes after `_start`'s three stores.
- `StackAt.lch`: `Ctx.Lch` of it, for an exec that is not a secure one and an environment with no string beginning
  with `GLIBC_TUNABLES=` or a tunable's alias and `=`.
- `launch_lch`: the same from the launch (`Launch.Of`), for some choice of the kernel.
- `ctxOf_entry`: `ctxOf` is as `entry_cpu` asks of its context (`hbp`, `hmain`, `hargc`, `hargv`, `hinit`, `hfini`,
  `hrtld`, `hV0`, `hq`, `hz`, `hln`).
-/
namespace FV7z.Start
open ZellicX86
open FV7z.AuxInit (Vars)
open FV7z.Auxv (Gl)
open FV7z.Tun (gz)

/-- `_dl_aux_init`'s variables as the bytes `V` hold them. -/
def varsOf (V : Addr → Byte) : Vars where
  pagesize := rdq(V, 0x7933d8#64)
  clktck := rdd(V, 0x7a85c0#64)
  phdr := rdq(V, 0x7a8580#64)
  phnum := rdq(V, 0x7a8598#64)
  platform := rdq(V, 0x7a8548#64)
  hwcap := rdq(V, 0x7a4ac8#64)
  hwcap2 := rdq(V, 0x7a4ac0#64)
  sysinfoDso := rdq(V, 0x7a8508#64)
  fpuControl := rdw(V, 0x7933cc#64)
  secure := rdd(V, 0x791ce0#64)
  decided := rdd(V, 0x7a85c4#64)
  random := rdq(V, 0x791ca0#64)

theorem gl_varsOf (V : Addr → Byte) : Gl V (varsOf V) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The context of `__libc_start_main`'s start in a state `execve` starts 7zzs in. -/
noncomputable def ctxOf (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) : Ctx where
  bp := s.cpu.gpr.rsp - 400#64
  main := 0x41cd90#64
  argc := (rdq(s.proc.mm.mem.readByte, s.cpu.gpr.rsp)).setWidth 32
  argv := s.cpu.gpr.rsp + 8#64
  init := 0x613ca0#64
  fini := 0x613d40#64
  rtld := s.cpu.gpr.rdx
  stackEnd := s.cpu.gpr.rsp - 8#64
  envp := BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))
  N := a.envp.length
  M := auxCount prof.linux - 1
  ty := fun n => BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)).getD n (0, 0)).1
  val := fun n => BitVec.ofNat 64 ((auxv prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)).getD n (0, 0)).2
  sn := Classical.choose (auxv_idx prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)).2.2.1
  w0 := varsOf (Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp s.cpu.gpr.rax)
  ptr := fun i => BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
    (a.argv'.length + i) 0)
  ez := fun i k => (a.envp.getD i [] ++ [0]).getD k 0
  len := fun i => (a.envp.getD i []).length
  lmax := 131071
  aq := aqI
  az := azI
  alen := alenI
  V0 := Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp s.cpu.gpr.rax

/-- What the launch gives of `__libc_start_main`'s start (`Ctx.Lch`), in a state `execve` starts 7zzs in: for an exec
that is not a secure one, and an environment with no string beginning with `GLIBC_TUNABLES=` or with a tunable's
alias and `=`. -/
theorem StackAt.lch {prof : Profile} {s : State} {a : ExecArgs} {c : ExecChoice}
    (h : StackAt prof s a (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c)
    (hlo : 0x7a9000 + 400 ≤ (stackLayout a prof.linux c).sp) (hs : a.secure = false)
    (noG : ∀ i < a.envp.length, (∀ k < 14, (a.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (a.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < a.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (a.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (a.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61) :
    (ctxOf prof s a c).Lch := by
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
  have hbp : (s.cpu.gpr.rsp - 400#64).toNat = (stackLayout a prof.linux c).sp - 400 := by bv_omega
  have henv : (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))).toNat =
      (stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hlo' : 24 ≤ (stackLayout a prof.linux c).sp := by omega
  have hrd := h.lch_reads hlo' s.cpu.gpr.rax
  have hax := auxv_idx prof (ElfHeader.read V2606.zzs.blob.bytes)
    (phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs) a c (stackLayout a prof.linux c)
  have hzz := auxv_zzs prof a c (stackLayout a prof.linux c) hs
  have hptr : ∀ i < a.envp.length,
      (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
        (a.argv'.length + i) 0)).toNat =
      (stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 := by
    intro i hi
    have := (h.lch_str hlo' s.cpu.gpr.rax hi).2.1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  exact {
    hbp := by
      show (s.cpu.gpr.rsp - 400#64).toNat + 392 ≤ 2 ^ 64
      omega
    himg := by
      show (s.cpu.gpr.rsp - 400#64).toNat + 376 ≤ 0x400000 ∨ 0x7a9000 ≤ (s.cpu.gpr.rsp - 400#64).toNat
      omega
    hse := V1_se _ _ _ (by omega)
    henvp := h.envp
    hfit := by
      show (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))).toNat +
        (8 * (a.envp.length + 1) + 16 * (auxCount prof.linux - 1) + 8) ≤ 2 ^ 64
      omega
    cEnv := by
      show ((s.cpu.gpr.rsp - 400#64).toNat + 376 ≤
          (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))).toNat ∨ _) ∧
        (_ ∨ 0x7a85c8 ≤ (BitVec.ofNat 64 ((stackLayout a prof.linux c).sp + 8 * (1 + a.argv'.length + 1))).toNat)
      exact ⟨.inl (by omega), .inr (by omega)⟩
    henv := hrd.1
    hend := hrd.2.1
    hnz := by
      intro i hi h0
      have e := congrArg BitVec.toNat h0
      have b := (h.lch_str hlo' s.cpu.gpr.rax hi).1
      rw [show (ctxOf prof s a c).ptr i = BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings
        (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0) from rfl, hptr i hi] at e
      change _ = 0 at e
      omega
    hty := fun n hn => (hrd.2.2 n (Nat.lt_of_lt_of_le hn (Nat.sub_le _ _))).1
    hval := fun n hn => (hrd.2.2 n (Nat.lt_of_lt_of_le hn (Nat.sub_le _ _))).2
    hnzT := hax.1
    hendT := by
      have := (hrd.2.2 (auxCount prof.linux - 1) (by omega)).1
      rw [hax.2.1] at this
      exact this
    hsn := (Classical.choose_spec hax.2.2.1).1
    hsec := (Classical.choose_spec hax.2.2.1).2
    hsec0 := hzz.1
    hph := hax.2.2.2.2.1
    hph0 := hzz.2
    hgl := gl_varsOf _
    sfit := by
      intro i hi
      have b := (h.lch_str hlo' s.cpu.gpr.rax hi).2.1
      show (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
        (a.argv'.length + i) 0)).toNat + (a.envp.getD i []).length + 1 ≤ 2 ^ 64
      rw [hptr i hi]
      omega
    cStr := by
      intro i hi
      have b := (h.lch_str hlo' s.cpu.gpr.rax hi).1
      show ((s.cpu.gpr.rsp - 400#64).toNat + 376 ≤
          (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings (a.argv' ++ a.envp)).getD
            (a.argv'.length + i) 0)).toNat ∨ _) ∧
        (_ ∨ 0x7a85c8 ≤ (BitVec.ofNat 64 ((stringAddrs (stackLayout a prof.linux c).strings
          (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0)).toNat)
      rw [hptr i hi]
      exact ⟨.inl (by omega), .inr (by omega)⟩
    hstr := fun i hi k hk => (h.lch_str hlo' s.cpu.gpr.rax hi).2.2 k hk
    hz := by
      intro i _
      show (a.envp.getD i [] ++ [0]).getD (a.envp.getD i []).length 0 = 0
      simp
    hlen := by
      intro i hi
      have := env_len h.limits hi
      show (a.envp.getD i []).length ≤ 131071
      omega
    noG := noG
    noA := by
      have e1 : (ctxOf prof s a c).aq = aqI := rfl
      have e2 : (ctxOf prof s a c).az = azI := rfl
      have e3 : (ctxOf prof s a c).alen = alenI := by simp only [ctxOf]
      intro i hi t ht
      rw [e1, e2, e3]
      exact noA i hi t ht }

/-- From the launch of 7zzs (Zellic's `execve`): for some choice of the kernel, `Ctx.Lch` of `ctxOf`, for an exec that
is not a secure one and an environment with no string beginning with `GLIBC_TUNABLES=` or with a tunable's alias and
`=`. -/
theorem launch_lch {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) (hs : l.args.secure = false)
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Lch := by
  obtain ⟨hdr, c, hr, hv, hst⟩ := launch_stackAt h hroom
  obtain rfl := readElf_zzs_hdr h.1 hr
  refine ⟨c, hv, hst, hst.lch ?_ hs noG noA⟩
  obtain ⟨-, hge, hlt⟩ := ExecStart.rsp h.2.1 hroom
  obtain ⟨r1, r2, r3⟩ := runs_apart (prof := l.prof) (hdr := ElfHeader.read V2606.zzs.blob.bytes)
    (phs := zzsPhdrs) hst.top.1 hst.align hst.limits
  simp only [List.length_append] at r2
  have htop := hst.top.2
  rw [hst.rsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hge
  omega

/-- `ctxOf` is as `entry_cpu` asks of its context: the stack, the arguments `_start` passes, the bytes after its
stores, and the tunables' aliases. -/
theorem ctxOf_entry (prof : Profile) (s : State) (a : ExecArgs) (c : ExecChoice) :
    (ctxOf prof s a c).bp + 376#64 = s.cpu.gpr.rsp - 24#64 ∧ (ctxOf prof s a c).main = 0x41cd90#64 ∧
    (ctxOf prof s a c).argc = (rdq(s.proc.mm.mem.readByte, s.cpu.gpr.rsp)).setWidth 32 ∧
    (ctxOf prof s a c).argv = s.cpu.gpr.rsp + 8#64 ∧ (ctxOf prof s a c).init = 0x613ca0#64 ∧
    (ctxOf prof s a c).fini = 0x613d40#64 ∧ (ctxOf prof s a c).rtld = s.cpu.gpr.rdx ∧
    (ctxOf prof s a c).V0 = Entry.V1 s.proc.mm.mem.readByte s.cpu.gpr.rsp s.cpu.gpr.rax ∧
    (ctxOf prof s a c).aq = aqI ∧ (ctxOf prof s a c).az = azI ∧ (ctxOf prof s a c).alen = alenI := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp only [ctxOf]⟩
  show s.cpu.gpr.rsp - 400#64 + 376#64 = s.cpu.gpr.rsp - 24#64
  bv_omega

end FV7z.Start
