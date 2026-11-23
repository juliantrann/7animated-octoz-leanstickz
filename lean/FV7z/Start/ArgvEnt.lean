import FV7z.Start.Arg0Ent
import FV7z.Start.Argv0
import FV7z.Start.LchOf
/-!
# `argv[0]` for `lif_ok`, from the launch (PLAN.md G3, startup)

At the call of `__libc_init_first`, `r12` holds `argv` (`ctxOf`'s, `rsp + 8` of the launch). `StackAt.argv0` gives
the pointer there and the string in the launch bytes; `ent_arg0` carries them to `lif_ok`'s bytes, which differ
from the launch bytes only below the stack words they lie in.

- `ent_argv`: `ha0`, `hnz`, `nfit`, `nnz`, `nz` of `lif_ok` for `argv = rsp + 8`, with `a0 = strings` and
  `n = (arg0 a).length`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- `argv[0]` in `lif_ok`'s bytes, for the launch's `argv`: the stack from the layout's `sp` up is data, and
`__libc_init_first`'s frame, the TLS block and the image lie below it. -/
theorem ent_argv {prof : Profile} {s : State} {a : ExecArgs} {c : ExecChoice} {W V : Addr → Byte} {b : Addr}
    {ver : BitVec 32} {D : Addr → Prop} {g : Gprs} {ra ra₀ : BitVec 64}
    (h : StackAt prof s a (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c) (hok : a.Ok)
    (hM : MB (ctxOf prof s a c) V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW (ctxOf prof s a c) W V b ver D) (hlo : 400 ≤ (stackLayout a prof.linux c).sp)
    (htl : b.toNat + 8192 ≤ (stackLayout a prof.linux c).sp + 8)
    (hr : g.rsp.toNat ≤ (stackLayout a prof.linux c).sp) (hr0 : 32 ≤ g.rsp.toNat)
    (hD : ∀ x : Addr, (stackLayout a prof.linux c).sp ≤ x.toNat → x.toNat < c.stackTop → D x) :
    rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        s.cpu.gpr.rsp + 8#64) = BitVec.ofNat 64 (stackLayout a prof.linux c).strings ∧
      BitVec.ofNat 64 (stackLayout a prof.linux c).strings ≠ 0#64 ∧
      (BitVec.ofNat 64 (stackLayout a prof.linux c).strings).toNat + (arg0 a).length < 2 ^ 64 ∧
      (∀ k < (arg0 a).length, Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)
        (Addr.add (BitVec.ofNat 64 (stackLayout a prof.linux c).strings) k) ≠ 0) ∧
      Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)
        (Addr.add (BitVec.ofNat 64 (stackLayout a prof.linux c).strings) (arg0 a).length) = 0 := by
  obtain ⟨hV, hVs, h1, h2⟩ := StackAt.argv0 h (by omega) s.cpu.gpr.rax
  have htop := h.top.2
  have t0 : s.cpu.gpr.rsp.toNat = (stackLayout a prof.linux c).sp := by
    rw [h.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hy : (s.cpu.gpr.rsp + 8#64).toNat = (stackLayout a prof.linux c).sp + 8 := by
    have := t0
    clear hV hVs
    bv_omega
  have tbp : (ctxOf prof s a c).bp.toNat = (stackLayout a prof.linux c).sp - 400 := by
    show (s.cpu.gpr.rsp - 400#64).toNat = _
    have := t0
    clear hV hVs
    bv_omega
  have ts : ∀ k ≤ (arg0 a).length, (BitVec.ofNat 64 ((stackLayout a prof.linux c).strings + k)).toNat =
      (stackLayout a prof.linux c).strings + k := fun k hk => by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  exact ent_arg0 (y := s.cpu.gpr.rsp + 8#64) (S := (stackLayout a prof.linux c).strings)
    (n := (arg0 a).length) (s := arg0 a) hM hb hb' hW (by omega) (by omega) (by omega) (by omega) hr0
    (fun i hi => by
      have t : (Addr.add (s.cpu.gpr.rsp + 8#64) i).toNat = (s.cpu.gpr.rsp + 8#64).toNat + i :=
        toNat_add_of_fits (n := 8) hi (by omega)
      exact hD _ (by omega) (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k hk => by
      have t := ts k hk
      exact hD _ (by omega) (by omega))
    hV hVs rfl (arg0_nz hok)

end FV7z.Start
