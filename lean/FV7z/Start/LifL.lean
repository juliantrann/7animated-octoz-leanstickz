import FV7z.Start.ToLif
import FV7z.Start.ToPtr
import FV7z.Start.PtrAll
import FV7z.Start.ArgvEnt
import FV7z.Start.PlAt
import FV7z.Start.Psz
import FV7z.Start.Sdso
import FV7z.Start.Fpu
import FV7z.Start.Plat
/-!
# Names for the run from the launch to `__libc_init_first`'s return (PLAN.md G3, startup)

`launch_to_ptr` speaks of the break, the stack region below the layout's `sp` and the events of the run to
`0x613434` in the terms of the launch; `ptr_lif` takes them as `B`, `lo`, `lim` and `gev`. The abbreviations name
them, and the lemmas give what `ptr_lif` asks that `launch_to_ptr` does not state in its words:

- `brkOf`, `loOf`, `limOf`, `ptrEvs`: the break, the bottom of the stack region, the break's limit in pages and the
  events of `launch_to_ptr`'s continuation.
- `wn_data`: the data of `withNew F [⟨B, 8192⟩]` is `F`'s or the TLS block's.
- `lifW_lo`, `lifM_lo`: below `__libc_multiple_libcs` and the stack, `lif_ok`'s bytes are those at `0x613434`;
  the GOT is there.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- The break of the launch. -/
abbrev brkOf (l : Launch) : Addr := l.s₀.proc.mm.brk

/-- The bottom of the stack region of `launch_to_ptr`: `n` below the layout's `sp`. -/
abbrev loOf (l : Launch) (n : Nat) (c : ExecChoice) : Nat := (stackLayout l.args l.prof.linux c).sp - n

/-- The break's limit in pages in `launch_to_ptr`'s `Base`. -/
abbrev limOf (l : Launch) : Nat := pageUp (l.s₀.proc.mm.brk.toNat + 2 ^ 41) / 4096

/-- The events of the run from the launch to `0x613434`, after those of the caller (`launch_to_ptr`). -/
noncomputable abbrev ptrEvs (l : Launch) (c : ExecChoice) (s₂ : State) (g : Gprs) (x1 x2 x3 d r10 r8 r9 : BitVec 64)
    (u : List Byte) (y1 y2 y3 y4 y5 q1 q2 q3 : BitVec 64) : List Event :=
  [Seg.cetEv g,
    ⟨12, [0, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk, [], []⟩,
    ⟨12, [l.s₀.proc.mm.brk + 4544#64, x1, 63#64, x2, 7829360#64, x3], l.s₀.proc.mm.brk + 4544#64, [], []⟩,
    ⟨158#64, [4098#64, l.s₀.proc.mm.brk + 2176#64, d, r10, r8, r9], 0, [], []⟩,
    ⟨63, [(ctxOf l.prof l.s₀ l.args c).bp - 320#64, y1, y2, y3, y4, y5], 0, [], u⟩,
    ⟨218#64, [l.s₀.proc.mm.brk + 2176#64 + 720#64, q1, l.s₀.proc.mm.brk + 2176#64, q2, 7991568#64, q3],
      BitVec.ofNat 64 l.s₀.thread.tid, [], []⟩,
    ⟨273#64, [l.s₀.proc.mm.brk + 2176#64 + 736#64, 24#64, l.s₀.proc.mm.brk + 2176#64, q2, 7991568#64, q3],
      0, [], []⟩,
    Pim.sgEv 32#64 q3 ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
    Pim.sgEv 33#64 0 ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
    Pim.mskEv ((ctxOf l.prof l.s₀ l.args c).bp + 104#64),
    Pim.rlEv ((ctxOf l.prof l.s₀ l.args c).bp + 104#64) 0 0 (s₂.proc.signal.rlimits ⟨3, by decide⟩).bytes]

/-- The data of a footprint with the TLS block's region added is the footprint's or the region's. -/
theorem wn_data {F : Footprint} {B a : Addr} (h : Foot (withNew F [⟨B, 8192⟩]).data a) :
    Foot F.data a ∨ (B.toNat ≤ a.toNat ∧ a.toNat < B.toNat + 8192) := by
  change Foot ((([⟨B, 8192⟩] ++ F.writes) ++ []) ++ F.reads) a at h
  rcases foot_append_iff.1 h with h | h
  · rcases foot_append_iff.1 h with h | h
    · rcases foot_append_iff.1 h with h | h
      · obtain ⟨r, hr, hb⟩ := h
        rw [List.mem_singleton] at hr
        subst hr
        exact .inr hb
      · exact .inl (foot_writes h)
    · obtain ⟨r, hr, -⟩ := h
      cases hr
  · exact .inl (foot_append_iff.2 (.inr h))

/-- `lif_ok`'s bytes `lifW` below `__libc_multiple_libcs` (`0x793ac0`) and far below the stack: those at
`0x613434`. -/
theorem lifW_lo {W : Addr → Byte} {g : Gprs} {ra ra₀ : BitVec 64} {a : Addr} (ha : a.toNat < 7944640)
    (hr : 7944640 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) a = W a := by
  unfold Lif.LifMem Lif.LifStk
  rw [Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_, Ndi.vap (toBytesLE_length _ _) ?_ ?_,
    Ndi.vap (toBytesLE_length _ _) ?_ ?_]
  all_goals bv_omega

/-- `lif_ok`'s bytes `fV W sp gY` below `sp + 80`: `W`'s. -/
theorem lifM_lo {W : Addr → Byte} {sp : Addr} {g : Gprs} {a : Addr} (hs : sp.toNat + 120 ≤ 2 ^ 64)
    (ha : a.toNat < sp.toNat + 80) : Ndi.fV W sp g a = W a :=
  Ndi.fV_out hs (.inl ha)

end FV7z.Start
