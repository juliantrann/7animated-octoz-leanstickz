import FV7z.Pco.Cuts
import FV7z.Pcp.Holds
import FV7z.Close.Holds
/-!
# `_pthread_cleanup_pop` unlinks a cleanup buffer (PLAN.md §M, M1)

glibc 2.31's `_pthread_cleanup_pop (buffer, execute)` at `0x5ff010` in `7zzs`: the thread's `cleanup` (`fs:0x2f8`)
set to `buffer->__prev` (at 24); if `execute` (32 bits) is 0, `ret` (40); else a tail jump (`jmp rax`, 31) to
`buffer->__routine` (at 0) with `rdi` = `buffer->__arg` (at 8). Two pieces of the code, from the entry (0) to the
`ret` or to the loads (21), and from 21 to the jump.

- `V1`: the store of `__prev` to the thread's word; `rtn`, `arg`: the routine and its argument, read after it.
- `pco_ok`: with `execute` 0, at the return address with the store done and `rax` the old `__prev` (`kn`); else at
  the routine with `rax` the routine, `rdi` and `r8` its argument (`kx`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pco

/-- The `jmp rax`. -/
def pjr : List Byte := [0xff, 0xe0]
theorem pjr_0 : ∀ feat, Dec feat pjr 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem wr_31 : pjr <+: pco.drop 31 := by decide +kernel
theorem jmp_31 (feat : Features) : Dec feat pco 31 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 31) (k := 0) (pjr_0 feat) wr_31 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_40 : pret <+: pco.drop 40 := by decide +kernel
theorem ret_40 (feat : Features) : Dec feat pco 40 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 40) (k := 0) (pret_0 feat) w_40 (Nat.zero_le _)

/-- `buffer->__prev`. -/
abbrev prv (V : Addr → Byte) (p : Addr) : BitVec 64 := ofBytesLE 64 (List.map V (byteAddrs (p + 24#64) 8))
/-- The thread's `cleanup` set to `buffer->__prev`. -/
abbrev V1 (fb : Addr) (p : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst V (fb + 760#64) (toBytesLE (prv V p) 8)
/-- `buffer->__routine`. -/
abbrev rtn (V : Addr → Byte) (p : Addr) : BitVec 64 := ofBytesLE 64 (List.map V (byteAddrs p 8))
/-- `buffer->__arg`. -/
abbrev arg (V : Addr → Byte) (p : Addr) : BitVec 64 := ofBytesLE 64 (List.map V (byteAddrs (p + 8#64) 8))

variable {F : Footprint} {Wl : List Rgn}

/-- `execute` 0: the store, then the `ret`. -/
theorem vc_no {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : BitVec.setWidth 32 g.rsi = 0#32)
    (hb : ∀ i < 32, Foot F.data (Addr.add g.rdi i)) (hfw : ∀ i < 8, Foot Wl ((fb + 760#64).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 40 ∧ g' = { g with rax := prv V g.rdi } ∧ V' = V1 fb g.rdi V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hb ⊢
  wpx [W_0, W_21, o0, o1, Op.ld, Op.stf, BitVec.and_self]
  first
  | exact ⟨Pcp.ft8 hb 24 (by decide), hfw, fun hc => absurd hz (by simpa using hc)⟩
  | exact ⟨Pcp.ft8 hb 24 (by decide), hfw, fun _ => trivial, fun hc => absurd hz (by simpa using hc)⟩

/-- `execute` not 0: the store, the loads, up to the jump. -/
theorem vc_ex {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : BitVec.setWidth 32 g.rsi ≠ 0#32)
    (hb : ∀ i < 32, Foot F.data (Addr.add g.rdi i)) (hfw : ∀ i < 8, Foot Wl ((fb + 760#64).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 31 ∧
      g' = { g with
        rax := rtn (V1 fb g.rdi V) g.rdi, rdi := arg (V1 fb g.rdi V) g.rdi, r8 := arg (V1 fb g.rdi V) g.rdi } ∧
      V' = V1 fb g.rdi V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hb ⊢
  wpx [W_0, W_21, o0, o1, Op.ld, Op.stf, BitVec.and_self]
  refine ⟨Pcp.ft8 hb 24 (by decide), hfw, fun hc => absurd (by simpa using hc) hz, fun _ => ?_⟩
  first
  | exact ⟨Pcp.ft8 hb 8 (by decide), fun i hi => hb i (by omega)⟩
  | exact ⟨Pcp.ft8 hb 8 (by decide), fun i hi => hb i (by omega), rfl, rfl⟩
  | exact ⟨Pcp.ft8 hb 8 (by decide), fun i hi => hb i (by omega), rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `_pthread_cleanup_pop (buffer, execute)`: the thread's list set to `buffer->__prev` (`V1`); with `execute` 0, at
the return address (`kn`); else at `buffer->__routine`, a code byte (`hR`), with `rdi` its argument (`kx`). -/
theorem pco_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pco_at pco)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pco_at)
    (hb : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hfw : ∀ i < 8, Foot Wl ((fb + 760#64).add i))
    (hfb : (fb + 760#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 760#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (fb + 760#64).toNat)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (hR : BitVec.setWidth 32 X.cpu.gpr.rsi ≠ 0#32 → ∃ (eR : Addr) (codeR : List Byte) (jR : Nat),
      CodeIn L eR codeR ∧ jR < codeR.length ∧ rtn (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi = eR.add jR)
    (kn : BitVec.setWidth 32 X.cpu.gpr.rsi = 0#32 → ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (V1 fb X.cpu.gpr.rdi V) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := prv V X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kx : BitVec.setWidth 32 X.cpu.gpr.rsi ≠ 0#32 → ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (V1 fb X.cpu.gpr.rdi V) → Y.cpu.rip = rtn (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := rtn (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi,
        rdi := arg (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi,
        r8 := arg (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases hz : BitVec.setWidth 32 X.cpu.gpr.rsi = 0#32
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 40 ∧ g' = { X.cpu.gpr with rax := prv V X.cpu.gpr.rdi } ∧ V' = V1 fb X.cpu.gpr.rdi V)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_no hz hb hfw) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    have hra1 : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (V1 fb X.cpu.gpr.rdi V)) = e₂.add j₂ := by
      rw [Tun.rd_Vst V (fb + 760#64) (toBytesLE (prv V X.cpu.gpr.rdi) 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length]; exact hfb) hsp8 (by rw [toBytesLE_length]; exact hfd)]
      exact hra
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_40 _) (by rw [hsp]; exact hl) hin₂ h₂
      (by rw [hsp]; exact hra1) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hz Z t' hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · obtain ⟨eR, codeR, jR, hinR, hjR, hRt⟩ := hR hz
    refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 31 ∧
        g' = { X.cpu.gpr with
          rax := rtn (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi,
          rdi := arg (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi,
          r8 := arg (V1 fb X.cpu.gpr.rdi V) X.cpu.gpr.rdi } ∧
        V' = V1 fb X.cpu.gpr.rdi V)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_ex hz hb hfw) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine c.s_jmp_rx hKY hAY hin (lt_len (by decide)) hrY (jmp_31 _) hinR hjR (by rw [hgY]; exact hRt) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kx hz Y₂ t₂ hK₂ hA₂ (hr₂.trans hRt.symm) (hg₂.trans hgY)

end FV7z.Pco
