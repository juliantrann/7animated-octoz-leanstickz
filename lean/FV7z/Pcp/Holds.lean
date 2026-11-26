import FV7z.Pcp.Cuts
import FV7z.Close.Holds
/-!
# `_pthread_cleanup_push` links a cleanup buffer (PLAN.md §M, M1)

glibc 2.31's `_pthread_cleanup_push (buffer, routine, arg)` at `0x5fefe0` in `7zzs`: `buffer->__routine` = `routine`
(at 0), `buffer->__arg` = `arg` (at 8), `buffer->__prev` = the thread's `cleanup` (`fs:0x2f8`, at 24), and the thread's
`cleanup` = `buffer`; `ret` (33).

- `ret_33`: the instruction outside the block; `vc_0`: the verification condition of the block.
- `pcp_ok`: with the buffer's 32 bytes and the thread's word writable, the run reaches the return address with the
  four stores done (`V4`) and `rax` the old head (`hd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pcp

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: pcp.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat pcp 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)

/-- The buffer's routine and argument stored. -/
abbrev V2 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst V g.rdi (toBytesLE g.rsi 8)) (g.rdi + 8#64) (toBytesLE g.rdx 8)
/-- The thread's `cleanup` before. -/
abbrev hd (fb : Addr) (g : Gprs) (V : Addr → Byte) : BitVec 64 :=
  ofBytesLE 64 (List.map (V2 g V) (byteAddrs (fb + 760#64) 8))
/-- The four stores. -/
abbrev V4 (fb : Addr) (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (V2 g V) (g.rdi + 24#64) (toBytesLE (hd fb g V) 8)) (fb + 760#64) (toBytesLE g.rdi 8)

/-- 8 bytes at `d` of 32. -/
theorem ft8 {R : List Rgn} {a : Addr} (h : ∀ i < 32, Foot R (Addr.add a i)) (d : Nat) (hd : d + 8 ≤ 32) :
    ∀ i < 8, Foot R ((a + BitVec.ofNat 64 d).add i) := fun i hi => by
  have := h (d + i) (by omega)
  rw [← addr_add_add] at this
  exact this

variable {F : Footprint} {Wl : List Rgn}

/-- The four stores and the load. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 32, Foot Wl (Addr.add g.rdi i)) (hfr : ∀ i < 8, Foot F.data ((fb + 760#64).add i))
    (hfw : ∀ i < 8, Foot Wl ((fb + 760#64).add i)) (h : ∀ fl, Q 33 { g with rax := hd fb g V } fl (V4 fb g V)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.st, Op.ldf, Op.stf]
  exact ⟨fun i hi => hw i (by omega), ft8 hw 8 (by decide), hfr, ft8 hw 24 (by decide), hfw, h _⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- `_pthread_cleanup_push (buffer, routine, arg)`: the run reaches the return address with the buffer filled and
linked in front of the thread's list (`V4`), `rax` the old head. -/
theorem pcp_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pcp_at pcp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pcp_at)
    (hw : ∀ i < 32, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hfr : ∀ i < 8, Foot F.data ((fb + 760#64).add i))
    (hfw : ∀ i < 8, Foot Wl ((fb + 760#64).add i))
    (hd32 : X.cpu.gpr.rdi.toNat + 32 ≤ 2 ^ 64)
    (hdr : X.cpu.gpr.rdi.toNat + 32 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hfb : (fb + 760#64).toNat + 8 ≤ 2 ^ 64)
    (hfd : (fb + 760#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (fb + 760#64).toNat)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (V4 fb X.cpu.gpr V) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := hd fb X.cpu.gpr V, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 :=
    toNat_add_of_fits (a := X.cpu.gpr.rdi) (i := 8) (n := 32) (by decide) hd32
  have e24 : (X.cpu.gpr.rdi + 24#64).toNat = X.cpu.gpr.rdi.toNat + 24 :=
    toNat_add_of_fits (a := X.cpu.gpr.rdi) (i := 24) (n := 32) (by decide) hd32
  have hra4 : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (V4 fb X.cpu.gpr V)) = e₂.add j₂ := by
    simp only [V4, V2]
    rw [Tun.rd_Vst _ (fb + 760#64) (toBytesLE X.cpu.gpr.rdi 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length]; exact hfb) hsp8 (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 24#64) (toBytesLE (hd fb X.cpu.gpr V) 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length, e24]; omega) hsp8 (by rw [toBytesLE_length, e24]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rdi + 8#64) (toBytesLE X.cpu.gpr.rdx 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length, e8]; omega) hsp8 (by rw [toBytesLE_length, e8]; omega),
      Tun.rd_Vst _ X.cpu.gpr.rdi (toBytesLE X.cpu.gpr.rsi 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length]; omega) hsp8 (by rw [toBytesLE_length]; omega)]
    exact hra
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 33 ∧
      g' = { X.cpu.gpr with rax := hd fb X.cpu.gpr V } ∧ V' = V4 fb X.cpu.gpr V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hw hfr hfw fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_33 _) (by rw [hsp]; exact hl) hin₂ h₂
    (by rw [hsp]; exact hra4) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hgY]
  try rfl

end FV7z.Pcp
