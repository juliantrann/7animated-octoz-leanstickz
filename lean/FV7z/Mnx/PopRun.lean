import FV7z.Mnx.Pop
import FV7z.Mnx.Run
/-!
# `malloc` from a non-empty tcache bin: from 52 to the return address (PLAN.md G3, `malloc`)

- `mal_pop_tail`: `vc_52p` (`tcache_get`), `vc_164r` (the pops, `rax` the entry) and the `ret`, beside `mal_tail`
  (the empty bin, `_int_malloc`). The memory at the return address is `Vget` of the memory at 52; the registers the
  pops set are read from it.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- The count of bin `ix` of the tcache `C` as `malloc` reads it. -/
abbrev cntM (V : Addr → Byte) (C ix : Addr) : BitVec 16 := ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2))

/-- `malloc` after the first call, from 52 (the pushes done, `rbx` the bin `ix`, `S` the stack pointer) with a chunk
in the bin: `tcache_get`, the pops, the `ret`; `rax` the entry `e`. -/
theorem mal_pop_tail {fb C ix e : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mnx_at mnx) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mnx_at.add 52) (hbx : X.cpu.gpr.rbx = ix) (hk : ix.toNat < 64)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hcn : cntM V C ix ≠ 0) (he : rdq(V, C + ix * 8#64 + 128#64) = e)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (f1 : ∀ i < 2, Foot F.data (Addr.add (C + ix * 2#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add e i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (e + 8#64) i))
    (hsd : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Vget V C ix e (cntM V C ix), X.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vget V C ix e (cntM V C ix)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = e → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8 + 8 + 8 →
      Z.cpu.gpr.rbx = rdq(Vget V C ix e (cntM V C ix), X.cpu.gpr.rsp) →
      Z.cpu.gpr.rbp = rdq(Vget V C ix e (cntM V C ix), X.cpu.gpr.rsp + 8) →
      Z.cpu.gpr.r12 = rdq(Vget V C ix e (cntM V C ix), X.cpu.gpr.rsp + 8 + 8) →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- 52 → 164
  refine (c_52 prof fb).run c hfs hin _ hK hA hrip
    (vc_52p hbx hk htb htc hC hcn he hfb hft f1 f2 f3 w1 w2 w3) ?_
  rintro j' g₁ fl V₁ ⟨rfl, sp₁, -, -, -, r13₁, r14₁, r15₁, r8₁, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  -- 164 → 171
  refine (c_164 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
    (vc_164r (by rw [sp₁]; exact fun i hi => hsd i (by omega))) ?_
  rintro j' g₅ fl V₅ ⟨rfl, rfl, ax₅, sp₅, bx₅, bp₅, r12₅, r13₅, r14₅, r15₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  subst hg₅
  rw [sp₁] at sp₅ bx₅ bp₅ r12₅
  have e24 : X.cpu.gpr.rsp + 8 + 8 + 8 = X.cpu.gpr.rsp + BitVec.ofNat 64 24 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  -- the `ret`
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_171 _)
    (by rw [sp₅]; exact off_ft hsd 24 e24 (by decide)) hin₂ h₂ (by rw [sp₅]; exact hra) ?_
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg']; exact ax₅.trans r8₁) ?_ (by rw [hg']; exact bx₅)
    (by rw [hg']; exact bp₅) (by rw [hg']; exact r12₅) (by rw [hg']; exact r13₅.trans r13₁)
    (by rw [hg']; exact r14₅.trans r14₁) (by rw [hg']; exact r15₅.trans r15₁)
  rw [hg']
  show Y₅.cpu.gpr.rsp + 8 = _
  rw [sp₅]

end FV7z.Mnx
