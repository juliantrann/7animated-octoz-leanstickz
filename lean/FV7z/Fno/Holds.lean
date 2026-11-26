import FV7z.Fno.Cuts
import FV7z.Close.Holds
/-!
# `__fileno` returns a stream's descriptor (PLAN.md §M, M1)

glibc 2.31's `__fileno (fp)` at `0x627140` in `7zzs`: if the stream is open (`_IO_IS_FILEBUF`, bit `0x2000` of
`fp->_flags`, the 4 bytes at `fp`) and its descriptor (`fp->_fileno`, the 4 bytes at `fp + 0x70`) is not negative,
that descriptor in `eax`; else `errno` (`fs:-0x48`, `Close.errnoAt`) set to `EBADF` (9) and -1 in `eax`. Two pieces
of the code: from the entry (0) to the first `ret` (19) or to the error path (24), and from 24 to the second `ret`
(43).

- `FnoOk`: the stream open and its descriptor not negative.
- `fno_ok`: called with the flags and the descriptor readable and `errno`'s 4 bytes in what the run may store into,
  the run reaches the return address with the descriptor in `rax` (`FnoOk`) or `errno` set and `eax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fno

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: fno.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat fno 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)
theorem w_43 : pret <+: fno.drop 43 := by decide +kernel
theorem ret_43 (feat : Features) : Dec feat fno 43 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 43) (k := 0) (pret_0 feat) w_43 (Nat.zero_le _)

/-- The low 4 bytes of the stream's flags. -/
abbrev flg (V : Addr → Byte) (p : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs p 4).map V)
/-- The stream's descriptor. -/
abbrev fdv (V : Addr → Byte) (p : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs (Addr.add p 112) 4).map V)
/-- The stream open (`_IO_IS_FILEBUF`) and its descriptor not negative. -/
def FnoOk (V : Addr → Byte) (p : Addr) : Prop := flg V p &&& 8192#32 ≠ 0 ∧ (fdv V p).msb = false
/-- `EBADF` as `errno`'s bytes. -/
abbrev ebadf : List Byte := toBytesLE (9#32) 4

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the first `ret`: the stream open and its descriptor not negative. -/
theorem vc_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (fd : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 112) i)) (h : FnoOk V g.rdi) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 19 ∧ g' = { g with rax := BitVec.setWidth 64 (fdv V g.rdi) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2⟩ := h
  dsimp only at fa fd h1 h2 ⊢
  wpx [W_0, W_12, o0, o1, Op.testmi, Op.ld]
  refine ⟨fa, fun hc => absurd (by simpa using hc) h1, fun _ => ⟨fd, fun hc => ?_, fun _ => rfl⟩⟩
  rw [BitVec.and_self] at hc
  exact absurd (hc.symm.trans h2) (by decide)

/-- From the entry to the error path: the stream closed or its descriptor negative. -/
theorem vc_bad {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (fd : ∀ i < 4, Foot F.data (Addr.add (Addr.add g.rdi 112) i)) (h : ¬ FnoOk V g.rdi) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 24 ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold FnoOk at h
  dsimp only at fa fd h ⊢
  wpx [W_0, W_12, o0, o1, Op.testmi, Op.ld]
  refine ⟨fa, fun _ => ⟨_, rfl⟩, fun hc => ⟨fd, fun _ => ⟨_, rfl⟩, fun hm => (h ⟨?_, ?_⟩).elim⟩⟩
  · first
    | simpa using hc
    | exact fun e => by simp [e] at hc
  · rw [BitVec.and_self] at hm
    exact hm

/-- The error path: `errno` = `EBADF`, `eax` -1. -/
theorem vc_24 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_24 fb F Wl (fun j' g' _ V' => j' = 43 ∧ g' = { g with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) ebadf)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_24, o2, Op.stfi]
  first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, by rw [show BitVec.setWidth 64 4294967295#32 = 4294967295#64 by decide]⟩
  | exact ⟨fe, rfl, rfl, rfl⟩
  | exact ⟨fe, rfl, by rw [show BitVec.setWidth 64 4294967295#32 = 4294967295#64 by decide], rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__fileno (fp)` from its entry to the return address, the return address popped: if the stream is open and its
descriptor not negative (`FnoOk`), that descriptor in `rax`; else `errno` = `EBADF` and `eax` -1. -/
theorem fno_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fno_at fno)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fno_at)
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd : ∀ i < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi 112) i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (FnoOk V X.cpu.gpr.rdi → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = { X.cpu.gpr with rax := BitVec.setWidth 64 (fdv V X.cpu.gpr.rdi) }.set 4 (X.cpu.gpr.rsp + 8)) →
      (¬ FnoOk V X.cpu.gpr.rdi → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) ebadf) ∧
        Z.cpu.gpr = { X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases hok : FnoOk V X.cpu.gpr.rdi
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 19 ∧ g' = { X.cpu.gpr with rax := BitVec.setWidth 64 (fdv V X.cpu.gpr.rdi) } ∧ V' = V)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_ok fa fd hok) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY] <;> rfl
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_19 _) (fun i hi => by rw [hspY]; exact hl i hi)
      hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k Z t₂ hKZ hrZ (fun _ => ⟨hAZ, ?_⟩) fun h => absurd hok h
    rw [hgZ, hgY] <;> rfl
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 24 ∧ (∃ a, g' = { X.cpu.gpr with rax := a }) ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_bad fa fd hok) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine (c_24 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 43 ∧ g' = { Y.cpu.gpr with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) ebadf)
      hKY hAY hrY (vc_24 fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hgY] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_43 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : ebadf.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + ebadf.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + ebadf.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) ebadf X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₃ hKZ' hrZ' (fun h => absurd h hok) fun _ => ⟨hAZ', ?_⟩
    rw [hgZ', hgZ, hgY] <;> rfl

end FV7z.Fno
