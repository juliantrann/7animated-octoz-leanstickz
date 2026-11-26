import FV7z.Fsk.Cuts
import FV7z.Lseek.Holds
/-!
# `CFileBase::seek` moves its file's position (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NIO::CFileBase::seek (off, whence)` at `0x4560b0` in `7zzs`: `edi` = the
descriptor (`this->_handle`, the 4 bytes at `this`), then a `jmp` to `__libc_lseek` (`Lseek.lseek_ok`), which
returns to `seek`'s caller.

- `jmp_6`: the instruction outside the block; `vc_0`: the verification condition of the load.
- `seek_ok`: called with `this`'s 4 bytes readable and `whence` at most `SEEK_END`, `lseek_ok` from the registers at
  the entry with `edi` the descriptor.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fsk

/-- The jump to `__libc_lseek`. -/
def pjm : List Byte := [0xe9, 0x85, 0x93, 0x1a, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 1741701] 5) := by dec_rfl
theorem wj_6 : pjm <+: fsk.drop 6 := by decide +kernel
theorem jmp_6 (feat : Features) : Dec feat fsk 6 (FV7z.mk .jmp 64 [.rel 1741701] 5) :=
  Dec.shift (j := 6) (k := 0) (pjm_0 feat) wj_6 (Nat.zero_le _)

/-- The descriptor at `this`. -/
abbrev fdOf (V : Addr → Byte) (p : Addr) : BitVec 64 := BitVec.setWidth 64 (ofBytesLE 32 ((byteAddrs p 4).map V))

variable {F : Footprint} {Wl : List Rgn}

/-- `mov edi, [rdi]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 6 ∧ g' = { g with rdi := fdOf V g.rdi } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa ⊢
  wpx [W_0, o0, Op.ld]
  first
  | exact fa
  | exact ⟨fa, rfl⟩
  | exact ⟨fa, rfl, rfl⟩
  | exact ⟨fa, fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fa, fun _ => rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `CFileBase::seek (off, whence)` from its entry to the return address: `lseek_ok` from the registers at the entry
with `rdi` the descriptor at `this` (`fdOf`). -/
theorem seek_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L fsk_at fsk) (hinl : CodeIn L Lseek.lsk_at Lseek.lsk)
    (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fsk_at)
    (fa : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hw : arg32 X.cpu.gpr.rdx ≤ 2)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Y S Z : State) (r : BitVec 64) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.gpr = { X.cpu.gpr with rdi := fdOf V X.cpu.gpr.rdi }.set 0 8 → Y.cpu.rip = Lseek.lsk_at.add 9 →
      S.cpu = (sysSt Y 2 r).cpu → S.proc.mm = Y.proc.mm → S.proc.files = Y.proc.files →
      Seg prof F Wl L S o → KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr r → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 r).set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr r → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB r)) ∧
        Z.cpu.gpr = (Lseek.lsErrG ((sysGpr Y 2).set 0 r)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [Lseek.lsEv { X.cpu.gpr with rdi := fdOf V X.cpu.gpr.rdi } r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 6 ∧ g' = { X.cpu.gpr with rdi := fdOf V X.cpu.gpr.rdi } ∧
    V' = V) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fa) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  refine c.s_jmp_x hK₁ hA₁ hin (lt_len (by decide)) hr₁ (jmp_6 _) hinl (Lseek.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hg : Y₂.cpu.gpr = { X.cpu.gpr with rdi := fdOf V X.cpu.gpr.rdi } := hg₂.trans hg₁
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := (congrArg Gprs.rsp hg).trans rfl
  have hdx₂ : Y₂.cpu.gpr.rdx = X.cpu.gpr.rdx := (congrArg Gprs.rdx hg).trans rfl
  refine Lseek.lseek_ok c hfs hrs hinl hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hdx₂]; exact hw) fe hfe
    (by rw [hsp₂]; exact hl) (by rw [hsp₂]; exact hsp) (by rw [hsp₂]; exact hsa) hin₂ h₂
    (by rw [hsp₂]; exact hra) ?_
  intro Y S Z r t' hKY hAY hgY hrY hcS hmS hfS cS hKZ hrZ hok herr
  rw [hg] at hgY
  have e : Lseek.lsEv Y₂.cpu.gpr r = Lseek.lsEv { X.cpu.gpr with rdi := fdOf V X.cpu.gpr.rdi } r := by rw [hg]
  rw [e]
  exact k Y S Z r t' hKY hAY hgY hrY hcS hmS hfS cS hKZ hrZ (by rw [hsp₂] at hok; exact hok)
    (by rw [hsp₂] at herr; exact herr)

end FV7z.Fsk
