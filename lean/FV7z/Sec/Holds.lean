import FV7z.Sec.Cuts
import FV7z.Spec.InitSecure
import FV7z.Lemmas.BlkOps2
/-!
# `__libc_init_secure` keeps its contract (PLAN.md G3, startup)

One cut point, the entry: with `__libc_enable_secure_decided` not 0 the code loads it, tests it and returns; the way
to the system calls (16) is not taken. `secRun`: by `Seg.cfg` the run reaches the `ret` with the registers as at the
call. `sec_holds`: every call of the code at its place in `7zzs`, on every processor, returns as the contract says.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Sec FV7z.InitSecure
namespace FV7z.Sec

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_14 : pret <+: sec.drop 14 := by decide +kernel
theorem ret_14 (feat : Features) : Dec feat sec 14 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 14) (k := 0) (pret_0 feat) w_14 (Nat.zero_le _)

/-- At the `ret`: the registers a call keeps are as at the call. -/
def R (s : State) (g : Gprs) : Prop :=
  g.rsp = s.cpu.gpr.rsp ∧ g.rbx = s.cpu.gpr.rbx ∧ g.rbp = s.cpu.gpr.rbp ∧ g.r12 = s.cpu.gpr.r12 ∧
    g.r13 = s.cpu.gpr.r13 ∧ g.r14 = s.cpu.gpr.r14 ∧ g.r15 = s.cpu.gpr.r15

/-- At the entry: these, and `__libc_enable_secure_decided` is not 0. -/
def Inv (s : State) (ℓ : Nat) (_ : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ℓ = 0 ∧ R s g ∧ ofBytesLE 32 (List.map V (byteAddrs 0x7a85c4#64 4)) ≠ 0

variable {s : State} {F : Footprint} {Wl : List Rgn}

theorem vcAll (hE : ∀ i, i < 4 → Foot F.data (Addr.add 0x7a85c4#64 i)) (ℓ : Nat) :
    ∀ n g f V, Inv s ℓ n g V → Wt ℓ F Wl (fun j' g' _ V' => (∃ m', m' < n ∧ Inv s j' m' g' V') ∨ (j' = 14 ∧ R s g'))
      g f V := by
  rintro n g f V ⟨rfl, hR, hd⟩
  simp only [Wt, ↓reduceIte]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.lda]
  exact ⟨hE, fun hc => absurd (by simpa using hc) hd, fun _ => Or.inr hR⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {ra : Addr} {o : Oracle}

/-- A call runs to its return, as the contract says. -/
theorem secRun (c : Call prof 0 (fun _ => []) reads Pre (fun _ _ => True) sec_at L s ra o)
    (hin : CodeIn L sec_at sec) (t : Nat) :
    Go prof 0 (fun _ => []) reads Pre (fun _ _ => True) L s ra o s t := by
  have hE : ∀ i, i < 4 → Foot (fp 0 (fun _ => []) reads Pre (fun _ _ => True) L s).data (Addr.add 0x7a85c4#64 i) := by
    intro i hi
    refine ⟨rDecided, by simp [Footprint.data, Contract.footprint, fn, reads], ?_⟩
    have e : (Addr.add 0x7a85c4#64 i).toNat = 0x7a85c4 + i := toNat_add_of_fits hi (by decide)
    have e0 : (0x7a85c4 : Addr).toNat = 0x7a85c4 := by decide
    simp only [Rgn.Mem, rDecided, e, e0]
    omega
  refine c.toSeg.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V => Inv s ℓ n g V)
    (fun j' g' _ _ => j' = 14 ∧ R s g') (fun ℓ n g f V h => vcAll hE ℓ n g f V h) ?_ 0 0
    (KeptW.refl _ _) (V := s.proc.mm.mem.readByte) (fun a _ => rfl)
    (by rw [addr_add_zero]; exact c.call.shape.1)
    ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, c.call.pre.decided⟩
  rintro j' g fl V' ⟨rfl, hsp, hbx, hbp, h12, h13, h14, h15⟩ Y t' hKY hAY hrY rfl rfl
  exact c.ret hKY ⟨hbx, hsp, hbp, h12, h13, h14, h15⟩ hin (lt_len (by decide)) hrY (ret_14 _) fun M hM => trivial

/-- `__libc_init_secure`, at its place in `7zzs`, on every processor: every call returns as its contract says. -/
theorem sec_holds (L : List (Addr × List Byte)) (prof : Profile) (hin : CodeIn L sec_at sec) :
    ImplementsCall prof sec_at L InitSecure.contract := by
  intro s₀ ra hcall
  have hcall' : CallOf prof sec_at L (fn 0 (fun _ => []) reads Pre (fun _ _ => True)) s₀ ra := hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    secRun (Call.of hcall' ho (by rintro i hi ⟨r, hr, hm⟩; cases hr)) hin t

end FV7z.Sec
