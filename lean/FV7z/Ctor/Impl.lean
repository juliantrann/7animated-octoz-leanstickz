import FV7z.Ctor.Ret
import FV7z.Lemmas.CallFn
import FV7z.Start.StackMap
/-!
# A constructor that is a function with its own proof (PLAN.md §M, constructors)

`csuTg 5`, `7`, `9`, `92` are `endbr64; jmp f`, with `f` a function whose code has its own proof (`ImplementsCall` of
a contract `fnK`: `Prepare/K.lean`). At `f`'s entry the frame's call is a call of `f`: the return address into
`__libc_csu_init` is on the stack, and the callee returns as its contract says, keeping the registers a call keeps.

- `implK_runs`: a function at `e` with `ImplementsCall` of `fnK` is a function as `Csu.csu_ok` asks, for an
  invariant that goes from `m` to `m + 1` by the contract's postcondition and the bytes it may store.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The return address into `__libc_csu_init` is canonical. -/
theorem csu_canon {j : Nat} (hj : j < Csu.csu.length) (b : Bool) : (Csu.csu_at.add j).canonical b = true := by
  have hl := Csu.csu_length
  have e0 : Csu.csu_at.toNat = 0x613ca0 := rfl
  refine canonical_low ?_ b
  rw [toNat_add_of_fits hj (by rw [e0]; omega), e0]
  omega

/-- A function at `e` with its own proof (`ImplementsCall` of `fnK`) is a function as `Csu.csu_ok` asks: at its
entry from the frame's call (`rsp = sp - 64`, the return address in the slot) the call is one its contract covers
(`hY`: the footprint a part of the run's, what it may store among the run's `Wl` and apart from the frame's bytes and
the arrays, its precondition), and `J (m + 1)` holds of the bytes after its return (`hJ`: by the postcondition, the
bytes it does not store into as before, the memory there). -/
theorem implK_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} {m : Nat}
    {e : Addr} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (himp : ImplementsCall prof e L (fnK k W R pre post))
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0) (hal : (sp - 64#64 + 8).toNat % 16 = 0)
    (hY : ∀ (Y : State) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → J m V → Y.cpu.rip = e →
      Y.cpu.gpr.rsp = sp - 64#64 → (m ≠ 1 → Y.cpu.gpr.rdi = a₀ ∧ Y.cpu.gpr.rsi = a₁ ∧ Y.cpu.gpr.rdx = a₂) →
      Sub F ((fnK k W R pre post).footprint L Y) ∧ (∀ y, Foot (ws k W Y) y → Foot Wl y) ∧ pre Y ∧
        Apart [frame Y k] (W Y ++ R Y) ∧
        ∀ y, Foot (ws k W Y) y → ¬ (sp.toNat - 56 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) ∧
          ¬ (7829400 ≤ y.toNat ∧ y.toNat < 7830224))
    (hJ : ∀ (Y Z : State) (V V' : Addr → Byte), Y.cpu.gpr.rsp = sp - 64#64 → J m V → post Y Z →
      (∀ y, ¬ Foot (ws k W Y) y → V' y = V y) → Agree F Z.proc.mm.mem V' → J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m e := by
  intro X t V j₂ hK hA hI hr hsp hargs hj₂ hra k'
  obtain ⟨hsub, hwsW, hpre, hfa, hout⟩ := hY X V hK hA hI hr hsp hargs
  have hokX : F.Ok prof.feat X := c.foot.keptW c.ready.rseq c.hws hK c.sub_self
  have hRX : Ready prof.feat X := c.ready.keptW c.foot c.hws hK
  have hGok := c.foot.keptW c.ready.rseq c.hws hK hsub
  have hs0 := hC.s0
  have hword : Word X X.cpu.gpr.rsp (Csu.csu_at.add j₂) := by
    unfold Word
    rw [hsp, hA.read (fun i hi => c.hws _ (hC.st i (by omega)))]
    exact hra
  have hent : sysv.entry X := ⟨by rw [hsp]; exact hal, by rw [hK.df]; exact hdf, by rw [hK.x87]; exact hx87⟩
  have hcall : CallOf prof e L (fnK k W R pre post) X (Csu.csu_at.add j₂) :=
    ⟨⟨hr, hword, csu_canon hj₂ _, hent⟩, hRX, hGok, fnK_apart hfa, hpre⟩
  refine RunsFrom.bind (runsFrom_of_reach (himp X _ hcall) c.env t (gE := gE) fun _ _ h => h.elim) ?_
  rintro Z T _ ⟨evs, rfl, hret, -, ⟨hpost, hKZ⟩, hev⟩
  have hev' : evs = [] := hev
  subst hev'
  rw [List.append_nil]
  have hZm : ∀ y, Foot F.data y → ¬ Foot (ws k W X) y → Z.proc.mm.mem.readByte y = V y := fun y hy hny => by
    rw [hKZ.calm.readByte_apart hokX hRX.rseq (fun y hy => c.hws y (hwsW y hy)) (foot_append_iff.2 (Or.inl hy))
      hny]
    exact hA y hy
  classical
  let V' : Addr → Byte := fun y => if Foot (ws k W X) y then Z.proc.mm.mem.readByte y else V y
  have hV' : ∀ y, ¬ Foot (ws k W X) y → V' y = V y := fun y h => if_neg h
  have hAZ : Agree F Z.proc.mm.mem V' := fun y hy => by
    by_cases h : Foot (ws k W X) y
    · exact (if_pos h).symm
    · rw [hV' y h]
      exact hZm y hy h
  obtain ⟨hrZ, hp, hsZ, -⟩ := hret
  have eg : ∀ r : Reg, RegName.gpr r ∈ sysv.preserved → Z.cpu.gpr.get r = X.cpu.gpr.get r := fun r hr => hp _ hr
  exact k' Z T V' (hK.trans hKZ hwsW) hAZ (hJ X Z V V' hsp hI hpost hV' hAZ)
    (fun a ha => hV' a fun h => (hout a h).1 ha) (fun a ha => hV' a fun h => (hout a h).2 ha) hrZ
    ⟨hsZ, eg 3 (by simp [sysv]), eg 5 (by simp [sysv]), eg 12 (by simp [sysv]), eg 13 (by simp [sysv]),
      eg 14 (by simp [sysv]), eg 15 (by simp [sysv])⟩

end FV7z.Ctor
