import FV7z.Start.Guard
/-!
# `__libc_start_main` sets the pointer guard (PLAN.md G3, startup)

glibc 2.31's `__libc_start_main` from `0x6133ff`, after `__pthread_initialize_minimal`: the pointer guard, the second
8 of `AT_RANDOM`'s 16 bytes (`_dl_random`, `0x791ca0`, points to them), is stored in the thread control block
(`fs:0x30`). `rtld_fini` (`r13`) being 0 in a static program started by `execve`, `__cxa_atexit` is not called for
it, and the stretch at `0x613424` loads the arguments of `__libc_init_first`: `__environ`, `argv`, `argc`.

- `ptrGuard V`, `PtrMem V fb`: the pointer guard from the bytes `V`, and the bytes after the store.
- `vc_959`, `vc_996`: the verification conditions of the two stretches (`StartB/Cuts.lean`).
- `lsb_ptr`: the run from `0x6133ff` to the call of `__libc_init_first` at `0x613434`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- The pointer guard: the second 8 bytes `_dl_random` points to. -/
def ptrGuard (V : Addr → Byte) : BitVec 64 := rdq(V, rdq(V, 7937184#64) + 8#64)

/-- The bytes after the store of the pointer guard in the thread control block at `fb`. -/
def PtrMem (V : Addr → Byte) (fb : Addr) : Addr → Byte := Vst V (fb + 48#64) (toBytesLE (ptrGuard V) 8)

/-- From `0x6133ff` to `0x613424`, `r13` being 0: the store of the pointer guard. -/
theorem vc_959 {fb rp : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h2 : ∀ i < 8, Foot F.data (Addr.add 7937184#64 i)) (hw : ∀ i < 8, Foot Wl ((fb + 48#64).add i))
    (hrp : rdq(V, 7937184#64) = rp) (hrf : ∀ i < 8, Foot F.data ((rp + 8#64).add i)) (h13 : g.r13 = 0) :
    W_959 fb F Wl (fun j' g' _ V' => j' = 996 ∧ g' = g.set 0 (ptrGuard V) ∧ V' = PtrMem V fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : r13 = 0 := h13
  subst hrp
  wpx [W_959, o2, Op.lda, Op.ld, Op.stf, Op.test]
  exact ⟨h2, hrf, hw, fun af => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩⟩

/-- From `0x613424` to the call of `__libc_init_first`: its three arguments. -/
theorem vc_996 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ev av : BitVec 64} {ac : BitVec 32}
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h3 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i)) (he : rdq(V, 8013720#64) = ev)
    (ha : rdq(V, g.rsp + 16#64) = av) (hc : rdd(V, g.rsp + 12#64) = ac) :
    W_996 fb F Wl (fun j' g' _ V' => j' = 1012 ∧ g' = ((g.set 2 ev).set 6 av).set 7 (ac.setWidth 64) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h2 h3 ha hc
  subst he ha hc
  wpx [W_996, o4, Op.lda, Op.ld]
  exact ⟨h1, h2, h3, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From `0x6133ff` to the call of `__libc_init_first` (`0x613434`), `rtld_fini` being 0: the pointer guard is in
the thread control block, `rax` is the guard, and `rdx`, `rsi`, `edi` are `__environ` and the frame's `argv` and
`argc`. -/
theorem lsb_ptr {fb rp : Addr} {ev av : BitVec 64} {ac : BitVec 32} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hl : CodeIn L lsm_at lsm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at.add 959) (hfb : 0x7a9000 ≤ fb.toNat) (hfb' : fb.toNat + 56 ≤ 2 ^ 64)
    (h2 : ∀ i < 8, Foot F.data (Addr.add 7937184#64 i)) (hw : ∀ i < 8, Foot Wl ((fb + 48#64).add i))
    (hrp : rdq(V, 7937184#64) = rp) (hrf : ∀ i < 8, Foot F.data ((rp + 8#64).add i)) (h13 : X.cpu.gpr.r13 = 0)
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (h3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 16#64) i))
    (h4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 12#64) i))
    (hsp : X.cpu.gpr.rsp.toNat + 24 ≤ 2 ^ 64)
    (hsl : X.cpu.gpr.rsp.toNat + 24 ≤ fb.toNat ∨ fb.toNat + 56 ≤ X.cpu.gpr.rsp.toNat)
    (he : rdq(V, 8013720#64) = ev) (ha : rdq(V, X.cpu.gpr.rsp + 16#64) = av)
    (hc : rdd(V, X.cpu.gpr.rsp + 12#64) = ac)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (PtrMem V fb) → Y.cpu.rip = lsm_at.add 1012 →
      Y.cpu.gpr = (((X.cpu.gpr.set 0 (ptrGuard V)).set 2 ev).set 6 av).set 7 (ac.setWidth 64) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have t48 : (fb + 48#64).toNat = fb.toNat + 48 := by bv_omega
  refine (c_959 prof fb).run c hfs hl _ hK hA hrip (vc_959 h2 hw hrp hrf h13) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; rfl
  refine (c_996 prof fb).run c hfs hl _ hKY hAY hrY (vc_996 (ev := ev) (av := av) (ac := ac) h1
    (by rw [hsY]; exact h3) (by rw [hsY]; exact h4) ?_ ?_ ?_) ?_
  · unfold PtrMem
    rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t48]; omega) (by decide)
      (.inr (by rw [t48]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega))]
    exact he
  · unfold PtrMem
    rw [hsY, rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t48]; omega) (by bv_omega)
      (by rw [toBytesLE_length, t48]; bv_omega)]
    exact ha
  · unfold PtrMem
    rw [hsY, rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t48]; omega) (by bv_omega)
      (by rw [toBytesLE_length, t48]; bv_omega)]
    exact hc
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t'' hKZ hAZ hrZ hgZ -
  exact k Z t'' hKZ hAZ hrZ (by rw [hgZ, hgY])

end FV7z.StartB
