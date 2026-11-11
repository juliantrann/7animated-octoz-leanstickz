import FV7z.StartB.Cuts
import FV7z.Start.ToTls
/-!
# `__libc_start_main` sets the stack guard (PLAN.md G3, startup)

glibc 2.31's `__libc_start_main` from `0x6133c0`, after `__libc_setup_tls`: the thread control block is at the `fs`
base `fb`. The first stretch stores `_dl_x86_feature_1` (`0x7a85b8`) in the block's `feature_1` (`fs:0x48`) and the
stack guard in `fs:0x28`: the first 8 of `AT_RANDOM`'s 16 bytes (`_dl_random`, `0x791ca0`, points to them), the lowest
byte cleared (`_dl_setup_stack_chk_guard`); then, `__libc_multiple_libcs` (`0x7939c0`) being 0, it goes to the call of
`_dl_discover_osversion` at `0x61363e`.

- `guard V`, `GuardMem V fb`: the guard from the bytes `V`, and the bytes after the two stores.
- `vc_896`: the verification condition of the stretch (`StartB/Cuts.lean`, `W_896`).
- `lsb_guard`: the run from `0x6133c0` to `0x61363e`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- The stack guard: the first 8 bytes `_dl_random` points to, the lowest cleared. -/
def guard (V : Addr → Byte) : BitVec 64 := rdq(V, rdq(V, 7937184#64)) &&& 0xffffffffffffff00#64

/-- The bytes after the stores of `feature_1` and of the stack guard in the thread control block at `fb`. -/
def GuardMem (V : Addr → Byte) (fb : Addr) : Addr → Byte :=
  Vst (Vst V (fb + 72#64) (toBytesLE rdd(V, 8029624#64) 4)) (fb + 40#64) (toBytesLE (guard V) 8)

theorem xor_lo (x : BitVec 64) : x &&& ~~~BitVec.ofNat 64 ((256 - 1) * 1) |||
    BitVec.setWidth 64 (BitVec.setWidth 8 x ^^^ BitVec.setWidth 8 x) <<< 0 = x &&& 0xffffffffffffff00#64 := by
  rw [BitVec.xor_self]
  simp

/-- From `0x6133c0` to the call of `_dl_discover_osversion`: the two stores in the thread control block. -/
theorem vc_896 {fb rp : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hfb : 0x7a9000 ≤ fb.toNat) (hfb' : fb.toNat + 80 ≤ 2 ^ 64)
    (h1 : ∀ i < 4, Foot F.data (Addr.add 8029624#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add 7937184#64 i))
    (h3 : ∀ i < 4, Foot F.data (Addr.add 7944640#64 i)) (hw : ∀ i < 80, Foot Wl (fb.add i))
    (hrp : rdq(V, 7937184#64) = rp) (hrf : ∀ i < 8, Foot F.data (rp.add i)) (hrp' : rp.toNat + 8 ≤ 2 ^ 64)
    (hrl : rp.toNat + 8 ≤ fb.toNat ∨ fb.toNat + 80 ≤ rp.toNat) (hml : rdd(V, 7944640#64) = 0) :
    W_896 fb F Wl (fun j' g' _ V' => j' = 1534 ∧ g' = g.set 0 (guard V) ∧ V' = GuardMem V fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have t72 : (fb + 72#64).toNat = fb.toNat + 72 := by bv_omega
  have t40 : (fb + 40#64).toNat = fb.toNat + 40 := by bv_omega
  have e1 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 0x7a9000 →
      List.map (Vst V (fb + 72#64) (toBytesLE rdd(V, 8029624#64) 4)) (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n hx => rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t72]; omega) (by omega)
      (.inr (by rw [t72]; omega))
  have e2 : List.map (Vst V (fb + 72#64) (toBytesLE rdd(V, 8029624#64) 4)) (byteAddrs rp 8) =
      List.map V (byteAddrs rp 8) :=
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, t72]; omega) hrp' (by rw [toBytesLE_length, t72]; omega)
  have e3 : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 8 →
      List.map (Vst W (fb + 40#64) bs) (byteAddrs 7944640#64 4) = List.map W (byteAddrs 7944640#64 4) :=
    fun W bs hb => rd_Vst _ _ _ _ _ (by rw [hb, t40]; omega) (by decide)
      (.inr (by rw [t40]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
  wpx [W_896, o0, Op.lda, Op.cmpmia, Op.ldf, Op.stf, Op.xor8]
  rw [e1 7937184#64 8 (by decide), hrp, e2, xor_lo, e3 _ _ (toBytesLE_length _ _), e1 7944640#64 4 (by decide), hml]
  refine ⟨h1, fun i hi => ?_, h2, hrf, fun i hi => ?_, h3, fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
  · have := hw (72 + i) (by omega)
    rwa [show fb.add (72 + i) = (fb + 72#64).add i from by simp only [Addr.add]; bv_omega] at this
  · have := hw (40 + i) (by omega)
    rwa [show fb.add (40 + i) = (fb + 40#64).add i from by simp only [Addr.add]; bv_omega] at this
  · simp only [guard, hrp]
    rfl
  · simp only [GuardMem, guard, hrp]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From `0x6133c0` to the call of `_dl_discover_osversion` (`0x61363e`), in a run whose start has the `fs` base
`fb`: `feature_1` and the stack guard are in the thread control block, `rax` is the guard. -/
theorem lsb_guard {fb rp : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hl : CodeIn L lsm_at lsm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at.add 896) (hfb : 0x7a9000 ≤ fb.toNat) (hfb' : fb.toNat + 80 ≤ 2 ^ 64)
    (h1 : ∀ i < 4, Foot F.data (Addr.add 8029624#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add 7937184#64 i))
    (h3 : ∀ i < 4, Foot F.data (Addr.add 7944640#64 i)) (hw : ∀ i < 80, Foot Wl (fb.add i))
    (hrp : rdq(V, 7937184#64) = rp) (hrf : ∀ i < 8, Foot F.data (rp.add i)) (hrp' : rp.toNat + 8 ≤ 2 ^ 64)
    (hrl : rp.toNat + 8 ≤ fb.toNat ∨ fb.toNat + 80 ≤ rp.toNat) (hml : rdd(V, 7944640#64) = 0)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (GuardMem V fb) → Y.cpu.rip = lsm_at.add 1534 →
      Y.cpu.gpr = X.cpu.gpr.set 0 (guard V) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_896 prof fb).run c hfs hl _ hK hA hrip (vc_896 hfb hfb' h1 h2 h3 hw hrp hrf hrp' hrl hml) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  exact k Y t' hKY hAY hrY hgY

end FV7z.StartB
