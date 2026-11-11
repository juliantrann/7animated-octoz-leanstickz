import FV7z.Tgv.Cuts
import FV7z.Raf.Holds
/-!
# `__tunable_get_val` of a 32-bit tunable not set (PLAN.md G3, startup)

glibc 2.31's `__tunable_get_val (id, valp, callback)` at `0x66f3a0` in `7zzs` (`elf/dl-tunables.c`), by the blocks
of `Tgv/Cuts.lean`: for a tunable of type `TUNABLE_TYPE_INT_32` (its type code, at offset 8 of its entry, 0) that
was not set (its `initialized` byte, at offset 40, 0), the low 4 bytes of its value go to `*valp` and the function
returns without the callback. (`CpuFeat/Tgv.lean` has the call for a tunable of either type, the bytes stored 4 or 8,
which not said; here the caller's frame has only 4 bytes for them.)

- `ent`: a tunable's entry. `ret_96`: the `ret`. `vc_0`, `vc_49`: the verification conditions.
- `tgv32_ok`: from the entry to the return address, `*valp` the value's low 4 bytes, the registers a call keeps as
  at the entry (`Osv.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
namespace FV7z.Tgv

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_96 : pret <+: tgv.drop 96 := by decide +kernel
theorem ret_96 (feat : Features) : Dec feat tgv 96 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 96) (k := 0) (pret_0 feat) w_96 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The entry of tunable `d` in `tunable_list` (`0x791660`, 56 bytes an entry), as the code computes it. -/
def ent (d : Addr) : Addr := 7935584#64 + (d * 8#64 - d) * 8#64

/-- A 32-bit tunable: its value's low 4 bytes to `*valp`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {d : Addr}
    (hd : BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) = d)
    (hty : ∀ i < 4, Foot F.data ((ent d + 8#64).add i)) (hva : ∀ i < 8, Foot F.data ((ent d + 32#64).add i))
    (ht0 : rdd(V, ent d + 8#64) = 0) (hp : ∀ i < 4, Foot Wl (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 49 ∧
      g' = { g with rdi := d, rcx := 7935584#64, rax := rdq(V, ent d + 32#64), r8 := 0 } ∧
      V' = Vst V g.rsi (toBytesLE (BitVec.setWidth 32 rdq(V, ent d + 32#64)) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hp
  simp only [ent] at hty hva ht0
  wpx [W_0, W_42, W_47, o0, o1, o2, hd, ent, ht0]
  exact ⟨hty, hva, fun h => absurd h (by decide), fun _ => ⟨fun h => absurd h (by decide), fun _ => ⟨hp, rfl⟩⟩⟩

/-- A tunable not set: to the `ret`. -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} {d : Addr} (hdi : g.rdi = d) (hcx : g.rcx = 7935584#64)
    (hin0 : ∀ i < 1, Foot F.data ((ent d + 40#64).add i)) (hz : rdb(V, ent d + 40#64) = 0) :
    W_49 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = { g with rax := d * 8#64 - d, rsi := (d * 8#64 - d) * 8#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi hcx
  subst hdi hcx
  simp only [ent] at hin0 hz
  wpx [W_49, W_75, W_80, o3, o4, o5, Op.cmpmi, hz]
  exact ⟨hin0, fun _ => trivial, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `__tunable_get_val (d, valp, _)` for a 32-bit tunable `d` not set: the run reaches the return address with the
value's low 4 bytes at `valp`. -/
theorem tgv32_ok {d : Addr} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tgv_at tgv) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tgv_at)
    (hd : BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdi) = d)
    (hty : ∀ i < 4, Foot F.data ((ent d + 8#64).add i)) (hva : ∀ i < 8, Foot F.data ((ent d + 32#64).add i))
    (hin0 : ∀ i < 1, Foot F.data ((ent d + 40#64).add i))
    (ht0 : rdd(V, ent d + 8#64) = 0) (hz : rdb(V, ent d + 40#64) = 0)
    (hp : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rsi i)) (hpf : X.cpu.gpr.rsi.toNat + 4 ≤ 2 ^ 64)
    (hpd : (ent d + 40#64).toNat < X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 4 ≤ (ent d + 40#64).toNat)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hrd : X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat ∨ X.cpu.gpr.rsi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat)
    (k : ∀ g' Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rsi (toBytesLE (BitVec.setWidth 32 rdq(V, ent d + 32#64)) 4)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → Osv.Back X.cpu.gpr g' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hd hty hva ht0 hp) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hz₁ : rdb(Vst V X.cpu.gpr.rsi (toBytesLE (BitVec.setWidth 32 rdq(V, ent d + 32#64)) 4), ent d + 40#64) = 0 := by
    pv
    exact hz
  refine (c_49 prof).run c hin _ hK₁ hA₁ hr₁ (vc_49 (by rw [hg₁]) (by rw [hg₁]) hin0 hz₁) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hg₁]
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_96 _) (fun i hi => by rw [hsp₂]; exact hl i hi) hin₂ h₂
    ?_ ?_
  · rw [hsp₂, ← hra]
    pv
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have keep : Y₂.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y₂.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
      Y₂.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine k _ Z t' hKZ hAZ hrZ hgZ ⟨?_, keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1, keep.2.2.2.2.1, keep.2.2.2.2.2⟩
  show Y₂.cpu.gpr.rsp + 8 = _
  rw [hsp₂]
  rfl

/-- A 32-bit tunable `d` not set, as `tgv32_ok` takes it: its type code 0 and its `initialized` byte 0, these and its
value where the run may load. -/
structure Unset (F : Footprint) (V : Addr → Byte) (d : Addr) : Prop where
  ty : ∀ i < 4, Foot F.data ((ent d + 8#64).add i)
  va : ∀ i < 8, Foot F.data ((ent d + 32#64).add i)
  ini : ∀ i < 1, Foot F.data ((ent d + 40#64).add i)
  t0 : rdd(V, ent d + 8#64) = 0
  z : rdb(V, ent d + 40#64) = 0

/-- The same of bytes that are `V`'s outside a range above the entry. -/
theorem Unset.out {d : Addr} {V V' : Addr → Byte} {lo hi : Nat} (h : Unset F V d) (hd : (ent d).toNat + 48 ≤ lo)
    (hlo : lo ≤ 2 ^ 64) (ho : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → V' a = V a) : Unset F V' d := by
  refine ⟨h.ty, h.va, h.ini, ?_, ?_⟩
  · rw [← h.t0]
    exact congrArg (ofBytesLE 32) (Sga.rd_out ho (by bv_omega) (by bv_omega))
  · rw [← h.z]
    exact congrArg (ofBytesLE 8) (Sga.rd_out ho (by bv_omega) (by bv_omega))

end FV7z.Tgv
