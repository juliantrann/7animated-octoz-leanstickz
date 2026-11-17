-- PROBE_ARGS: -DElab.async=false -Dprofiler=true -Dprofiler.threshold=300
-- PROBE_TIMEOUT: 10m
-- Gor.Holds g4_readlink
import FV7z.Gor.Loop
/-!
# `_dl_get_origin` from its entry to the `malloc` it calls, or to the `ret` with `-1` (PLAN.md G3, startup)

glibc 2.31's `_dl_get_origin` at `0x6aefa0`: `readlink ("/proc/self/exe", buf, 4096)` into a buffer `B` on the stack,
4136 bytes below the stack pointer of the entry.

- `frV_out`, `frV_rd`, `Vst_head`, `map_eq`: the bytes of the frame and of the buffer.
- `gEv`: the event of the `readlink`.
- `err_path`: from 51 with an error (`eax` above `-4096`) and `_dl_origin_path` null: the `ret` with `rax = -1`, the
  saved registers back.
- `gor_head`: from the entry, `ProcSelfExe` of the stream: the file system's answer an error or a path of `PATH_MAX`
  bytes or more (to the `ret` with `-1`), or the path `x` (`x.bytes.length < 4096`): at 124 (`malloc (2)`, no `/` after
  the first byte) or at 278 (`malloc (s + 2)`, `s = sl` the last `/`), the bytes `x.bytes` at `B`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gor

/-- `bv_omega` on the goal only: `bv_omega` simplifies every hypothesis too (`simp … at *`), which hangs in the big
contexts of these proofs (probes of 43634134673). Equalities of addresses by their `toNat`; `bitvec_to_nat` is
`bv_omega`'s simp set. -/
macro "bvg" : tactic => `(tactic| ((try apply BitVec.eq_of_toNat_eq) <;>
  (try simp only [ZellicX86.Addr.add, FV7z.toBytesLE_length]) <;>
  (try simp -implicitDefEqProofs only [bitvec_to_nat]) <;> omega))

/-- `Vst` of no bytes, over variables: stated apart, since `rfl` on `Vst (frV V g) B [] = frV V g` unfolds `frV` first
and compares the addresses by computing (a timeout, probes of 44086214316). -/
theorem Vst_nil (V : Addr → Byte) (a : Addr) : Vst V a [] = V := rfl

/-- `x.add ↑i` (`BitVec.add`, as the `syscall` lemmas state their bytes) is `Addr.add x i`; over variables, so the
literal addresses are never unfolded (`Nat.rec` on `7366691`). -/
theorem bva (x : BitVec 64) (i : Nat) : x.add (i : BitVec 64) = Addr.add x i := rfl

theorem upm (feat : Features) : 2 ^ 47 - 4096 ≤ userPtrMax feat := by
  unfold userPtrMax
  split <;> omega

/-- The bytes outside the four saved registers are as they were. -/
theorem frV_out (V : Addr → Byte) (g : Gprs) (a : Addr) (h32 : 32 ≤ g.rsp.toNat)
    (h : a.toNat + 32 < g.rsp.toNat ∨ g.rsp.toNat ≤ a.toNat) : frV V g a = V a := by
  unfold frV
  rw [Tun.Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Tun.Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Tun.Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega),
    Tun.Vst_out _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by simp only [toBytesLE_length]; bv_omega)]

/-- Bytes read the same where they agree. -/
theorem map_eq {V W : Addr → Byte} (x : Addr) (n : Nat) (h : ∀ i < n, W (x.add i) = V (x.add i)) :
    List.map W (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h j hj

/-- Bytes apart from those stored. -/
theorem map_out (V : Addr → Byte) (a : Addr) (bs : List Byte) (x : Addr) (n : Nat) (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hx : x.toNat + n ≤ 2 ^ 64) (h : x.toNat + n ≤ a.toNat ∨ a.toNat + bs.length ≤ x.toNat) :
    List.map (Vst V a bs) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  map_eq x n fun i hi => Tun.Vst_out _ _ _ _ ha (by simp only [Addr.add]; bv_omega)

/-- The first byte stored. -/
theorem Vst_head (V : Addr → Byte) (a : Addr) (b : Byte) (bs : List Byte) (h : a.toNat + 1 + bs.length < 2 ^ 64) :
    Vst V a (b :: bs) a = b := by
  show Vst (upd1 V a b) (a.add 1) bs a = b
  rw [Tun.Vst_out _ _ _ _ (by simp only [Addr.add]; bv_omega) (.inl (by simp only [Addr.add]; bv_omega))]
  simp [upd1]

/-- The four saved registers, read back from the frame, the bytes `bs` stored below it. -/
theorem frV_rd (V : Addr → Byte) (g : Gprs) (B : Addr) (bs : List Byte) (h32 : 4136 ≤ g.rsp.toNat)
    (hB : B = g.rsp - 4136#64) (hl : bs.length ≤ 4096) :
    rdq(Vst (frV V g) B bs, B + 4104#64) = g.rbx ∧ rdq(Vst (frV V g) B bs, B + 4104#64 + 8) = g.rbp ∧
      rdq(Vst (frV V g) B bs, B + 4104#64 + 8 + 8) = g.r12 ∧
      rdq(Vst (frV V g) B bs, B + 4104#64 + 8 + 8 + 8) = g.r13 := by
  subst hB
  have o : ∀ x : Addr, g.rsp.toNat - 32 ≤ x.toNat → x.toNat + 8 ≤ g.rsp.toNat →
      List.map (Vst (frV V g) (g.rsp - 4136#64) bs) (byteAddrs x 8) = List.map (frV V g) (byteAddrs x 8) :=
    fun x h1 h2 => map_eq x 8 fun i hi =>
      Tun.Vst_out _ _ _ _ (by bvg) (.inr (by simp only [Addr.add]; bvg))
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  have a1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bvg
  have a2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by bvg
  have a3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by bvg
  have a4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by bvg
  have m4 := fun W => map_out W (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)
  have m3 := fun W => map_out W (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)
  have m2 := fun W => map_out W (g.rsp - 8 - 8) (toBytesLE g.r12 8)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o _ (by bvg) (by bvg), show g.rsp - 4136#64 + 4104#64 = g.rsp - 8 - 8 - 8 - 8 by bvg]
    unfold frV
    rw [Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bvg) (by bvg), show g.rsp - 4136#64 + 4104#64 + 8 = g.rsp - 8 - 8 - 8 by bvg]
    unfold frV
    rw [m4 _ (g.rsp - 8 - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bvg) (by bvg), show g.rsp - 4136#64 + 4104#64 + 8 + 8 = g.rsp - 8 - 8 by bvg]
    unfold frV
    rw [m4 _ (g.rsp - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m3 _ (g.rsp - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bvg) (by bvg), show g.rsp - 4136#64 + 4104#64 + 8 + 8 + 8 = g.rsp - 8 by bvg]
    unfold frV
    rw [m4 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m3 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m2 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]

/-- An error number above `-4096` as `eax`. -/
theorem err_hi {e : Nat} (h1 : 0 < e) (h2 : e < 4096) : 4294963200 < (BitVec.setWidth 32 (errRet e)).toNat := by
  have he : e % 2 ^ 64 = e := Nat.mod_eq_of_lt (by omega)
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  unfold errRet
  first
  | (rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, he, h0]; omega)
  | (rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, he, h0]; simp; omega)
  | (simp only [bv_toNat]; omega)
  | (simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.zero_mod,
      Nat.add_zero, Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]; omega)

/-- The event of the `readlink` of `_dl_get_origin` called with registers `g`, the file system's answer `r`. -/
abbrev gEv (g : Gprs) (r : LinkResult) : Event :=
  ⟨BitVec.setWidth 64 89#32, [7366691#64, g.rsp - 4136#64, BitVec.setWidth 64 4096#32, g.r10, g.r8, g.r9],
    (linkRes 4096 r).1, pse, (linkRes 4096 r).2⟩

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 1000000 in
/-- From 51 with an error `e` returned, `rsp` the buffer `B` 4136 bytes below `g`'s, the four saved registers of `g` in
the frame, `_dl_origin_path` null: the `ret` with `rax = -1`, `rsp` and the saved registers `g`'s. -/
theorem err_path (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {g : Gprs} {V : Addr → Byte} {e : Nat}
    (he1 : 0 < e) (he2 : e < 4096) (h32 : 4136 ≤ g.rsp.toNat)
    (hfr : ∀ i < 32, Foot F.data (Addr.add (g.rsp - 32#64) i))
    (hof : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i)) (hoz : rdq(frV V g, 8029440#64) = 0#64)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (frV V g))
    (hrip : X.cpu.rip = gor_at.add 51) (hax : X.cpu.gpr.rax = errRet e) (hsp : X.cpu.gpr.rsp = g.rsp - 4136#64)
    (h14 : X.cpu.gpr.r14 = g.r14) (h15 : X.cpu.gpr.r15 = g.r15)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (frV V g) → Z.cpu.rip = gor_at.add 271 →
      Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = g.rsp → Z.cpu.gpr.rbx = g.rbx →
      Z.cpu.gpr.rbp = g.rbp → Z.cpu.gpr.r12 = g.r12 → Z.cpu.gpr.r13 = g.r13 → Z.cpu.gpr.r14 = g.r14 →
      Z.cpu.gpr.r15 = g.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  sorry

set_option maxHeartbeats 1000000 in
/-- `_dl_get_origin` from its entry: `readlink ("/proc/self/exe", B, 4096)`, `B` 4136 bytes below the stack pointer.
An error, or an executable's path of `PATH_MAX` bytes or more: the `ret` with `-1` (`ke`). The path `x` of fewer
bytes: at the `call` of `malloc` at 124 (`edi = 2`: no `/` after the first byte, `k1`) or at 278 (`edi = s + 2`,
`ebx = s`, the last `/` at `s ≥ 1`, `k2`), the bytes of `x` at `B`, `rsp = rbp = B`. -/
theorem gor_head (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gor_at)
    (h32 : 8192 ≤ X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hst : ∀ i < 4136, Foot Wl (Addr.add (X.cpu.gpr.rsp - 4136#64) i)) (hlo : 8029448 ≤ X.cpu.gpr.rsp.toNat - 4136)
    (hpf : ∀ i < 16, Foot F.data (Addr.add 7366691#64 i)) (hpn : ∀ i < 14, V (Addr.add 7366691#64 i) ≠ 0)
    (hpz : V (Addr.add 7366691#64 14) = 0) (hpp : (byteAddrs 7366691#64 14).map V = pse)
    (hof : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i)) (hoz : rdq(V, 8029440#64) = 0#64)
    (hps : ProcSelfExe o)
    (ke : ∀ r Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (frV V X.cpu.gpr) → Z.cpu.rip = gor_at.add 271 →
      Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv X.cpu.gpr r]) gP gE Z t')
    (k1 : ∀ x Z t', x.bytes.length < 4096 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) → Z.cpu.rip = gor_at.add 124 →
      Z.cpu.gpr.rdi = BitVec.ofNat 64 2 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 4136#64 →
      Z.cpu.gpr.rbp = X.cpu.gpr.rsp - 4136#64 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      sl (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) (X.cpu.gpr.rsp - 4136#64) x.bytes.length = 0 →
      GoG prof L o (gev ++ [gEv X.cpu.gpr (.procExe x)]) gP gE Z t')
    (k2 : ∀ x Z t', x.bytes.length < 4096 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) → Z.cpu.rip = gor_at.add 278 →
      Z.cpu.gpr.rdi = BitVec.ofNat 64
        (sl (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) (X.cpu.gpr.rsp - 4136#64) x.bytes.length + 2) →
      Z.cpu.gpr.rbx = BitVec.ofNat 64
        (sl (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) (X.cpu.gpr.rsp - 4136#64) x.bytes.length) →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 4136#64 →
      Z.cpu.gpr.rbp = X.cpu.gpr.rsp - 4136#64 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      1 ≤ sl (Vst (frV V X.cpu.gpr) (X.cpu.gpr.rsp - 4136#64) x.bytes) (X.cpu.gpr.rsp - 4136#64) x.bytes.length →
      GoG prof L o (gev ++ [gEv X.cpu.gpr (.procExe x)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have slot : ∀ (a : Addr) (k : Nat), k < 4136 → a = Addr.add (X.cpu.gpr.rsp - 4136#64) k → Foot Wl a :=
    fun a k hk ha => ha ▸ hst k hk
  have fout : ∀ a : Addr, a.toNat + 32 < X.cpu.gpr.rsp.toNat → frV V X.cpu.gpr a = V a :=
    fun a h => frV_out V X.cpu.gpr a (by omega) (.inl h)
  -- the prologue
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun i hi => ?_) ?_
  · exact slot _ (4104 + i) (by omega) (by simp only [Addr.add]; bvg)
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 4128#64 := by
    rw [hg₁]
    show X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 4096#64 = _
    bvg
  -- the stack probe
  refine c.s_or_mi64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (or_17 _) (fun i hi => ?_) ?_
  · show Foot Wl (Addr.add (Y₁.cpu.gpr.rsp + BitVec.ofNat 64 0) i)
    rw [hsp₁]
    exact slot _ (8 + i) (by omega) (by simp only [Addr.add]; bvg)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [probe_same] at hA₂
  -- the arguments of `readlink`
  refine (c_22 prof).run c hin _ hK₂ hA₂ hr₂ vc_22 ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hg₂] at hg₃
  have hsi₃ : Y₃.cpu.gpr.rsi = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bvg
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bvg
  have hbp₃ : Y₃.cpu.gpr.rbp = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bvg
  have hdi₃ : Y₃.cpu.gpr.rdi = 7366691#64 := by rw [hg₃]
  have hev : ∀ a bs, linkEv Y₃.cpu.gpr pse a bs = ⟨BitVec.setWidth 64 89#32, [7366691#64, X.cpu.gpr.rsp - 4136#64,
      BitVec.setWidth 64 4096#32, X.cpu.gpr.r10, X.cpu.gpr.r8, X.cpu.gpr.r9], a, pse, bs⟩ := by
    intro a bs
    unfold linkEv
    rw [hdi₃, hsi₃, hg₃, hg₁]
  -- `readlink`
  refine c.s_readlink hK₃ hA₃ hin (lt_len (by decide)) hr₃ (sys_49 _) (m := 14) (n := 4096) (p := pse)
    (by rw [hg₃]; first | rfl | (dsimp only; decide)) (by decide)
    (by rw [hdi₃, BitVec.toNat_ofNat]; have := upm prof.feat; omega)
    (fun i hi => by rw [hdi₃, bva]; exact hpf i (by omega))
    (fun i hi => by
      rw [hdi₃, bva, fout (Addr.add 7366691#64 i) (by simp only [Addr.add]; bvg)]
      exact hpn i hi)
    (by
      rw [hdi₃, bva, fout (Addr.add 7366691#64 14) (by simp only [Addr.add]; bvg)]
      exact hpz)
    (by
      rw [hdi₃, map_eq (7366691#64) 14 fun i hi => fout (Addr.add 7366691#64 i) (by simp only [Addr.add]; bvg)]
      exact hpp)
    (by rw [hg₃]; first | rfl | (dsimp only; decide)) (by decide) (by rw [hsi₃]; bvg)
    (fun i hi => by rw [hsi₃, bva]; exact slot _ i (by omega) rfl)
    (P := fun r => ∀ bs, r ≠ .target bs) (fun t' bs => hps t' none bs) ?_
  intro r hr Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsi₃] at hA₄
  sorry

end FV7z.Gor

