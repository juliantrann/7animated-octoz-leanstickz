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
theorem Vst_head (V : Addr → Byte) (a : Addr) (b : Byte) (bs : List Byte) (h : a.toNat + 1 + bs.length ≤ 2 ^ 64) :
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
      Tun.Vst_out _ _ _ _ (by bv_omega) (.inr (by simp only [Addr.add]; bv_omega))
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  have a1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bv_omega
  have a2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by bv_omega
  have a3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by bv_omega
  have a4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by bv_omega
  have m4 := fun W => map_out W (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)
  have m3 := fun W => map_out W (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)
  have m2 := fun W => map_out W (g.rsp - 8 - 8) (toBytesLE g.r12 8)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o _ (by bv_omega) (by bv_omega), show g.rsp - 4136#64 + 4104#64 = g.rsp - 8 - 8 - 8 - 8 by bv_omega]
    unfold frV
    rw [Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bv_omega) (by bv_omega), show g.rsp - 4136#64 + 4104#64 + 8 = g.rsp - 8 - 8 - 8 by bv_omega]
    unfold frV
    rw [m4 _ (g.rsp - 8 - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bv_omega) (by bv_omega), show g.rsp - 4136#64 + 4104#64 + 8 + 8 = g.rsp - 8 - 8 by bv_omega]
    unfold frV
    rw [m4 _ (g.rsp - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m3 _ (g.rsp - 8 - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [o _ (by bv_omega) (by bv_omega), show g.rsp - 4136#64 + 4104#64 + 8 + 8 + 8 = g.rsp - 8 by bv_omega]
    unfold frV
    rw [m4 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m3 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      m2 _ (g.rsp - 8) 8 (by rw [l8]; omega) (by omega) (.inr (by rw [l8]; omega)),
      Tun.rd_Vst_self _ _ _ (l8 _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl]

/-- An error number above `-4096` as `eax`. -/
theorem err_hi {e : Nat} (h1 : 0 < e) (h2 : e < 4096) : 4294963200 < (BitVec.setWidth 32 (errRet e)).toNat := by
  unfold errRet
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The event of the `readlink` of `_dl_get_origin` called with registers `g`, the file system's answer `r`. -/
abbrev gEv (g : Gprs) (r : LinkResult) : Event :=
  ⟨BitVec.setWidth 64 89#32, [7366691#64, g.rsp - 4136#64, BitVec.setWidth 64 4096#32, g.r10, g.r8, g.r9],
    (linkRes 4096 r).1, pse, (linkRes 4096 r).2⟩

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

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
  refine (c_51 prof).run c hin _ hK hA hrip (vc_51e (by rw [hax]; exact err_hi he1 he2)) ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine (c_152 prof).run c hin _ hK₁ hA₁ hr₁ (vc_152 hof hoz) ?_
  rintro j' g₂ fl V' ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine (c_248 prof).run c hin _ hK₂ hA₂ hr₂ vc_248 ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hsp₃ : Y₃.cpu.gpr.rsp = g.rsp - 4136#64 := by rw [hg₃, hg₂, hg₁]; exact hsp
  refine (c_255 prof).run c hin _ hK₃ hA₃ hr₃ (vc_255 fun i hi => ?_) ?_
  · rw [hsp₃, show g.rsp - 4136#64 + 4104#64 = g.rsp - 32#64 by bv_omega]
    exact hfr i hi
  rintro j' g₄ fl V' ⟨rfl, hax₄, hsp₄, hbx₄, hbp₄, h12₄, h13₄, h14₄, h15₄, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst hg₄
  obtain ⟨r1, r2, r3, r4⟩ := frV_rd V g (g.rsp - 4136#64) [] h32 rfl (Nat.zero_le _)
  have v0 : Vst (frV V g) (g.rsp - 4136#64) [] = frV V g := rfl
  rw [v0] at r1 r2 r3 r4
  rw [hsp₃] at hsp₄ hbx₄ hbp₄ h12₄ h13₄
  refine k Y₄ t₄ hK₄ hA₄ hr₄ (by rw [hax₄, hg₃]) (by rw [hsp₄]; bv_omega) (hbx₄.trans r1) (hbp₄.trans r2)
    (h12₄.trans r3) (h13₄.trans r4) ?_ ?_
  · rw [h14₄, hg₃, hg₂, hg₁]
    exact h14
  · rw [h15₄, hg₃, hg₂, hg₁]
    exact h15

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
  · exact slot _ (4104 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 4128#64 := by
    rw [hg₁]
    show X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 4096#64 = _
    bv_omega
  -- the stack probe
  refine c.s_or_mi64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (or_17 _) (fun i hi => ?_) ?_
  · show Foot Wl (Addr.add (Y₁.cpu.gpr.rsp + BitVec.ofNat 64 0) i)
    rw [hsp₁]
    exact slot _ (8 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [probe_same] at hA₂
  -- the arguments of `readlink`
  refine (c_22 prof).run c hin _ hK₂ hA₂ hr₂ vc_22 ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hg₂] at hg₃
  have hsi₃ : Y₃.cpu.gpr.rsi = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bv_omega
  have hsp₃ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bv_omega
  have hbp₃ : Y₃.cpu.gpr.rbp = X.cpu.gpr.rsp - 4136#64 := by
    rw [hg₃]; show Y₁.cpu.gpr.rsp - 8#64 = _; rw [hsp₁]; bv_omega
  have hdi₃ : Y₃.cpu.gpr.rdi = 7366691#64 := by rw [hg₃]
  have hev : ∀ a bs, linkEv Y₃.cpu.gpr pse a bs = ⟨BitVec.setWidth 64 89#32, [7366691#64, X.cpu.gpr.rsp - 4136#64,
      BitVec.setWidth 64 4096#32, X.cpu.gpr.r10, X.cpu.gpr.r8, X.cpu.gpr.r9], a, pse, bs⟩ := by
    intro a bs
    unfold linkEv
    rw [hdi₃, hsi₃, hg₃, hg₁]
  -- `readlink`
  refine c.s_readlink hK₃ hA₃ hin (lt_len (by decide)) hr₃ (sys_49 _) (m := 14) (n := 4096) (p := pse)
    (by rw [hg₃]; decide) (by decide) (by rw [hdi₃, BitVec.toNat_ofNat]; have := upm prof.feat; omega)
    (fun i hi => by rw [hdi₃]; exact hpf i (by omega))
    (fun i hi => by
      rw [hdi₃, fout (Addr.add 7366691#64 i) (by simp only [Addr.add]; bv_omega)]
      exact hpn i hi)
    (by rw [hdi₃, fout (Addr.add 7366691#64 14) (by simp only [Addr.add]; bv_omega)]; exact hpz)
    (by
      rw [hdi₃, map_eq (7366691#64) 14 fun i hi => fout (Addr.add 7366691#64 i) (by simp only [Addr.add]; bv_omega)]
      exact hpp)
    (by rw [hg₃]; decide) (by decide) (by rw [hsi₃]; bv_omega)
    (fun i hi => by rw [hsi₃]; exact slot _ i (by omega) rfl)
    (P := fun r => ∀ bs, r ≠ .target bs) (fun t' bs => hps t' none bs) ?_
  intro r hr Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hsi₃] at hA₄
  rw [hev]
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 4136#64 := by rw [hg₄]; exact hsp₃
  have hbp₄ : Y₄.cpu.gpr.rbp = X.cpu.gpr.rsp - 4136#64 := by rw [hg₄]; exact hbp₃
  have h14₄ : Y₄.cpu.gpr.r14 = X.cpu.gpr.r14 := by
    rw [hg₄]
    show Y₃.cpu.gpr.r14 = _
    rw [hg₃, hg₁]
  have h15₄ : Y₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₄]
    show Y₃.cpu.gpr.r15 = _
    rw [hg₃, hg₁]
  have hax₄ : Y₄.cpu.gpr.rax = (linkRes 4096 r).1 := by rw [hg₄]; rfl
  have hfr : ∀ i < 32, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32#64) i) :=
    fun i hi => c.hws _ (slot _ (4104 + i) (by omega) (by simp only [Addr.add]; bv_omega))
  have hoz' : rdq(frV V X.cpu.gpr, 8029440#64) = 0#64 := by
    rw [map_eq (8029440#64) 8 fun i hi => fout (Addr.add 8029440#64 i) (by simp only [Addr.add]; bv_omega)]
    exact hoz
  have kerr : ∀ e, 0 < e → e < 4096 → (linkRes 4096 r) = (errRet e, []) →
      GoG prof L o (gev ++ [gEv X.cpu.gpr r]) gP gE Y₄ t₄ := by
    intro e he1 he2 hl
    rw [hl] at hA₄ hax₄
    try dsimp only at hA₄ hax₄
    exact err_path c hin he1 he2 (by omega) hfr hof hoz' hK₄ hA₄ hr₄ hax₄ hsp₄ h14₄ h15₄
      fun Z t' hKZ hAZ hrZ h0 h1 h2 h3 h4 h5 h6 h7 => ke r Z t' hKZ hAZ hrZ h0 h1 h2 h3 h4 h5 h6 h7
  cases r with
  | error e => exact kerr e.val e.2.1 e.2.2 rfl
  | target bs => exact absurd rfl (hr bs)
  | procExe x =>
    by_cases hx : x.bytes.length < pathMax
    · have hl : linkRes 4096 (.procExe x) = (BitVec.ofNat 64 x.bytes.length, x.bytes) := by
        have hle : x.bytes.length ≤ 4096 := by unfold pathMax at hx; omega
        simp only [linkRes, hx, ↓reduceIte, List.take_of_length_le hle]
      have hx' : x.bytes.length < 4096 := hx
      rw [hl] at hA₄ hax₄
      try dsimp only at hA₄ hax₄
      obtain ⟨rb, hrb⟩ := x.bytes_head
      have hn1 : 1 ≤ x.bytes.length := by rw [hrb]; simp
      have hB : ∀ i < 4096, Foot F.data (Addr.add (X.cpu.gpr.rsp - 4136#64) i) :=
        fun i hi => c.hws _ (slot _ i (by omega) rfl)
      refine (c_51 prof).run c hin _ hK₄ hA₄ hr₄ (vc_51k hn1 hx' hax₄ (fun i hi => ?_) ?_) ?_
      · obtain rfl : i = 0 := by omega
        have := hB 0 (by omega)
        rw [addr_add_zero] at this
        rw [addr_add_zero, hsp₄]
        exact this
      · have hlr := congrArg List.length hrb
        simp only [List.length_cons] at hlr
        rw [hsp₄, hrb, Vst_head _ _ _ _ (by bv_omega)]
      rintro j' g₅ fl V' ⟨rfl, hcx₅, hax₅, hkp₅, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
      subst hg₅
      refine loop c hin (g₀ := Y₄.cpu.gpr) hbp₄ hB ?_ ?_ x.bytes.length hn1 hx' rfl Y₅ t₅ hK₅ hA₅ hr₅ hcx₅
        (by rw [hax₅, hbp₄]) hkp₅
      · intro Z t' hKZ hAZ hrZ hdi hkp h0
        exact k1 x Z t' hx' hKZ hAZ hrZ hdi (hkp.1.trans hsp₄) (hkp.2.1.trans hbp₄) (hkp.2.2.1.trans h14₄)
          (hkp.2.2.2.trans h15₄) h0
      · intro Z t' hKZ hAZ hrZ hdi hbx hkp h1
        exact k2 x Z t' hx' hKZ hAZ hrZ hdi hbx (hkp.1.trans hsp₄) (hkp.2.1.trans hbp₄) (hkp.2.2.1.trans h14₄)
          (hkp.2.2.2.trans h15₄) h1
    · exact kerr ENAMETOOLONG (by decide) (by decide) (by simp only [linkRes, hx, ↓reduceIte])

end FV7z.Gor
